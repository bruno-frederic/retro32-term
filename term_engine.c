/*
 * Retro32 Terminal - a tiny ANSI terminal
 *
 *
 * Earlier versions handed the
 * ANSI work to console.device; the console cannot express PC ANSI - SGR
 * 1 is a brightness bit on a PC but a font weight to the console, and
 * the console addresses only pens 0-7, leaving the bright palette half
 * (the dark grey of shadows and dot leaders above all) unreachable on
 * any Kickstart - so the terminal now parses and draws itself (see the
 * terminal engine section).
 *
 * This module requires the following elements from DCTelnet for term_init():
 *   Screen   : must already be opened
 *   TextFont : must already be opened; should be 8x8
 *
 * Outgoing data is transmitted through TCP socket
 */



/* NDK headers */
#include <proto/exec.h>
#include <proto/dos.h>
#include <proto/graphics.h>
#include <proto/intuition.h>
#include <proto/console.h>
#include <devices/conunit.h>
#include <devices/bsdsocket.h>


// Wrapper around send() from bsdsocket.library that maintains the nBytesSent counter.
long ser_write(const UBYTE *buf, long len)
{
    if(send(tcpSocket, data, len, 0) < 0) return -1;

    nBytesSent += len;
    return len;
}



/* --- terminal engine ------------------------------------------------------
 * A PC-ANSI (ANSI.SYS / ANSI-BBS) terminal rendered by hand. Kickstart's
 * and AROS's console.device both fall short of what BBS art assumes:
 * SGR 1 selects a bold font instead of the bright palette half, only
 * pens 0-7 are addressable so bright black (grey) cannot exist, the
 * parameterized erase forms differ, and the AROS parser had to be
 * defended against outright (its command scanner runs past finals it
 * does not know, spilling the following text). So the console is not
 * used at all: incoming bytes run through a small ECMA-48 state machine
 * here and are drawn straight into the screen's 4 bitplanes.
 *
 * - A character cell is 8x8 pixels, and 8 hires pixels are exactly one
 *   byte per bitplane, so a glyph is 32 byte writes with foreground and
 *   background masks; no blitter, no read-modify-write.
 * - Glyphs come from the ROM Topaz 8 (see font_extract), so the art
 *   renders in the face it was drawn for on every Kickstart and AROS.
 * - Scrolls, erases and insert/delete go through BltBitMap on the
 *   screen bitmap: minterm 0xFF or 0x00 with a plane mask paints any
 *   pen, and BltBitMap picks the descending mode by itself when the
 *   rectangles overlap. The one rule is WaitBlit before the next CPU
 *   write into the planes (term_blit_sync).
 * - PC semantics throughout: the palette is the 16-colour CGA set in
 *   ANSI order, bold folds into bright foregrounds, blink into bright
 *   backgrounds (iCE colours), erases fill with the current background
 *   (BCE), ESC[2J homes the cursor like ANSI.SYS, autowrap is deferred
 *   DEC-style (a glyph in column 80 parks the cursor there and the
 *   next glyph wraps), and DSR 6 is answered on the serial line here,
 *   on Kickstart and AROS alike. */

#define COLS 80

static struct BitMap *term_bm; /* the screen's bitmap */
static UBYTE *term_plane[4];
static WORD term_bpr;  /* bytes per plane row (80 at 640 wide) */
static WORD term_rows; /* text rows: 32 PAL, 25 NTSC */

/* Topaz 8 glyphs, one byte per row, flat for fast cell addressing. */
static UBYTE font8[256 * 8];

static WORD cur_x, cur_y;
static WORD sav_x, sav_y; /* CSI s/u (and ESC 7/8) cursor save slot */
static WORD atr_fg = 7;   /* base colours 0-7; brightness lives in */
static WORD atr_bg;       /* atr_bold / atr_blink */
static WORD atr_bold, atr_blink, atr_inv, atr_under;
static WORD wrap_pending;
static WORD cursor_visible = 1; /* ESC[?25l/h */
static WORD cursor_drawn;       /* cursor cell is currently inverted */
static WORD blit_pending;       /* a BltBitMap has been started */

/* CSI parser state. */
#define P_MAX 16
static WORD p_state; /* 0 plain, 1 ESC, 2 ESC intermediates, 3 CSI body */
static WORD p_params[P_MAX];
static WORD p_np;     /* index of the parameter being collected */
static WORD p_have;   /* a digit or ';' has been seen */
static WORD p_priv;   /* leading private marker ('?'), or 0 */
static WORD p_ignore; /* unknown byte seen: parse fully, execute nothing */

/* Pull the glyph bitmaps out of an opened font. tf_CharData is one wide
 * bitmap, tf_Modulo bytes per scanline; tf_CharLoc gives each glyph's
 * bit offset into it. Topaz 8 is byte-aligned 8x8 so the shift path is
 * insurance, not the norm. Characters the font lacks stay blank (BSS). */
static void font_extract(struct TextFont *tf)
{
    const UBYTE *data = (const UBYTE *)tf->tf_CharData;
    const ULONG *loc = (const ULONG *)tf->tf_CharLoc;
    WORD ys = tf->tf_YSize > 8 ? 8 : tf->tf_YSize;
    WORD c, r;

    for (c = tf->tf_LoChar; c <= tf->tf_HiChar; c++) {
        ULONG bitoff = loc[c - tf->tf_LoChar] >> 16;
        const UBYTE *src = data + (bitoff >> 3);
        WORD sh = (WORD)(bitoff & 7);
        UBYTE *dst = &font8[c << 3];
        for (r = 0; r < ys; r++) {
            UBYTE g = (UBYTE)(src[0] << sh);
            if (sh)
                g |= src[1] >> (8 - sh);
            dst[r] = g;
            src += tf->tf_Modulo;
        }
    }
}

static void term_blit_sync(void)
{
    if (blit_pending) {
        WaitBlit();
        blit_pending = 0;
    }
}

/* Cell-aligned rectangle fill in an arbitrary pen: set the planes where
 * the pen has a 1 bit (minterm 0xFF ignores its inputs and writes 1s),
 * clear the rest. Coordinates and sizes are in character cells. */
static void term_rect_fill(WORD x, WORD y, WORD w, WORD h, WORD pen)
{
    ULONG setm = (ULONG)pen & 0xF;
    if (w <= 0 || h <= 0)
        return;
    if (setm)
        BltBitMap(term_bm, x << 3, y << 3, term_bm, x << 3, y << 3,
                  w << 3, h << 3, 0xFF, setm, NULL);
    if (setm != 0xF)
        BltBitMap(term_bm, x << 3, y << 3, term_bm, x << 3, y << 3,
                  w << 3, h << 3, 0x00, setm ^ 0xF, NULL);
    blit_pending = 1;
}

static void term_rect_copy(WORD sx, WORD sy, WORD dx, WORD dy, WORD w, WORD h)
{
    if (w <= 0 || h <= 0)
        return;
    BltBitMap(term_bm, sx << 3, sy << 3, term_bm, dx << 3, dy << 3,
              w << 3, h << 3, 0xC0, 0xF, NULL);
    blit_pending = 1;
}

static WORD term_fg_pen(void)
{
    WORD fg = atr_fg + (atr_bold ? 8 : 0);
    WORD bg = atr_bg + (atr_blink ? 8 : 0);
    return atr_inv ? bg : fg;
}

static WORD term_bg_pen(void)
{
    WORD fg = atr_fg + (atr_bold ? 8 : 0);
    WORD bg = atr_bg + (atr_blink ? 8 : 0);
    return atr_inv ? fg : bg;
}

static void term_glyph(WORD x, WORD y, UBYTE ch)
{
    const UBYTE *g = &font8[(UWORD)ch << 3];
    LONG off = (LONG)y * (term_bpr << 3) + x;
    WORD fg = term_fg_pen(), bg = term_bg_pen();
    WORD p, r;

    term_blit_sync();
    for (p = 0; p < 4; p++) {
        UBYTE fm = (UBYTE)((fg & (1 << p)) ? 0xFF : 0x00);
        UBYTE bm = (UBYTE)((bg & (1 << p)) ? 0xFF : 0x00);
        UBYTE *dst = term_plane[p] + off;
        for (r = 0; r < 8; r++) {
            UBYTE bits = g[r];
            if (r == 7 && atr_under)
                bits = 0xFF;
            *dst = (UBYTE)((bits & fm) | (~bits & bm));
            dst += term_bpr;
        }
    }
}

/* The cursor is the cell under it with every plane byte inverted (pen
 * XOR 15), which is self-restoring: flipping twice puts the cell back.
 * Drawing only ever happens with the cursor hidden (see drain_serial),
 * so glyphs never land on an inverted cell. */
static void term_cursor_flip(void)
{
    LONG off = (LONG)cur_y * (term_bpr << 3) + cur_x;
    WORD p, r;

    term_blit_sync();
    for (p = 0; p < 4; p++) {
        UBYTE *dst = term_plane[p] + off;
        for (r = 0; r < 8; r++) {
            *dst ^= 0xFF;
            dst += term_bpr;
        }
    }
}

static void cursor_hide(void)
{
    if (cursor_drawn) {
        term_cursor_flip();
        cursor_drawn = 0;
    }
}

static void cursor_show(void)
{
    if (cursor_visible && !cursor_drawn) {
        term_cursor_flip();
        cursor_drawn = 1;
    }
}

static void term_scroll_up(WORD n)
{
    WORD bg = term_bg_pen();
    if (n >= term_rows) {
        term_rect_fill(0, 0, COLS, term_rows, bg);
        return;
    }
    term_rect_copy(0, n, 0, 0, COLS, term_rows - n);
    term_rect_fill(0, term_rows - n, COLS, n, bg);
}

static void term_scroll_down(WORD n)
{
    WORD bg = term_bg_pen();
    if (n >= term_rows) {
        term_rect_fill(0, 0, COLS, term_rows, bg);
        return;
    }
    term_rect_copy(0, 0, 0, n, COLS, term_rows - n);
    term_rect_fill(0, 0, COLS, n, bg);
}

static void term_erase_display(WORD mode)
{
    WORD bg = term_bg_pen();
    if (mode >= 2) {
        /* ANSI.SYS semantics: 2J (and xterm's 3J) clears and homes. */
        term_rect_fill(0, 0, COLS, term_rows, bg);
        cur_x = cur_y = 0;
        wrap_pending = 0;
    } else if (mode == 1) {
        term_rect_fill(0, 0, COLS, cur_y, bg);
        term_rect_fill(0, cur_y, cur_x + 1, 1, bg);
    } else {
        term_rect_fill(cur_x, cur_y, COLS - cur_x, 1, bg);
        term_rect_fill(0, cur_y + 1, COLS, term_rows - 1 - cur_y, bg);
    }
}

static void term_erase_line(WORD mode)
{
    WORD bg = term_bg_pen();
    if (mode >= 2)
        term_rect_fill(0, cur_y, COLS, 1, bg);
    else if (mode == 1)
        term_rect_fill(0, cur_y, cur_x + 1, 1, bg);
    else
        term_rect_fill(cur_x, cur_y, COLS - cur_x, 1, bg);
}

static void term_insert_lines(WORD n)
{
    WORD below = term_rows - cur_y;
    if (n > below)
        n = below;
    term_rect_copy(0, cur_y, 0, cur_y + n, COLS, below - n);
    term_rect_fill(0, cur_y, COLS, n, term_bg_pen());
}

static void term_delete_lines(WORD n)
{
    WORD below = term_rows - cur_y;
    if (n > below)
        n = below;
    term_rect_copy(0, cur_y + n, 0, cur_y, COLS, below - n);
    term_rect_fill(0, term_rows - n, COLS, n, term_bg_pen());
}

static void term_insert_chars(WORD n)
{
    WORD rest = COLS - cur_x;
    if (n > rest)
        n = rest;
    term_rect_copy(cur_x, cur_y, cur_x + n, cur_y, rest - n, 1);
    term_rect_fill(cur_x, cur_y, n, 1, term_bg_pen());
}

static void term_delete_chars(WORD n)
{
    WORD rest = COLS - cur_x;
    if (n > rest)
        n = rest;
    term_rect_copy(cur_x + n, cur_y, cur_x, cur_y, rest - n, 1);
    term_rect_fill(COLS - n, cur_y, n, 1, term_bg_pen());
}

static void term_sgr(WORD v)
{
    /* aixterm bright forms: brightness without the attribute dance. */
    if (v >= 90 && v <= 97) {
        atr_fg = v - 90;
        atr_bold = 1;
        return;
    }
    if (v >= 100 && v <= 107) {
        atr_bg = v - 100;
        atr_blink = 1;
        return;
    }
    switch (v) {
    case 0:
        atr_fg = 7;
        atr_bg = 0;
        atr_bold = atr_blink = atr_inv = atr_under = 0;
        break;
    case 1:
        atr_bold = 1;
        break;
    case 2: /* faint: no separate rendition, treat as intensity off */
    case 21:
    case 22:
        atr_bold = 0;
        break;
    case 4:
        atr_under = 1;
        break;
    case 24:
        atr_under = 0;
        break;
    case 5: /* blink selects bright backgrounds, the iCE colour rule */
    case 6:
        atr_blink = 1;
        break;
    case 25:
        atr_blink = 0;
        break;
    case 7:
        atr_inv = 1;
        break;
    case 27:
        atr_inv = 0;
        break;
    case 39:
        atr_fg = 7;
        break;
    case 49:
        atr_bg = 0;
        break;
    default:
        if (v >= 30 && v <= 37)
            atr_fg = v - 30;
        else if (v >= 40 && v <= 47)
            atr_bg = v - 40;
        break;
    }
}

static void term_linefeed(void)
{
    if (cur_y >= term_rows - 1) {
        cur_y = term_rows - 1;
        term_scroll_up(1);
    } else {
        cur_y++;
    }
}

static void term_ctl(UBYTE b)
{
    switch (b) {
    case 0x08: /* BS: move, do not erase */
        if (cur_x > 0)
            cur_x--;
        wrap_pending = 0;
        break;
    case 0x09: /* TAB: 8-column stops, clamped to the last column */
        cur_x = (cur_x & ~7) + 8;
        if (cur_x > COLS - 1)
            cur_x = COLS - 1;
        wrap_pending = 0;
        break;
    case 0x0A:
        wrap_pending = 0;
        term_linefeed();
        break;
    case 0x0C: /* FF: clear and home, as on the console it replaces */
        term_rect_fill(0, 0, COLS, term_rows, term_bg_pen());
        cur_x = cur_y = 0;
        wrap_pending = 0;
        break;
    case 0x0D:
        cur_x = 0;
        wrap_pending = 0;
        break;
    default: /* BEL and the rest: ignored */
        break;
    }
}

static void term_printable(UBYTE ch)
{
    if (wrap_pending) {
        wrap_pending = 0;
        cur_x = 0;
        term_linefeed();
    }
    term_glyph(cur_x, cur_y, ch);
    if (cur_x >= COLS - 1)
        wrap_pending = 1;
    else
        cur_x++;
}

static WORD fmt_num(UBYTE *buf, WORD n, WORD v)
{
    UBYTE d[5];
    WORD k = 0;
    if (!v)
        d[k++] = '0';
    while (v) {
        d[k++] = (UBYTE)('0' + v % 10);
        v /= 10;
    }
    while (k)
        buf[n++] = d[--k];
    return n;
}

/* DSR: answered here on the serial line, so it works identically on
 * Kickstart and AROS (the console used to answer it on Kickstart only). */
static void term_dsr(WORD which)
{
    UBYTE buf[12];
    WORD n = 0;
    if (which == 6) { /* CPR: cursor position, 1-based */
        buf[n++] = 0x1B;
        buf[n++] = '[';
        n = fmt_num(buf, n, cur_y + 1);
        buf[n++] = ';';
        n = fmt_num(buf, n, cur_x + 1);
        buf[n++] = 'R';
        ser_write(buf, n);
    } else if (which == 5) { /* device status: ready */
        ser_write((const UBYTE *)"\x1B[0n", 4);
    }
}

static WORD pn1(WORD i)
{
    return p_params[i] ? p_params[i] : 1;
}

/* Shared tail for every cursor motion: absolute and relative moves both
 * clamp to the screen and cancel a pending wrap. */
static void term_moved(void)
{
    if (cur_x < 0)
        cur_x = 0;
    if (cur_x > COLS - 1)
        cur_x = COLS - 1;
    if (cur_y < 0)
        cur_y = 0;
    if (cur_y > term_rows - 1)
        cur_y = term_rows - 1;
    wrap_pending = 0;
}

static void term_reset(void);

static void term_csi(UBYTE final)
{
    WORD i, np;

    if (p_priv) {
        /* DEC private modes: only cursor visibility (ESC[?25l/h)
         * matters to BBS output; the rest parse and drop. */
        if (p_params[0] == 25 && (final == 'h' || final == 'l'))
            cursor_visible = (final == 'h');
        return;
    }
    if (p_ignore)
        return;

    switch (final) {
    case 'A':
        cur_y -= pn1(0);
        term_moved();
        break;
    case 'B':
        cur_y += pn1(0);
        term_moved();
        break;
    case 'C':
        cur_x += pn1(0);
        term_moved();
        break;
    case 'D':
        cur_x -= pn1(0);
        term_moved();
        break;
    case 'E':
        cur_x = 0;
        cur_y += pn1(0);
        term_moved();
        break;
    case 'F':
        cur_x = 0;
        cur_y -= pn1(0);
        term_moved();
        break;
    case 'G':
        cur_x = pn1(0) - 1;
        term_moved();
        break;
    case 'f': /* HVP: same motion as CUP */
    case 'H':
        cur_y = pn1(0) - 1;
        cur_x = pn1(1) - 1;
        term_moved();
        break;
    case 'J':
        term_erase_display(p_params[0]);
        break;
    case 'K':
        term_erase_line(p_params[0]);
        break;
    case 'L':
        term_insert_lines(pn1(0));
        break;
    case 'M':
        term_delete_lines(pn1(0));
        break;
    case '@':
        term_insert_chars(pn1(0));
        break;
    case 'P':
        term_delete_chars(pn1(0));
        break;
    case 'S':
        term_scroll_up(pn1(0));
        break;
    case 'T':
        term_scroll_down(pn1(0));
        break;
    case 'm':
        np = p_np + 1;
        for (i = 0; i < np; i++) {
            WORD v = p_params[i];
            if (v == 38 || v == 48) {
                /* Extended colour introducers carry sub-arguments
                 * (38;5;N, 38;2;R;G;B) that must be consumed, not
                 * executed - N would otherwise read as blink or the
                 * like. 16 pens have nothing to map them onto, so
                 * they are skipped whole. */
                if (i + 1 < np && p_params[i + 1] == 5)
                    i += 2;
                else if (i + 1 < np && p_params[i + 1] == 2)
                    i += 4;
                continue;
            }
            term_sgr(v);
        }
        break;
    case 's':
        sav_x = cur_x;
        sav_y = cur_y;
        break;
    case 'u':
        cur_x = sav_x;
        cur_y = sav_y;
        term_moved();
        break;
    case 'n':
        term_dsr(p_params[0]);
        break;
    default:
        /* Anything else: a real terminal parses and ignores. */
        break;
    }
}

static void term_csi_begin(void)
{
    WORD i;
    for (i = 0; i < P_MAX; i++)
        p_params[i] = 0;
    p_np = 0;
    p_have = 0;
    p_priv = 0;
    p_ignore = 0;
    p_state = 3;
}

/* One byte of BBS output. */
static void term_feed(UBYTE b)
{
    switch (p_state) {
    case 1: /* ESC seen */
        if (b == '[') {
            term_csi_begin();
            return;
        }
        if (b == 0x1B)
            return; /* ESC restarts ESC */
        if (b >= 0x20 && b <= 0x2F) {
            p_state = 2;
            return;
        }
        p_state = 0;
        if (b == 'c')
            term_reset(); /* RIS */
        else if (b == '7') {
            sav_x = cur_x;
            sav_y = cur_y;
        } else if (b == '8') {
            cur_x = sav_x;
            cur_y = sav_y;
            term_moved();
        }
        /* every other ESC sequence: parsed and dropped */
        return;
    case 2: /* ESC intermediates: swallow through the final byte */
        if (b >= 0x30 && b <= 0x7E)
            p_state = 0;
        return;
    case 3: /* CSI body */
        if (b >= '0' && b <= '9') {
            WORD v = p_params[p_np];
            if (v < 1000)
                p_params[p_np] = v * 10 + (b - '0');
            p_have = 1;
        } else if (b == ';') {
            if (p_np < P_MAX - 1)
                p_np++;
            p_have = 1;
        } else if (b == '?' && !p_have && !p_priv) {
            p_priv = b;
        } else if (b == 0x1B) {
            p_state = 1; /* aborted sequence, ESC restarts */
        } else if (b == 0x9B) {
            term_csi_begin(); /* ditto for the 8-bit introducer */
        } else if (b < 0x20) {
            term_ctl(b); /* ECMA-48: controls execute mid-sequence */
        } else if (b >= 0x40 && b <= 0x7E) {
            p_state = 0;
            term_csi(b);
        } else {
            /* other private markers, intermediates, ':' subparameters
             * (ESC[<...m, ESC[0;40 D, ESC[38:5:201m): parse to the
             * final byte, execute nothing */
            p_ignore = 1;
        }
        return;
    default:
        break;
    }

    /* plain data */
    if (b == 0x1B) {
        p_state = 1;
        return;
    }
    if (b == 0x9B) {
        term_csi_begin();
        return;
    }
    if (b < 0x20) {
        term_ctl(b);
        return;
    }
    term_printable(b);
}

static void term_puts(const char *s)
{
    while (*s)
        term_feed((UBYTE)*s++);
}

static void term_num(ULONG v)
{
    UBYTE d[10];
    WORD k = 0;
    if (!v)
        d[k++] = '0';
    while (v) {
        d[k++] = (UBYTE)('0' + v % 10);
        v /= 10;
    }
    while (k)
        term_feed(d[--k]);
}

/* RIS (ESC c), and the power-on state. */
static void term_reset(void)
{
    term_sgr(0);
    cur_x = cur_y = sav_x = sav_y = 0;
    wrap_pending = 0;
    cursor_visible = 1;
    cursor_drawn = 0;
    term_rect_fill(0, 0, COLS, term_rows, 0);
}

/* The caller must open both the Screen and the TextFont before calling
 * term_init(). This function uses these resources to extract glyphs from
 * the supplied font and to initialize the terminal renderer using the
 * screen's BitMap. */
static int term_init(struct Screen *screen, struct TextFont *tf)
{
    WORD i;

    /* The engine's glyphs */
    font_extract(tf);

    /* RastPort.BitMap is the authoritative bitmap on every OS (the
     * embedded Screen.BitMap is a compatibility copy on V39+/AROS). */
    term_bm = screen->RastPort.BitMap;
    if (term_bm->Depth < 4)
        return 1;
    for (i = 0; i < 4; i++) {
        term_plane[i] = term_bm->Planes[i];
        if (!term_plane[i])
            return 1;
    }
    term_bpr = (WORD)term_bm->BytesPerRow;
    term_rows = screen->Height >> 3;
    term_reset();
    return 0;
}
