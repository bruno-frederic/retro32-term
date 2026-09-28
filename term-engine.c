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
 * - A character cell is 8 pixels high and as wide as the font: 8 hires
 *   pixels are exactly one byte per bitplane (the C64 font's 16, two), so
 *   a glyph is 32 (64) byte writes with foreground and background masks;
 *   no blitter, no read-modify-write.
 * - Glyphs come from the ROM Topaz 8 (see font_extract), so the art
 *   renders in the face it was drawn for on every Kickstart and AROS.
 * - Scrolls, erases and insert/delete go through BltBitMap on the
 *   screen bitmap: minterm 0xFF or 0x00 with a plane mask paints any
 *   pen, and BltBitMap picks the descending mode by itself when the
 *   rectangles overlap. The one rule is WaitBlit before the next CPU
 *   write into the planes (term_blit_sync).
 * - Drawing straight into the bitmap is only right while nothing lies
 *   over the terminal: another window, a requester, an open menu owns
 *   those pixels, and the terminal must neither draw over them nor
 *   scroll them along. Then (term_covered), and on a bitmap that is not
 *   planar (RTG), the same operations go through the terminal window's
 *   RastPort instead: Text() in runs, RectFill(), ScrollRaster() and a
 *   COMPLEMENT fill for the cursor. Its layer keeps what is covered
 *   (smart refresh) and gives it back when the window over it goes.
 * - PC semantics throughout: the palette is the 16-colour CGA set in
 *   ANSI order, bold folds into bright foregrounds, blink into bright
 *   backgrounds (iCE colours), erases fill with the current background
 *   (BCE), ESC[2J homes the cursor like ANSI.SYS, autowrap is deferred
 *   DEC-style (a glyph in the last column parks the cursor there and the
 *   next glyph wraps), and DSR 6 is answered,
 *   on Kickstart and AROS alike.
 *
 * Runs on Kickstart 1.3 as well as 2.0+ and the AROS ROM Copperline
 * bundles. Public domain (see LICENSE).
 *
 * Prerequisites required by this module for term_init() and
 * term_init_area():
 * - Screen   : must already be opened
 * - TextFont : must already be opened; 8 pixels high, 8 to 16 wide
 * Additional requirements:
 * - Caller must include the necessary NDK headers before including this
 *   module.
 * - The caller must define the send_data() function to allow the
 *   terminal engine to answer to DSR.
 */

#define COLS 80          /* the most columns (the 8-pixel font) */

static struct BitMap *term_bm; /* the screen's bitmap */
static UBYTE *term_plane[4];
static WORD term_bpr;  /* bytes per plane row (80 at 640 wide) */
static WORD term_rows; /* text rows: the area's height / 8 */

/* Topaz 8 glyphs, one byte per row, flat for fast cell addressing. */
static UBYTE font8[256 * 8];
/* A font of 9 to 16 pixel wide cells (the C64's, 16x8: 40 columns): one
 * word per row. term_xs is the cell width's shift, 3 or 4. */
static UWORD font16[256 * 8];
static WORD term_xs = 3;
static WORD term_cols = COLS;   /* columns: the area's width in cells, at most COLS */
static WORD term_w;             /* the area's width in pixels */

static WORD cur_x, cur_y;
static WORD sav_x, sav_y; /* CSI s/u (and ESC 7/8) cursor save slot */
static LONG term_row_stride;  /* bytes per character row (term_bpr * 8), computed once */
static LONG term_row_base;    /* cur_y * term_row_stride, kept in sync by term_sync_row_base() */
static WORD atr_fg = 7;   /* base colours 0-7; brightness lives in */
static WORD atr_bg;       /* atr_bold / atr_blink */
static WORD atr_bold, atr_blink, atr_inv, atr_under;
static UBYTE term_pen_fg = 7, term_pen_bg; /* Cached resolved pens */
static WORD wrap_pending;
static WORD cursor_visible = 1; /* ESC[?25l/h */
static WORD cursor_drawn;       /* cursor cell is currently inverted */
static WORD blit_pending;       /* a BltBitMap has been started */

/* The terminal's place in the screen bitmap: top-left pixel (term_x0 a
 * multiple of 8 for direct drawing), term_cols columns by term_rows rows. */
static WORD term_x0, term_y0;

/* Drawing through a RastPort (see the header comment): term_rp is the
 * window's RastPort while it is in use, NULL while drawing directly. A
 * pixel (x, y) of the bitmap is (x - term_rp_dx, y - term_rp_dy) in it. */
static struct RastPort *term_rp;
static struct RastPort *term_win_rp;  /* the window's; NULL: direct only */
static WORD term_rp_dx, term_rp_dy;
static WORD term_direct_ok;           /* planar, 4+ planes, byte-aligned area */
static WORD term_pens_ansi = 1;       /* pens 0-15 are the ANSI colours (direct drawing needs it) */
/* Not 0: a glyph takes the long way -- the RastPort, or 16-pixel cells.
 * The 8-pixel direct path pays one test for both. */
static WORD term_alt;
static WORD term_baseline;            /* the font's, for Move() before Text() */
static UBYTE term_pen_map[16];        /* ANSI colour -> screen pen (RastPort path) */

/* Glyphs waiting for one Text() call: same row, adjacent, same pens. */
static UBYTE term_run[COLS];
static WORD term_run_n, term_run_x, term_run_y;
static UBYTE term_run_fg, term_run_bg, term_run_ul;

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

    if (tf->tf_XSize > 8) {         /* up to 16 pixels: one word per row */
        for (c = 0; c < 256 * 8; c++)
            font16[c] = 0;
        for (c = tf->tf_LoChar; c <= tf->tf_HiChar; c++) {
            ULONG bitoff = loc[c - tf->tf_LoChar] >> 16;
            WORD bits = (WORD)(loc[c - tf->tf_LoChar] & 0xFFFF);
            const UBYTE *src = data + (bitoff >> 3);
            WORD sh = (WORD)(bitoff & 7);
            UWORD *dst = &font16[c << 3];
            for (r = 0; r < ys; r++) {
                ULONG g = (ULONG)src[0] << 16 | (ULONG)src[1] << 8 | src[2];
                g = (g << sh) >> 8 & 0xFFFF;
                if (bits < 16)
                    g &= (0xFFFF0000UL >> bits) & 0xFFFF;
                dst[r] = (UWORD)g;
                src += tf->tf_Modulo;
            }
        }
        term_xs = 4;
        return;
    }
    term_xs = 3;
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

#define TERM_PX(x) ((WORD)(term_x0 + ((x) << term_xs) - term_rp_dx))
#define TERM_PY(y) ((WORD)(term_y0 + ((y) << 3) - term_rp_dy))

/* Draw the waiting glyphs (RastPort path). */
static void term_run_flush(void)
{
    struct RastPort *rp = term_rp;
    WORD x, y;

    if (!term_run_n)
        return;
    x = TERM_PX(term_run_x);
    y = TERM_PY(term_run_y);
    SetAPen(rp, term_pen_map[term_run_fg]);
    SetBPen(rp, term_pen_map[term_run_bg]);
    SetDrMd(rp, JAM2);
    Move(rp, x, y + term_baseline);
    Text(rp, (STRPTR)term_run, term_run_n);
    if (term_run_ul)
        RectFill(rp, x, y + 7, x + (term_run_n << term_xs) - 1, y + 7);
    term_run_n = 0;
    blit_pending = 1;
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
    WORD px, py;
    if (w <= 0 || h <= 0)
        return;
    if (term_rp) {
        term_run_flush();
        SetAPen(term_rp, term_pen_map[pen & 0xF]);
        SetDrMd(term_rp, JAM1);
        RectFill(term_rp, TERM_PX(x), TERM_PY(y), TERM_PX(x + w) - 1, TERM_PY(y + h) - 1);
        blit_pending = 1;
        return;
    }
    px = term_x0 + (x << term_xs);
    py = term_y0 + (y << 3);
    if (setm)
        BltBitMap(term_bm, px, py, term_bm, px, py,
                  w << term_xs, h << 3, 0xFF, setm, NULL);
    if (setm != 0xF)
        BltBitMap(term_bm, px, py, term_bm, px, py,
                  w << term_xs, h << 3, 0x00, setm ^ 0xF, NULL);
    blit_pending = 1;
}

/* Move the cells of the rectangle x, y, w, h by (dx, dy) cells -- the
 * cells moved out fall off its edge, the ones uncovered are filled with
 * pen. On the RastPort path one ScrollRaster(), which moves what other
 * windows cover too. */
static void term_rect_scroll(WORD x, WORD y, WORD w, WORD h, WORD dx, WORD dy, WORD pen)
{
    WORD adx = dx < 0 ? -dx : dx, ady = dy < 0 ? -dy : dy;

    if (w <= 0 || h <= 0)
        return;
    if (adx >= w || ady >= h) {
        term_rect_fill(x, y, w, h, pen);
        return;
    }
    if (term_rp) {
        /* The uncovered strip is filled below: ScrollRaster() leaves it to a
         * backfill hook, when the window has one, instead of BgPen (V39). */
        term_run_flush();
        SetBPen(term_rp, term_pen_map[pen & 0xF]);
        ScrollRaster(term_rp, -dx << term_xs, -dy << 3,
                     TERM_PX(x), TERM_PY(y), TERM_PX(x + w) - 1, TERM_PY(y + h) - 1);
        blit_pending = 1;
    } else {
        /* copy what stays, then fill what the move uncovered */
        BltBitMap(term_bm, term_x0 + ((x + (dx < 0 ? adx : 0)) << term_xs), term_y0 + ((y + (dy < 0 ? ady : 0)) << 3),
                  term_bm, term_x0 + ((x + (dx > 0 ? adx : 0)) << term_xs), term_y0 + ((y + (dy > 0 ? ady : 0)) << 3),
                  (w - adx) << term_xs, (h - ady) << 3, 0xC0, 0xF, NULL);
        blit_pending = 1;
    }
    if (dy > 0)
        term_rect_fill(x, y, w, ady, pen);
    else if (dy < 0)
        term_rect_fill(x, y + h - ady, w, ady, pen);
    if (dx > 0)
        term_rect_fill(x, y, adx, h, pen);
    else if (dx < 0)
        term_rect_fill(x + w - adx, y, adx, h, pen);
}

/* Resolve the current SGR attributes to foreground and background pens. */
static void term_update_pens(void)
{
    WORD fg = atr_fg + (atr_bold ? 8 : 0);
    WORD bg = atr_bg + (atr_blink ? 8 : 0);

    term_pen_fg = (UBYTE)(atr_inv ? bg : fg);
    term_pen_bg = (UBYTE)(atr_inv ? fg : bg);
}

 /* Update the cached row offset based on cur_y.
 *
 * This is called only when cur_y changes (roughly once per line),
 * instead of from the per‑glyph rendering path. Doing the multiply
 * here means we pay the cost once per line rather than once per
 * character drawn on that line.
 */
static void term_sync_row_base(void)
{
    term_row_base = (LONG)cur_y * term_row_stride + (LONG)term_y0 * term_bpr + (term_x0 >> 3);
}

/* The glyph at column x of the current row, in a 16-pixel cell (two bytes
 * per plane row). */
static void term_glyph_wide(WORD x, UBYTE ch)
{
    const UWORD *g = &font16[(UWORD)ch << 3];
    LONG off = term_row_base + (x << 1);
    UBYTE fg = term_pen_fg, bg = term_pen_bg;
    WORD p, r;

    term_blit_sync();
    for (p = 0; p < 4; p++) {
        UBYTE f = (UBYTE)((fg >> p) & 1), b = (UBYTE)((bg >> p) & 1);
        UBYTE *dst = term_plane[p] + off;
        for (r = 0; r < 8; r++) {
            UWORD v = f == b ? (f ? 0xFFFF : 0) : f ? g[r] : (UWORD)~g[r];
            dst[0] = (UBYTE)(v >> 8);
            dst[1] = (UBYTE)v;
            dst += term_bpr;
        }
        if (atr_under) {
            dst -= term_bpr;
            dst[0] = dst[1] = f ? 0xFF : 0x00;
        }
    }
}

/* Draws the glyph at column x, on the current row.

 * The row isn't a parameter: it's read from term_row_base, kept in sync
 * with cur_y by term_sync_row_base(), so callers never need to pass it
 * (and term_glyph() never needs to multiply for it).
 * Only caller: term_printable(), with x == cur_x. */
static void term_glyph(WORD x, UBYTE ch)
{
    const UBYTE *g = &font8[(UWORD)ch << 3];
    LONG off = term_row_base + x;
    UBYTE fg = term_pen_fg, bg = term_pen_bg;
    WORD bpr = term_bpr;    /* Keep term_bpr in a register for 32 writes. */
    WORD p, r;
    UBYTE **plane = term_plane;

    if (term_alt) {
        if (!term_rp) {
            term_glyph_wide(x, ch);
            return;
        }
        /* collect a run for one Text() */
        if (term_run_n && (x != term_run_x + term_run_n || cur_y != term_run_y
                           || fg != term_run_fg || bg != term_run_bg || atr_under != term_run_ul))
            term_run_flush();
        if (!term_run_n) {
            term_run_x = x;
            term_run_y = cur_y;
            term_run_fg = fg;
            term_run_bg = bg;
            term_run_ul = (UBYTE)atr_under;
        }
        term_run[term_run_n++] = ch;
        return;
    }
    term_blit_sync();

    for (p = 0; p < 4; p++) {
        UBYTE f = (UBYTE)((fg >> p) & 1);
        UBYTE b = (UBYTE)((bg >> p) & 1);
        UBYTE *dst = *plane++ + off;

        /* A plane is either constant, the glyph, or its inverse.  This
         * avoids two masks and three byte operations for every pixel row.
         * It matters for ANSI art, where SGR changes far less often than
         * printable characters. */
        if (f == b) {
            UBYTE v = f ? 0xFF : 0x00;
            for (r = 0; r < 8; r++) {
                *dst = v;
                dst += bpr;
            }
        } else if (f) {
            for (r = 0; r < 8; r++) {
                *dst = *g++;
                dst += bpr;
            }
            g -= 8;
        } else {
            for (r = 0; r < 8; r++) {
                *dst = (UBYTE)~*g++;
                dst += bpr;
            }
            g -= 8;
        }
        if (atr_under)
            *(dst - bpr) = f ? 0xFF : 0x00;
    }
}

/* The cursor is the cell under it with every plane byte inverted (pen
 * XOR 15), which is self-restoring: flipping twice puts the cell back.
 * Drawing only ever happens with the cursor hidden (see drain_serial),
 * so glyphs never land on an inverted cell. */
static void term_cursor_flip(void)
{
    LONG off = term_row_base + cur_x;
    WORD p, r;

    if (term_rp) {          /* pen XOR 15, as below */
        UBYTE mask = term_rp->Mask;
        term_run_flush();
        SetDrMd(term_rp, COMPLEMENT);
        term_rp->Mask = 0x0F;
        RectFill(term_rp, TERM_PX(cur_x), TERM_PY(cur_y), TERM_PX(cur_x + 1) - 1, TERM_PY(cur_y + 1) - 1);
        term_rp->Mask = mask;
        SetDrMd(term_rp, JAM2);
        blit_pending = 1;
        return;
    }
    term_blit_sync();
    if (term_xs == 4)
        off += cur_x;           /* 16-pixel cells: two bytes, from 2 * x */
    for (p = 0; p < 4; p++) {
        UBYTE *dst = term_plane[p] + off;
        for (r = 0; r < 8; r++) {
            *dst ^= 0xFF;
            if (term_xs == 4)
                dst[1] ^= 0xFF;
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
    WORD bg = term_pen_bg;

    /* The line feed at the bottom: the most frequent scroll, kept short. */
    if (!term_rp && n < term_rows) {
        BltBitMap(term_bm, term_x0, term_y0 + (n << 3), term_bm, term_x0, term_y0,
                  term_cols << term_xs, (term_rows - n) << 3, 0xC0, 0xF, NULL);
        blit_pending = 1;
        term_rect_fill(0, term_rows - n, term_cols, n, bg);
        return;
    }
    term_rect_scroll(0, 0, term_cols, term_rows, 0, -n, bg);
}

static void term_scroll_down(WORD n)
{
    term_rect_scroll(0, 0, term_cols, term_rows, 0, n, term_pen_bg);
}

static void term_erase_display(WORD mode)
{
    WORD bg = term_pen_bg;
    if (mode >= 2) {
        /* ANSI.SYS semantics: 2J (and xterm's 3J) clears and homes. */
        term_rect_fill(0, 0, term_cols, term_rows, bg);
        cur_x = cur_y = 0;
        wrap_pending = 0;
        term_sync_row_base();
    } else if (mode == 1) {
        term_rect_fill(0, 0, term_cols, cur_y, bg);
        term_rect_fill(0, cur_y, cur_x + 1, 1, bg);
    } else {
        term_rect_fill(cur_x, cur_y, term_cols - cur_x, 1, bg);
        term_rect_fill(0, cur_y + 1, term_cols, term_rows - 1 - cur_y, bg);
    }
}

static void term_erase_line(WORD mode)
{
    WORD bg = term_pen_bg;
    if (mode >= 2)
        term_rect_fill(0, cur_y, term_cols, 1, bg);
    else if (mode == 1)
        term_rect_fill(0, cur_y, cur_x + 1, 1, bg);
    else
        term_rect_fill(cur_x, cur_y, term_cols - cur_x, 1, bg);
}

static void term_insert_lines(WORD n)
{
    term_rect_scroll(0, cur_y, term_cols, term_rows - cur_y, 0, n, term_pen_bg);
}

static void term_delete_lines(WORD n)
{
    term_rect_scroll(0, cur_y, term_cols, term_rows - cur_y, 0, -n, term_pen_bg);
}

static void term_insert_chars(WORD n)
{
    term_rect_scroll(cur_x, cur_y, term_cols - cur_x, 1, n, 0, term_pen_bg);
}

static void term_delete_chars(WORD n)
{
    term_rect_scroll(cur_x, cur_y, term_cols - cur_x, 1, -n, 0, term_pen_bg);
}

/* https://syncterm.net/cterm.html#_csi_ps_m_select_graphic_rendition_sgr */
#ifdef __SASC
static void __inline
#else
static inline void
#endif
term_sgr(WORD v)
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
    term_sync_row_base();
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
        if (cur_x > term_cols - 1)
            cur_x = term_cols - 1;
        wrap_pending = 0;
        break;
    case 0x0A:
        wrap_pending = 0;
        term_linefeed();
        break;
    case 0x0C: /* FF: clear and home, as on the console it replaces */
        term_rect_fill(0, 0, term_cols, term_rows, term_pen_bg);
        cur_x = cur_y = 0;
        wrap_pending = 0;
        term_sync_row_base();
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
    term_glyph(cur_x, ch);
    if (cur_x >= term_cols - 1)
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
        send_data(buf, n);
    } else if (which == 5) { /* device status: ready */
        send_data((const UBYTE *)"\x1B[0n", 4);
    }
}

static WORD pn1(WORD i)
{
    return (WORD) (p_params[i] ? p_params[i] : 1);
}

/* Shared tail for every cursor motion: absolute and relative moves both
 * clamp to the screen and cancel a pending wrap. */
static void term_moved(void)
{
    if (cur_x < 0)
        cur_x = 0;
    if (cur_x > term_cols - 1)
        cur_x = term_cols - 1;
    if (cur_y < 0)
        cur_y = 0;
    if (cur_y > term_rows - 1)
        cur_y = term_rows - 1;
    wrap_pending = 0;
    term_sync_row_base();
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
        /* Resolve fore/background pens only when SGR attributes change */
        term_update_pens();
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
    /* Parameters are initialized lazily instead of clearing all P_MAX slots
     * at ESC[ time.
     * Resetting all sixteen slots here made every CSI introducer write
     * 32 bytes, although BBS output normally has one or two parameters.
     * term_feed() initializes each subsequent p_params[] entry when it
     * encounters a semicolon. */
    p_params[0] = 0;
    p_np = 0;
    p_have = 0;
    p_priv = 0;
    p_ignore = 0;
    p_state = 3;
}

/* One byte of BBS output.
 * inline: called on every byte received (the hottest path in the
 * program); without it, VBCC compiles a real JSR/RTS here with the
 * byte pushed/popped on the stack (measured: ~5% slower). */
#ifdef __SASC
static void __inline
#else
static inline void
#endif
term_feed(UBYTE b)
{
    switch (p_state) {

    /* Plain text is by far the common case.  Test it before the escape
     * state dispatch: on a 68000 this avoids the three failed comparisons
     * generated by the switch for every ordinary byte. */
    case 0: /* plain data */
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
        return;
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
            if (p_np < P_MAX - 1) {
                p_np++;
                /* Initialize the newly selected parameter lazily.
                 * This also makes empty parameters (for example ESC[;31m)
                 * read as zero. */
                p_params[p_np] = 0;
            }
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
    term_update_pens();
    cur_x = cur_y = sav_x = sav_y = 0;
    wrap_pending = 0;
    cursor_visible = 1;
    cursor_drawn = 0;
    term_sync_row_base();
    term_rect_fill(0, 0, term_cols, term_rows, 0);
}

/* Draw what waits (the RastPort path collects glyphs into runs). Call it
 * after a batch of term_feed(). */
static void term_flush(void)
{
    if (term_rp)
        term_run_flush();
}

/* Something lies over the terminal (another window, an open menu): draw
 * through the RastPort until it is gone. Only switches when it can:
 * without a window RastPort there is only the direct way, and a bitmap
 * the engine cannot draw into directly always takes the RastPort. */
static void term_covered(WORD covered)
{
    struct RastPort *want = (covered || !term_direct_ok || !term_pens_ansi) ? term_win_rp : NULL;

    if (want == term_rp)
        return;
    term_flush();
    term_rp = want;
    term_alt = term_rp || term_xs != 3;
    blit_pending = 1;       /* the RastPort's blits may still run */
}

/* The pens the 16 ANSI colours are on (NULL: pens 0-15, a screen of the
 * engine's own). Other pens are drawn only through the RastPort: direct
 * drawing writes the colour number into the planes. */
static void term_set_pens(const UBYTE *pens)
{
    WORD i;

    term_pens_ansi = 1;
    for (i = 0; i < 16; i++) {
        term_pen_map[i] = pens ? pens[i] : (UBYTE)i;
        if (term_pen_map[i] != i)
            term_pens_ansi = 0;
    }
    if (!term_pens_ansi && term_win_rp && !term_rp) {
        term_rp = term_win_rp;
        blit_pending = 1;
    }
    term_alt = term_rp || term_xs != 3;
}

/* Another font of the same cell width (the C64's upper-case/graphics and
 * lower-case sets): new glyphs for what comes next, the screen stays. */
static void term_set_font(struct TextFont *tf)
{
    term_flush();
    font_extract(tf);
    if (term_win_rp)
        SetFont(term_win_rp, tf);
}

/* The terminal in the rectangle x0, y0, w x h of screen's bitmap: as many
 * columns of font tf's cells as fit, at most COLS, h / 8 rows. rp is the RastPort of the window it
 * lies in, whose (0, 0) is pixel (rpdx, rpdy) of the bitmap, for drawing
 * while something covers it and on a bitmap that is not planar; NULL:
 * direct drawing only. 0 when the terminal can be drawn. */
static int term_init_area(struct Screen *screen, struct RastPort *rp, WORD rpdx, WORD rpdy,
                          WORD x0, WORD y0, WORD w, WORD h, struct TextFont *tf)
{
    WORD i;

    if (screen == NULL || tf == NULL || h < 8)
        return 1;

    /* The engine's glyphs */
    font_extract(tf);

    /* RastPort.BitMap is the authoritative bitmap on every OS (the
     * embedded Screen.BitMap is a compatibility copy on V39+/AROS). */
    term_bm = screen->RastPort.BitMap;
    /* Exactly 4 planes: the direct path writes planes 0-3 only, so on a
     * deeper screen the upper planes' bits (a window's backfill) would
     * show through as other colours. */
    term_w = w;
    term_cols = (WORD)(w >> term_xs) < COLS ? (WORD)(w >> term_xs) : COLS;
    term_direct_ok = term_bm->Depth == 4 && (x0 & 7) == 0;
    if (((struct Library *)GfxBase)->lib_Version >= 39
        && !(GetBitMapAttr(term_bm, BMA_FLAGS) & BMF_STANDARD))
        term_direct_ok = 0;             /* RTG: not bitplanes */
    for (i = 0; i < 4 && term_direct_ok; i++) {
        term_plane[i] = term_bm->Planes[i];
        if (!term_plane[i])
            term_direct_ok = 0;
    }
    if (!term_direct_ok && !rp)
        return 1;
    term_bpr = (WORD)term_bm->BytesPerRow;
    /* Fixed for the life of the screen, so computed once here instead
     * of on every glyph. */
    term_row_stride = (LONG)term_bpr << 3;
    term_x0 = x0;
    term_y0 = y0;
    term_rows = h >> 3;
    term_win_rp = rp;
    term_rp_dx = rpdx;
    term_rp_dy = rpdy;
    term_baseline = tf->tf_Baseline;
    term_run_n = 0;
    if (rp)
        SetFont(rp, tf);
    term_rp = term_direct_ok ? NULL : rp;
    term_set_pens(NULL);
    term_reset();
    return 0;
}

/* The caller must open both the Screen and the TextFont before calling
 * term_init(). This function uses these resources to extract glyphs from
 * the supplied font and to initialize the terminal renderer using the
 * screen's BitMap, the whole of it, drawn directly. */
static int term_init(struct Screen *screen, struct TextFont *tf)
{
    if (screen == NULL)
        return 1;
    return term_init_area(screen, NULL, 0, 0, 0, 0, screen->Width, screen->Height, tf);
}
