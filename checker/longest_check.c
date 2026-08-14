/*
 * longest_check.c -- an independent FIDE-rules chess checker.
 * ===========================================================================
 *
 * WHY THIS FILE EXISTS
 *
 *   The reference game in data/longest.pgn was built and replayed with
 *   python-chess.  A reader who wants to be convinced the game is legal
 *   should not have to take one library's move generator on faith.  This
 *   program re-derives the rules from the FIDE Laws of Chess and re-checks
 *   the game with a deliberately different implementation.
 *
 *   Independence is the entire point, so this file was written without
 *   reading python-chess.  Where a rule is subtle, the governing FIDE
 *   article is cited in a comment, numbered as in the Laws effective
 *   1 January 2023: Art. 3.7 (pawn moves, en passant, promotion),
 *   Art. 3.8 (castling), Art. 5.2.2 (dead position), Art. 9.2.2
 *   (identity of positions), Art. 9.6.1 / 9.6.2 (fivefold repetition and the
 *   75-move rule).
 *
 *   The two implementations also differ in representation.  python-chess is
 *   bitboard based; this file is a 0x88 mailbox with pseudo-legal generation
 *   filtered by make / king-attacked / unmake.  Implementations that share a
 *   representation tend to share bugs.  Implementations that do not, do not.
 *
 * BUILD
 *
 *   gcc -std=c99 -O2 -Wall -Wextra -Werror -pedantic \
 *       -o /tmp/lc checker/longest_check.c
 *
 *   One translation unit, C99, standard library only, and no dynamic
 *   allocation anywhere: every buffer in this file is a fixed-size array.
 *
 * WHAT IT DOES
 *
 *   The board, FEN input/output, legal move generation, perft (the move
 *   generator's self-test) against an external table of authoritative node
 *   counts, a table of hand-written rule cases that pins the individual Laws
 *   by name, a PGN/SAN reader, and then adjudication: the FIDE rules that end
 *   a game on their own -- checkmate, stalemate, insufficient material,
 *   fivefold repetition (Art. 9.6.1) and the 75-move rule (Art. 9.6.2) --
 *   applied after every ply, with an optional per-ply trace.
 *
 *   It also re-runs the four claims about the rules of chess that the
 *   home-rank lemma in src/long_chess/bound/invariant.py leans on -- [H1]
 *   [H2] [H5] [H6] -- over a corpus of positions this program walks for
 *   itself.  That check exists on the python side too, which is precisely
 *   why it is here: passing it there leaves python-chess inside the chain of
 *   things a reader has to trust.  See --corpus.
 *
 *   The reader is part of the independence claim, not a convenience.  SAN is
 *   not a move list: "Nge4" says where a knight is going and leaves the reader
 *   to work out which knight can legally get there, so resolving SAN is move
 *   generation.  Letting some other program parse the file and hand this one
 *   the resulting moves would leave that program's move generator inside the
 *   chain of things a reader has to trust.
 *
 *   Nothing about the game under test is compiled in.  How long that game is
 *   and how it ends are claims, supplied on the command line as --expect-plies
 *   and --expect-termination and compared against what the replay actually
 *   found.  MAX_GAME_PLIES is the size of an array and nothing else; it is set
 *   far above any plausible game precisely so that it cannot be mistaken for
 *   knowledge of the answer.
 *
 * USAGE
 *
 *   longest_check --perft "<FEN>" <depth>
 *   longest_check --perft-divide "<FEN>" <depth>
 *   longest_check --perft-suite [--max-depth D]
 *   longest_check --rule-cases
 *   longest_check --corpus <positions> [--seed S]
 *   longest_check <file.pgn> [--trace FILE] [--expect-plies N]
 *                            [--expect-termination NAME] [--dump-uci FILE]
 *                            [--dump-moves FILE]
 *
 *   Exit status: 0 accepted, 1 rejected (or an expectation not met),
 *   2 bad command line.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ------------------------------------------------------------------------ */
/* Fixed capacities.  Nothing in this program allocates.                     */
/* ------------------------------------------------------------------------ */

/* No chess position has more than 218 legal moves; 256 is a safe ceiling. */
#define MAX_MOVES 256

/* Reserved for the replay phase.  The game under test is far shorter than
 * this; the bound is deliberately generous so the program does not encode
 * any assumption about the length it is asked to verify. */
#define MAX_GAME_PLIES 65536
#define REPETITION_SLOTS 131072

/* A FEN string never exceeds ~90 bytes; round up for comfort. */
#define MAX_FEN 128

/* The longest movetext token in a PGN is a move number ("8849.") or a SAN
 * move ("Qa1xb2+"); 32 bytes is several times either. */
#define MAX_TOKEN 32

/* Art. 2.1-2.4: the array both players start from.  A PGN can only say
 * otherwise with a [FEN] tag, which the reader below refuses rather than
 * skips. */
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

/* ------------------------------------------------------------------------ */
/* Board representation: 0x88 mailbox.                                      */
/*                                                                          */
/* The board is a 16x8 array.  A square index packs rank in the high nibble */
/* and file in the low nibble, so a1 = 0x00, h1 = 0x07, a8 = 0x70,          */
/* h8 = 0x77.  The right-hand 8 columns of every rank are off-board padding.*/
/* An index is on the board exactly when (index & 0x88) == 0, which makes    */
/* the "did this ray fall off the edge" test a single mask -- including file */
/* wrap-around, which is the bug a plain 8x8 array invites.                  */
/* ------------------------------------------------------------------------ */

#define ON_BOARD(sq) ((sq) >= 0 && ((sq) & 0x88) == 0)
#define RANK_OF(sq) ((sq) >> 4)
#define FILE_OF(sq) ((sq) & 7)
#define SQUARE_OF(file, rank) (((rank) << 4) | (file))

#define SQ_NONE (-1)

enum {
    SQ_A1 = 0x00, SQ_B1 = 0x01, SQ_C1 = 0x02, SQ_D1 = 0x03,
    SQ_E1 = 0x04, SQ_F1 = 0x05, SQ_G1 = 0x06, SQ_H1 = 0x07,
    SQ_A8 = 0x70, SQ_B8 = 0x71, SQ_C8 = 0x72, SQ_D8 = 0x73,
    SQ_E8 = 0x74, SQ_F8 = 0x75, SQ_G8 = 0x76, SQ_H8 = 0x77
};

/* Piece encoding: colour in bit 3, type in bits 0-2.  EMPTY is 0, so the
 * colour of EMPTY is meaningless and every caller must test for EMPTY first. */
enum { EMPTY = 0, PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6 };
enum { WHITE = 0, BLACK = 1 };

#define MAKE_PIECE(colour, type) (((colour) << 3) | (type))
#define PIECE_TYPE(piece) ((piece) & 7)
#define PIECE_COLOUR(piece) (((piece) >> 3) & 1)

/* Castling rights, one bit each (Art. 3.8.2). */
enum {
    CASTLE_WK = 1,  /* White may castle kingside  (e1-g1, rook h1) */
    CASTLE_WQ = 2,  /* White may castle queenside (e1-c1, rook a1) */
    CASTLE_BK = 4,  /* Black may castle kingside  (e8-g8, rook h8) */
    CASTLE_BQ = 8   /* Black may castle queenside (e8-c8, rook a8) */
};

/* Move flags.  A move carries at most one of these. */
enum {
    MF_NORMAL       = 0,
    MF_DOUBLE_PUSH  = 1, /* pawn advanced two squares; sets the ep target   */
    MF_EN_PASSANT   = 2, /* pawn captured en passant (Art. 3.7.3.1-3.7.3.2) */
    MF_CASTLE_KING  = 4, /* kingside castling (Art. 3.8.2)                  */
    MF_CASTLE_QUEEN = 8  /* queenside castling (Art. 3.8.2)                 */
};

typedef struct {
    int board[128];        /* 0x88 mailbox; off-board slots stay EMPTY */
    int side_to_move;      /* WHITE or BLACK */
    int castling;          /* OR of the CASTLE_* bits */
    int ep_square;         /* square a pawn may be captured ON, or SQ_NONE */
    int halfmove_clock;    /* plies since the last capture or pawn move */
    int fullmove_number;   /* starts at 1, increments after Black's move */
    int king_square[2];    /* cached so the legality filter is cheap */
} Position;

typedef struct {
    int from;
    int to;
    int promotion;         /* EMPTY, or QUEEN / ROOK / BISHOP / KNIGHT */
    int flags;             /* one of the MF_* values */
} Move;

/* Everything make_move() destroys, so unmake_move() can put it back. */
typedef struct {
    Move move;
    int captured_piece;    /* EMPTY if the move was not a capture */
    int captured_square;   /* differs from move.to only for en passant */
    int castling;
    int ep_square;
    int halfmove_clock;
    int fullmove_number;
} Undo;

/* Ray and step offsets in 0x88 space.  A rank step is 16, a file step is 1. */
static const int KNIGHT_DIRS[8] = { -33, -31, -18, -14, 14, 18, 31, 33 };
static const int KING_DIRS[8]   = { -17, -16, -15,  -1,  1, 15, 16, 17 };
static const int BISHOP_DIRS[4] = { -17, -15, 15, 17 };
static const int ROOK_DIRS[4]   = { -16,  -1,  1, 16 };

/* Promotion choices, Art. 3.7.3.3: queen, rook, bishop or knight of the same
 * colour.  Underpromotions are distinct moves, which is exactly why perft
 * node counts explode once a pawn can reach the last rank. */
static const int PROMOTION_PIECES[4] = { QUEEN, ROOK, BISHOP, KNIGHT };

/* ------------------------------------------------------------------------ */
/* Small helpers                                                            */
/* ------------------------------------------------------------------------ */

/* Reads a square that may be off the board.  Returns -1 for off-board, which
 * can never equal a piece code, so callers can compare without a guard. */
static int piece_at(const Position *pos, int sq)
{
    if (!ON_BOARD(sq)) {
        return -1;
    }
    return pos->board[sq];
}

static char piece_to_char(int piece)
{
    static const char *letters = ".pnbrqk";
    char c;

    if (piece == EMPTY) {
        return '.';
    }
    c = letters[PIECE_TYPE(piece)];
    if (PIECE_COLOUR(piece) == WHITE) {
        c = (char)(c - 'a' + 'A');
    }
    return c;
}

/* Returns EMPTY for a character that is not a piece letter. */
static int piece_from_char(char c)
{
    switch (c) {
    case 'P': return MAKE_PIECE(WHITE, PAWN);
    case 'N': return MAKE_PIECE(WHITE, KNIGHT);
    case 'B': return MAKE_PIECE(WHITE, BISHOP);
    case 'R': return MAKE_PIECE(WHITE, ROOK);
    case 'Q': return MAKE_PIECE(WHITE, QUEEN);
    case 'K': return MAKE_PIECE(WHITE, KING);
    case 'p': return MAKE_PIECE(BLACK, PAWN);
    case 'n': return MAKE_PIECE(BLACK, KNIGHT);
    case 'b': return MAKE_PIECE(BLACK, BISHOP);
    case 'r': return MAKE_PIECE(BLACK, ROOK);
    case 'q': return MAKE_PIECE(BLACK, QUEEN);
    case 'k': return MAKE_PIECE(BLACK, KING);
    default:  return EMPTY;
    }
}

/* Writes three bytes: file letter, rank digit, NUL. */
static void square_to_string(int sq, char *out)
{
    out[0] = (char)('a' + FILE_OF(sq));
    out[1] = (char)('1' + RANK_OF(sq));
    out[2] = '\0';
}

/* Returns SQ_NONE if the two characters are not a square name. */
static int square_from_string(const char *text)
{
    int file, rank;

    if (text[0] < 'a' || text[0] > 'h' || text[1] < '1' || text[1] > '8') {
        return SQ_NONE;
    }
    file = text[0] - 'a';
    rank = text[1] - '1';
    return SQUARE_OF(file, rank);
}

/* Long algebraic ("e2e4", "e7e8q").  Writes at most six bytes. */
static void move_to_string(Move move, char *out)
{
    square_to_string(move.from, out);
    square_to_string(move.to, out + 2);
    if (move.promotion != EMPTY) {
        out[4] = piece_to_char(MAKE_PIECE(BLACK, move.promotion));
        out[5] = '\0';
    }
}

static const char *skip_spaces(const char *s)
{
    while (*s == ' ' || *s == '\t') {
        s++;
    }
    return s;
}

/* ------------------------------------------------------------------------ */
/* FEN input                                                                */
/* ------------------------------------------------------------------------ */

static int fen_error(const char *reason)
{
    fprintf(stderr, "error: bad FEN (%s)\n", reason);
    return 0;
}

/* Parses a FEN record into `pos`.  Returns 1 on success, 0 on failure (with
 * a message on stderr).  The halfmove clock and fullmove number may be
 * omitted, in which case they default to 0 and 1.  Everything parsed is
 * stored verbatim, so position_to_fen() reproduces the input exactly. */
static int parse_fen(Position *pos, const char *fen)
{
    const char *s = fen;
    int rank = 7;
    int file = 0;
    int i;
    int kings[2];

    for (i = 0; i < 128; i++) {
        pos->board[i] = EMPTY;
    }
    pos->side_to_move = WHITE;
    pos->castling = 0;
    pos->ep_square = SQ_NONE;
    pos->halfmove_clock = 0;
    pos->fullmove_number = 1;
    pos->king_square[WHITE] = SQ_NONE;
    pos->king_square[BLACK] = SQ_NONE;
    kings[WHITE] = 0;
    kings[BLACK] = 0;

    /* Field 1: piece placement, rank 8 first, files a..h within a rank. */
    while (*s != '\0' && *s != ' ') {
        if (*s == '/') {
            if (file != 8) {
                return fen_error("rank does not describe eight files");
            }
            rank--;
            file = 0;
            s++;
            continue;
        }
        if (*s >= '1' && *s <= '8') {
            file += *s - '0';
            s++;
            continue;
        }
        {
            int piece = piece_from_char(*s);
            int sq;

            if (piece == EMPTY) {
                return fen_error("unknown piece letter");
            }
            if (rank < 0 || rank > 7 || file < 0 || file > 7) {
                return fen_error("piece placed outside the board");
            }
            sq = SQUARE_OF(file, rank);
            pos->board[sq] = piece;
            if (PIECE_TYPE(piece) == KING) {
                pos->king_square[PIECE_COLOUR(piece)] = sq;
                kings[PIECE_COLOUR(piece)]++;
            }
            file++;
            s++;
        }
    }
    if (rank != 0 || file != 8) {
        return fen_error("placement does not cover eight ranks");
    }
    if (kings[WHITE] != 1 || kings[BLACK] != 1) {
        return fen_error("each side needs exactly one king");
    }

    /* Field 2: side to move. */
    s = skip_spaces(s);
    if (*s == 'w') {
        pos->side_to_move = WHITE;
    } else if (*s == 'b') {
        pos->side_to_move = BLACK;
    } else {
        return fen_error("side to move must be w or b");
    }
    s++;

    /* Field 3: castling availability (Art. 3.8.2). */
    s = skip_spaces(s);
    if (*s == '-') {
        s++;
    } else {
        while (*s != '\0' && *s != ' ') {
            switch (*s) {
            case 'K': pos->castling |= CASTLE_WK; break;
            case 'Q': pos->castling |= CASTLE_WQ; break;
            case 'k': pos->castling |= CASTLE_BK; break;
            case 'q': pos->castling |= CASTLE_BQ; break;
            default:  return fen_error("unknown castling letter");
            }
            s++;
        }
    }

    /* Field 4: en passant target square (Art. 3.7.3.1-3.7.3.2).  This
     * names the square a capturing pawn would move TO, not the square the
     * captured pawn is standing on. */
    s = skip_spaces(s);
    if (*s == '-') {
        s++;
    } else {
        pos->ep_square = square_from_string(s);
        if (pos->ep_square == SQ_NONE) {
            return fen_error("bad en passant square");
        }
        s += 2;
    }

    /* Fields 5 and 6: halfmove clock and fullmove number, both optional. */
    s = skip_spaces(s);
    if (*s != '\0') {
        char *end;
        long value = strtol(s, &end, 10);

        if (end == s || value < 0) {
            return fen_error("bad halfmove clock");
        }
        pos->halfmove_clock = (int)value;
        s = skip_spaces(end);
    }
    if (*s != '\0') {
        char *end;
        long value = strtol(s, &end, 10);

        if (end == s || value < 1) {
            return fen_error("bad fullmove number");
        }
        pos->fullmove_number = (int)value;
    }
    return 1;
}

/* ------------------------------------------------------------------------ */
/* FEN output                                                               */
/* ------------------------------------------------------------------------ */

static void fen_append_char(char *buf, int *n, char c)
{
    if (*n < MAX_FEN - 1) {
        buf[(*n)++] = c;
    }
}

static void fen_append_int(char *buf, int *n, int value)
{
    char digits[16];
    int len = 0;

    if (value <= 0) {
        fen_append_char(buf, n, '0');
        return;
    }
    while (value > 0 && len < (int)sizeof digits) {
        digits[len++] = (char)('0' + value % 10);
        value /= 10;
    }
    while (len > 0) {
        fen_append_char(buf, n, digits[--len]);
    }
}

/* Writes the FEN of `pos` into `out` (at most `size` bytes including NUL),
 * spelling the en passant field with `ep_square` rather than with the
 * position's own.  The two callers below say why that is a parameter. */
static void write_fen(const Position *pos, int ep_square, char *out, size_t size)
{
    char buf[MAX_FEN];
    int n = 0;
    int rank, file;

    for (rank = 7; rank >= 0; rank--) {
        int empty = 0;

        for (file = 0; file < 8; file++) {
            int piece = pos->board[SQUARE_OF(file, rank)];

            if (piece == EMPTY) {
                empty++;
                continue;
            }
            if (empty > 0) {
                fen_append_char(buf, &n, (char)('0' + empty));
                empty = 0;
            }
            fen_append_char(buf, &n, piece_to_char(piece));
        }
        if (empty > 0) {
            fen_append_char(buf, &n, (char)('0' + empty));
        }
        if (rank > 0) {
            fen_append_char(buf, &n, '/');
        }
    }

    fen_append_char(buf, &n, ' ');
    fen_append_char(buf, &n, pos->side_to_move == WHITE ? 'w' : 'b');

    fen_append_char(buf, &n, ' ');
    if (pos->castling == 0) {
        fen_append_char(buf, &n, '-');
    } else {
        if (pos->castling & CASTLE_WK) { fen_append_char(buf, &n, 'K'); }
        if (pos->castling & CASTLE_WQ) { fen_append_char(buf, &n, 'Q'); }
        if (pos->castling & CASTLE_BK) { fen_append_char(buf, &n, 'k'); }
        if (pos->castling & CASTLE_BQ) { fen_append_char(buf, &n, 'q'); }
    }

    fen_append_char(buf, &n, ' ');
    if (ep_square == SQ_NONE) {
        fen_append_char(buf, &n, '-');
    } else {
        char name[3];

        square_to_string(ep_square, name);
        fen_append_char(buf, &n, name[0]);
        fen_append_char(buf, &n, name[1]);
    }

    fen_append_char(buf, &n, ' ');
    fen_append_int(buf, &n, pos->halfmove_clock);
    fen_append_char(buf, &n, ' ');
    fen_append_int(buf, &n, pos->fullmove_number);
    buf[n] = '\0';

    if (size > 0) {
        size_t len = strlen(buf);

        if (len > size - 1) {
            len = size - 1;
        }
        memcpy(out, buf, len);
        out[len] = '\0';
    }
}

/* The verbatim FEN: whatever double pawn push the position remembers is
 * printed, whether or not anyone could act on it.  parse_fen() followed by
 * this is the identity on well-formed six-field input, which is what the
 * perft suite round-trips and what error messages should show.
 *
 * The other spelling -- an en passant field that is written only when an en
 * passant capture is actually legal -- is the one the FIDE notion of position
 * identity calls for (Art. 9.2.2), and it is produced at the one place that
 * needs it, in the replay below.  A right nobody can exercise is not a right,
 * and printing it here would be printing a difference that is not one. */
static void position_to_fen(const Position *pos, char *out, size_t size)
{
    write_fen(pos, pos->ep_square, out, size);
}

/* ------------------------------------------------------------------------ */
/* Attack detection                                                         */
/*                                                                          */
/* Rather than generating every move of `by_colour` and looking for one that */
/* lands on `sq`, this scans outwards FROM `sq` and asks what is standing at */
/* the other end.  It is the same relation read backwards, and it is what    */
/* makes the check test cheap enough to run after every pseudo-legal move.   */
/* ------------------------------------------------------------------------ */

static int is_square_attacked(const Position *pos, int sq, int by_colour)
{
    int i, dir, scan, piece;

    /* Pawns (Art. 3.7.3): a pawn captures one square diagonally forward, so a
     * white pawn attacking `sq` must stand on sq-17 or sq-15, and a black
     * pawn on sq+15 or sq+17. */
    if (by_colour == WHITE) {
        if (piece_at(pos, sq - 17) == MAKE_PIECE(WHITE, PAWN)) { return 1; }
        if (piece_at(pos, sq - 15) == MAKE_PIECE(WHITE, PAWN)) { return 1; }
    } else {
        if (piece_at(pos, sq + 15) == MAKE_PIECE(BLACK, PAWN)) { return 1; }
        if (piece_at(pos, sq + 17) == MAKE_PIECE(BLACK, PAWN)) { return 1; }
    }

    /* Knights and the king: fixed step patterns, symmetric, so the same
     * offsets work read backwards. */
    for (i = 0; i < 8; i++) {
        if (piece_at(pos, sq + KNIGHT_DIRS[i]) == MAKE_PIECE(by_colour, KNIGHT)) {
            return 1;
        }
        if (piece_at(pos, sq + KING_DIRS[i]) == MAKE_PIECE(by_colour, KING)) {
            return 1;
        }
    }

    /* Sliders: walk each ray until something blocks it, then look at the
     * blocker.  Bishops and queens on the diagonals... */
    for (i = 0; i < 4; i++) {
        dir = BISHOP_DIRS[i];
        for (scan = sq + dir; ON_BOARD(scan); scan += dir) {
            piece = pos->board[scan];
            if (piece == EMPTY) {
                continue;
            }
            if (PIECE_COLOUR(piece) == by_colour &&
                (PIECE_TYPE(piece) == BISHOP || PIECE_TYPE(piece) == QUEEN)) {
                return 1;
            }
            break;
        }
    }
    /* ...rooks and queens on the ranks and files. */
    for (i = 0; i < 4; i++) {
        dir = ROOK_DIRS[i];
        for (scan = sq + dir; ON_BOARD(scan); scan += dir) {
            piece = pos->board[scan];
            if (piece == EMPTY) {
                continue;
            }
            if (PIECE_COLOUR(piece) == by_colour &&
                (PIECE_TYPE(piece) == ROOK || PIECE_TYPE(piece) == QUEEN)) {
                return 1;
            }
            break;
        }
    }
    return 0;
}

/* Is the side to move in check right now? */
static int is_in_check(const Position *pos)
{
    return is_square_attacked(pos, pos->king_square[pos->side_to_move],
                              pos->side_to_move ^ 1);
}

/* ------------------------------------------------------------------------ */
/* Pseudo-legal move generation                                             */
/*                                                                          */
/* "Pseudo-legal" means every rule is enforced except the one that says you  */
/* may not leave your own king attacked.  That last rule is applied by the   */
/* make / test / unmake filter further down, which is the only way to get    */
/* the awkward cases (en passant discovering a check along a rank) right     */
/* without a pile of special-case pin logic.                                 */
/* ------------------------------------------------------------------------ */

static void add_move(Move *list, int *count, int from, int to, int promotion,
                     int flags)
{
    if (*count >= MAX_MOVES) {
        /* Unreachable for legal chess positions; a fixed-size buffer that
         * silently overflowed would be far worse than a loud abort. */
        fprintf(stderr, "internal error: move list overflow\n");
        exit(2);
    }
    list[*count].from = from;
    list[*count].to = to;
    list[*count].promotion = promotion;
    list[*count].flags = flags;
    (*count)++;
}

static void add_pawn_move(Move *list, int *count, int from, int to,
                          int promotion_rank, int flags)
{
    int i;

    if (RANK_OF(to) == promotion_rank) {
        /* Art. 3.7.3.3: the pawn must be exchanged, as part of the same move,
         * for a queen, rook, bishop or knight of the same colour. */
        for (i = 0; i < 4; i++) {
            add_move(list, count, from, to, PROMOTION_PIECES[i], flags);
        }
    } else {
        add_move(list, count, from, to, EMPTY, flags);
    }
}

static void generate_pawn_moves(const Position *pos, int from, Move *list,
                                int *count)
{
    int us = pos->side_to_move;
    int forward = (us == WHITE) ? 16 : -16;
    int start_rank = (us == WHITE) ? 1 : 6;
    int promotion_rank = (us == WHITE) ? 7 : 0;
    int one = from + forward;
    int side;

    /* Art. 3.7.1: the pawn moves forward to the unoccupied square in front. */
    if (ON_BOARD(one) && pos->board[one] == EMPTY) {
        add_pawn_move(list, count, from, one, promotion_rank, MF_NORMAL);

        /* Art. 3.7.2: from its original square it may instead advance two
         * squares, provided both are unoccupied. */
        if (RANK_OF(from) == start_rank) {
            int two = one + forward;

            if (ON_BOARD(two) && pos->board[two] == EMPTY) {
                add_move(list, count, from, two, EMPTY, MF_DOUBLE_PUSH);
            }
        }
    }

    /* Art. 3.7.3: the pawn captures diagonally forward. */
    for (side = -1; side <= 1; side += 2) {
        int to = from + forward + side;
        int target;

        if (!ON_BOARD(to)) {
            continue;
        }
        target = pos->board[to];
        if (target != EMPTY) {
            if (PIECE_COLOUR(target) != us) {
                add_pawn_move(list, count, from, to, promotion_rank, MF_NORMAL);
            }
            continue;
        }
        /* Art. 3.7.3.1-3.7.3.2, en passant: a pawn that has just advanced
         * two squares may be captured by an enemy pawn as though it had
         * advanced only one.  The capture is onto the skipped square and
         * is available on the immediately following move only, which is
         * why ep_square is cleared by every other move. */
        if (to == pos->ep_square) {
            add_move(list, count, from, to, EMPTY, MF_EN_PASSANT);
        }
    }
}

static void generate_step_moves(const Position *pos, int from, const int *dirs,
                                Move *list, int *count)
{
    int us = pos->side_to_move;
    int i;

    for (i = 0; i < 8; i++) {
        int to = from + dirs[i];
        int target;

        if (!ON_BOARD(to)) {
            continue;
        }
        target = pos->board[to];
        if (target != EMPTY && PIECE_COLOUR(target) == us) {
            continue;
        }
        add_move(list, count, from, to, EMPTY, MF_NORMAL);
    }
}

static void generate_slide_moves(const Position *pos, int from, const int *dirs,
                                 int ndirs, Move *list, int *count)
{
    int us = pos->side_to_move;
    int i, to, target;

    for (i = 0; i < ndirs; i++) {
        for (to = from + dirs[i]; ON_BOARD(to); to += dirs[i]) {
            target = pos->board[to];
            if (target == EMPTY) {
                add_move(list, count, from, to, EMPTY, MF_NORMAL);
                continue;
            }
            if (PIECE_COLOUR(target) != us) {
                add_move(list, count, from, to, EMPTY, MF_NORMAL);
            }
            break;
        }
    }
}

/* Art. 3.8.2.  Castling is a king move: the king moves two squares towards a
 * rook on its own first rank, and that rook moves to the square the king has
 * just crossed.  It is unavailable if the king or that rook has already
 * moved (tracked by the rights bits), if any square between them is
 * occupied, or if the king is in check, would pass over an attacked square,
 * or would land on one.
 *
 * Note that the SQUARE THE ROOK CROSSES is not constrained: b1/b8 may be
 * attacked and queenside castling is still legal. */
static void try_castling(const Position *pos, int right, int king_from,
                         int king_to, int rook_from, int flags, Move *list,
                         int *count)
{
    int us = pos->side_to_move;
    int them = us ^ 1;
    int step = (king_to > king_from) ? 1 : -1;
    int sq;

    if ((pos->castling & right) == 0) {
        return;
    }
    /* The rights bits should already imply these, but a checker that trusts
     * its own bookkeeping is not much of a checker. */
    if (pos->board[king_from] != MAKE_PIECE(us, KING)) {
        return;
    }
    if (pos->board[rook_from] != MAKE_PIECE(us, ROOK)) {
        return;
    }

    for (sq = king_from + step; sq != rook_from; sq += step) {
        if (pos->board[sq] != EMPTY) {
            return;
        }
    }
    for (sq = king_from; ; sq += step) {
        if (is_square_attacked(pos, sq, them)) {
            return;
        }
        if (sq == king_to) {
            break;
        }
    }
    add_move(list, count, king_from, king_to, EMPTY, flags);
}

static void generate_castling_moves(const Position *pos, Move *list, int *count)
{
    if (pos->side_to_move == WHITE) {
        try_castling(pos, CASTLE_WK, SQ_E1, SQ_G1, SQ_H1, MF_CASTLE_KING,
                     list, count);
        try_castling(pos, CASTLE_WQ, SQ_E1, SQ_C1, SQ_A1, MF_CASTLE_QUEEN,
                     list, count);
    } else {
        try_castling(pos, CASTLE_BK, SQ_E8, SQ_G8, SQ_H8, MF_CASTLE_KING,
                     list, count);
        try_castling(pos, CASTLE_BQ, SQ_E8, SQ_C8, SQ_A8, MF_CASTLE_QUEEN,
                     list, count);
    }
}

/* Fills `list` and returns how many moves were written. */
static int generate_pseudo_legal_moves(const Position *pos, Move *list)
{
    int count = 0;
    int rank, file;

    for (rank = 0; rank < 8; rank++) {
        for (file = 0; file < 8; file++) {
            int from = SQUARE_OF(file, rank);
            int piece = pos->board[from];

            if (piece == EMPTY || PIECE_COLOUR(piece) != pos->side_to_move) {
                continue;
            }
            switch (PIECE_TYPE(piece)) {
            case PAWN:
                generate_pawn_moves(pos, from, list, &count);
                break;
            case KNIGHT:
                generate_step_moves(pos, from, KNIGHT_DIRS, list, &count);
                break;
            case BISHOP:
                generate_slide_moves(pos, from, BISHOP_DIRS, 4, list, &count);
                break;
            case ROOK:
                generate_slide_moves(pos, from, ROOK_DIRS, 4, list, &count);
                break;
            case QUEEN:
                generate_slide_moves(pos, from, BISHOP_DIRS, 4, list, &count);
                generate_slide_moves(pos, from, ROOK_DIRS, 4, list, &count);
                break;
            case KING:
                generate_step_moves(pos, from, KING_DIRS, list, &count);
                break;
            default:
                break;
            }
        }
    }
    generate_castling_moves(pos, list, &count);
    return count;
}

/* ------------------------------------------------------------------------ */
/* Make and unmake                                                          */
/* ------------------------------------------------------------------------ */

/* A castling right dies when the king moves, when the rook moves, and --
 * the case implementations most often forget -- when the rook is CAPTURED
 * on its home square.  That is why the destination square is examined and
 * not only the origin. */
static void update_castling_rights(Position *pos, int from, int to)
{
    if (from == SQ_E1) { pos->castling &= ~(CASTLE_WK | CASTLE_WQ); }
    if (from == SQ_E8) { pos->castling &= ~(CASTLE_BK | CASTLE_BQ); }
    if (from == SQ_H1 || to == SQ_H1) { pos->castling &= ~CASTLE_WK; }
    if (from == SQ_A1 || to == SQ_A1) { pos->castling &= ~CASTLE_WQ; }
    if (from == SQ_H8 || to == SQ_H8) { pos->castling &= ~CASTLE_BK; }
    if (from == SQ_A8 || to == SQ_A8) { pos->castling &= ~CASTLE_BQ; }
}

static void make_move(Position *pos, Move move, Undo *undo)
{
    int us = pos->side_to_move;
    int piece = pos->board[move.from];
    int captured_square = move.to;

    undo->move = move;
    undo->castling = pos->castling;
    undo->ep_square = pos->ep_square;
    undo->halfmove_clock = pos->halfmove_clock;
    undo->fullmove_number = pos->fullmove_number;

    /* For an en passant capture the captured pawn is NOT on the destination
     * square: it is one rank behind it, on the square it actually occupies.
     * Removing it from there rather than from move.to is what makes the
     * make/test/unmake filter handle the en passant rank pin for free -- both
     * pawns leave the rank at once, and if that exposes the king along the
     * rank the filter simply sees the king attacked. */
    if (move.flags & MF_EN_PASSANT) {
        captured_square = move.to + ((us == WHITE) ? -16 : 16);
    }
    undo->captured_piece = pos->board[captured_square];
    undo->captured_square = captured_square;

    /* Art. 9.3: the clock counts plies since the last capture or pawn move. */
    if (PIECE_TYPE(piece) == PAWN || undo->captured_piece != EMPTY) {
        pos->halfmove_clock = 0;
    } else {
        pos->halfmove_clock++;
    }

    pos->board[captured_square] = EMPTY;
    pos->board[move.from] = EMPTY;
    pos->board[move.to] = (move.promotion == EMPTY)
                        ? piece
                        : MAKE_PIECE(us, move.promotion);

    if (PIECE_TYPE(piece) == KING) {
        pos->king_square[us] = move.to;
    }

    if (move.flags & MF_CASTLE_KING) {
        int rook_from = (us == WHITE) ? SQ_H1 : SQ_H8;
        int rook_to   = (us == WHITE) ? SQ_F1 : SQ_F8;

        pos->board[rook_to] = pos->board[rook_from];
        pos->board[rook_from] = EMPTY;
    } else if (move.flags & MF_CASTLE_QUEEN) {
        int rook_from = (us == WHITE) ? SQ_A1 : SQ_A8;
        int rook_to   = (us == WHITE) ? SQ_D1 : SQ_D8;

        pos->board[rook_to] = pos->board[rook_from];
        pos->board[rook_from] = EMPTY;
    }

    /* The en passant target lives for exactly one ply (Art. 3.7.3.2). */
    if (move.flags & MF_DOUBLE_PUSH) {
        pos->ep_square = move.from + ((us == WHITE) ? 16 : -16);
    } else {
        pos->ep_square = SQ_NONE;
    }

    update_castling_rights(pos, move.from, move.to);

    if (us == BLACK) {
        pos->fullmove_number++;
    }
    pos->side_to_move = us ^ 1;
}

static void unmake_move(Position *pos, const Undo *undo)
{
    Move move = undo->move;
    int us = pos->side_to_move ^ 1;   /* the side that made the move */
    int piece;

    pos->side_to_move = us;
    pos->castling = undo->castling;
    pos->ep_square = undo->ep_square;
    pos->halfmove_clock = undo->halfmove_clock;
    pos->fullmove_number = undo->fullmove_number;

    piece = pos->board[move.to];
    if (move.promotion != EMPTY) {
        piece = MAKE_PIECE(us, PAWN);
    }
    pos->board[move.from] = piece;

    /* Clear the destination first, then restore the captured piece.  For an
     * ordinary capture the two squares coincide and the second write wins;
     * for en passant they differ and both writes are needed. */
    pos->board[move.to] = EMPTY;
    pos->board[undo->captured_square] = undo->captured_piece;

    if (PIECE_TYPE(piece) == KING) {
        pos->king_square[us] = move.from;
    }

    if (move.flags & MF_CASTLE_KING) {
        int rook_from = (us == WHITE) ? SQ_H1 : SQ_H8;
        int rook_to   = (us == WHITE) ? SQ_F1 : SQ_F8;

        pos->board[rook_from] = pos->board[rook_to];
        pos->board[rook_to] = EMPTY;
    } else if (move.flags & MF_CASTLE_QUEEN) {
        int rook_from = (us == WHITE) ? SQ_A1 : SQ_A8;
        int rook_to   = (us == WHITE) ? SQ_D1 : SQ_D8;

        pos->board[rook_from] = pos->board[rook_to];
        pos->board[rook_to] = EMPTY;
    }
}

/* ------------------------------------------------------------------------ */
/* Legality filter and perft                                                */
/* ------------------------------------------------------------------------ */

/* `pos` must be the position AFTER `undo`'s move was made.  Returns 1 if the
 * move was legal, i.e. it did not leave the mover's own king attacked. */
static int move_was_legal(const Position *pos, int mover)
{
    return !is_square_attacked(pos, pos->king_square[mover], mover ^ 1);
}

/* Filters a pseudo-legal list down to the legal moves, in place. */
static int generate_legal_moves(Position *pos, Move *list)
{
    Move pseudo[MAX_MOVES];
    Undo undo;
    int n = generate_pseudo_legal_moves(pos, pseudo);
    int mover = pos->side_to_move;
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        make_move(pos, pseudo[i], &undo);
        if (move_was_legal(pos, mover)) {
            list[count++] = pseudo[i];
        }
        unmake_move(pos, &undo);
    }
    return count;
}

/* perft(depth) counts the leaves of the legal move tree at that depth.  It
 * is the standard way to test a move generator: the counts are enormous,
 * every rule contributes to them, and independently computed reference
 * values exist, so a single wrong number localises a missing rule. */
static long long perft(Position *pos, int depth)
{
    Move moves[MAX_MOVES];
    Undo undo;
    long long nodes = 0;
    int mover = pos->side_to_move;
    int n, i;

    if (depth == 0) {
        return 1;
    }
    n = generate_pseudo_legal_moves(pos, moves);
    for (i = 0; i < n; i++) {
        make_move(pos, moves[i], &undo);
        if (move_was_legal(pos, mover)) {
            nodes += perft(pos, depth - 1);
        }
        unmake_move(pos, &undo);
    }
    return nodes;
}

/* Prints every legal move in a position, one per line, then a summary line.
 * This is the smallest unit a reviewer can check by hand against a board. */
static void print_legal_moves(Position *pos)
{
    Move moves[MAX_MOVES];
    int n = generate_legal_moves(pos, moves);
    int i;

    for (i = 0; i < n; i++) {
        char text[6];

        move_to_string(moves[i], text);
        printf("%s\n", text);
    }
    printf("legal %d  check %s\n", n, is_in_check(pos) ? "yes" : "no");
}

/* Per-root-move breakdown.  When a perft total is wrong, comparing divides
 * between two implementations narrows the fault to one move in a few steps. */
static void perft_divide(Position *pos, int depth)
{
    Move moves[MAX_MOVES];
    Undo undo;
    long long total = 0;
    int mover = pos->side_to_move;
    int n = generate_pseudo_legal_moves(pos, moves);
    int i;

    for (i = 0; i < n; i++) {
        char text[6];
        long long nodes;

        make_move(pos, moves[i], &undo);
        if (move_was_legal(pos, mover)) {
            nodes = (depth > 0) ? perft(pos, depth - 1) : 1;
            move_to_string(moves[i], text);
            printf("%-5s %lld\n", text, nodes);
            total += nodes;
        }
        unmake_move(pos, &undo);
    }
    printf("total %lld\n", total);
}

/* ------------------------------------------------------------------------ */
/* What a position is, for the rules that end a game                        */
/*                                                                          */
/* Three facts about a position drive every automatic termination, and all   */
/* three fall out of one legal move list, so they are gathered once.         */
/* ------------------------------------------------------------------------ */

typedef struct {
    int legal_moves;  /* how many moves the side to move actually has */
    int in_check;     /* whether the side to move is in check (Art. 3.9) */
    int legal_ep;     /* the square an en passant capture may legally be
                       * made ON, or SQ_NONE.  NOT the same thing as
                       * pos->ep_square -- see Art. 9.2.2 below. */
} PositionFacts;

static void examine_position(Position *pos, PositionFacts *facts)
{
    Move moves[MAX_MOVES];
    int n = generate_legal_moves(pos, moves);
    int i;

    facts->legal_moves = n;
    facts->in_check = is_in_check(pos);
    facts->legal_ep = SQ_NONE;

    /* Art. 9.2.2: two positions are the same only if "the possible moves of
     * all the pieces ... are the same", and it says in terms that this
     * includes the right to capture en passant.  A right that cannot be
     * exercised is not one of the possible moves, so what matters is whether
     * a LEGAL en passant capture exists -- not whether the previous move
     * happened to be a double pawn push.  The difference is not academic:
     * the pinned-pawn case (a king and an enemy rook sharing the fifth rank
     * with both pawns) has an ep target square and no ep capture, and a
     * checker that recorded the square would call two identical positions
     * different and never see the repetition. */
    for (i = 0; i < n; i++) {
        if (moves[i].flags & MF_EN_PASSANT) {
            facts->legal_ep = moves[i].to;
        }
    }
}

/* ------------------------------------------------------------------------ */
/* Insufficient material                                                    */
/*                                                                          */
/* CAVEAT, and it is the important part.  Art. 5.2.2 ends the game when a    */
/* position is DEAD: when no series of legal moves whatsoever can lead to    */
/* checkmate.  That is a property of the whole game tree, not of the piece   */
/* inventory, and deciding it in general is not what this function does.     */
/*                                                                          */
/* What this function decides is the material-only special case: a handful of */
/* inventories from which mate is impossible no matter where the pieces      */
/* stand.  The error is one-sided --                                         */
/*                                                                          */
/*     this returns 1  =>  the position is dead                              */
/*     the position is dead  =>  NOT NECESSARILY 1                           */
/*                                                                          */
/* -- and it says nothing about dead positions only a search could see, such */
/* as a wall of blocked pawns.  docs/verification.md sets out the gap.        */
/*                                                                          */
/* WHICH WAY THAT CUTS, since it is easy to get backwards.  Under-detecting  */
/* deadness makes this checker end games LATER than FIDE would.  That is the */
/* permissive direction, and for a claim about a game's LENGTH it is the     */
/* exposed one: a game containing a dead position this test cannot see would */
/* be accepted at a length FIDE does not grant it.                           */
/*                                                                          */
/* What makes that harmless for a game that ends in checkmate is not this    */
/* function but an argument that needs no dead-position test at all.  Take   */
/* any position in such a game: the remaining moves are a series of legal    */
/* moves ending in checkmate, so mate is reachable from it and Art. 5.2.2    */
/* does not apply.  A game that ends in checkmate contains no dead position, */
/* each of its positions having the rest of the game as a witness.  A game   */
/* this checker reports as ending in a DRAW carries no such witness, and the */
/* gap above is then a real limitation of the verdict.                       */
/* ------------------------------------------------------------------------ */

typedef struct {
    int pawns, knights, bishops, rooks, queens;
    int light_bishops;  /* bishops standing on light squares */
    int dark_bishops;   /* bishops standing on dark squares  */
} Material;

/* Fills out[WHITE] and out[BLACK]. */
static void count_material(const Position *pos, Material out[2])
{
    int rank, file;

    memset(out, 0, 2 * sizeof *out);
    for (rank = 0; rank < 8; rank++) {
        for (file = 0; file < 8; file++) {
            int sq = SQUARE_OF(file, rank);
            int piece = pos->board[sq];
            Material *m;

            if (piece == EMPTY) {
                continue;
            }
            m = &out[PIECE_COLOUR(piece)];
            switch (PIECE_TYPE(piece)) {
            case PAWN:   m->pawns++;   break;
            case KNIGHT: m->knights++; break;
            case ROOK:   m->rooks++;   break;
            case QUEEN:  m->queens++;  break;
            case BISHOP:
                m->bishops++;
                if (((file + rank) & 1) != 0) {
                    m->light_bishops++;
                } else {
                    m->dark_bishops++;
                }
                break;
            default:
                break;  /* kings: always exactly one each, never decisive */
            }
        }
    }
}

/* 1 exactly when the inventory rules mate out wherever the pieces stand: bare
 * kings, a single minor piece in total, or -- whatever their number -- bishops
 * alone with every bishop on the board standing on one colour of square.
 *
 * The bishop clause is the one worth deriving, because the count does not
 * matter and it is tempting to think it does.  A bishop never leaves the colour
 * it stands on, so if every bishop on the board is dark then no light square is
 * ever attacked by anything but a king, and a king cannot deliver mate: the
 * mated king would have to stand beside it, which Art. 3.9.2 forbids for both.
 * A mate would therefore need the mated king on a dark square with every light
 * square beside it covered, and only the enemy king can cover those.  A dark
 * square has at least two light neighbours, no two of which share a neighbour
 * other than the mated king's own square and a square adjacent to it, so one
 * king cannot cover them without standing beside the mated king.  No mate
 * exists, and the position is dead -- with two bishops exactly as with one.
 *
 * Knights are outside that clause.  Two knights cannot FORCE mate, but
 * Art. 5.2.2 ends the game when mate is IMPOSSIBLE, not when it cannot be
 * forced, and a cooperating defender can be mated by two knights.  K+N+N vs K
 * is alive, and so is any inventory holding a knight beside another minor. */
static int is_insufficient_material(const Position *pos)
{
    Material m[2];
    int minors, knights, light_bishops, dark_bishops;

    count_material(pos, m);

    /* A pawn can promote, so no pawn position is decided by inventory. */
    if (m[WHITE].pawns != 0 || m[BLACK].pawns != 0) {
        return 0;
    }
    if (m[WHITE].rooks != 0 || m[BLACK].rooks != 0) {
        return 0;
    }
    if (m[WHITE].queens != 0 || m[BLACK].queens != 0) {
        return 0;
    }

    knights = m[WHITE].knights + m[BLACK].knights;
    minors = knights + m[WHITE].bishops + m[BLACK].bishops;

    /* Bare kings, or a single minor piece against a bare king. */
    if (minors <= 1) {
        return 1;
    }

    /* A knight beside any other minor: mate is constructible, so the inventory
     * does not settle it. */
    if (knights != 0) {
        return 0;
    }

    /* Bishops only.  Dead exactly when they all stand on one colour of square,
     * however many there are and however they are divided between the players.
     * Bishops on both colours can mate a cornered king, so that inventory
     * leaves the position alive. */
    light_bishops = m[WHITE].light_bishops + m[BLACK].light_bishops;
    dark_bishops = m[WHITE].dark_bishops + m[BLACK].dark_bishops;
    return (light_bishops == 0 || dark_bishops == 0);
}

/* ------------------------------------------------------------------------ */
/* Termination                                                              */
/* ------------------------------------------------------------------------ */

enum {
    TERM_CONTINUE = 0,
    TERM_CHECKMATE,
    TERM_STALEMATE,
    TERM_INSUFFICIENT,
    TERM_FIVEFOLD,
    TERM_SEVENTYFIVE
};

/* Art. 9.6.2: drawn once the last 75 moves by EACH player have been completed
 * with no pawn move and no capture.  75 by each player is 150 ply. */
#define SEVENTYFIVE_MOVE_PLY_LIMIT 150

/* Art. 9.6.1: drawn once the same position has appeared five times. */
#define FIVEFOLD_REPETITION_COUNT 5

static const char *termination_name(int termination)
{
    switch (termination) {
    case TERM_CHECKMATE:    return "checkmate";
    case TERM_STALEMATE:    return "stalemate";
    case TERM_INSUFFICIENT: return "insufficient-material";
    case TERM_FIVEFOLD:     return "fivefold-repetition";
    case TERM_SEVENTYFIVE:  return "seventyfive-move-rule";
    default:                return "continue";
    }
}

/* The name a --expect-termination argument may use; TERM_CONTINUE is not one
 * of them, since "the game did not end" is not a way for a game to end.
 * Returns TERM_CONTINUE for anything unrecognised. */
static int termination_from_name(const char *name)
{
    int t;

    for (t = TERM_CHECKMATE; t <= TERM_SEVENTYFIVE; t++) {
        if (strcmp(name, termination_name(t)) == 0) {
            return t;
        }
    }
    return TERM_CONTINUE;
}

/* Classifies the position reached AFTER a move, given how many times that
 * position has now occurred (this occurrence included).
 *
 * THE ORDER OF THESE TESTS IS ITSELF A RULE.
 *
 *   checkmate > stalemate > insufficient material > fivefold > 150 ply
 *
 * Checkmate has to be asked first, and specifically before the 150-ply clock.
 * A game that runs its quiet segments to the legal maximum reaches its final
 * move with the clock already at 150, and that final move is the mate: the
 * two conditions hold in the same position.  Art. 5.1.1 says the game "is
 * immediately ended" by checkmate, and Art. 9.6 says its draws apply "if" the
 * position arises -- so a mating move ends the game as a win, and asking the
 * clock first would score that same game as a draw, one ply shorter, with one
 * segment fewer.  The whole result turns on these five lines being in this
 * order. */
static int classify_position(const Position *pos, const PositionFacts *facts,
                             int repetitions)
{
    if (facts->legal_moves == 0) {
        /* Art. 5.1.1 and 5.2.1: with no legal move it is mate if the king is
         * attacked and stalemate if it is not. */
        return facts->in_check ? TERM_CHECKMATE : TERM_STALEMATE;
    }
    if (is_insufficient_material(pos)) {
        return TERM_INSUFFICIENT;
    }
    if (repetitions >= FIVEFOLD_REPETITION_COUNT) {
        return TERM_FIVEFOLD;
    }
    if (pos->halfmove_clock >= SEVENTYFIVE_MOVE_PLY_LIMIT) {
        return TERM_SEVENTYFIVE;
    }
    return TERM_CONTINUE;
}

/* ------------------------------------------------------------------------ */
/* Counting repetitions (Art. 9.2.2, Art. 9.6.1)                            */
/*                                                                          */
/* A position's identity is: the placement of the pieces, whose turn it is,  */
/* the castling rights, and the right to capture en passant if one really    */
/* exists.  The halfmove clock and the move number are NOT part of it -- they*/
/* are bookkeeping about how the position was reached, not about what can be */
/* done from it.  Comparing whole FENs is therefore wrong in the worst way:  */
/* the clock makes every position look new, no position ever repeats, and    */
/* the fivefold rule silently never fires.                                   */
/*                                                                          */
/* The key is a plain byte string, 35 bytes, built as:                       */
/*                                                                          */
/*   bytes 0..31   the 64 squares, a1 first, four bits each (the piece codes */
/*                 run 0..14, which is exactly a nibble)                     */
/*   byte 32       side to move                                              */
/*   byte 33       castling rights                                           */
/*   byte 34       the file of a legal en passant capture, or REP_EP_NONE    */
/*                                                                          */
/* The table is open addressing over a fixed array, and each slot stores the */
/* WHOLE KEY.  The hash only chooses where to start probing; equality is     */
/* decided by comparing all 35 bytes.  A hash collision therefore costs one  */
/* extra probe and cannot produce a wrong count -- which matters, because a  */
/* miscounted repetition is a wrong verdict about a game and there would be  */
/* nothing to see afterwards.  There is no Zobrist key here for the same     */
/* reason: a Zobrist scheme asks the reader to trust that 64 random numbers  */
/* never collide over the run, and this asks them to trust nothing.          */
/* ------------------------------------------------------------------------ */

#define REP_KEY_BYTES 35
#define REP_EP_NONE 8   /* files are 0..7, so 8 is free to mean "none" */

typedef struct {
    unsigned char key[REP_KEY_BYTES];
    int count;   /* 0 means the slot has never been used */
} RepetitionSlot;

/* Static, not allocated, and sized so it can never fill: at most
 * MAX_GAME_PLIES + 1 distinct positions can ever be entered, which is half
 * the slots. */
static RepetitionSlot repetition_table[REPETITION_SLOTS];

static void repetition_reset(void)
{
    memset(repetition_table, 0, sizeof repetition_table);
}

static void build_repetition_key(const Position *pos, int legal_ep,
                                 unsigned char *key)
{
    int rank, file;

    memset(key, 0, REP_KEY_BYTES);
    for (rank = 0; rank < 8; rank++) {
        for (file = 0; file < 8; file++) {
            int index = rank * 8 + file;
            int piece = pos->board[SQUARE_OF(file, rank)];

            /* Piece codes are EMPTY=0, white 1..6, black 9..14: four bits. */
            key[index / 2] |= (unsigned char)(piece << ((index & 1) ? 4 : 0));
        }
    }
    key[32] = (unsigned char)pos->side_to_move;

    /* The castling bits are already "clean" -- set only when the king and
     * that rook really are on their home squares -- because the replay starts
     * from the initial array and update_castling_rights() clears a right when
     * the king moves, when the rook moves, and when anything captures or
     * promotes onto the rook's home square.  A right that survived the loss
     * of its rook would make two identical positions look different here. */
    key[33] = (unsigned char)pos->castling;
    key[34] = (unsigned char)((legal_ep == SQ_NONE) ? REP_EP_NONE
                                                    : FILE_OF(legal_ep));
}

/* FNV-1a, masked to 32 bits so the result does not depend on how wide an
 * unsigned long happens to be.  This picks a probe start and nothing else. */
static unsigned long repetition_hash(const unsigned char *key)
{
    unsigned long hash = 2166136261UL;
    int i;

    for (i = 0; i < REP_KEY_BYTES; i++) {
        hash = (hash ^ key[i]) * 16777619UL;
        hash &= 0xffffffffUL;
    }
    return hash;
}

/* Records one occurrence of `key` and returns how many times it has now
 * occurred, counting this one.  Returns 0 only if the table is full, which
 * the sizing above makes impossible; it is reported rather than ignored
 * because a silent wrap would corrupt every count after it. */
static int repetition_record(const unsigned char *key)
{
    unsigned long mask = (unsigned long)(REPETITION_SLOTS - 1);
    unsigned long slot = repetition_hash(key) & mask;
    int probe;

    for (probe = 0; probe < REPETITION_SLOTS; probe++) {
        RepetitionSlot *entry = &repetition_table[slot];

        if (entry->count == 0) {
            memcpy(entry->key, key, REP_KEY_BYTES);
            entry->count = 1;
            return 1;
        }
        if (memcmp(entry->key, key, REP_KEY_BYTES) == 0) {
            entry->count++;
            return entry->count;
        }
        slot = (slot + 1) & mask;   /* linear probing */
    }
    return 0;
}

/* ------------------------------------------------------------------------ */
/* Reference perft table                                                    */
/*                                                                          */
/* These node counts are the ORACLE.  They come from outside this project --  */
/* the Chess Programming Wiki's "Perft Results" page,                        */
/* https://www.chessprogramming.org/Perft_Results, where they have been      */
/* cross-checked by many independent engines over many years.  If this        */
/* program disagrees with a number here, this program is wrong.  The numbers  */
/* are never to be edited to match it.                                       */
/*                                                                          */
/* Index into `nodes` is the depth; index 0 is unused and left at zero, and  */
/* a zero at any depth means "no reference value published here", which the  */
/* suite skips rather than fails.                                            */
/* ------------------------------------------------------------------------ */

#define PERFT_MAX_DEPTH 7

typedef struct {
    const char *name;
    const char *fen;
    long long nodes[PERFT_MAX_DEPTH + 1];
} PerftCase;

static const PerftCase PERFT_CASES[] = {
    /* The starting array (CPW "Initial Position"). */
    { "initial", START_FEN,
      { 0, 20, 400, 8902, 197281, 4865609, 119060324, 0 } },

    /* "Kiwipete": dense middlegame, both castlings live for both sides,
       many pins.  The classic castling-rights and pin detector. */
    { "kiwipete",
      "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
      { 0, 48, 2039, 97862, 4085603, 193690690, 0, 0 } },

    /* Sparse rook-and-pawn endgame.  Cheap enough to push to depth 7, and
       the position where en passant and discovered check interact. */
    { "endgame",
      "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1",
      { 0, 14, 191, 2812, 43238, 674624, 11030083, 178633661 } },

    /* Promotion torture test: pawns on the seventh for both sides, so the
       underpromotion moves dominate the node counts. */
    { "promotion",
      "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1",
      { 0, 6, 264, 9467, 422333, 15833292, 0, 0 } },

    /* The same position mirrored, with colours swapped.  Identical counts,
       so any white/black asymmetry in the generator shows up immediately. */
    { "promotion-mirror",
      "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1",
      { 0, 6, 264, 9467, 422333, 15833292, 0, 0 } },

    /* CPW position 5: a known killer for buggy castling-rights bookkeeping. */
    { "position-5",
      "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8",
      { 0, 44, 1486, 62379, 2103487, 89941194, 0, 0 } },

    /* CPW position 6 ("Steven Edwards"): quiet, symmetric, heavily analysed. */
    { "position-6",
      "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
      { 0, 46, 2079, 89890, 3894594, 164075551, 0, 0 } }
};

static const int PERFT_CASE_COUNT =
    (int)(sizeof(PERFT_CASES) / sizeof(PERFT_CASES[0]));

/* Runs every published (position, depth) pair up to `max_depth`, plus a FEN
 * round-trip check per position.  Returns 0 if everything passed. */
static int run_perft_suite(int max_depth)
{
    Position pos;
    char fen[MAX_FEN];
    clock_t suite_start = clock();
    int checks = 0;
    int passed = 0;
    int failed = 0;
    int c, depth;

    if (max_depth > PERFT_MAX_DEPTH) {
        max_depth = PERFT_MAX_DEPTH;
    }

    for (c = 0; c < PERFT_CASE_COUNT; c++) {
        const PerftCase *pc = &PERFT_CASES[c];

        if (!parse_fen(&pos, pc->fen)) {
            printf("[FAIL] %-17s fen-parse\n", pc->name);
            checks++;
            failed++;
            continue;
        }

        /* Round-trip: what we printed must be what we were given. */
        position_to_fen(&pos, fen, sizeof fen);
        checks++;
        if (strcmp(fen, pc->fen) == 0) {
            printf("[PASS] %-17s fen-roundtrip\n", pc->name);
            passed++;
        } else {
            printf("[FAIL] %-17s fen-roundtrip\n", pc->name);
            printf("           expected %s\n", pc->fen);
            printf("           produced %s\n", fen);
            failed++;
        }

        for (depth = 1; depth <= max_depth; depth++) {
            long long expected = pc->nodes[depth];
            long long actual;
            clock_t start;
            double seconds;

            if (expected == 0) {
                continue;   /* no published reference at this depth */
            }
            start = clock();
            actual = perft(&pos, depth);
            seconds = (double)(clock() - start) / (double)CLOCKS_PER_SEC;

            checks++;
            if (actual == expected) {
                printf("[PASS] %-17s d%d %14lld  (%.2f s)\n",
                       pc->name, depth, actual, seconds);
                passed++;
            } else {
                printf("[FAIL] %-17s d%d %14lld  expected %lld  (delta %lld)\n",
                       pc->name, depth, actual, expected, actual - expected);
                failed++;
            }
            fflush(stdout);
        }
    }

    printf("perft-suite: %d checks, %d passed, %d failed"
           "  (max depth %d, %.2f s)\n",
           checks, passed, failed, max_depth,
           (double)(clock() - suite_start) / (double)CLOCKS_PER_SEC);
    return failed == 0 ? 0 : 1;
}

/* ------------------------------------------------------------------------ */
/* Hand-written rule cases                                                  */
/*                                                                          */
/* perft proves the generator produces the right NUMBER of moves in a few    */
/* well-travelled positions.  It never names a rule, so a wrong count tells  */
/* you only that something is broken; and it says nothing at all about       */
/* positions its trees do not reach.  The table further down is the          */
/* complement: each entry is one sentence of the Laws turned into a position */
/* plus an expectation, small enough that a reviewer can set it up on a      */
/* board and agree or disagree without running anything.                     */
/*                                                                          */
/* Every position here was constructed from the Laws and every expectation   */
/* was worked out by hand.  None came from another engine, and none was      */
/* edited afterwards to agree with this program's output.                    */
/* ------------------------------------------------------------------------ */

/* "e7e8q" plus NUL is six bytes; eight keeps the token array aligned. */
#define MAX_MOVE_TEXT 8
#define MOVE_LIST_TEXT (MAX_MOVES * MAX_MOVE_TEXT)

/* Splits a space-separated move list, sorts the tokens, and rejoins them.
 * Both the generated list and the expected list are put through this, so a
 * case is a claim about the SET of legal moves and never about the order the
 * generator happens to emit them in. */
static void sort_move_list(const char *text, char *out, size_t size)
{
    char tokens[MAX_MOVES][MAX_MOVE_TEXT];
    const char *s = text;
    size_t used = 0;
    int n = 0;
    int i, j;

    while (*s != '\0' && n < MAX_MOVES) {
        int len = 0;

        while (*s == ' ') {
            s++;
        }
        if (*s == '\0') {
            break;
        }
        while (*s != '\0' && *s != ' ') {
            if (len < MAX_MOVE_TEXT - 1) {
                tokens[n][len++] = *s;
            }
            s++;
        }
        tokens[n][len] = '\0';
        n++;
    }

    /* Insertion sort.  n is at most 256 and this runs once per case, so the
     * simplest correct sort is the right one. */
    for (i = 1; i < n; i++) {
        char key[MAX_MOVE_TEXT];

        memcpy(key, tokens[i], sizeof key);
        j = i - 1;
        while (j >= 0 && strcmp(tokens[j], key) > 0) {
            memcpy(tokens[j + 1], tokens[j], MAX_MOVE_TEXT);
            j--;
        }
        memcpy(tokens[j + 1], key, sizeof key);
    }

    if (size == 0) {
        return;
    }
    out[0] = '\0';
    for (i = 0; i < n; i++) {
        size_t len = strlen(tokens[i]);
        size_t gap = (used > 0) ? 1u : 0u;

        if (used + gap + len + 1 > size) {
            break;
        }
        if (gap > 0) {
            out[used++] = ' ';
        }
        memcpy(out + used, tokens[i], len);
        used += len;
        out[used] = '\0';
    }
}

/* Writes the legal moves of `pos` as a sorted, space-separated UCI list. */
static void legal_moves_text(Position *pos, char *out, size_t size)
{
    Move moves[MAX_MOVES];
    char raw[MOVE_LIST_TEXT];
    size_t used = 0;
    int n = generate_legal_moves(pos, moves);
    int i;

    raw[0] = '\0';
    for (i = 0; i < n; i++) {
        char text[MAX_MOVE_TEXT];
        size_t len;

        move_to_string(moves[i], text);
        len = strlen(text);
        if (used + len + 2 > sizeof raw) {
            break;
        }
        if (used > 0) {
            raw[used++] = ' ';
        }
        memcpy(raw + used, text, len);
        used += len;
        raw[used] = '\0';
    }
    sort_move_list(raw, out, size);
}

/* Looks a UCI move up among the LEGAL moves of `pos`.  Returns 1 if it is
 * there.  Note that this is the only thing the "must be legal" and "must not
 * be legal" expectations consult: a move that the generator never produced
 * and a move that the legality filter rejected are the same answer here. */
static int find_legal_move(Position *pos, const char *uci, Move *out)
{
    Move moves[MAX_MOVES];
    int n = generate_legal_moves(pos, moves);
    int i;

    for (i = 0; i < n; i++) {
        char text[MAX_MOVE_TEXT];

        move_to_string(moves[i], text);
        if (strcmp(text, uci) == 0) {
            *out = moves[i];
            return 1;
        }
    }
    return 0;
}

/* Plays a space-separated list of UCI moves from `pos`, insisting that each
 * one is legal at the moment it is played.  A case whose setup does not run
 * is a failed case, not a skipped one. */
static int apply_setup_moves(Position *pos, const char *setup, char *why,
                             size_t size)
{
    const char *s = setup;

    while (*s != '\0') {
        char token[MAX_MOVE_TEXT];
        Move move;
        Undo undo;
        int len = 0;

        while (*s == ' ') {
            s++;
        }
        if (*s == '\0') {
            break;
        }
        while (*s != '\0' && *s != ' ') {
            if (len < MAX_MOVE_TEXT - 1) {
                token[len++] = *s;
            }
            s++;
        }
        token[len] = '\0';

        if (!find_legal_move(pos, token, &move)) {
            snprintf(why, size, "setup move %s is not legal", token);
            return 0;
        }
        make_move(pos, move, &undo);
    }
    return 1;
}

static int count_legal_moves(Position *pos)
{
    Move moves[MAX_MOVES];

    return generate_legal_moves(pos, moves);
}

/* The expectation forms a case may carry. */
enum {
    RC_MOVESET,    /* the exact set of legal moves, as sorted UCI */
    RC_LEGAL,      /* this one UCI move must be legal             */
    RC_ILLEGAL,    /* this one UCI move must NOT be legal         */
    RC_CHECKMATE,  /* Art. 5.1.1  in check, no legal move         */
    RC_STALEMATE,  /* Art. 5.2.1  not in check, no legal move     */
    RC_CHECK,      /* in check, but at least one legal move       */
    RC_NEITHER,    /* neither checkmate nor stalemate             */
    RC_DEAD,       /* Art. 5.2.2  dead by material alone          */
    RC_ALIVE       /* Art. 5.2.2  not dead by material alone      */
};

typedef struct {
    const char *name;
    const char *article;  /* the Law the case exists to pin down */
    const char *fen;
    const char *setup;    /* UCI moves played before judging, or "" */
    int kind;
    const char *detail;   /* a move, or a move list; "" for the status kinds */
} RuleCase;

/* Sub-article numbers below follow the FIDE Laws effective 1 January 2023:
 *   3.7.3.1-3.7.3.2  en passant    3.7.3.3  promotion    3.8.2  castling
 *   3.9   check; 3.9.2 the ban on leaving or exposing one's own king to it
 *   5.1.1 checkmate                5.2.1    stalemate                     */
static const RuleCase RULE_CASES[] = {

    /* --- En passant, Art. 3.7.3.1-3.7.3.2, self-check ban Art. 3.9.2 ---- */

    /* Both pawns leave the fifth rank in the same move.  With the white king
     * on a5 and a black rook on h5, removing the black d5 pawn AND the white
     * e5 pawn opens the whole rank onto the king, so exd6 e.p. leaves the
     * mover's own king in check and Art. 3.9.2 forbids it.  Nothing else on
     * the board changes -- this is the case a generator that special-cases
     * pins by ray, rather than by make/test/unmake, gets wrong. */
    { "ep-rank-pin-illegal", "Art. 3.9.2",
      "8/8/8/K2pP2r/8/8/8/7k w - d6 0 1", "",
      RC_ILLEGAL, "e5d6" },

    /* The same position stated exhaustively, so the missing e.p. capture is
     * an absence a reader can see rather than one they have to trust.  Kb5
     * IS legal: the white e5 pawn still blocks the rook's rank. */
    { "ep-rank-pin-moveset", "Art. 3.9.2",
      "8/8/8/K2pP2r/8/8/8/7k w - d6 0 1", "",
      RC_MOVESET, "a5a4 a5a6 a5b4 a5b5 a5b6 e5e6" },

    /* Contrast, identical but for the king standing on a4 instead of a5.
     * The rank the two pawns vacate is now not the king's rank, so the same
     * capture is legal.  Art. 3.7.3.1 in its ordinary form. */
    { "ep-legal-contrast", "Art. 3.7.3.1",
      "8/8/8/3pP2r/K7/8/8/7k w - d6 0 1", "",
      RC_LEGAL, "e5d6" },

    /* --- Castling, Art. 3.8.2 ------------------------------------------- */

    /* Control for the three cases below: the black rook is on h8, which
     * attacks none of e1, f1, g1, so kingside castling is available. */
    { "castle-baseline", "Art. 3.8.2",
      "k6r/8/8/8/8/8/8/4K2R w K - 0 1", "",
      RC_LEGAL, "e1g1" },

    /* Rook on f8 attacks f1, the square the king must CROSS.  e1 and g1 are
     * both free, so this case isolates the crossing condition alone. */
    { "castle-through-attack", "Art. 3.8.2",
      "k4r2/8/8/8/8/8/8/4K2R w K - 0 1", "",
      RC_ILLEGAL, "e1g1" },

    /* Rook on e8 gives check.  A king in check may not castle out of it;
     * f1 and g1 are unattacked, so only the check explains the refusal. */
    { "castle-while-in-check", "Art. 3.8.2",
      "k3r3/8/8/8/8/8/8/4K2R w K - 0 1", "",
      RC_ILLEGAL, "e1g1" },

    /* Rook on g8 attacks g1, the square the king is to OCCUPY.  Under
     * Art. 3.9 alone this would already be illegal as a king move; it is
     * listed separately because castling is generated as its own move and a
     * generator can easily forget to test the destination. */
    { "castle-into-attack", "Art. 3.8.2",
      "k5r1/8/8/8/8/8/8/4K2R w K - 0 1", "",
      RC_ILLEGAL, "e1g1" },

    /* Queenside, and the one implementations most often get wrong: the black
     * rook on b8 attacks b1, which the ROOK crosses.  Art. 3.8.2 constrains
     * only the squares the KING stands on, crosses, and occupies -- e1, d1,
     * c1 here, all free -- so 0-0-0 is legal. */
    { "castle-rook-path-attacked", "Art. 3.8.2",
      "1r5k/8/8/8/8/8/8/R3K3 w Q - 0 1", "",
      RC_LEGAL, "e1c1" },

    /* The same claim with the colours swapped, so a white/black asymmetry in
     * the castling code cannot hide behind the case above. */
    { "castle-rook-path-black", "Art. 3.8.2",
      "r3k3/8/8/8/8/8/8/1R5K b q - 0 1", "",
      RC_LEGAL, "e8c8" },

    /* Control for the case below: with nothing having moved, White castles. */
    { "castle-rights-baseline", "Art. 3.8.2",
      "b3k3/8/8/8/7R/8/8/4K2R w K - 0 1", "",
      RC_LEGAL, "e1g1" },

    /* The right dies when the rook is CAPTURED on its home square, not only
     * when it moves.  Black plays Bxh1, White recaptures Rxh1, Black steps
     * aside -- so a white rook is standing on h1 again, the king has never
     * left e1, and f1/g1 are empty and unattacked.  Every board-level
     * precondition for 0-0 is restored; only the lost right forbids it, so
     * this case fails if update_castling_rights() ignores the destination
     * square of a capture. */
    { "castle-rook-captured", "Art. 3.8.2",
      "b3k3/8/8/8/7R/8/8/4K2R b K - 0 1", "a8h1 h4h1 e8e7",
      RC_ILLEGAL, "e1g1" },

    /* --- Promotion, Art. 3.7.3.3 ---------------------------------------- */

    /* The promoted piece acts from its new square at once, so b8=Q gives
     * check along the eighth rank.  Black still has Kd7, Ke7 and Kf7, so the
     * expectation is check and specifically NOT mate. */
    { "promotion-gives-check", "Art. 3.7.3.3",
      "4k3/1P6/8/8/8/8/8/4K3 w - - 0 1", "b7b8q",
      RC_CHECK, "" },

    /* Underpromotion is a real choice, not a formality.  f8=N checks the
     * king on h7; g6 and h6 are covered by the white king on g5, and g7, g8
     * and h8 are blocked by Black's own men.  A knight check cannot be
     * blocked, and the knight on f8 is untouchable: the bishop on g8 is a
     * light-squared bishop and f8 is dark, and the rook on h8 is shut in
     * behind it.  Mate. */
    { "underpromotion-knight-mate", "Art. 3.7.3.3",
      "6br/5Ppk/8/6K1/8/8/8/8 w - - 0 1", "f7f8n",
      RC_CHECKMATE, "" },

    /* The same pawn, promoted to the strongest piece instead: a queen on f8
     * bears on the eighth rank, the f-file and the two diagonals, and h7 is
     * on none of them, so it is not even check.  This is why the four
     * promotion choices have to be generated as four distinct moves. */
    { "queen-promotion-not-mate", "Art. 3.7.3.3",
      "6br/5Ppk/8/6K1/8/8/8/8 w - - 0 1", "f7f8q",
      RC_NEITHER, "" },

    /* --- Check, pins and king safety, Art. 3.9 -------------------------- */

    /* Double check from the rook on e1 and the knight on d6.  Neither
     * checking piece can be captured to any purpose and a knight check
     * cannot be blocked, so only king moves survive -- Rxe1 and Rxd6 each
     * answer one check and leave the other.  e7 is on the rook's file and
     * f7 is a knight's move from d6, which leaves exactly three squares. */
    { "double-check-king-only", "Art. 3.9",
      "4k3/8/r2N4/8/7K/8/8/r3R3 b - - 0 1", "",
      RC_MOVESET, "e8d7 e8d8 e8f8" },

    /* A pinned piece is not frozen: the rook on e2 is pinned against its own
     * king by the rook on e8, and moving ALONG that line keeps the king
     * screened, so Re5 is legal. */
    { "pin-move-along-ray", "Art. 3.9",
      "4r2k/8/8/8/8/8/4R3/4K3 w - - 0 1", "",
      RC_LEGAL, "e2e5" },

    /* Off the line, the same rook exposes its own king, which Art. 3.9
     * forbids.  Ra2 is a perfectly ordinary rook move otherwise. */
    { "pin-move-off-ray", "Art. 3.9",
      "4r2k/8/8/8/8/8/4R3/4K3 w - - 0 1", "",
      RC_ILLEGAL, "e2a2" },

    /* The whole position, so that "along the ray" is shown to mean every
     * square of the ray including the capture on e8, and the pinned rook's
     * seven sideways moves are all shown to be absent. */
    { "pin-moveset", "Art. 3.9",
      "4r2k/8/8/8/8/8/4R3/4K3 w - - 0 1", "",
      RC_MOVESET, "e1d1 e1d2 e1f1 e1f2 e2e3 e2e4 e2e5 e2e6 e2e7 e2e8" },

    /* A king in check from a slider may not step BACKWARDS along the ray.
     * The rook on e8 checks the king on e4; e3 looks shielded by the king
     * itself, and is not, because the king vacates e4 as part of the move.
     * The attack has to be recomputed with the king removed from the
     * occupancy -- which the make / test / unmake filter does for free. */
    { "king-no-retreat-on-ray", "Art. 3.9",
      "4r2k/8/8/8/4K3/8/8/8 w - - 0 1", "",
      RC_ILLEGAL, "e4e3" },

    /* The same position exhaustively: six escapes off the e-file, and both
     * e3 and e5 absent. */
    { "king-escape-moveset", "Art. 3.9",
      "4r2k/8/8/8/4K3/8/8/8 w - - 0 1", "",
      RC_MOVESET, "e4d3 e4d4 e4d5 e4f3 e4f4 e4f5" },

    /* --- Stalemate against checkmate, Art. 5.2.1 and 5.1.1 -------------- */

    /* The queen on g6 covers g7, g8 and h7 and does not bear on h8, and the
     * king on f7 covers g7 and g8.  Black has no legal move and is not in
     * check: stalemate.  Having no move is not, by itself, losing. */
    { "stalemate-queen-g6", "Art. 5.2.1",
      "7k/5K2/6Q1/8/8/8/8/8 b - - 0 1", "",
      RC_STALEMATE, "" },

    /* One square different: the queen steps to g7.  Now it is check, the
     * king on f7 defends the queen so Kxg7 is illegal under Art. 3.9, and
     * g8 and h7 are both covered.  Checkmate.  The pair exists because a
     * generator that mislabels "no legal moves" decides a whole game on it. */
    { "checkmate-queen-g7", "Art. 5.1.1",
      "7k/5KQ1/8/8/8/8/8/8 b - - 0 1", "",
      RC_CHECKMATE, "" },

    /* --- Insufficient material, Art. 5.2.2 ------------------------------ */

    /* The reference game ends in checkmate, so nothing in it ever exercises
     * the material test.  These cases are the only thing standing between a
     * wrong material test and a silent wrong verdict on some other game. */

    { "material-bare-kings", "Art. 5.2.2",
      "8/8/4k3/8/8/3K4/8/8 w - - 0 1", "", RC_DEAD, "" },
    { "material-king-bishop", "Art. 5.2.2",
      "8/8/4k3/8/8/3K1B2/8/8 w - - 0 1", "", RC_DEAD, "" },
    { "material-king-knight", "Art. 5.2.2",
      "8/8/4k3/8/8/3K1N2/8/8 w - - 0 1", "", RC_DEAD, "" },

    /* Both bishops on dark squares (c1 and f8 are both dark): neither can
     * ever reach the other's colour, and no mate exists. */
    { "material-bishops-same-colour", "Art. 5.2.2",
      "5b2/4k3/8/8/8/8/4K3/2B5 w - - 0 1", "", RC_DEAD, "" },

    /* c1 dark, c8 light.  Opposite colours can mate a cornered king, so the
     * inventory alone does not settle it and the game goes on. */
    { "material-bishops-opposite-colour", "Art. 5.2.2",
      "2b5/4k3/8/8/8/8/4K3/2B5 w - - 0 1", "", RC_ALIVE, "" },

    /* Two knights cannot FORCE mate, but mate is reachable against a
     * cooperating defender, so the position is not dead.  Art. 5.2.2 turns
     * on impossibility, not on what can be forced. */
    { "material-two-knights", "Art. 5.2.2",
      "8/8/4k3/8/8/3K1NN1/8/8 w - - 0 1", "", RC_ALIVE, "" },

    /* A single pawn keeps every position alive: it can promote. */
    { "material-lone-pawn", "Art. 5.2.2",
      "8/8/4k3/8/8/3K4/4P3/8 w - - 0 1", "", RC_ALIVE, "" },

    /* The bishop clause does not count bishops, and these four cases are why.
     * Two white bishops both on dark squares (c1, e1) against a bare king is
     * dead for exactly the reason one bishop is: no light square is ever
     * attacked, so no king can be mated on one, and a dark square always keeps
     * a light neighbour the white king cannot reach without standing beside
     * its target.  An earlier version of this file stopped at one bishop per
     * side and called this position alive; the case is here so that the
     * boundary is a stated answer rather than an accident of where the
     * enumeration happened to stop. */
    { "material-two-bishops-same-colour", "Art. 5.2.2",
      "8/k7/8/8/8/8/8/2B1B1K1 w - - 0 1", "", RC_DEAD, "" },

    /* c1 dark, d1 light.  One bishop of each colour mates a cornered king, so
     * adding a second bishop can revive a position rather than only deadening
     * it -- which is why the clause turns on the colours present and not on
     * the count. */
    { "material-two-bishops-opposite-colour", "Art. 5.2.2",
      "8/k7/8/8/8/8/8/2BB2K1 w - - 0 1", "", RC_ALIVE, "" },

    /* Three bishops, split across the players (white c1 and e1, black f8), all
     * three dark.  Ownership does not enter the argument either. */
    { "material-three-bishops-one-colour", "Art. 5.2.2",
      "5b2/k7/8/8/8/8/8/2B1B1K1 w - - 0 1", "", RC_DEAD, "" },

    /* A knight beside another minor is alive whatever the bishop colours say:
     * the knight reaches both colours, and K+B+N mates outright. */
    { "material-bishop-and-knight", "Art. 5.2.2",
      "8/k7/8/8/8/8/8/2B1N1K1 w - - 0 1", "", RC_ALIVE, "" }
};

static const int RULE_CASE_COUNT =
    (int)(sizeof(RULE_CASES) / sizeof(RULE_CASES[0]));

static const char *rule_kind_name(int kind)
{
    switch (kind) {
    case RC_MOVESET:   return "exact legal set";
    case RC_LEGAL:     return "must be legal";
    case RC_ILLEGAL:   return "must be illegal";
    case RC_CHECKMATE: return "checkmate";
    case RC_STALEMATE: return "stalemate";
    case RC_CHECK:     return "check but not mate";
    case RC_DEAD:      return "insufficient material";
    case RC_ALIVE:     return "sufficient material";
    default:           return "neither mate nor stalemate";
    }
}

/* Judges one case against an already-prepared position.  Returns 1 for pass
 * and fills `why` with what was actually observed, either way. */
static int judge_rule_case(Position *pos, const RuleCase *rc, char *why,
                           size_t size)
{
    if (rc->kind == RC_MOVESET) {
        char got[MOVE_LIST_TEXT];
        char want[MOVE_LIST_TEXT];

        legal_moves_text(pos, got, sizeof got);
        sort_move_list(rc->detail, want, sizeof want);
        if (strcmp(got, want) == 0) {
            snprintf(why, size, "%s", got);
            return 1;
        }
        snprintf(why, size, "got [%s], wanted [%s]", got, want);
        return 0;
    }

    if (rc->kind == RC_LEGAL || rc->kind == RC_ILLEGAL) {
        Move move;
        int found = find_legal_move(pos, rc->detail, &move);
        int wanted = (rc->kind == RC_LEGAL);

        snprintf(why, size, "%s is %s", rc->detail,
                 found ? "legal" : "not legal");
        return found == wanted;
    }

    if (rc->kind == RC_DEAD || rc->kind == RC_ALIVE) {
        int dead = is_insufficient_material(pos);

        snprintf(why, size, "%s material",
                 dead ? "insufficient" : "sufficient");
        return dead == (rc->kind == RC_DEAD);
    }

    {
        int check = is_in_check(pos);
        int moves = count_legal_moves(pos);
        int mate = check && moves == 0;
        int stale = !check && moves == 0;
        int ok;

        if (rc->kind == RC_CHECKMATE) {
            ok = mate;
        } else if (rc->kind == RC_STALEMATE) {
            ok = stale;
        } else if (rc->kind == RC_CHECK) {
            ok = check && !mate;
        } else {
            ok = !mate && !stale;
        }
        snprintf(why, size, "%s, %d legal move%s",
                 mate ? "checkmate" : (stale ? "stalemate"
                     : (check ? "check" : "no check")),
                 moves, moves == 1 ? "" : "s");
        return ok;
    }
}

/* Walks the whole table.  Returns 0 only if every case passed. */
static int run_rule_cases(void)
{
    /* One buffer, reused; a failing move-set case prints both lists. */
    char why[2 * MOVE_LIST_TEXT + 64];
    Position pos;
    int passed = 0;
    int failed = 0;
    int c;

    for (c = 0; c < RULE_CASE_COUNT; c++) {
        const RuleCase *rc = &RULE_CASES[c];
        int ok;

        if (!parse_fen(&pos, rc->fen)) {
            snprintf(why, sizeof why, "FEN did not parse");
            ok = 0;
        } else if (!apply_setup_moves(&pos, rc->setup, why, sizeof why)) {
            ok = 0;
        } else {
            ok = judge_rule_case(&pos, rc, why, sizeof why);
        }

        printf("[%s] %-26s %-10s %s\n", ok ? "PASS" : "FAIL",
               rc->name, rc->article, why);
        if (!ok) {
            printf("           expected %s", rule_kind_name(rc->kind));
            if (rc->detail[0] != '\0' && rc->kind != RC_MOVESET) {
                printf(": %s", rc->detail);
            }
            printf("\n           position %s", rc->fen);
            if (rc->setup[0] != '\0') {
                printf("  after %s", rc->setup);
            }
            printf("\n");
            failed++;
        } else {
            passed++;
        }
    }

    printf("rule-cases: %d cases, %d passed, %d failed\n",
           RULE_CASE_COUNT, passed, failed);
    return failed == 0 ? 0 : 1;
}

/* ------------------------------------------------------------------------ */
/* Material scan                                                            */
/*                                                                          */
/* is_insufficient_material() reads nothing but the inventory, so its entire */
/* domain is finite and small: how many knights and how many bishops of each */
/* square colour each player holds, and whether a pawn, rook or queen is on  */
/* the board at all.  This mode walks that domain, builds one representative */
/* position per point of it, and prints its FEN with the verdict beside it.  */
/*                                                                          */
/* WHY IT EXISTS.  Every other check in this file is anchored either to an   */
/* oracle from outside the project (perft) or to the reference game, and the */
/* reference game never reaches a position where the material test can fire  */
/* -- it ends in checkmate with a queen on the board.  So the one part of    */
/* the termination rules that the trace comparison cannot reach is this one, */
/* and a disagreement with the verifier in src/long_chess/verifier/, which   */
/* decides Art. 5.2.2 through python-chess, would sit behind every passing   */
/* check here.  It did: an earlier version of this file called every         */
/* inventory holding two bishops of one colour alive, python-chess called it */
/* dead, thirty rule cases passed, and the trace matched byte for byte.      */
/*                                                                          */
/* scripts/check_movegen.py reads this output and puts the same FENs to      */
/* python-chess.  The two must agree on every line.  That is a check on two  */
/* implementations of one approximation, not on the approximation itself --  */
/* both decide Art. 5.2.2 by inventory alone, which docs/verification.md     */
/* explains is not a decision procedure for a dead position.                 */
/* ------------------------------------------------------------------------ */

#define SCAN_MAX_PER_KIND 2

static void material_scan(void)
{
    /* Four squares of each colour, four for knights, one for the heavy piece,
     * two for the kings -- all distinct, so every inventory in the domain
     * places without collision.  Where the pieces stand cannot change the
     * verdict, since the test reads counts and bishop square-colours and
     * nothing else; that is itself part of what is being cross-checked. */
    static const int LIGHT_SQUARES[4] = {   /* a2 a4 a6 a8 */
        SQUARE_OF(0, 1), SQUARE_OF(0, 3), SQUARE_OF(0, 5), SQUARE_OF(0, 7)
    };
    static const int DARK_SQUARES[4] = {    /* c1 c3 c5 c7 */
        SQUARE_OF(2, 0), SQUARE_OF(2, 2), SQUARE_OF(2, 4), SQUARE_OF(2, 6)
    };
    static const int KNIGHT_SQUARES[4] = {  /* g2 g3 g4 g5 */
        SQUARE_OF(6, 1), SQUARE_OF(6, 2), SQUARE_OF(6, 3), SQUARE_OF(6, 4)
    };
    /* The three piece types that end the scan early, one of each colour, plus
     * the empty case.  A pawn stands on h5, so it is never on a promotion
     * rank. */
    static const int HEAVY_TYPE[7] = { EMPTY, PAWN, ROOK, QUEEN, PAWN, ROOK, QUEEN };
    static const int HEAVY_COLOUR[7] = { WHITE, WHITE, WHITE, WHITE,
                                         BLACK, BLACK, BLACK };
    const int heavy_square = SQUARE_OF(7, 4);   /* h5 */
    const int white_king = SQUARE_OF(4, 0);     /* e1 */
    const int black_king = SQUARE_OF(4, 7);     /* e8 */

    int heavy, wn, wl, wd, bn, bl, bd;
    long emitted = 0;
    char fen[MAX_FEN];

    for (heavy = 0; heavy < 7; heavy++) {
    for (wn = 0; wn <= SCAN_MAX_PER_KIND; wn++) {
    for (wl = 0; wl <= SCAN_MAX_PER_KIND; wl++) {
    for (wd = 0; wd <= SCAN_MAX_PER_KIND; wd++) {
    for (bn = 0; bn <= SCAN_MAX_PER_KIND; bn++) {
    for (bl = 0; bl <= SCAN_MAX_PER_KIND; bl++) {
    for (bd = 0; bd <= SCAN_MAX_PER_KIND; bd++) {
        Position pos;
        int i, light_used = 0, dark_used = 0, knights_used = 0;

        memset(&pos, 0, sizeof pos);   /* EMPTY is 0, so this clears the board */
        pos.side_to_move = WHITE;
        pos.castling = 0;
        pos.ep_square = SQ_NONE;
        pos.halfmove_clock = 0;
        pos.fullmove_number = 1;
        pos.king_square[WHITE] = white_king;
        pos.king_square[BLACK] = black_king;
        pos.board[white_king] = MAKE_PIECE(WHITE, KING);
        pos.board[black_king] = MAKE_PIECE(BLACK, KING);

        for (i = 0; i < wl; i++) {
            pos.board[LIGHT_SQUARES[light_used++]] = MAKE_PIECE(WHITE, BISHOP);
        }
        for (i = 0; i < bl; i++) {
            pos.board[LIGHT_SQUARES[light_used++]] = MAKE_PIECE(BLACK, BISHOP);
        }
        for (i = 0; i < wd; i++) {
            pos.board[DARK_SQUARES[dark_used++]] = MAKE_PIECE(WHITE, BISHOP);
        }
        for (i = 0; i < bd; i++) {
            pos.board[DARK_SQUARES[dark_used++]] = MAKE_PIECE(BLACK, BISHOP);
        }
        for (i = 0; i < wn; i++) {
            pos.board[KNIGHT_SQUARES[knights_used++]] = MAKE_PIECE(WHITE, KNIGHT);
        }
        for (i = 0; i < bn; i++) {
            pos.board[KNIGHT_SQUARES[knights_used++]] = MAKE_PIECE(BLACK, KNIGHT);
        }
        if (HEAVY_TYPE[heavy] != EMPTY) {
            pos.board[heavy_square] =
                MAKE_PIECE(HEAVY_COLOUR[heavy], HEAVY_TYPE[heavy]);
        }

        write_fen(&pos, SQ_NONE, fen, sizeof fen);
        printf("%s\t%s\n", fen,
               is_insufficient_material(&pos) ? "dead" : "alive");
        emitted++;
    }}}}}}}

    printf("material-scan: %ld inventories\n", emitted);
}

/* ------------------------------------------------------------------------ */
/* The corpus check: obligations [H1] [H2] [H5] [H6]                        */
/*                                                                          */
/* src/long_chess/bound/invariant.py proves the home-rank lemma: that under  */
/* the restriction the bound argument imposes, a defender's pawn home rank   */
/* never changes and no attacker pawn moves more than four times.  It is an  */
/* induction, and every step where it appeals to the rules of chess rather   */
/* than to itself is written down as a named obligation.  Four of those are  */
/* claims about chess itself, true in every position there is:               */
/*                                                                          */
/*   [H1] a legal move starts on a square holding a piece of the side to     */
/*        move                                                              */
/*   [H2] a move onto an occupied square is a capture of an ENEMY piece      */
/*   [H5] a move changes the occupancy of its own from- and to-squares and   */
/*        of no others, except the rook's two squares when castling          */
/*        (Art. 3.8.2) and the captured pawn's square when capturing         */
/*        en passant (Art. 3.7.3.1-3.7.3.2)                                  */
/*   [H6] a pawn advances exactly one rank, or two from its OWN home rank    */
/*        only (Art. 3.7.1, Art. 3.7.2)                                      */
/*                                                                          */
/* No enumeration settles a claim about every position, and nothing below    */
/* pretends to.  These four are read off the Laws; what a corpus can do is   */
/* catch a MOVE GENERATOR that fails to obey them.  This mode is therefore a */
/* check on the tooling, not on the mathematics -- which is exactly the role */
/* invariant.py assigns it.                                                  */
/*                                                                          */
/* WHY IT IS HERE AS WELL AS THERE.  invariant.py runs these four checks     */
/* over positions produced by python-chess, so passing them leaves           */
/* python-chess inside the set of things a reader has to trust.  This mode   */
/* runs them again over positions produced here: a different move generator, */
/* a different board representation, and a different random walk.  The two   */
/* corpora are deliberately NOT the same positions and are not meant to be.  */
/* What is compared is the CONCLUSION -- no exception anywhere -- and two    */
/* unrelated walks cover more of chess than one walk run twice.              */
/* ------------------------------------------------------------------------ */

/* How far a single game is walked before the next one is started.  Games are
 * restarted rather than played out to enormous length because the opening
 * moves of a fresh game are cheap variety, and variety is the whole point of
 * a corpus. */
#define CORPUS_PLIES_PER_GAME 160

/* How often the walk restricts itself to pawn moves and captures, in percent.
 * See corpus_choose_move() for why the walk is biased at all. */
#define CORPUS_INTERESTING_PERCENT 70

/* An exception is a catastrophe, not a statistic: if one appears it should be
 * printed in full.  But a generator broken in some systematic way would emit
 * one per move, so the printing stops after this many per obligation and the
 * rest are counted and reported as a suppressed total.  Nothing is hidden;
 * the summary line always states the true number. */
#define CORPUS_MAX_PRINTED 20

/* --- splitmix64 ---------------------------------------------------------- */
/*                                                                          */
/* rand() is implementation-defined.  The same seed produces different games */
/* on different C libraries, so a corpus generated with it could not be      */
/* reproduced by a reader on another machine, and an unreproducible corpus   */
/* is not much of a record.  splitmix64 is short enough to state completely: */
/* the state advances by a fixed odd constant and the output is that state   */
/* run through a fixed avalanche.  These six lines ARE the specification, so */
/* anyone can re-derive the exact walk this program took.                    */
/* -------------------------------------------------------------------------*/

/* The default seed: the first 64 bits of the fractional part of pi.  Any
 * fixed value would do.  What matters is that it is fixed, that it is
 * written down, and that --seed can replace it -- a run always prints the
 * seed it actually used, so any run can be repeated exactly. */
#define CORPUS_DEFAULT_SEED 0x243F6A8885A308D3ULL

static unsigned long long corpus_rng_state;

static void corpus_seed(unsigned long long seed)
{
    corpus_rng_state = seed;
}

static unsigned long long corpus_random(void)
{
    unsigned long long z = (corpus_rng_state += 0x9E3779B97F4A7C15ULL);

    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* Uniform in [0, n), for n >= 1.  A plain modulo would make the first few
 * moves in every list very slightly likelier than the rest; the bias is far
 * too small to matter here, and rejecting the short tail costs three lines
 * and removes the need to argue about it. */
static int corpus_below(int n)
{
    unsigned long long span = (unsigned long long)n;
    unsigned long long zone = ~0ULL - (~0ULL % span);   /* a multiple of span */
    unsigned long long r;

    do {
        r = corpus_random();
    } while (r >= zone);
    return (int)(r % span);
}

/* --- the four obligations ------------------------------------------------ */

enum { OB_H1 = 0, OB_H2, OB_H5, OB_H6, OB_COUNT };

typedef struct {
    const char *tag;
    const char *claim;
    const char *unit;      /* what this obligation counts as a checked move */
    long long positions;   /* positions inspected */
    long long moves;       /* moves actually looked at */
    long long exceptions;  /* moves that broke the claim */
    long long printed;     /* exceptions printed in full, up to the cap */
    unsigned doubles_from; /* [H6] only: bitmask of ranks a double push came
                            * from.  Recorded because a corpus that never saw
                            * a double push would discharge [H6] vacuously,
                            * and a vacuous pass should be visible. */
} Obligation;

static void corpus_note_exception(Obligation *ob, const Position *pos,
                                  Move move, const char *detail)
{
    char fen[MAX_FEN];
    char uci[8];

    ob->exceptions++;
    if (ob->printed >= CORPUS_MAX_PRINTED) {
        return;
    }
    ob->printed++;
    position_to_fen(pos, fen, sizeof fen);
    move_to_string(move, uci);
    printf("[%s] EXCEPTION  %s / %s%s%s\n", ob->tag, fen, uci,
           (detail[0] != '\0') ? "  -- " : "", detail);
}

/* [H1] A legal move starts on a square holding a piece of the side to move.
 *
 * Art. 1.1 and Art. 3.1: a player moves their OWN pieces, and there is
 * nothing to move on an empty square. */
static void corpus_check_h1(Obligation *ob, const Position *pos,
                            const Move *legal, int n)
{
    int i;

    ob->positions++;
    for (i = 0; i < n; i++) {
        int piece = pos->board[legal[i].from];

        ob->moves++;
        if (piece == EMPTY) {
            corpus_note_exception(ob, pos, legal[i], "the origin is empty");
        } else if (PIECE_COLOUR(piece) != pos->side_to_move) {
            corpus_note_exception(ob, pos, legal[i],
                                  "the origin holds an enemy piece");
        }
    }
}

/* [H2] A move onto an occupied square is a capture of an enemy piece.
 *
 * Two things have to hold, and the second is the one worth the work: the
 * occupant must belong to the other side (Art. 3.1 -- a piece may not be
 * moved to a square occupied by a piece of the same colour), and the move
 * must actually TAKE it.  Checking the colours alone would still accept a
 * generator that let a rook slide through an enemy piece and leave it
 * standing, so the move is made and the capture record is read back. */
static void corpus_check_h2(Obligation *ob, Position *pos, const Move *legal,
                            int n)
{
    Undo undo;
    int i;

    ob->positions++;
    for (i = 0; i < n; i++) {
        int occupant = pos->board[legal[i].to];
        int took_it;

        if (occupant == EMPTY) {
            continue;   /* not a move this obligation says anything about */
        }
        ob->moves++;
        if (PIECE_COLOUR(occupant) == pos->side_to_move) {
            corpus_note_exception(ob, pos, legal[i],
                                  "the occupant is the mover's own piece");
            continue;
        }
        make_move(pos, legal[i], &undo);
        took_it = (undo.captured_square == legal[i].to &&
                   undo.captured_piece == occupant);
        unmake_move(pos, &undo);
        if (!took_it) {
            corpus_note_exception(ob, pos, legal[i],
                                  "the piece standing there was not captured");
        }
    }
}

/* [H5] A move changes the occupancy of its own from- and to-squares and of no
 * others -- except the rook's two squares when castling (Art. 3.8.2) and the
 * captured pawn's square when capturing en passant (Art. 3.7.3.1-3.7.3.2).
 *
 * The check is literal: photograph the board, make the move, compare every
 * slot, unmake.  All 128 slots of the 0x88 array are compared and not just
 * the 64 real squares, so a generator that wrote into the off-board padding
 * would be caught here rather than corrupting a later position quietly.
 *
 * invariant.py runs this one over an eighth of its corpus, because copying a
 * python board per move is expensive.  Here it runs over every move of every
 * position: a make and an unmake and 128 integer comparisons cost nothing.
 *
 * WHAT THIS CANNOT SEE, since the claim is one-directional and so is the
 * check.  [H5] bounds the squares a move MAY change; it says nothing about
 * squares a move must change.  A generator that changes too LITTLE therefore
 * passes.  The sharpest instance: remove the en passant victim from the wrong
 * side of the target square, and the square wrongly cleared is the one the
 * victim pawn has just vacated by double-pushing, so it is ALWAYS empty --
 * clearing it changes nothing, the real victim survives, and no square
 * outside the allowed set moves.  That is not a gap to be patched here; the
 * upper bound is what the lemma's steps (a) and (b) actually use.  It is a
 * reminder that this check is one net among several, and that the one which
 * catches that particular bug is the en passant rule case (Art. 3.9, the rank
 * pin) together with the perft suite, both a few hundred lines above. */
static void corpus_check_h5(Obligation *ob, Position *pos, const Move *legal,
                            int n)
{
    int before[128];
    Undo undo;
    int i, j, sq;

    ob->positions++;
    for (i = 0; i < n; i++) {
        Move move = legal[i];
        int allowed[4];       /* from, to, and at most two exemptions */
        int nallowed = 0;
        int offending = SQ_NONE;

        ob->moves++;
        allowed[nallowed++] = move.from;
        allowed[nallowed++] = move.to;

        if (move.flags & (MF_CASTLE_KING | MF_CASTLE_QUEEN)) {
            /* Art. 3.8.2: the rook leaves its corner and lands on the square
             * the king crossed.  Both squares are taken from the move's own
             * geometry rather than from a table, so the exemption is exactly
             * as wide as the rule and no wider. */
            int back = RANK_OF(move.from);
            int kingside = (move.flags & MF_CASTLE_KING) != 0;

            allowed[nallowed++] = SQUARE_OF(kingside ? 7 : 0, back);
            allowed[nallowed++] = SQUARE_OF(kingside ? 5 : 3, back);
        } else if (move.flags & MF_EN_PASSANT) {
            /* Art. 3.7.3.1-3.7.3.2: the captured pawn stands beside
             * the capturing pawn, not on the square the capturing pawn
             * moves to. */
            allowed[nallowed++] =
                move.to + ((pos->side_to_move == WHITE) ? -16 : 16);
        }

        memcpy(before, pos->board, sizeof before);
        make_move(pos, move, &undo);
        for (sq = 0; sq < 128 && offending == SQ_NONE; sq++) {
            if (pos->board[sq] == before[sq]) {
                continue;
            }
            for (j = 0; j < nallowed; j++) {
                if (allowed[j] == sq) {
                    break;
                }
            }
            if (j == nallowed) {
                offending = sq;
            }
        }
        unmake_move(pos, &undo);

        if (offending != SQ_NONE) {
            char detail[64];

            if (ON_BOARD(offending)) {
                char name[3];

                square_to_string(offending, name);
                snprintf(detail, sizeof detail, "%s also changed", name);
            } else {
                snprintf(detail, sizeof detail,
                         "off-board slot %d was written", offending);
            }
            corpus_note_exception(ob, pos, move, detail);
        }
    }
}

/* [H6] A pawn advances exactly one rank, or two from its own home rank only.
 *
 * Art. 3.7.1 gives the single step, Art. 3.7.2 the double, and the double only
 * "provided [the pawn] has not yet moved" -- which is to say, only from the
 * rank it started on.  Note that this is about the RANK the pawn crosses, so
 * a diagonal capture and a straight push are the same case here. */
static void corpus_check_h6(Obligation *ob, const Position *pos,
                            const Move *legal, int n)
{
    int i;

    ob->positions++;
    for (i = 0; i < n; i++) {
        int piece = pos->board[legal[i].from];
        int us, home, from_rank, advance;

        if (piece == EMPTY || PIECE_TYPE(piece) != PAWN) {
            continue;
        }
        ob->moves++;
        us = PIECE_COLOUR(piece);
        home = (us == WHITE) ? 1 : 6;
        from_rank = RANK_OF(legal[i].from);
        /* Measured in the direction the mover's pawns travel, so a negative
         * advance is a pawn moving backwards and is caught by the same test
         * that catches a triple push. */
        advance = (us == WHITE) ? RANK_OF(legal[i].to) - from_rank
                                : from_rank - RANK_OF(legal[i].to);

        if (advance == 2) {
            ob->doubles_from |= 1u << from_rank;
            if (from_rank != home) {
                corpus_note_exception(ob, pos, legal[i],
                                      "a double push from a rank that is not "
                                      "this pawn's home rank");
            }
        } else if (advance != 1) {
            corpus_note_exception(ob, pos, legal[i],
                                  "a pawn move that does not advance one rank");
        }
    }
}

/* --- what the corpus actually contained ---------------------------------- */

/* Zero exceptions is worth only as much as the corpus that produced it.  Two
 * of the four claims above are mostly about awkward cases -- the exemptions
 * [H5] grants castling and en passant, and the two-rank case in [H6] -- and a
 * walk that never generated a castling move would discharge [H5] without ever
 * testing the clause that makes it interesting.
 *
 * So the awkward moves are counted as they go past.  Nothing fails on these
 * numbers; they are here so that a reader can see whether the bias in
 * corpus_choose_move() did its job, instead of taking it on trust. */
typedef struct {
    long long castling;
    long long en_passant;
    long long promotions;
} Coverage;

static void corpus_note_coverage(Coverage *cov, const Move *legal, int n)
{
    int i;

    for (i = 0; i < n; i++) {
        if (legal[i].flags & (MF_CASTLE_KING | MF_CASTLE_QUEEN)) {
            cov->castling++;
        }
        if (legal[i].flags & MF_EN_PASSANT) {
            cov->en_passant++;
        }
        if (legal[i].promotion != EMPTY) {
            cov->promotions++;
        }
    }
}

/* --- the walk ------------------------------------------------------------ */

/* A uniform random walk from the initial array is a poor corpus.  It spends
 * almost all of its time shuffling pieces around the middle of the board:
 * promotions are rare, en passant captures rarer, and the back ranks empty
 * out and stay empty.  Those are precisely the cases these four obligations
 * would break on if the generator were wrong, and precisely the ones an
 * unbiased walk never reaches.
 *
 * So most of the time the choice is restricted to pawn moves and captures.
 * That pushes pawns down the board, keeps material on it, and makes double
 * pushes -- and therefore en passant -- common.  invariant.py biases its own
 * walk the same way and for the same reason; the two walks share the intent
 * and nothing else. */
static Move corpus_choose_move(const Position *pos, const Move *legal, int n)
{
    int interesting[MAX_MOVES];
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        /* An en passant capture lands on an empty square, but it is a pawn
         * move, so the first test already covers it. */
        if (PIECE_TYPE(pos->board[legal[i].from]) == PAWN ||
            pos->board[legal[i].to] != EMPTY) {
            interesting[count++] = i;
        }
    }
    if (count > 0 && corpus_below(100) < CORPUS_INTERESTING_PERCENT) {
        return legal[interesting[corpus_below(count)]];
    }
    return legal[corpus_below(n)];
}

static int run_corpus(long positions_wanted, unsigned long long seed)
{
    Obligation obligations[OB_COUNT] = {
        { "H1", "a legal move starts on a piece of the side to move",
          "moves", 0, 0, 0, 0, 0 },
        { "H2", "a move onto an occupied square captures an enemy piece there",
          "moves onto an occupied square", 0, 0, 0, 0, 0 },
        { "H5", "a move changes only from, to, the castling rook and the "
                "en-passant victim",
          "moves", 0, 0, 0, 0, 0 },
        { "H6", "a pawn advances one rank, or two from its own home rank only",
          "pawn moves", 0, 0, 0, 0, 0 }
    };
    Coverage coverage = { 0, 0, 0 };
    Position pos;
    long visited = 0;
    long games = 0;
    int discharged = 0;
    int i;

    corpus_seed(seed);
    printf("corpus: seed 0x%016llx, %ld positions requested\n",
           seed, positions_wanted);

    while (visited < positions_wanted) {
        PositionFacts facts;
        Move legal[MAX_MOVES];
        Undo undo;
        int ply;

        if (!parse_fen(&pos, START_FEN)) {
            fprintf(stderr, "internal error: the initial array did not parse\n");
            return 1;
        }
        games++;

        for (ply = 0; ply < CORPUS_PLIES_PER_GAME; ply++) {
            int n = generate_legal_moves(&pos, legal);

            corpus_check_h1(&obligations[OB_H1], &pos, legal, n);
            corpus_check_h2(&obligations[OB_H2], &pos, legal, n);
            corpus_check_h5(&obligations[OB_H5], &pos, legal, n);
            corpus_check_h6(&obligations[OB_H6], &pos, legal, n);
            corpus_note_coverage(&coverage, legal, n);
            visited++;

            if (visited >= positions_wanted) {
                break;
            }
            /* Start a new game once this one is over.  The walk does not
             * count repetitions, so the third argument is what it has
             * actually seen -- this position, once.  A game that FIDE would
             * end by fivefold repetition simply runs on to the ply cap here,
             * which costs nothing: the corpus is a supply of positions, and
             * how its games end is not part of what is being checked.
             *
             * examine_position() generates the legal moves a second time
             * rather than being handed the list above.  That is a wasted
             * microsecond and not a second opinion; it is worth it to have
             * one function that says what a position's facts are, instead of
             * a copy of its body here that could drift from it. */
            examine_position(&pos, &facts);
            if (classify_position(&pos, &facts, 1) != TERM_CONTINUE) {
                break;
            }
            /* The walk never takes a move back, so the undo record is
             * written and dropped. */
            make_move(&pos, corpus_choose_move(&pos, legal, n), &undo);
        }
    }

    printf("\n");
    for (i = 0; i < OB_COUNT; i++) {
        const Obligation *ob = &obligations[i];
        int vacuous = (ob->moves == 0);
        int ok = (ob->exceptions == 0 && !vacuous);

        printf("[%s] %-4s %s\n", ob->tag,
               ok ? "ok" : (vacuous ? "none" : "FAIL"), ob->claim);
        printf("          %lld positions, %lld %s, %lld exceptions\n",
               ob->positions, ob->moves, ob->unit, ob->exceptions);
        if (ob->exceptions > ob->printed) {
            printf("          %lld further exceptions were not printed\n",
                   ob->exceptions - ob->printed);
        }
        if (vacuous) {
            printf("          nothing was checked, so this is not discharged: "
                   "a vacuous pass is a failure\n");
        }
        if (ob->doubles_from != 0) {
            char ranks[32];
            int len = 0;
            int r;

            for (r = 0; r < 8; r++) {
                if ((ob->doubles_from & (1u << r)) == 0) {
                    continue;
                }
                if (len > 0 && len < (int)sizeof ranks - 1) {
                    ranks[len++] = ' ';
                }
                if (len < (int)sizeof ranks - 1) {
                    ranks[len++] = (char)('1' + r);
                }
            }
            ranks[len] = '\0';
            printf("          double pushes seen only from ranks %s\n", ranks);
        }
        if (ok) {
            discharged++;
        }
    }

    printf("\ncorpus: among the moves checked, %lld castling moves, "
           "%lld en passant captures, %lld promotions\n",
           coverage.castling, coverage.en_passant, coverage.promotions);
    printf("corpus: %ld positions from %ld games, %d of %d obligations "
           "discharged\n", visited, games, discharged, OB_COUNT);
    return discharged == OB_COUNT ? 0 : 1;
}

/* ------------------------------------------------------------------------ */
/* PGN reading                                                              */
/*                                                                          */
/* The reference game is recorded in SAN, and SAN is not a move list: "Nge4" */
/* names a destination and leaves the reader to work out which knight can    */
/* legally get there.  Resolving that IS move generation.  If some other     */
/* program parsed the file and handed this one the resulting moves, that     */
/* program's move generator would still be part of what a reader has to      */
/* trust -- so the file is read here, and every SAN token is resolved        */
/* against the legal moves this program generates for itself.                */
/*                                                                          */
/* The reader is deliberately strict.  Comments, variations and annotation   */
/* glyphs do not occur in the file under test, and are refused rather than   */
/* skipped: a movetext token quietly dropped in the middle of a game would   */
/* leave a truncated move list, which the phases after this one would then   */
/* pronounce a perfectly legal -- and much shorter -- game.  A parse failure */
/* has to look like a failure.                                               */
/* ------------------------------------------------------------------------ */

typedef struct {
    FILE *file;
    const char *path;
    long line;        /* 1-based, for error messages */
    int pushback;     /* one pushed-back character, or EOF */
} PgnReader;

static void pgn_open_reader(PgnReader *r, FILE *file, const char *path)
{
    r->file = file;
    r->path = path;
    r->line = 1;
    r->pushback = EOF;
}

static int pgn_getc(PgnReader *r)
{
    int c;

    if (r->pushback != EOF) {
        c = r->pushback;
        r->pushback = EOF;
        return c;
    }
    c = fgetc(r->file);
    if (c == '\n') {
        r->line++;
    }
    return c;
}

/* Only ever called with one of the punctuation characters that ends a token,
 * never with a newline, so the line counter does not have to be rewound. */
static void pgn_ungetc(PgnReader *r, int c)
{
    r->pushback = c;
}

static int is_pgn_space(int c)
{
    return c == ' ' || c == '\t' || c == '\r' || c == '\n' ||
           c == '\f' || c == '\v';
}

/* Structural parse failures: a malformed tag, an unsupported construct.
 * Always returns 0 so a caller can write `return pgn_error(...)`. */
static int pgn_error(const PgnReader *r, const char *what, const char *token)
{
    fprintf(stderr, "error: %s:%ld: %s", r->path, r->line, what);
    if (token != NULL && token[0] != '\0') {
        fprintf(stderr, " (\"%s\")", token);
    }
    fprintf(stderr, "\n");
    return 0;
}

/* Failures that belong to one move of the game.  The ply and the token are
 * always named, because "this game does not parse" is not a useful thing to
 * tell someone holding a 17,000-move file. */
static int san_error(const PgnReader *r, int ply, const char *token,
                     const char *what)
{
    fprintf(stderr, "error: %s: ply %d, token \"%s\": %s\n",
            r->path, ply, token, what);
    return 0;
}

/* Consumes a  [Key "Value"]  tag pair.  The value is a quoted string that may
 * contain a ']' of its own, so the scan has to track quoting.
 *
 * The tag NAME is kept, because two of them change what the movetext means:
 * [FEN] and [SetUp] say the game does not begin from the initial array.
 * Skipping those and replaying from the initial array anyway would verify a
 * different game than the file describes. */
static int pgn_read_tag(PgnReader *r)
{
    char key[MAX_TOKEN];
    size_t len = 0;
    int in_quotes = 0;
    int in_key = 1;
    int c;

    while ((c = pgn_getc(r)) != EOF) {
        if (in_quotes) {
            if (c == '\\') {
                if (pgn_getc(r) == EOF) {
                    break;
                }
                continue;
            }
            if (c == '"') {
                in_quotes = 0;
            }
            continue;
        }
        if (c == '"') {
            in_quotes = 1;
            in_key = 0;
            continue;
        }
        if (c == ']') {
            key[len] = '\0';
            if (strcmp(key, "FEN") == 0 || strcmp(key, "SetUp") == 0) {
                return pgn_error(r, "games that do not start from the initial "
                                    "array are not supported", key);
            }
            return 1;
        }
        if (in_key) {
            if (is_pgn_space(c)) {
                in_key = 0;
            } else if (len < sizeof key - 1) {
                key[len++] = (char)c;
            }
        }
    }
    return pgn_error(r, "tag pair is not closed before end of file", NULL);
}

/* Reads the next movetext token.  Returns 1 for a token, 0 for end of file,
 * and -1 when a parse error has been reported. */
static int pgn_next_token(PgnReader *r, char *token)
{
    size_t len;
    int c;

    token[0] = '\0';
    for (;;) {
        do {
            c = pgn_getc(r);
        } while (is_pgn_space(c));

        if (c == EOF) {
            return 0;
        }
        if (c != '[') {
            break;
        }
        if (!pgn_read_tag(r)) {
            return -1;
        }
    }

    /* The constructs this file does not contain.  Refused, not skipped. */
    if (c == '{' || c == '}') {
        pgn_error(r, "comments { } are not supported", NULL);
        return -1;
    }
    if (c == '(' || c == ')') {
        pgn_error(r, "variations ( ) are not supported", NULL);
        return -1;
    }
    if (c == '$') {
        pgn_error(r, "numeric annotation glyphs $n are not supported", NULL);
        return -1;
    }
    if (c == ';') {
        pgn_error(r, "rest-of-line comments ; are not supported", NULL);
        return -1;
    }

    len = 0;
    while (c != EOF && !is_pgn_space(c)) {
        if (c == '{' || c == '}' || c == '(' || c == ')' ||
            c == '$' || c == ';' || c == '[') {
            pgn_ungetc(r, c);   /* reported on the next call */
            break;
        }
        if (len >= (size_t)(MAX_TOKEN - 1)) {
            token[len] = '\0';
            pgn_error(r, "movetext token is too long", token);
            return -1;
        }
        token[len++] = (char)c;
        c = pgn_getc(r);
    }
    token[len] = '\0';
    return 1;
}

static int is_result_token(const char *token)
{
    return strcmp(token, "1-0") == 0 || strcmp(token, "0-1") == 0 ||
           strcmp(token, "1/2-1/2") == 0 || strcmp(token, "*") == 0;
}

/* Measures a leading move number: digits followed by dots, as in "1.",
 * "8849." or the "1..." that resumes at Black's move.  Returns the number of
 * characters it occupies, which is 0 when the token does not begin with one.
 * Note that result tokens must be tested for first: "1/2-1/2" also starts
 * with a digit. */
static size_t move_number_prefix_length(const char *token)
{
    size_t i = 0;

    while (token[i] >= '0' && token[i] <= '9') {
        i++;
    }
    if (i == 0 || token[i] != '.') {
        return 0;
    }
    while (token[i] == '.') {
        i++;
    }
    return i;
}

/* One SAN token, taken apart but not yet matched to a move. */
typedef struct {
    int piece_type;    /* PAWN, KNIGHT, BISHOP, ROOK, QUEEN or KING       */
    int from_file;     /* 0-7 from a disambiguating file letter, else -1  */
    int from_rank;     /* 0-7 from a disambiguating rank digit, else -1   */
    int to;            /* destination square                              */
    int promotion;     /* EMPTY, or the piece named after '='             */
    int is_capture;    /* the token carried an 'x'                        */
    int castle;        /* MF_CASTLE_KING, MF_CASTLE_QUEEN, or 0           */
    int says_check;    /* the token ended in '+'                          */
    int says_mate;     /* the token ended in '#'                          */
} SanMove;

/* Piece letters are upper case in SAN, which is what keeps 'B' (bishop)
 * apart from 'b' (the b-file). */
static int san_piece_from_letter(char c)
{
    switch (c) {
    case 'K': return KING;
    case 'Q': return QUEEN;
    case 'R': return ROOK;
    case 'B': return BISHOP;
    case 'N': return KNIGHT;
    default:  return EMPTY;
    }
}

/* Splits a SAN token into its parts.  The shape being parsed is
 *
 *     [piece letter] [from file] [from rank] ['x'] file rank ['=' piece]
 *
 * read from the right, because the destination square is the only field that
 * is always present and always two characters wide.  Everything to the left
 * of it is the piece letter and the disambiguation. */
static int parse_san_token(const PgnReader *r, int ply, const char *token,
                           SanMove *san)
{
    char body[MAX_TOKEN];
    size_t len = strlen(token);
    size_t head = 0;    /* length of the piece letter: 1, or 0 for a pawn */
    size_t rest;        /* length of the piece letter plus disambiguation */

    san->piece_type = PAWN;
    san->from_file = -1;
    san->from_rank = -1;
    san->to = SQ_NONE;
    san->promotion = EMPTY;
    san->is_capture = 0;
    san->castle = 0;
    san->says_check = 0;
    san->says_mate = 0;

    /* Strip the check and checkmate marks.  The last token of the reference
     * game is "Qd7++" -- two plus signs, which no standard describes -- so any
     * run of '+' and '#' is accepted.  Annotation glyphs ('!', '?') are NOT
     * stripped: they do not occur in this file, and quietly ignoring a suffix
     * it does not understand is how a parser starts accepting anything. */
    while (len > 0 && (token[len - 1] == '+' || token[len - 1] == '#')) {
        if (token[len - 1] == '#') {
            san->says_mate = 1;
        } else {
            san->says_check = 1;
        }
        len--;
    }
    if (len == 0 || len >= sizeof body) {
        return san_error(r, ply, token, "not a move");
    }
    memcpy(body, token, len);
    body[len] = '\0';

    /* Castling, Art. 3.8.2.  PGN spells it with the letter O; digits are
     * accepted too because the two are widely confused in the wild. */
    if (strcmp(body, "O-O-O") == 0 || strcmp(body, "0-0-0") == 0) {
        san->piece_type = KING;
        san->castle = MF_CASTLE_QUEEN;
        return 1;
    }
    if (strcmp(body, "O-O") == 0 || strcmp(body, "0-0") == 0) {
        san->piece_type = KING;
        san->castle = MF_CASTLE_KING;
        return 1;
    }

    {
        int type = san_piece_from_letter(body[0]);

        if (type != EMPTY) {
            san->piece_type = type;
            head = 1;
        }
    }

    /* Promotion, Art. 3.7.3.3.  "=Q" is always the last thing in the token. */
    if (len >= 2 && body[len - 2] == '=') {
        san->promotion = san_piece_from_letter(body[len - 1]);
        if (san->promotion == EMPTY || san->promotion == KING) {
            return san_error(r, ply, token,
                             "a pawn promotes to Q, R, B or N (Art. 3.7.3.3)");
        }
        len -= 2;
        body[len] = '\0';
    }

    if (len < head + 2) {
        return san_error(r, ply, token, "no destination square");
    }
    san->to = square_from_string(body + len - 2);
    if (san->to == SQ_NONE) {
        return san_error(r, ply, token, "no destination square");
    }
    rest = len - 2;

    if (rest > head && body[rest - 1] == 'x') {
        san->is_capture = 1;
        rest--;
    }

    /* Whatever is left over is disambiguation: a file, a rank, or both. */
    if (rest - head > 2) {
        return san_error(r, ply, token, "more than two disambiguating "
                                        "characters");
    }
    if (rest - head == 2) {
        if (body[head] < 'a' || body[head] > 'h' ||
            body[head + 1] < '1' || body[head + 1] > '8') {
            return san_error(r, ply, token, "disambiguation is not a square");
        }
        san->from_file = body[head] - 'a';
        san->from_rank = body[head + 1] - '1';
    } else if (rest - head == 1) {
        if (body[head] >= 'a' && body[head] <= 'h') {
            san->from_file = body[head] - 'a';
        } else if (body[head] >= '1' && body[head] <= '8') {
            san->from_rank = body[head] - '1';
        } else {
            return san_error(r, ply, token,
                             "disambiguation is not a file or a rank");
        }
    }

    if (san->promotion != EMPTY && san->piece_type != PAWN) {
        return san_error(r, ply, token, "only a pawn may promote");
    }
    return 1;
}

/* Matches a parsed SAN token against the LEGAL moves of `pos`, and insists
 * that exactly one of them fits.
 *
 * Legal, not pseudo-legal, is the whole point: "Nge4" is ambiguous only if
 * both knights can lawfully reach e4, and a knight pinned against its own
 * king cannot.  A reader that disambiguated against pseudo-legal moves would
 * call a perfectly clear token ambiguous, and -- worse -- a reader that took
 * the first pseudo-legal match would sometimes take the pinned one. */
static int resolve_san(const PgnReader *r, Position *pos, const SanMove *san,
                       int ply, const char *token, Move *out)
{
    Move legal[MAX_MOVES];
    char candidates[256];
    size_t used = 0;
    int n = generate_legal_moves(pos, legal);
    int matches = 0;
    int i;

    candidates[0] = '\0';
    for (i = 0; i < n; i++) {
        Move move = legal[i];
        char text[MAX_MOVE_TEXT];
        size_t text_len;

        if (san->castle != 0) {
            if ((move.flags & san->castle) == 0) {
                continue;
            }
        } else {
            int piece = pos->board[move.from];
            int captures;

            /* "Kg1" is a king move and must not be answered with 0-0, even
             * though castling is generated as a two-square king move. */
            if (move.flags & (MF_CASTLE_KING | MF_CASTLE_QUEEN)) {
                continue;
            }
            if (PIECE_TYPE(piece) != san->piece_type) {
                continue;
            }
            if (move.to != san->to || move.promotion != san->promotion) {
                continue;
            }
            if (san->from_file >= 0 && FILE_OF(move.from) != san->from_file) {
                continue;
            }
            if (san->from_rank >= 0 && RANK_OF(move.from) != san->from_rank) {
                continue;
            }
            /* The 'x' is treated as information, not decoration.  An en
             * passant capture counts even though its destination square is
             * empty (Art. 3.7.3.1-3.7.3.2). */
            captures = (pos->board[move.to] != EMPTY) ||
                       ((move.flags & MF_EN_PASSANT) != 0);
            if (captures != san->is_capture) {
                continue;
            }
        }

        matches++;
        *out = move;

        move_to_string(move, text);
        text_len = strlen(text);
        if (used + text_len + 2 < sizeof candidates) {
            if (used > 0) {
                candidates[used++] = ' ';
            }
            memcpy(candidates + used, text, text_len + 1);
            used += text_len;
        }
    }

    if (matches == 1) {
        return 1;
    }
    {
        char why[384];

        if (matches == 0) {
            snprintf(why, sizeof why,
                     "no legal move matches (move %d, %s to play, %d legal "
                     "moves available)", pos->fullmove_number,
                     pos->side_to_move == WHITE ? "White" : "Black", n);
        } else {
            snprintf(why, sizeof why, "ambiguous: %d legal moves match [%s]",
                     matches, candidates);
        }
        return san_error(r, ply, token, why);
    }
}

/* The '+' and '#' marks are a statement the file makes about the position
 * after the move, so they are checked rather than thrown away.  Over a game
 * this long that is thousands of extra assertions about attack detection and
 * mate detection, obtained for nothing.
 *
 * `pos` is the position AFTER the move, so the side to move is the side the
 * mark is about.  A move that gives check and carries no mark is refused too:
 * the marks are only evidence if their absence means something.
 *
 * "++" is accepted as a check mark and nothing more.  It once meant mate, but
 * this phase does not adjudicate, and reading intent into a mark no standard
 * defines is not the checker's job. */
static int verify_check_marks(const PgnReader *r, Position *pos,
                              const SanMove *san, int ply, const char *token)
{
    int check = is_in_check(pos);

    if (san->says_mate) {
        if (!check || count_legal_moves(pos) != 0) {
            return san_error(r, ply, token,
                             "marked # but the move does not mate");
        }
        return 1;
    }
    if (san->says_check) {
        if (!check) {
            return san_error(r, ply, token,
                             "marked + but the move gives no check");
        }
        return 1;
    }
    if (check) {
        return san_error(r, ply, token,
                         "the move gives check but carries no + mark");
    }
    return 1;
}

/* The replayed game.  File scope and static: MAX_GAME_PLIES moves are far too
 * much for the stack, and this program does not allocate. */
static Move game_moves[MAX_GAME_PLIES];

/* Reads the first game of a PGN file, replaying it on a board as it goes,
 * because SAN cannot be resolved any other way.  Every move is required to be
 * legal in the position it is played in.  Returns 1 on success and writes the
 * ply count to *out_plies.
 *
 * The ply count is an OUTPUT.  Nothing in this program knows in advance how
 * long the game is meant to be; MAX_GAME_PLIES is only the size of the array
 * it will not be allowed to run past. */
static int read_pgn_game(const char *path, int *out_plies)
{
    PgnReader reader;
    Position pos;
    FILE *file;
    char token[MAX_TOKEN];
    int plies = 0;
    int status = 0;
    int ok = 1;

    file = fopen(path, "rb");
    if (file == NULL) {
        fprintf(stderr, "error: cannot open %s\n", path);
        return 0;
    }
    pgn_open_reader(&reader, file, path);

    if (!parse_fen(&pos, START_FEN)) {
        fclose(file);
        return 0;
    }

    while (ok && (status = pgn_next_token(&reader, token)) == 1) {
        const char *text = token;
        SanMove san;
        Move move;
        Undo undo;

        /* A result token ends the game.  Anything after it belongs to the
         * next game in the file, which this reader does not look at. */
        if (is_result_token(token)) {
            break;
        }
        text += move_number_prefix_length(token);
        if (*text == '\0') {
            continue;   /* the token was nothing but a move number */
        }

        if (plies >= MAX_GAME_PLIES) {
            fprintf(stderr, "error: %s: game is longer than %d plies\n",
                    path, MAX_GAME_PLIES);
            ok = 0;
            break;
        }
        if (!parse_san_token(&reader, plies + 1, text, &san) ||
            !resolve_san(&reader, &pos, &san, plies + 1, text, &move)) {
            ok = 0;
            break;
        }
        make_move(&pos, move, &undo);
        if (!verify_check_marks(&reader, &pos, &san, plies + 1, text)) {
            ok = 0;
            break;
        }
        game_moves[plies++] = move;
    }
    if (ok && status < 0) {
        ok = 0;   /* pgn_next_token has already said what went wrong */
    }
    fclose(file);

    if (!ok) {
        return 0;
    }
    /* A file with no movetext at all parses "successfully" into the empty
     * game, which is legal and worth nothing.  That is the truncation failure
     * mode in its most complete form, so it is refused here rather than
     * reported as a very short game. */
    if (plies == 0) {
        fprintf(stderr, "error: %s: no moves found\n", path);
        return 0;
    }
    *out_plies = plies;
    return 1;
}

/* Writes the replayed game as one UCI move per line, and nothing else, so
 * that the file can be compared byte for byte against another program's
 * reading of the same PGN. */
static int write_uci_file(const char *path, int plies)
{
    FILE *out = fopen(path, "w");
    int i;

    if (out == NULL) {
        fprintf(stderr, "error: cannot open %s for writing\n", path);
        return 0;
    }
    for (i = 0; i < plies; i++) {
        char text[MAX_MOVE_TEXT];

        move_to_string(game_moves[i], text);
        fprintf(out, "%s\n", text);
    }
    if (fclose(out) != 0) {
        fprintf(stderr, "error: could not finish writing %s\n", path);
        return 0;
    }
    return 1;
}

/* Writes the COMPLETE set of legal moves at every position the game passes
 * through, one line per ply:
 *
 *     <ply><TAB><space-separated UCI moves, sorted bytewise>
 *
 * The point is what the UCI dump above leaves out.  Comparing the moves that
 * were PLAYED shows that two move generators agree about those moves.  It
 * says nothing about the moves that were not played, and that is where a
 * generator's disagreements actually live: a castling right one side kept
 * and the other dropped, an en passant capture one side offers and the other
 * does not, a pin one side honours.  A game only exercises such a rule if it
 * happens to walk into it.  Comparing the whole legal-move SET at every
 * position exercises all of them at every position, whether the game used
 * them or not.
 *
 * Ply 0 is the starting array, and the last line is the position AFTER the
 * final move -- which, for a game that ends in mate or stalemate, has no
 * legal moves at all and so carries an empty list after its tab. */
static int write_moves_file(const char *path, int move_count)
{
    Position pos;
    FILE *out;
    char moves[MOVE_LIST_TEXT];
    int i;

    if (!parse_fen(&pos, START_FEN)) {
        return 0;
    }
    out = fopen(path, "w");
    if (out == NULL) {
        fprintf(stderr, "error: cannot open %s for writing\n", path);
        return 0;
    }
    for (i = 0; i <= move_count; i++) {
        Undo undo;

        legal_moves_text(&pos, moves, sizeof moves);
        fprintf(out, "%d\t%s\n", i, moves);
        if (i < move_count) {
            make_move(&pos, game_moves[i], &undo);
        }
    }
    if (fclose(out) != 0) {
        fprintf(stderr, "error: could not finish writing %s\n", path);
        return 0;
    }
    return 1;
}

/* ------------------------------------------------------------------------ */
/* Replaying a game under the FIDE termination rules                        */
/*                                                                          */
/* Reading the PGN established that every move is legal in the position it   */
/* is played in.  That is not enough to call the file a game: a game also    */
/* has to still be running when each of its moves is played.  This is where  */
/* that is decided.                                                          */
/* ------------------------------------------------------------------------ */

typedef struct {
    int plies;               /* moves actually played before the game ended */
    int termination;         /* one of the TERM_* values                    */
    int critical_moves;      /* pawn moves and captures actually played     */
    int critical_segments;   /* those, plus the closing quiet run if any    */
    int trace_rows;          /* records a trace of this game would hold     */
    char final_fen[MAX_FEN];
} GameResult;

/* Whether `move`, played in `pos`, resets the 75-move clock: a pawn move or a
 * capture.  Art. 9.6.2 counts moves "without the movement of any pawn and
 * without any capture", so these two and only these two close a quiet run.
 * Must be asked BEFORE the move is made, while the board still shows what was
 * standing on the destination square.
 *
 * Neither special case needs special code: en passant is a pawn move and a
 * capture at once, and a promotion is a pawn move. */
static int is_critical_move(const Position *pos, Move move)
{
    if (PIECE_TYPE(pos->board[move.from]) == PAWN) {
        return 1;
    }
    return pos->board[move.to] != EMPTY;
}

/* Whether `move` is one of the legal moves of `pos`.  The PGN reader would
 * have refused the file already if it were not, but the replay is meant to be
 * the judge on its own terms, so it asks again rather than inheriting the
 * answer. */
static int move_is_legal_here(Position *pos, Move move)
{
    Move legal[MAX_MOVES];
    int n = generate_legal_moves(pos, legal);
    int i;

    for (i = 0; i < n; i++) {
        if (legal[i].from == move.from && legal[i].to == move.to &&
            legal[i].promotion == move.promotion) {
            return 1;
        }
    }
    return 0;
}

/* The trace is a tab-separated table with one row per ply and a header row.
 * Ply 0 is the starting position and carries no move, so every row's
 * "position before the move" is the previous row's FEN.  The format is fixed:
 * being able to diff two independent replays ply by ply is the only practical
 * way to localise a disagreement in a game this long, and that only works if
 * both sides spell it identically. */
static void write_trace_header(FILE *out)
{
    if (out != NULL) {
        fprintf(out,
                "ply\tfen\tuci\tcritical\thalfmove_clock\trepetitions\t"
                "termination\n");
    }
}

static void write_trace_row(FILE *out, int ply, const char *fen,
                            const char *uci, int critical, int halfmove_clock,
                            int repetitions, int termination)
{
    if (out != NULL) {
        fprintf(out, "%d\t%s\t%s\t%d\t%d\t%d\t%s\n", ply, fen, uci,
                critical ? 1 : 0, halfmove_clock, repetitions,
                termination_name(termination));
    }
}

/* Replays the first `move_count` moves of game_moves[] from the starting
 * array, applying the termination rules after every ply.  Returns 1 if the
 * move sequence is a game and 0 if it is not, having said why on stderr.
 * `trace` may be NULL, in which case no trace is written.
 *
 * Two things make a move sequence not a game, and both are rejections rather
 * than quiet truncations:
 *
 *   - a move that is not legal in the position it is played in;
 *   - moves left over after the game has already ended.  A file that records
 *     play continuing past its own checkmate is not a longer game, it is a
 *     corrupt file, and accepting the prefix would report a length that the
 *     file does not actually claim. */
static int replay_game(int move_count, FILE *trace, GameResult *result)
{
    Position pos;
    PositionFacts facts;
    unsigned char key[REP_KEY_BYTES];
    char fen[MAX_FEN];
    int termination;
    int repetitions;
    int last_critical_ply = 0;
    int consumed;

    result->plies = 0;
    result->termination = TERM_CONTINUE;
    result->critical_moves = 0;
    result->critical_segments = 0;
    result->trace_rows = 0;
    result->final_fen[0] = '\0';

    if (!parse_fen(&pos, START_FEN)) {
        return 0;
    }
    repetition_reset();

    /* The starting position is classified too.  A position handed in already
     * mated, stalemated or dead is not a game with no moves played -- it is
     * not a game at all, and letting it through would mean "verifying" moves
     * that could never have been made. */
    examine_position(&pos, &facts);
    build_repetition_key(&pos, facts.legal_ep, key);
    repetitions = repetition_record(key);
    termination = classify_position(&pos, &facts, repetitions);
    if (termination != TERM_CONTINUE) {
        fprintf(stderr, "REJECTED: the starting position is already over by "
                        "%s\n", termination_name(termination));
        return 0;
    }

    write_trace_header(trace);
    write_fen(&pos, facts.legal_ep, fen, sizeof fen);
    write_trace_row(trace, 0, fen, "", 0, pos.halfmove_clock, repetitions,
                    TERM_CONTINUE);
    result->trace_rows = 1;

    for (consumed = 0;
         consumed < move_count && termination == TERM_CONTINUE;
         consumed++) {
        Move move = game_moves[consumed];
        Undo undo;
        char uci[MAX_MOVE_TEXT];
        int ply = consumed + 1;
        int critical;

        move_to_string(move, uci);
        if (!move_is_legal_here(&pos, move)) {
            position_to_fen(&pos, fen, sizeof fen);
            fprintf(stderr, "REJECTED: ply %d: illegal move %s in %s\n",
                    ply, uci, fen);
            return 0;
        }

        critical = is_critical_move(&pos, move);
        make_move(&pos, move, &undo);

        examine_position(&pos, &facts);
        build_repetition_key(&pos, facts.legal_ep, key);
        repetitions = repetition_record(key);
        if (repetitions == 0) {
            fprintf(stderr, "REJECTED: ply %d: the repetition table is full\n",
                    ply);
            return 0;
        }
        termination = classify_position(&pos, &facts, repetitions);

        if (critical) {
            result->critical_moves++;
            last_critical_ply = ply;
        }

        /* The FEN in the trace spells the en passant field the way Art. 9.2.2
         * counts positions: the square is written only when the capture is
         * really available.  That keeps the trace and the repetition key
         * telling the same story about which positions are the same. */
        write_fen(&pos, facts.legal_ep, fen, sizeof fen);
        write_trace_row(trace, ply, fen, uci, critical, pos.halfmove_clock,
                        repetitions, termination);
        result->trace_rows++;
    }

    if (consumed < move_count) {
        fprintf(stderr, "REJECTED: game ended at ply %d by %s with %d move(s) "
                        "unplayed\n", consumed, termination_name(termination),
                move_count - consumed);
        return 0;
    }

    result->plies = consumed;
    result->termination = termination;

    /* Critical SEGMENTS, which is what a segment decomposition counts.  Each
     * pawn move or capture closes a segment behind it, and the quiet moves
     * after the last one form a closing segment of their own -- one that is
     * only closed if the game is actually over.  That is plainest for a
     * checkmate, which outranks the 75-move draw and so lets its segment run
     * to the end and then some, but it is equally true of a game that ends by
     * the 75-move rule, by fivefold repetition or in stalemate.  A game whose
     * final move is itself critical has no closing segment; a game still in
     * progress has not closed one yet. */
    result->critical_segments = result->critical_moves;
    if (termination != TERM_CONTINUE && last_critical_ply != consumed) {
        result->critical_segments++;
    }

    write_fen(&pos, facts.legal_ep, result->final_fen,
              sizeof result->final_fen);
    return 1;
}

/* Writes the trace, by replaying the accepted game a second time.
 *
 * A second pass rather than a running write, so that a game this program
 * REJECTS never leaves a half-written trace behind that reads like the record
 * of a legal one.  The replay costs a fraction of a second and buys the rule
 * that a trace file exists only for a game that was accepted whole. */
static int write_trace_file(const char *path, int move_count,
                            GameResult *result)
{
    FILE *out = fopen(path, "w");
    int ok;

    if (out == NULL) {
        fprintf(stderr, "error: cannot open %s for writing\n", path);
        return 0;
    }
    ok = replay_game(move_count, out, result);
    if (fclose(out) != 0) {
        fprintf(stderr, "error: could not finish writing %s\n", path);
        return 0;
    }
    return ok;
}

/* ------------------------------------------------------------------------ */
/* Command line                                                             */
/* ------------------------------------------------------------------------ */

static void print_usage(FILE *out)
{
    fprintf(out,
        "longest_check -- independent FIDE-rules chess checker\n"
        "\n"
        "  longest_check --perft \"<FEN>\" <depth>\n"
        "        print the perft node count for a position\n"
        "  longest_check --perft-divide \"<FEN>\" <depth>\n"
        "        print per-root-move node counts, then the total\n"
        "  longest_check --perft-suite [--max-depth D]\n"
        "        run the built-in reference table (default: every depth in it)\n"
        "  longest_check --rule-cases\n"
        "        run the built-in table of hand-written FIDE rule cases\n"
        "  longest_check --material-scan\n"
        "        walk the whole domain of the Art. 5.2.2 material test and\n"
        "        print \"<FEN>\\t<dead|alive>\" for every inventory in it, for\n"
        "        comparison against python-chess\n"
        "  longest_check --corpus <positions> [--seed <n>]\n"
        "        walk random legal games and check obligations [H1] [H2]\n"
        "        [H5] [H6] -- the claims about the rules of chess that the\n"
        "        home-rank lemma in src/long_chess/bound/invariant.py leans\n"
        "        on -- over every legal move of every position visited\n"
        "  longest_check --moves \"<FEN>\"\n"
        "        list the legal moves in a position\n"
        "  longest_check --fen \"<FEN>\"\n"
        "        re-emit the position as FEN (round-trip check)\n"
        "  longest_check <file.pgn> [--trace <file>] [--expect-plies <n>]\n"
        "                           [--expect-termination <name>]\n"
        "                           [--dump-uci <file>] [--dump-moves <file>]\n"
        "        read the PGN, replay it under the FIDE termination rules,\n"
        "        and report how long the game is and how it ends.\n"
        "        --trace writes the per-ply log as TSV\n"
        "        --dump-uci writes the moves as one UCI move per line\n"
        "        --dump-moves writes, for every position of the game, all of\n"
        "        its legal moves: \"<ply>\\t<sorted UCI moves>\"\n"
        "        --expect-plies and --expect-termination turn the report into\n"
        "        a test: the run fails unless the replay agrees.  A name is\n"
        "        one of checkmate, stalemate, insufficient-material,\n"
        "        fivefold-repetition, seventyfive-move-rule\n"
        "\n");
}

/* Strict integer argument: no trailing junk, no silly magnitudes. */
static int parse_depth_arg(const char *text, int *out)
{
    char *end;
    long value = strtol(text, &end, 10);

    if (end == text || *end != '\0' || value < 0 || value > 20) {
        return 0;
    }
    *out = (int)value;
    return 1;
}

/* Same, for a ply count.  The ceiling is the size of the array a game is
 * replayed into, and expresses no opinion about how long any game is. */
static int parse_ply_count_arg(const char *text, int *out)
{
    char *end;
    long value = strtol(text, &end, 10);

    if (end == text || *end != '\0' || value < 0 || value > MAX_GAME_PLIES) {
        return 0;
    }
    *out = (int)value;
    return 1;
}

/* How many positions the corpus walk should visit.  The ceiling is there to
 * catch a mistyped argument, not to express an opinion about how large a
 * corpus is worth running. */
#define CORPUS_MAX_POSITIONS 10000000L

static int parse_corpus_count_arg(const char *text, long *out)
{
    char *end;
    long value = strtol(text, &end, 10);

    if (end == text || *end != '\0' || value < 1 ||
        value > CORPUS_MAX_POSITIONS) {
        return 0;
    }
    *out = value;
    return 1;
}

/* Any 64-bit value is a valid seed, in decimal or with a 0x prefix.  A value
 * too large to represent saturates rather than being refused; the run prints
 * the seed it actually used, so it stays reproducible either way. */
static int parse_seed_arg(const char *text, unsigned long long *out)
{
    char *end;
    unsigned long long value = strtoull(text, &end, 0);

    if (end == text || *end != '\0') {
        return 0;
    }
    *out = value;
    return 1;
}

/* True for the options that take a following value. */
static int option_takes_value(const char *option)
{
    return strcmp(option, "--trace") == 0 ||
           strcmp(option, "--dump-uci") == 0 ||
           strcmp(option, "--dump-moves") == 0 ||
           strcmp(option, "--expect-plies") == 0 ||
           strcmp(option, "--expect-termination") == 0;
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        print_usage(stderr);
        return 2;
    }

    if (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0) {
        print_usage(stdout);
        return 0;
    }

    /* A first argument that is not an option is a PGN file to read. */
    if (argv[1][0] != '-') {
        const char *pgn_path = argv[1];
        const char *uci_path = NULL;
        const char *moves_path = NULL;
        const char *trace_path = NULL;
        /* Both claims start unmade: a negative ply count and TERM_CONTINUE
         * are values no replay can produce, so "unset" needs no extra flag. */
        int expect_plies = -1;
        int expect_termination = TERM_CONTINUE;
        GameResult result;
        int plies = 0;
        int failures = 0;
        int i;

        for (i = 2; i < argc; i++) {
            const char *option = argv[i];
            const char *value;

            if (!option_takes_value(option)) {
                fprintf(stderr, "error: unknown argument '%s'\n", option);
                return 2;
            }
            if (i + 1 >= argc) {
                fprintf(stderr, "error: %s needs a value\n", option);
                return 2;
            }
            value = argv[++i];

            if (strcmp(option, "--trace") == 0) {
                trace_path = value;
            } else if (strcmp(option, "--dump-uci") == 0) {
                uci_path = value;
            } else if (strcmp(option, "--dump-moves") == 0) {
                moves_path = value;
            } else if (strcmp(option, "--expect-plies") == 0) {
                if (!parse_ply_count_arg(value, &expect_plies)) {
                    fprintf(stderr, "error: bad ply count '%s'\n", value);
                    return 2;
                }
            } else {
                expect_termination = termination_from_name(value);
                if (expect_termination == TERM_CONTINUE) {
                    fprintf(stderr, "error: '%s' is not a way for a game to "
                                    "end\n", value);
                    return 2;
                }
            }
        }

        if (!read_pgn_game(pgn_path, &plies)) {
            return 1;
        }
        if (uci_path != NULL && !write_uci_file(uci_path, plies)) {
            return 1;
        }
        if (!replay_game(plies, NULL, &result)) {
            return 1;
        }

        printf("%-19s%d\n", "plies", result.plies);
        printf("%-19s%s\n", "termination",
               termination_name(result.termination));
        printf("%-19s%d\n", "critical segments", result.critical_segments);
        printf("%-19s%s\n", "final fen", result.final_fen);

        if (trace_path != NULL) {
            if (!write_trace_file(trace_path, plies, &result)) {
                return 1;
            }
            printf("%-19s%d records -> %s\n", "trace", result.trace_rows,
                   trace_path);
        }
        /* Written only for a game that was accepted whole, for the same
         * reason the trace is: a dump left behind by a rejected game reads
         * exactly like the record of a legal one. */
        if (moves_path != NULL) {
            if (!write_moves_file(moves_path, result.plies)) {
                return 1;
            }
            printf("%-19s%d positions -> %s\n", "legal moves",
                   result.plies + 1, moves_path);
        }

        /* The expectations are checked last, so that the report is printed
         * whether or not it is the report that was expected.  A checker that
         * only speaks when it agrees is not much use when it disagrees. */
        if (expect_plies >= 0 && result.plies != expect_plies) {
            fprintf(stderr, "FAIL: expected %d plies, got %d\n",
                    expect_plies, result.plies);
            failures++;
        }
        if (expect_termination != TERM_CONTINUE &&
            result.termination != expect_termination) {
            fprintf(stderr, "FAIL: expected %s, got %s\n",
                    termination_name(expect_termination),
                    termination_name(result.termination));
            failures++;
        }
        return failures == 0 ? 0 : 1;
    }

    if (strcmp(argv[1], "--perft") == 0 ||
        strcmp(argv[1], "--perft-divide") == 0) {
        Position pos;
        int depth;

        if (argc != 4) {
            fprintf(stderr, "error: %s needs a FEN and a depth\n", argv[1]);
            return 2;
        }
        if (!parse_fen(&pos, argv[2])) {
            return 2;
        }
        if (!parse_depth_arg(argv[3], &depth)) {
            fprintf(stderr, "error: bad depth '%s'\n", argv[3]);
            return 2;
        }
        if (strcmp(argv[1], "--perft") == 0) {
            printf("%lld\n", perft(&pos, depth));
        } else {
            perft_divide(&pos, depth);
        }
        return 0;
    }

    if (strcmp(argv[1], "--moves") == 0 || strcmp(argv[1], "--fen") == 0) {
        Position pos;

        if (argc != 3) {
            fprintf(stderr, "error: %s needs a FEN\n", argv[1]);
            return 2;
        }
        if (!parse_fen(&pos, argv[2])) {
            return 2;
        }
        if (strcmp(argv[1], "--moves") == 0) {
            print_legal_moves(&pos);
        } else {
            char fen[MAX_FEN];

            position_to_fen(&pos, fen, sizeof fen);
            printf("%s\n", fen);
        }
        return 0;
    }

    if (strcmp(argv[1], "--perft-suite") == 0) {
        int max_depth = PERFT_MAX_DEPTH;

        if (argc == 4 && strcmp(argv[2], "--max-depth") == 0) {
            if (!parse_depth_arg(argv[3], &max_depth)) {
                fprintf(stderr, "error: bad depth '%s'\n", argv[3]);
                return 2;
            }
        } else if (argc != 2) {
            fprintf(stderr, "error: --perft-suite takes only --max-depth D\n");
            return 2;
        }
        return run_perft_suite(max_depth);
    }

    if (strcmp(argv[1], "--rule-cases") == 0) {
        if (argc != 2) {
            fprintf(stderr, "error: --rule-cases takes no arguments\n");
            return 2;
        }
        return run_rule_cases();
    }

    if (strcmp(argv[1], "--material-scan") == 0) {
        if (argc != 2) {
            fprintf(stderr, "error: --material-scan takes no arguments\n");
            return 2;
        }
        material_scan();
        return 0;
    }

    if (strcmp(argv[1], "--corpus") == 0) {
        unsigned long long seed = CORPUS_DEFAULT_SEED;
        long positions;

        if (argc != 3 && argc != 5) {
            fprintf(stderr, "error: --corpus needs a position count, and "
                            "takes only --seed S after it\n");
            return 2;
        }
        if (!parse_corpus_count_arg(argv[2], &positions)) {
            fprintf(stderr, "error: bad position count '%s'\n", argv[2]);
            return 2;
        }
        if (argc == 5) {
            if (strcmp(argv[3], "--seed") != 0) {
                fprintf(stderr, "error: unknown argument '%s'\n", argv[3]);
                return 2;
            }
            if (!parse_seed_arg(argv[4], &seed)) {
                fprintf(stderr, "error: bad seed '%s'\n", argv[4]);
                return 2;
            }
        }
        return run_corpus(positions, seed);
    }

    fprintf(stderr, "error: unknown option '%s'\n", argv[1]);
    print_usage(stderr);
    return 2;
}
