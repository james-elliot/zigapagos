const std = @import("std");

// 27 bits use 2GB
const NB_BITS: u8 = 28;
const NB_PLATES: usize = 4;
const MAX_PAWNS: usize = 2 * NB_PLATES - 1;

const Vals = i16;
const Vals_min: Vals = std.math.minInt(Vals);
const Vals_max: Vals = std.math.maxInt(Vals);
const Depth = u8;
const Colors = u8;
const Sigs = u64;
const Move = u16;
const InvalidMove: Move = std.math.maxInt(Move);
const Win = Vals_max - 1;
//const Win = 1;

const EMPTY: Colors = 0;
const WHITE: Colors = 1;
const BLACK: Colors = 2;
const NB_COLS: usize = BLACK + 1;
const HASH_SIZE: usize = 1 << NB_BITS;
const HASH_MASK: Sigs = HASH_SIZE - 1;

var tab: [NB_PLATES][NB_COLS]u8 = undefined;
var pos: [NB_PLATES]u8 = undefined;
var rems: u8 = undefined;
var rem_cols: [NB_COLS]u8 = undefined;

var hashesw: [NB_PLATES][MAX_PAWNS + 1]Sigs = undefined;
var hashesb: [NB_PLATES][MAX_PAWNS + 1]Sigs = undefined;
var hashesp: [NB_PLATES][NB_PLATES]Sigs = undefined;

const HashElem = packed struct {
    sig: Sigs,
    v_inf: Vals,
    v_sup: Vals,
    d: Depth,
    bmove: Move,
};

const ZHASH = HashElem{
    .sig = 0,
    .v_inf = Vals_min,
    .v_sup = Vals_max,
    .d = 0,
    .bmove = InvalidMove,
};

var hashes: []HashElem = undefined;

fn retrieve(hv: Sigs, v_inf: *Vals, v_sup: *Vals, lmove: *Move, depth: Depth) bool {
    const ind: usize = hv & HASH_MASK;
    const d = std.math.maxInt(Depth) - depth;
    if (hashes[ind].sig == hv) {
        lmove.* = hashes[ind].bmove;
        if (hashes[ind].d == d) {
            v_inf.* = hashes[ind].v_inf;
            v_sup.* = hashes[ind].v_sup;
            return true;
        }
    }
    return false;
}

fn store(hv: Sigs, alpha: Vals, beta: Vals, g: Vals, depth: Depth, bmove: Move) void {
    const ind = hv & HASH_MASK;
    const d = std.math.maxInt(Depth) - depth;
    if (hashes[ind].d <= d) {
        if ((hashes[ind].sig != hv) or (hashes[ind].d != d)) {
            hashes[ind].d = d;
            hashes[ind].v_inf = Vals_min;
            hashes[ind].v_sup = Vals_max;
            hashes[ind].sig = hv;
        }
        hashes[ind].bmove = bmove;
        if ((g > alpha) and (g < beta)) {
            hashes[ind].v_inf = g;
            hashes[ind].v_sup = g;
        } else if (g <= alpha) {
            hashes[ind].v_sup = @min(g, hashes[ind].v_sup);
        } else if (g >= beta) {
            hashes[ind].v_inf = @max(g, hashes[ind].v_inf);
        }
    }
}

fn compute_hash() Sigs {
    var h: Sigs = 0;
    for (0..NB_PLATES) |i| {
        h ^= hashesw[i][tab[i][WHITE]];
        h ^= hashesb[i][tab[i][BLACK]];
    }
    for (0..NB_PLATES) |i| {
        h ^= hashesp[i][pos[i]];
    }
    return h;
}

fn play_pos(
    a: Vals,
    b: Vals,
    depth: Depth,
    base: Depth,
    p1: usize,
    color: Colors,
    oppcol: Colors,
    n_pos: [NB_PLATES]u8,
    n_tab: [NB_PLATES][NB_COLS]u8,
) Vals {
    const b1 = pos[p1];
    tab[b1][EMPTY] -= 1;
    tab[b1][color] += 1;
    if (p1 != NB_PLATES - 1) {
        const p2 = p1 + 1;
        const b2 = pos[p2];
        pos[p1] = b2;
        pos[p2] = b1;
    }
    rems -= 1;
    rem_cols[color] -= 1;
    const v = ab(a, b, oppcol, depth + 1, base);
    rem_cols[color] += 1;
    rems += 1;
    pos = n_pos;
    tab = n_tab;
    return v;
}

fn play_move(
    a: Vals,
    b: Vals,
    depth: Depth,
    base: Depth,
    k1: usize,
    k2: usize,
    color: Colors,
    oppcol: Colors,
    n_tab: [NB_PLATES][NB_COLS]u8,
) Vals {
    tab[pos[k1]][color] -= 1;
    tab[pos[k1]][EMPTY] += 1;
    tab[pos[k2]][color] += 1;
    tab[pos[k2]][EMPTY] -= 1;
    const v = ab(a, b, oppcol, depth + 1, base);
    tab = n_tab;
    return v;
}
var best_move: Move = undefined;
fn updateab(color: Colors, depth: Depth, base: Depth, v: Vals, a: *Vals, b: *Vals, g: *Vals, p: u64, lmove: *Move) bool {
    if (color == WHITE) {
        if (v > g.*) {
            g.* = v;
            lmove.* = @as(Move, @intCast(p));
            if (depth == base) {
                best_move = lmove.*;
            }
        }
        a.* = @max(a.*, g.*);
    } else {
        if (v < g.*) {
            g.* = v;
            lmove.* = @as(Move, @intCast(p));
            if (depth == base) {
                best_move = lmove.*;
            }
        }
        b.* = @min(b.*, g.*);
    }
    return (a.* >= b.*);
}

fn ab(alp: Vals, bet: Vals, color: Colors, depth: Depth, base: Depth) Vals {
    if (rems == 0) {
        if (tab[pos[NB_PLATES - 1]][WHITE] > tab[pos[NB_PLATES - 1]][BLACK]) {
            return Win - @as(Vals, depth);
            //return 1;
        } else {
            return -Win + @as(Vals, depth);
            //return -1;
        }
    }

    var alpha = alp;
    var beta = bet;
    var lmove: Move = InvalidMove;
    var bmove: Move = InvalidMove;
    const hv = compute_hash();
    var v_inf: Vals = undefined;
    var v_sup: Vals = undefined;
    if (retrieve(hv, &v_inf, &v_sup, &bmove, depth)) {
        if (depth == base) {
            best_move = bmove;
        }
        if (v_inf == v_sup) return v_inf;
        if (v_inf >= beta) return v_inf;
        if (v_sup <= alpha) return v_sup;
        alpha = @max(alpha, v_inf);
        beta = @min(beta, v_sup);
    }

    var a = alpha;
    var b = beta;

    const oppcol = if (color == WHITE) BLACK else WHITE;
    var g: Vals = if (color == WHITE) Vals_min else Vals_max;
    const n_tab = tab;
    const n_pos = pos;

    outer: {
        for (0..NB_PLATES) |p| {
            if ((tab[pos[p]][EMPTY] > 0) and (rem_cols[color] > 0)) {
                const v = play_pos(a, b, depth, base, p, color, oppcol, n_pos, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, p, &lmove)) {
                    break :outer;
                }
            }
        }
        for (0..NB_PLATES) |p| {
            if ((tab[pos[p]][EMPTY] > 0) and (rem_cols[oppcol] > 0)) {
                const v = play_pos(a, b, depth, base, p, oppcol, oppcol, n_pos, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, p + 8, &lmove)) {
                    break :outer;
                }
            }
        }
        for (1..NB_PLATES) |p| {
            if (tab[pos[p]][color] > 0) {
                for (0..p) |k| {
                    if (tab[pos[k]][EMPTY] > 0) {
                        const v = play_move(a, b, depth, base, p, k, color, oppcol, n_tab);
                        if (updateab(color, depth, base, v, &a, &b, &g, 16 + p + (k * 8), &lmove)) {
                            break :outer;
                        }
                    }
                }
            }
        }
    }
    store(hv, alpha, beta, g, depth, lmove);
    return g;
}

fn print_pos(stdout: std.fs.File.Writer) !void {
    for (0..NB_PLATES) |i| {
        const p = pos[NB_PLATES - 1 - i];
        for (0..tab[p][WHITE]) |_| {
            try stdout.print("O ", .{});
        }
        for (0..tab[p][BLACK]) |_| {
            try stdout.print("X ", .{});
        }
        for (0..tab[p][EMPTY]) |_| {
            try stdout.print(". ", .{});
        }
        try stdout.print("\n", .{});
    }
}

fn print_move(stdout: std.fs.File.Writer, m: Move) !void {
    if (m < 8) {
        try stdout.print("I put my marble on:{d}\n", .{m});
    } else if (m < 16) {
        try stdout.print("I put YOUR marble on:{d}\n", .{(m - 8)});
    } else {
        try stdout.print("I move my marble from {d} to {d}\n", .{ (m - 16) % 8, (m - 16) / 8 });
    }
}

fn really_play_move(m: Move, color: Colors) bool {
    if (m < 8) {
        const p1 = m;
        if (p1 >= NB_PLATES) return false;
        const b1 = pos[p1];
        if ((rems == 0) or (rem_cols[color] == 0) or (tab[b1][EMPTY] == 0)) {
            return false;
        }
        tab[b1][EMPTY] -= 1;
        tab[b1][color] += 1;
        if (p1 != NB_PLATES - 1) {
            const p2 = p1 + 1;
            const b2 = pos[p2];
            pos[p1] = b2;
            pos[p2] = b1;
        }
        rems -= 1;
        rem_cols[color] -= 1;
    } else if (m < 16) {
        const p1 = m - 8;
        if (p1 >= NB_PLATES) return false;
        const b1 = pos[p1];
        const oppcol = if (color == WHITE) BLACK else WHITE;
        if ((rems == 0) or (rem_cols[oppcol] == 0) or (tab[b1][EMPTY] == 0)) {
            return false;
        }
        tab[b1][EMPTY] -= 1;
        tab[b1][oppcol] += 1;
        if (p1 != NB_PLATES - 1) {
            const p2 = p1 + 1;
            const b2 = pos[p2];
            pos[p1] = b2;
            pos[p2] = b1;
        }
        rems -= 1;
        rem_cols[oppcol] -= 1;
    } else {
        const k1 = (m - 16) % 8;
        const k2 = (m - 16) / 8;
        if ((k1 >= NB_PLATES) or (k2 >= NB_PLATES)) return false;
        if ((tab[pos[k1]][color] == 0) or (tab[pos[k2]][EMPTY] == 0)) {
            return false;
        }
        tab[pos[k1]][color] -= 1;
        tab[pos[k1]][EMPTY] += 1;
        tab[pos[k2]][color] += 1;
        tab[pos[k2]][EMPTY] -= 1;
    }
    return true;
}

pub fn main() !void {
    const stdout = std.io.getStdOut().writer();
    const stdin = std.io.getStdIn().reader();

    for (0..NB_PLATES) |i| {
        pos[i] = @as(u8, @intCast(i));
        tab[i][EMPTY] = 2 * @as(u8, @intCast(i)) + 1;
        tab[i][WHITE] = 0;
        tab[i][BLACK] = 0;
    }
    rems = NB_PLATES * NB_PLATES;
    rem_cols[WHITE] = 10;
    rem_cols[BLACK] = 10;
    try print_pos(stdout);

    const allocator = std.heap.page_allocator;
    const RndGen = std.Random.DefaultPrng;
    hashes = try allocator.alloc(HashElem, HASH_SIZE);
    defer allocator.free(hashes);
    for (hashes) |*a| a.* = ZHASH;
    var rnd = RndGen.init(0);
    for (&hashesw) |*b| {
        for (b) |*a| a.* = rnd.random().int(Sigs);
    }
    for (&hashesb) |*b| {
        for (b) |*a| a.* = rnd.random().int(Sigs);
    }
    for (&hashesp) |*b| {
        for (b) |*a| a.* = rnd.random().int(Sigs);
    }

    var base: Depth = 0;
    var t: i64 = undefined;
    var ret: Vals = undefined;
    const color: Colors = WHITE;
    var buf: [1000]u8 = undefined;

    while (true) {
        best_move = InvalidMove;
        t = std.time.milliTimestamp();
        ret = ab(Vals_min, Vals_max, WHITE, base, base);
        if (best_move == InvalidMove) {
            break;
        }
        t = std.time.milliTimestamp() - t;
        try stdout.print("t={d}ms\n", .{t});
        try stdout.print("ret={d}\n", .{ret});
        try stdout.print("best_move={d}\n", .{best_move});
        try print_move(stdout, best_move);
        if (!(really_play_move(best_move, color))) {
            break;
        }
        try print_pos(stdout);
        base += 1;
        try stdout.print("Your move:", .{});
        if (try stdin.readUntilDelimiterOrEof(&buf, '\n')) |m| {
            std.debug.print("msg: {s}\n", .{m});
            const i = std.fmt.parseInt(Move, m, 10) catch InvalidMove;
            std.debug.print("i: {d}\n", .{i});
        }
    }
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
