const std = @import("std");

const stdin = std.io.getStdIn().reader();
const stdout = std.io.getStdOut().writer();
const stderr = std.io.getStdErr().writer();

// Number of plates must be less or equal to 8
const NB_PLATES: usize = 5;
const NB_PAWNS_BY_COLOR: u8 = 15; // We need at least (NB_PLATES*NB_PLATES)/2 marbles for each color
const FIND_SHORTEST: bool = true; // Find shortest path/best defence, or simply win/lose
const USE_BMOVE: bool = false; // Looks like, for finding the shortest solution, it is better not to use bmove...

// 27 bits use 2GB
const NB_BITS: u8 = 28;

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
const Bwin = Win / 2;
const EMPTY: Colors = 0;
const WHITE: Colors = 1;
const BLACK: Colors = 2;
const NB_COLS: usize = BLACK + 1;

var tab: [NB_PLATES][NB_COLS]u8 = undefined;
var pos: [NB_PLATES]u8 = undefined;
var rems: u8 = undefined;
var rem_cols: [NB_COLS]u8 = undefined;

const HASH_SIZE: usize = 1 << NB_BITS;
const HASH_MASK: Sigs = HASH_SIZE - 1;
var hashesw: [NB_PLATES][MAX_PAWNS + 1]Sigs = undefined;
var hashesb: [NB_PLATES][MAX_PAWNS + 1]Sigs = undefined;
var hashesp: [NB_PLATES][NB_PLATES]Sigs = undefined;
var hash_black: Sigs = undefined;

const HashElem = packed struct {
    sig: Sigs,
    v_inf: Vals,
    v_sup: Vals,
    base: Depth,
    dist: Depth,
    bmove: Move,
};

const ZHASH = HashElem{
    .sig = 0,
    .v_inf = Vals_min,
    .v_sup = Vals_max,
    .base = 0,
    .dist = 0,
    .bmove = InvalidMove,
};

var hashes: []HashElem = undefined;

fn retrieve(hv: Sigs, v_inf: *Vals, v_sup: *Vals, bmove: *Move, dist: Depth) bool {
    const ind: usize = hv & HASH_MASK;
    if (hashes[ind].sig == hv) {
        bmove.* = hashes[ind].bmove;
        if (hashes[ind].dist == dist) {
            v_inf.* = hashes[ind].v_inf;
            v_sup.* = hashes[ind].v_sup;
            return true;
        }
    }
    return false;
}

fn store(hv: Sigs, alpha: Vals, beta: Vals, g: Vals, dist: Depth, base: Depth, bmove: Move) void {
    const ind = hv & HASH_MASK;
    if ((hashes[ind].base != base) or (hashes[ind].dist <= dist)) {
        if ((hashes[ind].sig != hv) or (hashes[ind].dist != dist)) {
            hashes[ind].dist = dist;
            hashes[ind].v_inf = Vals_min;
            hashes[ind].v_sup = Vals_max;
            hashes[ind].sig = hv;
        }
        hashes[ind].base = base;
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

fn compute_hash(color: Colors) Sigs {
    var h: Sigs = 0;
    for (0..NB_PLATES) |i| {
        h ^= hashesw[i][tab[i][WHITE]];
        h ^= hashesb[i][tab[i][BLACK]];
    }
    for (0..NB_PLATES) |i| {
        h ^= hashesp[i][pos[i]];
    }
    if (color == BLACK) h ^= hash_black;
    return h;
}

// Exact hash, to be used only for 4 plates
fn compute_hash4(color: Colors) Sigs {
    var h: [NB_COLS]Sigs = [NB_COLS]Sigs{ 0, 0, 0 };
    var hp: Sigs = 0;
    for (WHITE..BLACK + 1) |i| {
        h[i] |= @as(Sigs, tab[0][i]);
        h[i] |= @as(Sigs, tab[1][i]) << 1;
        h[i] |= @as(Sigs, tab[2][i]) << 3;
        h[i] |= @as(Sigs, tab[3][i]) << 6;
    }
    var dec: u6 = 0;
    for (0..NB_PLATES) |i| {
        hp |= @as(Sigs, pos[i]) << dec;
        dec += 2;
    }
    if (color == WHITE)
        return h[WHITE] | (h[BLACK] << 9) | (hp << 18)
    else
        return h[WHITE] | (h[BLACK] << 9) | (hp << 18) | (1 << 26);
}

fn play_pos(
    a: Vals,
    b: Vals,
    maxdepth: Depth,
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
    rem_cols[EMPTY] -= 1;
    rem_cols[color] -= 1;
    const v = ab(a, b, oppcol, maxdepth, depth + 1, base);
    rem_cols[color] += 1;
    rem_cols[EMPTY] += 1;
    pos = n_pos;
    tab = n_tab;
    return v;
}

fn play_move(
    a: Vals,
    b: Vals,
    maxdepth: Depth,
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
    const v = ab(a, b, oppcol, maxdepth, depth + 1, base);
    tab = n_tab;
    return v;
}

var best_move: Move = undefined;
fn updateab(color: Colors, depth: Depth, base: Depth, v: Vals, a: *Vals, b: *Vals, g: *Vals, p: u64, lmove: *Move) bool {
    if (color == WHITE) {
        if (v > g.*) {
            g.* = v;
            lmove.* = @as(Move, @intCast(p));
            if (depth == base) best_move = lmove.*;
        }
        a.* = @max(a.*, g.*);
    } else {
        if (v < g.*) {
            g.* = v;
            lmove.* = @as(Move, @intCast(p));
            if (depth == base) best_move = lmove.*;
        }
        b.* = @min(b.*, g.*);
    }
    return (a.* >= b.*);
}

fn eval(depth: Depth) Vals {
    if (rem_cols[EMPTY] == 0) {
        if (tab[pos[NB_PLATES - 1]][WHITE] > tab[pos[NB_PLATES - 1]][BLACK])
            return Win - depth
        else
            return -Win + depth;
    }
    var v: Vals = 0;
    for (0..NB_PLATES) |i| {
        if (tab[i][EMPTY] >= NB_PLATES - 1 - pos[i]) {
            if (tab[i][WHITE] > tab[i][BLACK]) v += @as(Vals, @intCast(i));
            if (tab[i][WHITE] < tab[i][BLACK]) v -= @as(Vals, @intCast(i));
        }
    }
    return v;
}

var hit: u64 = 0;
var nodes: u64 = 0;
fn ab(alp: Vals, bet: Vals, color: Colors, maxdepth: Depth, depth: Depth, base: Depth) Vals {
    if ((depth == maxdepth) or (rem_cols[EMPTY] == 0)) return eval(depth);
    nodes += 1;
    var alpha = alp;
    var beta = bet;
    var bmove: Move = InvalidMove;
    const hv = compute_hash(color);
    var v_inf: Vals = undefined;
    var v_sup: Vals = undefined;
    if (retrieve(hv, &v_inf, &v_sup, &bmove, maxdepth - depth)) {
        if (depth == base) best_move = bmove;
        if (v_inf == v_sup) return v_inf;
        if (v_inf >= beta) return v_inf;
        if (v_sup <= alpha) return v_sup;
        alpha = @max(alpha, v_inf);
        beta = @min(beta, v_sup);
        hit += 1;
    }

    if (!USE_BMOVE) bmove = InvalidMove;

    var a = alpha;
    var b = beta;
    var lmove: Move = InvalidMove;

    const oppcol = if (color == WHITE) BLACK else WHITE;
    var g: Vals = if (color == WHITE) Vals_min else Vals_max;
    const n_tab = tab;
    const n_pos = pos;
    outer: {
        if (bmove != InvalidMove) {
            if (bmove < 8) {
                const v = play_pos(a, b, maxdepth, depth, base, bmove, color, oppcol, n_pos, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, bmove, &lmove)) break :outer;
            } else if (bmove < 16) {
                const v = play_pos(a, b, maxdepth, depth, base, bmove - 8, oppcol, oppcol, n_pos, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, bmove, &lmove)) break :outer;
            } else {
                const k1 = (bmove - 16) % 8;
                const k2 = (bmove - 16) / 8;
                const v = play_move(a, b, maxdepth, depth, base, k1, k2, color, oppcol, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, bmove, &lmove)) break :outer;
            }
        }
        for (0..NB_PLATES) |p| {
            if (p == bmove) continue;
            if ((tab[pos[p]][EMPTY] > 0) and (rem_cols[color] > 0)) {
                const v = play_pos(a, b, maxdepth, depth, base, p, color, oppcol, n_pos, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, p, &lmove)) break :outer;
            }
        }
        for (0..NB_PLATES) |p| {
            if ((p + 8) == bmove) continue;
            if ((tab[pos[p]][EMPTY] > 0) and (rem_cols[oppcol] > 0)) {
                const v = play_pos(a, b, maxdepth, depth, base, p, oppcol, oppcol, n_pos, n_tab);
                if (updateab(color, depth, base, v, &a, &b, &g, p + 8, &lmove)) break :outer;
            }
        }
        for (1..NB_PLATES) |p| {
            if (tab[pos[p]][color] > 0) {
                for (0..p) |k| {
                    if ((16 + p + (k * 8)) == bmove) continue;
                    if (tab[pos[k]][EMPTY] > 0) {
                        const v = play_move(a, b, maxdepth, depth, base, p, k, color, oppcol, n_tab);
                        if (updateab(color, depth, base, v, &a, &b, &g, 16 + p + (k * 8), &lmove)) break :outer;
                    }
                }
            }
        }
    }
    store(hv, alpha, beta, g, maxdepth - depth, base, lmove);
    return g;
}

fn print_pos() !void {
    for (0..NB_PLATES) |i| {
        const p = pos[NB_PLATES - 1 - i];
        try stderr.print("{d}: ", .{NB_PLATES - 1 - i});
        for (0..tab[p][WHITE]) |_| try stderr.print("O ", .{});
        for (0..tab[p][BLACK]) |_| try stderr.print("X ", .{});
        for (0..tab[p][EMPTY]) |_| try stderr.print(". ", .{});
        try stderr.print("\n", .{});
    }
    for (0..NB_COLS) |i| try stderr.print("rems[{d}]:{d} ", .{ i, rem_cols[i] });
    try stderr.print("\n", .{});
    try stderr.print("eval={d}\n", .{eval(0)});
}

fn print_move(m: Move) !void {
    if (m < 8) {
        try stderr.print("I put my marble on:{d}\n", .{m});
    } else if (m < 16) {
        try stderr.print("I put YOUR marble on:{d}\n", .{(m - 8)});
    } else {
        try stderr.print("I move my marble from {d} to {d}\n", .{ (m - 16) % 8, (m - 16) / 8 });
    }
}

fn really_play_move(m: Move, color: Colors) bool {
    if (m < 8) {
        const p1 = m;
        if (p1 >= NB_PLATES) return false;
        const b1 = pos[p1];
        if ((rem_cols[EMPTY] == 0) or (rem_cols[color] == 0) or (tab[b1][EMPTY] == 0)) return false;
        tab[b1][EMPTY] -= 1;
        tab[b1][color] += 1;
        if (p1 != NB_PLATES - 1) {
            const p2 = p1 + 1;
            const b2 = pos[p2];
            pos[p1] = b2;
            pos[p2] = b1;
        }
        rem_cols[EMPTY] -= 1;
        rem_cols[color] -= 1;
    } else if (m < 16) {
        const p1 = m - 8;
        if (p1 >= NB_PLATES) return false;
        const b1 = pos[p1];
        const oppcol = if (color == WHITE) BLACK else WHITE;
        if ((rem_cols[EMPTY] == 0) or (rem_cols[oppcol] == 0) or (tab[b1][EMPTY] == 0)) return false;
        tab[b1][EMPTY] -= 1;
        tab[b1][oppcol] += 1;
        if (p1 != NB_PLATES - 1) {
            const p2 = p1 + 1;
            const b2 = pos[p2];
            pos[p1] = b2;
            pos[p2] = b1;
        }
        rem_cols[EMPTY] -= 1;
        rem_cols[oppcol] -= 1;
    } else {
        const k1 = (m - 16) % 8;
        const k2 = (m - 16) / 8;
        if ((k1 >= NB_PLATES) or (k2 >= NB_PLATES)) return false;
        if ((tab[pos[k1]][color] == 0) or (tab[pos[k2]][EMPTY] == 0) or (k2 >= k1)) return false;
        tab[pos[k1]][color] -= 1;
        tab[pos[k1]][EMPTY] += 1;
        tab[pos[k2]][color] += 1;
        tab[pos[k2]][EMPTY] -= 1;
    }
    return true;
}

pub fn main() !void {
    var args = std.process.args();
    _ = args.next();
    const sturn = args.next().?;
    var turn = std.fmt.parseInt(u8, sturn, 10) catch 0;
    if ((turn != 1) and (turn != 2)) std.posix.exit(255);
    for (0..NB_PLATES) |i| {
        pos[i] = @as(u8, @intCast(i));
        tab[i][EMPTY] = 2 * @as(u8, @intCast(i)) + 1;
        tab[i][WHITE] = 0;
        tab[i][BLACK] = 0;
    }
    rem_cols[EMPTY] = NB_PLATES * NB_PLATES;
    rem_cols[WHITE] = NB_PAWNS_BY_COLOR;
    rem_cols[BLACK] = NB_PAWNS_BY_COLOR;
    try print_pos();

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
    hash_black = rnd.random().int(Sigs);

    var base: Depth = 0;
    var t: i64 = undefined;
    var ret: Vals = undefined;
    var buf: [1000]u8 = undefined;
    var oppmove: Move = undefined;
    var color: Colors = undefined;
    var maxdepth: Depth = undefined;
    color = if (turn == 1) WHITE else BLACK;
    while (true) {
        if (turn == 1) {
            var total_time: i64 = 0;
            maxdepth = base + 1;
            ret = 0;
            while ((total_time < 2000) and (@abs(ret) < Bwin)) {
                best_move = InvalidMove;
                t = std.time.milliTimestamp();
                hit = 0;
                nodes = 0;
                ret = ab(Vals_min, Vals_max, color, maxdepth, base, base);
                if (best_move == InvalidMove) break;
                t = std.time.milliTimestamp() - t;
                total_time += t;
                try stderr.print("depth={d} t={d}ms ret={d} nodes={d} hit={d} best_move={d}\n", .{ maxdepth - base, t, ret, nodes, hit, best_move });
                maxdepth += 1;
            }
            try print_move(best_move);
            if (!(really_play_move(best_move, color))) break;
            try print_pos();
            try stdout.print("{d}\n", .{best_move});
            try stderr.print("\n", .{});
            base += 1;
            color = if (color == WHITE) BLACK else WHITE;
            if (rem_cols[EMPTY] == 0) break;
        }
        turn = 1;
        while (true) {
            try stderr.print("Your move:", .{});
            if (try stdin.readUntilDelimiterOrEof(&buf, '\n')) |m| oppmove = std.fmt.parseInt(Move, m, 10) catch InvalidMove;
            if (really_play_move(oppmove, color)) break;
            try stdout.print("Invalid move:{d}\n", .{oppmove});
        }
        try print_move(oppmove);
        try print_pos();
        base += 1;
        color = if (color == WHITE) BLACK else WHITE;
        if (rem_cols[EMPTY] == 0) break;
    }
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
