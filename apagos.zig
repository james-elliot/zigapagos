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
var invpos: [NB_PLATES]u8 = undefined;
var rems: u8 = NB_PLATES * NB_PLATES;

var hashesw: [NB_PLATES][MAX_PAWNS + 1]Sigs = undefined;
var hashesb: [NB_PLATES][MAX_PAWNS + 1]Sigs = undefined;
var hashesp: [NB_PLATES][NB_PLATES]Sigs = undefined;

const HashElem = packed struct {
    sig: Sigs,
    v_inf: Vals,
    v_sup: Vals,
    d: Depth,
};

const ZHASH = HashElem{
    .sig = 0,
    .v_inf = 0,
    .v_sup = 0,
    .d = 0,
};

var hashes: []HashElem = undefined;

fn retrieve(hv: Sigs, v_inf: *Vals, v_sup: *Vals) bool {
    const ind: usize = hv & HASH_MASK;
    if (hashes[ind].sig == hv) {
        v_inf.* = hashes[ind].v_inf;
        v_sup.* = hashes[ind].v_sup;
        return true;
    } else {
        return false;
    }
}

fn store(hv: Sigs, alpha: Vals, beta: Vals, g: Vals, depth: Depth) void {
    const ind = hv & HASH_MASK;
    const d = 255 - depth;
    if (hashes[ind].d <= d) {
        if (hashes[ind].sig != hv) {
            hashes[ind].d = d;
            hashes[ind].v_inf = Vals_min;
            hashes[ind].v_sup = Vals_max;
            hashes[ind].sig = hv;
        }
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
    p: usize,
    color: Colors,
    oppcol: Colors,
    n_pos: [NB_PLATES]u8,
    n_tab: [NB_PLATES][NB_COLS]u8,
    n_invpos: [NB_PLATES]u8,
) Vals {
    tab[pos[p]][EMPTY] -= 1;
    tab[pos[p]][color] += 1;
    if (pos[p] != NB_PLATES - 1) {
        const old_pos = pos[p];
        const new_pos = pos[p] + 1;
        const p2 = invpos[new_pos];
        invpos[old_pos] = p2;
        invpos[new_pos] = @as(u8, @intCast(p));
        pos[p] = new_pos;
        pos[p2] = old_pos;
    }
    rems -= 1;
    const v = ab(a, b, oppcol, depth + 1);
    rems += 1;
    pos = n_pos;
    invpos = n_invpos;
    tab = n_tab;
    return v;
}

var best_move: u64 = undefined;
fn updateab(color: Colors, depth: Depth, v: Vals, a: *Vals, b: *Vals, g: *Vals, p: u64) void {
    if (color == WHITE) {
        if (v > g.*) {
            g.* = v;
            if (depth == 0) {
                best_move = p;
            }
        }
        a.* = @max(a.*, g.*);
    } else {
        if (v < g.*) {
            g.* = v;
            if (depth == 0) {
                best_move = p;
            }
        }
        b.* = @min(b.*, g.*);
    }
}

fn ab(
    alpha: Vals,
    beta: Vals,
    color: Colors,
    depth: Depth,
) Vals {
    if (rems == 0) {
        if (tab[pos[NB_PLATES - 1]][WHITE] > tab[pos[NB_PLATES - 1]][BLACK]) {
            //            return Win - @as(Vals, depth);
            return Win;
        } else {
            //            return -Win + @as(Vals, depth);
            return -Win;
        }
    }

    var a = alpha;
    var b = beta;

    var v_inf: Vals = undefined;
    var v_sup: Vals = undefined;
    const hv = compute_hash();
    if (retrieve(hv, &v_inf, &v_sup)) {
        if (v_inf == v_sup) return v_inf;
        if (v_inf >= b) return v_inf;
        if (v_sup <= a) return v_sup;
        a = @max(a, v_inf);
        b = @min(b, v_sup);
    }

    const oppcol = if (color == WHITE) BLACK else WHITE;
    var g: Vals = if (color == WHITE) Vals_min else Vals_max;
    const n_tab = tab;
    const n_pos = pos;
    const n_invpos = invpos;

    for (0..NB_PLATES) |p| {
        if (a > b) {
            break;
        }
        if (tab[pos[p]][EMPTY] > 0) {
            const v = play_pos(a, b, depth, p, color, oppcol, n_pos, n_tab, n_invpos);
            updateab(color, depth, v, &a, &b, &g, p);
        }
    }
    for (0..NB_PLATES) |p| {
        if (a > b) {
            break;
        }
        if (tab[pos[p]][EMPTY] > 0) {
            const v = play_pos(a, b, depth, p, oppcol, oppcol, n_pos, n_tab, n_invpos);
            updateab(color, depth, v, &a, &b, &g, p << 8);
        }
    }
    for (0..NB_PLATES) |p| {
        if (a > b) {
            break;
        }
        if ((tab[pos[p]][color] > 0) and (pos[p] > 0) and (tab[pos[p] - 1][EMPTY] > 0)) {
            tab[pos[p]][color] -= 1;
            tab[pos[p]][EMPTY] += 1;
            tab[pos[p] - 1][color] += 1;
            tab[pos[p] - 1][EMPTY] -= 1;
            const v = ab(a, b, oppcol, depth + 1);
            tab = n_tab;
            updateab(color, depth, v, &a, &b, &g, p << 16);
        }
    }
    store(hv, alpha, beta, g, depth);
    return g;
}

pub fn main() !void {
    const stdout = std.io.getStdOut().writer();

    for (0..NB_PLATES) |i| {
        pos[i] = @as(u8, @intCast(i));
        invpos[i] = @as(u8, @intCast(i));
        tab[i][EMPTY] = 2 * @as(u8, @intCast(i)) + 1;
        tab[i][WHITE] = 0;
        tab[i][BLACK] = 0;
    }

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
    var t = std.time.milliTimestamp();
    const ret = ab(Vals_min, Vals_max, WHITE, 0);
    t = std.time.milliTimestamp() - t;
    try stdout.print("t={d}ms\n", .{t});
    try stdout.print("ret={d}\n", .{ret});
    try stdout.print("best_move={d}\n", .{best_move});
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
