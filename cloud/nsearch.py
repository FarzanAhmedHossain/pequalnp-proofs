"""Exact SAT search (CEGAR over the 1024 inputs) for an AND/OR/NOT circuit of fan-in <= 2 computing the
edge function of Petersen minus edge 0-1 (10 vertices, 14 edges).  Every gate counts (NOT included), as in
PEqualNP.MetaComplexity.HasCircuitSize.  AND/OR gates read two distinct wires (op0 < op1); a NOT gate reads
op0 (op1 is forced equal).  Output = last gate.
Usage: nsearch.py <gates> <seed> <minutes> [notmode]   notmode: 'free' | 'eq<k>' (exactly k NOT gates) | 'ge<k>'
(env CADICAL = cadical binary, OUT = output dir)
"""
import itertools
import os
import random
import subprocess
import sys
import time

N = 10
EDGES = [(0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (3, 8), (4, 9), (5, 7), (5, 8), (6, 8), (6, 9),
         (7, 9)]
ROWS = list(range(1 << N))


def f(r):
    return any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES)


TARGET = {r: f(r) for r in ROWS}


class Enc:
    def __init__(self):
        self.nv, self.cl = 0, []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, *c):
        self.cl.append(c)

    def atmost(self, lits, k):
        # sequential counter
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self.add(-l)
            return
        s = [[self.var() for _ in range(k)] for _ in range(n)]
        for i in range(n):
            self.add(-lits[i], s[i][0])
            if i > 0:
                for j in range(k):
                    self.add(-s[i - 1][j], s[i][j])
                for j in range(1, k):
                    self.add(-lits[i], -s[i - 1][j - 1], s[i][j])
                self.add(-lits[i], -s[i - 1][k - 1])

    def atleast(self, lits, k):
        self.atmost([-l for l in lits], len(lits) - k)


def build(s, rows, notmode):
    e = Enc()
    W = lambda j: N + j  # number of wires available to gate j
    sel = [[[e.var() for i in range(W(j))] for k in range(2)] for j in range(s)]
    tand = [e.var() for j in range(s)]
    tor = [e.var() for j in range(s)]
    tnot = [e.var() for j in range(s)]
    for j in range(s):
        e.add(tand[j], tor[j], tnot[j])
        e.add(-tand[j], -tor[j]); e.add(-tand[j], -tnot[j]); e.add(-tor[j], -tnot[j])
        for k in range(2):
            e.add(*sel[j][k])
            for a, b in itertools.combinations(sel[j][k], 2):
                e.add(-a, -b)
        # binary: op0 < op1 ; NOT: op1 == op0
        for i in range(W(j)):
            for i2 in range(i + 1):
                if i2 == i:
                    e.add(tnot[j], -sel[j][0][i], -sel[j][1][i2])
                else:
                    e.add(-sel[j][0][i], -sel[j][1][i2])
            e.add(-tnot[j], -sel[j][0][i], sel[j][1][i])
        # no NOT of NOT
        for k2 in range(j):
            e.add(-tnot[j], -sel[j][0][N + k2], -tnot[k2])
    # every gate but the last is read
    for j in range(s - 1):
        e.add(*[sel[j2][k][N + j] for j2 in range(j + 1, s) for k in range(2)])
    # the last gate is not a NOT of a NOT etc. fine. Symmetry: adjacent independent gates in lex order of (op1, op0)
    for j in range(s - 2):
        a1, b1 = sel[j][1], sel[j + 1][1]
        for a in range(W(j)):
            for b in range(a):
                e.add(-a1[a], -b1[b])
            for c in range(W(j)):
                for d in range(c):
                    e.add(-a1[a], -b1[a], -sel[j][0][c], -sel[j + 1][0][d])
    if notmode.startswith('eq'):
        k = int(notmode[2:])
        e.atmost(tnot, k)
        e.atleast(tnot, k)
    elif notmode.startswith('ge'):
        e.atleast(tnot, int(notmode[2:]))
    elif notmode.startswith('le'):
        e.atmost(tnot, int(notmode[2:]))
    val = {}
    for r in rows:
        for j in range(s):
            v = e.var()
            val[(j, r)] = v
            u = [e.var(), e.var()]
            for k in range(2):
                for i in range(W(j)):
                    x = sel[j][k][i]
                    if i < N:
                        e.add(-x, u[k] if (r >> i) & 1 else -u[k])
                    else:
                        w = val[(i - N, r)]
                        e.add(-x, -w, u[k])
                        e.add(-x, w, -u[k])
            ta, to, tn = tand[j], tor[j], tnot[j]
            e.add(-ta, -v, u[0]); e.add(-ta, -v, u[1]); e.add(-ta, v, -u[0], -u[1])
            e.add(-to, v, -u[0]); e.add(-to, v, -u[1]); e.add(-to, -v, u[0], u[1])
            e.add(-tn, v, u[0]); e.add(-tn, -v, -u[0])
        e.add(val[(s - 1, r)] if TARGET[r] else -val[(s - 1, r)])
    return e, sel, (tand, tor, tnot)


def decode(model, sel, types, s):
    tand, tor, tnot = types
    gates = []
    for j in range(s):
        ops = [next(i for i, x in enumerate(sel[j][k]) if model.get(x)) for k in range(2)]
        op = 'and' if model.get(tand[j]) else ('or' if model.get(tor[j]) else 'not')
        gates.append((op, ops[0], ops[1]))
    return gates


def run_circuit(gates, r):
    vals = [(r >> i) & 1 for i in range(N)]
    for op, a, b in gates:
        if op == 'and':
            vals.append(vals[a] & vals[b])
        elif op == 'or':
            vals.append(vals[a] | vals[b])
        else:
            vals.append(1 - vals[a])
    return vals[-1] == 1


def solve(e, seed, timeout_s, tag):
    out = os.environ.get('OUT', '.')
    path = os.path.join(out, 'q_%s.cnf' % tag)
    with open(path, 'w') as fh:
        fh.write('p cnf %d %d\n' % (e.nv, len(e.cl)))
        fh.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in e.cl))
    cad = os.environ.get('CADICAL', 'cadical')
    try:
        r = subprocess.run([cad, '-q', '--seed=%d' % seed, path],
                           capture_output=True, text=True, timeout=timeout_s + 60)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', None
    finally:
        try:
            os.remove(path)
        except OSError:
            pass
    if r.returncode == 20:
        return 'UNSAT', None
    if r.returncode != 10:
        return 'TIMEOUT', None
    model = {}
    for line in r.stdout.splitlines():
        if line.startswith('v'):
            for t in line.split()[1:]:
                x = int(t)
                if x:
                    model[abs(x)] = x > 0
    return 'SAT', model


def mis_rows():
    adj = [0] * N
    for a, b in EDGES:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    res = []
    for r in ROWS:
        if TARGET[r]:
            continue
        if all((r >> v) & 1 or (adj[v] & r) for v in range(N)):
            res.append(r)
    return res


def main():
    s, seed, minutes = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    notmode = sys.argv[4] if len(sys.argv) > 4 else 'free'
    deadline = time.time() + 60 * minutes
    rnd = random.Random(seed)
    base = set()
    for a, b in EDGES:
        base.add((1 << a) | (1 << b))
    for a in range(N):
        for b in range(a + 1, N):
            base.add((1 << a) | (1 << b))
        base.add(1 << a)
    base.add(0)
    base.add((1 << N) - 1)
    base.update(mis_rows())
    rows = sorted(base)
    others = [r for r in ROWS if r not in base]
    rows += rnd.sample(others, 30)
    print('start gates=%d seed=%d notmode=%s rows=%d' % (s, seed, notmode, len(rows)), flush=True)
    it = 0
    while time.time() < deadline:
        it += 1
        e, sel, types = build(s, rows, notmode)
        st, model = solve(e, seed, max(60, deadline - time.time()), 's%d_%d' % (s, seed))
        print('iter %d rows %d vars %d clauses %d -> %s (%.1f min left)'
              % (it, len(rows), e.nv, len(e.cl), st, (deadline - time.time()) / 60), flush=True)
        if st == 'UNSAT':
            print('RESULT UNSAT gates=%d notmode=%s rows=%d' % (s, notmode, len(rows)), flush=True)
            with open(os.path.join(os.environ.get('OUT', '.'), 'unsat_%d_%d_%s.txt' % (s, seed, notmode)), 'w') as fh:
                fh.write(repr(rows) + '\n')
            return
        if st != 'SAT':
            print('RESULT TIMEOUT gates=%d' % s, flush=True)
            return
        gates = decode(model, sel, types, s)
        bad = [r for r in ROWS if run_circuit(gates, r) != TARGET[r]]
        if not bad:
            print('RESULT FOUND gates=%d' % s, flush=True)
            print('CIRCUIT', gates, flush=True)
            with open(os.path.join(os.environ.get('OUT', '.'), 'found_%d_%d.txt' % (s, seed)), 'w') as fh:
                fh.write(repr(gates) + '\n')
            return
        rnd.shuffle(bad)
        rows = rows + bad[:12]
    print('RESULT TIMEOUT gates=%d' % s, flush=True)


if __name__ == '__main__':
    main()
