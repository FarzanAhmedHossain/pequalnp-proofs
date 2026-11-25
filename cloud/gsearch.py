"""Exact search (SAT, CEGAR) for a small monotone circuit for CYCLE_11's graph H on pairs.

L-meta-9501 asks for an AND/OR fan-in-2 circuit of at most 71 gates representing the 33x33 matrix
  A a b = exists i, (a in {i, 11+i} and b in {(i+1)%11, 22+i}) or the same with a, b swapped.
With w_u = x_u OR y_u (33 gates), A a b = [ {a,b} is an edge of H ], where H on 33 vertices has, for each
i (P_i = i, Q_i = 11+i, S_i = 22+i): edges P_i-P_{i+1}, P_i-S_i, Q_i-P_{i+1}, Q_i-S_i. So a circuit g on the
w's with s gates, right on every 2-set (false on non-edges, true on edges), gives one of 33 + s gates.
(Singletons are then false too: g is monotone and every vertex has a non-neighbour.)
Usage: gsearch.py <gates> <seed> <minutes>   (env CADICAL = the cadical binary, OUT = output dir)
"""
import itertools
import os
import random
import subprocess
import sys
import time

N = 33


def P(i): return i % 11
def Q(i): return 11 + i % 11
def S(i): return 22 + i % 11


EDGES = set()
for _i in range(11):
    for _a, _b in ((P(_i), P(_i + 1)), (P(_i), S(_i)), (Q(_i), P(_i + 1)), (Q(_i), S(_i))):
        EDGES.add((min(_a, _b), max(_a, _b)))
ROWS = [(a, b) for a in range(N) for b in range(a + 1, N)]
TARGET = {r: (r in EDGES) for r in ROWS}


class Enc:
    def __init__(self):
        self.nv, self.cl = 0, []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, *c):
        self.cl.append(c)


def build(s, rows):
    e = Enc()
    sel = [[[e.var() for i in range(N + j)] for k in range(2)] for j in range(s)]
    typ = [e.var() for j in range(s)]
    for j in range(s):
        for k in range(2):
            e.add(*sel[j][k])                                   # at least one operand
            for a, b in itertools.combinations(sel[j][k], 2):   # at most one
                e.add(-a, -b)
        for i in range(N + j):                                  # operand 0 index < operand 1 index
            for i2 in range(i + 1):
                e.add(-sel[j][0][i], -sel[j][1][i2])
    for j in range(s - 1):                                      # every gate but the last is read
        e.add(*[sel[j2][k][N + j] for j2 in range(j + 1, s) for k in range(2)])
    val = {}
    for r in rows:
        on = set(r)
        for j in range(s):
            v = e.var()
            val[(j, r)] = v
            u = [e.var(), e.var()]
            for k in range(2):
                for i in range(N + j):
                    x = sel[j][k][i]
                    if i < N:
                        e.add(-x, u[k] if i in on else -u[k])
                    else:
                        w = val[(i - N, r)]
                        e.add(-x, -w, u[k])
                        e.add(-x, w, -u[k])
            t = typ[j]
            e.add(-t, -v, u[0]); e.add(-t, -v, u[1]); e.add(-t, v, -u[0], -u[1])
            e.add(t, v, -u[0]); e.add(t, v, -u[1]); e.add(t, -v, u[0], u[1])
        e.add(val[(s - 1, r)] if TARGET[r] else -val[(s - 1, r)])
    return e, sel, typ


def decode(model, sel, typ, s):
    gates = []
    for j in range(s):
        ops = [next(i for i, x in enumerate(sel[j][k]) if model.get(x)) for k in range(2)]
        gates.append(('and' if model.get(typ[j]) else 'or', ops[0], ops[1]))
    return gates


def run_circuit(gates, r):
    vals = [1 if i in r else 0 for i in range(N)]
    for op, a, b in gates:
        vals.append(vals[a] & vals[b] if op == 'and' else vals[a] | vals[b])
    return vals[-1] == 1


def solve(e, seed, timeout_s, tag):
    out = os.environ.get('OUT', '.')
    path = os.path.join(out, 'q_%s.cnf' % tag)
    with open(path, 'w') as f:
        f.write('p cnf %d %d\n' % (e.nv, len(e.cl)))
        f.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in e.cl))
    cad = os.environ.get('CADICAL', 'cadical')
    try:
        r = subprocess.run([cad, '-q', '--seed=%d' % seed, '-t', str(int(timeout_s)), path],
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


def main():
    s, seed, minutes = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    deadline = time.time() + 60 * minutes
    rnd = random.Random(seed)
    nonedges = [r for r in ROWS if not TARGET[r]]
    rows = sorted(EDGES) + rnd.sample(nonedges, 60)
    it = 0
    while time.time() < deadline:
        it += 1
        e, sel, typ = build(s, rows)
        st, model = solve(e, seed, max(60, deadline - time.time()), 's%d_%d' % (s, seed))
        print('iter %d rows %d vars %d clauses %d -> %s (%.0f min left)'
              % (it, len(rows), e.nv, len(e.cl), st, (deadline - time.time()) / 60), flush=True)
        if st == 'UNSAT':
            print('RESULT UNSAT gates=%d (no circuit of %d gates even on these rows)' % (s, s), flush=True)
            return
        if st != 'SAT':
            print('RESULT TIMEOUT gates=%d' % s, flush=True)
            return
        gates = decode(model, sel, typ, s)
        bad = [r for r in ROWS if run_circuit(gates, r) != TARGET[r]]
        if not bad:
            print('RESULT FOUND gates=%d total=%d' % (s, s + 33), flush=True)
            print('CIRCUIT', gates, flush=True)
            with open(os.path.join(os.environ.get('OUT', '.'), 'found_%d_%d.txt' % (s, seed)), 'w') as f:
                f.write(repr(gates) + '\n')
            return
        rnd.shuffle(bad)
        rows = rows + bad[:25]
    print('RESULT TIMEOUT gates=%d' % s, flush=True)


if __name__ == '__main__':
    main()
