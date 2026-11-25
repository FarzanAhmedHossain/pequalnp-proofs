"""Incremental CEGAR (pysat) version of nsearch.py: rows are added to a live solver, learned clauses kept.
Usage: nsearch2.py <gates> <seed> <minutes> <notmode> <solver>"""
import os, random, sys, time, threading
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nsearch as g
from pysat.solvers import Solver


class LiveEnc(g.Enc):
    def __init__(self):
        super().__init__()
        self.sent = 0


def row_clauses(e, s, sel, types, r):
    tand, tor, tnot = types
    N = g.N
    val = {}
    for j in range(s):
        v = e.var(); val[j] = v
        u = [e.var(), e.var()]
        for k in range(2):
            for i in range(N + j):
                x = sel[j][k][i]
                if i < N:
                    e.add(-x, u[k] if (r >> i) & 1 else -u[k])
                else:
                    w = val[i - N]
                    e.add(-x, -w, u[k]); e.add(-x, w, -u[k])
        ta, to, tn = tand[j], tor[j], tnot[j]
        e.add(-ta, -v, u[0]); e.add(-ta, -v, u[1]); e.add(-ta, v, -u[0], -u[1])
        e.add(-to, v, -u[0]); e.add(-to, v, -u[1]); e.add(-to, -v, u[0], u[1])
        e.add(-tn, v, u[0]); e.add(-tn, -v, -u[0])
    e.add(val[s - 1] if g.TARGET[r] else -val[s - 1])


def main():
    s, seed, minutes, notmode, sname = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4], sys.argv[5]
    deadline = time.time() + 60 * minutes
    rnd = random.Random(seed)
    e, sel, types = g.build(s, [], notmode)
    # extra pruning: AND/OR of a wire with the NOT of that wire is useless
    tand, tor, tnot = types
    for j in range(s):
        for k2 in range(j):
            for i in range(g.N + k2):
                # gate k2 = NOT(i); gate j reads i and k2 -> forbidden
                e.add(-tnot[k2], -sel[k2][0][i], -sel[j][0][i], -sel[j][1][g.N + k2])
    base = set()
    for a, b in g.EDGES:
        base.add((1 << a) | (1 << b))
    for a in range(g.N):
        for b in range(a + 1, g.N):
            base.add((1 << a) | (1 << b))
        base.add(1 << a)
    base.add(0); base.add((1 << g.N) - 1)
    base.update(g.mis_rows())
    rows = sorted(base)
    others = [r for r in g.ROWS if r not in base]
    rows += rnd.sample(others, 20)
    for r in rows:
        row_clauses(e, s, sel, types, r)
    sol = Solver(name=sname, bootstrap_with=e.cl)
    e.sent = len(e.cl)
    print('start gates=%d seed=%d notmode=%s solver=%s rows=%d vars=%d' % (s, seed, notmode, sname, len(rows), e.nv), flush=True)
    it = 0
    while time.time() < deadline:
        it += 1
        t = time.time()
        ok = sol.solve()
        print('iter %d rows %d -> %s %.1fs (%.1f min left)' % (it, len(rows), ok, time.time() - t, (deadline - time.time()) / 60), flush=True)
        if not ok:
            print('RESULT UNSAT gates=%d notmode=%s rows=%d' % (s, notmode, len(rows)), flush=True)
            with open(os.path.join(os.environ.get('OUT', '.'), 'unsat_%d_%d_%s.txt' % (s, seed, notmode)), 'w') as fh:
                fh.write(repr(rows) + '\n')
            return
        m = sol.get_model()
        model = {abs(x): x > 0 for x in m}
        gates = g.decode(model, sel, types, s)
        bad = [r for r in g.ROWS if g.run_circuit(gates, r) != g.TARGET[r]]
        if not bad:
            print('RESULT FOUND gates=%d' % s, flush=True)
            print('CIRCUIT', gates, flush=True)
            with open(os.path.join(os.environ.get('OUT', '.'), 'found_%d_%d.txt' % (s, seed)), 'w') as fh:
                fh.write(repr(gates) + '\n')
            return
        rnd.shuffle(bad)
        for r in bad[:4]:
            rows.append(r)
            row_clauses(e, s, sel, types, r)
        for c in e.cl[e.sent:]:
            sol.add_clause(c)
        e.sent = len(e.cl)
    print('RESULT TIMEOUT gates=%d' % s, flush=True)


if __name__ == '__main__':
    main()
