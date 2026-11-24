"""L-meta-3576: LP relaxation and its dual weights on small graphs (graph6 on stdin).

Primal: min sum_S x_S (n - |S|) over independent S, 1 <= |S| <= n-2, x >= 0, with
  pair rows  (non-adjacent a<b):  sum_{S contains a,b} x_S >= 1
  in rows    (vertex v):          sum_{S contains v}   x_S >= 1
  out rows   (vertex v):          sum_{S misses v}     x_S >= 1
Dual weights y >= 0 on the rows with  y(pairs in S) + y_in(S) + y_out(V-S) <= n - |S|  for all S.
Prints graphs whose LP value is within SLACK of |E| + tau + 1, with a dual solution.
"""
import sys
import numpy as np
from scipy.optimize import linprog

SLACK = float(sys.argv[1]) if len(sys.argv) > 1 else 0.5

def g6(line):
    s = line.strip(); n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63; bits.extend((v >> (5 - i)) & 1 for i in range(6))
    adj = [0] * n; k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: adj[i] |= 1 << j; adj[j] |= 1 << i
            k += 1
    return n, adj

for line in sys.stdin:
    if not line.strip(): continue
    n, adj = g6(line)
    E = [(a, b) for a in range(n) for b in range(a + 1, n) if (adj[a] >> b) & 1]
    indep = []; alpha = 0
    for m in range(1, 1 << n):
        if all(not (adj[v] & m) for v in range(n) if (m >> v) & 1):
            c = bin(m).count('1'); alpha = max(alpha, c)
            if c <= n - 2: indep.append(m)
    tau = n - alpha; target = len(E) + tau + 1
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n) if not (adj[a] >> b) & 1]
    rows = [('p', a, b) for a, b in pairs] + [('in', v) for v in range(n)] + [('out', v) for v in range(n)]
    A = np.zeros((len(rows), len(indep)))
    for c, m in enumerate(indep):
        for r, row in enumerate(rows):
            if row[0] == 'p': A[r, c] = (m >> row[1]) & 1 and (m >> row[2]) & 1
            elif row[0] == 'in': A[r, c] = (m >> row[1]) & 1
            else: A[r, c] = not (m >> row[1]) & 1
    if (A.sum(axis=1) == 0).any(): continue
    cost = np.array([n - bin(m).count('1') for m in indep], float)
    # The dual directly: max sum y, A^T y <= cost, y >= 0; prefer weight on in/out rows (tiny bonus).
    bonus = np.array([0.0 if r[0] == 'p' else 1e-4 for r in rows])
    d = linprog(-(np.ones(len(rows)) + bonus), A_ub=A.T, b_ub=cost, bounds=(0, None), method='highs')
    y = d.x; val = float(np.ones(len(rows)) @ y)
    if val - target > SLACK: continue
    deg = [bin(a).count('1') for a in adj]
    print('GRAPH n=%d E=%d tau=%d target=%d LP=%.4f edges=%s deg=%s' % (n, len(E), tau, target, val, E, deg))
    for r, row in enumerate(rows):
        if y[r] > 1e-6:
            if row[0] == 'p':
                a, b = row[1], row[2]
                common = [z for z in range(n) if (adj[z] >> a) & 1 and (adj[z] >> b) & 1]
                print('   pair %s y=%.4f dist=%s' % ((a, b), y[r], '2 via %d' % common[0] if common else 'far'))
            else:
                print('   %s %d y=%.4f deg=%d' % (row[0], row[1], y[r], deg[row[1]]))
    sys.stdout.flush()
