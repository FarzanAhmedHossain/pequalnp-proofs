"""L-meta-3576 counterexample search.

For a bipartite graph G with no 4-cycle (from geng -bf), find the least
  sum_j (n - |I_j|)
over families of independent sets I_j with |I_j| <= n-2 such that every non-adjacent pair lies in
some I_j, every vertex lies in some I_j and outside some I_j (k >= 2 then holds by itself). The
step claims this least value is >= |E| + tau + 1, with tau the least vertex cover (= n - alpha).
An integer program per graph (HiGHS through scipy), with the LP bound tried first.
Reads graph6 lines on stdin; prints one line per n and every violation or tight case.
"""
import sys, itertools
import numpy as np
from scipy.optimize import milp, linprog, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

def g6(line):
    s = line.strip()
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - i)) & 1 for i in range(6))
    adj = [0] * n
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i] |= 1 << j; adj[j] |= 1 << i
            k += 1
    return n, adj

def solve(n, adj):
    E = sum(bin(a).count('1') for a in adj) // 2
    indep = []
    alpha = 0
    for m in range(1, 1 << n):
        ok = True
        x = m
        while x:
            v = (x & -x).bit_length() - 1
            if adj[v] & m: ok = False; break
            x &= x - 1
        if ok:
            c = bin(m).count('1')
            alpha = max(alpha, c)
            if c <= n - 2: indep.append(m)
    tau = n - alpha
    target = E + tau + 1
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n) if not (adj[a] >> b) & 1]
    rows = [('p', a, b) for a, b in pairs] + [('in', v) for v in range(n)] + [('out', v) for v in range(n)]
    A = lil_matrix((len(rows), len(indep)))
    for c, m in enumerate(indep):
        for r, row in enumerate(rows):
            if row[0] == 'p': hit = (m >> row[1]) & 1 and (m >> row[2]) & 1
            elif row[0] == 'in': hit = (m >> row[1]) & 1
            else: hit = not (m >> row[1]) & 1
            if hit: A[r, c] = 1
    A = A.tocsr()
    if any(A[r].nnz == 0 for r in range(len(rows))):
        return None, target, E, tau  # hypotheses cannot hold
    cost = np.array([n - bin(m).count('1') for m in indep], dtype=float)
    lp = linprog(cost, A_ub=-A, b_ub=-np.ones(len(rows)), bounds=(0, 1), method='highs')
    if lp.status == 0 and lp.fun >= target - 1e-7:
        return ('lp', lp.fun), target, E, tau
    res = milp(cost, constraints=LinearConstraint(A, lb=np.ones(len(rows)), ub=np.inf),
               integrality=np.ones(len(indep)), bounds=Bounds(0, 1))
    fam = [indep[c] for c in range(len(indep)) if res.x[c] > 0.5]
    return ('ip', round(res.fun), fam), target, E, tau

def main():
    stats = {}
    for line in sys.stdin:
        if not line.strip(): continue
        n, adj = g6(line)
        r, target, E, tau = solve(n, adj)
        st = stats.setdefault(n, {'graphs': 0, 'vacuous': 0, 'ip': 0, 'tight': 0, 'bad': 0, 'minslack': None})
        st['graphs'] += 1
        if r is None: st['vacuous'] += 1; continue
        val = r[1]
        slack = val - target
        if r[0] == 'ip': st['ip'] += 1
        st['minslack'] = slack if st['minslack'] is None else min(st['minslack'], slack)
        if slack < -1e-7:
            st['bad'] += 1
            print('COUNTEREXAMPLE', line.strip(), 'n', n, 'E', E, 'tau', tau, 'best', val, 'target', target,
                  'family', [sorted(v for v in range(n) if (m >> v) & 1) for m in r[2]], flush=True)
        elif r[0] == 'ip' and abs(slack) < 1e-7:
            st['tight'] += 1
            if st['tight'] <= 20:
                print('TIGHT', line.strip(), 'n', n, 'E', E, 'tau', tau, 'family',
                      [sorted(v for v in range(n) if (m >> v) & 1) for m in r[2]], flush=True)
    for n in sorted(stats):
        print('SUMMARY n=%d' % n, stats[n], flush=True)

main()
