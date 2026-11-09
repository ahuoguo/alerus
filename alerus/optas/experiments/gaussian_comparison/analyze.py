"""Exact output distributions and TV to N_Z(0, s^2), s = n/d, for each sampler,
plus empirical checks of the histograms the samplers wrote. Prints one CSV
row per sampler (no header); `analyze.py --header` prints the header.

usage: analyze.py n d nt mb outprefix   (nt, mb: the Rust pipeline's Taylor terms and weight bits)
"""
import sys, os, math, csv
import numpy as np
from mpmath import mp, mpf, exp as mexp
mp.dps = 60

COLS = ['sigma', 'n', 'd', 'method', 'B', 'k', 'nt', 'mb', 'tv_exact', 'log2_tv', 'tv_emp', 'ks_emp',
        'std_emp', 'N', 'ns_per_sample', 'calls', 'bits', 'matrix_ns']
out = csv.DictWriter(sys.stdout, COLS, lineterminator='\n')
if sys.argv[1] == '--header':
    out.writeheader(); sys.exit()
n, d, nt, mb = (int(a) for a in sys.argv[1:5])
pre = sys.argv[5]
s = mpf(n) / d
s2 = s * s

# ── the target N_Z(0, s^2): support |z| <= R, the rest is < e^-800 ──────────
R = int(40 * s) + 40
def target_np():
    z = np.arange(-R, R + 1, dtype=np.float64)
    lw = -z * z / (2 * float(s2))
    w = np.exp(lw - lw.max())
    return z.astype(np.int64), w / w.sum()
Z, P = target_np()                    # float64 target (for the empirical checks)
def p_exact(zs):                      # mpmath target (for the Saad variants)
    zs = list(zs)
    tot = sum(mexp(-mpf(z * z) / (2 * s2)) for z in range(-R, R + 1))
    return {z: mexp(-mpf(z * z) / (2 * s2)) / tot for z in zs}, tot

def read(path):
    if not os.path.exists(path):
        return None
    with open(path) as f:
        head = f.readline().split()
        meta = {head[i]: head[i + 1] for i in range(0, len(head) - 1, 2)}
        h = {}
        for line in f:
            z, c = line.split()
            h[int(z)] = int(c)
    return meta, h

def emp(h, q):
    """empirical TV to q (aligned with Z), KS distance, and std"""
    N = sum(h.values())
    e = np.zeros_like(P)
    for z, c in h.items():
        if -R <= z <= R:
            e[z + R] += c / N
    ks = float(np.max(np.abs(np.cumsum(e) - np.cumsum(q))))
    sd = math.sqrt(sum(c * z * z for z, c in h.items()) / N - (sum(c * z for z, c in h.items()) / N) ** 2)
    return 0.5 * float(np.abs(e - q).sum()), ks, sd, N

rows = []
def row(method, tv_exact, meta, h, q, **extra):
    r = dict(sigma=float(s), n=n, d=d, method=method, tv_exact=tv_exact,
             log2_tv=math.log2(tv_exact) if tv_exact else '', **extra)
    if meta is not None:
        etv, ks, sd, N = emp(h, q)
        r.update(tv_emp=etv, ks_emp=ks, std_emp=sd, N=N, ns_per_sample=float(meta['ns']),
                 calls=float(meta.get('calls', 'nan')), bits=float(meta.get('bits', 'nan')))
    rows.append(r)

# CKS exact: output = target
r = read(pre + '_cks.txt')
row('cks_exact', 0.0, *(r or (None, None)), P)

# Saad: output = M / 2^k on [-B, B]
for tag, method in [('saad', 'saad_rust'), ('c', 'saad_c')]:
    r = read(pre + ('_saad.txt' if tag == 'saad' else '_py.txt'))
    if r is None:
        continue
    ms = [int(x) for x in r[0]['ms'].split(',')]
    B = (len(ms) - 1) // 2
    tot = sum(ms)
    k = tot.bit_length() - 1
    pe, _ = p_exact(range(-R, R + 1))
    tv = mpf(0)
    for z in range(-R, R + 1):
        qz = mpf(ms[z + B]) / tot if -B <= z <= B else mpf(0)
        tv += abs(qz - pe[z])
    tv = float(tv / 2)
    q = np.zeros_like(P)
    for z in range(-B, B + 1):
        q[z + R] = ms[z + B] / tot
    rr = r if tag != 'c' else read(pre + '_c.txt')
    extra = dict(B=B, k=k)
    if tag == 'saad':
        extra.update(nt=nt, mb=mb, matrix_ns=float(r[0]['ns_matrix']))
    row(method, tv, *(rr or (None, None)), q, **extra)

out.writerows(rows)
