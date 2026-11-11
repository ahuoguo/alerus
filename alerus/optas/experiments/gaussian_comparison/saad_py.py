"""The table of Saad et al. POPL'20 (optas, Python) for the discrete Gaussian
N_Z(0, s^2), truncated to [-B, B], as in the artifact: Algorithm 3 (TV
kernel) on Z = 2^k, then the packed encoding. As in the paper, Python only
builds the table; the C sampler (gsenc.c) samples it.

usage: OPTAS=<optimal-approximate-sampling checkout> saad_py.py n d B k out

With EXACT=1, the target is computed in mpmath (well below 2^-200) as exact
Fractions, and get_delta_error is patched to use Fraction(M, Z) instead of
the float M/Z (the only change to optas's Algorithm 3), so that Z = 2^k with
k ~ 100 works. Otherwise it runs as the artifact does, in floats.
Writes out (one line of `key value` pairs, with M) and out.enc.
"""
import os, sys, time
from fractions import Fraction
from math import exp

sys.path.insert(0, os.environ['OPTAS'])
import src.utils as U
import src.opt as O
from src.divergences import KERNELS
from src.construct import construct_sample_ky_encoding

def orderm2(M):                      # optas shells out to GNU bc; pure Python
    k, x = 1, 2 % M
    while x != 1 % M:
        x = (2 * x) % M; k += 1
    return k
U.orderm2 = orderm2

def get_delta_error_exact(Z, p, M, delta, kernel):
    assert delta in [-1, 1]
    if delta == -1 and M == 0:
        return float('inf')
    if delta == 1 and M == Z:
        return float('inf')
    return kernel(p, Fraction(M + delta, Z)) - kernel(p, Fraction(M, Z))

def target(n, d, B, exact):
    if exact:
        from mpmath import mp, mpf, exp as mexp, floor as mfloor
        mp.dps = 120
        s2 = mpf(n) ** 2 / mpf(d) ** 2
        SC = 2 ** 300
        w = [Fraction(int(mfloor(mexp(-mpf(z * z) / (2 * s2)) * SC)), SC) for z in range(-B, B + 1)]
    else:
        s2 = (n / d) ** 2
        w = [exp(-z * z / (2 * s2)) for z in range(-B, B + 1)]
    Sw = sum(w)
    return [x / Sw for x in w]

n, d, B, k = map(int, sys.argv[1:5])
out = sys.argv[5]
EXACT = os.environ.get('EXACT') == '1'
if EXACT:
    O.get_delta_error = get_delta_error_exact

t0 = time.time()
q = O.get_optimal_probabilities(2 ** k, target(n, d, B, EXACT), KERNELS['tv'])
enc, _, _ = construct_sample_ky_encoding(q)
prep = time.time() - t0
Ms = [int(x * 2 ** k) for x in q]

with open(out + '.enc', 'w') as f:
    f.write('%d\n%s\n' % (len(enc), ' '.join(map(str, enc))))
with open(out, 'w') as f:
    f.write('prep_s %f enc_len %d ms %s\n' % (prep, len(enc), ','.join(map(str, Ms))))
