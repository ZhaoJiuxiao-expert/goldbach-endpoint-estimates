"""Recompute the 4800 example directly from the divisor-sum definition."""
from itertools import combinations
from math import comb, gcd, isqrt, log, prod


def factor(n):
    factors = []
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors.append(p)
            n //= p
        p += 1
    if n > 1:
        factors.append(n)
    return factors


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def tail(m, t):
    primes = sorted(set(factor(m)))
    # The only divisors with nonzero Möbius weight are squarefree.
    return sum((-1) ** k for k in range(len(primes) + 1)
               for subset in combinations(primes, k) if prod(subset) > t)


def counts(N, z):
    t = N // z
    hits, true_pairs = set(), set()
    for n in range((N + 2) // 3, (2 * N + 2) // 3):
        m = N - n
        if not is_prime(n) or gcd(n, N) > 1 or min(factor(m)) < z:
            continue
        if tail(m, t) == -1:
            hits.add(n)
        if is_prime(m):
            true_pairs.add(n)
    assert true_pairs <= hits
    primes_in_pool = sum(is_prime(p) for p in range(z, N // z**2 + 1))
    assert len(hits - true_pairs) <= comb(primes_in_pool, 3)
    return z, t, len(hits), len(true_pairs), sorted(hits - true_pairs), primes_in_pool


def weighted_endpoints(N, z):
    single, squared, prime_pair_mass = 0.0, 0.0, 0.0
    numerator, denominator = 1, 1
    for n in range((N + 2) // 3, (2 * N + 2) // 3):
        m = N - n
        if gcd(n, N) > 1 or min(factor(m)) < z:
            continue
        bases = set(factor(n))
        if len(bases) != 1:
            continue
        weight = tail(m, N // z)
        base = bases.pop()
        mangoldt = log(base)
        numerator *= base ** max(0, weight)
        denominator *= base ** max(0, -weight)
        single += mangoldt * weight
        squared += mangoldt * weight ** 2
        if is_prime(n) and is_prime(m):
            prime_pair_mass += mangoldt
    below_threshold = numerator * 4 ** isqrt(N - 2) < denominator
    return single, (squared - single) / 2, prime_pair_mass, below_threshold


if __name__ == "__main__":
    result = counts(4800, 8)
    assert result == (8, 600, 89, 88, [2083], 17)
    assert factor(4800 - 2083) == [11, 13, 19]
    print("N=4800, z=8, t=600: detected=89, genuine=88 (ordered).")
    print("The only extra term is 2083 + 11*13*19.")
    assert counts(4800, 24)[2:5] == (88, 88, [])
    single, combined, mass, below_threshold = weighted_endpoints(4800, 24)
    budget = isqrt(4798) * log(4)
    print(f"N=4800, z=24: detected=genuine=88; single={single:.4f}, "
          f"combined={combined:.4f}, prime-pair log sum={mass:.4f}, "
          f"excess={combined-mass:.4f}, power bound={budget:.4f}.")
    assert -1e-9 <= combined - mass <= budget + 1e-9
    assert below_threshold  # Exact integer comparison, independent of floating-point logs.
    powers = [(n, factor(n), 4800 - n) for n in range(1600, 3200)
              if gcd(n, 4800) == 1 and len(factor(n)) > 1
              and len(set(factor(n))) == 1 and is_prime(4800 - n)]
    assert powers == [(1681, [41, 41], 3119), (2209, [47, 47], 2591),
                      (2401, [7, 7, 7, 7], 2399)]
    assert abs(combined - mass - log(13489)) < 1e-9
    square_single, square_combined, square_mass, _ = weighted_endpoints(4800, isqrt(4800) + 1)
    assert abs(square_single + square_combined) < 1e-9
    assert abs(-square_single - square_mass - log(13489)) < 1e-9
    print("At z=70 the negative single endpoint equals the pair log sum plus log(13489).")
