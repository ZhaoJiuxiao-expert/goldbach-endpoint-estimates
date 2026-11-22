"""Enclose the limiting absolute endpoint constant using rational arithmetic."""

from fractions import Fraction as F
from math import factorial


GRID = 512
SCALE = 10**22


def ceil(x):
    return -(-x.numerator // x.denominator)


def mark_intensities(round_up):
    # The interval mass for grid cell j is log(1 + 1/(2*GRID-j-1)).
    lower = [0] * (GRID + 1)
    upper = [0] * (GRID + 1)
    for j in range(GRID):
        x = F(1, 2 * GRID - j - 1)
        lo = x - x**2 / 2 + x**3 / 3 - x**4 / 4
        hi = lo + x**5 / 5
        lower[j + round_up] = (SCALE * lo).__floor__()
        upper[j + round_up] = ceil(SCALE * hi)
    return lower, upper


def hinge_bound(round_up):
    # For positive marks the compound Poisson recursion has only positive terms.
    lo, hi = mark_intensities(round_up)
    rate = hi if round_up else lo
    p0 = F(1, 2) if round_up else F(GRID, 2 * GRID - 1)
    p = [ceil(SCALE * p0) if round_up else (SCALE * p0).__floor__()]
    for k in range(1, 2 * GRID):
        numerator = sum(j * rate[j] * p[k-j] for j in range(1, min(k, GRID) + 1))
        denom = k * SCALE
        p.append((numerator + denom - 1) // denom if round_up else numerator // denom)
    mean = sum(j * rate[j] for j in range(1, GRID + 1))
    shortfall = sum((2 * GRID - k) * pk for k, pk in enumerate(p))
    return F(mean + shortfall, SCALE * GRID) - 2


def gamma_factor_bounds():
    # H_n - log(n+1) < gamma < H_n - log(n).
    n = 100_000
    harmonic_floor = sum(SCALE // k for k in range(1, n + 1))
    xlo = F(harmonic_floor, 16 * SCALE)
    xhi = F(harmonic_floor + n, 16 * SCALE)
    elo = sum(xlo**k / factorial(k) for k in range(17))
    ehi = sum(xhi**k / factorial(k) for k in range(17))
    ehi += xhi**17 / factorial(17) / (1 - xhi / 18)
    return n / ehi**16, (n + 1) / elo**16


def enclose():
    # log(2) = 2 atanh(1/3).
    log_lo = sum(F(2, (2*k+1) * 3**(2*k+1)) for k in range(16))
    log_hi = log_lo + F(9, 8) * F(2, 33 * 3**33)
    g_lo, g_hi = gamma_factor_bounds()
    lo = g_lo * (3 - 2*log_hi + 2*hinge_bound(0))
    hi = g_hi * (3 - 2*log_lo + 2*hinge_bound(1))
    return lo, hi


if __name__ == "__main__":
    lower, upper = enclose()
    assert F(91105, 100000) < lower <= upper < F(91116, 100000)
    # Print an outward-rounded interval, independently of binary floating point.
    digits = 10**8
    for tag, k in [("lower", (lower*digits).__floor__()), ("upper", ceil(upper*digits))]:
        print(f"{tag}: {k // digits}.{k % digits:08d}")
