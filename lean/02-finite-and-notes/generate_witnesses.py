"""Build witness tables for the finite Lean proof. Lean checks every supplied digit."""
from bisect import bisect_left
from math import isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LIMIT = 1_000_000
FILTER_START = 6256
BLOCK_LENGTH = 128
MODULE_LENGTH = 32768


def prime_table():
    table = bytearray([1]) * (LIMIT + 1)
    table[:2] = bytes(2)
    for p in range(2, isqrt(LIMIT) + 1):
        if table[p]:
            table[p * p::p] = bytes((LIMIT - p*p) // p + 1)
    return table


def allowed(p):
    return p % 8 in (3, 5, 7) and p % 9 in (2, 4, 5, 7)


def write_module(name, start, digits, strict):
    """The final theorem covers every index in this module, via binary concatenation."""
    tag = str(strict).lower()
    lines = [
        "import Certificates", "", "namespace Goldbach.Finite",
        "open Goldbach.Certificate", "", "set_option maxRecDepth 16000",
        "set_option maxHeartbeats 5000000", "",
    ]
    nodes = []
    for i in range(0, len(digits), BLOCK_LENGTH):
        group = digits[i:i + BLOCK_LENGTH]
        if any(d < 0 or d >= 65536 for d in group):
            raise ValueError("Witness offset does not fit the 16-bit encoding")
        value = int.from_bytes(b"".join(d.to_bytes(2, "little") for d in group), "little")
        symbol = f"b{i // BLOCK_LENGTH}"
        n = start + 2*i
        lines.extend([
            f"private theorem {symbol} : Block {tag} {n} {len(group)} :=",
            f"  @checkDigits_sound {tag} {len(group)} {n} {hex(value)} (by rfl)", "",
        ])
        nodes.append((n, len(group), symbol))
    depth = 0
    while len(nodes) > 1:
        pairs = []
        for i in range(0, len(nodes), 2):
            a, k, left = nodes[i]
            if i + 1 == len(nodes):
                pairs.append(nodes[i])
                continue
            b, l, right = nodes[i + 1]
            if a + 2*k != b:
                raise ValueError("Intervals do not join")
            symbol = f"join{depth}_{i}"
            lines.append(f"private theorem {symbol} : Block {tag} {a} {k+l} :=")
            lines.append(f"  @append {tag} {a} {k} {l} {left} {right}")
            lines.append("")
            pairs.append((a, k+l, symbol))
        nodes = pairs
        depth += 1
    lines += [f"theorem {name} : Block {tag} {start} {len(digits)} := {nodes[0][2]}",
              "", "end Goldbach.Finite", ""]
    (ROOT / "Blocks" / f"{name}.lean").write_text("\n".join(lines), encoding="utf-8")


def main():
    (ROOT / "Blocks").mkdir(exist_ok=True)
    prime = prime_table()
    all_primes = [p for p in range(2, LIMIT + 1) if prime[p]]
    permitted = [p for p in all_primes if allowed(p)]
    masks = bytearray(ok and allowed(p) for p, ok in enumerate(prime))
    ordinary = [next(p for p in all_primes if p <= n // 2 and prime[n-p])
                for n in range(4, FILTER_START, 2)]
    write_module("Low", 4, ordinary, False)
    index = 0
    module_table = []
    for start in range(FILTER_START, LIMIT+1, 2*MODULE_LENGTH):
        last = min(LIMIT, start + 2*(MODULE_LENGTH-1))
        digits = []
        for n in range(start, last+1, 2):
            lo = (n+2)//3
            i = bisect_left(permitted, lo)
            while i < len(permitted) and 2*permitted[i] <= n:
                p = permitted[i]
                if masks[n-p]:
                    digits.append(p-lo)
                    break
                i += 1
            else:
                raise ValueError(f"Missing balanced filtered witness at {n}")
        name = f"Segment{index:02d}"
        write_module(name, start, digits, True)
        module_table.append((name, start, len(digits)))
        index += 1

    lines = [f"import Blocks.{name}" for name, _, _ in module_table]
    lines += ["import Blocks.Low", "", "namespace Goldbach.Finite",
              "open Goldbach.Certificate", ""]
    name, start, count = module_table[-1]
    tail = name
    for left, a, k in reversed(module_table[:-1]):
        symbol = f"from{a}"
        lines.extend([f"private theorem {symbol} : Block true {a} {k+count} :=",
                      f"  @append true {a} {k} {count} {left} {tail}", ""])
        count += k
        tail = symbol
    lines += [
        f"theorem balanced_6256_to_million (n : Nat) (lo : {FILTER_START} ≤ n)",
        f"    (hi : n ≤ {LIMIT}) (even : n % 2 = 0) : BalancedFiltered n := by",
        f"  let i := (n-{FILTER_START})/2",
        f"  have heq : n = {FILTER_START}+2*i := by dsimp [i]; omega",
        f"  exact heq ▸ ({tail} i (by dsimp [i]; omega))", "",
        f"theorem goldbach_to_million (n : Nat) (lo : 4 ≤ n) (hi : n ≤ {LIMIT})",
        "    (even : n % 2 = 0) : HasPair n := by",
        f"  by_cases h : {FILTER_START} ≤ n",
        "  · exact (balanced_6256_to_million n h hi even).hasPair",
        "  · let i := (n-4)/2",
        "    have heq : n = 4+2*i := by dsimp [i]; omega",
        "    exact heq ▸ (Low i (by dsimp [i]; omega))",
        "", "end Goldbach.Finite", "",
    ]
    (ROOT / "FiniteRange.lean").write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()

