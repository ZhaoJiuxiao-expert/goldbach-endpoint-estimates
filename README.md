# Endpoint estimates for individual even integers in the binary Goldbach problem

**Zixu Zhao (赵子旭), Sichuan University · 2026**

[English manuscript (PDF)](papers/paper-en.pdf) · [中文论文（PDF）](papers/paper-zh.pdf) · [English LaTeX source](papers/paper-en.tex) · [Lean source and verification materials (ZIP)](lean-source.zip)

[Zenodo record](https://zenodo.org/records/24461761) · [DOI: 10.5281/zenodo.24461761](https://doi.org/10.5281/zenodo.24461761)

## Results

For each even integer $N \ge 4096$, the paper compares a corrected endpoint with the logarithmically weighted pairs of distinct primes in the central third of the interval. At the square-root sieve level, the exact correction is a sum over higher prime powers and is at most $\lfloor\sqrt{N-2}\rfloor\log 4$. At a lower cube-root level, the extra composite complements detected by the negative Möbius sign are products of three distinct primes. The remaining open step is to establish strict positivity of the prime-pair mass for every sufficiently large even integer.

对每个偶数 $N\ge4096$，论文给出端点与中央区间真素数对权重之间可逐项计算的素数幂修正。平方根筛下，该修正至多为 $\lfloor\sqrt{N-2}\rfloor\log 4$。一般情形下的严格正性仍待证明。

## Reproducibility

| Directory | Contents |
| --- | --- |
| [Endpoint estimates](lean/01-endpoint/) | Lean 4.13.0 formalization of the endpoint estimates, including the sieve weights, exact prime-power correction, and single-endpoint criterion. The archived verification checks 19 modules and the axiom reports for 81 public statements. |
| [Finite certificates and research notes](lean/02-finite-and-notes/) | Earlier Lean certificates for even integers through one million, conditional criteria, and analytical notes. The notes identify estimates that have not been formalized. |
| [Earlier positive-extension formalization](lean/03-published/) | Two Lean projects from the companion paper on positive-definite extensions and prime-weighted endpoint formulae. [Earlier paper](https://doi.org/10.5281/zenodo.24439399) |

The [source bundle guide](lean/README.md) gives separate commands for each project. The expanded directory reproduces every file in the ZIP. Its [SHA-256 manifest](lean/SHA256SUMS) covers the archived sources and verification records. The Chinese PDF also contains a copy of the source bundle as an embedded attachment.

## Rights

The English and Chinese manuscripts are licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The original Lean code and other original materials in the reproducibility bundle are distributed with other rights reserved. Third-party components retain their respective terms. See [the file-specific rights statement](RIGHTS.txt).

