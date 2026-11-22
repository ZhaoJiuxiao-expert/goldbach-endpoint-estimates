# 哥德巴赫素数对的端点误差　论文复核材料

三个目录各自保留工程结构。同名模块出现在不同目录时，应在所属目录内编译。以下命令假定 Lean 4.13.0、Lake 与 Python 3.11 或更高版本在命令路径中。带 Mathlib 的工程会按各自锁文件取得依赖，首次运行通常需要联网。各工程内的 verification.json 记录了随包源码的核验状态与摘要，重新验证时可生成不同文件名的本地报告。

## 01-endpoint　本论文的端点误差

19 个模块，81 项公开声明的公理输出。5 个基础模块取自前作。该工程在本次整编时再次运行了构建、公理检查和算例。进入 01-endpoint 后运行：

```
lake exe cache get
lake build
python verify.py --record local-verification.json
python example.py
```

SquareCutoff.lean 给出平方根筛下的精确素数幂修正；ZeroTriple.lean、ExactPollution.lean 和 SignedContrast.lean 分别处理精确立方筛、素数幂及半素数的对照；CubicRate.lean 在较低的立方筛上估计三素因子误计。精确算例取 N = 4800。推导与核验.md 含数学记号及其它文件入口。

## 02-finite-and-notes　有限验证、判据与解析工作笔记

34 个仅依赖 Lean 标准库的模块，含普通偶数 4 至 1,000,000 的表示证书和 6,256 至 1,000,000 的加强条件。数据块 Blocks 已随包提供。进入 02-finite-and-notes 后运行：

```
python verify.py --jobs 2 --output local-verification.json
python endpoint_constant.py
```

如需重新生成证书，在该目录副本中运行 `python generate_witnesses.py`，再运行 `verify.py`。生成操作会重写副本中的 Blocks/*.lean 和 FiniteRange.lean。`endpoint_constant.py` 使用有理数算术包围笔记中的端段常数。

谱假设研究记录.md、单边筛法推导.md、中段小弧与截点.md 保存了数学推导及其引用。谱假设工作笔记仅收录数学正文，止于关于半素数权矩的分析。笔记中的谱极限、零点相关、筛法渐近、长截点中段与小弧估计有其各自的假设与论证状态。形式化证书覆盖文件中逐条陈述的有限代数、判据和区间命题。常数计算本身、主弧模型和平均界都不能替代逐个充分大偶数所需的端点符号估计。

## 03-published　前作的两个形式化工程

该目录展开前作 Zenodo 记录中的 lean-source.zip。共 14 个模块，4 个属于根目录的有限证书工程，10 个属于 MathlibLibrary。原 README.md 给出具体定理与文件的对应关系；survey 是当时对上游仓库的索引材料。在 03-published 内依次运行：

```
python verify.py --out local-verification.json
cd MathlibLibrary
lake exe cache get
lake build
python verify_mathlib.py --out local-verification.json
```

前作作者与权利说明原文收录在 03-published/RIGHTS.txt，适用范围以该文件为准。原记录 https://zenodo.org/records/24439399 。本包沿用上游材料已有的权利说明，Mathlib 等外部依赖依其原有许可提供。

## 完整性

SHA256SUMS 列有本包所有其它文件的 SHA-256。它包含本包使用的路径与文件名，不依赖生成时的设备。源码摘要、公理输出、数值验证和解析笔记分别记载不同种类的证据；任何一项都不能单独证明对所有充分大偶数的素数对存在性。
