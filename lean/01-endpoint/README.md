# 逐偶数端点误差的 Lean 验证

先读[推导与核验](./推导与核验.md)。[SquareCutoff.lean](./SquareCutoff.lean) 直接估计原论文的单个校正端点。[ZeroTriple.lean](./ZeroTriple.lean) 在较低筛选界上估计两个端点的组合。[SingleEndpoint.lean](./SingleEndpoint.lean) 把原单端点上的负值估计变成该整数的素数对存在性判据。该负值估计是判据的前提。

## 从源码重跑

使用 Lean 的工具链管理器 elan，在解压后的目录运行以下命令。首次运行需能访问 GitHub 和 Mathlib 的编译缓存。项目固定 Lean 4.13.0 及 Mathlib 提交 `d7317655e2826dc1f1de9a0c138db2775c4bb841`。

~~~sh
lake exe cache get
lake build
~~~

若还要检查每个公开审计条目的公理依赖，并重算 4800 的例子，安装 Python 3 后运行：

~~~sh
python verify.py --record local-verification.json
~~~

[verification.json](./verification.json) 保存了随包源码实际通过的检查与文件摘要。算例可单独执行 `python example.py`。例中的小数供阅读，原单端点与门槛的比较另外使用整数运算核验。

## 文件来源

`PaperFourier.lean`、`FourierWindow.lean`、`Orthogonality.lean`、`PrincipalMass.lean`、`PrimeEndpoint.lean` 来自此前论文的形式化工程。本工作沿用其相邻端点、主特征校正和有符号权的定义。原论文及其许可信息见[Zenodo 记录](https://zenodo.org/records/24439399)。
