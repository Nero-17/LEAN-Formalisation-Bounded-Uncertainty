# LEAN Formalisation of Bounded Uncertainty

Lean 4 formalisation of Section 3 of *Dynamics with state-dependent uncertainty: a boundary map approach*. The checked project contains 69 mathematical modules and 510 audited named declarations. Lean 4.28.0 and an exact mathlib revision are pinned below.

本工程覆盖固定论文基线 Section 3 的全部演绎性内容：定义和接口、全部引理／命题／定理、解析例子及备注中的反例。Definition 3.9 先给出公式，Proposition 3.10 随后在 contraction 条件下证明良定义；工程形式化了这一组合。额外的 `DefinitionScope` 例子说明去掉相应条件后的全域推广不成立，并未反驳原文上下文中的定义或命题。数值图片不作为已证明的动力学结论。

论文基线为 `3200c88826c73210d1e83bfc46de1656ee0788ef`，Section 3 对应原始 `main.tex` 第 581–1857 行。Lean 为 4.28.0，mathlib 固定为 `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。

| 原文内容 | 形式化结果 | 主要模块 |
|---|---|---|
| Definition 3.1、Notation 3.2 | 系统、真实局部延拓、正则闭域上规范导数／梯度的选择独立性；有限阶、同一邻域 C∞ 及混合阶接口 | Basic、AmbientDerivative、CanonicalDerivative、BoundaryMap、SmoothLocalExtension、MixedRegularity |
| Notation 3.3 | f(A) 紧且正则闭，frontier(f(A))=f(frontier A)；实际贡献对／唯一贡献对；向内、向外法向对与法向束及图表独立性 | DiffeomorphismSetGeometry、Section3Interfaces、NormalBundleNotation |
| Lemma 3.4 | 排除内点贡献者；紧中心集下贡献者存在性和集合包含关系；连接实际 setValuedImage | BoundaryContributors、InflationGeometry |
| Lemmas 3.5–3.7、Theorem 3.8 | 从未定向 C1 边界图和正则闭性导出集合在图的一侧，再构造真实外法向；共法向、内切球、接触梯度、有符号乘子、实际 E 及显式位置公式；包含零半径 | C1FrontierTopology、C1FrontierGraph、C1FrontierContact、LocalBoundary、SphereBoundary、ContactGeometry、ContributorFormula |
| Definition 3.9、Proposition 3.10 | raw E 公式与 contraction 下真正球面值 E 的良定义和连续性；另证明去掉条件后的全域推广不成立 | NormalFormula、ExponentialMap、BoundaryMap、DefinitionScope |
| Definition 3.11、Remark 3.12 | 从真实微分构造逆转置、L、E、β；半径只在 X 上恒定已足以推出规范梯度为零及经典公式 | InverseTranspose、LinearLiftHomeomorph、ConstantRadius |
| Example 3.13 | 原 SIRS 多项式、状态单纯形、实际导数／行列式、单射与真实 C∞ 逆；精确梯度及达到的上确界；半径到边界距离、球不变性；实际系统与其光滑 β | SIRSAlgebra、SIRSGeometry、SIRSGradient、SIRSDeterministic、CompactSmoothInverse、SIRSInvariance、SIRSSystem、SIRSSmooth |
| Theorem 3.14：拓扑 | β 到实际像的同胚；f(X)=X 时成为整个状态束的自同胚 | RayMonotonicity、ExponentialInjectivity、ExponentialEmbedding、SelfSurjectivity、BoundaryHomeomorph |
| Theorem 3.14：正则性 | 实际 β 和实际像上的逆具有 C^(min(r,s)−1) 局部延拓；两阶均∞、任一阶∞、任意有限正阶均覆盖；输出真正落在球面的邻域延拓 | HigherDerivative、HigherExponential、HigherLinearLift、HigherLinearInverse、HigherBoundaryMap、ImplicitRadius、HigherExponentialInverse、HigherBoundaryInverse、SmoothBoundaryForward、SmoothImplicitRadius、SmoothExponentialInverse、SmoothBoundaryInverse、MixedRegularity、BundleSphereExtension、SmoothSphereExtension |
| Theorem 3.14：非奇异微分 | 束切空间 E×n⊥、维数 2d−1；扩张微分在切空间的选择独立性；足够可微阶数下实际连续线性等价 E×n⊥ ≃ E×u⊥ | BundleTangent、BundleDifferential、BoundaryDifferential、SmoothBoundaryInverse、MixedRegularity |
| Proposition 3.15、Remark 3.16 | 内部／全空间零半径点梯度为零并被 E 固定；实际二维 contracting SIRS 系统在零半径边界点改变法向；根式非负已足以保证单位输出 | ZeroRadius、DegenerateNormal、SIRSSystem |
| Theorem 3.17 | f(X)=X 时，无需 contraction 参数定义的候选 β 给出全状态束双射，当且仅当真实半径满足逐点 contraction | ContractionNecessity、ContractionCharacterization |
| Remark 3.18 | 一维单位法向为 ±1、根式等于 1；X=[−1,1]、f=id、ε=(1−x²)/2 满足除维数外全部系统条件，却在不严格 contraction 时仍使实际 β 双射 | OneDimensionalCounterexample、OneDimensionalSystem |
| 非 C1 不变集动机 | 实际二维恒等、零半径系统有边界映射自同胚，同时紧正则闭不变三角形的顶点不存在 C1 边界图 | NonsmoothInvariantSet |

**Definition 3.9 与 Proposition 3.10 的良定义关系**

原文明确采用“先给公式，再验证良定义”的顺序，Proposition 3.10 已在 contraction 条件下完成验证。此前审查将“去掉条件后的全域推广不成立”称为“原定义被反驳、必须修正”，措辞过重，现予更正。以下例子检验条件的作用，并不构成对原文定义及其随后良定义证明的反例。

在全空间取 f=id、ε(x)=2+sin(2x₁)。半径正、有界且光滑，所有闭球都留在全空间，故这是合法的二维 Definition 3.1 系统。在 x=0，规范梯度为 (2,0)；选择 n=(0,1)，实根式的参数为负。Lean 的实数 sqrt 对非正数返回零，因而原始公式输出法向为 (−2,0)，不在单位球面上。`exists_system_raw_exponential_not_unit` 证明这一失败发生在实际系统中。

工程保留无条件的实值 raw formula，并在 contraction 下通过 Proposition 3.10 构造 typed sphere-valued map；`norm_normalUpdate_of_radicand_nonneg` 还证明点态根式非负已足够保证单位输出。Theorem 3.17 用独立于 contraction 的候选公式陈述双射等价，避免循环定义。这里没有悄悄将一个未证假设放入待证定理。

**原假设与忠实性**

X 可以非凸，f(X) 可以非闭，半径可以为零。Contraction 始终是每一点梯度范数严格小于 1，没有改成全域统一界。全空间函数仅代表域内数据；所有微分来自开邻域中的真实局部延拓，其规范值已证明独立于延拓。没有加入 `UniqueDiffOn X` 或把域外辅助代表的光滑性当作假设。

`C1FrontierGraphAt` 采用欧氏 C1 超曲面的局部图定义，既不预设集合位于哪一侧，也不预设法向。正则闭性加边界图性质证明局部单侧性。Tietze 延拓仅用于拓扑直化，局部微分始终使用原 C1 图函数。有限阶中的 r、s 为正自然数；无限阶使用同一个底层系统上的固定 `SmoothLocalExtensionAt` 证据，要求同一函数在同一开邻域上 C∞，不是不相容的有限阶扩张族。混合阶结论直接作用于同一系统。

SIRS 使用 `EuclideanSpace ℝ (Fin 2)` 的欧氏范数。精确行列式为 171/200+(57/200)S−(51/200)I，且至少为 3/5。梯度范数上确界为 κ/(20√2)，在 (1/2,1/2) 达到；28.28<20√2 及 κ=3 均以精确算术证明。单射性采用等价的代数证明，不必沿原文的等值线证明路线。无 C1 不变集的见证采用三角形；这是解析存在性证明，不是对数值图片的认证。

原文中的数值绘图、轨迹和由图片示意的不变边界不具有可供 Lean 检查的精确数值证书。本项目不声称这些图像已形式化，也不声称已完成 Section 4 之后的动力学定理。逐项范围、历史状态及独立审查在 `section3-coverage-review.md` 中记录。

**构建与公理检查**

在当前电脑的工程目录执行：

~~~powershell
.\scripts\Check.ps1 -Audit
~~~

脚本按入口依赖顺序逐个重新编译全部模块，随后编译入口并执行 `AxiomAudit.lean`。可用 `LeanExe` 和 `DependencyRoot` 指定其他工具链与依赖缓存。构建输出仅写入工程 `.lake/build`。其他装有 Lean/Lake 的机器可以运行：

~~~text
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
~~~

`AxiomAudit.lean` 显式审计所有手写具名定义、定理、引理和结构；自动生成的声明随依赖传递检查。仅允许标准 `propext`、`Classical.choice`、`Quot.sound`。本工程不使用 `sorry`、`admit`、新增未证公理、`unsafe` 或 `native_decide`。

本轮完整复编由 16 个串行完成的模块和 53 个按依赖就绪并行编译的模块组成；入口编译通过后，510 条独立公理查询分成三组，逐条由 Lean 检查。过程见 `verification-build-procedure.md`。最终完整重编译与公理审计输出在 `verification.txt`；`verification.json` 记录各模块和支持文件的 SHA-256、实际声明数、模块数、源码行数、工具链及范围说明。归档 ZIP 的每个条目另与源文件逐一比较 SHA-256。此前 38 模块阶段证据保留在 `verification-38-module-batch.*`，更早阶段保留在 `verification-previous-batch.*`；旧阶段文件仅用于历史追溯。最终验收使用本轮全部模块的完整重编译，独立语义审查不会被编译成功代替。


