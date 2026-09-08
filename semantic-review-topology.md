# Section 3 Lean 形式化：语义与假设审查

日期：2026-09-08。审查者：`lean_normal_algebra`。

审查对象为当前 `outputs/bounded-uncertainty-lean/BoundedUncertainty` 源码；论文基准为 `work/fundamental-audit-20260907/online-3200c88/main.tex`，特别是 Definition 3.1、局部 ambient-extension 约定、Theorem 3.14、Proposition 3.15 和 Theorem 3.17。

**结论：在下述已核对的数学范围内，未发现假设被加强、定义循环、用错误的梯度代表替代论文梯度，或借助非闭像集的闭性。Theorem 3.14 的拓扑结论和 Theorem 3.17 的等价关系具有忠实的形式化语义。** 这不是 Section 3 全部定理已完成的声明，也不替代最终 Lean 编译与公理依赖审计。

## 独立性与审查范围

本代理独立阅读并审查了其他作者的以下模块：`Basic`、`AmbientDerivative`、`CanonicalDerivative`、`InverseTranspose`、`LinearLift`、`VaryingLinearLift`、`BoundaryMap`、`BoundaryContinuity`、`LinearLiftHomeomorph`、`RayMonotonicity`、`ExponentialEmbedding`、`SelfSurjectivity`、`ContractionNecessity`、`ContractionCharacterization`。

本代理参与编写 `NormalFormula`、`ExponentialMap`、`ZeroRadius`、`ExponentialInjectivity`、`BoundaryInjectivity`、`BoundaryHomeomorph`。这些文件可作为实现内容列出，**不能把本报告对它们的阅读算作独立复核**。主代理已另外明确复核 `BoundaryHomeomorph` 的限制、复合、实际 range 包装与 full-image 分支；其余本人模块的独立验收与全项目公理审计仍由主代理统筹。

## 原假设与形式化假设对应

| 论文条件 | 当前表达与审查结论 |
| --- | --- |
| 有限维 Euclidean 空间，维数至少 2 | 实内积空间中的 `2 ≤ Module.finrank ℝ E`。需要有限维性时由正 finrank 推导实例，没有把有限维紧性当作未声明假设。坐标无关表达包含原 Euclidean 情形。 |
| `X` regular closed | `closure (interior X) = X` 原样表达；闭性从此推导。未要求 `X` 凸、有界、紧或无边界。 |
| `f : X → f(X) ⊆ X` 是论文约定下的微分同胚 | 显式 inverse、inverse maps-to、left inverse、正反向局部扩张、正向可逆微分。右逆与单射由现有字段推出。没有把 `f(X)=X` 放进基础系统。 |
| 半径非负且有统一有限上界 | `radius_nonneg`、`radius_le_bound`、正的 `radius_bound`。没有正下界；零半径保留。 |
| `F(X) ⊆ X` | `closedBall (map x) (radius (map x)) ⊆ domain`，半径取值位置确实是 `f(x)`。 |
| smoothness 仅要求各点附近的 ambient extension | `LocalExtensionAt` 的 open neighbourhood、局部 `ContDiffOn` 与在 `X ∩ neighbourhood` 上的相等。ambient 代表在域外没有被要求光滑。 |
| pointwise contraction | 对每个 `y : domain`，`‖radiusGradient y‖ < 1`。没有用 `sup ‖gradient‖ < 1` 替代。 |
| 主定理的像与逆 | range 包装取实际 `Set.range (boundaryMap hcontraction)`，使用子空间拓扑；不预设像闭。full-image 分支才显式要求 `map '' domain = domain`。 |

`r,s` 当前编码为有限正整数。当前已经闭合的是拓扑结论；没有把 `C^(min(r,s)-1)` 的高阶局部正则性包装进 Homeomorph 并声称已证。

## 独立证据与判定

### R1 — 局部扩张的导数相容性：ACCEPT

`AmbientDerivative.eqOn_fderiv_of_contDiffOn_eqOn` 先在 `interior X ∩ U` 上借局部函数相等得到导数相等，再利用两边导数的连续性推广到 `X ∩ U`。这里确实使用了 `X ⊆ closure (interior X)` 与 `U` 开，足以保证需要的局部稠密性。

`fderiv_eq_of_local_ambient_extensions` 将两个不同 neighbourhood 限制到交集，未要求存在统一全局光滑扩张。`CanonicalDerivative.ambientDerivative_eq_extension` 因而证明了 choice 选出的导数与每一个合法局部扩张的导数一致。canonical derivative 的连续性同样通过每点一个 neighbourhood 推得。

这一步避免了两种错误捷径：直接微分域外任意的 ambient 代表；未经证明就给原集合加入 `UniqueDiffWithinAt`。

### R2 — 实际梯度、微分与 inverse transpose：ACCEPT

`BoundaryMap.radiusGradient` 是 canonical radius derivative 经实内积空间 Riesz 对偶同构的逆得到的向量。`radiusGradient_eq_extension` 把它连接到合法扩张的实际梯度，而非一个独立假定的 vector field。

`derivativeEquiv` 来自原微分同胚假设中的非奇异局部扩张；`derivativeEquiv_eq_ambientDerivative` 连接到已证明扩张无关的导数。`InverseTranspose` 的正向算子是逆算子的 adjoint，逆向是原算子的 adjoint，符合实 Euclidean 情形的 `Df^{-T}` 与 `Df^T`。

### R3 — 线性 lift 及其逆的连续性：ACCEPT

`VaryingLinearLift.continuous_linearEquiv_symm` 从正向算子的 operator-norm 连续性推出逆算子连续性；没有将后者另列为额外假设。归一化分母非零来自算子可逆和输入单位范数。

`LinearLiftHomeomorph.mapImageHomeomorph` 的目标是实际 `f(X)` subtype。其逆连续性来自原逆函数的局部扩张。`linearLiftHomeomorph` 的逆位置是给定的 `f^{-1}`，逆法向是相应转置作用后归一化。`f(X)` 的闭性没有出现在论证中。

### R4 — 非凸域上的射线微分与严格单调：ACCEPT

`RayMonotonicity.hasDerivAt_radius_ray` 只在参数 neighbourhood 的射线确实留在 `X` 时成立。它选择空间中的局部扩张、沿射线求导，再由射线上的局部相等把导数转回真实半径。

`strictMonoOn_radius_ray` 在闭区间上使用真实半径的相对连续性，只在该区间的内点要求导数。导数为

`1 + inner (radiusGradientOnAmbient (z - t • u)) u`。

单位 `u` 与逐点梯度界使此导数严格正。因此无需 `X` 凸，也无需整条无穷射线留在 `X`，更不需要统一收缩常数。

### R5 — closed admissible centre 集与指数 lift 的 embedding：ACCEPT

`ExponentialEmbedding.admissibleCentres` 要求 centre 属于 `X`，且所有 `‖v‖≤1` 的 `y + ε(y) • v` 属于 `X`。固定单位球的表达方便将该条件写成闭集的任意交；连续性只在 closed domain subtype 上使用。

`admissibleCentres_ball_subset` 通过非负半径的 closed-ball affinity 等式连接回真正的 constituent ball。该等式包括半径 0，故此处没有丢失零半径。

在闭的 admissible centre 子集上，若指数 lift 的输出位置属于有界集，则输入 centre 的范数至多增加原有 `radius_bound`；输入 normal 始终为单位向量。于是紧输出集的逆像包含在输入 bundle 的一个紧集里，并且由连续性保持闭，因而紧。properness 加已证明的单射给出 closed embedding。

该论证使用有限维性、原半径上界和 centre 集闭性。最终对 `f(X)` 使用的是对大 admissible 集 embedding 的**子空间限制**，因此 `f(X)` 自身可以非闭。原论文的逆连续性结论得以保留。

### R6 — full-image 情形的存在性与满射：ACCEPT

`SelfSurjectivity` 从 `f(X)=X` 推得每个 domain centre 的 constituent ball 包含在 `X`。若边界 centre 的半径为正，该 centre 会是内点，矛盾；因此半径在 `frontier X` 上为 0。

将半径在域外延拓为 0 只获得**连续**函数，文件没有宣称此延拓光滑。连续函数 `q ↦ radiusZeroExtension (z - q • u)` 将 `[0,R]` 映入自身，一维区间固定点／中间值论证给出 `q = radiusZeroExtension (z-q•u)`。

若所获 centre 不在 `X`，则零延拓迫使 `q=0`，centre 就等于已在 `X` 中的 `z`，矛盾。因此所得根确实位于原域。再用法向逆公式及线性 lift 的满射，得到真实 beta 的满射。

这是原 first-exit 论证的有效替代，不要求域凸、连通、紧或半径处处正；根存在这一步甚至不需要 contraction。

### R7 — contraction 必要性：ACCEPT

`ContractionNecessity` 在维数至少 2 时构造与非零梯度正交的单位向量。若梯度范数至少 1，`n` 与 `-n` 的根式均为非正数。

Lean 的 `Real.sqrt` 是总函数，在非正数处取 0。因此这两个输入的法向输出都为负梯度，位置输出也相同。单位向量不可能等于其相反数，故 raw normal/exponential formula 的单射已迫使梯度范数严格小于 1。该证明覆盖梯度范数等于 1 和大于 1 两种情况，未将根式的合法性或 contraction 偷放进前提。

### R8 — Theorem 3.17 的候选公式与等价关系：ACCEPT

`ContractionCharacterization.boundaryFormula` 只以 system 为参数，不以 contraction 为参数。它使用的 `linearLift` 本身也不要求 contraction。目标先取 ambient `E × E`，所以没有通过构造单位 normal subtype 预先假定需要证明的结论。

`BoundaryFormulaIsBijection` 是从整个输入 bundle 到 `domain ×ˢ {n | ‖n‖ = 1}` 的 `Set.BijOn`，含有：

1. 所有输出位置在 domain，且输出 normal 的范数为 1；
2. 单射；
3. 对完整目标 bundle 满射。

正向由实际 beta 的良定义性、单射与 full-image 满射组成。反向借 `f(X)=X` 时线性 lift 的满射，将候选 beta 的单射传给完整 domain 上的指数公式，再应用 R7。没有从结论中抽取一个 contraction witness 来定义候选公式，因而没有循环。

总化平方根与论文的实根式具有表面差别，但在此双向定理中不产生错误接受：任何梯度范数至少 1 的情形均被 R7 排除；在得到 contraction 后，原根式严格正且输出单位性成立。故该 predicate 的真值与论文“公式良定义并给出 bijection”的条件相符。

## 完成范围与尚未涵盖的结论

- Theorem 3.14 的拓扑内容：实际 beta 对其真实 range 是 homeomorphism，逆连续；`f(X)=X` 时为整个 domain bundle 的 homeomorphism。
- Theorem 3.17：候选公式给出完整 bundle bijection 与逐点 contraction 的等价关系。
- Proposition 3.15 的零半径结论已有实现，但它属于本代理编写部分，本报告不将自身阅读算作其独立审查。
- 当前结果没有宣称已经形式化 contributor–recipient 几何、所有边界对应引理、高阶 `C^(min(r,s)-1)` 局部正则性、或第 4 节主结果。

最终的“无 `sorry`、无新增未证公理”验收应以全项目最新源码编译及展开依赖的公理审计为证。本报告只对上述已阅读源码的数学含义、假设与非循环性作出判定，不将编译成功等同于命题与论文一致。

## 主代理的补充独立复核

主代理另外阅读全文并复核了其他作者的本轮新增模块 ExponentialInjectivity、BoundaryInjectivity、LinearLiftHomeomorph、SelfSurjectivity、BoundaryHomeomorph 和 ContractionNecessity。结论均为 ACCEPT。

- ExponentialInjectivity 的两个根对应同一输出位置和单位方向。比较半径时只使用较大半径中心的球包含性，进而获得整段射线包含于 X；交换两个中心得到半径相等，再恢复中心和输入法向。一般 admissible centre 集的接口没有把单射性列为假设。
- BoundaryInjectivity 将实际 beta 的相等输出传给实际 E，然后使用 L 的真实像包含于 f(X)，最后使用 L 的单射。三个映射的坐标一致。
- LinearLiftHomeomorph 的显式逆先恢复确定性源点，再在同一源点计算转置作用。逆算子的连续性来自已证明的连续算子场结论，源点恢复的连续性来自已有 inverse_extension。
- SelfSurjectivity 仅在 full-image 条件下把球包含性推广到所有域内中心。边界半径为零保证连续拼接；区间固定点所得中心在域外会迫使射线参数为零，与输出在域内矛盾。恢复法向和 L 的逆像之后得到真实 beta 的满射。
- BoundaryHomeomorph 从闭 admissible 中心集的 E 嵌入限制到实际 f(X)，与 L 同胚复合。由输出子类型的连续包含恢复 beta 的嵌入，再对实际 range 打包为 Homeomorph；full-image 情形另用实际满射。没有把连续双射直接当作同胚。
- ContractionNecessity 用维数至少二保证正交方向存在，并通过单位长度排除 n = -n；范数至少一时的位置和法向输出同时发生碰撞。结论施加于 canonical radiusGradient，没有换成其他代表。

本轮主代理编写的 RayMonotonicity、ExponentialEmbedding 和 ContractionCharacterization 由上文另一代理独立复核，不以主代理自查替代。第一批的独立审查保存在 semantic-review-first-batch.md。最终源码哈希与编译、公理审计记录见 verification.json 和 verification.txt。
