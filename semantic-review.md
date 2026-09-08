**Section 3：边界几何与高阶正则性的交叉语义复核**

日期：2026-09-08。论文基线：3200c88826c73210d1e83bfc46de1656ee0788ef。

本报告记录源码的数学含义与假设；编译和公理验收另见 verification.txt/json。旧轮次见 semantic-review-topology.md 与 semantic-review-first-batch.md。

| 独立审查者 | 本轮审查的他人源码 | 判定 |
|---|---|---|
| lean_normal_algebra | BoundaryContributors、LocalBoundary、ContactGeometry | ACCEPT，附局部边界模型桥接范围说明 |
| lean_lift | ContributorFormula、BoundaryInverseRepresentation、HigherBoundaryInverse | ACCEPT，附有限阶与切空间接口范围说明 |
| 主代理 | InflationGeometry、BoundaryNormalAlgebra、SphereBoundary、C1BoundaryGraph、ContributorFormula，以及全部 8 个高阶／隐函数／局部扩张操作代理模块 | ACCEPT |

主代理编写 BoundaryContributors、LocalBoundary、ContactGeometry、BoundaryInverseRepresentation、HigherBoundaryInverse，独立复核由另一代理承担。各代理都没有把本人编写模块的自查算作独立审查。

**贡献中心与膨胀**

InflationGeometry 用 B 与闭单位球的积经 (y,u)↦y+radius(y)u 的连续像证明紧性。只需半径在 B 上相对连续，零半径参数化仍有效。正半径球由内点闭包覆盖，零半径中心则使用 B 的正则闭性和 B 包含于膨胀。

BoundaryContributors 的逐点引理不要求中心集紧或边界光滑。正半径内点贡献者使 q−radius(z−qu) 在零点有局部最小值，而真实局部延拓的导数为 1+inner(gradient,u)>0，矛盾。零半径先由 z=y 排除内点。最终包含关系通过紧性证明贡献者存在，不把存在性隐藏在前提里。

**C1 边界、有符号乘子和实际公式**

C1BoundaryAt 只给集合的局部非正定义函数及归一化实际梯度。LocalBoundary 由一侧射线导数符号证明进入或离开集合，再得正切锥成员和局部极大值的导数不等式。BoundaryNormalAlgebra 将半空间不等式严格转成非负法向倍数。共法向、frontier 成员、法向唯一性都是结论，不是结构字段。

SphereBoundary 计算平方距离的实际梯度，在正半径球面上证明其非零，再得径向外法向。ContactGeometry 用球包含性与共法向识别接收法向；用负平方接触势在 B 上的局部最大值证明乘子符号。接触梯度来自真实局部半径扩张并与规范梯度一致，−2 与除以 2 的缩放正确。

C1BoundaryGraph 允许任意可逆线性坐标的一侧 C1 图表，不预设图函数在零点导数为零。横向导数为 1，故梯度非零，进而构造边界数据。**尚未从单独的 regular closed 与 C1 hypersurface frontier 假设构造一侧图表。** 3.5–3.8 当前验收的是明确的定义函数／一侧图表版本，编译成功不能消除该范围限制。

ContributorFormula 的正半径分支从真实内切球与乘子关系得到 u+gradient 是源外法向的非负倍数。Contraction 排除该向量为零，因此倍数严格正，归一化后用已证 normalUpdate 逆公式。

零半径时 z=y，集合包含性使两端外法向一致。半径在 B 上非负且于 y 取零，负半径的实际扩张在 B 上取局部最大值，故 gradient=(-coefficient)•normal，coefficient≥0。平行梯度的 normalUpdate 恒等式完成法向公式，没有假设边界梯度为零。实际 raw E、typed exponentialLift 和显式 lambda、位置表达式均与原稿 3.8 连接。

**高阶正则性与隐函数逆**

HigherDerivative 逐点微分原 C^r/C^s 局部扩张，通过正则闭域上的规范导数唯一性识别域内导数场，得到 C^(r−1) 梯度与 C^(s−1) 微分。没有要求域外零填充代表本身光滑或 UniqueDiffOn X。

HigherExponential 将平方范数视为内积求导，覆盖零梯度；点态 contraction 保证根号内严格正。HigherLinearLift 在真实可逆微分处使用算子逆的光滑性，单位法向保证归一化分母非零。HigherLinearInverse 在实际 f(X) 上恢复源点，再在同一个源点计算真实微分的转置。

LocalExtensionOperations 的复合先缩小邻域，使内扩张落入外扩张邻域；相等只在合法交集使用。自然数减一在 r,s≥1 时正确覆盖 C0。

ImplicitRadius 对 q−radius(z−qu)=0 使用 mathlib 的高阶 IFT，偏导来自真实 HasFDerivAt，非零性来自 1+inner(gradient,u)>0。结论含基点值、局部方程和联合邻域中的唯一性。

HigherExponentialInverse 仅以已经建立的连续右逆为输入。相对连续性使恢复中心及半径进入扩张与唯一性邻域，真实根因而等于隐函数分支。中心恢复和归一化逆法向给出 C^(r−1) 延拓。未预设高阶逆光滑性，也未要求半径为正或像闭。

**beta 的实际像与正逆正则性**

BoundaryInverseRepresentation 的范围是 typed 候选公式的真实 ambient 输出 Set.range boundaryFormula。逆代表在此范围取真实同胚逆的坐标，域外零值不承担正则性结论。正反复合等式与原 beta 一致。

HigherBoundaryInverse 中，L∘betaInverse 的连续性来自真实 beta 逆的连续性与 L 连续；E 的右逆等式就是已经证明的 beta 复合等式。IFT 给中间逆 C^(r−1)，mapsTo_image 保证中心落在 f(X)，然后才复合 L 的 C^(s−1) 逆。最终仅在真实 range 使用 L逆∘L=id，阶数 min(r,s)−1 正确。全像分支只在显式 f(X)=X 后使用满射性。没有循环假设。

当前完成范围为有限自然数阶下的同胚及双向局部坐标延拓，r=1 或 s=1 时退化为 C0。**未构造流形切空间上的 D beta 线性等价、非奇异 bundle-diffeomorphism 结构或单独 C∞ 接口。** Theorem 3.14 的有限阶陈述及双向正则性已得到；这些额外接口不能同时算作完成。

