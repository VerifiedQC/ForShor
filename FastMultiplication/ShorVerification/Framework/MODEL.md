# ForShor Framework —— 量子模型、指令集与语义

当前框架现状的参考文档,内容取自 `FastMultiplication/ShorVerification/Framework/`。下文路径均相对该目录。
**框架里没有任何 Lean `axiom` 声明**;可信基 = 这些 typeclass 的字段,加上内核 `#print axioms`(propext 等)。
技术标识符保留英文。

---

## 1. 量子模型 —— `Framework/Quantum/`

模型是一个抽象 Hilbert 空间,带一组计算基和 Born 规则测量。它从不固定某个具体 Hilbert 空间,而是用
typeclass 把它「假设」进来。

### 1.1 状态空间 —— `class QSemantics` (`Quantum/QSemantics.lean:31`)

- `Basis : Type`、`State : Type`。
- `State` 是复内积空间:`[NormedAddCommGroup State]`、`[InnerProductSpace ℂ State]`。
- `ket : Basis → State` —— 计算基态。
- **正交归一性**(最承重的假设):`ket_inner_eq_of_eq`(⟨ket b, ket b⟩ = 1)与
  `ket_inner_eq_zero_of_ne`(b₁ ≠ b₂ 时 ⟨ket b₁, ket b₂⟩ = 0)。
- **张成 / 归纳**:`state_induction` —— 任意态都能从 0 出发经 `+`、`•`、`ket b` 到达(证明中把任意态的性质
  归约到基 ket)。
- 派生(非假设):`ket_ne_zero`、`ket_inj`、`ket_norm_one`(`QSemantics.lean:69–158`)。

### 1.2 寄存器编码 —— `class RegEncoding (Basis)` (`Quantum/Registers.lean:180`)

- `toNat : Reg → Basis → ℕ` 及配套(`writeNat`、`bit` …)—— 物理寄存器如何从一个基元读出/写入一个自然数值。
- `Reg` = 有序的物理 qubit 列表;`ExtReg` = 寄存器 + 可增长的「reserve」位(`newBits`、`CanGrow`、
  `capacity`),用于临时进位/高位。

### 1.3 测量 —— `class MeasureClass qs` (`Quantum/Measurement.lean:21`)

- `measProj : Reg → ℕ → State →L[ℂ] State` —— 测量寄存器 `r`、结果为 `o` 的投影算子。
- 假设:`measProj_ket`(作用在基 ket 上:`toNat r b = o` 则保留、否则为 0)、`measProj_zero_outOfRange`、
  `measProj_selfAdjoint`、`measProj_orthogonal`、`measProj_complete`(所有结果求和 = 恒等,即单位分解)。
- `probMeas r o ψ = ‖measProj r o ψ‖²`(**Born 规则**,`Measurement.lean:56`)。

> **量子可信基小结:** 正交归一计算基 + 线性结构(QSemantics)、自然数值的寄存器编码(RegEncoding)、
> 一族完备的自伴结果投影算子 + Born 规则(MeasureClass)。关于「物理」的假设仅此而已。

---

## 2. 指令集 —— `Framework/AbstractMachine/`

两套 gate 语言:高层 `Gate` 是证明用的 IR;低层 `LowGate` 是 submission 真正搭建、并被求值/测量的目标语言。

### 2.1 高层 `inductive Gate` (`Gates.lean:27`,18 个构造子)

- 结构:`id`、`seq`(`;;`)、`adj`(`†`)。
- 原语幺正:`H q`、`X q`、`QFT (r : ExtReg)`、`RadixReverse r m`。
- 相位乘积:`SignedPhaseProd φ x z`、`CSignedPhaseProd ctrl φ x z`。
- 寄存器算术:`ShiftL r n`、`ShiftR r n`、`Negate r`、`AddScaled dst src negSrc shift`。
- 宽度管理:`zeroExtend`、`signExtend`、`zeroDealloc`、`signDealloc`。
- 逃生口:`Prim (tag : String) (args : List ℕ)` —— 命名原语,用于那些被计入 cost、但在这里不再进一步分解的
  模算术构件。

### 2.2 低层 `inductive LowGate` (`LowGate.lean:22`,20 个构造子)

镜像 `Gate`,但作为 **lowering 目标**:

- `QFT` 消失 —— submission 用 `H`、`RadixReverse`、phase gate 把它表达出来。
- phase product 变成显式电路 fallback:`Naive_SignedPhaseProd` / `Naive_CSignedPhaseProd`。
- 相同的算术(`ShiftL/ShiftR/Negate/AddScaled` on `ExtReg`)、宽度管理、`RadixReverse`、`Prim` 逃生口;
  记号 `;;`(seq)、`†`(adj)同 `Gate`。

> QFT 相位表助手 —— `radixReverseIndex`、`qftPhase`、`ω_N`,在 `Gates.lean:47,170–181`;它们是指令含义的数学
> 支撑,本身不是指令。

---

## 3. 语义 —— `Framework/Semantics/`

指令集在量子状态空间上的含义。结构为:一个带幺正/线性定律的核心求值器,然后每个 gate 家族一个 class,
钉住它在基 ket 上的作用。

### 3.1 核心 —— `class GateSemanticsCore qs` (`GateSemantics.lean:39`)

- `eval : Gate → State → State`。
- 让每个 gate 成为 **幺正线性算子** 的定律:`eval_id`、`eval_seq`(eval (U;;V) = eval V ∘ eval U)、
  `inner_preserved`(⟨Uψ,Uφ⟩=⟨ψ,φ⟩,即等距)、`eval_add`/`eval_smul`(ℂ-线性)、
  `eval_adj_apply`(伴随求逆:eval (†U) (eval U ψ) = ψ)。

### 3.2 每个 gate 的作用 class(各自钉住 `eval g (ket b)`)

- `QFTSemantics`(`:70`):QFT = `(1/√2^w) Σ_y qftPhase(2^w, toNat r b, y) • ket(writeNat r.active y b)`。
- `HadamardSemantics`(`:84`):`H q` 对目标 qubit 做 ± 叠加。
- `PauliXSemantics`(`:101`):`X q` 翻转第 q 位。
- `RadixReverseSemantics`(`:132`):按 radix reversal 置换基索引(`radixReverseBasis`)。
- `PhaseSemantics`(`:143`):`SignedPhaseProd φ x z (ket b) = exp(φ·i·(x·z)) • ket b`;`CSignedPhaseProd`
  是受控版本(control 位为 1 时才加相位)。
- `ExtensionSemantics`(`:224`):零/符号扩展与 dealloc 在编码上的作用。
- `ArithmeticSemantics`(`:371`):`ShiftL/ShiftR/Negate/AddScaled` 作为对应的精确整数寄存器算术。
- `GateSemanticsFacts`(`:408`):把上面所有 per-gate class 打包成一个接口。

### 3.3 模乘规范(数论核心)

- `class Spec`(`:422`):声明 **理想** gate:`idealModMul (c N) (x)` 与 `idealCtrlModMul (c N) (x) (ctrl)`
  —— 把寄存器 `x` 乘以 `c` 模 `N`(受控)。
- `IdealCtrlModMulExactSemantics`(`:465`):理想受控模乘所需的精确基-ket 作用。
  `ModMulPrimitiveGateSemantics`(`:491`):真实模乘所用原语 gate 的语义。布局谓词(`ModMulCoreLayout`、
  `QubitOutside`、disjoint-ownership)约束合法调用。

### 3.4 Lowering —— `class LowerGateClass qs` (`Semantics/LowerGate.lean:14`)

- `evalL : LowGate → State → State` —— 低层目标的求值器。**这正是 submission 接口所测量的对象**:
  `Submission.lean` 在 `probability_of_success` 里用 `LowerGateClass.evalL`。
- `LowerGatePrimitiveBridge`(`:141`):把低层原语的 `evalL` 接回高层 `Gate` 语义,从而 lowering 后的电路
  含义 = 高层电路含义。

---

## 4. 如何拼装到 spec(`Framework/Submission.lean`)

submission 提供一个 `LowGate` 电路族。`probability_of_success` = 对测量结果求和:(continued-fraction 后处理
检验指示) × (该结果在电路 `evalL` 作用于全零态下的 Born 概率)。正确性 = 存在精度 `m` 使
`probability_of_success ≥ κ/(log₂N)^4 − ε`;gate count 由 `shorGateCostModel` 在 `LowGate` 电路上计。

即:**量子模型(§1)** 给出态与测量,**指令集(§2)** 是电路的构件,**语义(§3)** 赋予 `evalL`/`eval` 含义,
而 spec 把三者绑到数论成功界上。
