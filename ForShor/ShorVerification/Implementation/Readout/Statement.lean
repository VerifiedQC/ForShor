import ForShor.ShorVerification.Framework.Semantics.MSemantics
import ForShor.ShorVerification.Implementation.ModularExponentiation.Statement

/-!
# Readout: the semiclassical readout circuit

Everything needed to state the equivalence proved in `Readout/Main.lean`:
the readout circuit on one recycled control qubit, its instance with the ideal
controlled modular multiplier, the qubit layout it needs, and the integer a
measurement record encodes. It imports nothing from `Readout/`.

## The circuit

`readoutRounds U c m` runs `m` rounds on the control qubit `c`; round `j`
(`j = 0, …, m-1`, in this order) is

  `H c ;; U j ;; ffPhase c j ;; H c ;; measureReset c`

where `U j` is a gate controlled by `c`, and `ffPhase c j` is the feed-forward
phase `Phase c (ffAngle j rec)` whose angle is read from the outcomes of the
rounds `0, …, j-1` (`Framework/AbstractMachine/MGate.lean`). Round `j`'s outcome
is record slot `j`.

`semiclassicalIdeal a N m data c` takes for `U j` the ideal controlled
multiplication by `a ^ (2 ^ (m-1-j)) mod N` on `data`: the multiplier of the
MOST significant exponent bit runs first, and the last round multiplies by `a`.

## Reading the record

`readoutOfRecord rec` reads the record little-endian: slot `i` is bit `i`
(`readoutOfRecord_testBit` in `Main.lean`). This is the integer `o` that
`MeasureClass.probMeas x o` reads from the exponent register `x` in the
coherent readout. The order of the multipliers and the form of `ffAngle`
(sign included) are the ones for which the semiclassical branch at a record and
the coherent state projected on `x = o` are the same explicit vector up to
writing `x := o` (`semiclassical_branch_state`, `coherent_projected_state`); the
distribution-level `semiclassical_eq_iqft` follows, but on its own it would not
detect a flipped phase sign.
-/

namespace Shor

/-- The integer encoded by a measurement record, read little-endian: slot `0`
(the first outcome) is the least significant bit, slot `i` has weight `2^i`,
`true` is bit value `1`. -/
def readoutOfRecord : Record → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * readoutOfRecord rest

/-- `m` rounds of the semiclassical readout on the control qubit `c`. Round `j`
(`j < m`, executed in increasing `j`) is
`H c ;; unitary (U j) ;; ffPhase c j ;; H c ;; measureReset c`; `U j` is
meant to be a gate controlled by `c`. With `m = 0` it is the identity. -/
def readoutRounds (U : ℕ → Gate) (c : ℕ) : ℕ → MGate
  | 0 => .unitary Gate.id
  | j + 1 => .seq (readoutRounds U c j)
      (.seq (.unitary (Gate.H c)) (.seq (.unitary (U j))
        (.seq (.ffPhase c j) (.seq (.unitary (Gate.H c)) (.measureReset c)))))

/-- The semiclassical readout with ideal controlled modular multipliers: `m`
rounds on the control qubit `c`, where round `j` multiplies the register `data`
by `a ^ (2 ^ (m-1-j)) mod N` when `c` is `1` (`Gate.idealCtrlModMul`). Round
`0` carries the most significant exponent bit, round `m-1` the least. -/
def semiclassicalIdeal (a N m : ℕ) (data : Reg) (c : ℕ) : MGate :=
  readoutRounds (fun j => Gate.idealCtrlModMul ((a ^ (2 ^ (m - 1 - j))) % N) N data c) c m

/-- The control qubit `c` of the semiclassical readout lies outside every
register of one modular multiplication: the data register `data`, the work
register `work`, the comparator scratch `scratch` (each including its
reserve) and the comparator flag `flag`. -/
structure SemiclassicalLayout (c : ℕ) (data work scratch : ExtReg) (flag : ℕ) : Prop where
  c_not_mem_data : c ∉ data.ownedQubits
  c_not_mem_work : c ∉ work.ownedQubits
  c_not_mem_scratch : c ∉ scratch.ownedQubits
  c_ne_flag : c ≠ flag

end Shor
