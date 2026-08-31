import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas

namespace Shor

open Gate

def cmpLtNWWidth (N : ℕ) (data work : Reg) : ℕ :=
  2 + max
    (regSize data + regSize work)
    (Nat.log2 (N + 1) + 1 + regSize work)

structure CmpLtNWWorkspace
    (N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ) where
  data_can_grow : data.CanGrow 1

  mulWorkspace :
    Gate.PhaseProdWorkspace work.active scratch.active

  mul_xReserve_eq :
    mulWorkspace.xReserve = work.reserve

  mul_zReserve_eq :
    mulWorkspace.zReserve = scratch.reserve

  data_work_disjoint :
    ExtReg.OwnedDisjoint data work

  data_scratch_disjoint :
    ExtReg.OwnedDisjoint data scratch

  work_scratch_disjoint :
    ExtReg.OwnedDisjoint work scratch

  flag_not_data :
    flag ∉ data.ownedQubits

  flag_not_work :
    flag ∉ work.ownedQubits

  flag_not_scratch :
    flag ∉ scratch.ownedQubits

  scratch_width :
    regSize scratch.active = cmpLtNWWidth N data.active work.active

def cmpLtNWSignQubit
    (scratch : ExtReg)
    (h : 0 < regSize scratch.active) : ℕ :=
  scratch.active.get
    ⟨regSize scratch.active - 1, by
      have hlt :
          regSize scratch.active - 1 <
            regSize scratch.active := by
        omega
      simpa [regSize] using hlt⟩

noncomputable def fastConstMulInto
    (N : ℕ)
    (work scratch : ExtReg)
    (hworkspace : Gate.PhaseProdWorkspace work.active scratch.active) :
    Gate :=
  let phi : ℝ :=
    (2 * Real.pi * (N : ℝ)) / (ASize hworkspace.zExt.active : ℝ)

  Gate.QFT hworkspace.zExt ;;
  Gate.PhaseProdUsing
    phi
    work.active
    scratch.active
    hworkspace ;;
  †(Gate.QFT hworkspace.zExt)

def cmpLtNWDifference
    (data work scratch : ExtReg)
    (_hdata : data.CanGrow 1) :
    Gate :=
  Gate.zeroExtend data 1 ;;
  Gate.Negate scratch ;;
  Gate.AddScaled
    scratch
    (data.grow 1)
    false
    (regSize work.active) ;;
  Gate.zeroDealloc data 1

noncomputable def cmpLtNW
    (N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace :
      CmpLtNWWorkspace N data work scratch flag) :
    Gate :=
  let mul :=
    fastConstMulInto
      N work scratch hworkspace.mulWorkspace

  let diff :=
    cmpLtNWDifference
      data work scratch hworkspace.data_can_grow

  have hscratch :
      0 < regSize scratch.active := by
    rw [hworkspace.scratch_width]
    unfold cmpLtNWWidth
    omega

  let sign :=
    cmpLtNWSignQubit scratch hscratch

  mul ;;
  diff ;;
  Gate.CNOT sign flag ;;
  †diff ;;
  †mul

theorem eval_cmp_lt_nw_ket
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (N : ℕ)
    (data work scratch : ExtReg)
    (flag : ℕ)
    (hworkspace :
      CmpLtNWWorkspace N data work scratch flag)
    (b : qs.Basis)
    (hdataFresh :
      data.FreshFor 1 b)
    (hworkFresh :
      work.FreshFor 1 b)
    (hscratchZero :
      RegEncoding.toNat scratch.active b = 0)
    (hscratchFresh :
      scratch.FreshFor 1 b) :
    qs.eval
        (cmpLtNW N data work scratch flag hworkspace)
        (qs.ket b)
      =
    qs.ket
      (RegEncoding.writeNat
        (qubitReg flag)
        (if RegEncoding.bit flag b then
          if RegEncoding.toNat data.active b *
                ASize work.active
              <
              N * RegEncoding.toNat work.active b
          then 0
          else 1
        else
          if RegEncoding.toNat data.active b *
                ASize work.active
              <
              N * RegEncoding.toNat work.active b
          then 1
          else 0)
        b) := by
  sorry

end Shor
