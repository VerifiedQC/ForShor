import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace

/-!
# Modular-Exponentiation Circuit: `CmpLtNW`

The concrete Step-4 comparator circuit (`cmpLtNW`): a fast constant
multiplication into a clean scratch register (`fastConstMulInto`), the signed
difference against the data register (`cmpLtNWDifference`), and copying its
sign bit to the flag (`cmpLtNWSignQubit`).
-/

namespace Shor

open Gate

def cmpLtNWSignQubit (scratch : ExtReg) (h : 0 < regSize scratch.active) : ℕ :=
  scratch.active.get
    ⟨regSize scratch.active - 1, by
      have hlt : regSize scratch.active - 1 < regSize scratch.active := by omega
      simpa [regSize] using hlt⟩

def fastConstMulInto
    (N : ℕ) (work scratch : ExtReg) (hworkspace : Gate.PhaseProdWorkspace work.active scratch.active) :
    Gate :=
  let phi : Angle := (2 * (N : ℚ)) / (ASize hworkspace.zExt.active : ℚ)
  Gate.QFT hworkspace.zExt ;;
  Gate.PhaseProdUsing phi work.active scratch.active hworkspace ;;
  †(Gate.QFT hworkspace.zExt)

def cmpLtNWDifference (data work scratch : ExtReg) (_hdata : data.CanGrow 1) : Gate :=
  Gate.zeroExtend data 1 ;;
  Gate.Negate scratch ;;
  Gate.AddScaled scratch (data.grow 1) false (regSize work.active) ;;
  Gate.zeroDealloc data 1

def cmpLtNW
    (N : ℕ) (data work scratch : ExtReg) (flag : ℕ)
    (hworkspace : CmpLtNWWorkspace N data work scratch flag) :
    Gate :=
  let mul := fastConstMulInto N work scratch hworkspace.mulWorkspace
  let diff := cmpLtNWDifference data work scratch hworkspace.data_can_grow
  have hscratch : 0 < regSize scratch.active := by
    rw [hworkspace.scratch_width]
    unfold cmpLtNWWidth
    omega
  let sign := cmpLtNWSignQubit scratch hscratch
  mul ;;
  diff ;;
  Gate.CNOT sign flag ;;
  †diff ;;
  †mul

end Shor
