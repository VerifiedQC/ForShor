import Source.Policy

/-!
# Pf4 fixed constructions

Fixed program constructions for the Pf4 policy. Defines the explicit `k = 3` program `phaseProductK3Program` over `phaseProductK3Points`, plus builders for `k ≥ 5` (`initialBuild`, `combineAt`, `appendSingleton`) with register helpers such as `regZero`.
-/

namespace TableGeneration.Policies.Accepted.Pf4aff955f16b.Fixed

open Operations

def phaseProductK3Points : List Point :=
  [.int 0, .int 1, .frac 0, .int (-2), .int (-1)]

def phaseProductK3Program : Prog 3 :=
  let r0 : Fin 3 := ⟨0, by decide⟩
  let r1 : Fin 3 := ⟨1, by decide⟩
  let r2 : Fin 3 := ⟨2, by decide⟩
  [.addScaled r1 r0 false 0,
   .addScaled r1 r2 false 0,
   .phaseProduct r0,
   .phaseProduct r1,
   .phaseProduct r2,
   .addScaled r0 r1 true 0,
   .addScaled r1 r2 false 1,
   .addScaled r1 r0 false 1,
   .addScaled r0 r1 false 0,
   .addScaled r0 r2 false 2,
   .phaseProduct r0,
   .phaseProduct r1,
   .addScaled r1 r2 true 0,
   .addScaled r0 r2 true 2,
   .addScaled r1 r0 true 0,
   .addScaled r0 r1 false 1]

def positive_of_ge_five {k : Nat} (hk : k >= 5) : 0 < k :=
  Nat.lt_of_lt_of_le (by decide) hk

def one_lt_of_ge_five {k : Nat} (hk : k >= 5) : 1 < k :=
  Nat.lt_of_lt_of_le (by decide) hk

def two_lt_of_ge_five {k : Nat} (hk : k >= 5) : 2 < k :=
  Nat.lt_of_lt_of_le (by decide) hk

def regZero (k : Nat) (hk : k >= 5) : Fin k :=
  ⟨0, positive_of_ge_five hk⟩

def regOne (k : Nat) (hk : k >= 5) : Fin k :=
  ⟨1, one_lt_of_ge_five hk⟩

def regTwo (k : Nat) (hk : k >= 5) : Fin k :=
  ⟨2, two_lt_of_ge_five hk⟩

def appendInitialEven
    (k : Nat) (hk : k >= 5) (ops : Prog k) (j : Fin k) : Prog k :=
  if j.val % 2 = 0 ∧ j ≠ regTwo k hk then
    ops ++ [.addScaled (regTwo k hk) j false 0]
  else
    ops

def appendInitialOdd
    (k : Nat) (hk : k >= 5) (ops : Prog k) (j : Fin k) : Prog k :=
  if j.val % 2 = 1 ∧ j ≠ regOne k hk then
    ops ++ [.addScaled (regOne k hk) j false 0]
  else
    ops

def combineAt {k : Nat} (even odd : Fin k) : Prog k :=
  [.addScaled odd even false 0,
   .shiftL even 1,
   .addScaled even odd true 0]

def initialBuild (k : Nat) (hk : k >= 5) : Prog k :=
  let even := regTwo k hk
  let odd := regOne k hk
  (List.finRange k).foldl (appendInitialEven k hk) [] ++
    (List.finRange k).foldl (appendInitialOdd k hk) [] ++
    combineAt even odd

def appendSingleton
    (k : Nat) (hk : k >= 5) (e : Nat) (ops : Prog k) (j : Fin k) : Prog k :=
  if j = regZero k hk then
    ops
  else
    ops ++ [.addScaled (regZero k hk) j false (e * j.val)]

def singletonBlock (k : Nat) (hk : k >= 5) (e : Nat) : Prog k :=
  let build := (List.finRange k).foldl (appendSingleton k hk e) []
  build ++ [.phaseProduct (regZero k hk)] ++ apply_Op_inverse build

def phaseTripleProductK4Points : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1),
   .int 2, .int (-2), .int 4, .int (-4), .int 8, .int (-8)]

def phaseTripleProductK5Points : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1),
   .int 2, .int (-2), .int 4, .int (-4),
   .int 8, .int (-8), .int 16, .int (-16), .int 32]

def phaseTripleProductK6Points : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1),
   .int 2, .int (-2), .int 4, .int (-4),
   .int 8, .int (-8), .int 16, .int (-16),
   .int 32, .int (-32), .int 64, .int (-64)]

def initialPhase (k : Nat) (hk : k >= 5) : Prog k :=
  initialBuild k hk ++
    [.phaseProduct (regZero k hk),
     .phaseProduct (finLast (positive_of_ge_five hk)),
     .phaseProduct (regOne k hk),
     .phaseProduct (regTwo k hk)]

def phaseTripleProductK4InitialBuild : Prog 4 :=
  [.addScaled 1 3 false 0,
   .addScaled 2 0 false 0] ++ combineAt 2 1

def phaseTripleProductK4ScaleStep (e : Nat) : Prog 4 :=
  [.addScaled 1 0 true 0,
   .addScaled 1 2 false 0,
   .shiftL 2 1,
   .addScaled 2 3 true (3 * e + 1),
   .addScaled 2 3 true (3 * e + 2),
   .addScaled 2 1 false 0,
   .shiftL 1 2,
   .addScaled 1 2 true 0,
   .addScaled 2 0 true 1]

def phaseTripleProductK4Return : Prog 4 :=
  [.addScaled 1 2 true 0,
   .addScaled 2 0 true 0,
   .shiftR 1 4,
   .addScaled 2 1 false 3,
   .shiftR 2 6,
   .addScaled 1 3 true 6]

def phaseTripleProductK5ScaleStep (e : Nat) : Prog 5 :=
  [.addScaled 1 0 true 0,
   .addScaled 1 2 false 0,
   .addScaled 1 4 false (4 * e + 2),
   .shiftL 2 1,
   .addScaled 2 3 true (3 * e + 1),
   .addScaled 2 3 true (3 * e + 2),
   .addScaled 2 1 false 0,
   .shiftL 1 2,
   .addScaled 1 2 true 0,
   .addScaled 2 0 true 1,
   .addScaled 2 4 false (4 * e + 3)]

def phaseTripleProductK6ScaleStep (e : Nat) : Prog 6 :=
  [.addScaled 1 0 true 0,
   .addScaled 1 2 false 0,
   .addScaled 1 4 false (4 * e + 2),
   .shiftL 2 1,
   .addScaled 2 3 true (3 * e + 1),
   .addScaled 2 3 true (3 * e + 2),
   .addScaled 2 5 true (5 * e + 5),
   .addScaled 2 5 false (5 * e + 1),
   .addScaled 2 1 false 0,
   .shiftL 1 2,
   .addScaled 1 2 true 0,
   .addScaled 2 0 true 1,
   .addScaled 2 4 false (4 * e + 3)]

def phaseTripleProductK5FinalBuild : Prog 5 :=
  [.shiftL 2 8,
   .addScaled 2 0 false 0,
   .addScaled 2 4 false 16,
   .shiftL 1 4,
   .addScaled 1 3 false 12] ++ combineAt 2 1

def phaseTripleProductK6FinalBuild : Prog 6 :=
  [.shiftL 2 12,
   .addScaled 2 0 false 0,
   .addScaled 2 4 false 24,
   .shiftL 1 6,
   .addScaled 1 3 false 18,
   .addScaled 1 5 false 30] ++ combineAt 2 1

def phaseTripleProductK4Program : Prog 4 :=
  phaseTripleProductK4InitialBuild ++
    [.phaseProduct 0, .phaseProduct 3, .phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK4ScaleStep 0 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK4ScaleStep 1 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK4ScaleStep 2 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK4Return

def phaseTripleProductK5Program : Prog 5 :=
  initialPhase 5 (by decide) ++
    phaseTripleProductK5ScaleStep 0 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK5ScaleStep 1 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK5ScaleStep 2 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK5ScaleStep 3 ++ [.phaseProduct 1, .phaseProduct 2] ++
    apply_Op_inverse phaseTripleProductK5FinalBuild ++
    singletonBlock 5 (by decide) 5

def phaseTripleProductK6Program : Prog 6 :=
  initialPhase 6 (by decide) ++
    phaseTripleProductK6ScaleStep 0 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK6ScaleStep 1 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK6ScaleStep 2 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK6ScaleStep 3 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK6ScaleStep 4 ++ [.phaseProduct 1, .phaseProduct 2] ++
    phaseTripleProductK6ScaleStep 5 ++ [.phaseProduct 1, .phaseProduct 2] ++
    apply_Op_inverse phaseTripleProductK6FinalBuild

end TableGeneration.Policies.Accepted.Pf4aff955f16b.Fixed
