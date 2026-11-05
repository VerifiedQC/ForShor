import Provider.Effective.Enumeration

/-! # Enumeration Size Bounds
Proves exact and upper length bounds for the bounded enumeration: `wordsOfLength_length`, `sourceAlphabet_length`, `wordsUpTo_length` and `searchEntries_length`, with the inequalities `wordsUpTo_length_le` and `searchEntries_length_le`. These bound the size of the finite lists only; no running-time claim is made.
-/

namespace Paper.BoundedThreshold

theorem wordsOfLength_length {α : Type*} (alphabet : List α) (n : Nat) :
    (wordsOfLength alphabet n).length = alphabet.length ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    simp [wordsOfLength, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem sourceAlphabet_length (k a : Nat) :
    (sourceAlphabet k a).length =
      k * (2 * (a+1) + 2 + k * (2 * (a+1))) := by
  simp [sourceAlphabet, List.length_flatMap] <;> ring_nf <;> simp

theorem wordsUpTo_length {α : Type*} (alphabet : List α) (L : Nat) :
    (wordsUpTo alphabet L).length =
      ((List.range (L+1)).map fun n => alphabet.length ^ n).sum := by
  simp [wordsUpTo, List.length_flatMap, wordsOfLength_length]

theorem wordsUpTo_length_le {α : Type*} (alphabet : List α) (L : Nat) :
    (wordsUpTo alphabet L).length ≤
      (L+1) * (alphabet.length+1)^L := by
  rw [wordsUpTo_length]
  have hterm : ∀ n ∈ List.range (L+1),
      alphabet.length^n ≤ (alphabet.length+1)^L := by
    intro n hn
    have hnl : n ≤ L := by simpa using hn
    gcongr <;> omega
  calc
    ((List.range (L+1)).map fun n => alphabet.length^n).sum ≤
      ((List.range (L+1)).map fun _ => (alphabet.length+1)^L).sum := by
        apply List.sum_le_sum
        intro n hn
        exact hterm n hn
    _ = (L+1) * (alphabet.length+1)^L := by simp

theorem searchEntries_length (k a L : Nat) :
    (searchEntries k a L).length =
      (wordsUpTo (sourceAlphabet k a) L).length *
        (Paper.F2CatalogTransfer.f2Points k).permutations.length := by
  simp [searchEntries, List.length_flatMap, Nat.mul_comm]

theorem searchEntries_length_le (k a L : Nat) (hk : 2 ≤ k) :
    (searchEntries k a L).length ≤
      (L+1) *
        (k * (2 * (a+1) + 2 + k * (2 * (a+1))) + 1)^L *
        (2*k)^(2*k) := by
  have hp : (Paper.F2CatalogTransfer.f2Points k).permutations.length ≤
      (2*k)^(2*k) := by
    have hlen : (Paper.F2CatalogTransfer.f2Points k).length =
        2*(k-1)+1 := by
      simp [Paper.F2CatalogTransfer.f2Points]
      omega
    rw [List.length_permutations, hlen]
    calc
      (2*(k-1)+1).factorial ≤
          (2*(k-1)+1)^(2*(k-1)+1) := Nat.factorial_le_pow _
      _ ≤ (2*k)^(2*k) := by gcongr <;> omega
  rw [searchEntries_length]
  have hw := wordsUpTo_length_le (sourceAlphabet k a) L
  rw [sourceAlphabet_length] at hw
  exact Nat.mul_le_mul hw hp

end Paper.BoundedThreshold
