import OMAReductions.R_OeisA182126_conjecture3_R1

/-! The first 61 terms use only the first 63 primes. -/

namespace OMA.A182126

def primeTable : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307]

-- Checking the count below each entry also certifies that no prime was skipped.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma table_cert : ∀ i : Fin 63,
    let q := primeTable[i.val]!
    q.Prime ∧ Nat.count Nat.Prime q = i.val := by
  decide +kernel

lemma nth_eq_table (i : ℕ) (hi : i < 63) : Nat.nth Nat.Prime i = primeTable[i]! := by
  have h := table_cert (⟨i, hi⟩ : Fin 63)
  change (primeTable[i]!).Prime ∧ Nat.count Nat.Prime (primeTable[i]!) = i at h
  have hn := Nat.nth_count h.1
  rwa [h.2] at hn

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma remainder_cert : ∀ i : Fin 62,
    let n := i.val
    let v := (primeTable[n - 1]! * primeTable[n + 1 - 1]!) % primeTable[n + 2 - 1]!
    v.Prime → v ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  decide +kernel

end OMA.A182126

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hpos hbound
  unfold OeisA182126.a
  rw [if_neg (by omega : n ≠ 0)]
  unfold OeisA182126.prime
  rw [OMA.A182126.nth_eq_table (n - 1) (by omega),
    OMA.A182126.nth_eq_table (n + 1 - 1) (by omega),
    OMA.A182126.nth_eq_table (n + 2 - 1) (by omega)]
  exact OMA.A182126.remainder_cert ⟨n, by omega⟩
