import OMAReductions.R_OeisA182126_conjecture3_R1

-- Step OeisA182126.conjecture3.R1.H2: hypothesis H2 of reduction OeisA182126.conjecture3.R1
-- Credit: @sebastianbachmaier
-- H2 := ∀ n : ℕ, 0 < n → n ≤ 61 → (OeisA182126.a n).Prime →     OeisA182126.a n ∈ ([2, 7, 11, 13, 29] : List ℕ)

namespace OMAStepA182126

def L : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
  71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
  167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
  269, 271, 277, 281, 283, 293, 307]

lemma hcount : ∀ i < 63, (L.getD i 0).Prime ∧ Nat.count Nat.Prime (L.getD i 0) = i := by
  decide +kernel

lemma nth_eq (i : ℕ) (hi : i < 63) : Nat.nth Nat.Prime i = L.getD i 0 := by
  obtain ⟨hp, hc⟩ := hcount i hi
  conv_lhs => rw [← hc]
  exact Nat.nth_count hp

lemma fin_check : ∀ n : ℕ, n < 62 → 0 < n →
    ((L.getD (n - 1) 0 * L.getD n 0) % L.getD (n + 1) 0).Prime →
    (L.getD (n - 1) 0 * L.getD n 0) % L.getD (n + 1) 0 ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  decide +kernel

end OMAStepA182126

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn hle hp
  have ha : OeisA182126.a n =
      (OMAStepA182126.L.getD (n - 1) 0 * OMAStepA182126.L.getD n 0) %
        OMAStepA182126.L.getD (n + 1) 0 := by
    unfold OeisA182126.a OeisA182126.prime
    rw [if_neg (by omega)]
    rw [show n + 1 - 1 = n by omega, show n + 2 - 1 = n + 1 by omega,
      OMAStepA182126.nth_eq (n - 1) (by omega), OMAStepA182126.nth_eq n (by omega),
      OMAStepA182126.nth_eq (n + 1) (by omega)]
  rw [ha] at hp ⊢
  exact OMAStepA182126.fin_check n (by omega) hn hp
