import OMAStatements.S_oeis_a375853
import Mathlib

namespace OMA.S_oeis_a375853

def EE (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), m.choose (2 * k)
def OO (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), m.choose (2 * k + 1)

lemma EE_succ (m : ℕ) : EE (m + 1) = EE m + OO m := by
  unfold EE OO
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => m.choose (2 * k))]
  have h1 : ∑ k ∈ Finset.range (m + 1), (m + 1).choose (2 * (k + 1))
      = ∑ k ∈ Finset.range (m + 1), (m.choose (2 * k + 1) + m.choose (2 * k + 2)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.choose_succ_succ]
  rw [h1, Finset.sum_add_distrib, Finset.sum_range_succ (fun k => m.choose (2 * k + 2))]
  have : m.choose (2 * m + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [this]
  ring

lemma OO_succ (m : ℕ) : OO (m + 1) = EE m + OO m := by
  unfold EE OO
  rw [Finset.sum_range_succ]
  have h1 : ∑ k ∈ Finset.range (m + 1), (m + 1).choose (2 * k + 1)
      = ∑ k ∈ Finset.range (m + 1), (m.choose (2 * k) + m.choose (2 * k + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ]
  rw [h1, Finset.sum_add_distrib]
  have : (m + 1).choose (2 * (m + 1) + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [this]

lemma EO (m : ℕ) : EE (m + 1) = OO (m + 1) := by rw [EE_succ, OO_succ]

lemma EE_eq (m : ℕ) : EE (m + 1) = 2 ^ m := by
  induction m with
  | zero => simp [EE, Finset.sum_range_succ]
  | succ m ih =>
    have h2 : EE (m + 2) = EE (m + 1) + OO (m + 1) := EE_succ (m + 1)
    rw [h2, ← EO, ih]; ring

lemma OO_eq (m : ℕ) : OO (m + 1) = 2 ^ m := by rw [← EO]; exact EE_eq m

lemma term (n k : ℕ) (hk : k ≤ n) :
    4 * ((k : ℚ) * (n - k)) * ((2 * n + 2).choose (2 * k + 1) : ℚ)
    = (2 * n + 2) * (2 * n + 1) * ((2 * n).choose (2 * k) : ℚ) - (2 * n + 1) * ((2 * n + 2).choose (2 * k + 1) : ℚ) := by
  have h1 : ((2 * n + 1).choose (2 * k) : ℚ) * (2 * n + 1 - 2 * k : ℕ) = ((2 * n + 1).choose (2 * k) * (2 * n + 1 - 2 * k) : ℕ) := by push_cast; ring
  have e1 : (2 * n + 1) * (2 * n).choose (2 * k) = (2 * n + 1).choose (2 * k) * (2 * n + 1 - 2 * k) := by
    have := Nat.choose_mul_succ_eq (2 * n) (2 * k)
    linarith
  have e2 : (2 * n + 1 + 1) * (2 * n + 1).choose (2 * k) = (2 * n + 1 + 1).choose (2 * k + 1) * (2 * k + 1) := Nat.add_one_mul_choose_eq (2 * n + 1) (2 * k)
  have e1q : ((2 * n + 1 : ℕ) : ℚ) * ((2 * n).choose (2 * k) : ℚ) = ((2 * n + 1).choose (2 * k) : ℚ) * ((2 * n + 1 - 2 * k : ℕ) : ℚ) := by exact_mod_cast e1
  have e2q : ((2 * n + 1 + 1 : ℕ) : ℚ) * ((2 * n + 1).choose (2 * k) : ℚ) = ((2 * n + 1 + 1).choose (2 * k + 1) : ℚ) * ((2 * k + 1 : ℕ) : ℚ) := by exact_mod_cast e2
  have hs : ((2 * n + 1 - 2 * k : ℕ) : ℚ) = 2 * n + 1 - 2 * k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hs] at e1q
  push_cast at e1q e2q
  have e3 : (2 * n + 2).choose (2 * k + 1) = (2 * n + 1 + 1).choose (2 * k + 1) := rfl
  rw [e3]
  set A : ℚ := ((2 * n + 1).choose (2 * k) : ℚ)
  set B : ℚ := ((2 * n + 1 + 1).choose (2 * k + 1) : ℚ)
  set C : ℚ := ((2 * n).choose (2 * k) : ℚ)
  have : (2 * n + 2 : ℚ) * (2 * n + 1) * C = (2 * n + 2) * (A * (2 * n + 1 - 2 * k)) := by rw [← e1q]; ring
  rw [this]
  have e2q' : (2 * n + 2 : ℚ) * A = B * (2 * k + 1) := by linarith
  calc 4 * ((k : ℚ) * (n - k)) * B = B * (2 * k + 1) * (2 * n + 1 - 2 * k) - (2 * n + 1) * B := by ring
    _ = _ := by rw [← e2q']; ring

lemma EE_restrict (n : ℕ) : EE (2 * n) = ∑ k ∈ Finset.range (n + 1), (2 * n).choose (2 * k) := by
  unfold EE
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk
    simp at hk
    exact Nat.choose_eq_zero_of_lt (by omega)

lemma OO_restrict (n : ℕ) : OO (2 * n + 2) = ∑ k ∈ Finset.range (n + 1), (2 * n + 2).choose (2 * k + 1) := by
  unfold OO
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk
    simp at hk
    exact Nat.choose_eq_zero_of_lt (by omega)

lemma key (n : ℕ) : ∑ k ∈ Finset.range (n + 1), 4 * ((k : ℚ) * (n - k)) * ((2 * n + 2).choose (2 * k + 1) : ℚ)
    = (2 * n + 2) * (2 * n + 1) * (EE (2 * n) : ℚ) - (2 * n + 1) * (OO (2 * n + 2) : ℚ) := by
  rw [Finset.sum_congr rfl (fun k hk => term n k (by simpa [Nat.lt_succ_iff] using hk)), Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, EE_restrict, OO_restrict]
  push_cast
  rfl

theorem sumT (n : ℕ) (hn : 1 ≤ n) : ∑ k ∈ Finset.Ico 1 n, T n k
    = (∑ k ∈ Finset.range (n + 1), 4 * ((k : ℚ) * (n - k)) * ((2 * n + 2).choose (2 * k + 1) : ℚ)) / (4 * (4 * n + 2)) := by
  rw [Finset.sum_range_eq_add_Ico _ (by omega), Finset.sum_Ico_succ_top hn]
  simp only [T]
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_self, zero_add, add_zero]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

end OMA.S_oeis_a375853

theorem OMA.solution : type_of% @OMA.S_oeis_a375853.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [OMA.S_oeis_a375853.sumT _ (by omega), OMA.S_oeis_a375853.key]
  have h1 : OMA.S_oeis_a375853.EE (2 * (m + 2)) = 2 ^ (2 * (m + 2) - 1) := by
    have := OMA.S_oeis_a375853.EE_eq (2 * (m + 2) - 1)
    rwa [show 2 * (m + 2) - 1 + 1 = 2 * (m + 2) by omega] at this
  have h2 : OMA.S_oeis_a375853.OO (2 * (m + 2) + 2) = 2 ^ (2 * (m + 2) + 1) := by
    exact OMA.S_oeis_a375853.OO_eq _
  rw [h1, h2]
  simp only [OMA.S_oeis_a375853.A002699]
  have e1 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  have e2 : 2 * (m + 2 - 1) - 1 = 2 * m + 1 := by omega
  rw [e1, e2]
  push_cast
  field_simp
  ring
