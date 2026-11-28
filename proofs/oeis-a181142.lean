import OMAStatements.S_oeis_a181142
import Mathlib

open OMA.S_oeis_a181142

namespace P181142

open Finset

def Pp (n k : ℚ) : ℚ := -8 - 12 * k - 4 * k ^ 2 + 44 * n + 46 * n * k + 10 * n * k ^ 2 - 68 * n ^ 2
  - 48 * n ^ 2 * k - 8 * n ^ 2 * k ^ 2 + 40 * n ^ 3 + 22 * n ^ 3 * k + 2 * n ^ 3 * k ^ 2 - 8 * n ^ 4 - 4 * n ^ 4 * k

def β (m k : ℕ) : ℚ := ((m + 1).choose k : ℚ) * (-2) ^ k * ((2 * m + 1 - k).factorial : ℚ)

def Gf (m k : ℕ) : ℚ := Pp ((m : ℚ) + 2) k * k / (-2 * ((m : ℚ) + 1) * m) * β m k

lemma facs (m k : ℕ) (hk : k ≤ m + 1) (hm : 1 ≤ m) :
    ((2 * (m + 2) - k).factorial : ℚ) = ((2 * m - k).factorial : ℚ) *
      ((2 * (m : ℚ) + 4 - k) * (2 * m + 3 - k) * (2 * m + 2 - k) * (2 * m + 1 - k)) ∧
    ((2 * (m + 1) - k).factorial : ℚ) = ((2 * m - k).factorial : ℚ) * ((2 * (m : ℚ) + 2 - k) * (2 * m + 1 - k)) ∧
    ((2 * m + 1 - k).factorial : ℚ) = ((2 * m - k).factorial : ℚ) * (2 * (m : ℚ) + 1 - k) ∧
    ((2 * m + 1 - (k + 1)).factorial : ℚ) = ((2 * m - k).factorial : ℚ) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * m - k = r := ⟨_, rfl⟩
  have hr' : (r : ℚ) = 2 * m - k := by
    rw [← hr, Nat.cast_sub (by omega)]; push_cast; ring
  rw [show 2 * (m + 2) - k = r + 1 + 1 + 1 + 1 by omega, show 2 * m + 1 - k = r + 1 by omega,
    show 2 * (m + 1) - k = r + 1 + 1 by omega, show 2 * m - k = r by omega,
    show 2 * m + 1 - (k + 1) = r by omega]
  simp only [Nat.factorial_succ]
  push_cast
  rw [hr']
  refine ⟨by ring, by ring, by ring, by simp⟩

lemma ch1 (m k : ℕ) (hk : k ≤ m + 1) :
    (m.choose k : ℚ) = ((m + 1).choose k : ℚ) * ((m : ℚ) + 1 - k) / ((m : ℚ) + 1) := by
  have h := Nat.choose_mul_succ_eq m k
  have h' : (m.choose k : ℚ) * ((m : ℚ) + 1) = ((m + 1).choose k : ℚ) * ((m : ℚ) + 1 - k) := by
    have : ((m + 1 - k : ℕ) : ℚ) = (m : ℚ) + 1 - k := by rw [Nat.cast_sub hk]; push_cast; ring
    rw [← this]; exact_mod_cast h
  have : ((m : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

lemma ch0 (m k : ℕ) (hk : k ≤ m + 1) (hm : 1 ≤ m) :
    ((m - 1).choose k : ℚ) = ((m + 1).choose k : ℚ) * ((m : ℚ) + 1 - k) * ((m : ℚ) - k) /
      (((m : ℚ) + 1) * m) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  rw [show p + 1 - 1 = p by omega]
  rcases Nat.lt_or_ge (p + 1) k with h | h
  · have hk2 : k = p + 2 := by omega
    subst hk2
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    push_cast; ring
  · have e1 := ch1 p k (by omega)
    have e2 := ch1 (p + 1) k hk
    rw [e1, e2]
    push_cast
    have : ((p : ℚ) + 1) ≠ 0 := by positivity
    have : ((p : ℚ) + 1 + 1) ≠ 0 := by positivity
    field_simp

lemma chs (m k : ℕ) (hk : k ≤ m + 1) :
    ((m + 1).choose (k + 1) : ℚ) = ((m + 1).choose k : ℚ) * ((m : ℚ) + 1 - k) / ((k : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (m + 1) k
  have h' : ((m + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((m + 1).choose k : ℚ) * ((m : ℚ) + 1 - k) := by
    have : ((m + 1 - k : ℕ) : ℚ) = (m : ℚ) + 1 - k := by rw [Nat.cast_sub hk]; push_cast; ring
    rw [← this]; exact_mod_cast h
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

lemma term (m k : ℕ) (hk : k ≤ m + 1) (hm : 1 ≤ m) :
    (1 - ((m : ℚ) + 2)) * (((m + 1).choose k : ℚ) * (-2) ^ k * ((2 * (m + 2) - k).factorial : ℚ)) +
    2 * (2 * ((m : ℚ) + 2) - 1) * (((m : ℚ) + 2) ^ 2 - ((m : ℚ) + 2) - 1) *
      ((m.choose k : ℚ) * (-2) ^ k * ((2 * (m + 1) - k).factorial : ℚ)) +
    4 * ((m : ℚ) + 2) ^ 2 * ((m : ℚ) + 2 - 2) *
      (((m - 1).choose k : ℚ) * (-2) ^ k * ((2 * m - k).factorial : ℚ)) =
    Gf m (k + 1) - Gf m k := by
  obtain ⟨f2, f1, fb, fs⟩ := facs m k hk hm
  unfold Gf β
  rw [f2, f1, fb, fs, ch1 m k hk, ch0 m k hk hm, chs m k hk]
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hk' : (k : ℚ) ≤ m + 1 := by exact_mod_cast hk
  have : ((m : ℚ) + 1) ≠ 0 := by positivity
  have : (m : ℚ) ≠ 0 := by positivity
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  unfold Pp
  push_cast
  field_simp
  ring

lemma tele (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ range (m + 2), ((1 - ((m : ℚ) + 2)) * (((m + 1).choose k : ℚ) * (-2) ^ k * ((2 * (m + 2) - k).factorial : ℚ)) +
    2 * (2 * ((m : ℚ) + 2) - 1) * (((m : ℚ) + 2) ^ 2 - ((m : ℚ) + 2) - 1) *
      ((m.choose k : ℚ) * (-2) ^ k * ((2 * (m + 1) - k).factorial : ℚ)) +
    4 * ((m : ℚ) + 2) ^ 2 * ((m : ℚ) + 2 - 2) *
      (((m - 1).choose k : ℚ) * (-2) ^ k * ((2 * m - k).factorial : ℚ))) = 0 := by
  rw [Finset.sum_congr rfl (fun k hk => term m k (by simp at hk; omega) hm), Finset.sum_range_sub]
  unfold Gf β
  rw [Nat.choose_eq_zero_of_lt (show m + 1 < m + 2 by omega)]
  simp

lemma ext (m e : ℕ) (f : ℕ → ℚ) (hf : ∀ k, m ≤ k → f k = 0) :
    ∑ k ∈ range m, f k = ∑ k ∈ range (m + e), f k := by
  induction e with
  | zero => rfl
  | succ e ih => rw [← add_assoc, Finset.sum_range_succ, ← ih, hf _ (by omega), add_zero]

end P181142

theorem OMA.solution : type_of% @OMA.S_oeis_a181142.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have t := P181142.tele m hm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at t
  have e2 : (a (m + 2) : ℚ) = ∑ k ∈ Finset.range (m + 2), (((m + 1).choose k : ℚ) * (-2) ^ k * ((2 * (m + 2) - k).factorial : ℚ)) := by
    unfold a; push_cast; rfl
  have e1 : (a (m + 2 - 1) : ℚ) = ∑ k ∈ Finset.range (m + 2), ((m.choose k : ℚ) * (-2) ^ k * ((2 * (m + 1) - k).factorial : ℚ)) := by
    rw [show m + 2 - 1 = m + 1 by omega]
    unfold a; push_cast
    rw [P181142.ext (m + 1) 1]
    intro k hk; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have e0 : (a (m + 2 - 2) : ℚ) = ∑ k ∈ Finset.range (m + 2), (((m - 1).choose k : ℚ) * (-2) ^ k * ((2 * m - k).factorial : ℚ)) := by
    rw [show m + 2 - 2 = m by omega]
    unfold a; push_cast
    rw [P181142.ext m 2]
    intro k hk; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have goalq : (-((m + 2 : ℕ) : ℚ) + 1) * (a (m + 2) : ℚ) +
      2 * (2 * ((m + 2 : ℕ) : ℚ) - 1) * (((m + 2 : ℕ) : ℚ) ^ 2 - ((m + 2 : ℕ) : ℚ) - 1) * (a (m + 2 - 1) : ℚ) +
      4 * ((m + 2 : ℕ) : ℚ) ^ 2 * (((m + 2 : ℕ) : ℚ) - 2) * (a (m + 2 - 2) : ℚ) = 0 := by
    rw [e2, e1, e0]
    push_cast
    linear_combination t
  exact_mod_cast goalq
