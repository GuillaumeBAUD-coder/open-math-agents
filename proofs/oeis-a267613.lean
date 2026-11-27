import OMAStatements.S_oeis_a267613
import Mathlib

namespace A267613Aux
open OMA.S_oeis_a267613 PowerSeries

lemma rule185 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 185 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat) =
      decide ((¬P ∧ (Q ↔ R)) ∨ (P ∧ (¬Q ∨ R))) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR] <;> decide

lemma step_eq (s : ℤ → Bool) (x : ℤ) (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (hl : s (x - 1) = decide P) (hc : s x = decide Q) (hr : s (x + 1) = decide R) :
    step 185 s x = decide ((¬P ∧ (Q ↔ R)) ∨ (P ∧ (¬Q ∨ R))) := by
  unfold step
  rw [hl, hc, hr]
  exact rule185 P Q R

lemma inv1 (x : ℤ) : state 185 1 x = decide (x ≠ -1 ∧ x ≠ 0) := by
  have h : state 185 1 x = step 185 (state 185 0) x := rfl
  rw [h, step_eq (state 185 0) x (x - 1 = 0) (x = 0) (x + 1 = 0) rfl rfl rfl]
  exact decide_eq_decide.mpr (by omega)

lemma inv2 (x : ℤ) : state 185 2 x = decide (x ≠ -2 ∧ x ≠ 0) := by
  have h : state 185 2 x = step 185 (state 185 1) x := rfl
  rw [h, step_eq (state 185 1) x _ _ _ (inv1 (x - 1)) (inv1 x) (inv1 (x + 1))]
  exact decide_eq_decide.mpr (by omega)

lemma inv (n : ℕ) : ∀ x : ℤ,
    state 185 (n + 2) x = decide (x ≠ -((n : ℤ) + 2) ∧ x ≠ -(n : ℤ)) := by
  induction n with
  | zero =>
    intro x
    show state 185 2 x = _
    rw [inv2]
    exact decide_eq_decide.mpr (by push_cast; omega)
  | succ n ih =>
    intro x
    have h : state 185 (n + 1 + 2) x = step 185 (state 185 (n + 2)) x := rfl
    rw [h, step_eq (state 185 (n + 2)) x _ _ _ (ih (x - 1)) (ih x) (ih (x + 1))]
    exact decide_eq_decide.mpr (by push_cast; omega)

lemma val (n i : ℕ) : (state 185 (n + 2) (((n + 2 : ℕ) : ℤ) - (i : ℤ))).toNat =
    if i = 2 * n + 4 ∨ i = 2 * n + 2 then 0 else 1 := by
  rw [inv]
  by_cases h : i = 2 * n + 4 ∨ i = 2 * n + 2
  · rw [if_pos h]
    have hd : ¬ (((n + 2 : ℕ) : ℤ) - (i : ℤ) ≠ -((n : ℤ) + 2) ∧
        ((n + 2 : ℕ) : ℤ) - (i : ℤ) ≠ -(n : ℤ)) := by push_cast; omega
    rw [decide_eq_false hd]; rfl
  · rw [if_neg h]
    have hd : (((n + 2 : ℕ) : ℤ) - (i : ℤ) ≠ -((n : ℤ) + 2) ∧
        ((n + 2 : ℕ) : ℤ) - (i : ℤ) ≠ -(n : ℤ)) := by push_cast; omega
    rw [decide_eq_true hd]; rfl

lemma a_closed (n : ℕ) :
    a (n + 2) = (∑ i ∈ Finset.range (2 * n + 2), 10 ^ i) + 10 ^ (2 * n + 3) := by
  unfold a rowDigits
  simp only [val]
  rw [show 2 * (n + 2) + 1 = 2 * n + 2 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have T0 : (if 2 * n + 2 = 2 * n + 4 ∨ 2 * n + 2 = 2 * n + 2 then 0 else 1) = 0 :=
    if_pos (by omega)
  have T1 : (if 2 * n + 2 + 1 = 2 * n + 4 ∨ 2 * n + 2 + 1 = 2 * n + 2 then 0 else 1) = 1 :=
    if_neg (by omega)
  have T2 : (if 2 * n + 2 + 1 + 1 = 2 * n + 4 ∨ 2 * n + 2 + 1 + 1 = 2 * n + 2 then 0 else 1)
      = 0 := if_pos (by omega)
  have S : ∑ i ∈ Finset.range (2 * n + 2),
      (if i = 2 * n + 4 ∨ i = 2 * n + 2 then 0 else 1) * 10 ^ i =
      ∑ i ∈ Finset.range (2 * n + 2), 10 ^ i :=
    Finset.sum_congr rfl (fun i hi => by
      have hi' := Finset.mem_range.mp hi
      rw [if_neg (by omega), one_mul])
  rw [T0, T1, T2, S]
  ring

lemma G_succ (n k : ℕ) (hk : k = n + 1) : ∑ i ∈ Finset.range (2 * k + 2), 10 ^ i =
    (∑ i ∈ Finset.range (2 * n + 2), 10 ^ i) + 10 ^ (2 * n + 2) + 10 ^ (2 * n + 2 + 1) := by
  subst hk
  rw [show 2 * (n + 1) + 2 = 2 * n + 2 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ]

lemma recur (m : ℕ) : (a (m + 4) : ℤ) = 101 * a (m + 3) - 100 * a (m + 2) := by
  have h2 := a_closed m
  have h3 := a_closed (m + 1)
  have h4 := a_closed (m + 2)
  have g1 := G_succ m (m + 1) rfl
  have g2 := G_succ (m + 1) (m + 2) rfl
  rw [g2, g1] at h4
  rw [g1] at h3
  have e4 : a (m + 4) = a (m + 2 + 2) := rfl
  have e3 : a (m + 3) = a (m + 1 + 2) := rfl
  rw [e4, e3, h4, h3, h2]
  push_cast
  ring

lemma recN (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
  exact recur m

lemma a_0 : a 0 = 1 := by decide
lemma a_1 : a 1 = 1 := by decide
lemma a_2 : a 2 = 1011 := by
  have h := a_closed 0
  norm_num [Finset.sum_range_succ] at h
  exact h
lemma a_3 : a 3 = 101111 := by
  have h := a_closed 1
  norm_num [Finset.sum_range_succ] at h
  exact h

lemma hD : ((1 - X) * (1 - 100 * X) : ℚ⟦X⟧) = 1 - C 101 * X + C 100 * X ^ 2 := by
  simp only [map_ofNat]
  ring

lemma dcoeff (k : ℕ) : coeff k ((1 - X) * (1 - 100 * X) : ℚ⟦X⟧) =
    (if k = 0 then 1 else 0) - 101 * (if k = 1 then 1 else 0) +
      100 * (if k = 2 then 1 else 0) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma hN : (1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3 : ℚ⟦X⟧) =
    1 - C 100 * X + C 1010 * X ^ 2 - C 900 * X ^ 3 := by
  simp only [map_ofNat]

lemma ncoeff (k : ℕ) : coeff k (1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3 : ℚ⟦X⟧) =
    (if k = 0 then 1 else 0) - 100 * (if k = 1 then 1 else 0) +
      1010 * (if k = 2 then 1 else 0) - 900 * (if k = 3 then 1 else 0) := by
  rw [hN]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma sum_d (f : ℕ → ℚ) (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), coeff k ((1 - X) * (1 - 100 * X) : ℚ⟦X⟧) * f k =
      f 0 - 101 * f 1 + 100 * f 2 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 3 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 3 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

lemma AD : A * ((1 - X) * (1 - 100 * X)) = 1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3 := by
  ext n
  rw [mul_comm A, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i ((1 - X) * (1 - 100 * X) : ℚ⟦X⟧) * coeff j A)]
  simp only [A, coeff_mk]
  by_cases hn : 4 ≤ n
  · rw [sum_d (fun k => (a (n - k) : ℚ)) n (by omega)]
    have hr := recN n (by omega)
    have hr' : (a n : ℚ) = 101 * a (n - 1) - 100 * a (n - 2) := by exact_mod_cast hr
    have hz : coeff n (1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3 : ℚ⟦X⟧) = 0 := by
      rw [ncoeff]
      simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega]
    rw [hz, Nat.sub_zero]
    linarith
  · have hn' : n ≤ 3 := by omega
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, ncoeff, a_0, a_1, a_2, a_3]
end A267613Aux

open OMA.S_oeis_a267613 PowerSeries A267613Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267613.main := by
  refine ⟨recN, ?_⟩
  have hc : constantCoeff ((1 - X) * (1 - 100 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← AD, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]
