import OMAStatements.S_oeis_a266594
import Mathlib

namespace A266594Aux
open OMA.S_oeis_a266594 PowerSeries

lemma rule37 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 37 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat) =
      decide ((¬P ∧ ¬R) ∨ (P ∧ ¬Q ∧ R)) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR] <;> decide

lemma step_eq (s : ℤ → Bool) (x : ℤ) (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (hl : s (x - 1) = decide P) (hc : s x = decide Q) (hr : s (x + 1) = decide R) :
    step 37 s x = decide ((¬P ∧ ¬R) ∨ (P ∧ ¬Q ∧ R)) := by
  unfold step
  rw [hl, hc, hr]
  exact rule37 P Q R

lemma inv0 (x : ℤ) : state 37 0 x = decide (x = 0) := rfl

lemma inv1 (x : ℤ) : state 37 1 x = decide (x ≠ -1 ∧ x ≠ 1) := by
  have h : state 37 1 x = step 37 (state 37 0) x := rfl
  rw [h, step_eq (state 37 0) x (x - 1 = 0) (x = 0) (x + 1 = 0) rfl rfl rfl]
  exact decide_eq_decide.mpr (by omega)

lemma inv2 (x : ℤ) : state 37 2 x = decide (-1 ≤ x ∧ x ≤ 1) := by
  have h : state 37 2 x = step 37 (state 37 1) x := rfl
  rw [h, step_eq (state 37 1) x _ _ _ (inv1 (x - 1)) (inv1 x) (inv1 (x + 1))]
  exact decide_eq_decide.mpr (by omega)

lemma odd_of_even (n : ℕ) (h : ∀ x : ℤ, state 37 n x = decide (-1 ≤ x ∧ x ≤ 1)) :
    ∀ x : ℤ, state 37 (n + 1) x = decide (x < -2 ∨ 2 < x) := by
  intro x
  have e : state 37 (n + 1) x = step 37 (state 37 n) x := rfl
  rw [e, step_eq (state 37 n) x _ _ _ (h (x - 1)) (h x) (h (x + 1))]
  exact decide_eq_decide.mpr (by omega)

lemma even_of_odd (n : ℕ) (h : ∀ x : ℤ, state 37 n x = decide (x < -2 ∨ 2 < x)) :
    ∀ x : ℤ, state 37 (n + 1) x = decide (-1 ≤ x ∧ x ≤ 1) := by
  intro x
  have e : state 37 (n + 1) x = step 37 (state 37 n) x := rfl
  rw [e, step_eq (state 37 n) x _ _ _ (h (x - 1)) (h x) (h (x + 1))]
  exact decide_eq_decide.mpr (by omega)

lemma inv_even (m : ℕ) : ∀ x : ℤ, state 37 (2 * m + 2) x = decide (-1 ≤ x ∧ x ≤ 1) := by
  induction m with
  | zero => intro x; exact inv2 x
  | succ m ih =>
    rw [show 2 * (m + 1) + 2 = 2 * m + 2 + 1 + 1 by ring]
    exact even_of_odd _ (odd_of_even _ ih)

lemma inv_odd (m : ℕ) : ∀ x : ℤ, state 37 (2 * m + 3) x = decide (x < -2 ∨ 2 < x) :=
  odd_of_even _ (inv_even m)

lemma rc_even (m k : ℕ) (hk : k = 2 * m + 2) : rowCount (state 37 k) k = 3 := by
  subst hk
  unfold rowCount
  have h : (Finset.Icc (-((2 * m + 2 : ℕ) : ℤ)) ((2 * m + 2 : ℕ) : ℤ)).filter
      (fun x => state 37 (2 * m + 2) x = true) = Finset.Icc (-1) 1 := by
    ext x
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, inv_even m x, decide_eq_true_eq]
    push_cast
    omega
  rw [h]
  rfl

lemma rc_odd (m k : ℕ) (hk : k = 2 * m + 3) : rowCount (state 37 k) k = 4 * m + 2 := by
  subst hk
  unfold rowCount
  have h : (Finset.Icc (-((2 * m + 3 : ℕ) : ℤ)) ((2 * m + 3 : ℕ) : ℤ)).filter
      (fun x => state 37 (2 * m + 3) x = true) =
      Finset.Icc (-((2 * m + 3 : ℕ) : ℤ)) (-3) ∪ Finset.Icc 3 ((2 * m + 3 : ℕ) : ℤ) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc,
      inv_odd m x, decide_eq_true_eq]
    push_cast
    omega
  have hdisj : Disjoint (Finset.Icc (-((2 * m + 3 : ℕ) : ℤ)) (-3))
      (Finset.Icc 3 ((2 * m + 3 : ℕ) : ℤ)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  rw [h, Finset.card_union_of_disjoint hdisj, Int.card_Icc, Int.card_Icc]
  push_cast
  omega

lemma rc_0 : rowCount (state 37 0) 0 = 1 := by
  unfold rowCount
  have h : (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter
      (fun x => state 37 0 x = true) = Finset.Icc 0 0 := by
    ext x
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, inv0 x, decide_eq_true_eq]
    push_cast
    omega
  rw [h]
  rfl

lemma rc_1 : rowCount (state 37 1) 1 = 1 := by
  unfold rowCount
  have h : (Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).filter
      (fun x => state 37 1 x = true) = Finset.Icc 0 0 := by
    ext x
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, inv1 x, decide_eq_true_eq]
    push_cast
    omega
  rw [h]
  rfl

lemma a_succ (n k : ℕ) (hk : k = n + 1) : a k = a n + rowCount (state 37 k) k := by
  subst hk
  unfold a
  rw [Finset.sum_range_succ]

lemma a_0 : a 0 = 1 := by
  unfold a
  rw [Finset.sum_range_one, rc_0]

lemma a_1 : a 1 = 2 := by rw [a_succ 0 1 rfl, a_0, rc_1]

lemma closed (m : ℕ) : a (2 * m + 1) = 2 * m * m + 3 * m + 2 ∧
    a (2 * m + 2) = 2 * m * m + 3 * m + 5 := by
  induction m with
  | zero =>
    refine ⟨a_1, ?_⟩
    show a 2 = 5
    rw [a_succ 1 2 rfl, a_1, rc_even 0 2 rfl]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : a (2 * (m + 1) + 1) = 2 * (m + 1) * (m + 1) + 3 * (m + 1) + 2 := by
      rw [a_succ (2 * m + 2) (2 * (m + 1) + 1) (by ring), h2,
        rc_odd m (2 * (m + 1) + 1) (by ring)]
      ring
    have e2 : a (2 * (m + 1) + 2) = 2 * (m + 1) * (m + 1) + 3 * (m + 1) + 5 := by
      rw [a_succ (2 * (m + 1) + 1) (2 * (m + 1) + 2) rfl, e1,
        rc_even (m + 1) (2 * (m + 1) + 2) rfl]
    exact ⟨e1, e2⟩

lemma cl1 (m k : ℕ) (hk : k = 2 * m + 1) : (a k : ℤ) = 2 * m * m + 3 * m + 2 := by
  subst hk
  rw [(closed m).1]
  push_cast
  ring

lemma cl2 (m k : ℕ) (hk : k = 2 * m + 2) : (a k : ℤ) = 2 * m * m + 3 * m + 5 := by
  subst hk
  rw [(closed m).2]
  push_cast
  ring

lemma part1 (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = ((n : ℚ) ^ 2 - (-1) ^ n * ((n : ℚ) - 3) + 5) / 2 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 ∨ n = 2 * m + 2 := ⟨(n - 1) / 2, by omega⟩
  rcases hm with rfl | rfl
  · have hs : (-1 : ℚ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [(closed m).1, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (2 * m + 2) = 1 := by
      rw [pow_add, pow_mul]; norm_num
    rw [(closed m).2, hs]
    push_cast
    ring

lemma recN (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨i, hi⟩ : ∃ i, n = 2 * i + 6 ∨ n = 2 * i + 7 := ⟨(n - 6) / 2, by omega⟩
  rcases hi with rfl | rfl
  · rw [show 2 * i + 6 - 1 = 2 * i + 5 by omega, show 2 * i + 6 - 2 = 2 * i + 4 by omega,
      show 2 * i + 6 - 3 = 2 * i + 3 by omega, show 2 * i + 6 - 4 = 2 * i + 2 by omega,
      show 2 * i + 6 - 5 = 2 * i + 1 by omega]
    rw [cl2 (i + 2) (2 * i + 6) (by ring), cl1 (i + 2) (2 * i + 5) (by ring),
      cl2 (i + 1) (2 * i + 4) (by ring), cl1 (i + 1) (2 * i + 3) (by ring),
      cl2 i (2 * i + 2) rfl, cl1 i (2 * i + 1) rfl]
    push_cast
    ring
  · rw [show 2 * i + 7 - 1 = 2 * i + 6 by omega, show 2 * i + 7 - 2 = 2 * i + 5 by omega,
      show 2 * i + 7 - 3 = 2 * i + 4 by omega, show 2 * i + 7 - 4 = 2 * i + 3 by omega,
      show 2 * i + 7 - 5 = 2 * i + 2 by omega]
    rw [cl1 (i + 3) (2 * i + 7) (by ring), cl2 (i + 2) (2 * i + 6) (by ring),
      cl1 (i + 2) (2 * i + 5) (by ring), cl2 (i + 1) (2 * i + 4) (by ring),
      cl1 (i + 1) (2 * i + 3) (by ring), cl2 i (2 * i + 2) rfl]
    push_cast
    ring

lemma a_2 : a 2 = 5 := (closed 0).2
lemma a_3 : a 3 = 7 := (closed 1).1
lemma a_4 : a 4 = 10 := (closed 1).2
lemma a_5 : a 5 = 16 := (closed 2).1

lemma hD : ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) =
    1 - X - C 2 * X ^ 2 + C 2 * X ^ 3 + X ^ 4 - X ^ 5 := by
  simp only [map_ofNat]
  ring

lemma dcoeff (k : ℕ) : coeff k ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) =
    (if k = 0 then 1 else 0) - (if k = 1 then 1 else 0) - 2 * (if k = 2 then 1 else 0) +
      2 * (if k = 3 then 1 else 0) + (if k = 4 then 1 else 0) - (if k = 5 then 1 else 0) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma hN : (1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5 : ℚ⟦X⟧) =
    1 + X + X ^ 2 - C 2 * X ^ 4 + C 3 * X ^ 5 := by
  simp only [map_ofNat]

lemma ncoeff (k : ℕ) : coeff k (1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5 : ℚ⟦X⟧) =
    (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) -
      2 * (if k = 4 then 1 else 0) + 3 * (if k = 5 then 1 else 0) := by
  rw [hN]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma sum_d (f : ℕ → ℚ) (n : ℕ) (hn : 5 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), coeff k ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) * f k =
      f 0 - f 1 - 2 * f 2 + 2 * f 3 + f 4 - f 5 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 6 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 6 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
      show k ≠ 4 by omega, show k ≠ 5 by omega]

lemma AD : A * ((1 - X) ^ 3 * (1 + X) ^ 2) = 1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5 := by
  ext n
  rw [mul_comm A, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) * coeff j A)]
  simp only [A, coeff_mk]
  by_cases hn : 6 ≤ n
  · rw [sum_d (fun k => (a (n - k) : ℚ)) n (by omega)]
    have hr := recN n (by omega)
    have hr' : (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
      exact_mod_cast hr
    have hz : coeff n (1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5 : ℚ⟦X⟧) = 0 := by
      rw [ncoeff]
      simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega,
        show n ≠ 5 by omega]
    rw [hz, Nat.sub_zero]
    linarith
  · have hn' : n ≤ 5 := by omega
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, ncoeff, a_0, a_1, a_2, a_3, a_4, a_5]
end A266594Aux

open OMA.S_oeis_a266594 PowerSeries A266594Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266594.main := by
  refine ⟨part1, recN, ?_⟩
  have hc : constantCoeff ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← AD, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]
