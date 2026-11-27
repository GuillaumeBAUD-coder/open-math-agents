import OMAStatements.S_oeis_a266790
import Mathlib

namespace A266790Aux
open OMA.S_oeis_a266790 PowerSeries

lemma rule61 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 61 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat) =
      decide ((¬P ∧ (¬R ∨ Q)) ∨ (P ∧ ¬Q)) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR] <;> decide

lemma step_eq (n : ℕ) (x : ℤ) (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (hl : state n (x - 1) = decide P) (hc : state n x = decide Q)
    (hr : state n (x + 1) = decide R) :
    state (n + 1) x = decide ((¬P ∧ (¬R ∨ Q)) ∨ (P ∧ ¬Q)) := by
  have h : state (n + 1) x = eca 61 (state n (x - 1)) (state n x) (state n (x + 1)) := rfl
  rw [h, hl, hc, hr]
  unfold eca
  exact rule61 P Q R

lemma inv1 (x : ℤ) : state 1 x = decide (x ≠ -1) :=
  (step_eq 0 x (x - 1 = 0) (x = 0) (x + 1 = 0) rfl rfl rfl).trans
    (decide_eq_decide.mpr (by omega))

lemma inv2 (x : ℤ) : state 2 x = decide (x = -1 ∨ x = 0) :=
  (step_eq 1 x _ _ _ (inv1 (x - 1)) (inv1 x) (inv1 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv3 (x : ℤ) : state 3 x = decide (x ≠ -2 ∧ x ≠ 0) :=
  (step_eq 2 x _ _ _ (inv2 (x - 1)) (inv2 x) (inv2 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv4 (x : ℤ) : state 4 x = decide (-2 ≤ x ∧ x ≤ 1) :=
  (step_eq 3 x _ _ _ (inv3 (x - 1)) (inv3 x) (inv3 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv5 (x : ℤ) : state 5 x = decide (¬ (x = -3 ∨ x = -1 ∨ x = 0 ∨ x = 1)) :=
  (step_eq 4 x _ _ _ (inv4 (x - 1)) (inv4 x) (inv4 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma O_to_E (n i : ℕ)
    (h : ∀ x : ℤ, state n x = decide (¬ (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨
      x = -(i : ℤ) + 1))) :
    ∀ x : ℤ, state (n + 1) x = decide (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 2 ∨
      x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨ x = -(i : ℤ) + 2) := by
  intro x
  exact (step_eq n x _ _ _ (h (x - 1)) (h x) (h (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma E_to_O (n i : ℕ)
    (h : ∀ x : ℤ, state n x = decide (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 2 ∨
      x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨ x = -(i : ℤ) + 2)) :
    ∀ x : ℤ, state (n + 1) x = decide (¬ (x = -((i + 1 : ℕ) : ℤ) - 3 ∨
      x = -((i + 1 : ℕ) : ℤ) - 1 ∨ x = -((i + 1 : ℕ) : ℤ) ∨ x = -((i + 1 : ℕ) : ℤ) + 1)) := by
  intro x
  exact (step_eq n x _ _ _ (h (x - 1)) (h x) (h (x + 1))).trans
    (decide_eq_decide.mpr (by push_cast; omega))

lemma invO (i : ℕ) : ∀ x : ℤ, state (2 * i + 5) x =
    decide (¬ (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨ x = -(i : ℤ) + 1)) := by
  induction i with
  | zero =>
    intro x
    show state 5 x = _
    rw [inv5]
    exact decide_eq_decide.mpr (by push_cast; omega)
  | succ i ih =>
    rw [show 2 * (i + 1) + 5 = 2 * i + 5 + 1 + 1 by ring]
    exact E_to_O _ i (O_to_E _ i ih)

lemma invE (i : ℕ) : ∀ x : ℤ, state (2 * i + 5 + 1) x =
    decide (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 2 ∨ x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨
      x = -(i : ℤ) + 2) :=
  O_to_E _ i (invO i)

lemma mO (i : ℕ) : state (2 * i + 5) 0 = decide (2 ≤ i) :=
  (invO i 0).trans (decide_eq_decide.mpr (by omega))

lemma mE (i : ℕ) : state (2 * i + 5 + 1) 0 = decide (i = 0 ∨ i = 2) :=
  (invE i 0).trans (decide_eq_decide.mpr (by omega))

lemma mid (t : ℕ) (ht : 11 ≤ t) : state t 0 = decide (t % 2 = 1) := by
  obtain ⟨i, hi⟩ : ∃ i, t = 2 * i + 5 ∨ t = 2 * i + 5 + 1 := ⟨(t - 5) / 2, by omega⟩
  rcases hi with rfl | rfl
  · exact (mO i).trans (decide_eq_decide.mpr (by omega))
  · exact (mE i).trans (decide_eq_decide.mpr (by omega))

lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + (if state (n + 1) 0 then 1 else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero]
  congr 1
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have ht' := Finset.mem_range.mp ht
  by_cases h : state t 0 = true
  · rw [if_pos h, if_pos h, show n + 1 - t = (n - t) + 1 by omega, pow_succ]
    ring
  · rw [if_neg h, if_neg h, mul_zero]

lemma a_step (n k v w : ℕ) (b : Bool) (hk : k = n + 1) (hv : a n = v) (hb : state k 0 = b)
    (hw : w = 10 * v + (if b then 1 else 0)) : a k = w := by
  subst hk
  rw [a_succ, hv, hb, hw]

lemma m0 : state 0 0 = true := by decide
lemma m1 : state 1 0 = true := (inv1 0).trans (by decide)
lemma m2 : state 2 0 = true := (inv2 0).trans (by decide)
lemma m3 : state 3 0 = false := (inv3 0).trans (by decide)
lemma m4 : state 4 0 = true := (inv4 0).trans (by decide)
lemma m5 : state 5 0 = false := (mO 0).trans (by decide)
lemma m6 : state 6 0 = true := (mE 0).trans (by decide)
lemma m7 : state 7 0 = false := (mO 1).trans (by decide)
lemma m8 : state 8 0 = false := (mE 1).trans (by decide)
lemma m9 : state 9 0 = true := (mO 2).trans (by decide)
lemma m10 : state 10 0 = true := (mE 2).trans (by decide)
lemma m11 : state 11 0 = true := (mO 3).trans (by decide)
lemma m12 : state 12 0 = false := (mE 3).trans (by decide)

lemma a_0 : a 0 = 1 := by decide
lemma a_1 : a 1 = 11 := a_step 0 1 1 11 true rfl a_0 m1 (by decide)
lemma a_2 : a 2 = 111 := a_step 1 2 11 111 true rfl a_1 m2 (by decide)
lemma a_3 : a 3 = 1110 := a_step 2 3 111 1110 false rfl a_2 m3 (by decide)
lemma a_4 : a 4 = 11101 := a_step 3 4 1110 11101 true rfl a_3 m4 (by decide)
lemma a_5 : a 5 = 111010 := a_step 4 5 11101 111010 false rfl a_4 m5 (by decide)
lemma a_6 : a 6 = 1110101 := a_step 5 6 111010 1110101 true rfl a_5 m6 (by decide)
lemma a_7 : a 7 = 11101010 := a_step 6 7 1110101 11101010 false rfl a_6 m7 (by decide)
lemma a_8 : a 8 = 111010100 := a_step 7 8 11101010 111010100 false rfl a_7 m8 (by decide)
lemma a_9 : a 9 = 1110101001 := a_step 8 9 111010100 1110101001 true rfl a_8 m9 (by decide)
lemma a_10 : a 10 = 11101010011 :=
  a_step 9 10 1110101001 11101010011 true rfl a_9 m10 (by decide)
lemma a_11 : a 11 = 111010100111 :=
  a_step 10 11 11101010011 111010100111 true rfl a_10 m11 (by decide)
lemma a_12 : a 12 = 1110101001110 :=
  a_step 11 12 111010100111 1110101001110 false rfl a_11 m12 (by decide)

lemma closed (k : ℕ) : 198 * (a (k + 10) : ℤ) =
    -9 * (-1) ^ (k + 10) + 1098999991099 * 2 ^ (k + 1) * 5 ^ k - 11 := by
  induction k with
  | zero =>
    show 198 * (a 10 : ℤ) = _
    rw [a_10]
    norm_num
  | succ k ih =>
    have hs : a (k + 1 + 10) = 10 * a (k + 10) + (if state (k + 10 + 1) 0 then 1 else 0) :=
      a_succ (k + 10)
    have hm := mid (k + 10 + 1) (by omega)
    rcases Nat.even_or_odd k with he | ho
    · have he' := Nat.even_iff.mp he
      have h1 : (-1 : ℤ) ^ (k + 10) = 1 := Even.neg_one_pow (by
        rw [Nat.even_iff]; omega)
      have h2 : (-1 : ℤ) ^ (k + 1 + 10) = -1 := Odd.neg_one_pow (by
        rw [Nat.odd_iff]; omega)
      rw [decide_eq_true (by omega)] at hm
      rw [hm, if_pos rfl] at hs
      rw [h1] at ih
      rw [hs, h2]
      push_cast
      linear_combination 10 * ih
    · have ho' := Nat.odd_iff.mp ho
      have h1 : (-1 : ℤ) ^ (k + 10) = -1 := Odd.neg_one_pow (by
        rw [Nat.odd_iff]; omega)
      have h2 : (-1 : ℤ) ^ (k + 1 + 10) = 1 := Even.neg_one_pow (by
        rw [Nat.even_iff]; omega)
      rw [decide_eq_false (by omega)] at hm
      rw [hm, if_neg (by decide)] at hs
      rw [h1] at ih
      rw [hs, h2]
      push_cast
      linear_combination 10 * ih

lemma part1 (n : ℕ) (hn : 9 < n) : 198 * (a n : ℤ) =
    -9 * (-1) ^ n + 1098999991099 * 2 ^ (n - 9) * 5 ^ (n - 10) - 11 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  rw [show k + 10 - 9 = k + 1 by omega, show k + 10 - 10 = k by omega]
  exact closed k

lemma rec13 (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℤ) - 10 * a (n - 1) - a (n - 2) + 10 * a (n - 3) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have s3 : a (k + 3) = 10 * a (k + 2) + (if state (k + 2 + 1) 0 then 1 else 0) := a_succ (k + 2)
  have s1 : a (k + 1) = 10 * a k + (if state (k + 1) 0 then 1 else 0) := a_succ k
  have hm3 := mid (k + 2 + 1) (by omega)
  have hm1 := mid (k + 1) (by omega)
  have hpar : decide ((k + 2 + 1) % 2 = 1) = decide ((k + 1) % 2 = 1) :=
    decide_eq_decide.mpr (by omega)
  rw [hm3, hpar, ← hm1] at s3
  rw [s3, s1]
  push_cast
  ring

lemma hD : ((1 - X) * (1 + X) * (1 - 10 * X) : PowerSeries ℤ) =
    1 - C 10 * X - X ^ 2 + C 10 * X ^ 3 := by
  simp only [map_ofNat]
  ring

lemma dcoeff (k : ℕ) : coeff k ((1 - X) * (1 + X) * (1 - 10 * X) : PowerSeries ℤ) =
    (if k = 0 then 1 else 0) - 10 * (if k = 1 then 1 else 0) - (if k = 2 then 1 else 0) +
      10 * (if k = 3 then 1 else 0) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma ncoeff (k : ℕ) :
    coeff k (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 : PowerSeries ℤ) =
    (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0) -
      (if k = 8 then 1 else 0) + (if k = 9 then 1 else 0) + (if k = 10 then 1 else 0) -
      (if k = 12 then 1 else 0) := by
  simp only [map_add, map_sub, coeff_one, coeff_X_pow, coeff_X]

lemma sum_d (f : ℕ → ℤ) (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      coeff k ((1 - X) * (1 + X) * (1 - 10 * X) : PowerSeries ℤ) * f k =
      f 0 - 10 * f 1 - f 2 + 10 * f 3 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 4 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 4 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega]

lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
    (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 : PowerSeries ℤ) := by
  ext n
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i ((1 - X) * (1 + X) * (1 - 10 * X) : PowerSeries ℤ) *
      coeff j (mk (fun n => (a n : ℤ)))), ncoeff]
  simp only [coeff_mk]
  by_cases hn : 13 ≤ n
  · rw [sum_d (fun k => (a (n - k) : ℤ)) n (by omega)]
    have hr := rec13 n hn
    simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
      show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 12 by omega,
      if_false]
    rw [Nat.sub_zero]
    linarith
  · have hn' : n ≤ 12 := by omega
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9,
        a_10, a_11, a_12]
end A266790Aux

open A266790Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266790.main :=
  ⟨part1, gf⟩
