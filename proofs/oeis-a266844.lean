import OMAStatements.S_oeis_a266844
import Mathlib

namespace A266844Aux
open OMA.S_oeis_a266844 PowerSeries

lemma rule70 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 70 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat) =
      decide ((¬P ∧ ¬Q ∧ R) ∨ (Q ∧ ¬R)) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR] <;> decide

lemma inv (n : ℕ) : ∀ x : ℤ,
    state n x = decide (x = -(n : ℤ) ∨ (-(n : ℤ) ≤ x ∧ x ≤ 0 ∧ x % 2 = 0)) := by
  induction n with
  | zero =>
    intro x
    show decide (x = 0) = _
    exact decide_eq_decide.mpr (by push_cast; omega)
  | succ n ih =>
    intro x
    have h : state (n + 1) x = eca 70 (state n (x - 1)) (state n x) (state n (x + 1)) := rfl
    rw [h, ih (x - 1), ih x, ih (x + 1)]
    unfold eca
    rw [rule70]
    exact decide_eq_decide.mpr (by push_cast; omega)

lemma val (n k : ℕ) :
    (if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0) =
      if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * n - k) else 0 := by
  rw [inv]
  by_cases h : (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0))
  · have hP : ((k : ℤ) - (n : ℤ) = -(n : ℤ) ∨
        (-(n : ℤ) ≤ (k : ℤ) - (n : ℤ) ∧ (k : ℤ) - (n : ℤ) ≤ 0 ∧ ((k : ℤ) - (n : ℤ)) % 2 = 0)) := by
      omega
    rw [if_pos h, decide_eq_true hP]
    rfl
  · have hP : ¬ ((k : ℤ) - (n : ℤ) = -(n : ℤ) ∨
        (-(n : ℤ) ≤ (k : ℤ) - (n : ℤ) ∧ (k : ℤ) - (n : ℤ) ≤ 0 ∧ ((k : ℤ) - (n : ℤ)) % 2 = 0)) := by
      omega
    rw [if_neg h, decide_eq_false hP]
    rfl

lemma term_split (n k : ℕ) :
    (if (k = 0 ∨ (k ≤ n + 2 ∧ (n + 2 + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) =
      (if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) +
        (if k = n + 2 then 10 ^ (n + 2) else 0) := by
  by_cases h1 : (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0))
  · rw [if_pos h1, if_pos (by omega), if_neg (by omega), add_zero]
  · by_cases h2 : k = n + 2
    · rw [if_neg h1, if_pos h2, if_pos (by omega), zero_add,
        show 2 * (n + 2) - k = n + 2 by omega]
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]

lemma a_rec (n : ℕ) : a (n + 2) = 10000 * a n + 10 ^ (n + 2) := by
  unfold a
  simp only [val]
  have hA : ∑ k ∈ Finset.range (2 * (n + 2) + 1),
      (if (k = 0 ∨ (k ≤ n + 2 ∧ (n + 2 + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) =
      ∑ k ∈ Finset.range (2 * (n + 2) + 1),
        ((if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) +
          (if k = n + 2 then 10 ^ (n + 2) else 0)) :=
    Finset.sum_congr rfl (fun k _ => term_split n k)
  have hB : ∑ k ∈ Finset.range (2 * (n + 2) + 1), (if k = n + 2 then 10 ^ (n + 2) else 0) =
      10 ^ (n + 2) := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
  have hC : ∑ k ∈ Finset.range (2 * (n + 2) + 1),
      (if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) =
      ∑ k ∈ Finset.range (2 * n + 1),
        (if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    rw [Finset.mem_range] at hk
    rw [if_neg (by omega)]
  have hD : ∑ k ∈ Finset.range (2 * n + 1),
      (if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * (n + 2) - k) else 0) =
      10000 * ∑ k ∈ Finset.range (2 * n + 1),
        (if (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0)) then 10 ^ (2 * n - k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    by_cases h : (k = 0 ∨ (k ≤ n ∧ (n + k) % 2 = 0))
    · rw [if_pos h, if_pos h, show 2 * (n + 2) - k = 4 + (2 * n - k) by omega, pow_add]
      norm_num
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hA, Finset.sum_add_distrib, hB, hC, hD]

lemma a_0 : a 0 = 1 := by decide
lemma a_1 : a 1 = 110 := by decide

lemma closed : ∀ n : ℕ, 198 * (a n : ℤ) = 209 * 100 ^ n - 9 * (-100) ^ n - 2 * 10 ^ n ∧
    198 * (a (n + 1) : ℤ) = 209 * 100 ^ (n + 1) - 9 * (-100) ^ (n + 1) - 2 * 10 ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a_0]; norm_num
    · show 198 * (a 1 : ℤ) = _
      rw [a_1]; norm_num
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    show 198 * (a (n + 2) : ℤ) = 209 * 100 ^ (n + 2) - 9 * (-100) ^ (n + 2) - 2 * 10 ^ (n + 2)
    rw [a_rec]
    push_cast
    linear_combination 10000 * h0

lemma recN (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 10 * a (n - 1) + 10000 * a (n - 2) - 100000 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have h0 := (closed m).1
  have h1 := (closed (m + 1)).1
  have h2 := (closed (m + 2)).1
  have h3 := (closed (m + 3)).1
  have h198 : 198 * (a (m + 3) : ℤ) =
      198 * (10 * a (m + 2) + 10000 * a (m + 1) - 100000 * a m) := by
    linear_combination h3 - 10 * h2 - 10000 * h1 + 100000 * h0
  exact mul_left_cancel₀ (by norm_num : (198 : ℤ) ≠ 0) h198

lemma hD : ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℤ) =
    1 - C 10 * X - C 10000 * X ^ 2 + C 100000 * X ^ 3 := by
  simp only [map_ofNat]
  ring

lemma dcoeff (k : ℕ) :
    coeff k ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℤ) =
    (if k = 0 then 1 else 0) - 10 * (if k = 1 then 1 else 0) -
      10000 * (if k = 2 then 1 else 0) + 100000 * (if k = 3 then 1 else 0) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma hN : (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) = 1 + C 100 * X - C 1000 * X ^ 2 := by
  simp only [map_ofNat]

lemma ncoeff (k : ℕ) : coeff k (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) =
    (if k = 0 then 1 else 0) + 100 * (if k = 1 then 1 else 0) -
      1000 * (if k = 2 then 1 else 0) := by
  rw [hN]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma sum_d (f : ℕ → ℤ) (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      coeff k ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℤ) * f k =
      f 0 - 10 * f 1 - 10000 * f 2 + 100000 * f 3 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 4 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 4 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega]

lemma a_2 : a 2 = 10100 := by rw [a_rec, a_0]; norm_num

lemma gf : mk (fun n => (a n : ℤ)) * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) =
    (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) := by
  ext n
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℤ) *
      coeff j (mk (fun n => (a n : ℤ))))]
  simp only [coeff_mk]
  by_cases hn : 3 ≤ n
  · rw [sum_d (fun k => (a (n - k) : ℤ)) n hn]
    have hr := recN n (by omega)
    have hz : coeff n (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) = 0 := by
      rw [ncoeff]
      simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega]
    rw [hz, Nat.sub_zero]
    linarith
  · have hn' : n ≤ 2 := by omega
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, ncoeff, a_0, a_1, a_2]
end A266844Aux

open A266844Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266844.main :=
  ⟨fun n => (closed n).1, recN, gf⟩
