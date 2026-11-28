import OMAStatements.S_oeis_a192031
import Mathlib


namespace OMAHelp192031
open PowerSeries OMA.S_oeis_a192031

lemma coeff_mk_mul_sum (f d : ℕ → ℚ) (K n : ℕ) :
    coeff n (mk f * ∑ k ∈ Finset.range K, C (d k) * X ^ k) =
      ∑ k ∈ Finset.range K, d k * (if k ≤ n then f (n - k) else 0) := by
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

lemma coeff_sum_C (c : ℕ → ℚ) (K n : ℕ) :
    coeff n (∑ k ∈ Finset.range K, C (c k) * X ^ k : ℚ⟦X⟧) = if n < K then c n else 0 := by
  simp [map_sum, coeff_C_mul, coeff_X_pow]

lemma a_big (m : ℕ) : a (m + 6) = row (4 + ((m / 4 : ℕ) : ℚ)) (m % 4) := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]
  simp

lemma quad (m : ℕ) : a (m + 18) - 3 * a (m + 14) + 3 * a (m + 10) - a (m + 6) = 0 := by
  have h1 : a (m + 18) = row (4 + ((m / 4 : ℕ) : ℚ) + 3) (m % 4) := by
    rw [show m + 18 = (m + 12) + 6 by omega, a_big, show (m + 12) / 4 = m / 4 + 3 by omega,
      show (m + 12) % 4 = m % 4 by omega]
    congr 1
    push_cast; ring
  have h2 : a (m + 14) = row (4 + ((m / 4 : ℕ) : ℚ) + 2) (m % 4) := by
    rw [show m + 14 = (m + 8) + 6 by omega, a_big, show (m + 8) / 4 = m / 4 + 2 by omega,
      show (m + 8) % 4 = m % 4 by omega]
    congr 1
    push_cast; ring
  have h3 : a (m + 10) = row (4 + ((m / 4 : ℕ) : ℚ) + 1) (m % 4) := by
    rw [show m + 10 = (m + 4) + 6 by omega, a_big, show (m + 4) / 4 = m / 4 + 1 by omega,
      show (m + 4) % 4 = m % 4 by omega]
    congr 1
    push_cast; ring
  rw [h1, h2, h3, a_big]
  generalize ((m / 4 : ℕ) : ℚ) = q
  have hj : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize m % 4 = j at hj ⊢
  interval_cases j <;> simp [row] <;> ring

def e (k : ℕ) : ℚ :=
  if k = 0 then 1 else if k = 4 then -3 else if k = 8 then 3 else if k = 12 then -1 else 0

def r (k : ℕ) : ℚ :=
  if k = 3 then 9 else if k = 4 then 9 else if k = 5 then 3 else if k = 6 then 12 else if k = 7 then -13 else if k = 8 then -19 else if k = 9 then -7 else if k = 10 then -21 else if k = 11 then 5 else if k = 12 then 18 else if k = 13 then 8 else if k = 14 then 9 else if k = 16 then -6 else if k = 17 then -3 else 0

def c (k : ℕ) : ℚ :=
  if k = 3 then 9 else if k = 5 then 3 else if k = 6 then 9 else if k = 7 then -22 else if k = 8 then 3 else if k = 9 then -10 else if k = 10 then -11 else if k = 11 then 16 else if k = 12 then 2 else if k = 13 then 6 else if k = 14 then 3 else if k = 15 then -3 else if k = 16 then -3 else 0

def d (k : ℕ) : ℚ :=
  if k = 0 then 1 else if k = 1 then -1 else if k = 2 then 1 else if k = 3 then -1 else if k = 4 then -2 else if k = 5 then 2 else if k = 6 then -2 else if k = 7 then 2 else if k = 8 then 1 else if k = 9 then -1 else if k = 10 then 1 else if k = 11 then -1 else 0

lemma hE : ((1 - X ^ 4) ^ 3 : ℚ⟦X⟧) = ∑ k ∈ Finset.range 13, C (e k) * X ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e]
  norm_num
  repeat rw [map_ofNat C]
  ring

lemma hD : ((1-X)^3 * (1+X)^2 * (1+X^2)^3 : ℚ⟦X⟧) = ∑ k ∈ Finset.range 12, C (d k) * X ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, d]
  norm_num
  repeat rw [map_ofNat C]
  ring

lemma hRc : (X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) : ℚ⟦X⟧) =
      ∑ k ∈ Finset.range 17, C (c k) * X ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c]
  norm_num
  repeat rw [map_ofNat C]
  ring

lemma hRr : (X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) * (1 + X) : ℚ⟦X⟧) =
      ∑ k ∈ Finset.range 18, C (r k) * X ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r]
  norm_num
  repeat rw [map_ofNat C]
  ring

lemma small (n : ℕ) (hn : n < 18) :
    ∑ k ∈ Finset.range 13, e k * (if k ≤ n then a (n - k) else 0) = r n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e]
  interval_cases n <;> norm_num [a, r, row]

lemma part1 : mk a * ((1-X)^3 * (1+X)^2 * (1+X^2)^3) =
      X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) := by
  have h1 : (1 + X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp at this
  refine mul_right_cancel₀ h1 ?_
  rw [hRr, show mk a * ((1-X)^3 * (1+X)^2 * (1+X^2)^3) * (1 + X) = mk a * (1 - X ^ 4) ^ 3 by ring,
    hE]
  ext n
  rw [coeff_mk_mul_sum, coeff_sum_C]
  by_cases hn : n < 18
  · rw [if_pos hn]
    exact small n hn
  · rw [if_neg hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
    have := quad m
    simp [Finset.sum_range_succ, e]
    linarith

end OMAHelp192031

theorem OMA.solution : type_of% @OMA.S_oeis_a192031.main := by
  refine ⟨OMAHelp192031.part1, fun n hn => ?_⟩
  have h := congrArg (PowerSeries.coeff n) OMAHelp192031.part1
  rw [OMAHelp192031.hD, OMAHelp192031.hRc, OMAHelp192031.coeff_mk_mul_sum,
    OMAHelp192031.coeff_sum_C, if_neg (by omega)] at h
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega)])] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, OMAHelp192031.d] at h
  norm_num at h
  linarith
