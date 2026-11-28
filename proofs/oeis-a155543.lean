import OMAStatements.S_oeis_a155543
import Mathlib

/-!
(1-2x)/(1-4x) = 1 + Sum_{n>=1} 2*4^(n-1) x^n, so a(0) = 2 and a(n) = 4^n for n >= 1.
By the lifting-the-exponent lemma, v2(3^k - 1) = v2(k) + 2 for even k, and 3^k - 1 = 2 mod 4
for odd k. Hence the least k > 0 with 2^(2n+2) | 3^k - 1 is 2 for n = 0 and 2^(2n) = 4^n
for n >= 1.
-/

namespace R155543
open OMA.S_oeis_a155543 PowerSeries

theorem ser : ((1 - 2 * X : PowerSeries ℚ) * (1 - 4 * X)⁻¹) =
    mk (fun n => if n = 0 then (1 : ℚ) else 2 * 4 ^ (n - 1)) := by
  symm
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  rw [show (1 - 4 * X : ℚ⟦X⟧) = 1 - C 4 * X ^ 1 by simp only [map_ofNat]; ring,
    show (1 - 2 * X : ℚ⟦X⟧) = 1 - C 2 * X ^ 1 by simp only [map_ofNat]; ring,
    show ∀ p : ℚ⟦X⟧, p * (1 - C 4 * X ^ 1) = p - C 4 * (p * X ^ 1) from fun p => by ring]
  ext n
  simp only [map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
  rcases n with _ | _ | n <;> simp <;> ring

theorem v2 (k : ℕ) (hk : 0 < k) (he : Even k) : padicValNat 2 (3 ^ k - 1) = padicValNat 2 k + 2 := by
  have h := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by decide) (by decide)
    hk.ne' he
  rw [one_pow] at h
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    rw [show 3 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h2 : padicValNat 2 (3 - 1) = 1 := by
    rw [show 3 - 1 = 2 by norm_num]
    exact padicValNat_self
  omega

theorem odd_case (k : ℕ) (ho : ¬ Even k) : ¬ 4 ∣ 3 ^ k - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := by
    rcases Nat.even_or_odd k with h | ⟨j, hj⟩
    · exact absurd h ho
    · exact ⟨j, hj⟩
  have h3 : 3 ^ (2 * j + 1) % 4 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 3 ^ (2 * j + 1) = t at h3 ⊢
  omega

theorem A_eq (m k : ℕ) (hmem : 0 < k ∧ 2 ^ m ∣ 3 ^ k - 1)
    (hlow : ∀ j, 0 < j → 2 ^ m ∣ 3 ^ j - 1 → k ≤ j) : A090129 m = k := by
  unfold A090129
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · exact le_csInf ⟨k, hmem⟩ (fun j hj => hlow j hj.1 hj.2)

theorem A0 : A090129 (2 * 0 + 2) = 2 := by
  apply A_eq
  · norm_num
  · intro j hj hd
    by_contra h
    have : j = 1 := by omega
    subst this
    norm_num at hd

theorem Ai (i : ℕ) : A090129 (2 * (i + 1) + 2) = 4 ^ (i + 1) := by
  have hK : (4 : ℕ) ^ (i + 1) = 2 ^ (2 * (i + 1)) := by rw [pow_mul]; norm_num
  apply A_eq
  · refine ⟨by positivity, ?_⟩
    have hKpos : 0 < 4 ^ (i + 1) := by positivity
    have hev : Even (4 ^ (i + 1)) := Nat.even_pow.mpr ⟨by decide, by omega⟩
    have hne : 3 ^ (4 ^ (i + 1)) - 1 ≠ 0 := by
      have := Nat.one_lt_pow hKpos.ne' (show 1 < 3 by norm_num)
      omega
    rw [padicValNat_dvd_iff_le hne, v2 _ hKpos hev, hK, padicValNat.prime_pow]
  · intro j hj hd
    have h4 : 4 ∣ 3 ^ j - 1 := by
      refine dvd_trans ?_ hd
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have hev : Even j := by
      by_contra ho
      exact odd_case j ho h4
    have hne : 3 ^ j - 1 ≠ 0 := by
      have := Nat.one_lt_pow hj.ne' (show 1 < 3 by norm_num)
      omega
    rw [padicValNat_dvd_iff_le hne, v2 j hj hev] at hd
    have hdj : 2 ^ (2 * (i + 1)) ∣ j := (padicValNat_dvd_iff_le hj.ne').mpr (by omega)
    rw [hK]
    exact Nat.le_of_dvd hj hdj

theorem main' (n : ℕ) : a n = (A090129 (2 * n + 2) : ℚ) := by
  unfold a A081294
  rw [ser, coeff_mk]
  rcases n with _ | i
  · rw [A0]
    norm_num
  · rw [Ai i, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    push_cast
    ring

end R155543

theorem OMA.solution : type_of% @OMA.S_oeis_a155543.main := by
  intro n
  exact R155543.main' n
