import OMAStatements.S_oeis_a000254
import Mathlib
open OMA.S_oeis_a000254

lemma a_succ' (n : ℕ) : a (n+1) = (n+1) * a n + n.factorial := rfl

lemma a_le_succ (n : ℕ) : a n ≤ a (n+1) := by
  rw [a_succ']
  exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))

lemma a_pos (n : ℕ) : 0 < a (n+1) := by
  rw [a_succ']; have := Nat.factorial_pos n; omega

lemma cast_a1 (k : ℕ) : ((a (k+1) : ℕ) : ZMod (k+1)) = (k.factorial : ZMod (k+1)) := by
  have h : ((k : ZMod (k+1)) + 1) = 0 := ZMod.natCast_self' k
  rw [a_succ']; push_cast
  linear_combination ((a k : ℕ) : ZMod (k+1)) * h

lemma cast_a2 (k : ℕ) : ((a (k+2) : ℕ) : ZMod (k+1)) = (k.factorial : ZMod (k+1)) := by
  have h : ((k : ZMod (k+1)) + 1) = 0 := ZMod.natCast_self' k
  have h1 := cast_a1 k
  rw [a_succ' (k+1), Nat.factorial_succ]; push_cast; rw [h1]
  linear_combination (2 * (k.factorial : ZMod (k+1))) * h

lemma mul_dvd_fact {x y m : ℕ} (hx : 0 < x) (hxy : x < y) (hym : y ≤ m) :
    x * y ∣ m.factorial := by
  have h1 : y.factorial ∣ m.factorial := Nat.factorial_dvd_factorial hym
  have h2 : x ∣ (y-1).factorial := Nat.dvd_factorial hx (by omega)
  have h3 : y * (y-1).factorial = y.factorial := Nat.mul_factorial_pred (by omega)
  rw [← h3] at h1
  exact dvd_trans (by rw [mul_comm]; exact Nat.mul_dvd_mul_left y h2) h1

lemma comp_dvd (n : ℕ) (h2 : 2 ≤ n) (hp : ¬ n.Prime) (h4 : n ≠ 4) :
    n ∣ (n-1).factorial := by
  have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨q, hq⟩ := Nat.minFac_dvd n
  have hpq : n.minFac ≤ q := by
    have hq0 : q ≠ 0 := by rintro rfl; omega
    have hq1 : q ≠ 1 := by
      rintro rfl; rw [mul_one] at hq; rw [← hq] at hpp; exact hp hpp
    exact Nat.minFac_le_of_dvd (by omega) ⟨n.minFac, by rw [mul_comm]; exact hq⟩
  generalize n.minFac = p at hpp hq hpq
  have hp2 := hpp.two_le
  subst hq
  rcases lt_or_eq_of_le hpq with hlt | heq
  · have : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp2
    exact mul_dvd_fact (by omega) hlt (by omega)
  · subst heq
    have h3 : 3 ≤ p := by
      by_contra hc
      have : p = 2 := by omega
      subst this; exact h4 rfl
    have hd : p * (2 * p) ∣ (p * p - 1).factorial :=
      mul_dvd_fact (by omega) (by omega)
        (by have : 3 * p ≤ p * p := Nat.mul_le_mul_right p h3; omega)
    exact dvd_trans (Nat.mul_dvd_mul_left _ (Dvd.intro_left 2 rfl)) hd

lemma comp_dvd_sq (n : ℕ) (h2 : 2 ≤ n) (hp : ¬ n.Prime) :
    n ∣ (n-1).factorial ^ 2 := by
  by_cases h4 : n = 4
  · subst h4; decide
  · exact dvd_pow (comp_dvd n h2 hp h4) (by norm_num)

lemma wilson (k : ℕ) (hp : (k+1).Prime) : ((k.factorial : ℕ) : ZMod (k+1)) = -1 := by
  have := Fact.mk hp
  have := ZMod.wilsons_lemma (p := k+1)
  simpa using this

theorem OMA.solution : type_of% @OMA.S_oeis_a000254.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn h4
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hA := cast_a1 k
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have hk : ((k : ℕ) : ZMod (k+1)) = -1 := by
        linear_combination (ZMod.natCast_self' k)
      rw [wilson k hp, ← hk] at hA
      rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mp hA, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hd := comp_dvd (k+1) hn hp h4
      simp only [Nat.add_sub_cancel] at hd
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd] at hA
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hA)
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hle : a (k+1) ^ 2 ≤ a (k+1+1) ^ 2 := Nat.pow_le_pow_left (a_le_succ _) 2
    have hAe : ((a (k+1) : ℕ) : ℤ) = (k+1) * (a k : ℤ) + (k.factorial : ℤ) := by
      rw [a_succ']; push_cast; ring
    have hCe : ((a (k+1+1) : ℕ) : ℤ) = (k+2) * (a (k+1) : ℤ) + (k+1) * (k.factorial : ℤ) := by
      rw [a_succ' (k+1), Nat.factorial_succ]; push_cast; ring
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have hw := wilson k hp
      have hd : ((k+1 : ℕ) : ℤ) ∣ (k.factorial : ℤ) + 1 := by
        have : (((k.factorial + 1 : ℕ)) : ZMod (k+1)) = 0 := by
          push_cast; rw [hw]; ring
        exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mp this
      obtain ⟨u, hu⟩ := hd
      apply Nat.modEq_iff_dvd.mpr
      push_cast [Nat.cast_sub hle]
      rw [hCe, hAe]
      push_cast at hu
      refine ⟨-(((k+1) * (a k : ℤ) + (k.factorial : ℤ)) ^ 2 + 2 * (k+1) * (a k : ℤ) ^ 2
        + 6 * (a k : ℤ) * (k.factorial : ℤ)
        + 2 * ((k+1) * (a k : ℤ) + (k.factorial : ℤ)) * (k.factorial : ℤ)
        + (k.factorial : ℤ) ^ 2) - 4 * ((k.factorial : ℤ) - 1) * u, ?_⟩
      linear_combination (-4 * ((k:ℤ)+1) * ((k.factorial : ℤ) - 1)) * hu
    · have hd := comp_dvd_sq (k+1) (by omega) hp
      simp only [Nat.add_sub_cancel] at hd
      obtain ⟨v, hv⟩ := hd
      apply Nat.mod_eq_zero_of_dvd
      apply Int.natCast_dvd_natCast.mp
      push_cast [Nat.cast_sub hle]
      rw [hCe, hAe]
      have hv' : (k.factorial : ℤ) ^ 2 = ((k:ℤ)+1) * (v : ℤ) := by exact_mod_cast hv
      refine ⟨(((k+1) * (a k : ℤ) + (k.factorial : ℤ)) ^ 2 + 2 * (k+1) * (a k : ℤ) ^ 2
        + 6 * (a k : ℤ) * (k.factorial : ℤ)
        + 2 * ((k+1) * (a k : ℤ) + (k.factorial : ℤ)) * (k.factorial : ℤ)
        + (k.factorial : ℤ) ^ 2) + 4 * v, ?_⟩
      linear_combination (4 * ((k:ℤ)+1)) * hv'
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hle : a (k+1) ^ 2 ≤ a (k+1+1) ^ 3 :=
      le_trans (Nat.pow_le_pow_left (a_le_succ _) 2)
        (Nat.pow_le_pow_right (a_pos _) (by norm_num))
    have hA := cast_a1 k
    have hC := cast_a2 k
    have hD : ((a (k+1+1) ^ 3 - a (k+1) ^ 2 : ℕ) : ZMod (k+1))
        = (k.factorial : ZMod (k+1)) ^ 3 - (k.factorial : ZMod (k+1)) ^ 2 := by
      push_cast [Nat.cast_sub hle]; rw [hA, hC]
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [wilson k hp] at hD
      have hk : ((k - 1 : ℕ) : ZMod (k+1)) = -1 - 1 := by
        push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
        linear_combination (ZMod.natCast_self' k)
      have : ((a (k+1+1) ^ 3 - a (k+1) ^ 2 : ℕ) : ZMod (k+1)) = ((k - 1 : ℕ) : ZMod (k+1)) := by
        rw [hD, hk]; ring
      rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mp this, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hd := comp_dvd_sq (k+1) (by omega) hp
      simp only [Nat.add_sub_cancel] at hd
      have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      push_cast at h0
      apply Nat.mod_eq_zero_of_dvd
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [hD]
      linear_combination ((k.factorial : ZMod (k+1)) - 1) * h0
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hA := cast_a1 k
    have hC := cast_a2 k
    have hD : ((a (k+1) ^ 2 + a (k+1+1) ^ 2 : ℕ) : ZMod (k+1))
        = 2 * (k.factorial : ZMod (k+1)) ^ 2 := by
      push_cast; rw [hA, hC]; ring
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [wilson k hp] at hD
      have : ((a (k+1) ^ 2 + a (k+1+1) ^ 2 : ℕ) : ZMod (k+1)) = ((2 : ℕ) : ZMod (k+1)) := by
        rw [hD]; push_cast; ring
      rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mp this, Nat.mod_eq_of_lt (by omega)]
    · have hd := comp_dvd_sq (k+1) (by omega) hp
      simp only [Nat.add_sub_cancel] at hd
      have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      push_cast at h0
      apply Nat.mod_eq_zero_of_dvd
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [hD]
      linear_combination 2 * h0
