import OMAStatements.S_oeis_a088039
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: k = 2^n + 1 works with b = 2. Conversely if b^n divides k^3 - 1 = (k-1)(k^2+k+1)
-- with 1 < k <= 2^n and n >= 3, take a prime p dividing b: p = 2 forces 2^n | k - 1
-- (k^2+k+1 is odd); p = 3 forces 3^(n-1) | k - 1; p >= 5 divides only one factor, which
-- then is >= 5^n > 4^n + 2^n + 1. a(1) = 2 (b = 7), a(2) = 4 (b = 3), a(0) = 0 give the g.f.

namespace OMA.P_oeis_a088039
open OMA.S_oeis_a088039

lemma cube_sub (j : ℕ) : (j + 1) ^ 3 - 1 = j * ((j + 1) ^ 2 + (j + 1) + 1) := by
  have : (j + 1) ^ 3 = j * ((j + 1) ^ 2 + (j + 1) + 1) + 1 := by ring
  omega

lemma dvd_of_modEq {k m n : ℕ} (hk : 1 ≤ k) (h : m ^ n ∣ k ^ 3 - 1) :
    m ^ n ∣ (k - 1) * (k ^ 2 + k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [cube_sub] at h
  simpa using h

lemma pow_three_ge (n : ℕ) (hn : 3 ≤ n) : 2 ^ n ≤ 3 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ, pow_succ]
    omega

lemma five_bound (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ 2 ^ n) : k ^ 2 + k + 1 < 5 ^ n := by
  have h1 : k ^ 2 ≤ 4 ^ n := by
    calc k ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hk 2
      _ = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : ∀ n, 2 ≤ n → 4 ^ n + 2 ^ n + 1 < 5 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ, pow_succ, pow_succ]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
  have := h2 n hn
  omega

lemma lower (n k m : ℕ) (hn : 3 ≤ n) (hk : 1 < k) (hm : 2 ≤ m) (h : m ^ n ∣ k ^ 3 - 1) :
    2 ^ n + 1 ≤ k := by
  have hd := dvd_of_modEq (by omega) h
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hpd : p ^ n ∣ (k - 1) * (k ^ 2 + k + 1) := (pow_dvd_pow_of_dvd hpm n).trans hd
  by_contra hlt
  push Not at hlt
  have hk1 : 0 < k - 1 := by omega
  -- k^2+k+1 is odd
  have hodd : ¬ 2 ∣ k ^ 2 + k + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have : (k ^ 2 + k) % 2 = 0 := by
      have : k ^ 2 + k = k * (k + 1) := by ring
      rw [this, Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]
    omega
  by_cases h2 : p = 2
  · subst h2
    have hc : Nat.Coprime (2 ^ n) (k ^ 2 + k + 1) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have := hc.dvd_of_dvd_mul_right hpd
    have := Nat.le_of_dvd hk1 this
    omega
  by_cases h3 : p = 3
  · subst h3
    have h3d : 3 ∣ (k - 1) * (k ^ 2 + k + 1) :=
      (dvd_pow_self 3 (by omega)).trans hpd
    have h3k : 3 ∣ k - 1 := by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3d with h | h
      · exact h
      · have h0 : (k ^ 2 + k + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
        have hk3 : k % 3 = 1 := by
          rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with r | r | r
          · simp [Nat.add_mod, Nat.pow_mod, r] at h0
          · exact r
          · simp [Nat.add_mod, Nat.pow_mod, r] at h0
        omega
    obtain ⟨t, ht⟩ := h3k
    have hu : k ^ 2 + k + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) := by
      have hk' : k = 3 * t + 1 := by omega
      rw [hk']; ring
    rw [ht, hu, show 3 * t * (3 * (3 * t ^ 2 + 3 * t + 1)) = 9 * t * (3 * t ^ 2 + 3 * t + 1) by ring] at hpd
    have hcop : Nat.Coprime (3 ^ n) (3 * t ^ 2 + 3 * t + 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    have h9 : 3 ^ n ∣ 9 * t := hcop.dvd_of_dvd_mul_right hpd
    rw [show n = (n - 2) + 2 by omega, pow_add, show (3:ℕ) ^ 2 = 9 by norm_num, mul_comm] at h9
    have ht' : 3 ^ (n - 2) ∣ t := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
    have htpos : 0 < t := by omega
    have := Nat.le_of_dvd htpos ht'
    have hpw := pow_three_ge n hn
    have : 3 ^ (n - 1) = 3 * 3 ^ (n - 2) := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
    omega
  -- p ≥ 5
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h h2
    · exact absurd h h3
    · exfalso; subst h; exact absurd hp (by decide)
    · exact h
  have hnot : ¬ (p ∣ k - 1 ∧ p ∣ k ^ 2 + k + 1) := by
    rintro ⟨h1, h2'⟩
    obtain ⟨t, ht⟩ := h1
    have hk' : k = p * t + 1 := by omega
    have : k ^ 2 + k + 1 = p * (p * t ^ 2 + 3 * t) + 3 := by rw [hk']; ring
    rw [this] at h2'
    have : p ∣ 3 := (Nat.dvd_add_right (dvd_mul_right p _)).mp h2'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcases : p ^ n ∣ k - 1 ∨ p ^ n ∣ k ^ 2 + k + 1 := by
    by_cases hp1 : p ∣ k - 1
    · left
      have hc : Nat.Coprime (p ^ n) (k ^ 2 + k + 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hnot ⟨hp1, h⟩))
      exact hc.dvd_of_dvd_mul_right hpd
    · right
      have hc : Nat.Coprime (p ^ n) (k - 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp1)
      exact hc.dvd_of_dvd_mul_left hpd
  have h5n : 5 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp5 n
  have h25 : 2 ^ n < 5 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  rcases hcases with h | h
  · have := Nat.le_of_dvd hk1 h
    omega
  · have := Nat.le_of_dvd (by positivity) h
    have := five_bound n k (by omega) (by omega)
    omega

lemma mem (n : ℕ) (_hn : 1 ≤ n) : 2 ^ n + 1 ∈ candidates n := by
  refine ⟨by have := Nat.one_le_two_pow (n := n); omega, 2, by norm_num, ?_⟩
  rw [cube_sub]
  exact Dvd.dvd.mul_right (dvd_refl _) _

lemma a_eq (n : ℕ) (hn : n ≠ 0) : a n = sInf (candidates n) := by
  simp [a, hn]

lemma closed (n : ℕ) (hn : 2 < n) : a n = 2 ^ n + 1 := by
  rw [a_eq n (by omega)]
  apply le_antisymm
  · exact Nat.sInf_le (mem n (by omega))
  · apply le_csInf ⟨_, mem n (by omega)⟩
    rintro k ⟨hk, m, hm, h⟩
    exact lower n k m hn hk hm h

lemma a1 : a 1 = 2 := by
  rw [a_eq 1 (by norm_num)]
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨by norm_num, 7, by norm_num, by decide⟩
  · apply le_csInf ⟨_, mem 1 le_rfl⟩
    rintro k ⟨hk, -⟩; omega

lemma a2 : a 2 = 4 := by
  rw [a_eq 2 (by norm_num)]
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨by norm_num, 3, by norm_num, by decide⟩
  · apply le_csInf ⟨_, mem 2 (by norm_num)⟩
    rintro k ⟨hk, m, hm, h⟩
    by_contra hlt
    push Not at hlt
    interval_cases k
    · norm_num at h
      have := Nat.le_of_dvd (by norm_num) h
      have : m ≤ 2 := by nlinarith
      interval_cases m; norm_num at h
    · norm_num at h
      have := Nat.le_of_dvd (by norm_num) h
      have : m ≤ 5 := by nlinarith
      interval_cases m <;> norm_num at h

lemma a0 : a 0 = 0 := by simp [a]

open PowerSeries in
theorem main' :
    (∀ n : ℕ, 2 < n → a n = 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n-1) : ℤ) - 2 * (a (n-2) : ℤ)) ∧
    ((1 - X) * (1 - 2 * X) * mk (fun n => (a n : ℤ)) =
      2 * X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4) := by
  refine ⟨closed, ?_, ?_⟩
  · intro n hn
    rw [closed n (by omega), closed (n - 1) (by omega), closed (n - 2) (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    simp only [show j + 2 - 1 = j + 1 by omega, Nat.add_sub_cancel]
    push_cast; ring
  · set A := mk (fun n => (a n : ℤ)) with hA
    have e1 : (1 - X) * (1 - 2 * X) * A = A - C (3:ℤ) * (A * X ^ 1) + C (2:ℤ) * (A * X ^ 2) := by
      simp only [map_ofNat]; ring
    have e2 : (2 * X - 2 * X ^ 2 + X ^ 3 - 2 * X ^ 4 : PowerSeries ℤ) =
        C (2:ℤ) * X ^ 1 - C (2:ℤ) * X ^ 2 + X ^ 3 - C (2:ℤ) * X ^ 4 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk, coeff_C]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h | h | h | h
    · subst h; simp [a0]
    · subst h; simp [a0, a1]
    · subst h; simp [a0, a1, a2]
    · subst h; simp [a1, a2, closed 3 (by norm_num)]
    · subst h; simp [a2, closed 3 (by norm_num), closed 4 (by norm_num)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
      simp only [show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega, if_true,
        show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
        show ¬ (j + 5 = 3) by omega]
      rw [closed (j + 5) (by omega), closed (j + 4) (by omega), closed (j + 3) (by omega)]
      push_cast
      ring

end OMA.P_oeis_a088039

theorem OMA.solution : type_of% @OMA.S_oeis_a088039.main := OMA.P_oeis_a088039.main'
