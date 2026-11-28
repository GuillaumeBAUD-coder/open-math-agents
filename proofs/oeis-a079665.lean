import OMAStatements.S_oeis_a079665
import Mathlib

/-!
# OEIS A079665: when does `b^r + 1` divide `b^s + 1`?

For `b ≥ 2` and `1 ≤ r < s`:  `b^r + 1 ∣ b^s + 1` iff `s = r m` with `m` odd.

* If `s = r m` with `m` odd, then `x + 1 ∣ x^m + 1` with `x = b^r`.
* Conversely write `s = r q + ρ` with `ρ < r` and put `N = b^r + 1`, `x = b^r`.
  - If `q` is even, `N ∣ x^q - 1`, so `N ∣ b^ρ + 1`; but `0 < b^ρ + 1 < N`. Contradiction.
  - If `q` is odd, `N ∣ x^q + 1`, so `N ∣ b^ρ - 1` with `0 ≤ b^ρ - 1 < N`; hence `b^ρ = 1`,
    `ρ = 0` and `s = r q`.

The right-hand side of the statement says the same thing: taking `s = k 2^t` with `k` odd, the
condition `r = 2^t u`, `u ∣ k` means `r ∣ s` with odd quotient, and then `2r < s`.
-/

namespace OMA.A079665

/-- The classical criterion. -/
lemma dvd_iff (b r s : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) :
    (b ^ r + 1 ∣ b ^ s + 1) ↔ ∃ m, Odd m ∧ s = r * m := by
  constructor
  · intro h
    -- divide `s` by `r`
    obtain ⟨q, ρ, hρ, hs⟩ : ∃ q ρ, ρ < r ∧ s = r * q + ρ :=
      ⟨s / r, s % r, Nat.mod_lt _ (by omega), (Nat.div_add_mod s r).symm⟩
    have hZ : ((b : ℤ) ^ r + 1) ∣ (b : ℤ) ^ s + 1 := by exact_mod_cast h
    have hbZ : (2 : ℤ) ≤ b := by exact_mod_cast hb
    have hpow : (b : ℤ) ^ s = ((b : ℤ) ^ r) ^ q * (b : ℤ) ^ ρ := by rw [hs, pow_add, pow_mul]
    have hρlt : (b : ℤ) ^ ρ < (b : ℤ) ^ r := pow_lt_pow_right₀ (by linarith) hρ
    have hρpos : (1 : ℤ) ≤ (b : ℤ) ^ ρ := one_le_pow₀ (by linarith)
    rcases Nat.even_or_odd q with hq | hq
    · -- `q` even: impossible
      exfalso
      obtain ⟨j, rfl⟩ := hq
      have h1 : ((b : ℤ) ^ r + 1) ∣ ((b : ℤ) ^ r) ^ (j + j) - 1 := by
        have h2 : ((b : ℤ) ^ r) ^ 2 - 1 ∣ (((b : ℤ) ^ r) ^ 2) ^ j - 1 := by
          simpa using sub_dvd_pow_sub_pow (((b : ℤ) ^ r) ^ 2) 1 j
        have h3 : ((b : ℤ) ^ r + 1) ∣ ((b : ℤ) ^ r) ^ 2 - 1 := ⟨(b : ℤ) ^ r - 1, by ring⟩
        have e : ((b : ℤ) ^ r) ^ (j + j) = (((b : ℤ) ^ r) ^ 2) ^ j := by rw [← pow_mul]; ring_nf
        rw [e]
        exact h3.trans h2
      have h4 : ((b : ℤ) ^ r + 1) ∣ (b : ℤ) ^ ρ + 1 := by
        have e : (b : ℤ) ^ ρ + 1
            = ((b : ℤ) ^ s + 1) - (((b : ℤ) ^ r) ^ (j + j) - 1) * (b : ℤ) ^ ρ := by
          rw [hpow]; ring
        rw [e]
        exact dvd_sub hZ (Dvd.dvd.mul_right h1 _)
      have h5 := Int.le_of_dvd (by linarith) h4
      linarith
    · -- `q` odd: then `ρ = 0`
      have h1 : ((b : ℤ) ^ r + 1) ∣ ((b : ℤ) ^ r) ^ q + 1 := by
        simpa using Odd.add_dvd_pow_add_pow ((b : ℤ) ^ r) 1 hq
      have h4 : ((b : ℤ) ^ r + 1) ∣ (b : ℤ) ^ ρ - 1 := by
        have e : (b : ℤ) ^ ρ - 1
            = (((b : ℤ) ^ r) ^ q + 1) * (b : ℤ) ^ ρ - ((b : ℤ) ^ s + 1) := by
          rw [hpow]; ring
        rw [e]
        exact dvd_sub (Dvd.dvd.mul_right h1 _) hZ
      have h5 : (b : ℤ) ^ ρ - 1 = 0 := by
        by_contra hne
        have hpos : 0 < (b : ℤ) ^ ρ - 1 := lt_of_le_of_ne (by linarith) (Ne.symm hne)
        have := Int.le_of_dvd hpos h4
        linarith
      have hρ0 : ρ = 0 := by
        by_contra hne
        have : (b : ℤ) ^ 1 ≤ (b : ℤ) ^ ρ := pow_le_pow_right₀ (by linarith) (by omega)
        rw [pow_one] at this
        linarith
      exact ⟨q, hq, by rw [hs, hρ0, add_zero]⟩
  · rintro ⟨m, hm, rfl⟩
    have h1 : ((b : ℤ) ^ r + 1) ∣ ((b : ℤ) ^ r) ^ m + 1 := by
      simpa using Odd.add_dvd_pow_add_pow ((b : ℤ) ^ r) 1 hm
    rw [pow_mul]
    exact_mod_cast h1

end OMA.A079665

open OMA.A079665 in
theorem OMA.solution : type_of% @OMA.S_oeis_a079665.main := by
  intro b hb s r hr hrs
  rw [dvd_iff b r s hb hr]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨c, rfl⟩ := hm
    have hc : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · simp at hrs
      · exact h
    refine ⟨by nlinarith, fun _ => Dvd.intro _ rfl, ?_⟩
    intro k t hk hcop
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact ⟨r, by simp, by rw [pow_zero, mul_one] at hk; exact ⟨2 * c + 1, hk.symm⟩⟩
    · -- `2^t` is coprime to the odd factor, so it divides `r`
      have hcop2 : Nat.Coprime (2 ^ t) (2 * c + 1) :=
        Nat.Coprime.pow_left t (Nat.coprime_two_left.mpr ⟨c, rfl⟩)
      have hdvd : 2 ^ t ∣ r := by
        have : 2 ^ t ∣ r * (2 * c + 1) := ⟨k, by rw [hk]; ring⟩
        exact hcop2.dvd_of_dvd_mul_right this
      obtain ⟨u, rfl⟩ := hdvd
      refine ⟨u, rfl, ⟨2 * c + 1, ?_⟩⟩
      have h2 : 0 < 2 ^ t := by positivity
      have : 2 ^ t * k = 2 ^ t * (u * (2 * c + 1)) := by rw [← mul_assoc, hk]; ring
      exact Nat.eq_of_mul_eq_mul_left h2 this
  · rintro ⟨-, -, h3⟩
    -- use the odd part of `s`
    obtain ⟨t, k, hkodd, hs⟩ := Nat.exists_eq_two_pow_mul_odd (n := s) (by omega)
    have hcop : Nat.Coprime k (2 ^ t) :=
      Nat.Coprime.pow_right t (Nat.coprime_two_right.mpr hkodd)
    obtain ⟨u, hu, m, hm⟩ := h3 k t (by rw [hs]; ring) hcop
    refine ⟨m, ?_, by rw [hs, hu, hm]; ring⟩
    -- `m` divides the odd number `k`
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      obtain ⟨j, rfl⟩ := he
      obtain ⟨c, hc⟩ := hkodd
      rw [hm] at hc
      have : (u * (j + j)) % 2 = 0 := by
        rw [show u * (j + j) = 2 * (u * j) by ring]; simp
      omega
    · exact ho
