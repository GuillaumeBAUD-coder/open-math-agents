import OMAReductions.R_mo_181683_R1
import Mathlib

namespace QuarticFactors

/-- Each factor smaller than the square must share a prime with its base. -/
private theorem shared_prime {r a b : ℕ} (hb : 0 < b) (hb' : b < r ^ 2)
    (h : r ^ 2 ∣ a * b) : ∃ p, p.Prime ∧ p ∣ r ∧ p ∣ a := by
  have hnc : ¬ r.Coprime a := by
    intro hc
    have hdiv : r ^ 2 ∣ b := (hc.pow_left 2).dvd_of_dvd_mul_left h
    exact (Nat.not_le_of_lt hb') (Nat.le_of_dvd hb hdiv)
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hnc
  exact ⟨p, hp, hpg.trans (Nat.gcd_dvd_left _ _), hpg.trans (Nat.gcd_dvd_right _ _)⟩

/-- Two consecutive factors force the two obstructing primes to be distinct. -/
private theorem consecutive_factors {r u : ℕ} (hu : 0 < u) (hv : u + 1 < r ^ 2)
    (h : r ^ 2 ∣ u * (u + 1)) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ r ∧ q ∣ r ∧ p ∣ u ∧ q ∣ u + 1 := by
  obtain ⟨p, hp, hpr, hpu⟩ := shared_prime (by omega : 0 < u + 1) hv h
  have hrev : r ^ 2 ∣ (u + 1) * u := by rwa [mul_comm]
  obtain ⟨q, hq, hqr, hqv⟩ := shared_prime hu (by omega : u < r ^ 2) hrev
  have hne : p ≠ q := by
    rintro rfl
    have : p ∣ 1 := (Nat.dvd_add_iff_right hpu).mpr hqv
    exact hp.not_dvd_one this
  exact ⟨p, q, hp, hq, hne, hpr, hqr, hpu, hqv⟩

/-- A multiple of four cannot be one less than the fourth power of an even number. -/
private theorem odd_difference {r s d : ℕ}
    (h : 4 * (r : ℤ) ^ 2 * s ∣ (d : ℤ) ^ 4 - 1) : Odd d := by
  by_contra hn
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hn
  obtain ⟨t, ht⟩ := h
  have hk' : (d : ℤ) = k + (k : ℤ) := by exact_mod_cast hk
  have he : (2 : ℤ) ∣ (d : ℤ) ^ 4 := by
    exact ⟨8 * (k : ℤ) ^ 4, by rw [hk']; ring⟩
  have ho : (2 : ℤ) ∣ (d : ℤ) ^ 4 - 1 := by
    exact ⟨2 * (r : ℤ) ^ 2 * s * t, by rw [ht]; ring⟩
  omega

/-- Cancel the four supplied by the two even factors of the quartic. -/
private theorem cancel_four {r s d u : ℕ} (hu : d ^ 2 = 2 * u + 1)
    (h : 4 * (r : ℤ) ^ 2 * s ∣ (d : ℤ) ^ 4 - 1) :
    r ^ 2 ∣ u * (u + 1) := by
  obtain ⟨t, ht⟩ := h
  have hcast : (d : ℤ) ^ 2 = 2 * u + 1 := by exact_mod_cast hu
  have hfour : (d : ℤ) ^ 4 - 1 = 4 * (u : ℤ) * (u + 1) := by
    rw [show (d : ℤ) ^ 4 = ((d : ℤ) ^ 2) ^ 2 by ring, hcast]
    ring
  rw [hfour] at ht
  have hint : (r : ℤ) ^ 2 ∣ (u : ℤ) * (u + 1) := by
    refine ⟨(s : ℤ) * t, ?_⟩
    linarith only [ht]
  exact_mod_cast hint

theorem split {r s : ℕ} (hs : 1 ≤ s) (hsr : s < r) (hnt : r - s ≠ 1)
    (h : 4 * (r : ℤ) ^ 2 * s ∣ ((r : ℤ) - s) ^ 4 - 1) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ r ∧ q ∣ r ∧
      p ∣ ((r - s) ^ 2 / 2) ∧ q ∣ ((r - s) ^ 2 / 2 + 1) := by
  let d := r - s
  have hd : 1 < d := by dsimp [d]; omega
  have hdr : d < r := by dsimp [d]; omega
  have hcast : (d : ℤ) = (r : ℤ) - s := Nat.cast_sub hsr.le
  have hh : 4 * (r : ℤ) ^ 2 * s ∣ (d : ℤ) ^ 4 - 1 := by rwa [hcast]
  obtain ⟨k, hk⟩ := odd_difference hh
  let u := d ^ 2 / 2
  have heq : d ^ 2 = 2 * u + 1 := by
    have : d ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
    dsimp [u]
    omega
  have hsquare : 1 < d ^ 2 := by nlinarith
  have hlt : d ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hdr (by decide)
  have hu : 0 < u := by omega
  have hv : u + 1 < r ^ 2 := by omega
  exact consecutive_factors hu hv (cancel_four heq hh)

end QuarticFactors

theorem OMA.solution : OMA.R_mo_181683_R1.H1 := by
  intro r s
  exact QuarticFactors.split
