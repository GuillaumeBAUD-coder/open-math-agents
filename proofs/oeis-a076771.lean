import OMAStatements.S_oeis_a076771
import Mathlib

/-!
# A076771: no threshold beyond which every even number is represented

For a prime p, 2p is not a sum of two non-coprime odd composites a + b: g = gcd(a, b) > 1 is odd and
divides 2p, so g = p, and then a = p·x, b = p·y with x + y = 2 forces a = p, which is prime. Since
there are arbitrarily large primes, no N works (the argument noted in the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a076771.main := by
  rintro ⟨N, hN⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 3)
  have hrep := hN (2 * p) (by omega) (even_two_mul p)
  obtain ⟨a, b, ha, ha1, hap, hb, hb1, hbp, hab, hsum⟩ := hrep
  set g := Nat.gcd a b with hg
  have hg1 : g ≠ 1 := hab
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hg2p : g ∣ 2 * p := hsum ▸ dvd_add hga hgb
  have hgodd : ¬ 2 ∣ g := fun h2 => by
    have := h2.trans hga
    rcases ha with ⟨k, hk⟩
    omega
  have hgp : g ∣ p := by
    rcases (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hgodd)) hg2p) with h
    exact h
  rcases (Nat.dvd_prime hp).mp hgp with h | h
  · exact hg1 h
  · rw [h] at hga hgb
    obtain ⟨x, rfl⟩ := hga
    obtain ⟨y, rfl⟩ := hgb
    have hxy : x + y = 2 := by
      have : p * (x + y) = p * 2 := by rw [mul_add, ← hsum]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have hx : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp at ha1
      · exact hx
    have hy : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp at hb1
      · exact hy
    have : x = 1 := by omega
    subst this
    exact hap (by simpa using hp)
