import OMAStatements.S_oeis_a193447
import Mathlib

/-!
# A193447: k(k−1) ∣ (k−2)! + k − 1 exactly for primes k ≥ 7

A composite c ≥ 6 divides (c−2)!: write c = ab with a = minFac c ≤ b; if a < b then a < b ≤ c − 2,
and if c = a² then a ≥ 3 and a < 2a ≤ c − 2. So for composite k, (k−2)! + k − 1 ≡ k − 1 (mod k) and k
does not divide it. For prime k, Wilson's theorem gives (k−2)! ≡ 1 (mod k), so k divides
(k−2)! + k − 1; and k − 1 ≥ 6 is composite, so k − 1 divides (k−3)! and hence (k−2)!. As k and k − 1
are coprime, k(k−1) divides the sum.
-/

namespace PA193447

theorem mul_dvd_fact (a b : ℕ) (ha : 0 < a) (hab : a < b) : a * b ∣ b.factorial := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Nat.factorial_succ, mul_comm (c + 1)]
  exact Nat.mul_dvd_mul (Nat.dvd_factorial ha (by omega)) (dvd_refl _)

theorem comp_dvd (c : ℕ) (hc : 6 ≤ c) (hnp : ¬ c.Prime) : c ∣ (c - 2).factorial := by
  have ha : c.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : c.minFac ^ 2 ≤ c := Nat.minFac_sq_le_self (by omega) hnp
  obtain ⟨b, hb⟩ := Nat.minFac_dvd c
  generalize c.minFac = a at ha hsq hb
  have ha2 := ha.two_le
  have hab : a ≤ b := by
    by_contra h
    have : a * b < a * a := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    nlinarith
  rcases Nat.lt_or_ge a b with hlt | hge
  · have h2b : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
    have hb2 : b ≤ c - 2 := by omega
    have := (mul_dvd_fact a b (by omega) hlt).trans (Nat.factorial_dvd_factorial hb2)
    rwa [← hb] at this
  · have hbe : b = a := le_antisymm hge hab
    rw [hbe] at hb
    have ha3 : 3 ≤ a := by
      by_contra h
      have h2 : a = 2 := by omega
      rw [h2] at hb
      omega
    have h4 : 2 * a + 2 ≤ a * a := by nlinarith
    have h2a : 2 * a ≤ c - 2 := by omega
    have h1 : a * (2 * a) ∣ (2 * a).factorial := mul_dvd_fact a (2 * a) (by omega) (by omega)
    have h2 : c ∣ a * (2 * a) := ⟨2, by rw [hb]; ring⟩
    exact h2.trans (h1.trans (Nat.factorial_dvd_factorial h2a))

end PA193447

theorem OMA.solution : type_of% @OMA.S_oeis_a193447.main := by
  intro k hk
  constructor
  · intro hd
    by_contra hnp
    have hk' : k ∣ (k - 2).factorial + (k - 1) := (Dvd.intro _ rfl).trans hd
    have h1 := PA193447.comp_dvd k (by omega) hnp
    have h2 : k ∣ k - 1 := (Nat.dvd_add_right h1).mp hk'
    have := Nat.le_of_dvd (by omega) h2
    omega
  · intro hp
    have : Fact k.Prime := ⟨hp⟩
    have hk1 : k - 1 ∣ (k - 2).factorial + (k - 1) := by
      have hnp : ¬ (k - 1).Prime := by
        intro h
        rcases hp.eq_two_or_odd with h2 | h2
        · omega
        · rcases h.eq_two_or_odd with h3 | h3 <;> omega
      have := PA193447.comp_dvd (k - 1) (by omega) hnp
      rw [show k - 1 - 2 = k - 3 by omega] at this
      have h3 : (k - 3).factorial ∣ (k - 2).factorial := Nat.factorial_dvd_factorial (by omega)
      exact dvd_add (this.trans h3) (dvd_refl _)
    have hkk : k ∣ (k - 2).factorial + (k - 1) := by
      rw [← ZMod.natCast_eq_zero_iff]
      have hw := ZMod.wilsons_lemma (p := k)
      rw [show k - 1 = (k - 2) + 1 by omega, Nat.factorial_succ] at hw
      push_cast at hw ⊢
      have hk2 : ((k - 2 : ℕ) : ZMod k) + 1 = -1 := by
        have : ((k - 2 + 1 + 1 : ℕ) : ZMod k) = 0 := by
          rw [show k - 2 + 1 + 1 = k by omega, ZMod.natCast_self]
        push_cast at this
        linear_combination this
      have hk3 : ((k - 1 : ℕ) : ZMod k) = -1 := by
        rw [show k - 1 = (k - 2) + 1 by omega]; push_cast; exact hk2
      rw [hk2] at hw
      linear_combination -hw + hk3
    have hcop : Nat.Coprime k (k - 1) := by
      have : Nat.Coprime (k - 1 + 1) (k - 1) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
      rwa [show k - 1 + 1 = k by omega] at this
    exact hcop.mul_dvd_of_dvd_of_dvd hkk hk1
