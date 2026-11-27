import OMAReductions.R_OeisA108129_conjecture_R1
import Mathlib

-- Step OeisA108129.conjecture.R1.H1: hypothesis H1 of reduction OeisA108129.conjecture.R1
-- Credit: @ivillar
-- H1 := OeisA108129.a 254602 = -1
--
-- 509203 is a Riesel number: the covering set {3, 5, 7, 13, 17, 241} (all dividing 2^24 - 1)
-- shows that 509203 * 2^m - 1 always has a factor from the set, and it exceeds that factor.

namespace OMA.A108129H1

/-- For each residue r mod 24, a prime of the covering set catches 509203 * 2^r. -/
lemma cover_small : ∀ r < 24, ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ),
    (509203 * 2 ^ r) % p = 1 := by
  decide

lemma pow_mod_24 (p m : ℕ) (h : 2 ^ 24 % p = 1) : 2 ^ m % p = 2 ^ (m % 24) % p := by
  conv_lhs => rw [← Nat.div_add_mod m 24, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h,
    one_pow]
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p <;> simp_all
  · rw [Nat.one_mod_eq_one.mpr (by omega), one_mul, Nat.mod_mod]

lemma cover (m : ℕ) : ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ),
    (509203 * 2 ^ m) % p = 1 := by
  obtain ⟨p, hp, hr⟩ := cover_small (m % 24) (Nat.mod_lt _ (by norm_num))
  refine ⟨p, hp, ?_⟩
  have h24 : 2 ^ 24 % p = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [Nat.mul_mod, pow_mod_24 p m h24, ← Nat.mul_mod, hr]

lemma not_prime (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  intro hpr
  obtain ⟨p, hp, hr⟩ := cover m
  have hp2 : 2 ≤ p ∧ p ≤ 241 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    apply Nat.sub_mod_eq_zero_of_mod_eq
    rw [hr, Nat.one_mod_eq_one.mpr (by omega)]
  have hbig : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
  rcases hpr.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

end OMA.A108129H1

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by norm_num), dif_neg]
  rintro ⟨m, hm, hpr⟩
  exact OMA.A108129H1.not_prime m hm (by simpa using hpr)
