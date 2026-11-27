import OMAReductions.R_OeisA108129_conjecture_R1
import Mathlib.Tactic

-- Proof of H1 of reduction OeisA108129.conjecture.R1: a 254602 = -1, so k = 509203 is a Riesel number.
-- Covering set 3, 5, 7, 13, 17, 241. Their product 5592405 divides 2^24 - 1.
-- After the merge, change the target to type_of% @OMA.R_OeisA108129_conjecture_R1.H1 (same statement).

namespace OMA.A108129H1

lemma mod_reduce (m : ℕ) :
    (509203 * 2 ^ m) % 5592405 = (509203 * 2 ^ (m % 24)) % 5592405 := by
  conv_lhs => rw [← Nat.div_add_mod m 24, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.mul_mod ((2 ^ 24) ^ (m / 24)), Nat.pow_mod]
  norm_num

lemma cover (r : ℕ) (hr : r < 24) :
    ∃ p, p ∣ 5592405 ∧ 2 ≤ p ∧ p ≤ 241 ∧ (509203 * 2 ^ r) % 5592405 % p = 1 := by
  interval_cases r <;> first
    | (refine ⟨3, ?_⟩; norm_num; done) | (refine ⟨5, ?_⟩; norm_num; done)
    | (refine ⟨7, ?_⟩; norm_num; done) | (refine ⟨13, ?_⟩; norm_num; done)
    | (refine ⟨17, ?_⟩; norm_num; done) | (refine ⟨241, ?_⟩; norm_num; done)

lemma not_prime (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  obtain ⟨p, hpM, hp2, hp241, hmod⟩ := cover (m % 24) (Nat.mod_lt _ (by norm_num))
  rw [← mod_reduce, Nat.mod_mod_of_dvd _ hpM] at hmod
  have hpos : 1 ≤ 509203 * 2 ^ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hdvd : p ∣ 509203 * 2 ^ m - 1 := by
    apply (Nat.modEq_iff_dvd' hpos).mp
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    exact h1.trans hmod.symm
  have hbig : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

end OMA.A108129H1

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  show OeisA108129.a 254602 = -1
  show OeisA108129.a 254602 = -1
  rw [OeisA108129.a, if_neg (by norm_num), dif_neg]
  rintro ⟨m, hm, hp⟩
  norm_num at hp
  exact OMA.A108129H1.not_prime m hm hp
