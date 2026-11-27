import OMAReductions.R_OeisA108129_conjecture_R1

-- The six divisors all have 2^24 = 1 modulo the divisor. For each
-- exponent modulo 24, one of them divides 509203 * 2^m - 1.
namespace Riesel509203

private theorem cover (r : Fin 24) :
    ∃ p : Fin 242, 2 ≤ p.val ∧
      Nat.ModEq p.val (2 ^ 24) 1 ∧ Nat.ModEq p.val (509203 * 2 ^ r.val) 1 := by
  fin_cases r <;> first
    | exact ⟨3, by decide⟩
    | exact ⟨5, by decide⟩
    | exact ⟨7, by decide⟩
    | exact ⟨13, by decide⟩
    | exact ⟨17, by decide⟩
    | exact ⟨241, by decide⟩

theorem composite (m : ℕ) : ¬ (509203 * 2 ^ m - 1).Prime := by
  obtain ⟨p, hp, hperiod, hresidue⟩ := cover ⟨m % 24, Nat.mod_lt _ (by decide)⟩
  change Nat.ModEq p.val (509203 * 2 ^ (m % 24)) 1 at hresidue
  have hfactor : 509203 * 2 ^ m =
      (509203 * 2 ^ (m % 24)) * (2 ^ 24) ^ (m / 24) := by
    rw [← pow_mul, Nat.mul_assoc, ← pow_add, Nat.mod_add_div]
  have hmod : Nat.ModEq p.val (509203 * 2 ^ m) 1 := by
    rw [hfactor]
    simpa using hresidue.mul (hperiod.pow (m / 24))
  have hdvd : p.val ∣ 509203 * 2 ^ m - 1 := hmod.symm.dvd'
  have hpow : 0 < (2 : ℕ) ^ m := by positivity
  have hlt := p.isLt
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p.val hdvd with h | h <;> omega

end Riesel509203

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  change OeisA108129.a 254602 = -1
  have hnone : ¬ ∃ m : ℕ, m ≠ 0 ∧ ((2 * 254602 - 1) * 2 ^ m - 1).Prime := by
    rintro ⟨m, _, hm⟩
    exact Riesel509203.composite m hm
  rw [OeisA108129.a, if_neg (by decide), dif_neg hnone]
