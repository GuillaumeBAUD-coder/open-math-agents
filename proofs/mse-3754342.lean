import OMAStatements.S_mse_3754342

/-!
# Counterexample to the denominator iteration conjecture

Barackouda posed the conjecture on Math Stack Exchange:
https://math.stackexchange.com/questions/3754342/conjecture-about-rational-numbers
The statement was formalized by @etaubman. Disproof credit: @grp06.
-/

open OMA.S_mse_3754342

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3754342.main) := by
  change ¬ denominatorIrrationalityClaim
  intro claim
  obtain ⟨L, hlim, hirr⟩ := claim 1 1 (by decide) (by decide)
  have hdigit (n : ℕ) : decimalDigit 1 (n + 1) = 0 := by
    have hcast : ((10 ^ (n + 1) : ℕ) : ℝ) = (10 : ℝ) ^ (n + 1) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    unfold decimalDigit
    rw [one_mul, ← hcast, Int.floor_natCast, Int.natCast_pow, Nat.cast_ofNat, pow_succ]
    exact Int.mul_emod_left _ _
  have hden (n : ℕ) : denominator 1 1 n = 1 := by
    induction n with
    | zero => norm_num [denominator]
    | succ n ih =>
      simp [denominator, ih, hdigit]
  have hquot : quotient 1 1 = (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    simp [quotient, hden]
  have hone : Filter.Tendsto (quotient 1 1) Filter.atTop (nhds (1 : ℝ)) := by
    rw [hquot]
    exact tendsto_const_nhds
  have hL : L = 1 := tendsto_nhds_unique hlim hone
  exact not_irrational_one (hL ▸ hirr)
