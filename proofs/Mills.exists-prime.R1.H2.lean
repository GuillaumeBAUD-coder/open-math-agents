import OMAReductions.R_Mills_exists_prime_R1

-- Step Mills.exists-prime.R1.H2: hypothesis H2 of reduction Mills.exists-prime.R1
-- Credit: @ptc-prover-bot

/-! Mills' nested intervals: `lₙ = qₙ^(1/3^(n+1))` is increasing (`qₙ³ ≤ qₙ₊₁`), `uₙ = (qₙ+1)^(1/3^(n+1))`
is strictly decreasing (`qₙ₊₁ + 1 < (qₙ+1)³`) and `lₙ < uₙ`; `A = sup lₙ` satisfies
`lₙ ≤ A < uₙ`, so `qₙ ≤ A^(3^(n+1)) < qₙ + 1`. -/

open Real

namespace OMA.MillsH2

theorem H2_proof : OMA.R_Mills_exists_prime_R1.H2 := by
  intro q hq2 hlo hhi
  let d : ℕ → ℕ := fun n => 3 ^ (n + 1)
  let l : ℕ → ℝ := fun n => (q n : ℝ) ^ ((d n : ℝ)⁻¹)
  let u : ℕ → ℝ := fun n => ((q n : ℝ) + 1) ^ ((d n : ℝ)⁻¹)
  have dpos : ∀ n, 0 < d n := fun n => by positivity
  have lpos : ∀ n, 0 ≤ l n := fun n => rpow_nonneg (Nat.cast_nonneg _) _
  have upos : ∀ n, 0 ≤ u n := fun n => rpow_nonneg (by positivity) _
  have lp : ∀ n, l n ^ d n = (q n : ℝ) := fun n =>
    rpow_inv_natCast_pow (Nat.cast_nonneg _) (dpos n).ne'
  have up : ∀ n, u n ^ d n = (q n : ℝ) + 1 := fun n =>
    rpow_inv_natCast_pow (by positivity) (dpos n).ne'
  have deq : ∀ n, d (n + 1) = d n * 3 := fun n => by
    show 3 ^ (n + 1 + 1) = 3 ^ (n + 1) * 3; rw [pow_succ]
  have lmono : Monotone l := monotone_nat_of_le_succ fun n => by
    apply (pow_le_pow_iff_left₀ (lpos n) (lpos (n + 1)) (dpos (n + 1)).ne').mp
    rw [lp (n + 1), deq, pow_mul, lp]
    exact_mod_cast hlo n
  have uanti : StrictAnti u := strictAnti_nat_of_succ_lt fun n => by
    apply (pow_lt_pow_iff_left₀ (upos (n + 1)) (upos n) (dpos (n + 1)).ne').mp
    rw [up (n + 1), deq, pow_mul, up]
    exact_mod_cast hhi n
  have lu : ∀ n, l n < u n := fun n =>
    rpow_lt_rpow (Nat.cast_nonneg _) (lt_add_one _) (inv_pos.mpr (by exact_mod_cast dpos n))
  have lle : ∀ m n, l m ≤ u n := by
    intro m n
    rcases le_total m n with h | h
    · exact (lmono h).trans (lu n).le
    · exact (lu m).le.trans (uanti.antitone h)
  have bdd : BddAbove (Set.range l) := ⟨u 0, by rintro _ ⟨m, rfl⟩; exact lle m 0⟩
  set A := ⨆ n, l n with hAdef
  have hlA : ∀ n, l n ≤ A := fun n => le_ciSup bdd n
  have hAu : ∀ n, A < u n := fun n =>
    lt_of_le_of_lt (ciSup_le fun m => lle m (n + 1)) (uanti (Nat.lt_succ_self n))
  have hA0 : 0 ≤ A := (lpos 0).trans (hlA 0)
  refine ⟨A, ?_, fun n => ?_⟩
  · -- A ≥ l 0 = q₀^(1/3) > 1
    have h1 : 1 < l 0 := by
      apply one_lt_rpow (by exact_mod_cast (show 1 < q 0 by have := hq2 0; omega))
      exact inv_pos.mpr (by exact_mod_cast dpos 0)
    exact lt_of_lt_of_le h1 (hlA 0)
  · have hlo' : (q n : ℝ) ≤ A ^ d n := by
      rw [← lp n]; exact pow_le_pow_left₀ (lpos n) (hlA n) _
    have hhi' : A ^ d n < (q n : ℝ) + 1 := by
      rw [← up n]; exact pow_lt_pow_left₀ (hAu n) hA0 (dpos n).ne'
    show ⌊A ^ d n⌋₊ = q n
    rw [Nat.floor_eq_iff (pow_nonneg hA0 _)]
    exact ⟨hlo', hhi'⟩

end OMA.MillsH2

theorem OMA.solution : OMA.R_Mills_exists_prime_R1.H2 := OMA.MillsH2.H2_proof
