import FormalConjectures.ErdosProblems.«230»

-- Reduction Erdos230.erdos_230.variants.ultraflat.R1 of Erdős Problem 230 — ultraflat variant
-- Credit: @JosiahMcj
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős Problem 230 (ultraflat variant) reduces to the two halves of one construction.

The variant asks for ONE sequence of unit-modulus coefficient families whose circle sup of the
relative deviation `|norm P / sqrt n - 1|` tends to 0: EVERY point of the unit circle must have
`norm P(z)` within `o(sqrt n)` of `sqrt n`, from BOTH sides.

- The first hypothesis (the upper half, constructed): there is a unit-modulus sequence whose
  polynomials are uniformly flat ABOVE: for every `eps > 0`, eventually every point of the
  circle has `norm P(z) <= (1 + eps) * sqrt n`. This is the Kahane-type ultraflat construction
  direction - the half the formal literature has already proven for the one-sided main statement.
- The second hypothesis (the lower half, no dips): any unit-modulus sequence that is uniformly
  flat above has no flat dips: for every `eps > 0`, eventually every point has
  `norm P(z) >= (1 - eps) * sqrt n`. This is the no-flat-dips half of the construction - the
  genuinely open half.
- `main` glues: apply the lower half to the sequence the upper half provides; every point is then
  eventually inside the band `[(1 - eps/2), (1 + eps/2)] * sqrt n`, so the sup of
  `|norm P / sqrt n - 1|` is eventually at most `eps/2 < eps`, which is exactly the target's
  `Tendsto ... (nhds 0)`.
-/

namespace OMA.R_Erdos230_erdos_230_variants_ultraflat_R1

def H1 : Prop :=
  ∃ A : (n : ℕ) → Fin n → ℂ, (∀ (n : ℕ) (k : Fin n), ‖A n k‖ = 1) ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : Metric.sphere (0 : ℂ) 1,
      ‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ ≤ (1 + ε) * Real.sqrt n

def H2 : Prop :=
  ∀ A : (n : ℕ) → Fin n → ℂ, (∀ (n : ℕ) (k : Fin n), ‖A n k‖ = 1) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : Metric.sphere (0 : ℂ) 1,
      ‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ ≤ (1 + ε) * Real.sqrt n) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : Metric.sphere (0 : ℂ) 1,
      (1 - ε) * Real.sqrt n ≤ ‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖

theorem main : H1 → H2 → type_of% @Erdos230.erdos_230.variants.ultraflat := by
  intro h1 h2
  obtain ⟨A, hA1, hA2⟩ := h1
  obtain hlow := h2 A hA1 hA2
  refine ⟨A, hA1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nu, hu⟩ := hA2 (ε / 2) (half_pos hε)
  obtain ⟨Nl, hl⟩ := hlow (ε / 2) (half_pos hε)
  refine ⟨max (max Nu Nl) 1, fun n hn => ?_⟩
  have hNu : Nu ≤ n := Nat.le_trans (le_max_left Nu Nl)
    (Nat.le_trans (le_max_left (max Nu Nl) 1) hn)
  have hNl : Nl ≤ n := Nat.le_trans (le_max_right Nu Nl)
    (Nat.le_trans (le_max_left (max Nu Nl) 1) hn)
  have hn1 : 1 ≤ n := Nat.le_trans (le_max_right (max Nu Nl) 1) hn
  have hn1r : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn1r
  have hu' : ∀ z : Metric.sphere (0 : ℂ) 1,
      ‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ / Real.sqrt n ≤ 1 + ε / 2 := by
    intro z
    exact (div_le_iff₀ hsqrt).mpr (hu n hNu z)
  have hl' : ∀ z : Metric.sphere (0 : ℂ) 1,
      1 - ε / 2 ≤ ‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ / Real.sqrt n := by
    intro z
    exact (le_div_iff₀ hsqrt).mpr (hl n hNl z)
  have hpt : ∀ z : Metric.sphere (0 : ℂ) 1,
      |‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ / Real.sqrt n - 1| ≤ ε / 2 := by
    intro z
    rw [abs_le]
    constructor
    · linarith [hl' z]
    · linarith [hu' z]
  have hpos : (0 : ℝ) ≤ ⨆ z : Metric.sphere (0 : ℂ) 1,
      |‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ / Real.sqrt n - 1| := by
    refine le_ciSup_of_le (⟨ε / 2, by rintro _ ⟨z, rfl⟩; exact hpt z⟩) 1 (abs_nonneg _)
  have hsup : ⨆ z : Metric.sphere (0 : ℂ) 1,
      |‖∑ k : Fin n, A n k * (z : ℂ) ^ ((k : ℕ) + 1)‖ / Real.sqrt n - 1| ≤ ε / 2 :=
    ciSup_le hpt
  rw [Real.dist_0_eq_abs, abs_of_nonneg hpos]
  exact lt_of_le_of_lt hsup (half_lt_self hε)

end OMA.R_Erdos230_erdos_230_variants_ultraflat_R1