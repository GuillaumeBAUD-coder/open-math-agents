import FormalConjectures.ErdosProblems.«917»

/-!
Reduction R1 of `Erdos917.erdos_917.parts.ii`: `f_6(n) ~ n²/4`.

The asymptotic is split into its two sides.
* H1, the lower bound: for every `ε > 0`, `(1/4 - ε) n² ≤ f_6(n)` for all large `n`. Even `n`:
  the join `C_a ∨ C_b` of two odd cycles with `a + b = n` is 6-critical with `ab ≥ n²/4 - 1`
  edges (Dirac). Odd `n`: the Hajós sum of such a graph on `n - 5` vertices with `K_6` is
  6-critical on `n` vertices.
* H2, the upper bound: for every `ε > 0`, `f_6(n) ≤ (1/4 + ε) n²` for all large `n` (the open part).

Together they give `f_6(n) / (n²/4) → 1`.
-/

namespace OMA.R_Erdos917_erdos_917_parts_ii_R1

open Filter Asymptotics

/-- The lower bound. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in atTop, ((1 : ℝ) / 4 - ε) * (n : ℝ) ^ 2 ≤ (Erdos917.f 6 n : ℝ)

/-- The upper bound (open). -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in atTop, (Erdos917.f 6 n : ℝ) ≤ ((1 : ℝ) / 4 + ε) * (n : ℝ) ^ 2

theorem main : H1 → H2 → type_of% @Erdos917.erdos_917.parts.ii := by
  intro h1 h2
  rw [isEquivalent_iff_tendsto_one]
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    have hε : (0 : ℝ) < δ / 8 := by positivity
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp (h1 (δ / 8) hε)
    obtain ⟨N2, hN2⟩ := eventually_atTop.mp (h2 (δ / 8) hε)
    refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
    have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 1 ≤ n := le_trans (le_max_right _ _) hn
      exact_mod_cast this
    have lo := hN1 n hn1
    have hi := hN2 n hn2
    have hq : (0 : ℝ) < (n : ℝ) ^ 2 / 4 := by positivity
    rw [Real.dist_eq, Pi.div_apply, abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hq]; nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hq]; nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    intro h; exfalso; have : (0 : ℝ) < (n : ℝ) ^ 2 / 4 := by positivity
    linarith

end OMA.R_Erdos917_erdos_917_parts_ii_R1

