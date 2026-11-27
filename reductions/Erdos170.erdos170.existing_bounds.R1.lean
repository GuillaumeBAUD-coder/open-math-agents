import FormalConjectures.ErdosProblems.«170»

-- Reduction Erdos170.erdos170.existing_bounds.R1 of Erdos Problem 170 (existing bounds)
-- Credit: @green-notes
-- Splits the three classical theorems in Erdos170.erdos170.existing_bounds:
--   H1: Erdos-Gal (1948) existence of the limit of F(N) / sqrt(N).
--   H2: Leech (1956) trigonometric lower bound on (F(N) / sqrt(N))^2.
--   H3: Wichmann (1963) constructive ruler upper bound on F(N) / sqrt(N).

/-!
# Reduction of Erdős Problem 170 (existing bounds)
Splits the existence of the limit (Erdős-Gál 1948), Leech's trigonometric lower bound (1956),
and Wichmann's constructive upper bound (1963) into three independent subgoals.
-/

namespace OMA.R_Erdos170_erdos170_existing_bounds_R1

-- Existence of the limit lim_{N -> infty} F(N) / sqrt(N) (Erdos-Gal 1948).
def H1 : Prop :=
  ∃ x : ℝ, Filter.Tendsto (fun N : ℕ => (Erdos170.F N : ℝ) / √(N : ℝ)) Filter.atTop (nhds x)

-- Leech (1956) lower bound: for every theta != 0 and eps > 0, eventually
-- (F(N) / sqrt(N))^2 >= 2 * (1 - sin(theta) / theta) - eps.
def H2 : Prop :=
  ∀ θ : ℝ, θ ≠ 0 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * (1 - Real.sin θ / θ) - ε ≤ ((Erdos170.F N : ℝ) / √(N : ℝ)) ^ 2

-- Wichmann (1963) upper bound: for every eps > 0, eventually
-- F(N) / sqrt(N) <= sqrt(3) + eps.
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos170.F N : ℝ) / √(N : ℝ) ≤ Erdos170.upper_bound + ε

theorem main : H1 → H2 → H3 → type_of% @Erdos170.erdos170.existing_bounds := by
  intro h1 h2 h3
  obtain ⟨x, hx⟩ := h1
  have hx_nonneg : 0 ≤ x := by
    apply ge_of_tendsto hx
    filter_upwards with N
    positivity
  have hx_upper : x ≤ Erdos170.upper_bound := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto hx (h3 ε hε)
  have hx_lower : Erdos170.lower_bound ≤ x := by
    rw [← Real.sqrt_sq hx_nonneg]
    apply Real.sqrt_le_sqrt
    apply csSup_le
    · exact ⟨2 * (1 - Real.sin 1 / 1), 1, one_ne_zero, rfl⟩
    · rintro y ⟨θ, hθ, rfl⟩
      have hx2 : Filter.Tendsto (fun N : ℕ => ((Erdos170.F N : ℝ) / √(N : ℝ)) ^ 2)
          Filter.atTop (nhds (x ^ 2)) := hx.pow 2
      apply le_of_forall_pos_le_add
      intro ε hε
      have hle : 2 * (1 - Real.sin θ / θ) - ε ≤ x ^ 2 := ge_of_tendsto hx2 (h2 θ hθ ε hε)
      linarith
  exact ⟨x, ⟨hx_lower, hx_upper⟩, hx⟩

end OMA.R_Erdos170_erdos170_existing_bounds_R1
