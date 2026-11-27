import FormalConjectures.GreensOpenProblems.«97»

-- Reduction Green97.green_97.variants.simkin.R1 of Simkin's theorem.
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Simkin's theorem (M. Simkin, The number of n-queens configurations, Adv. Math. 427 (2023),
arXiv:2107.13460, Theorem 1.1) says Q(n) = ((1 + o(1)) n e^(-alpha))^n with 1.94 < alpha < 1.9449.
The paper proves it in three parts, and the hypotheses below are those three parts, each stated
with no reference to the queenon optimisation problem, so that each can be attacked on its own.

H1 is the existence of the limit of Q(n)^(1/n) / n: the entropy upper bound and the lower bound
from the randomised algorithm meet. No numerical value is asked.
H2 is the lower bound on the count with an explicit rate: Q(n) is at least (n e^(-c))^n for
some c < 1.9449 and all large n. In the paper this is the algorithm run on one explicit queenon
(the upper bound on alpha).
H3 is the upper bound on the count with an explicit rate: Q(n) is at most (n e^(-c))^n for
some c > 1.94 and all large n. In the paper this is the entropy method together with the
numerical lower bound on alpha; it needs no algorithm and no absorbers.

The split loses nothing: the target implies each of the three. The proof of main takes n-th
roots in H2 and H3, passes to the limit given by H1, and sets alpha = - log of the limit.
-/

namespace OMA.R_Green97_green_97_variants_simkin_R1

open Filter Topology

-- The limit of Q(n)^(1/n) / n exists.
def H1 : Prop := ∃ L : ℝ,
    Tendsto (fun n : ℕ ↦ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n) atTop (𝓝 L)

-- Lower bound on the count: Q(n) ≥ (n e^(-c))^n for some c < 1.9449 and all large n.
def H2 : Prop := ∃ c : ℝ, c < 1.9449 ∧
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) * Real.exp (-c)) ^ n ≤ (Green97.numQueens n : ℝ)

-- Upper bound on the count: Q(n) ≤ (n e^(-c))^n for some c > 1.94 and all large n.
def H3 : Prop := ∃ c : ℝ, 1.94 < c ∧
    ∀ᶠ n : ℕ in atTop, (Green97.numQueens n : ℝ) ≤ ((n : ℝ) * Real.exp (-c)) ^ n

/-- The n-th root of `(n * x) ^ n`, divided by `n`, is `x`. -/
lemma root_div (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    (((n : ℝ) * x) ^ n) ^ ((1 : ℝ) / n) / n = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h0 : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx
  rw [one_div, Real.pow_rpow_inv_natCast h0 hn.ne']
  field_simp

theorem main : H1 → H2 → H3 → type_of% @Green97.green_97.variants.simkin := by
  rintro ⟨L, hL⟩ ⟨c₂, hc₂, h₂⟩ ⟨c₃, hc₃, h₃⟩
  -- lower bound on the limit
  have hlow : Real.exp (-c₂) ≤ L := by
    refine ge_of_tendsto hL ?_
    filter_upwards [h₂, eventually_gt_atTop 0] with n hn hn0
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have h0 : (0 : ℝ) ≤ ((n : ℝ) * Real.exp (-c₂)) ^ n :=
      pow_nonneg (mul_nonneg hpos.le (Real.exp_pos _).le) n
    have h1 : (((n : ℝ) * Real.exp (-c₂)) ^ n) ^ ((1 : ℝ) / n)
        ≤ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) :=
      Real.rpow_le_rpow h0 hn (by positivity)
    calc Real.exp (-c₂)
        = (((n : ℝ) * Real.exp (-c₂)) ^ n) ^ ((1 : ℝ) / n) / n :=
          (root_div n hn0 _ (Real.exp_pos _).le).symm
      _ ≤ (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n :=
          div_le_div_of_nonneg_right h1 hpos.le
  -- upper bound on the limit
  have hup : L ≤ Real.exp (-c₃) := by
    refine le_of_tendsto hL ?_
    filter_upwards [h₃, eventually_gt_atTop 0] with n hn hn0
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have h1 : (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n)
        ≤ (((n : ℝ) * Real.exp (-c₃)) ^ n) ^ ((1 : ℝ) / n) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by positivity)
    calc (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n
        ≤ (((n : ℝ) * Real.exp (-c₃)) ^ n) ^ ((1 : ℝ) / n) / n :=
          div_le_div_of_nonneg_right h1 hpos.le
      _ = Real.exp (-c₃) := root_div n hn0 _ (Real.exp_pos _).le
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hexp : Real.exp (-(-Real.log L)) = L := by
    rw [neg_neg, Real.exp_log hLpos]
  have h1 : -c₂ ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hlow
    rwa [Real.log_exp] at this
  have h2 : Real.log L ≤ -c₃ := by
    have := Real.log_le_log hLpos hup
    rwa [Real.log_exp] at this
  refine ⟨-Real.log L, by linarith, by linarith, ?_⟩
  rw [hexp]
  exact hL

end OMA.R_Green97_green_97_variants_simkin_R1
