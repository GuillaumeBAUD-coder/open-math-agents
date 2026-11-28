import OMAStatements.S_opg_rendezvous_on_a_line

-- Reduction opg-rendezvous-on-a-line.R1 of Rendezvous on a line
-- Credit: @MBimrose (agent: hub-swarm-pi)

/-!
# Rendezvous on the line: the two halves of `rendezvousValue = 17 / 4`

`rendezvousValue` is the infimum, over probability laws `μ` on `Route` (paths starting at `0`
with speed at most one), of the expected value of the orientation average
`(τ(1,1) + τ(1,-1) + τ(-1,1) + τ(-1,-1)) / 4`, where `τ(a,b)` is the first time `t ≥ 0` with
`a · f t = 2 + b · g t`. Model: two agents start two units apart on a line, see nothing of each
other, may move at speed at most one, have no shared frame (each local orientation is independently
random, which is what the average over the four orientation pairs encodes), and both draw their
path from the same law. The payoff is the expected first meeting time.

The numerical value `17 / 4` is *conjectured* in the literature on this problem
(Han, Du, Vera and Zuluaga, Operations Research 56 (2008), DOI 10.1287/opre.1070.0439); no proof of
it is known, and published two-sided bounds still leave a gap around it. So this file does not
attempt the equality: it splits it, as `le_antisymm` does, into the two independent pieces

* `H1` (construction half): some probability law on routes has expected meeting time at most
  `17 / 4`. This is the half the published strategies address, and it also certifies that the
  infimum is taken over a nonempty set of laws.
* `H2` (optimality half): every probability law on routes has expected meeting time at least
  `17 / 4`. This is the research core: no symmetric strategy does better.

Neither hypothesis mentions the value `rendezvousValue` itself, so each can be attacked on its own,
and `main` assembles them through the `iInf` defining the value.

What *is* proved here below (not assumed): every finite first hit happens at time at least `1`, so
the orientation average is at least `1` pointwise, hence every admissible law has expected meeting
time at least `1` and `rendezvousValue ≥ 1`. This shows the target is not vacuous and pins down the
easy end of the range that `H2` sharpens to `17 / 4`.
-/

namespace OMA.R_opg_rendezvous_on_a_line_R1

open MeasureTheory
open scoped ENNReal NNReal
open OMA.S_opg_rendezvous_on_a_line

/-- The measurable structure on `Route` used by the statement file: the Borel structure of the
compact-open topology on paths. It is `local` there, so it is repeated here. -/
local instance : MeasurableSpace Route := borel Route

/-- Construction half: some probability measure on `Route` has expected meeting time at most
`17 / 4`. -/
def H1 : Prop :=
  ∃ μ : Measure Route, IsProbabilityMeasure μ ∧ expectedTime μ ≤ (17 / 4 : ℝ≥0∞)

/-- Optimality half: every probability measure on `Route` has expected meeting time at least
`17 / 4`. -/
def H2 : Prop :=
  ∀ μ : Measure Route, IsProbabilityMeasure μ → (17 / 4 : ℝ≥0∞) ≤ expectedTime μ

/-- A route moves at speed at most one and starts at `0`, so it is never further than `t` from `0`
at time `t`. -/
lemma Route.abs_le_time (f : Route) (t : ℝ≥0) : |f.val t| ≤ (t : ℝ) := by
  have h := f.2.2.dist_le_mul t 0
  rw [Real.dist_eq, f.2.1, sub_zero] at h
  have h2 : dist (t : ℝ≥0) (0 : ℝ≥0) = (t : ℝ) := by
    rw [NNReal.dist_eq]
    simp
  rw [h2] at h
  simpa using h

/-- The four oriented coincidence equations force distance two, which two unit-speed paths that
both start at `0` cannot have closed before time one. -/
lemma one_le_of_hit (f g : Route) (a b : ℝ) (ha : |a| = 1) (hb : |b| = 1) (t : ℝ≥0)
    (ht : a * f.val t = 2 + b * g.val t) : 1 ≤ t := by
  have hkey : a * f.val t - b * g.val t = 2 := by linarith
  have htwo : (2 : ℝ) ≤ |a * f.val t - b * g.val t| := by rw [hkey]; norm_num
  have htri : |a * f.val t - b * g.val t| ≤ |a * f.val t| + |b * g.val t| := by
    simpa [sub_eq_add_neg] using abs_add_le (a * f.val t) (-(b * g.val t))
  rw [abs_mul, abs_mul, ha, hb, one_mul, one_mul] at htri
  have hf := Route.abs_le_time f t
  have hg := Route.abs_le_time g t
  have h2t : (2 : ℝ) ≤ 2 * (t : ℝ) := by linarith
  have h1t : (1 : ℝ) ≤ (t : ℝ) := by linarith
  exact_mod_cast h1t

/-- Every oriented first hit is at least one. -/
lemma one_le_firstHit (f g : Route) (a b : ℝ) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : 1 ≤ firstHit a b f g := by
  have hab : |a| = 1 := by rcases ha with h | h <;> rw [h] <;> norm_num
  have hbb : |b| = 1 := by rcases hb with h | h <;> rw [h] <;> norm_num
  refine le_iInf fun t => ?_
  exact ENNReal.coe_le_coe.mpr (one_le_of_hit f g a b hab hbb t.val t.2)

/-- The orientation average is at least one, pointwise. -/
lemma one_le_orientationMean (f g : Route) : 1 ≤ orientationMean f g := by
  have h1 : (1 : ℝ≥0∞) ≤ firstHit 1 1 f g := one_le_firstHit f g 1 1 (Or.inl rfl) (Or.inl rfl)
  have h2 : (1 : ℝ≥0∞) ≤ firstHit 1 (-1) f g := one_le_firstHit f g 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have h3 : (1 : ℝ≥0∞) ≤ firstHit (-1) 1 f g := one_le_firstHit f g (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have h4 : (1 : ℝ≥0∞) ≤ firstHit (-1) (-1) f g :=
    one_le_firstHit f g (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  have hsum : (4 : ℝ≥0∞) ≤ firstHit 1 1 f g + firstHit 1 (-1) f g +
      firstHit (-1) 1 f g + firstHit (-1) (-1) f g := by
    have h4' : (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 := by norm_num
    rw [h4']
    exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  unfold orientationMean
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  simpa using hsum

/-- Every probability law on routes has expected meeting time at least one. -/
lemma one_le_expectedTime (μ : Measure Route) (hμ : IsProbabilityMeasure μ) :
    1 ≤ expectedTime μ := by
  have hmono : (∫⁻ p : Route × Route, (1 : ℝ≥0∞) ∂(μ.prod μ)) ≤
      ∫⁻ p : Route × Route, orientationMean p.1 p.2 ∂(μ.prod μ) :=
    lintegral_mono fun p => one_le_orientationMean p.1 p.2
  have huniv : (μ.prod μ) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hμ.measure_univ, one_mul]
  refine le_trans (le_of_eq ?_) hmono
  rw [lintegral_const, huniv, one_mul]

/-- The easy end of the range: the rendezvous value is at least one. -/
lemma one_le_rendezvousValue : 1 ≤ rendezvousValue := by
  unfold rendezvousValue
  exact le_iInf fun μ => one_le_expectedTime μ.val μ.2

/-- `H1` bounds the infimum from above through its witness, and `H2` bounds it from below
pointwise, so the two halves meet at `17 / 4`. -/
theorem main : H1 → H2 → type_of% @OMA.S_opg_rendezvous_on_a_line.main := by
  intro h1 h2
  unfold OMA.S_opg_rendezvous_on_a_line.rendezvousValue
  refine le_antisymm ?_ ?_
  · obtain ⟨μ, hμ, hle⟩ := h1
    exact le_trans (iInf_le (fun ν : {ν : Measure Route // IsProbabilityMeasure ν} =>
      expectedTime ν.val) ⟨μ, hμ⟩) hle
  · exact le_iInf fun ν => h2 ν.val ν.property

end OMA.R_opg_rendezvous_on_a_line_R1
