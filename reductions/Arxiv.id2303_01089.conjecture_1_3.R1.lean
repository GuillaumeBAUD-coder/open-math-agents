import FormalConjectures.Arxiv.«2303.01089».FurstenbergTimesPTimesQ

-- Reduction Arxiv.id2303_01089.conjecture_1_3.R1 of Conjecture 1.3
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Conjecture 1.3: the absolutely continuous case is not the hard case

The target says: an atomless probability measure `μ` on `𝕋` that is invariant under both
`T_p` and `T_q` (`p, q ≥ 2` multiplicatively independent) must be Lebesgue.

Every such `μ` splits as `μ = μ_ac + μ_sing` with `μ_ac ≪ volume` and `μ_sing ⊥ volume`, and
the conjecture is really a statement about the singular part: the absolutely continuous case is
already a theorem, and it needs only *one* of the two maps, with no atomlessness and no
independence hypothesis.

* `H1` (provable, Mathlib): if `2 ≤ p`, `μ` is a probability measure, `μ ≪ volume` and `μ` is
  `T_p`-invariant, then `μ = volume`. This is `Ergodic.eq_of_absolutelyContinuous` applied to
  `AddCircle.ergodic_nsmul`, the ergodicity of `y ↦ p • y` w.r.t. Haar measure.
* `H2` (open, the actual content of Conjecture 1.3): the hypotheses of the conjecture already
  force `μ ≪ volume`, i.e. no atomless `T_p`- and `T_q`-invariant probability measure has a
  singular part.

`H2` is *not* a consequence of `H1` and is a genuine strengthening of the target (it implies the
Furstenberg `×p, ×q` conjecture together with a description of the absolutely continuous part);
it is not known to be false — Lebesgue measure satisfies it, and the known partial results
(Rudolph/Johnson–Rudolph, Host, Hochman–Shmerkin, Lindenstrauss–Meiri, Badea–Grivaux) all require
extra entropy/ergodicity hypotheses. Note the implication direction: `H1 → H2 → target`.
-/

namespace OMA.R_Arxiv_id2303_01089_conjecture_1_3_R1

open MeasureTheory
open scoped MeasureTheory

/-- `H1`: the absolutely continuous, `T_p`-invariant case of Conjecture 1.3. -/
def H1 : Prop := ∀ {p : ℕ} (_hp : 2 ≤ p) {μ : Measure UnitAddCircle} [IsProbabilityMeasure μ],
    MeasurePreserving (Arxiv.id2303_01089.Tn p) μ μ → Measure.AbsolutelyContinuous μ (volume : Measure UnitAddCircle) →
      μ = volume

/-- `H2`: the hypotheses of Conjecture 1.3 force absolute continuity w.r.t. Lebesgue measure. -/
def H2 : Prop := ∀ {p q : ℕ} (_hp : 2 ≤ p) (_hq : 2 ≤ q)
    (_hpq : Nat.MultiplicativelyIndependent p q)
    {μ : Measure UnitAddCircle} [IsProbabilityMeasure μ] [Arxiv.id2303_01089.MeasureTheory.IsAtomLess μ]
    (_hmup : MeasurePreserving (Arxiv.id2303_01089.Tn p) μ μ)
    (_hmuq : MeasurePreserving (Arxiv.id2303_01089.Tn q) μ μ),
    Measure.AbsolutelyContinuous μ (volume : Measure UnitAddCircle)

theorem main : H1 → H2 → type_of% @Arxiv.id2303_01089.conjecture_1_3 := by
  intro h1 h2 p q hp hq hpq μ hprob hatom hmup hmuq
  exact h1 hp hmup (h2 hp hq hpq hmup hmuq)

end OMA.R_Arxiv_id2303_01089_conjecture_1_3_R1
