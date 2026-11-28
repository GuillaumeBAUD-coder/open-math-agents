import FormalConjectures.ErdosProblems.«601»

-- Reduction Erdos601.erdos_601.variants.universal.R1 of Erdős–Hajnal–Milner conjecture
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/601, [Er81] Section VII): every simple graph on the vertex set of a
-- limit ordinal `α` contains either an infinite path or an independent set of order type `α`.
--
-- The split is along the size of `α`, which is exactly the shape of the known mathematics:
--
--   * `H1` — `α = ω`.  This region is ELEMENTARY and is *already proved in the imported module*:
--     `Erdos601.erdos_601.variants.at_omega` (built from the private API lemma `at_omega_aux`) is a
--     real, sorry-free proof.  Ramsey for pairs applied to an injective enumeration of `ω` gives an
--     infinite path or an infinite independent set, and an infinite subset of `ω` has order type `ω`.
--     The proof of `H1_holds` below discharges this region by `subst` plus that one lemma.
--   * `H2` — `α` countable and `α ≠ ω`.  This region is SETTLED by the published theorem
--     [EHM70] of Erdős–Hajnal–Milner, which is stated in the same module as
--     `erdos_601.variants.erdos_hajnal_milner_1970`: it covers every limit ordinal
--     `α < ω₁ ^ (ω + 2)`, and every countable `α` satisfies `α < ω₁ ≤ ω₁ ^ (ω + 2)`.
--     So nothing is left open in `H2`.
--   * `H3` — `α` uncountable (cardinality above `ℵ₀`).  This is the CORE and it is genuinely open:
--     the critical ordinal `ω₁ ^ (ω + 2)` is uncountable, and there the answer is independent of ZFC
--     (fails under Jensen's diamond, holds under Martin's Axiom, [La90]).  Note `H3` is not a
--     restatement of the target: it drops the whole countable range, where the mathematics is done.
--
-- `main` is the trichotomy `α = ω` / countable non-`ω` / uncountable, so closing `H1` and `H2` and
-- `H3` closes the statement.  `H1` is fully discharged here, so only `H2` (a citation) and `H3`
-- (the open core) need future work.

namespace OMA.R_Erdos601_erdos_601_variants_universal_R1

open Cardinal Ordinal Erdos601

/-- The base case `α = ω`: elementary, and in fact proved in the imported module. -/
def H1 : Prop :=
  ∀ α : Ordinal.{0}, Order.IsSuccLimit α → α = ω → HasPathOrIndepSetOfType α

/-- The countable range away from `ω`: settled by Erdős–Hajnal–Milner 1970, which covers every limit
ordinal below `ω₁ ^ (ω + 2)`. -/
def H2 : Prop :=
  ∀ α : Ordinal.{0}, Order.IsSuccLimit α → α ≠ ω → α.card ≤ ℵ₀ → HasPathOrIndepSetOfType α

/-- The open core: uncountable limit ordinals, where `ω₁ ^ (ω + 2)` sits and where the statement is
independent of ZFC. -/
def H3 : Prop :=
  ∀ α : Ordinal.{0}, Order.IsSuccLimit α → ¬ α.card ≤ ℵ₀ → HasPathOrIndepSetOfType α

/-- The elementary region `H1` is immediate from the sorry-free `at_omega` of the imported module. -/
theorem H1_holds : H1 := by
  intro α _ hα
  subst hα
  exact Erdos601.erdos_601.variants.at_omega

theorem main : H1 → H2 → H3 → type_of% @Erdos601.erdos_601.variants.universal := by
  intro h1 h2 h3 α hα
  by_cases hω : α = ω
  · exact h1 α hα hω
  · by_cases hc : α.card ≤ ℵ₀
    · exact h2 α hα hω hc
    · exact h3 α hα hc

end OMA.R_Erdos601_erdos_601_variants_universal_R1
