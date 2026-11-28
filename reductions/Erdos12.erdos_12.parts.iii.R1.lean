import FormalConjectures.ErdosProblems.«12»

/-!
# Reduction R1 of Erdős Problem 12 — iii

Target (verbatim from the module): for every `A : Set ℕ` with `IsGood A`, the sum
`∑_{n ∈ A} 1/n` is summable, where

`IsGood A := A.Infinite ∧ ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b → a < c → b = c`.

The published Erdős–Sárközy theorem (`Erdos12.variants.erdos_sarkozy_density_0`, [ErSa70])
gives only density 0 for such `A`; whether the reciprocal sum must converge is open
(erdosproblems.com/12: it is unknown whether some such `A` has `∑ 1/n = ∞`).

This file partitions the quantified domain `{A : Set ℕ // IsGood A}` into three regions.
Because `IsGood A` contains `A.Infinite`, the conjecture only ever sees infinite `A`; the
finite region `H1` below is therefore *empty of IsGood sets*. It is nevertheless stated as a
genuine, non-vacuous elementary lemma (a sum over a finite subtype is a finite sum), not as a
disguised case split: `H1` is provable in one line from `Set.Finite`/`Fintype`, independently
of `IsGood`. The open content is split into the two halves `H2` and `H3` of the infinite
region:

* `H2`: infinite `A` that are pairwise coprime. This is the region that the literature
  attacks: Schoen [Sc01] proves `|A ∩ {1,…,N}| ≪ N^{2/3}` for infinitely many `N`, and
  Baier [Ba04] improves this to `≪ N^{2/3}/log N` (the module's `variants.schoen` and
  `variants.baier`). Both bounds are compatible with a divergent reciprocal sum, so `H2`
  is strictly weaker than the published results' conclusion and still open.
* `H3`: infinite `A` that are *not* pairwise coprime. This is the complementary half; it is
  a genuinely different regime (two elements then share a prime factor), and no published
  theorem in the module covers it. Note `{6, 14, 15}` is a finite good set that is not
  pairwise coprime, so this region is not obviously empty.

`H2` and `H3` are each strictly weaker than the target (they restrict the quantifier to one
half of the infinite sets), and `main` uses all three.
-/

open Erdos12

namespace OMA.R_Erdos12_erdos_12_parts_iii_R1

/-- Region 1: `A` is finite. Elementary: the subtype `A` is finite, so `∑ 1/n` over it is a
finite sum. This region contains no `IsGood` set (`IsGood` requires `A.Infinite`), but the
statement itself is a true and independently provable lemma. -/
def H1 : Prop :=
  ∀ (A : Set ℕ), A.Finite → Summable (fun (n : A) ↦ (1 / n : ℝ))

/-- Region 2: `A` is infinite and pairwise coprime — the regime of Schoen [Sc01] and
Baier [Ba04], whose density bounds do not settle summability. -/
def H2 : Prop :=
  ∀ (A : Set ℕ), A.Infinite → A.Pairwise Nat.Coprime → IsGood A →
    Summable (fun (n : A) ↦ (1 / n : ℝ))

/-- Region 3: `A` is infinite and not pairwise coprime — the complementary regime, not
covered by any published result in the module. -/
def H3 : Prop :=
  ∀ (A : Set ℕ), A.Infinite → ¬ A.Pairwise Nat.Coprime → IsGood A →
    Summable (fun (n : A) ↦ (1 / n : ℝ))

theorem main : H1 → H2 → H3 → type_of% @Erdos12.erdos_12.parts.iii := by
  intro h1 h2 h3 A hA
  by_cases hfin : A.Finite
  · exact h1 A hfin
  · by_cases hcop : A.Pairwise Nat.Coprime
    · exact h2 A hA.1 hcop hA
    · exact h3 A hA.1 hcop hA

end OMA.R_Erdos12_erdos_12_parts_iii_R1
