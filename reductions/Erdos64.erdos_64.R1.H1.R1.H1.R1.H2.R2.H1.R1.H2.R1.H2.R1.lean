import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1

-- Reduction Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H2.R1.H2.R1 of step Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H2.R1.H2
-- Credit: @maz777

/-!
# The odd regular residual, split by derived length

The parent step is the regular odd-order case in which the commutator subgroup is
nonabelian, so the group has derived length at least three. PR 12281 settled the
metabelian case through a voltage theorem over an abelian quotient with abelian kernel.

This reduction separates the next level of the derived series.

* `H1`: the second derived subgroup is abelian (derived length exactly three). Here the
  quotient by the second derived subgroup is metabelian, so the merged voltage theorem
  gives closed walks of length at most 32 in the quotient graph, and the kernel is abelian,
  so commutators of two lifted closed walks close up. What is missing is simplicity of
  such a commutator walk of power-of-two length.
* `H2`: the second derived subgroup is nonabelian (derived length at least four).

Experiments (note 68090 on the root problem) found a 16- or 32-cycle for every sampled
generating pair in three odd groups of derived length three, of orders 1029, 6591 and 6655.

Claude Code, claude-fable-5-2, for @maz777. Thanks to the authors of PR 12281 and of the
parent reductions, whose statements this file reuses.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R1
open SimpleGraph

/-- Two-generated odd groups of derived length exactly three: the commutator subgroup is
nonabelian and the second derived subgroup is abelian. -/
def H1 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∃ x y : commutator A, x * y ≠ y * x) →
    (∀ x ∈ derivedSeries A 2, ∀ y ∈ derivedSeries A 2, x * y = y * x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

/-- Two-generated odd groups of derived length at least four: the second derived
subgroup is nonabelian. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∃ x ∈ derivedSeries A 2, ∃ y ∈ derivedSeries A 2, x * y ≠ y * x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1.H2 := by
  intro three deeper A _ _ a b gen a1 b1 ab odd absent noncomm
  by_cases h : ∀ x ∈ derivedSeries A 2, ∀ y ∈ derivedSeries A 2, x * y = y * x
  · exact three A a b gen a1 b1 ab odd absent noncomm h
  · push Not at h
    exact deeper A a b gen a1 b1 ab odd absent h

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R1
