import OMAStatements.S_mo_330018
import Mathlib

/-
MathOverflow 330018: on a Fort space with special point b, a map f into the unit interval is
bounded, and it is continuous exactly when, for every eps > 0, only finitely many points x have
dist (f x) (f b) >= eps.

Bounded: the values lie in the unit interval. If f is continuous, the preimage of the open ball
around f b is open and contains b, so its complement is finite. Conversely, let V be open. If
b is not in the preimage of V, the preimage is open. Otherwise V contains a ball around f b,
and the complement of the preimage lies in a finite set.
-/

namespace OMA.PMO330018

open Set Metric

lemma main' : ∀ (X : Type) [TopologicalSpace X] [Infinite X] (b : X),
    (∀ U : Set X, IsOpen U ↔ b ∉ U ∨ Uᶜ.Finite) →
      ∀ f : X → Icc (0 : ℝ) 1,
        Bornology.IsBounded (range fun x => (f x : ℝ)) ∧
        (Continuous f ↔ ∀ ε > (0 : ℝ), {x | ε ≤ dist (f x) (f b)}.Finite) := by
  intro X _ _ b hF f
  refine ⟨(isBounded_Icc (0 : ℝ) 1).subset (by rintro _ ⟨x, rfl⟩; exact (f x).2),
    fun hc ε hε => ?_, fun h => ?_⟩
  · have ho : IsOpen (f ⁻¹' ball (f b) ε) := isOpen_ball.preimage hc
    rcases (hF _).1 ho with hb | hfin
    · exact absurd (by simpa using hε : b ∈ f ⁻¹' ball (f b) ε) hb
    · refine hfin.subset fun x hx => ?_
      simpa [mem_ball, not_lt] using hx
  · rw [continuous_def]
    intro V hV
    rw [hF]
    by_cases hb : b ∈ f ⁻¹' V
    · right
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV (f b) hb
      refine (h ε hε).subset fun x hx => ?_
      by_contra hlt
      exact hx (hball (by simpa [mem_ball, not_le] using hlt))
    · exact Or.inl hb

end OMA.PMO330018

theorem OMA.solution : type_of% @OMA.S_mo_330018.main := OMA.PMO330018.main'
