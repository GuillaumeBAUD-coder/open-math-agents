import OMAStatements.S_mo_330018
import Mathlib

/-!
# MathOverflow 330018: continuous functions on a Fort space

In the Fort topology with special point `b`, a set is open iff it misses `b` or is cofinite.

* The range of `f : X → [0, 1]` lies in `[0, 1]`, so it is bounded.
* If `f` is continuous, the preimage of the open ball of radius `ε` about `f b` is an open set
  containing `b`, hence cofinite: only finitely many `x` have `dist (f x) (f b) ≥ ε`.
* Conversely let `V` be open. If `b ∉ f⁻¹(V)` the preimage is open. Otherwise `V` contains a
  ball of some radius `ε` about `f b`, and the complement of `f⁻¹(V)` lies in the finite set
  `{x | ε ≤ dist (f x) (f b)}`, so the preimage is cofinite, hence open.
-/

open Set Metric OMA.S_mo_330018

theorem OMA.solution : type_of% @OMA.S_mo_330018.main := by
  intro X _ _ b hb f
  constructor
  · -- boundedness
    refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
    rintro _ ⟨x, rfl⟩
    exact (f x).2
  · constructor
    · -- continuous ⇒ finitely many far points
      intro hf ε hε
      have hopen : IsOpen (f ⁻¹' Metric.ball (f b) ε) := Metric.isOpen_ball.preimage hf
      rcases (hb _).mp hopen with h | h
      · exact absurd (Metric.mem_ball_self hε) h
      · refine h.subset ?_
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, not_lt]
        exact hx
    · -- finitely many far points ⇒ continuous
      intro h
      rw [continuous_def]
      intro V hV
      rw [hb]
      by_cases hbV : b ∈ f ⁻¹' V
      · right
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV (f b) hbV
        refine (h ε hε).subset ?_
        intro x hx
        by_contra hlt
        exact hx (hball (Metric.mem_ball.mpr (not_le.mp hlt)))
      · left
        exact hbV
