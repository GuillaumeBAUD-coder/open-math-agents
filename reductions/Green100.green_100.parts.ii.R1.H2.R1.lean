import OMAReductions.R_Green100_green_100_parts_ii_R1

/-! From Gao–Yu–Zhi's group representation criterion to uniform approximate triviality. -/

-- Problem: Green100.green_100.parts.ii.R1.H2
-- Credit: @sobrien032
-- Gao–Yu–Zhi, arXiv:2610.10248v2, Lemma 2.2 and Proposition 4.2.
-- Gao–Yu–Zhi’s raw relators for Λ supply the proposed R. Its zero-based generator 72 is J.

namespace OMA.R_Green100_green_100_parts_ii_R1_H2_R1

open Filter Green100
open scoped Topology

/-- Compactness for a fixed finite presentation. Killing the marked word in every
unitary sequence quotient gives a dimension-independent tolerance for each target error. -/
def H1 : Prop :=
  ∀ (k : ℕ) (R : Finset (List (Fin k × Bool))) (w : FreeGroup (Fin k)),
    let S := FreeGroup.mk '' (↑R : Set (List (Fin k × Bool)))
    (∀ (d : ℕ → ℕ), (∀ i, 0 < d i) →
      let U := (i : ℕ) → Matrix.unitaryGroup (Fin (d i)) ℂ
      let N := Subgroup.normalClosure {x : U |
        Tendsto (fun i => hsDist (x i) 1) (hyperfilter ℕ) (𝓝 0)}
      ∀ ρ : PresentedGroup S →* U ⧸ N, ρ (PresentedGroup.mk S w) = 1) →
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ u : Fin k → Matrix.unitaryGroup (Fin n) ℂ,
        (∀ r ∈ R, hsDist (FreeGroup.lift u (FreeGroup.mk r)) 1 ≤ δ) →
        hsDist (FreeGroup.lift u w) 1 < η

/-- Find a 74-generator presentation in which generator 72 survives and every
representation into the indicated unitary sequence quotients kills it. -/
def H2 : Prop :=
  ∃ R : Finset (List (Fin 74 × Bool)),
    let S := FreeGroup.mk '' (↑R : Set (List (Fin 74 × Bool)))
    let J := FreeGroup.of (72 : Fin 74)
    PresentedGroup.mk S J ≠ 1 ∧
    ∀ (d : ℕ → ℕ), (∀ i, 0 < d i) →
      let U := (i : ℕ) → Matrix.unitaryGroup (Fin (d i)) ℂ
      let N := Subgroup.normalClosure {x : U |
        Tendsto (fun i => hsDist (x i) 1) (hyperfilter ℕ) (𝓝 0)}
      ∀ ρ : PresentedGroup S →* U ⧸ N, ρ (PresentedGroup.mk S J) = 1

theorem main : H1 → H2 → OMA.R_Green100_green_100_parts_ii_R1.H2 := by
  intro compactness witness
  obtain ⟨R, survives, kills⟩ := witness
  let S := FreeGroup.mk '' (↑R : Set (List (Fin 74 × Bool)))
  let J := FreeGroup.of (72 : Fin 74)
  have lift_eq (v : FreeGroup (Fin 74)) :
      PresentedGroup.mk S v = FreeGroup.lift (PresentedGroup.of (rels := S)) v :=
    FreeGroup.lift_unique (PresentedGroup.mk S) (fun _ => rfl)
  refine ⟨74, R, [(72, true)], ?_, ?_⟩
  · refine ⟨PresentedGroup S, inferInstance, PresentedGroup.of, ?_, ?_⟩
    · intro r hr
      rw [← lift_eq]
      exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩
    · rw [← lift_eq]
      exact survives
  · obtain ⟨δ, hδ, uniform⟩ := compactness 74 R J kills (1 / 8) (by norm_num)
    refine ⟨δ, hδ, ?_⟩
    intro n u approx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hsDist]
    · exact (uniform n hn u (fun r hr => (approx r hr).le)).le

end OMA.R_Green100_green_100_parts_ii_R1_H2_R1
