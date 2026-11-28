import OMAStatements.S_mo_254840
import Mathlib

-- Problem: mo-254840, can one have more than n mutually orthogonal n-bit (+-1) sequences?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Mutually orthogonal +-1 vectors are nonzero and pairwise orthogonal in R^n, hence
-- linearly independent, so there are at most n of them.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_254840.main) := by
  rintro ⟨n, hn, S, hpm, horth, hcard⟩
  obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ : ∃ v : S → EuclideanSpace ℝ (Fin n),
      ∀ a, v a = WithLp.toLp 2 (fun i => ((a.1 i : ℤ) : ℝ)) := ⟨_, fun _ => rfl⟩
  have hz : ∀ a : S, v a ≠ 0 := by
    intro a h0
    rw [hv] at h0
    have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w i0) h0
    simp at h1
    rcases hpm a.1 a.2 i0 with h | h <;> omega
  have ho : Pairwise fun a b : S => inner ℝ (v a) (v b) = 0 := by
    intro a b hab
    have h := horth a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h))
    have e : inner ℝ (v a) (v b) = ((∑ i, a.1 i * b.1 i : ℤ) : ℝ) := by
      rw [hv, hv]
      simp [PiLp.inner_apply, mul_comm]
    rw [e, h]
    simp
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hz ho
  have hle := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, finrank_euclideanSpace_fin] at hle
  omega
