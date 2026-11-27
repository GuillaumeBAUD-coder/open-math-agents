import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

open Erdos338

private lemma fourEnough : HasOrder (Set.range fun n : ℕ => n ^ 2) 4 := by
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares n
  refine ⟨{a^2,b^2,c^2,d^2}, ?_, by simp, ?_⟩
  · intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨a,rfl⟩
    · exact ⟨b,rfl⟩
    · exact ⟨c,rfl⟩
    · exact ⟨d,rfl⟩
  · simpa [add_assoc] using h

private lemma orderLower (t : ℕ) (ht : HasOrder (Set.range fun n : ℕ => n^2) t) : 4 ≤ t := by
  by_contra! small
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 ht
  obtain ⟨s,hs,hc,hv⟩ := hN (8*N+7) (by omega)
  let u := s + Multiset.replicate (3-s.card) 0
  have uc : u.card = 3 := by simp [u]; omega
  have uv : u.sum = 8*N+7 := by simp [u,hv]
  have us : ∀ x ∈ u, x ∈ Set.range fun n : ℕ => n^2 := by
    intro x hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact hs x hx
    · have hx0 := Multiset.eq_of_mem_replicate hx
      exact ⟨0,by simp [hx0]⟩
  obtain ⟨x,y,z,hu⟩ := Multiset.card_eq_three.1 uc
  rw [hu] at uv us
  obtain ⟨a,rfl⟩ := us x (by simp)
  obtain ⟨b,rfl⟩ := us y (by simp)
  obtain ⟨c,rfl⟩ := us z (by simp)
  have h := congrArg (fun n : ℕ => (n : ZMod 8)) uv
  push_cast at h
  have bad : ∀ a b c : ZMod 8, a^2 + (b^2 + c^2) ≠ 7 := by decide
  have z8 : (8 : ZMod 8) = 0 := by decide
  exact bad a b c (by simpa [z8, add_assoc] using h)

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 basisOrder
  apply le_antisymm (iInf₂_le 4 fourEnough)
  refine le_iInf₂ fun t ht => ?_
  exact_mod_cast orderLower t ht
