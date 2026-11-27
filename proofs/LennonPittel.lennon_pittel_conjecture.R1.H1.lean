import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1
import Mathlib.Order.FixedPoints

/-! # Existence of a stable complete matching -/

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  classical
  intro n p
  -- A man can propose to a woman once every woman he prefers has a better proposal.
  let propose : Set (Fin n × Fin n) →o Set (Fin n × Fin n) :=
    ⟨fun S => {e | ∀ v, p.manRank e.1 v < p.manRank e.1 e.2 →
      ∃ j, (j, v) ∈ S ∧ p.womanRank v j < p.womanRank v e.1}, by
      intro S T hST e he v hv
      obtain ⟨j, hj, hrank⟩ := he v hv
      exact ⟨j, hST hj, hrank⟩⟩
  let proposals := propose.lfp
  have hproposal (m w : Fin n) : (m, w) ∈ proposals ↔
      ∀ v, p.manRank m v < p.manRank m w →
        ∃ j, (j, v) ∈ proposals ∧ p.womanRank v j < p.womanRank v m := by
    change (m, w) ∈ proposals ↔ (m, w) ∈ propose proposals
    rw [show propose proposals = proposals from propose.map_lfp]
  let wins (m w : Fin n) : Prop := (m, w) ∈ proposals ∧
    ∀ j, (j, w) ∈ proposals → p.womanRank w m ≤ p.womanRank w j
  have uniqueMan {m j w : Fin n} (hm : wins m w) (hj : wins j w) : m = j :=
    (p.womanRank w).injective (le_antisymm (hm.2 j hj.1) (hj.2 m hm.1))
  have uniqueWoman {m w v : Fin n} (hw : wins m w) (hv : wins m v) : w = v := by
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne ((p.manRank m).injective h)) with hlt | hgt
    · obtain ⟨j, hj, hrank⟩ := (hproposal m v).mp hv.1 w hlt
      exact (not_lt_of_ge (hw.2 j hj)) hrank
    · obtain ⟨j, hj, hrank⟩ := (hproposal m w).mp hw.1 v hgt
      exact (not_lt_of_ge (hv.2 j hj)) hrank
  have winnerExists (w : Fin n) (h : ∃ m, (m, w) ∈ proposals) : ∃ m, wins m w := by
    let eligible := Finset.univ.filter fun m : Fin n => (m, w) ∈ proposals
    have hnonempty : eligible.Nonempty := by
      obtain ⟨m, hm⟩ := h
      exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image eligible (p.womanRank w) hnonempty
    exact ⟨m, (Finset.mem_filter.mp hm).2,
      fun j hj => hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  have rejected (m w : Fin n) (hm : (m, w) ∈ proposals) (hw : ¬ wins m w) :
      ∃ j, (j, w) ∈ proposals ∧ p.womanRank w j < p.womanRank w m := by
    by_contra! noBetter
    exact hw ⟨hm, noBetter⟩
  -- An unmatched man would eventually propose to everyone. The winners would then
  -- give an injection from all women to men that omits him, which is impossible.
  have matched (m : Fin n) : ∃ w, wins m w := by
    by_contra! unmatched
    have proposedToAll (w : Fin n) : (m, w) ∈ proposals := by
      refine (measure (fun v : Fin n => (p.manRank m v).val)).wf.induction
        (C := fun v => (m, v) ∈ proposals) w ?_
      intro v ih
      apply (hproposal m v).mpr
      intro u hu
      exact rejected m u (ih u hu) (unmatched u)
    choose winner hwinner using fun w => winnerExists w ⟨m, proposedToAll w⟩
    have hinj : Function.Injective winner := by
      intro w v h
      exact uniqueWoman (h ▸ hwinner w) (hwinner v)
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj m
    exact unmatched w (hw ▸ hwinner w)
  choose partner hpartner using matched
  have hinj : Function.Injective partner := by
    intro m j h
    exact uniqueMan (h ▸ hpartner m) (hpartner j)
  let μ := Equiv.ofBijective partner hinj.bijective_of_finite
  unfold StableMarriage.numStableMatchings
  refine Fintype.card_pos_iff.mpr ⟨⟨μ, ?_⟩⟩
  intro m w hblock
  obtain ⟨_, hman, hwoman⟩ := hblock
  obtain ⟨j, hj, hrank⟩ := (hproposal m (μ m)).mp (hpartner m).1 w hman
  have hwinner : wins (μ.symm w) w := by
    have heq : partner (μ.symm w) = w := μ.apply_symm_apply w
    simpa only [heq] using hpartner (μ.symm w)
  exact (not_lt_of_ge ((hwinner.2 j hj).trans hrank.le)) hwoman
