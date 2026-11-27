import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1
open StableMarriage
namespace MatchingExistence
variable {n : ℕ} (p : Profile n)

def refused (P : Set (Fin n × Fin n)) (m w : Fin n) : Prop :=
  ∃ t, (t,w) ∈ P ∧ p.womanRank w t < p.womanRank w m

def offers : Set (Fin n × Fin n) →o Set (Fin n × Fin n) where
  toFun P := {a | ∀ w, p.manRank a.1 w < p.manRank a.1 a.2 → refused p P a.1 w}
  monotone' := by
    intro P Q h a ha w hw
    obtain ⟨t,ht,lt⟩ := ha w hw
    exact ⟨t,h ht,lt⟩

lemma stable : ∃ μ : Matching n, IsStable p μ := by
  classical
  let P := (offers p).lfp
  have hP : ∀ m w, (m,w) ∈ P ↔ ∀ v, p.manRank m v < p.manRank m w → refused p P m v := by
    intro m w
    change (m,w) ∈ P ↔ (m,w) ∈ offers p P
    rw [(offers p).isLeast_lfp.1]
  let ok (m w : Fin n) := (m,w) ∈ P ∧ ¬ refused p P m w
  have man (m w v : Fin n) (hw : ok m w) (hv : ok m v) : w = v := by
    apply (p.manRank m).injective
    apply le_antisymm <;> by_contra! h
    · exact hv.2 ((hP m w).1 hw.1 v h)
    · exact hw.2 ((hP m v).1 hv.1 w h)
  have woman (w m t : Fin n) (hm : ok m w) (ht : ok t w) : m = t := by
    apply (p.womanRank w).injective
    apply le_antisymm <;> by_contra! h
    · exact hm.2 ⟨t, ht.1, h⟩
    · exact ht.2 ⟨m, hm.1, h⟩
  have exists_man (m : Fin n) : ∃ w, ok m w := by
    by_contra! no
    have all (w : Fin n) : refused p P m w := by
      by_contra h
      obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter (fun v => ¬ refused p P m v)) (p.manRank m)
        ⟨w,by simpa using h⟩
      apply no v
      refine ⟨(hP m v).2 ?_, (Finset.mem_filter.mp hv).2⟩
      intro u hu
      by_contra hu'
      exact hu.not_ge (hmin u (by simpa using hu'))
    have chosen (w : Fin n) : ∃ t, ok t w := by
      obtain ⟨u,hu,_⟩ := all w
      obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter (fun t => (t,w) ∈ P)) (p.womanRank w) ⟨u,by simpa using hu⟩
      refine ⟨t,(Finset.mem_filter.mp ht).2, ?_⟩
      rintro ⟨v,hv,hlt⟩
      exact hlt.not_ge (hmin v (by simpa using hv))
    choose f hf using chosen
    have inj : Function.Injective f := by
      intro w v eq
      exact man _ _ _ (hf w) (eq.symm ▸ hf v)
    obtain ⟨w,hw⟩ := (Finite.surjective_of_injective inj) m
    exact no w (hw ▸ hf w)
  choose f hf using exists_man
  have inj : Function.Injective f := by
    intro m t eq
    exact woman _ _ _ (hf m) (eq.symm ▸ hf t)
  let μ := Equiv.ofBijective f ⟨inj, Finite.surjective_of_injective inj⟩
  refine ⟨μ, ?_⟩
  rintro m w ⟨_,hm,hw⟩
  have hc : ok (μ.symm w) w := by simpa [show f = μ from rfl] using hf (μ.symm w)
  obtain ⟨v,hv,hmv⟩ := (hP m (f m)).1 (hf m).1 w hm
  exact hc.2 ⟨v,hv,hmv.trans hw⟩
end MatchingExistence

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  classical
  intro n p
  obtain ⟨μ,hμ⟩ := MatchingExistence.stable p
  exact Fintype.card_pos_iff.mpr ⟨⟨μ,hμ⟩⟩
