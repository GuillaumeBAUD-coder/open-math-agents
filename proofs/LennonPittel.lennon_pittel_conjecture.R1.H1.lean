import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1

-- Step LennonPittel.lennon_pittel_conjecture.R1.H1: hypothesis H1 of reduction LennonPittel.lennon_pittel_conjecture.R1
-- Credit: @mattdorman
-- Every complete strict preference profile has a stable matching (Gale and Shapley).
-- Proof: a Tarski fixed point of the monotone map X ↦ (rejW (rejM X)ᶜ)ᶜ on sets of pairs gives a
-- stable partial matching X ∩ (rejM X)ᶜ (Fleiner's argument); with complete preferences a stable
-- partial matching is a complete stable matching (StableMarriage.isPartialStable_all_iff).

namespace OMA.LPH1

open StableMarriage

variable {n : ℕ} (p : Profile n)

/-- Pairs of `X` that the man rejects: he has a strictly better pair in `X`. -/
def rejM (X : Set (Fin n × Fin n)) : Set (Fin n × Fin n) :=
  {e | e ∈ X ∧ ∃ w', (e.1, w') ∈ X ∧ p.manRank e.1 w' < p.manRank e.1 e.2}

/-- Pairs of `Y` that the woman rejects: she has a strictly better pair in `Y`. -/
def rejW (Y : Set (Fin n × Fin n)) : Set (Fin n × Fin n) :=
  {e | e ∈ Y ∧ ∃ m', (m', e.2) ∈ Y ∧ p.womanRank e.2 m' < p.womanRank e.2 e.1}

lemma rejM_mono {X X' : Set (Fin n × Fin n)} (h : X ⊆ X') : rejM p X ⊆ rejM p X' := by
  rintro e ⟨he, w', hw', hlt⟩
  exact ⟨h he, w', h hw', hlt⟩

lemma rejW_mono {Y Y' : Set (Fin n × Fin n)} (h : Y ⊆ Y') : rejW p Y ⊆ rejW p Y' := by
  rintro e ⟨he, m', hm', hlt⟩
  exact ⟨h he, m', h hm', hlt⟩

/-- The monotone map whose fixed point yields a stable matching. -/
def F : Set (Fin n × Fin n) →o Set (Fin n × Fin n) where
  toFun X := (rejW p (rejM p X)ᶜ)ᶜ
  monotone' := by
    intro X X' h
    apply Set.compl_subset_compl.mpr
    apply rejW_mono
    exact Set.compl_subset_compl.mpr (rejM_mono p h)

lemma exists_best_woman (X : Set (Fin n × Fin n)) (m w : Fin n) (hw : (m, w) ∈ X) :
    ∃ w₀, (m, w₀) ∈ X ∧ ∀ w', (m, w') ∈ X → p.manRank m w₀ ≤ p.manRank m w' := by
  classical
  obtain ⟨w₀, hw₀, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun v => (m, v) ∈ X) (fun v => p.manRank m v) ⟨w, by simp [hw]⟩
  refine ⟨w₀, by simpa using hw₀, fun w' hw' => hmin w' (by simp [hw'])⟩

lemma exists_best_man (Y : Set (Fin n × Fin n)) (m w : Fin n) (hm : (m, w) ∈ Y) :
    ∃ m₀, (m₀, w) ∈ Y ∧ ∀ m', (m', w) ∈ Y → p.womanRank w m₀ ≤ p.womanRank w m' := by
  classical
  obtain ⟨m₀, hm₀, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun u => (u, w) ∈ Y) (fun u => p.womanRank w u) ⟨m, by simp [hm]⟩
  refine ⟨m₀, by simpa using hm₀, fun m' hm' => hmin m' (by simp [hm'])⟩

theorem exists_stable : ∃ M : PartialMatching n, IsPartialStable p (Admissibility.all n) M := by
  classical
  obtain ⟨X, hX⟩ : ∃ X, (rejW p (rejM p X)ᶜ)ᶜ = X := ⟨OrderHom.lfp (F p), OrderHom.map_lfp (F p)⟩
  have memX : ∀ e, e ∈ X ↔ e ∉ rejW p (rejM p X)ᶜ := fun e =>
    (Set.ext_iff.mp hX e).symm.trans (Set.mem_compl_iff _ _)
  -- the man's choice: a pair of `X` not rejected by its man is his best pair in `X`
  have manBest : ∀ e, e ∉ rejM p X → e ∈ X → ∀ w', (e.1, w') ∈ X →
      p.manRank e.1 e.2 ≤ p.manRank e.1 w' := by
    intro e he heX w' hw'
    by_contra hlt
    exact he ⟨heX, w', hw', lt_of_not_ge hlt⟩
  -- the woman's choice: a pair of `X` is her best pair in `(rejM X)ᶜ`
  have womanBest : ∀ e, e ∈ X → e ∉ rejM p X → ∀ m', (m', e.2) ∉ rejM p X →
      p.womanRank e.2 e.1 ≤ p.womanRank e.2 m' := by
    intro e heX heY m' hm'
    by_contra hlt
    exact (memX e).mp heX ⟨heY, m', hm', lt_of_not_ge hlt⟩
  let S : Finset (Fin n × Fin n) := Finset.univ.filter fun e => e ∈ X ∧ e ∉ rejM p X
  have memS : ∀ e, e ∈ S ↔ e ∈ X ∧ e ∉ rejM p X := fun e => by simp [S]
  let M : PartialMatching n :=
    { pairs := S
      left_inj := by
        rintro ⟨m, w⟩ ha ⟨m', w'⟩ hb hab
        simp only at hab
        subst hab
        obtain ⟨haX, haY⟩ := (memS _).mp ha
        obtain ⟨hbX, hbY⟩ := (memS _).mp hb
        have h1 := manBest (m, w) haY haX w' hbX
        have h2 := manBest (m, w') hbY hbX w haX
        have : p.manRank m w = p.manRank m w' := le_antisymm h1 h2
        rw [(p.manRank m).injective this]
      right_inj := by
        rintro ⟨m, w⟩ ha ⟨m', w'⟩ hb hab
        simp only at hab
        subst hab
        obtain ⟨haX, haY⟩ := (memS _).mp ha
        obtain ⟨hbX, hbY⟩ := (memS _).mp hb
        have h1 := womanBest (m, w) haX haY m' hbY
        have h2 := womanBest (m', w) hbX hbY m haY
        have : p.womanRank w m = p.womanRank w m' := le_antisymm h1 h2
        rw [(p.womanRank w).injective this] }
  refine ⟨M, fun _ _ => rfl, ?_⟩
  rintro m w ⟨-, hm, hw⟩
  have hmS : ∀ w', (m, w') ∈ S → p.manRank m w < p.manRank m w' := hm
  have hwS : ∀ m', (m', w) ∈ S → p.womanRank w m < p.womanRank w m' := hw
  by_cases hmwX : (m, w) ∈ X
  · by_cases hmwR : (m, w) ∈ rejM p X
    · obtain ⟨-, w', hw'X, hlt⟩ := hmwR
      obtain ⟨w₀, hw₀X, hw₀min⟩ := exists_best_woman p X m w hmwX
      have hw₀R : (m, w₀) ∉ rejM p X := by
        rintro ⟨-, v, hvX, hvlt⟩
        exact absurd (hw₀min v hvX) (not_le.mpr hvlt)
      have h1 := hmS w₀ ((memS _).mpr ⟨hw₀X, hw₀R⟩)
      have h2 := hw₀min w' hw'X
      exact absurd (lt_of_le_of_lt h2 hlt) (not_lt.mpr h1.le)
    · exact lt_irrefl _ (hmS w ((memS _).mpr ⟨hmwX, hmwR⟩))
  · have hrej : (m, w) ∈ rejW p (rejM p X)ᶜ := by
      by_contra h
      exact hmwX ((memX _).mpr h)
    obtain ⟨hmwY, m', hm'Y, hlt⟩ := hrej
    obtain ⟨m₀, hm₀Y, hm₀min⟩ := exists_best_man p (rejM p X)ᶜ m w hmwY
    have hm₀X : (m₀, w) ∈ X := by
      rw [memX]
      rintro ⟨-, u, huY, hult⟩
      exact absurd (hm₀min u huY) (not_le.mpr hult)
    have h1 := hwS m₀ ((memS _).mpr ⟨hm₀X, hm₀Y⟩)
    have h2 := hm₀min m' hm'Y
    exact absurd (lt_of_le_of_lt h2 hlt) (not_lt.mpr h1.le)

end OMA.LPH1

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  classical
  intro n p
  obtain ⟨M, hM⟩ := OMA.LPH1.exists_stable p
  obtain ⟨μ, ⟨-, hμ⟩, -⟩ := (StableMarriage.isPartialStable_all_iff p M).mp hM
  unfold StableMarriage.numStableMatchings
  exact Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩
