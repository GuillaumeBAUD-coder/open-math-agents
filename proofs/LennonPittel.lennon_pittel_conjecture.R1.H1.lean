import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1
import Mathlib

-- Step LennonPittel.lennon_pittel_conjecture.R1.H1: hypothesis H1 of reduction LennonPittel.lennon_pittel_conjecture.R1
-- Credit: @ivillar
-- H1 := ∀ n (p : StableMarriage.Profile n), 0 < StableMarriage.numStableMatchings p
--
-- This is the Gale–Shapley theorem (every complete strict profile has a stable matching),
-- proved via a history-free invariant of men-proposing deferred acceptance: R is the set
-- of rejected pairs, each man proposes to his best woman not in R, and every rejection is
-- justified by a current proposer the woman prefers. While some woman receives two
-- proposals, reject the worse one (R grows strictly). At the end each man proposes (a man
-- rejected by all n women would give an injection of the n women into the other n - 1 men),
-- proposals are injective hence a bijection, and the invariant rules out blocking pairs.

namespace OMA.GaleShapley

open StableMarriage

variable {n : ℕ}

/-- Man `m` currently proposes to `w`: the best woman who has not rejected him. -/
def Proposes (p : Profile n) (R : Finset (Fin n × Fin n)) (m w : Fin n) : Prop :=
  (m, w) ∉ R ∧ ∀ w', (m, w') ∉ R → p.manRank m w ≤ p.manRank m w'

/-- Every rejection of `m` by `w` is justified by a current proposer whom `w` prefers. -/
def Inv (p : Profile n) (R : Finset (Fin n × Fin n)) : Prop :=
  ∀ m w, (m, w) ∈ R → ∃ m', Proposes p R m' w ∧ p.womanRank w m' < p.womanRank w m

lemma proposes_unique {p : Profile n} {R : Finset (Fin n × Fin n)} {m w₁ w₂ : Fin n}
    (h₁ : Proposes p R m w₁) (h₂ : Proposes p R m w₂) : w₁ = w₂ :=
  (p.manRank m).injective (le_antisymm (h₁.2 w₂ h₂.1) (h₂.2 w₁ h₁.1))

lemma exists_proposes {p : Profile n} {R : Finset (Fin n × Fin n)} {m w : Fin n}
    (hw : (m, w) ∉ R) : ∃ w', Proposes p R m w' := by
  classical
  obtain ⟨w', hw', hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun x => (m, x) ∉ R)
    (fun x => p.manRank m x) ⟨w, by simpa using hw⟩
  exact ⟨w', (Finset.mem_filter.mp hw').2, fun x hx => hmin x (by simpa using hx)⟩

lemma proposes_insert {p : Profile n} {R : Finset (Fin n × Fin n)} {m m₂ w x : Fin n}
    (hm : m ≠ m₂) : Proposes p (insert (m₂, w) R) m x ↔ Proposes p R m x := by
  have key : ∀ y, (m, y) ∈ insert (m₂, w) R ↔ (m, y) ∈ R := by
    intro y
    simp [Finset.mem_insert, Prod.ext_iff, hm]
  simp only [Proposes, key]

lemma inv_insert {p : Profile n} {R : Finset (Fin n × Fin n)} (hR : Inv p R) {w m₁ m₂ : Fin n}
    (h₁ : Proposes p R m₁ w) (h₂ : Proposes p R m₂ w) (hne : m₁ ≠ m₂)
    (hlt : p.womanRank w m₁ < p.womanRank w m₂) : Inv p (insert (m₂, w) R) := by
  intro m x hmx
  rcases Finset.mem_insert.mp hmx with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨hm, hx⟩ := h
    subst hm hx
    exact ⟨m₁, (proposes_insert hne).mpr h₁, hlt⟩
  · obtain ⟨m', hm', hlt'⟩ := hR m x h
    by_cases hm'2 : m' = m₂
    · subst hm'2
      have hx : x = w := proposes_unique hm' h₂
      subst hx
      exact ⟨m₁, (proposes_insert hne).mpr h₁, lt_trans hlt hlt'⟩
    · exact ⟨m', (proposes_insert hm'2).mpr hm', hlt'⟩

lemma exists_stable_of_inv (p : Profile n) :
    ∀ k : ℕ, ∀ R : Finset (Fin n × Fin n), (Finset.univ \ R).card = k → Inv p R →
      ∃ μ : Matching n, IsStable p μ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro R hk hR
  by_cases hstep : ∃ w m₁ m₂, m₁ ≠ m₂ ∧ Proposes p R m₁ w ∧ Proposes p R m₂ w
  · obtain ⟨w, a, b, hab, ha, hb⟩ := hstep
    have key : ∃ m₁ m₂, m₁ ≠ m₂ ∧ Proposes p R m₁ w ∧ Proposes p R m₂ w ∧
        p.womanRank w m₁ < p.womanRank w m₂ := by
      rcases lt_or_gt_of_ne (fun h => hab ((p.womanRank w).injective h)) with h | h
      · exact ⟨a, b, hab, ha, hb, h⟩
      · exact ⟨b, a, hab.symm, hb, ha, h⟩
    obtain ⟨m₁, m₂, hne, h₁, h₂, hlt⟩ := key
    have hnot : (m₂, w) ∉ R := h₂.1
    have hcard : (Finset.univ \ insert (m₂, w) R).card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff (le_refl _)
        (Finset.subset_insert _ _))]
      exact ⟨(m₂, w), by simp [hnot], by simp⟩
    exact ih _ hcard _ rfl (inv_insert hR h₁ h₂ hne hlt)
  · push Not at hstep
    have hall : ∀ m, ∃ w, Proposes p R m w := by
      intro m
      by_contra hno
      push Not at hno
      have hrej : ∀ w, (m, w) ∈ R := by
        intro w
        by_contra hw
        obtain ⟨w', hw'⟩ := exists_proposes (p := p) hw
        exact hno w' hw'
      choose f hf using fun w => hR m w (hrej w)
      have hfinj : Function.Injective f := by
        intro w₁ w₂ h
        have h1 := (hf w₁).1
        rw [h] at h1
        exact proposes_unique h1 (hf w₂).1
      have hfne : ∀ w, f w ≠ m := by
        intro w h
        have h2 := (hf w).2
        rw [h] at h2
        exact lt_irrefl _ h2
      classical
      have hle : (Finset.univ : Finset (Fin n)).card ≤ (Finset.univ.erase m).card := by
        apply Finset.card_le_card_of_injOn f
        · intro w _
          simp [hfne w]
        · intro a _ b _ h
          exact hfinj h
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin] at hle
      have hpos : 0 < n := Fin.pos m
      omega
    choose g hg using hall
    have hginj : Function.Injective g := by
      intro a b h
      by_contra hab
      exact hstep (g a) a b hab (hg a) (by rw [h]; exact hg b)
    have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp hginj
    refine ⟨Equiv.ofBijective g hgbij, ?_⟩
    intro m w hblock
    simp only [IsBlockingPair] at hblock
    obtain ⟨_, hm, hw⟩ := hblock
    have hμ : ∀ x, (Equiv.ofBijective g hgbij) x = g x := fun x => rfl
    rw [hμ] at hm
    have hrej : (m, w) ∈ R := by
      by_contra hnot
      exact absurd hm (not_lt.mpr ((hg m).2 w hnot))
    obtain ⟨m', hm', hlt⟩ := hR m w hrej
    have hgm' : g m' = w := proposes_unique (hg m') hm'
    have hs : (Equiv.ofBijective g hgbij).symm w = m' := by
      rw [Equiv.symm_apply_eq, hμ]
      exact hgm'.symm
    rw [hs] at hw
    exact lt_asymm hlt hw

theorem exists_stable (p : Profile n) : ∃ μ : Matching n, IsStable p μ :=
  exists_stable_of_inv p _ ∅ rfl (fun m w h => by simp at h)

end OMA.GaleShapley

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  unfold OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1
  intro n p
  obtain ⟨μ, hμ⟩ := OMA.GaleShapley.exists_stable p
  classical
  unfold StableMarriage.numStableMatchings
  convert Fintype.card_pos_iff.mpr ⟨(⟨μ, hμ⟩ : {μ // StableMarriage.IsStable p μ})⟩
