import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5

-- Problem: Group structure via subgroup counts
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2604.08040/Conjecture5_5.lean:120 (declaration Arxiv.«2604.08040».cyc_alternatingGroup_five)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P15

abbrev A5 := alternatingGroup (Fin 5)

def P5 (g : A5) : Finset A5 := {1, g, g ^ 2, g ^ 3, g ^ 4}

lemma ord30 : ∀ g : A5, g ^ 30 = 1 := by decide +kernel

lemma pow_mem_P5 : ∀ g : A5, ∀ m : Fin 30, g ^ (m : ℕ) ∈ P5 g := by decide +kernel

lemma card_image : (Finset.univ.image P5).card = 32 := by decide +kernel

lemma mem_zp_iff (g h : A5) : h ∈ Subgroup.zpowers g ↔ h ∈ P5 g := by
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have h30z : g ^ (30 : ℤ) = 1 := by
      rw [show (30 : ℤ) = ((30 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact ord30 g
    have h0 : 0 ≤ k % 30 := Int.emod_nonneg _ (by norm_num)
    have hlt : k % 30 < 30 := Int.emod_lt_of_pos _ (by norm_num)
    have hm : (((k % 30).toNat : ℕ) : ℤ) = k % 30 := Int.toNat_of_nonneg h0
    have hlt' : (k % 30).toNat < 30 := by
      have h1 : (((k % 30).toNat : ℕ) : ℤ) < 30 := by rw [hm]; exact hlt
      exact_mod_cast h1
    have key : g ^ k = g ^ ((k % 30).toNat) := by
      rw [zpow_eq_zpow_emod k h30z, ← zpow_natCast, hm]
    rw [key]
    exact pow_mem_P5 g ⟨(k % 30).toNat, hlt'⟩
  · intro hh
    have hh' := hh
    simp only [P5, Finset.mem_insert, Finset.mem_singleton] at hh'
    rcases hh' with h | h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers g
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 2
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 3
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) 4

lemma coe_eq (g : A5) : ((Subgroup.zpowers g : Subgroup A5) : Set A5) = ((P5 g : Finset A5) : Set A5) := by
  ext h
  exact mem_zp_iff g h

lemma gen_of_cyclic (H : Subgroup A5) (hH : IsCyclic H) : ∃ g : A5, Subgroup.zpowers g = H := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨(x : A5), ?_⟩
  ext y
  constructor
  · intro hy
    exact (Subgroup.zpowers_le.mpr x.2) hy
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨y, hy⟩)
    have h2 := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow] at h2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩

theorem main : Arxiv.«2604.08040».cyc (alternatingGroup (Fin 5)) = 32 := by
  show Nat.card {H : Subgroup A5 // IsCyclic H} = 32
  have hT : Nat.card {H : Subgroup A5 // IsCyclic H} = ({H : Subgroup A5 | IsCyclic H} : Set (Subgroup A5)).ncard :=
    (Nat.card_coe_set_eq _)
  have himg : ((SetLike.coe : Subgroup A5 → Set A5) '' {H : Subgroup A5 | IsCyclic H})
      = (fun S : Finset A5 => (S : Set A5)) '' ((Finset.univ.image P5 : Finset (Finset A5)) : Set (Finset A5)) := by
    ext s
    constructor
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨g, rfl⟩ := gen_of_cyclic H hH
      refine ⟨P5 g, ?_, ?_⟩
      · exact Finset.mem_coe.2 (Finset.mem_image_of_mem P5 (Finset.mem_univ g))
      · exact (coe_eq g).symm
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hS)
      refine ⟨Subgroup.zpowers g, ?_, coe_eq g⟩
      show IsCyclic (Subgroup.zpowers g)
      exact inferInstance
  have hinj : Function.Injective (fun S : Finset A5 => (S : Set A5)) := Finset.coe_injective
  have hsub : ({H : Subgroup A5 | IsCyclic H} : Set (Subgroup A5)).ncard
      = ((SetLike.coe : Subgroup A5 → Set A5) '' {H : Subgroup A5 | IsCyclic H}).ncard :=
    (Set.ncard_image_of_injective _ SetLike.coe_injective).symm
  rw [hT, hsub, himg, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, card_image]

end OMA.P15

theorem OMA.solution : type_of% @Arxiv.«2604.08040».cyc_alternatingGroup_five := by
  exact OMA.P15.main
