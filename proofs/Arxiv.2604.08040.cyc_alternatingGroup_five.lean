import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5

/-!
# Counting the cyclic subgroups of A₅

Based on the original finite certificate proof by @ldy985. Cyclic subgroup generation
and membership use Mathlib's standard equivalences. The two computational certificates
are Prop-valued definitions so Lean elaborates them sequentially.
-/

namespace OMA.P15

abbrev A5 := alternatingGroup (Fin 5)

def P5 (g : A5) : Finset A5 := {1, g, g ^ 2, g ^ 3, g ^ 4}

def small_order : ∀ g : A5, g ^ 1 = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

lemma order_le (g : A5) : orderOf g ≤ 5 := by
  rcases small_order g with h | h | h | h
  all_goals exact (orderOf_le_of_pow_eq_one (by decide) h).trans (by decide)

lemma pow_mem_P5 (g : A5) (m : Fin 5) : g ^ (m : ℕ) ∈ P5 g := by
  fin_cases m <;> simp [P5]

def card_image : (Finset.univ.image P5).card = 32 := by decide +kernel

lemma mem_zp_iff (g h : A5) : h ∈ Subgroup.zpowers g ↔ h ∈ P5 g := by
  constructor
  · intro hh
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hh)
    exact pow_mem_P5 g ⟨k, (Finset.mem_range.mp hk).trans_le
      (order_le g)⟩
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
  exact (H.isCyclic_iff_exists_zpowers_eq_top).mp hH

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
