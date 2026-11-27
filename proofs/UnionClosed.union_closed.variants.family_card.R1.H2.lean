import OMAReductions.R_UnionClosed_union_closed_variants_family_card_R1
import Mathlib

/-! # Structural incidence estimate for separating union-closed families

We prove step H2 of the Roberts-Simpson (2010) reduction for the union-closed
sets conjecture on families of small cardinality. Given a separating family F
on Fin m of size 2n + 1 whose maximum element frequency is n, we take C to be
the ground set together with the maximal sets in F omitting each coordinate.
-/

namespace UnionClosedFamilyCardH2Proof

open Finset UnionClosed
open scoped Classical

private lemma biUnion_id_mem {α : Type*} [DecidableEq α] {F s : Finset (Finset α)}
    (hc : IsUnionClosed F) (hs : s.Nonempty) (hsub : s ⊆ F) :
    s.biUnion id ∈ F := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | @insert X t _ ih =>
    by_cases ht : t.Nonempty
    · rw [Finset.biUnion_insert]
      exact hc X (hsub (Finset.mem_insert_self X t))
        (t.biUnion id) (ih ht ((Finset.subset_insert X t).trans hsub))
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst ht0
      simpa using hsub (Finset.mem_singleton_self X)

theorem h2_proof : OMA.R_UnionClosed_union_closed_variants_family_card_R1.H2 := by
  intro m n hm F ha hs hc hcard hmax hex _hrec
  have hm0 : 0 < m := by omega
  have hF_ne : F.Nonempty := by
    obtain ⟨X, hX, _⟩ := ha ⟨0, hm0⟩
    exact ⟨X, hX⟩
  have huniv_eq : F.biUnion id = (univ : Finset (Fin m)) := by
    ext i
    simp only [mem_biUnion, id_eq, mem_univ, iff_true]
    exact ha i
  have huniv_mem : (univ : Finset (Fin m)) ∈ F := by
    rw [← huniv_eq]
    exact biUnion_id_mem hc hF_ne Subset.rfl
  let O : Fin m → Finset (Finset (Fin m)) := fun i => F.filter (i ∉ ·)
  let M : Fin m → Finset (Fin m) := fun i => (O i).biUnion id
  have hO_ne : ∀ i : Fin m, (O i).Nonempty := by
    intro i
    have hsum : (F.filter (i ∈ ·)).card + (O i).card = F.card :=
      card_filter_add_card_filter_not (s := F) (p := fun X => i ∈ X)
    have hhi := hmax i
    exact card_pos.mp (by omega)
  have hM_mem : ∀ i : Fin m, M i ∈ F := fun i =>
    biUnion_id_mem hc (hO_ne i) (filter_subset _ _)
  have hM_notMem : ∀ i : Fin m, i ∉ M i := by
    intro i hi
    obtain ⟨X, hXO, hiX⟩ := mem_biUnion.mp hi
    exact (mem_filter.mp hXO).2 hiX
  have hM_sub_iff : ∀ (i : Fin m) {X : Finset (Fin m)}, X ∈ F → (i ∉ X ↔ X ⊆ M i) := by
    intro i X hXF
    constructor
    · intro hiX a haX
      exact mem_biUnion.mpr ⟨X, mem_filter.mpr ⟨hXF, hiX⟩, haX⟩
    · intro hsub hiX
      exact hM_notMem i (hsub hiX)
  have hnotMem_M_iff : ∀ i j : Fin m, j ∉ M i ↔ F.filter (j ∈ ·) ⊆ F.filter (i ∈ ·) := by
    intro i j
    constructor
    · intro hj X hX
      obtain ⟨hXF, hjX⟩ := mem_filter.mp hX
      refine mem_filter.mpr ⟨hXF, ?_⟩
      by_contra hiX
      exact hj (((hM_sub_iff i hXF).mp hiX) hjX)
    · intro hsub hj
      have hMi : M i ∈ F.filter (j ∈ ·) := mem_filter.mpr ⟨hM_mem i, hj⟩
      exact hM_notMem i (mem_filter.mp (hsub hMi)).2
  have hM_inj : Function.Injective M := by
    intro i j hij
    have hij1 : F.filter (i ∈ ·) ⊆ F.filter (j ∈ ·) :=
      (hnotMem_M_iff j i).mp (hij ▸ hM_notMem i)
    have hij2 : F.filter (j ∈ ·) ⊆ F.filter (i ∈ ·) :=
      (hnotMem_M_iff i j).mp (hij.symm ▸ hM_notMem j)
    exact hs (Subset.antisymm hij1 hij2)
  have hM_ne_univ : ∀ i : Fin m, M i ≠ univ := by
    intro i h
    exact hM_notMem i (h ▸ mem_univ i)
  let C : Finset (Finset (Fin m)) := insert univ (univ.image M)
  have hC_sub : C ⊆ F := by
    intro X hX
    rcases mem_insert.mp hX with rfl | hXim
    · exact huniv_mem
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hXim
      exact hM_mem i
  have hdom_max_bound : ∀ z : Fin m,
      (∀ i : Fin m, F.filter (z ∈ ·) ⊆ F.filter (i ∈ ·) → i = z) →
      m ≤ (F.filter (z ∈ ·)).card ∧ ((F \ C).filter (z ∈ ·)).card ≤ n - m := by
    intro z hzmax
    let K : Finset (Finset (Fin m)) := insert univ ((univ.erase z).image M)
    have huniv_notMem : (univ : Finset (Fin m)) ∉ (univ.erase z).image M := by
      intro h
      obtain ⟨i, _, hi⟩ := mem_image.mp h
      exact hM_ne_univ i hi
    have hK_card : K.card = m := by
      rw [card_insert_of_notMem huniv_notMem, card_image_of_injective _ hM_inj,
        card_erase_add_one (mem_univ z), card_univ, Fintype.card_fin]
    have hK_sub_C : K ⊆ C := by
      intro X hX
      rcases mem_insert.mp hX with rfl | hXim
      · exact mem_insert_self _ _
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hXim
        exact mem_insert_of_mem (mem_image_of_mem M (mem_univ i))
    have hK_sub_Fz : K ⊆ F.filter (z ∈ ·) := by
      intro X hX
      rcases mem_insert.mp hX with rfl | hXim
      · exact mem_filter.mpr ⟨huniv_mem, mem_univ z⟩
      · obtain ⟨i, hi_er, rfl⟩ := mem_image.mp hXim
        have hne : i ≠ z := (mem_erase.mp hi_er).1
        have hzMi : z ∈ M i := by
          by_contra hznot
          exact hne (hzmax i ((hnotMem_M_iff i z).mp hznot))
        exact mem_filter.mpr ⟨hM_mem i, hzMi⟩
    have hm_le_Fz : m ≤ (F.filter (z ∈ ·)).card := by
      have hKle := card_le_card hK_sub_Fz
      omega
    have hres_sub_Fz : (F \ C).filter (z ∈ ·) ⊆ F.filter (z ∈ ·) :=
      filter_subset_filter _ sdiff_subset
    have hdisj : Disjoint ((F \ C).filter (z ∈ ·)) K := by
      rw [disjoint_left]
      intro X hX1 hX2
      exact (mem_sdiff.mp (mem_filter.mp hX1).1).2 (hK_sub_C hX2)
    have hunion_le : (((F \ C).filter (z ∈ ·)) ∪ K).card ≤ (F.filter (z ∈ ·)).card :=
      card_le_card (union_subset hres_sub_Fz hK_sub_Fz)
    rw [card_union_of_disjoint hdisj, hK_card] at hunion_le
    have hz_le_n : (F.filter (z ∈ ·)).card ≤ n := hmax z
    exact ⟨hm_le_Fz, by omega⟩
  obtain ⟨x, hx⟩ := hex
  have hxmax : ∀ i : Fin m, F.filter (x ∈ ·) ⊆ F.filter (i ∈ ·) → i = x := by
    intro i hsub
    have hle : (F.filter (i ∈ ·)).card ≤ (F.filter (x ∈ ·)).card := hx ▸ hmax i
    exact (hs (eq_of_subset_of_card_le hsub hle)).symm
  have hm_le_n : m ≤ n := (hdom_max_bound x hxmax).1.trans (hx ▸ le_rfl)
  have hexcep : ((F.filter (x ∉ ·)) ∩ C).card ≤ 1 := by
    have hsub_sing : (F.filter (x ∉ ·)) ∩ C ⊆ {M x} := by
      intro X hX
      obtain ⟨hXO, hXC⟩ := mem_inter.mp hX
      have hxnot : x ∉ X := (mem_filter.mp hXO).2
      rcases mem_insert.mp hXC with rfl | hXim
      · exact absurd (mem_univ x) hxnot
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hXim
        have hix : i = x := hxmax i ((hnotMem_M_iff i x).mp hxnot)
        exact mem_singleton.mpr (congrArg M hix)
    exact (card_le_card hsub_sing).trans (by simp)
  have hresidual : ∀ y : Fin m, ((F \ C).filter (y ∈ ·)).card ≤ n - m := by
    intro y
    let Sy : Finset (Fin m) := univ.filter (fun w : Fin m => F.filter (y ∈ ·) ⊆ F.filter (w ∈ ·))
    have hSy_ne : Sy.Nonempty := ⟨y, mem_filter.mpr ⟨mem_univ y, Subset.rfl⟩⟩
    obtain ⟨z, hzSy, hzmax_card⟩ := Sy.exists_max_image (fun w => (F.filter (w ∈ ·)).card) hSy_ne
    have hyz : F.filter (y ∈ ·) ⊆ F.filter (z ∈ ·) := (mem_filter.mp hzSy).2
    have hzmax : ∀ i : Fin m, F.filter (z ∈ ·) ⊆ F.filter (i ∈ ·) → i = z := by
      intro i hzi
      have hiSy : i ∈ Sy := mem_filter.mpr ⟨mem_univ i, hyz.trans hzi⟩
      have hle : (F.filter (i ∈ ·)).card ≤ (F.filter (z ∈ ·)).card := hzmax_card i hiSy
      exact (hs (eq_of_subset_of_card_le hzi hle)).symm
    have hres_sub : (F \ C).filter (y ∈ ·) ⊆ (F \ C).filter (z ∈ ·) := by
      intro X hX
      obtain ⟨hXFC, hyX⟩ := mem_filter.mp hX
      have hzX : z ∈ X := (mem_filter.mp (hyz (mem_filter.mpr ⟨(mem_sdiff.mp hXFC).1, hyX⟩))).2
      exact mem_filter.mpr ⟨hXFC, hzX⟩
    exact (card_le_card hres_sub).trans (hdom_max_bound z hzmax).2
  exact ⟨x, hx, C, hC_sub, hm_le_n, hexcep, hresidual⟩

end UnionClosedFamilyCardH2Proof

theorem OMA.solution : OMA.R_UnionClosed_union_closed_variants_family_card_R1.H2 := by
  exact UnionClosedFamilyCardH2Proof.h2_proof
