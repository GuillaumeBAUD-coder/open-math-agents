import FormalConjectures.ErdosProblems.«19»

-- Reduction Erdos19.erdos_19.variants.large_n.R1 of Erdős Problem 19 — large n
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- The clique configuration is dualised: shared vertices become edges of a linear hypergraph on
-- Fin n, uncovered pairs are adjoined to get a pairwise balanced design (PBD), and an n-edge-colouring
-- of the PBD is pulled back. H1: PBDs whose edges all have size at most sqrt n.
-- H2: PBDs having an edge of size above sqrt n.

namespace OMA.R_Erdos19_erdos_19_variants_large_n_R1

open Filter

def H1 : Prop :=
  ∀ᶠ n in Filter.atTop, ∀ K : Finset (Finset (Fin n)),
    (∀ A ∈ K, 2 ≤ A.card ∧ A.card * A.card ≤ n) →
    (∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →
    ∃ c : {x // x ∈ K} → Fin n, ∀ A B : {x // x ∈ K}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

def H2 : Prop :=
  ∀ᶠ n in Filter.atTop, ∀ K : Finset (Finset (Fin n)),
    (∀ A ∈ K, 2 ≤ A.card) → (∃ A ∈ K, n < A.card * A.card) →
    (∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →
    ∃ c : {x // x ∈ K} → Fin n, ∀ A B : {x // x ∈ K}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

section

open Finset

theorem edgeColoring_mono {n : ℕ} {H K : Finset (Finset (Fin n))}
    (hK : (∃ c : {x // x ∈ K} → Fin n, ∀ A B : {x // x ∈ K}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B)) (hHK : H ⊆ K) :
    (∃ c : {x // x ∈ H} → Fin n, ∀ A B : {x // x ∈ H}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B) := by
  obtain ⟨c, hc⟩ := hK
  let incl (A : H) : K := ⟨A.val, hHK A.property⟩
  refine ⟨fun A => c (incl A), fun A B hne h => hc (incl A) (incl B) ?_ h⟩
  exact fun heq => hne (Subtype.ext (congrArg (fun e : K => e.val) heq))

theorem exists_pairwiseBalanced_superset {n : ℕ} (H : Finset (Finset (Fin n)))
    (hsize : ∀ A ∈ H, 2 ≤ A.card) (hlin : (∀ ⦃A B⦄, A ∈ H → B ∈ H → ∀ ⦃i j : Fin n⦄, i ≠ j → i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B)) :
    ∃ K, H ⊆ K ∧ ((∀ A ∈ K, 2 ≤ A.card) ∧ ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) := by
  classical
  let P := ((univ : Finset (Fin n)).powersetCard 2).filter
    (fun e => ¬ ∃ A ∈ H, e ⊆ A)
  refine ⟨H ∪ P, subset_union_left, ?_, ?_⟩
  · intro A hA
    rcases mem_union.mp hA with hA | hA
    · exact hsize A hA
    · exact le_of_eq (mem_powersetCard.mp (mem_filter.mp hA).1).2.symm
  · intro i j hij
    have hcard : ({i, j} : Finset (Fin n)).card = 2 := card_pair hij
    have eq_pair {B : Finset (Fin n)} (hB : B ∈ P) (hi : i ∈ B) (hj : j ∈ B) :
        B = {i, j} := by
      have hs : ({i, j} : Finset (Fin n)) ⊆ B :=
        insert_subset hi (singleton_subset_iff.mpr hj)
      exact (eq_of_subset_of_card_le hs
        ((mem_powersetCard.mp (mem_filter.mp hB).1).2.trans hcard.symm).le).symm
    by_cases hcovered : ∃ A ∈ H, i ∈ A ∧ j ∈ A
    · obtain ⟨A, hA, hiA, hjA⟩ := hcovered
      refine ⟨A, ⟨mem_union_left _ hA, hiA, hjA⟩, ?_⟩
      rintro B ⟨hB, hiB, hjB⟩
      rcases mem_union.mp hB with hB | hB
      · exact hlin hB hA hij hiB hjB hiA hjA
      · have hmiss := (mem_filter.mp hB).2
        rw [eq_pair hB hiB hjB] at hmiss
        exact (hmiss ⟨A, hA, insert_subset hiA (singleton_subset_iff.mpr hjA)⟩).elim
    · have hpair : ({i, j} : Finset (Fin n)) ∈ P := by
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, ?_⟩
        rintro ⟨A, hA, hsub⟩
        exact hcovered ⟨A, hA, hsub (by simp), hsub (by simp)⟩
      refine ⟨{i, j}, ⟨mem_union_right _ hpair, by simp, by simp⟩, ?_⟩
      rintro B ⟨hB, hiB, hjB⟩
      rcases mem_union.mp hB with hB | hB
      · exact (hcovered ⟨B, hB, hiB, hjB⟩).elim
      · exact eq_pair hB hiB hjB

theorem colorable_of_pairwiseBalanced {V : Type} {n : ℕ} (C : Erdos19.EFLConfig V n)
    (hdesign : ∀ K : Finset (Finset (Fin n)), ((∀ A ∈ K, 2 ≤ A.card) ∧ ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →
      (∃ c : {x // x ∈ K} → Fin n, ∀ A B : {x // x ∈ K}, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B)) :
    C.graph.Colorable n := by
  classical
  let S (v : V) : Finset (Fin n) := univ.filter (fun i => v ∈ C.A i)
  let H := C.sharedSet.image S
  have memS (v : V) (i : Fin n) : i ∈ S v ↔ v ∈ C.A i := by simp [S]
  have shared (v : V) : v ∈ C.sharedSet ↔ C.IsShared v := by
    refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨?_, h⟩⟩
    obtain ⟨i, hi⟩ := C.cover v
    exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
  have same {u v : V} {i j : Fin n} (hij : i ≠ j)
      (hiu : i ∈ S u) (hju : j ∈ S u) (hiv : i ∈ S v) (hjv : j ∈ S v) : u = v :=
    card_le_one.mp (C.inter_le i j hij) u
      (mem_inter.mpr ⟨(memS _ _).mp hiu, (memS _ _).mp hju⟩) v
      (mem_inter.mpr ⟨(memS _ _).mp hiv, (memS _ _).mp hjv⟩)
  have hsize : ∀ A ∈ H, 2 ≤ A.card := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hA
    obtain ⟨i, j, hij, hi, hj⟩ := (shared v).mp hv
    exact one_lt_card.mpr ⟨i, (memS _ _).mpr hi, j, (memS _ _).mpr hj, hij⟩
  have hlin : (∀ ⦃A B⦄, A ∈ H → B ∈ H → ∀ ⦃i j : Fin n⦄, i ≠ j → i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B) := by
    intro A B hA hB i j hij hiA hjA hiB hjB
    obtain ⟨u, _, rfl⟩ := mem_image.mp hA
    obtain ⟨v, _, rfl⟩ := mem_image.mp hB
    exact congrArg S (same hij hiA hjA hiB hjB)
  obtain ⟨K, hHK, hK⟩ := exists_pairwiseBalanced_superset H hsize hlin
  obtain ⟨c, hc⟩ := edgeColoring_mono (hdesign K hK) hHK
  let col (v : V) : Fin n :=
    if h : v ∈ C.sharedSet then c ⟨S v, mem_image_of_mem S h⟩
    else (C.cover v).choose
  apply C.colorable_of_sharedColoring col
  intro k u v hku hkv hu hv heq
  have hmU := (shared u).mpr hu
  have hmV := (shared v).mpr hv
  let A : H := ⟨S u, mem_image_of_mem S hmU⟩
  let B : H := ⟨S v, mem_image_of_mem S hmV⟩
  have hAB : A = B := by
    by_contra hne
    apply hc A B hne ⟨k, mem_inter.mpr ⟨(memS _ _).mpr hku, (memS _ _).mpr hkv⟩⟩
    simpa only [col, dif_pos hmU, dif_pos hmV] using heq
  have hs : S u = S v := congrArg (fun e : H => e.val) hAB
  obtain ⟨i, j, hij, hi, hj⟩ := hu
  have his := (memS u i).mpr hi
  have hjs := (memS u j).mpr hj
  exact same hij his hjs (hs ▸ his) (hs ▸ hjs)

end

theorem main : H1 → H2 → type_of% @Erdos19.erdos_19.variants.large_n := by
  intro h1 h2
  filter_upwards [h1, h2] with n hn1 hn2 V C
  have hcol : C.graph.Colorable n := by
    apply colorable_of_pairwiseBalanced C
    intro K hK
    by_cases hbig : ∃ A ∈ K, n < A.card * A.card
    · exact hn2 K hK.1 hbig hK.2
    · push_neg at hbig
      exact hn1 K (fun A hA => ⟨hK.1 A hA, hbig A hA⟩) hK.2
  exact le_antisymm hcol.chromaticNumber_le C.le_chromaticNumber

end OMA.R_Erdos19_erdos_19_variants_large_n_R1
