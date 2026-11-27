import FormalConjectures.ErdosProblems.«21»

-- Credit: @zarnab222-dev
namespace OMA.R_Erdos21_erdos_21_variants_small_values_R1

open Erdos21

private theorem minimum_eq {n m : ℕ}
    (hw : ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m)
    (hl : ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily n F → m ≤ F.card) : f n = m := by
  apply IsLeast.csInf_eq
  exact ⟨hw, fun k ⟨F, hF, hcard⟩ => hcard ▸ hl F hF⟩

private theorem order_one : f 1 = 1 := by
  apply minimum_eq
  · refine ⟨{{0}}, ⟨by decide, by decide, ?_⟩, by decide⟩
    intro S hS
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    exact ⟨{0}, by decide, by simp⟩
  · intro F hF
    obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
    exact Finset.card_pos.mpr ⟨A, hA⟩

private theorem order_two : f 2 = 3 := by
  apply minimum_eq
  · refine ⟨{{0, 1}, {0, 2}, {1, 2}}, ⟨by decide, by decide, ?_⟩, by decide⟩
    intro S hS
    obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hS
    by_cases h0 : v = 0
    · exact ⟨{1, 2}, by decide, Finset.disjoint_of_subset_left hv (by simp [h0])⟩
    by_cases h1 : v = 1
    · exact ⟨{0, 2}, by decide, Finset.disjoint_of_subset_left hv (by simp [h1])⟩
    · exact ⟨{0, 1}, by decide, Finset.disjoint_of_subset_left hv (by simp [h0, h1])⟩
  · intro F hF
    obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hF.1 A hA]; decide)
    obtain ⟨B, hB, hdisB⟩ := hF.2.2 {x} (by simp)
    have hAB : A ≠ B := fun h => Finset.disjoint_singleton_left.mp hdisB (h ▸ hx)
    obtain ⟨y, hy⟩ := hF.2.1 A hA B hB
    obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨C, hC, hdisC⟩ := hF.2.2 {y} (by simp)
    have hyC := Finset.disjoint_singleton_left.mp hdisC
    have hAC : A ≠ C := fun h => hyC (h ▸ hyA)
    have hBC : B ≠ C := fun h => hyC (h ▸ hyB)
    calc
      3 = ({A, B, C} : Finset (Finset ℕ)).card := by simp [hAB, hAC, hBC]
      _ ≤ F.card := Finset.card_le_card (by
        rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hA, hB, hC⟩)

/-- In an intersecting family, any subfamily of at most two edges has a common vertex. -/
private theorem pair_cover {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 3 F)
    (hG : G ⊆ F) (hs : G.card ≤ 2) : ∃ y : ℕ, ∀ E ∈ G, y ∈ E := by
  by_cases ht : G.card = 2
  · obtain ⟨A, B, _, rfl⟩ := Finset.card_eq_two.mp ht
    obtain ⟨y, hy⟩ := hF.2.1 A (hG (by simp)) B (hG (by simp))
    refine ⟨y, ?_⟩
    simpa using Finset.mem_inter.mp hy
  by_cases ho : G.card = 1
  · obtain ⟨A, rfl⟩ := Finset.card_eq_one.mp ho
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hF.1 A (hG (by simp))]; decide)
    exact ⟨y, by simpa using hy⟩
  have hempty : G = ∅ := Finset.card_eq_zero.mp (by omega)
  exact ⟨0, by simp [hempty]⟩

private theorem lower_three (F : Finset (Finset ℕ)) (hF : IsErdosLovaszFamily 3 F) :
    6 ≤ F.card := by
  by_contra! hsmall
  -- At least three edges avoid each vertex, or a second vertex covers the rest.
  have miss (x : ℕ) : 3 ≤ (F.filter fun E => x ∉ E).card := by
    by_contra! h
    obtain ⟨y, hy⟩ := pair_cover hF (Finset.filter_subset _ F) (by omega : (F.filter fun E => x ∉ E).card ≤ 2)
    obtain ⟨E, hE, hd⟩ := hF.2.2 {x, y} Finset.card_le_two
    have hx : x ∉ E := fun hxE => Finset.disjoint_left.mp hd (by simp) hxE
    exact Finset.disjoint_left.mp hd (by simp : y ∈ ({x, y} : Finset ℕ)) (hy E (Finset.mem_filter.mpr ⟨hE, hx⟩))
  have degree (x : ℕ) : (F.filter fun E => x ∈ E).card ≤ 2 := by
    have := F.card_filter_add_card_filter_not (fun E => x ∈ E)
    have := miss x
    omega
  obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
  -- Each vertex of A can account for at most one further edge meeting A.
  let others (x : ℕ) := (F.erase A).filter fun E => x ∈ E
  have hcap (x : ℕ) (hx : x ∈ A) : (others x).card ≤ 1 := by
    rw [show others x = (F.filter fun E => x ∈ E).erase A from Finset.filter_erase ..,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hA, hx⟩)]
    have := degree x
    omega
  have hsub : F.erase A ⊆ A.biUnion others := by
    intro E hE
    obtain ⟨y, hy⟩ := hF.2.1 A hA E (Finset.mem_of_mem_erase hE)
    exact Finset.mem_biUnion.mpr ⟨y, (Finset.mem_inter.mp hy).1,
      Finset.mem_filter.mpr ⟨hE, (Finset.mem_inter.mp hy).2⟩⟩
  have hbound := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul A others 1 hcap)
  rw [Finset.card_erase_of_mem hA, hF.1 A hA, mul_one] at hbound
  -- Two distinct intersecting edges supply a vertex meeting at least two edges.
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hF.1 A hA]; decide)
  obtain ⟨B, hB, hdis⟩ := hF.2.2 {a} (by simp)
  have hAB : A ≠ B := fun he => Finset.disjoint_singleton_left.mp hdis (he ▸ ha)
  obtain ⟨z, hz⟩ := hF.2.1 A hA B hB
  have hp : ({A, B} : Finset (Finset ℕ)) ⊆ F.filter (fun E => z ∈ E) := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_filter.mpr ⟨hA, (Finset.mem_inter.mp hz).1⟩,
      Finset.mem_filter.mpr ⟨hB, (Finset.mem_inter.mp hz).2⟩⟩
  have hdeg := Finset.card_le_card hp
  simp only [Finset.card_pair hAB] at hdeg
  have := F.card_filter_add_card_filter_not (fun E => z ∈ E)
  have := miss z
  omega

-- The order-four and order-five families use the incidence matrices in
-- János Barát, arXiv:2011.04444, sections 6.1 and 6.2.
private theorem verify_family {n : ℕ} {F : Finset (Finset ℕ)} (V : Finset ℕ)
    (hsize : n - 1 ≤ V.card) (hinside : ∀ A ∈ F, A ⊆ V)
    (huniform : ∀ A ∈ F, A.card = n)
    (hpairs : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hmiss : ∀ T ∈ V.powersetCard (n - 1), ∃ A ∈ F, Disjoint T A) :
    IsErdosLovaszFamily n F := by
  refine ⟨huniform, hpairs, ?_⟩
  intro S hS
  obtain ⟨T, hST, hTV, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.inter_subset_right : S ∩ V ⊆ V)
    ((Finset.card_le_card Finset.inter_subset_left).trans hS) hsize
  obtain ⟨A, hA, hd⟩ := hmiss T (Finset.mem_powersetCard.mpr ⟨hTV, hcard⟩)
  refine ⟨A, hA, Finset.disjoint_left.mpr ?_⟩
  intro x hxS hxA
  exact Finset.disjoint_left.mp hd (hST (Finset.mem_inter.mpr ⟨hxS, hinside A hA hxA⟩)) hxA

-- Six lines of the Fano plane remain after deleting a line.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem witness_three :
    ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily 3 F ∧ F.card = 6 := by
  refine ⟨{{1, 3, 5},
      {0, 3, 4},
      {2, 3, 6},
      {0, 1, 2},
      {1, 4, 6},
      {0, 5, 6}}, ?_, by decide +kernel⟩
  apply verify_family (Finset.range 7) <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem witness_four :
    ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily 4 F ∧ F.card = 9 := by
  refine ⟨{{0, 1, 2, 3},
      {0, 4, 5, 6},
      {0, 7, 8, 9},
      {1, 4, 7, 10},
      {1, 2, 5, 8},
      {2, 6, 9, 10},
      {3, 4, 6, 8},
      {3, 5, 7, 9},
      {0, 3, 5, 10}}, ?_, by decide +kernel⟩
  apply verify_family (Finset.range 11) <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem witness_five :
    ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily 5 F ∧ F.card = 13 := by
  refine ⟨{{0, 1, 2, 3, 4},
      {0, 1, 5, 6, 7},
      {0, 2, 8, 9, 10},
      {0, 5, 8, 11, 12},
      {2, 5, 13, 14, 15},
      {3, 6, 8, 13, 16},
      {4, 5, 9, 10, 13},
      {2, 4, 6, 11, 12},
      {4, 7, 8, 14, 16},
      {3, 7, 9, 11, 15},
      {1, 10, 12, 15, 16},
      {1, 6, 9, 11, 14},
      {3, 7, 10, 12, 14}}, ?_, by decide +kernel⟩
  apply verify_family (Finset.range 17) <;> decide +kernel

/-- Rule out order-four families with at most eight edges. -/
def H1 : Prop := ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily 4 F → 9 ≤ F.card

/-- Rule out order-five families with at most twelve edges. -/
def H2 : Prop := ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily 5 F → 13 ≤ F.card

theorem main : H1 → H2 → type_of% @Erdos21.erdos_21.variants.small_values := by
  intro lower_four lower_five
  exact ⟨order_one, order_two, minimum_eq witness_three lower_three,
    minimum_eq witness_four lower_four, minimum_eq witness_five lower_five⟩

end OMA.R_Erdos21_erdos_21_variants_small_values_R1
