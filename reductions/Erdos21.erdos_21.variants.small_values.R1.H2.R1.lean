import OMAReductions.R_Erdos21_erdos_21_variants_small_values_R1

-- Reduction Erdos21.erdos_21.variants.small_values.R1.H2.R1 of step Erdos21.erdos_21.variants.small_values.R1.H2
-- Credit: @zarnab222-dev

/-!
A counterexample to the order-five lower bound has twelve edges. Counting incidences
bounds its support, and counting repeated vertex pairs excludes fifteen vertices.
Relabeling the support leaves finite searches on sixteen through nineteen vertices.
These four orders also occur in the computational proof by Barát (arXiv:2011.04444, §6.2).
-/

open Finset Erdos21

namespace OMA.R_Erdos21_erdos_21_variants_small_values_R1_H2_R1

private theorem hit_pair {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hG : G ⊆ F) (h : G.card ≤ 2) : ∃ x, ∀ A ∈ G, x ∈ A := by
  by_cases h2 : G.card = 2
  · obtain ⟨A, B, _, rfl⟩ := card_eq_two.mp h2
    obtain ⟨x,hx⟩ := hF.2.1 A (hG (by simp)) B (hG (by simp))
    exact ⟨x, by simpa using mem_inter.mp hx⟩
  by_cases h1 : G.card = 1
  · obtain ⟨A,rfl⟩ := card_eq_one.mp h1
    obtain ⟨x,hx⟩ := card_pos.mp (by rw [hF.1 A (hG (by simp))]; decide)
    exact ⟨x,by simpa using hx⟩
  have hem : G = ∅ := card_eq_zero.mp (by omega)
  exact ⟨0,by simp [hem]⟩

private theorem cover_pairs {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (k : ℕ) (G : Finset (Finset ℕ)) (hG : G ⊆ F) (hs : G.card ≤ 2*k) :
    ∃ S : Finset ℕ, S.card ≤ k ∧ ∀ A ∈ G, (S ∩ A).Nonempty := by
  induction k generalizing G with
  | zero =>
    have h : G = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅,by simp,by simp [h]⟩
  | succ k ih =>
    obtain ⟨P,hPG,hP⟩ := exists_subset_card_eq (s := G) (n := min 2 G.card) (min_le_right ..)
    obtain ⟨x,hx⟩ := hit_pair hF (hPG.trans hG) (hP.trans_le (min_le_left ..))
    obtain ⟨S,hsize,hcover⟩ := ih (G \ P) (sdiff_subset.trans hG)
      (by rw [card_sdiff_of_subset hPG,hP]; omega)
    refine ⟨insert x S,(card_insert_le ..).trans (by omega),?_⟩
    intro A hA
    by_cases ha : A ∈ P
    · exact ⟨x,mem_inter.mpr ⟨mem_insert_self ..,hx A ha⟩⟩
    · obtain ⟨y,hy⟩ := hcover A (mem_sdiff.mpr ⟨hA,ha⟩)
      exact ⟨y,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hy).1,(mem_inter.mp hy).2⟩⟩

private theorem neighbors {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hG : G ⊆ F) {A : Finset ℕ} (hA : A ∈ G) :
    G.card - 1 ≤ ∑ x ∈ A, ((G.filter fun B => x ∈ B).card - 1) := by
  let N (x : ℕ) := (G.filter fun B => x ∈ B).erase A
  have hsub : G.erase A ⊆ A.biUnion N := by
    intro B hB
    have hb := mem_erase.mp hB
    obtain ⟨x,hx⟩ := hF.2.1 A (hG hA) B (hG hb.2)
    exact mem_biUnion.mpr ⟨x,(mem_inter.mp hx).1,mem_erase.mpr ⟨hb.1,mem_filter.mpr ⟨hb.2,(mem_inter.mp hx).2⟩⟩⟩
  rw [← card_erase_of_mem hA]
  apply (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  exact sum_le_sum (fun x hx => (card_erase_of_mem (mem_filter.mpr ⟨hA,hx⟩)).le)

-- Among seven edges, any one meets six others at its five vertices. A vertex on
-- three edges and one common point from each of two remaining pairs suffice.
private theorem cover_seven {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hG : G ⊆ F) (h7 : G.card ≤ 7) :
    ∃ S : Finset ℕ, S.card ≤ 3 ∧ ∀ A ∈ G, (S ∩ A).Nonempty := by
  by_cases h6 : G.card ≤ 6
  · exact cover_pairs hF 3 G hG h6
  obtain ⟨A,hA⟩ := card_pos.mp (by omega : 0 < G.card)
  obtain ⟨x,hx,hx3⟩ : ∃ x ∈ A, 3 ≤ (G.filter fun B => x ∈ B).card := by
    by_contra! hn
    have h := (neighbors hF hG hA).trans (sum_le_sum (g := fun _ => 1)
      (by intro x hx; have := hn x hx; omega))
    simp [hF.1 A (hG hA)] at h
    omega
  have hsplit := G.card_filter_add_card_filter_not (fun B => x ∈ B)
  obtain ⟨S,hS,hcover⟩ := cover_pairs hF 2 (G.filter fun B => x ∉ B) ((filter_subset ..).trans hG) (by omega)
  refine ⟨insert x S,(card_insert_le ..).trans (by omega),?_⟩
  intro B hB
  by_cases h : x ∈ B
  · exact ⟨x,mem_inter.mpr ⟨mem_insert_self ..,h⟩⟩
  · obtain ⟨y,hy⟩ := hcover B (mem_filter.mpr ⟨hB,h⟩)
    exact ⟨y,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hy).1,(mem_inter.mp hy).2⟩⟩

private theorem degree_limit {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F) (x : ℕ) :
    (F.filter fun A => x ∈ A).card + 8 ≤ F.card := by
  by_contra! h
  have hh := F.card_filter_add_card_filter_not (fun A => x ∈ A)
  obtain ⟨S,hS,hcover⟩ := cover_seven hF (filter_subset ..) (by omega : (F.filter fun A => x ∉ A).card ≤ 7)
  obtain ⟨A,hA,hd⟩ := hF.2.2 (insert x S) ((card_insert_le ..).trans (by omega))
  have hx : x ∉ A := fun h => disjoint_left.mp hd (mem_insert_self ..) h
  obtain ⟨y,hy⟩ := hcover A (mem_filter.mpr ⟨hA,hx⟩)
  exact disjoint_left.mp hd (mem_insert_of_mem (mem_inter.mp hy).1) (mem_inter.mp hy).2

private theorem incidence {F : Finset (Finset ℕ)} (w : ℕ → ℕ) :
    ∑ x ∈ F.biUnion id, (F.filter fun A => x ∈ A).card * w x =
      ∑ A ∈ F, ∑ x ∈ A, w x := by
  calc
    _ = ∑ x ∈ F.biUnion id, ∑ A ∈ F, if x ∈ A then w x else 0 := by
      apply sum_congr rfl
      intro x _
      rw [← sum_filter, sum_const, smul_eq_mul]
    _ = ∑ A ∈ F, ∑ x ∈ F.biUnion id, if x ∈ A then w x else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro A hA
      rw [← sum_filter]
      congr 1
      ext x
      simp only [mem_filter, and_iff_right_iff_imp]
      exact fun hx => mem_biUnion.mpr ⟨A,hA,hx⟩

-- At eleven edges, every vertex must have degree three. The incidence count
-- would then make 55 divisible by three.
private theorem twelve_le (F : Finset (Finset ℕ)) (hF : IsErdosLovaszFamily 5 F) : 12 ≤ F.card := by
  by_contra! h
  let d (x : ℕ) := (F.filter fun A => x ∈ A).card
  have bound (x : ℕ) := degree_limit hF x
  obtain ⟨A,hA,_⟩ := hF.2.2 ∅ (by simp)
  have h11 : F.card = 11 := by
    by_contra hn
    have hnear := (neighbors hF Subset.rfl hA).trans (sum_le_sum (g := fun _ => F.card-9)
      (by intro x hx; have := bound x; omega))
    simp [hF.1 A hA] at hnear
    have := bound 0
    omega
  have all_three (x : ℕ) (hx : x ∈ F.biUnion id) : d x = 3 := by
    have hmax := bound x
    have hmax' : d x ≤ 3 := by dsimp [d]; omega
    by_contra hne
    obtain ⟨B,hB,hxB⟩ := mem_biUnion.mp hx
    change x ∈ B at hxB
    have hnear := neighbors hF Subset.rfl hB
    change F.card - 1 ≤ ∑ y ∈ B, (d y - 1) at hnear
    have hrest : ∑ y ∈ B.erase x, (d y - 1) ≤ ∑ _ ∈ B.erase x, 2 := sum_le_sum
      (fun y _ => by dsimp [d]; have := bound y; omega)
    rw [← add_sum_erase _ _ hxB] at hnear
    simp [card_erase_of_mem hxB,hF.1 B hB] at hrest
    omega
  have hsum := incidence (F := F) (fun _ => 1)
  simp only [mul_one,sum_const,smul_eq_mul] at hsum
  change (∑ x ∈ F.biUnion id, d x) = ∑ A ∈ F, A.card at hsum
  rw [sum_const_nat (m := 3) (fun x hx => all_three x hx),
    sum_const_nat (m := 5) (fun A hA => hF.1 A hA), h11] at hsum
  omega

private theorem degree_min {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    {x : ℕ} (hx : x ∈ F.biUnion id) : 2 ≤ (F.filter fun B => x ∈ B).card := by
  obtain ⟨A,hA,hxA⟩ := mem_biUnion.mp hx
  change x ∈ A at hxA
  have hsize : (A.erase x).card = 4 := by rw [card_erase_of_mem hxA, hF.1 A hA]
  obtain ⟨B,hB,hd⟩ := hF.2.2 (A.erase x) hsize.le
  have hAB : A ≠ B := by
    rintro rfl
    obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < (A.erase x).card)
    exact disjoint_left.mp hd hv (mem_of_mem_erase hv)
  obtain ⟨z,hz⟩ := hF.2.1 A hA B hB
  have hz' := mem_inter.mp hz
  have hzx : z = x := by
    by_contra h
    exact disjoint_left.mp hd (mem_erase.mpr ⟨h,hz'.1⟩) hz'.2
  have sub : {A,B} ⊆ F.filter (fun D => x ∈ D) := by
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_filter.mpr ⟨hA,hxA⟩,mem_filter.mpr ⟨hB,hzx ▸ hz'.2⟩⟩
  simpa [card_pair hAB] using card_le_card sub

-- Removing two degree-two vertices from one edge leaves at most two edges
-- uncovered. Their common point would complete a four-vertex transversal.
private theorem low_per_edge {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    {A : Finset ℕ} (hA : A ∈ F) :
    (A.filter fun x => (F.filter fun B => x ∈ B).card ≤ 2).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hxA,hx2⟩ := mem_filter.mp hx
  obtain ⟨hyA,hy2⟩ := mem_filter.mp hy
  let S := (A.erase x).erase y
  have hS : S.card = 3 := by
    rw [show S = (A.erase x).erase y from rfl, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hxy,hyA⟩),
      card_erase_of_mem hxA,hF.1 A hA]
  let G := F.filter (fun B => Disjoint S B)
  let N (z : ℕ) := (F.filter fun B => z ∈ B).erase A
  have sub : G ⊆ N x ∪ N y := by
    intro B hB
    obtain ⟨hb,hd⟩ := mem_filter.mp hB
    have hBA : B ≠ A := by
      rintro rfl
      obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < S.card)
      exact disjoint_left.mp hd hv (mem_of_mem_erase (mem_of_mem_erase hv))
    obtain ⟨v,hv⟩ := hF.2.1 A hA B hb
    obtain ⟨hvA,hvB⟩ := mem_inter.mp hv
    by_cases hxv : v = x
    · exact mem_union_left _ (mem_erase.mpr ⟨hBA,mem_filter.mpr ⟨hb,hxv ▸ hvB⟩⟩)
    by_cases hyv : v = y
    · exact mem_union_right _ (mem_erase.mpr ⟨hBA,mem_filter.mpr ⟨hb,hyv ▸ hvB⟩⟩)
    exact False.elim (disjoint_left.mp hd (mem_erase.mpr ⟨hyv,mem_erase.mpr ⟨hxv,hvA⟩⟩) hvB)
  have hsize := (card_le_card sub).trans (card_union_le ..)
  change G.card ≤ ((F.filter fun B => x ∈ B).erase A).card + ((F.filter fun B => y ∈ B).erase A).card at hsize
  rw [card_erase_of_mem (mem_filter.mpr ⟨hA,hxA⟩),card_erase_of_mem (mem_filter.mpr ⟨hA,hyA⟩)] at hsize
  obtain ⟨z,hz⟩ := hit_pair hF (filter_subset ..) (by omega : G.card ≤ 2)
  obtain ⟨D,hD,hd⟩ := hF.2.2 (insert z S) ((card_insert_le ..).trans (by omega))
  have hDS : Disjoint S D := hd.mono_left (subset_insert ..)
  exact disjoint_left.mp hd (mem_insert_self ..) (hz D (mem_filter.mpr ⟨hD,hDS⟩))

private theorem high_share {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (h12 : F.card = 12) {x y : ℕ}
    (hx : (F.filter fun B => x ∈ B).card = 4) (hy : (F.filter fun B => y ∈ B).card = 4) :
    ∃ A ∈ F, x ∈ A ∧ y ∈ A := by
  by_contra! h
  let X := F.filter fun B => x ∈ B
  let Y := F.filter fun B => y ∈ B
  have hd : Disjoint X Y := disjoint_left.mpr fun A hA hB =>
    h A (mem_filter.mp hA).1 (mem_filter.mp hA).2 (mem_filter.mp hB).2
  have hXY : (X ∪ Y).card = 8 := by rw [card_union_of_disjoint hd]; exact congrArg₂ (· + ·) hx hy
  have hsub : X ∪ Y ⊆ F := union_subset (filter_subset ..) (filter_subset ..)
  obtain ⟨S,hS,hcover⟩ := cover_pairs hF 2 (F \ (X ∪ Y)) sdiff_subset
    (by rw [card_sdiff_of_subset hsub,hXY,h12])
  obtain ⟨A,hA,hdis⟩ := hF.2.2 (insert x (insert y S))
    ((card_insert_le ..).trans (by have := card_insert_le y S; omega))
  have hax : x ∉ A := fun ha => disjoint_left.mp hdis (mem_insert_self ..) ha
  have hay : y ∉ A := fun ha => disjoint_left.mp hdis (mem_insert_of_mem (mem_insert_self ..)) ha
  have hrest : A ∈ F \ (X ∪ Y) := mem_sdiff.mpr ⟨hA, by simp [X,Y,hA,hax,hay]⟩
  obtain ⟨z,hz⟩ := hcover A hrest
  exact disjoint_left.mp hdis (mem_insert_of_mem (mem_insert_of_mem (mem_inter.mp hz).1)) (mem_inter.mp hz).2

-- Equality in the weight bound would force two degree-four vertices per edge
-- and six in total. Each of the six must meet the other five in just four edges.
private theorem exclude_twenty {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (h12 : F.card = 12) (h20 : (F.biUnion id).card = 20)
    (row : ∀ A ∈ F, (∑ x ∈ A, 12 / (F.filter fun B => x ∈ B).card) ≤ 20)
    (sumW : (F.biUnion id).card * 12 = ∑ A ∈ F, ∑ x ∈ A, 12 / (F.filter fun B => x ∈ B).card) :
    False := by
  let d (x : ℕ) := (F.filter fun B => x ∈ B).card
  let D := (F.biUnion id).filter fun x => d x = 4
  have row_eq (A : Finset ℕ) (hA : A ∈ F) : (∑ x ∈ A, 12 / d x) = 20 := by
    apply (row A hA).antisymm
    by_contra! h
    have hlt := sum_lt_sum row ⟨A,hA,h⟩
    rw [← sumW,h20,sum_const,smul_eq_mul,h12] at hlt
    omega
  have two (A : Finset ℕ) (hA : A ∈ F) : (A.filter (fun x => d x = 4)).card = 2 := by
    have hi (x : ℕ) : d x ≤ 4 := by dsimp [d]; have := degree_limit hF x; omega
    have hid : (∑ x ∈ A, (12 / d x + if d x = 4 then 1 else 0)) =
        ∑ x ∈ A, (4 + 2 * (if d x ≤ 2 then 1 else 0)) := by
      apply sum_congr rfl
      intro x hx
      have h₁ : 2 ≤ d x := degree_min hF (mem_biUnion.mpr ⟨A,hA,hx⟩)
      have h₂ := hi x
      rcases (show d x = 2 ∨ d x = 3 ∨ d x = 4 by omega) with h | h | h <;> rw [h] <;> decide
    simp only [sum_add_distrib,← mul_sum,sum_const,smul_eq_mul,sum_boole,hF.1 A hA,row_eq A hA] at hid
    norm_cast at hid
    have hone : (A.filter fun x => d x ≤ 2).card ≤ 1 := low_per_edge hF hA
    have hpos : 0 < (A.filter fun x => d x = 4).card := by
      by_contra! hn
      have hem := card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
      have hnear := (neighbors hF Subset.rfl hA).trans (sum_le_sum (g := fun _ => 2) (by
        intro x hx
        have hn4 : d x ≠ 4 := fun h4 => by
          have hmem : x ∈ A.filter (fun z => d z = 4) := mem_filter.mpr ⟨hx,h4⟩
          exact notMem_empty x (hem ▸ hmem)
        change d x - 1 ≤ 2
        have := hi x
        omega))
      rw [sum_const,smul_eq_mul,hF.1 A hA,h12] at hnear
      omega
    omega
  have hdbl := incidence (F := F) (fun x => if d x = 4 then 1 else 0)
  change (∑ x ∈ F.biUnion id, d x * (if d x = 4 then 1 else 0)) = _ at hdbl
  simp only [mul_ite,mul_one,mul_zero,← sum_filter,sum_const,smul_eq_mul] at hdbl
  change (∑ x ∈ D, d x) = ∑ A ∈ F, (A.filter fun x => d x = 4).card at hdbl
  rw [sum_const_nat (m := 4) (fun x hx => (mem_filter.mp hx).2),
    sum_const_nat (m := 2) two,h12] at hdbl
  change D.card * 4 = 12 * 2 at hdbl
  have hD : D.card = 6 := by omega
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : D.card > 0)
  have hx4 : d x = 4 := (mem_filter.mp hx).2
  let X := F.filter fun A => x ∈ A
  let N (A : Finset ℕ) := (A.filter fun y => d y = 4).erase x
  have hsub : D.erase x ⊆ X.biUnion N := by
    intro y hy
    obtain ⟨hyx,hyD⟩ := mem_erase.mp hy
    have hy4 : d y = 4 := (mem_filter.mp hyD).2
    obtain ⟨A,hA,hxA,hyA⟩ := high_share hF h12 hx4 hy4
    exact mem_biUnion.mpr ⟨A,mem_filter.mpr ⟨hA,hxA⟩,mem_erase.mpr ⟨hyx,mem_filter.mpr ⟨hyA,hy4⟩⟩⟩
  have hb := (card_le_card hsub).trans (card_biUnion_le_card_mul X N 1 (by
    intro A hA
    obtain ⟨ha,hxa⟩ := mem_filter.mp hA
    dsimp [N]
    rw [card_erase_of_mem (mem_filter.mpr ⟨hxa,hx4⟩),two A ha]))
  rw [card_erase_of_mem hx,hD,show X.card = 4 from hx4] at hb
  omega

private theorem structural {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F) (hc : F.card ≤ 12) :
    F.card = 12 ∧ 15 ≤ (F.biUnion id).card ∧ (F.biUnion id).card ≤ 19 := by
  have h12 := hc.antisymm (twelve_le F hF)
  let d (x : ℕ) := (F.filter fun B => x ∈ B).card
  have hhi (x : ℕ) : d x ≤ 4 := by
    dsimp [d]; have := degree_limit hF x; omega
  have hlo {x : ℕ} (hx : x ∈ F.biUnion id) : 2 ≤ d x := degree_min hF hx
  have total := incidence (F := F) (fun _ => 1)
  simp only [mul_one,sum_const,smul_eq_mul] at total
  change (∑ x ∈ F.biUnion id, d x) = ∑ A ∈ F, A.card at total
  rw [sum_const_nat (m := 5) (fun A hA => hF.1 A hA),h12] at total
  have hlow := (sum_le_sum (s := F.biUnion id) (fun x _ => hhi x))
  rw [total,sum_const,smul_eq_mul] at hlow
  refine ⟨h12,by omega,?_⟩
  -- Splitting weight 12 evenly over the incident edges gives a vertex of degree
  -- two, three or four a contribution of six, four or three to each edge.
  have row (A : Finset ℕ) (hA : A ∈ F) : ∑ x ∈ A, 12 / d x ≤ 20 := by
    have hid : (∑ x ∈ A, (12 / d x + (d x - 1))) =
        ∑ x ∈ A, (6 + if d x ≤ 2 then 1 else 0) := by
      apply sum_congr rfl
      intro x hx
      have hd := hlo (mem_biUnion.mpr ⟨A,hA,hx⟩)
      have hd' := hhi x
      rcases (show d x = 2 ∨ d x = 3 ∨ d x = 4 by omega) with h | h | h <;> rw [h] <;> decide
    simp only [sum_add_distrib,sum_const,smul_eq_mul,sum_boole,hF.1 A hA] at hid
    norm_cast at hid
    have hnear := neighbors hF Subset.rfl hA
    change F.card - 1 ≤ ∑ x ∈ A, (d x - 1) at hnear
    have hone := low_per_edge hF hA
    change (A.filter fun x => d x ≤ 2).card ≤ 1 at hone
    omega
  have double := incidence (F := F) (fun x => 12 / d x)
  change (∑ x ∈ F.biUnion id, d x * (12 / d x)) = ∑ A ∈ F, ∑ x ∈ A, 12 / d x at double
  rw [sum_const_nat (m := 12) (fun x hx => by
    have h1 := hlo hx; have h2 := hhi x
    rcases (show d x = 2 ∨ d x = 3 ∨ d x = 4 by omega) with h | h | h <;> rw [h])] at double
  have bound := sum_le_sum row
  rw [← double, sum_const,smul_eq_mul,h12] at bound
  have hle : (F.biUnion id).card ≤ 20 := by omega
  have hne : (F.biUnion id).card ≠ 20 := fun heq => exclude_twenty hF h12 heq row double
  exact Nat.le_of_lt_succ (lt_of_le_of_ne hle hne)

private theorem table_count {α β : Type} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (F : Finset β) (row : β → Finset α) (incl : ∀ A ∈ F, row A ⊆ U)
    (w : α → ℕ) :
    ∑ e ∈ U, (F.filter (fun A => e ∈ row A)).card * w e = ∑ A ∈ F, ∑ e ∈ row A, w e := by
  calc
    _ = ∑ e ∈ U, ∑ A ∈ F, if e ∈ row A then w e else 0 := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter, sum_const, smul_eq_mul]
    _ = ∑ A ∈ F, ∑ e ∈ U, if e ∈ row A then w e else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro A hA
      rw [← sum_filter]
      congr 1
      ext e
      simp only [mem_filter, and_iff_right_iff_imp]
      exact fun he => incl A hA he

private theorem no_fifteen {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hc : F.card = 12) (hv : (F.biUnion id).card = 15)
    (hmax : ∀ x ∈ F.biUnion id, (F.filter (x ∈ ·)).card ≤ 4)
    (coverPairs : ∀ k (G : Finset (Finset ℕ)), G ⊆ F → G.card ≤ 2*k →
      ∃ S : Finset ℕ, S.card ≤ k ∧ ∀ A ∈ G, (S ∩ A).Nonempty) : False := by
  classical
  let V := F.biUnion id
  let rows (x : ℕ) := F.filter (x ∈ ·)
  let pairs (A : Finset ℕ) := A.powersetCard 2
  let mult (e : Finset ℕ) := (F.filter (fun A => e ∈ pairs A)).card
  have incA (A) (hA : A ∈ F) : A ⊆ V := fun x hx => mem_biUnion.mpr ⟨A,hA,hx⟩
  have deg (x) (hx : x ∈ V) : (rows x).card = 4 := by
    by_contra hne
    have hlt : (rows x).card < 4 := lt_of_le_of_ne (hmax x hx) hne
    have hsum := sum_lt_sum (s := V) (f := fun y => (rows y).card) (g := fun _ => 4)
      (fun y hy => hmax y hy) ⟨x,hx,hlt⟩
    have count := table_count V F id incA (fun _ => 1)
    change (∑ y ∈ V, (rows y).card * 1) = _ at count
    simp only [mul_one, sum_const, smul_eq_mul, id_eq] at count hsum
    rw [sum_const_nat (m := 5) (fun A hA => hF.1 A hA)] at count
    change V.card = 15 at hv
    omega
  have budget (X : Finset ℕ) (k : ℕ) (hX : X.card + k ≤ 4) :
      2*k < (F.filter (fun B => Disjoint X B)).card := by
    by_contra! h
    obtain ⟨S,hS,hit⟩ := coverPairs k _ (filter_subset ..) h
    obtain ⟨B,hB,dis⟩ := hF.2.2 (X ∪ S) ((card_union_le X S).trans (by omega))
    have hx : Disjoint X B := disjoint_of_subset_left subset_union_left dis
    obtain ⟨z,hz⟩ := hit B (mem_filter.mpr ⟨hB,hx⟩)
    exact disjoint_left.mp dis (mem_union_right X (mem_inter.mp hz).1) (mem_inter.mp hz).2
  have positive (e) (he : e ∈ pairs V) : 1 ≤ mult e := by
    obtain ⟨hsub,hsize⟩ := mem_powersetCard.mp he
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hsize
    by_contra! hn
    have hdis : Disjoint (rows x) (rows y) := by
      apply disjoint_left.mpr
      intro A hx hy
      have hA : ({x,y} : Finset ℕ) ∈ pairs A := mem_powersetCard.mpr
        ⟨insert_subset (mem_filter.mp hx).2 (singleton_subset_iff.mpr (mem_filter.mp hy).2),
          by simp [hxy]⟩
      have hpos : 0 < mult {x,y} := card_pos.mpr ⟨A,mem_filter.mpr ⟨(mem_filter.mp hx).1,hA⟩⟩
      omega
    have hcard : (rows x ∪ rows y).card = 8 := by
      rw [card_union_of_disjoint hdis,deg x (hsub (by simp)),deg y (hsub (by simp))]
    have miss := budget {x,y} 2 (by simp [hxy])
    have sub : F.filter (fun B => Disjoint ({x,y} : Finset ℕ) B) ⊆ F \ (rows x ∪ rows y) := by
      intro B hB
      obtain ⟨hf,hd⟩ := mem_filter.mp hB
      refine mem_sdiff.mpr ⟨hf,fun h => ?_⟩
      rcases mem_union.mp h with h|h
      · exact disjoint_left.mp hd (by simp) (mem_filter.mp h).2
      · exact disjoint_left.mp hd (by simp) (mem_filter.mp h).2
    have hu : rows x ∪ rows y ⊆ F := union_subset (filter_subset ..) (filter_subset ..)
    have hle := card_le_card sub
    rw [card_sdiff_of_subset hu,hcard,hc] at hle
    omega
  have per_row (A : Finset ℕ) (hA : A ∈ F) :
      3 ≤ ((pairs A).filter fun e => 1 < mult e).card := by
    let R := (pairs A).filter fun e => 1 < mult e
    let pick (e : Finset ℕ) := if h : e.Nonempty then e.min' h else 0
    have picked (e) (he : e ∈ R) : pick e ∈ e := by
      have hn := (mem_powersetCard.mp (mem_filter.mp he).1).2
      have hpos : e.Nonempty := card_pos.mp (by omega)
      simpa only [pick,dif_pos hpos] using min'_mem e hpos
    by_contra! h
    have hr : R.card ≤ 2 := by dsimp [R]; omega
    have hle : (R.image pick).card ≤ 2 := card_image_le.trans hr
    let T := A \ R.image pick
    have hT : 3 ≤ T.card := by
      have hsub : R.image pick ⊆ A := by
        intro x hx
        obtain ⟨e,he,rfl⟩ := mem_image.mp hx
        exact (mem_powersetCard.mp (mem_filter.mp he).1).1 (picked e he)
      dsimp [T]
      rw [card_sdiff_of_subset hsub,hF.1 A hA]
      omega
    obtain ⟨X,hXT,h3⟩ := exists_subset_card_eq hT
    have hXA : X ⊆ A := hXT.trans sdiff_subset
    let N (x : ℕ) := (rows x).erase A
    have pairwise : (X : Set ℕ).PairwiseDisjoint N := by
      intro x hx y hy hxy
      apply disjoint_left.mpr
      intro B hxB hyB
      obtain ⟨hne,hxb⟩ := mem_erase.mp hxB
      have hyb := (mem_erase.mp hyB).2
      let e : Finset ℕ := {x,y}
      have esize : e.card = 2 := by simp [e,hxy]
      have eX : e ⊆ X := insert_subset hx (singleton_subset_iff.mpr hy)
      have eA : e ∈ pairs A := mem_powersetCard.mpr ⟨eX.trans hXA,esize⟩
      have eB : e ∈ pairs B := mem_powersetCard.mpr
        ⟨insert_subset (mem_filter.mp hxb).2 (singleton_subset_iff.mpr (mem_filter.mp hyb).2),
          esize⟩
      have two : 1 < mult e := by
        apply one_lt_card.mpr
        exact ⟨B,mem_filter.mpr ⟨(mem_filter.mp hxb).1,eB⟩,
          A,mem_filter.mpr ⟨hA,eA⟩,hne⟩
      have heR : e ∈ R := mem_filter.mpr ⟨eA,two⟩
      exact (mem_sdiff.mp (hXT (eX (picked e heR)))).2 (mem_image_of_mem _ heR)
    have hN : (X.biUnion N).card = 9 := by
      rw [card_biUnion pairwise,sum_const_nat (m := 3),h3]
      intro x hx
      dsimp [N]
      rw [card_erase_of_mem (mem_filter.mpr ⟨hA,hXA hx⟩),deg x (incA A hA (hXA hx))]
    have hnA : A ∉ X.biUnion N := by
      intro hm
      obtain ⟨x,hx,hxA⟩ := mem_biUnion.mp hm
      exact (mem_erase.mp hxA).1 rfl
    have inF : insert A (X.biUnion N) ⊆ F := by
      apply insert_subset hA
      intro B hB
      obtain ⟨x,hx,hxb⟩ := mem_biUnion.mp hB
      exact (mem_filter.mp (mem_erase.mp hxb).2).1
    have sub : F.filter (fun B => Disjoint X B) ⊆ F \ insert A (X.biUnion N) := by
      intro B hB
      obtain ⟨hf,dis⟩ := mem_filter.mp hB
      refine mem_sdiff.mpr ⟨hf,fun h => ?_⟩
      rcases mem_insert.mp h with eq|hb
      · subst B
        obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < X.card)
        exact disjoint_left.mp dis hx (hXA hx)
      · obtain ⟨x,hx,hB⟩ := mem_biUnion.mp hb
        exact disjoint_left.mp dis hx (mem_filter.mp (mem_erase.mp hB).2).2
    have hle' := card_le_card sub
    rw [card_sdiff_of_subset inF, card_insert_of_notMem hnA,hN,hc] at hle'
    have := budget X 1 (by omega)
    omega
  have pincl (A) (hA : A ∈ F) : pairs A ⊆ pairs V := by
    intro e he
    exact mem_powersetCard.mpr ⟨(mem_powersetCard.mp he).1.trans (incA A hA),
      (mem_powersetCard.mp he).2⟩
  have total := table_count (pairs V) F pairs pincl (fun _ => 1)
  change (∑ e ∈ pairs V, mult e * 1) = _ at total
  simp only [mul_one, sum_const, smul_eq_mul] at total
  have sizeA (A) (hA : A ∈ F) : (pairs A).card = 10 := by
    dsimp [pairs]
    rw [card_powersetCard,hF.1 A hA]
    decide
  rw [sum_const_nat (m := 10) sizeA,hc] at total
  have sizeV : (pairs V).card = 105 := by
    change ((F.biUnion id).powersetCard 2).card = 105
    rw [card_powersetCard,hv]
    decide
  let w (e : Finset ℕ) : ℕ := if 1 < mult e then 1 else 0
  have repeat_count := table_count (pairs V) F pairs pincl w
  change (∑ e ∈ pairs V, mult e * w e) = _ at repeat_count
  have lower : 36 ≤ ∑ e ∈ pairs V, mult e * w e := by
    rw [repeat_count]
    have h := sum_le_sum (s := F) (f := fun _ => 3)
      (g := fun A => ∑ e ∈ pairs A, w e) (by
        intro A hA
        simpa [w,← card_filter] using per_row A hA)
    simpa [hc] using h
  have bound := sum_le_sum (s := pairs V) (f := fun e => 2 + mult e * w e)
    (g := fun e => 2 * mult e) (by
      intro e he
      have h := positive e he
      dsimp [w]
      split <;> simp_all
      omega)
  rw [sum_add_distrib,sum_const,smul_eq_mul,sizeV,← mul_sum,total] at bound
  omega

/-- Number the vertices in the union of the edges. Pulling the edges back along
this numbering preserves their sizes, intersection pattern and covering number. -/
private theorem finite_relabel_degrees {n v : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos21.IsErdosLovaszFamily n F) (hv : (F.biUnion id).card = v)
    (hdeg : ∀ x ∈ F.biUnion id,
      2 ≤ (F.filter (x ∈ ·)).card ∧ (F.filter (x ∈ ·)).card ≤ 4)
    (hlow : ∀ A ∈ F, (A.filter fun x => (F.filter (x ∈ ·)).card ≤ 2).card ≤ 1) :
    ∃ G : Finset (Finset (Fin v)), G.card = F.card ∧
      (∀ A ∈ G, A.card = n) ∧
      (∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) ∧
      (∀ S : Finset (Fin v), S.card ≤ n - 1 → ∃ A ∈ G, Disjoint S A) ∧
      (∀ x : Fin v, ∃ A ∈ G, x ∈ A) ∧
      (∀ x : Fin v, 2 ≤ (G.filter (x ∈ ·)).card ∧ (G.filter (x ∈ ·)).card ≤ 4) ∧
      (∀ A ∈ G, (A.filter fun x => (G.filter (x ∈ ·)).card ≤ 2).card ≤ 1) := by
  classical
  let U := F.biUnion id
  let e := U.orderIsoOfFin hv
  let label : Fin v ↪ ℕ := e.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  let pull (A : Finset ℕ) := Finset.univ.filter (fun i : Fin v => label i ∈ A)
  have mem_pull (i : Fin v) (A : Finset ℕ) : i ∈ pull A ↔ label i ∈ A := by simp [pull]
  have cover (x : ℕ) (hx : x ∈ U) : ∃ i, label i = x := by
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    change ((e (e.symm ⟨x, hx⟩) : U) : ℕ) = x
    rw [e.apply_symm_apply]
  have back (A : Finset ℕ) (hA : A ∈ F) : (pull A).map label = A := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact (mem_pull i A).mp hi
    · intro hx
      obtain ⟨i, hi⟩ := cover x (Finset.mem_biUnion.mpr ⟨A, hA, hx⟩)
      exact Finset.mem_map.mpr ⟨i, (mem_pull i A).mpr (hi ▸ hx), hi⟩
  have hinj : Set.InjOn pull ↑F := by
    intro A hA B hB h
    simpa only [back A hA, back B hB] using congrArg (Finset.map label) h
  have degrees (i : Fin v) : ((F.image pull).filter (i ∈ ·)).card =
      (F.filter (label i ∈ ·)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    · simp only [mem_pull]
    · exact hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset ..))
  refine ⟨F.image pull, Finset.card_image_of_injOn hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
    calc
      (pull A).card = ((pull A).map label).card := (Finset.card_map _).symm
      _ = n := by rw [back A hA, hF.1 A hA]
  · intro a ha b hb
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x, hx⟩ := hF.2.1 A hA B hB
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, hi⟩ := cover x (Finset.mem_biUnion.mpr ⟨A, hA, hxA⟩)
    exact ⟨i, Finset.mem_inter.mpr ⟨(mem_pull _ _).mpr (hi ▸ hxA),
      (mem_pull _ _).mpr (hi ▸ hxB)⟩⟩
  · intro S hS
    obtain ⟨A, hA, hd⟩ := hF.2.2 (S.map label) (by simpa using hS)
    refine ⟨pull A, Finset.mem_image_of_mem _ hA, Finset.disjoint_left.mpr ?_⟩
    intro i hiS hiA
    exact Finset.disjoint_left.mp hd (Finset.mem_map_of_mem label hiS) ((mem_pull i A).mp hiA)
  · intro i
    obtain ⟨A, hA, hi⟩ := Finset.mem_biUnion.mp (e i).property
    exact ⟨pull A, Finset.mem_image_of_mem _ hA, (mem_pull i A).mpr hi⟩
  · intro i
    simpa only [degrees] using hdeg (label i) (e i).property
  · intro a ha
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
    have h := hlow A hA
    rw [← back A hA, Finset.filter_map, Finset.card_map] at h
    simpa only [degrees, Function.comp_def] using h

/-- Search for a four-point cover on sixteen or seventeen vertices. -/
def H1 : Prop := ∀ v ∈ ({16, 17} : Finset ℕ),
  ∀ G ∈ (((Finset.univ : Finset (Fin v)).powersetCard 5).powersetCard 12),
    (∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) →
    (∀ x : Fin v, 2 ≤ (G.filter (x ∈ ·)).card ∧ (G.filter (x ∈ ·)).card ≤ 4) →
    (∀ A ∈ G, (A.filter fun x => (G.filter (x ∈ ·)).card ≤ 2).card ≤ 1) →
    ∃ S ∈ (Finset.univ : Finset (Fin v)).powersetCard 4, ∀ A ∈ G, ¬ Disjoint S A

/-- Search for a four-point cover on eighteen or nineteen vertices. -/
def H2 : Prop := ∀ v ∈ ({18, 19} : Finset ℕ),
  ∀ G ∈ (((Finset.univ : Finset (Fin v)).powersetCard 5).powersetCard 12),
    (∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) →
    (∀ x : Fin v, 2 ≤ (G.filter (x ∈ ·)).card ∧ (G.filter (x ∈ ·)).card ≤ 4) →
    (∀ A ∈ G, (A.filter fun x => (G.filter (x ∈ ·)).card ≤ 2).card ≤ 1) →
    ∃ S ∈ (Finset.univ : Finset (Fin v)).powersetCard 4, ∀ A ∈ G, ¬ Disjoint S A

theorem main : H1 → H2 → OMA.R_Erdos21_erdos_21_variants_small_values_R1.H2 := by
  classical
  intro small large F hF
  by_contra! hc
  let v := (F.biUnion id).card
  obtain ⟨h12, hvlo, hvhi⟩ := structural hF (by omega)
  have hcap (x : ℕ) : (F.filter (x ∈ ·)).card ≤ 4 := by
    have h := degree_limit hF x
    omega
  have hn15 : v ≠ 15 := by
    intro hv
    exact no_fifteen hF h12 hv (fun x _ => hcap x) (cover_pairs hF)
  obtain ⟨G, hsize, hunif, hpairs, hmiss, _, hdeg, hlow⟩ :=
    finite_relabel_degrees hF (rfl : (F.biUnion id).card = v)
      (fun x hx => ⟨degree_min hF hx, hcap x⟩) (fun _ hA => low_per_edge hF hA)
  have hG : G ∈ ((Finset.univ : Finset (Fin v)).powersetCard 5).powersetCard 12 := by
    exact Finset.mem_powersetCard.mpr
      ⟨fun A hA => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hunif A hA⟩, hsize.trans h12⟩
  have hcase : v ∈ ({16,17} : Finset ℕ) ∨ v ∈ ({18,19} : Finset ℕ) := by
    change 15 ≤ v at hvlo
    change v ≤ 19 at hvhi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  obtain ⟨S, hs, hit⟩ := hcase.elim (fun h => small v h G hG hpairs hdeg hlow)
    (fun h => large v h G hG hpairs hdeg hlow)
  obtain ⟨A, hA, hd⟩ := hmiss S (by have := (Finset.mem_powersetCard.mp hs).2; omega)
  exact hit A hA hd

end OMA.R_Erdos21_erdos_21_variants_small_values_R1_H2_R1
