import OMAReductions.R_Erdos21_erdos_21_variants_small_values_R1

/-! An intersecting family of eight four-element edges always has a three-point cover. The argument counts pairs of degree-three vertices in the eight indexed edges. -/

open Finset Erdos21

namespace OrderFour

private theorem hit_pair (E : Fin 8 → Finset ℕ)
    (cross : ∀ i j, (E i ∩ E j).Nonempty) (t : Finset (Fin 8)) (ht : t.card ≤ 2) :
    ∃ x : ℕ, ∀ i ∈ t, x ∈ E i := by
  by_cases htwo : t.card = 2
  · obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp htwo
    obtain ⟨x, hx⟩ := cross a b
    exact ⟨x, by simpa using mem_inter.mp hx⟩
  by_cases hone : t.card = 1
  · obtain ⟨a, rfl⟩ := card_eq_one.mp hone
    obtain ⟨x, hx⟩ := cross a a
    exact ⟨x, by simpa using (mem_inter.mp hx).1⟩
  have : t = ∅ := card_eq_zero.mp (by omega)
  exact ⟨0, by simp [this]⟩

private theorem hit_four (E : Fin 8 → Finset ℕ)
    (cross : ∀ i j, (E i ∩ E j).Nonempty) (t : Finset (Fin 8)) (ht : t.card ≤ 4) :
    ∃ x y : ℕ, ∀ i ∈ t, x ∈ E i ∨ y ∈ E i := by
  obtain ⟨a, hat, ha⟩ := exists_subset_card_eq (s := t) (n := min 2 t.card) (min_le_right ..)
  obtain ⟨x, hx⟩ := hit_pair E cross a (ha.trans_le (min_le_left ..))
  obtain ⟨y, hy⟩ := hit_pair E cross (t \ a) (by rw [card_sdiff_of_subset hat, ha]; omega)
  exact ⟨x, y, fun i hi => by
    by_cases h : i ∈ a
    · exact Or.inl (hx i h)
    · exact Or.inr (hy i (mem_sdiff.mpr ⟨hi,h⟩))⟩

private theorem count_by_edges (D : Finset ℕ) (E : Fin 8 → Finset ℕ) (w : Fin 8 → ℕ) :
    ∑ x ∈ D, ∑ i ∈ univ.filter (fun i => x ∈ E i), w i =
      ∑ i, (D.filter fun x => x ∈ E i).card * w i := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_const_nat (s := D.filter fun x => x ∈ E i) (f := fun _ => w i) (fun _ _ => rfl)]
  rw [sum_filter]

private theorem eight_impossible (E : Fin 8 → Finset ℕ)
    (size : ∀ i, (E i).card = 4) (cross : ∀ i j, (E i ∩ E j).Nonempty)
    (miss : ∀ S : Finset ℕ, S.card ≤ 3 → ∃ i, Disjoint S (E i)) : False := by
  classical
  let bag (x : ℕ) := univ.filter (fun i => x ∈ E i)
  let V := univ.biUnion E
  let D := V.filter (fun x => (bag x).card = 3)
  let row (i : Fin 8) := D.filter (fun x => x ∈ E i)
  let k (i : Fin 8) := (row i).card
  have inbag {x i} : i ∈ bag x ↔ x ∈ E i := by simp [bag]
  have hdeg (x : ℕ) : (bag x).card ≤ 3 := by
    by_contra! h
    obtain ⟨y,z,hyz⟩ := hit_four E cross (univ \ bag x) (by
      rw [card_sdiff_of_subset (subset_univ _)]
      simpa using (show 8 - (bag x).card ≤ 4 by omega))
    obtain ⟨i, hi⟩ := miss {x,y,z} card_le_three
    have hnx : x ∉ E i := fun h => disjoint_left.mp hi (by simp) h
    rcases hyz i (mem_sdiff.mpr ⟨mem_univ _, fun h => hnx (inbag.mp h)⟩) with h | h
    · exact disjoint_left.mp hi (by simp : y ∈ ({x,y,z} : Finset ℕ)) h
    · exact disjoint_left.mp hi (by simp : z ∈ ({x,y,z} : Finset ℕ)) h
  have hd {x} (hx : x ∈ D) : (bag x).card = 3 := (mem_filter.mp hx).2
  have share {x y} (hx : x ∈ D) (hy : y ∈ D) : ∃ i, x ∈ E i ∧ y ∈ E i := by
    by_contra! h
    have hxy : Disjoint (bag x) (bag y) := disjoint_left.mpr fun i hi hj =>
      h i (inbag.mp hi) (inbag.mp hj)
    have sze : (bag x ∪ bag y).card = 6 := by rw [card_union_of_disjoint hxy, hd hx, hd hy]
    obtain ⟨z,hz⟩ := hit_pair E cross (univ \ (bag x ∪ bag y)) (by
      rw [card_sdiff_of_subset (subset_univ _), sze]; decide)
    obtain ⟨i,hi⟩ := miss {x,y,z} card_le_three
    have nx : i ∉ bag x := fun h => disjoint_left.mp hi (by simp) (inbag.mp h)
    have ny : i ∉ bag y := fun h => disjoint_left.mp hi (by simp) (inbag.mp h)
    exact disjoint_left.mp hi (by simp : z ∈ ({x,y,z} : Finset ℕ))
      (hz i (by simp [nx, ny]))
  have le_four (i) : k i ≤ 4 := (card_le_card (show row i ⊆ E i from
    fun _ h => (mem_filter.mp h).2)).trans_eq (size i)
  -- Each edge meets seven others, so at least three of its four vertices have degree three.
  have three_le (i : Fin 8) : 3 ≤ k i := by
    let neighbors (x : ℕ) := (bag x).erase i
    have hcover : univ.erase i ⊆ (E i).biUnion neighbors := by
      intro j hj
      obtain ⟨x, hx⟩ := cross i j
      exact mem_biUnion.mpr ⟨x, (mem_inter.mp hx).1,
        mem_erase.mpr ⟨(mem_erase.mp hj).1, inbag.mpr (mem_inter.mp hx).2⟩⟩
    have limit (x : ℕ) (hx : x ∈ E i) : (neighbors x).card ≤ (if x ∈ D then 1 else 0) + 1 := by
      have hV : x ∈ V := mem_biUnion.mpr ⟨i, mem_univ _, hx⟩
      rw [show neighbors x = (bag x).erase i from rfl, card_erase_of_mem (inbag.mpr hx)]
      by_cases hD : x ∈ D
      · simp [hD, hd hD]
      · have hn : (bag x).card ≠ 3 := fun h => hD (mem_filter.mpr ⟨hV, h⟩)
        simp [hD]; have := hdeg x; omega
    have h := (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum limit))
    have eqrow : E i ∩ D = row i := by ext a; simp [row, and_comm]
    simp [sum_add_distrib, card_erase_of_mem (mem_univ i), size i, eqrow, k] at h ⊢
    omega
  -- Every two degree-three vertices share an edge. Count the other vertices from each of them.
  have count (x) (hx : x ∈ D) : D.card - 1 ≤ ∑ i ∈ bag x, (k i - 1) := by
    let incident (i : Fin 8) := (row i).erase x
    have hsub : D.erase x ⊆ (bag x).biUnion incident := by
      intro y hy
      obtain ⟨i,hix,hiy⟩ := share hx (mem_erase.mp hy).2
      exact mem_biUnion.mpr ⟨i,inbag.mpr hix,mem_erase.mpr
        ⟨(mem_erase.mp hy).1,mem_filter.mpr ⟨(mem_erase.mp hy).2,hiy⟩⟩⟩
    rw [← card_erase_of_mem hx]
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    apply sum_le_sum
    intro i hi
    exact (card_erase_of_mem (s := row i) (a := x) (mem_filter.mpr ⟨hx,inbag.mp hi⟩)).le
  have hdouble := sum_le_sum count
  have highcount := count_by_edges D E (fun _ => 1)
  have hpairs := count_by_edges D E (fun i => k i - 1)
  change (∑ x ∈ D, ∑ i ∈ bag x, 1) = ∑ i, k i * 1 at highcount
  simp only [sum_const, smul_eq_mul, mul_one] at highcount
  rw [sum_const_nat (m := 3) (fun x hx => hd hx)] at highcount
  change (∑ _x ∈ D, (D.card - 1)) ≤ ∑ x ∈ D, ∑ i ∈ bag x, (k i - 1) at hdouble
  change (∑ x ∈ D, ∑ i ∈ bag x, (k i - 1)) = ∑ i, k i * (k i - 1) at hpairs
  rw [hpairs, sum_const, smul_eq_mul] at hdouble
  -- For a row containing k = 3 or 4 such vertices, k(k − 1) = 6k − 12.
  have eqn : (∑ i, (k i * (k i - 1) + 12)) = ∑ i, 6 * k i := by
    apply sum_congr rfl
    intro i _
    have ha := three_le i
    have hb := le_four i
    rcases (by omega : k i = 3 ∨ k i = 4) with h | h <;> simp [h]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    ← mul_sum, ← highcount] at eqn
  have sumle : ∑ i, k i ≤ ∑ _ : Fin 8, 4 := sum_le_sum (fun i _ => le_four i)
  rw [← highcount] at sumle
  norm_num at sumle
  generalize hD : D.card = d at hdouble eqn sumle
  have : d ≤ 10 := by omega
  interval_cases d <;> omega

theorem lower_four (F : Finset (Finset ℕ)) (hF : IsErdosLovaszFamily 4 F) :
    9 ≤ F.card := by
  classical
  by_contra! hsmall
  obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
  let e := Fintype.equivFin (↥F)
  let gen (i : Fin 8) : ↥F :=
    if hi : i.val < Fintype.card (↥F) then e.symm ⟨i.val, hi⟩ else ⟨A,hA⟩
  have onto (B : ↥F) : ∃ i, gen i = B := by
    have hi := (e B).isLt
    have hb : (e B).val < 8 := by simp at hi; omega
    exact ⟨⟨(e B).val, hb⟩, by simp only [gen, dif_pos (e B).isLt, Fin.eta, Equiv.symm_apply_apply]⟩
  apply eight_impossible (fun i => (gen i).val)
    (fun i => hF.1 _ (gen i).property)
    (fun i j => hF.2.1 _ (gen i).property _ (gen j).property)
  intro S hS
  obtain ⟨B,hB,hd⟩ := hF.2.2 S hS
  obtain ⟨i,hi⟩ := onto ⟨B,hB⟩
  exact ⟨i, by simpa [hi] using hd⟩

end OrderFour


theorem OMA.solution : OMA.R_Erdos21_erdos_21_variants_small_values_R1.H1 :=
  OrderFour.lower_four
