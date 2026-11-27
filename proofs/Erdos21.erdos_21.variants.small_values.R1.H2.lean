import OMAReductions.R_Erdos21_erdos_21_variants_small_values_R1

/-!
A lower bound of thirteen edges in the order-five Erdős–Lovász problem.

A family on at most twelve edges must have exactly twelve, with a vertex of degree
four. The eight edges avoiding it require four vertices to hit. Their three-edge
stars therefore meet pairwise, and each of the eight edge indices must be the
singleton intersection of two stars. After normalizing one such pair of triples,
a finite check on the three indices outside its union rules this out.

For the known extremal value see Barát, arXiv:2011.04444, §6.2. For the general
singleton-intersection parameter for triples see Talbot, arXiv:math/0306119.
-/

-- Credit: @zarnab222-dev

open Finset Erdos21

namespace OrderFive

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

end OrderFive

namespace EightResidual

private theorem pairCover {α : Type*} [DecidableEq α] (row : Fin 8 → Finset α)
    (meet : ∀ i j, (row i ∩ row j).Nonempty) (fallback : α)
    (k : ℕ) (G : Finset (Fin 8)) (hs : G.card ≤ 2*k) :
    ∃ S : Finset α, S.card ≤ k ∧ ∀ i ∈ G, (S ∩ row i).Nonempty := by
  have pair (P : Finset (Fin 8)) (hP : P.card ≤ 2) : ∃ a, ∀ i ∈ P, a ∈ row i := by
    by_cases h : P.card = 2
    · obtain ⟨i,j,_,rfl⟩ := card_eq_two.mp h
      obtain ⟨a,ha⟩ := meet i j
      exact ⟨a,by simpa using mem_inter.mp ha⟩
    by_cases h' : P.card = 1
    · obtain ⟨i,rfl⟩ := card_eq_one.mp h'
      obtain ⟨a,ha⟩ := meet i i
      exact ⟨a,by simpa using (mem_inter.mp ha).1⟩
    have hem : P = ∅ := card_eq_zero.mp (by omega)
    exact ⟨fallback,by simp [hem]⟩
  induction k generalizing G with
  | zero =>
    have h : G = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅,by simp,by simp [h]⟩
  | succ k ih =>
    obtain ⟨P,hPG,hP⟩ := exists_subset_card_eq (s := G) (n := min 2 G.card) (min_le_right ..)
    obtain ⟨a,ha⟩ := pair P (hP.trans_le (min_le_left ..))
    obtain ⟨S,hsize,hcover⟩ := ih (G \ P) (by rw [card_sdiff_of_subset hPG,hP]; omega)
    refine ⟨insert a S,(card_insert_le ..).trans (by omega),?_⟩
    intro i hi
    by_cases hp : i ∈ P
    · exact ⟨a,mem_inter.mpr ⟨mem_insert_self ..,ha i hp⟩⟩
    · obtain ⟨b,hb⟩ := hcover i (mem_sdiff.mpr ⟨hi,hp⟩)
      exact ⟨b,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hb).1,(mem_inter.mp hb).2⟩⟩

theorem residual {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (h12 : F.card = 12) (hsize : ∀ A ∈ F, A.card = 5)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hmiss : ∀ S : Finset α, S.card ≤ 4 → ∃ A ∈ F, Disjoint S A)
    (x : α) (hx : (F.filter (x ∈ ·)).card = 4) :
    ∃ T : Finset (Finset (Fin 8)),
      (∀ A ∈ T, A.card = 3) ∧ (∀ A ∈ T, ∀ B ∈ T, (A ∩ B).Nonempty) ∧
      (∀ i : Fin 8, ∃ A ∈ T, ∃ B ∈ T, A ∩ B = {i}) := by
  classical
  let R := F.filter (fun A => x ∉ A)
  have hR : R.card = 8 := by
    have := F.card_filter_add_card_filter_not (fun A => x ∈ A)
    dsimp [R]
    omega
  let e : Fin 8 ≃ R := (Fintype.equivFinOfCardEq (by simpa using hR)).symm
  let row (i : Fin 8) : Finset α := e i
  let star (y : α) := univ.filter fun i => y ∈ row i
  have inStar (i : Fin 8) (y : α) : i ∈ star y ↔ y ∈ row i := by simp [star]
  have rowF (i : Fin 8) : row i ∈ F := (mem_filter.mp (e i).property).1
  have meet (i j : Fin 8) := hinter _ (rowF i) _ (rowF j)
  have size (i : Fin 8) := hsize _ (rowF i)
  have miss (S : Finset α) (hS : S.card ≤ 3) : ∃ i, Disjoint S (row i) := by
    obtain ⟨A,hA,hd⟩ := hmiss (insert x S) ((card_insert_le ..).trans (by omega))
    have hxA : x ∉ A := fun ha => disjoint_left.mp hd (mem_insert_self ..) ha
    have haR : A ∈ R := mem_filter.mpr ⟨hA,hxA⟩
    refine ⟨e.symm ⟨A,haR⟩,?_⟩
    simp only [row,Equiv.apply_symm_apply]
    exact hd.mono_left (subset_insert ..)
  have budget (P : Finset α) (k : ℕ) (hk : P.card + k ≤ 3) :
      2*k < (univ \ P.biUnion star).card := by
    by_contra! h
    obtain ⟨S,hS,hit⟩ := pairCover row meet x k _ h
    obtain ⟨i,hd⟩ := miss (P ∪ S) ((card_union_le ..).trans (by omega))
    have hi : i ∈ univ \ P.biUnion star := by
      refine mem_sdiff.mpr ⟨mem_univ _,fun hmem => ?_⟩
      obtain ⟨y,hy,hyi⟩ := mem_biUnion.mp hmem
      exact disjoint_left.mp hd (mem_union_left _ hy) ((inStar i y).mp hyi)
    obtain ⟨b,hb⟩ := hit i hi
    exact disjoint_left.mp hd (mem_union_right _ (mem_inter.mp hb).1) (mem_inter.mp hb).2
  have cap (y : α) : (star y).card ≤ 3 := by
    have h := budget {y} 2 (by simp)
    simp only [singleton_biUnion,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin] at h
    omega
  have triplesMeet {a b : α} (ha : (star a).card = 3) (hb : (star b).card = 3) :
      (star a ∩ star b).Nonempty := by
    by_contra! hn
    have hd : Disjoint (star a) (star b) := disjoint_iff_inter_eq_empty.mpr hn
    have hab : a ≠ b := by
      rintro rfl
      have := disjoint_self.mp hd
      simp [this] at ha
    have ht := budget {a,b} 1 (by simp [hab])
    simp only [biUnion_insert,singleton_biUnion,card_sdiff_of_subset (subset_univ _),
      card_union_of_disjoint hd,card_univ,Fintype.card_fin,ha,hb] at ht
    omega
  have first (i : Fin 8) : ∃ z ∈ row i, (star z).card = 3 := by
    by_contra! hn
    have sub : univ.erase i ⊆ (row i).biUnion (fun y => (star y).erase i) := by
      intro j hj
      obtain ⟨y,hy⟩ := meet i j
      exact mem_biUnion.mpr ⟨y,(mem_inter.mp hy).1,mem_erase.mpr ⟨(mem_erase.mp hj).1,
        (inStar j y).mpr (mem_inter.mp hy).2⟩⟩
    have h := (card_le_card sub).trans (card_biUnion_le_card_mul _ _ 1 (by
      intro y hy
      rw [card_erase_of_mem ((inStar i y).mpr hy)]
      have := hn y hy
      have := cap y
      omega))
    simp only [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin,size,mul_one] at h
    omega
  have partner (i : Fin 8) (z : α) (hz : z ∈ row i) (h3 : (star z).card = 3) :
      ∃ y ∈ row i, (star y).card = 3 ∧ star z ∩ star y = {i} := by
    by_contra! hn
    have sub : univ \ star z ⊆ ((row i).erase z).biUnion (fun y => star y \ star z) := by
      intro j hj
      obtain ⟨y,hy⟩ := meet i j
      have hyj := (inStar j y).mpr (mem_inter.mp hy).2
      have hyz : y ≠ z := fun heq => (mem_sdiff.mp hj).2 (heq ▸ hyj)
      exact mem_biUnion.mpr ⟨y,mem_erase.mpr ⟨hyz,(mem_inter.mp hy).1⟩,mem_sdiff.mpr ⟨hyj,(mem_sdiff.mp hj).2⟩⟩
    have small (y : α) (hy : y ∈ (row i).erase z) : (star y \ star z).card ≤ 1 := by
      have hyi := mem_of_mem_erase hy
      have hi : i ∈ star z ∩ star y := mem_inter.mpr ⟨(inStar i z).mpr hz,(inStar i y).mpr hyi⟩
      have hp := card_pos.mpr ⟨i,hi⟩
      have hc := card_sdiff_add_card_inter (star y) (star z)
      rw [inter_comm] at hc
      by_cases h : (star y).card = 3
      · have hne := hn y hyi h
        have hn1 : (star z ∩ star y).card ≠ 1 := by
          intro heq
          obtain ⟨b,hb⟩ := card_eq_one.mp heq
          have hib : i = b := mem_singleton.mp (hb ▸ hi)
          exact hne (hib ▸ hb)
        omega
      · have := cap y
        omega
    have h := (card_le_card sub).trans (card_biUnion_le_card_mul _ _ 1 small)
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,h3,card_erase_of_mem hz,size] at h
    omega
  let D := (univ.biUnion row).filter fun y => (star y).card = 3
  refine ⟨D.image star,?_,?_,?_⟩
  · intro A hA
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    exact (mem_filter.mp ha).2
  · intro A hA B hB
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hB
    exact triplesMeet (mem_filter.mp ha).2 (mem_filter.mp hb).2
  · intro i
    obtain ⟨z,hz,h3⟩ := first i
    obtain ⟨y,hy,hy3,hint⟩ := partner i z hz h3
    have incl (a : α) (ha : a ∈ row i) (h : (star a).card = 3) : star a ∈ D.image star :=
      mem_image_of_mem _ (mem_filter.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,ha⟩,h⟩)
    exact ⟨star z,incl z hz h3,star y,incl y hy hy3,hint⟩

end EightResidual

namespace Eight

private abbrev Pt := Fin 8
private abbrev Row := Finset Pt
private def left : Row := {0,1,2}
private def right : Row := {0,3,4}
private def candidates (i : Pt) : Finset Row :=
  (univ.powersetCard 3).filter (fun A => i ∈ A ∧ (A ∩ left).Nonempty ∧ (A ∩ right).Nonempty)
private def options (i : Pt) :=
  ((candidates i) ×ˢ (candidates i)).filter (fun p => p.1 ∩ p.2 = {i})
private def compatible (p q : Row × Row) : Prop :=
  (p.1 ∩ q.1).Nonempty ∧ (p.1 ∩ q.2).Nonempty ∧
  (p.2 ∩ q.1).Nonempty ∧ (p.2 ∩ q.2).Nonempty
private instance (p q : Row × Row) : Decidable (compatible p q) := by
  unfold compatible
  infer_instance

private def decode (a : ℕ) : Row := univ.filter (fun x : Pt => a.testBit x.val)
private def asRows (p : ℕ × ℕ) : Row × Row := (decode p.1,decode p.2)
private def orient (xs : List (ℕ × ℕ)) := xs ++ xs.map Prod.swap
private def table5 : List (ℕ × ℕ) :=
  [(35,44),(35,52),(37,42),(37,50),(41,50),(41,52),(42,49),(42,52),(42,97),(42,161),(44,49),(44,50),(44,97),(44,161),(50,97),(50,161),(52,97),(52,161)]
private def table6 : List (ℕ × ℕ) :=
  [(67,76),(67,84),(69,74),(69,82),(73,82),(73,84),(74,81),(74,84),(74,97),(74,193),(76,81),(76,82),(76,97),(76,193),(82,97),(82,193),(84,97),(84,193)]
private def table7 : List (ℕ × ℕ) :=
  [(131,140),(131,148),(133,138),(133,146),(137,146),(137,148),(138,145),(138,148),(138,161),(138,193),(140,145),(140,146),(140,161),(140,193),(146,161),(146,193),(148,161),(148,193)]
private def covers (i : Pt) (xs : List (ℕ × ℕ)) : Prop :=
  options i ⊆ ((orient xs).toFinset.image asRows)
private instance (i : Pt) (xs) : Decidable (covers i xs) := by unfold covers; infer_instance
set_option maxRecDepth 4096 in
private theorem c5 : covers 5 table5 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem c6 : covers 6 table6 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem c7 : covers 7 table7 := by decide +kernel

private def cross (p q : ℕ × ℕ) : Bool :=
  (p.1 &&& q.1 != 0) && (p.1 &&& q.2 != 0) && (p.2 &&& q.1 != 0) && (p.2 &&& q.2 != 0)
private theorem cert :
    (orient table5).all (fun p => (orient table6).all (fun q =>
      !cross p q || (orient table7).all (fun r => !(cross p r && cross q r)))) = true := by
  decide +kernel
private theorem cross_of (p q) (hc : compatible (asRows p) (asRows q)) : cross p q = true := by
  have pos (a b) (h : (decode a ∩ decode b).Nonempty) : (a &&& b != 0) = true := by
    obtain ⟨x,hx⟩ := h
    have ha := (mem_filter.mp (mem_inter.mp hx).1).2
    have hb := (mem_filter.mp (mem_inter.mp hx).2).2
    apply bne_iff_ne.mpr
    intro he
    have hh := congrArg (fun n : ℕ => n.testBit x.val) he
    simp [Nat.testBit_and,ha,hb] at hh
  simp only [cross,Bool.and_eq_true]
  exact ⟨⟨⟨pos _ _ hc.1,pos _ _ hc.2.1⟩,pos _ _ hc.2.2.1⟩,pos _ _ hc.2.2.2⟩
private theorem no_extension (p) (hp : p ∈ options 5) (q) (hq : q ∈ options 6)
    (hpq : compatible p q) (r) (hr : r ∈ options 7) (hc : compatible p r ∧ compatible q r) : False := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp (c5 hp)
  obtain ⟨b,hb,rfl⟩ := mem_image.mp (c6 hq)
  obtain ⟨d,hd,rfl⟩ := mem_image.mp (c7 hr)
  have h := List.all_eq_true.mp (List.all_eq_true.mp cert a (List.mem_toFinset.mp ha)) b (List.mem_toFinset.mp hb)
  simp only [cross_of _ _ hpq,Bool.not_true,Bool.false_or] at h
  have hh := List.all_eq_true.mp h d (List.mem_toFinset.mp hd)
  simp [cross_of _ _ hc.1,cross_of _ _ hc.2] at hh

private theorem normalized (T : Finset Row) (size : ∀ A ∈ T, A.card = 3)
    (inter : ∀ A ∈ T, ∀ B ∈ T, (A ∩ B).Nonempty)
    (wit : ∀ i : Pt, ∃ A ∈ T, ∃ B ∈ T, A ∩ B = {i})
    (hl : left ∈ T) (hr : right ∈ T) : False := by
  have get (i : Pt) : ∃ p ∈ options i, p.1 ∈ T ∧ p.2 ∈ T := by
    obtain ⟨A,hA,B,hB,hAB⟩ := wit i
    have hi : i ∈ A ∩ B := hAB.symm ▸ mem_singleton_self i
    have inc (D) (hD : D ∈ T) (hiD : i ∈ D) : D ∈ candidates i :=
      mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,size D hD⟩,
        hiD,inter D hD left hl,inter D hD right hr⟩
    exact ⟨(A,B),mem_filter.mpr ⟨mem_product.mpr ⟨inc A hA (mem_inter.mp hi).1,
      inc B hB (mem_inter.mp hi).2⟩,hAB⟩, hA,hB⟩
  have comp (p q : Row × Row) (hp : p.1 ∈ T ∧ p.2 ∈ T)
      (hq : q.1 ∈ T ∧ q.2 ∈ T) : compatible p q :=
    ⟨inter _ hp.1 _ hq.1,inter _ hp.1 _ hq.2,inter _ hp.2 _ hq.1,inter _ hp.2 _ hq.2⟩
  obtain ⟨p,hp,hpt⟩ := get 5
  obtain ⟨q,hq,hqt⟩ := get 6
  obtain ⟨r,hr,hrt⟩ := get 7
  exact no_extension p hp q hq (comp p q hpt hqt) r hr ⟨comp p r hpt hrt,comp q r hqt hrt⟩

private theorem no_eight (T : Finset Row) (size : ∀ A ∈ T, A.card = 3)
    (inter : ∀ A ∈ T, ∀ B ∈ T, (A ∩ B).Nonempty)
    (wit : ∀ i : Pt, ∃ A ∈ T, ∃ B ∈ T, A ∩ B = {i}) : False := by
  classical
  obtain ⟨A,hA,B,hB,hAB⟩ := wit 0
  have h0 : (0 : Pt) ∈ A ∩ B := hAB.symm ▸ mem_singleton_self _
  have ha := (mem_inter.mp h0).1
  have hb := (mem_inter.mp h0).2
  obtain ⟨a,b,_,eA⟩ := card_eq_two.mp (show (A.erase 0).card = 2 by
    rw [card_erase_of_mem ha,size A hA])
  obtain ⟨c,d,_,eB⟩ := card_eq_two.mp (show (B.erase 0).card = 2 by
    rw [card_erase_of_mem hb,size B hB])
  have outside : (univ \ (A ∪ B)).card = 3 := by
    have hs := card_union_add_card_inter A B
    rw [size A hA,size B hB,hAB,card_singleton] at hs
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
    omega
  obtain ⟨f,g,h,_,_,_,out⟩ := card_eq_three.mp outside
  have aform : A = {0,a,b} := by rw [← eA,insert_erase ha]
  have bform : B = {0,c,d} := by rw [← eB,insert_erase hb]
  let L : Pt → Pt := ![0,a,b,c,d,f,g,h]
  have surj : Function.Surjective L := by
    intro y
    by_cases hya : y ∈ A
    · rw [aform] at hya
      simp only [mem_insert,mem_singleton] at hya
      rcases hya with rfl|rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    by_cases hyb : y ∈ B
    · rw [bform] at hyb
      simp only [mem_insert,mem_singleton] at hyb
      rcases hyb with rfl|rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨4,rfl⟩
    have hy : y ∈ univ \ (A ∪ B) := mem_sdiff.mpr ⟨mem_univ _,by simp [hya,hyb]⟩
    rw [out] at hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl|rfl|rfl
    · exact ⟨5,rfl⟩
    · exact ⟨6,rfl⟩
    · exact ⟨7,rfl⟩
  let e : Pt ≃ Pt := Equiv.ofBijective L ⟨(Finite.injective_iff_surjective).mpr surj,surj⟩
  let ren (R : Row) := R.map e.symm.toEmbedding
  have ihit (R S : Row) : ren (R ∩ S) = ren R ∩ ren S := map_inter ..
  have lmap : left.map e.toEmbedding = A := by
    rw [aform]
    simp only [left,map_insert,map_singleton]
    rfl
  have rmap : right.map e.toEmbedding = B := by
    rw [bform]
    simp only [right,map_insert,map_singleton]
    rfl
  have back (R : Row) : ren (R.map e.toEmbedding) = R := by simp [ren,map_map]
  apply normalized (T.image ren)
  · intro R hR
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hR
    simpa only [ren,card_map] using size S hS
  · intro R hR S hS
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hR
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hS
    rw [← ihit]
    exact (inter A hA B hB).map
  · intro i
    obtain ⟨R,hR,S,hS,hi⟩ := wit (e i)
    refine ⟨ren R,mem_image_of_mem _ hR,ren S,mem_image_of_mem _ hS,?_⟩
    rw [← ihit,hi]
    simp [ren]
  · exact mem_image.mpr ⟨A,hA,lmap ▸ back left⟩
  · exact mem_image.mpr ⟨B,hB,rmap ▸ back right⟩

end Eight

theorem OMA.solution : OMA.R_Erdos21_erdos_21_variants_small_values_R1.H2 := by
  intro F hF
  by_contra! hc
  have h12 : F.card = 12 := by have := OrderFive.twelve_le F hF; omega
  obtain ⟨A,hA,_⟩ := hF.2.2 ∅ (by simp)
  obtain ⟨x,hx⟩ : ∃ x : ℕ, (F.filter (x ∈ ·)).card = 4 := by
    by_contra! hn
    have total := (OrderFive.neighbors hF Subset.rfl hA).trans
      (Finset.sum_le_sum (g := fun _ => 2) (by
        intro x _
        have := OrderFive.degree_limit hF x
        have := hn x
        omega))
    simp [hF.1 A hA,h12] at total
  obtain ⟨T,hsize,hinter,hsingle⟩ := EightResidual.residual h12 hF.1 hF.2.1 hF.2.2 x hx
  exact Eight.no_eight T hsize hinter hsingle
