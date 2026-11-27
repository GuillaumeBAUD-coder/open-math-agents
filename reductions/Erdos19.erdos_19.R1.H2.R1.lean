import OMAReductions.R_Erdos19_erdos_19_R1

/-!
The disjointness graph joins two supports when they can share a color.
If this graph is bipartite, its two parts consist of intersecting supports.
Fisher's incidence-vector argument bounds every intersecting subfamily by n;
Hall's theorem then allows both parts to use the same n colors.

For the remaining families a disjoint triple saves two colors immediately.
When there is no disjoint triple, a color class has at most two members and
the remaining task is a matching of size |K|-n in the disjointness graph.
A local packing count around a minimum support also excludes the first
interval above the square of its size.
-/

-- Credit: @zarnab222-dev

section

open Finset

namespace E19Fisher

/-- Distinct blocks meet exactly once, so their real incidence vectors are independent. -/
theorem fisher_one {n : ℕ} (K : Finset (Finset (Fin n)))
    (size : ∀ A ∈ K, 2 ≤ A.card)
    (one : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card = 1) : K.card ≤ n := by
  classical
  let v (A : K) (i : Fin n) : ℝ := if i ∈ A.val then 1 else 0
  have gram (A B : K) : (∑ i ∈ A.val, v B i) =
      1 + (if B=A then (A.val.card:ℝ)-1 else 0) := by
    by_cases same : B=A
    · subst B
      simp [v]
    · have diff : A.val ≠ B.val := fun he => same (Subtype.ext he.symm)
      simp [v, same, one _ A.property _ B.property diff]
  have independent : LinearIndependent ℝ v := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro g relation
    let T : ℝ := ∑ B : K, g B
    have column (i : Fin n) : ∑ B : K, g B * v B i = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        using congrFun relation i
    have row (A : K) : T + g A * ((A.val.card:ℝ)-1) = 0 := by
      have he : ∑ B : K, g B * (∑ i ∈ A.val, v B i) = 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [column, Finset.sum_const_zero]
      simp only [gram, mul_add, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib] at he
      simpa [T] using he
    have weight (A : K) : 0 < (A.val.card:ℝ)-1 := by
      have h : (2:ℝ) ≤ A.val.card := by exact_mod_cast size _ A.property
      linarith
    have total : T=0 := by
      rcases lt_trichotomy T 0 with ht | ht | ht
      · have hpos (A : K) : 0 ≤ g A := by
          by_contra! hbad
          linarith [row A, mul_neg_of_neg_of_pos hbad (weight A)]
        exact (ht.not_ge (Finset.sum_nonneg fun A _ => hpos A)).elim
      · exact ht
      · have hneg (A : K) : g A ≤ 0 := by
          by_contra! hbad
          linarith [row A, mul_pos hbad (weight A)]
        exact (ht.not_ge (Finset.sum_nonpos fun A _ => hneg A)).elim
    intro A
    have h := row A
    rw [total,zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (weight A).ne'
  simpa only [Fintype.card_coe, Module.finrank_fin_fun] using independent.fintype_card_le_finrank

/-- At most n mutually intersecting linear supports of size at least two fit on n indices. -/
theorem fisher_bound {n : ℕ} (K : Finset (Finset (Fin n)))
    (size : ∀ A ∈ K, 2 ≤ A.card)
    (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (intersect : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty) : K.card ≤ n := by
  apply fisher_one K size
  intro A hA B hB hne
  have hpos := Finset.card_pos.mpr (intersect A hA B hB hne)
  have hle := linear A hA B hB hne
  omega

end E19Fisher

end

section

open Finset

namespace E19Packing

theorem packing_bound {n r : ℕ} (H : Finset (Finset (Fin n))) (hr : 2 ≤ r)
    (hsize : ∀ A ∈ H, r ≤ A.card)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    {T : Finset (Fin n)} (hT : T ∈ H) (hcard : T.card = r)
    (hmeet : n ≤ ((H.erase T).filter fun A => (T ∩ A).Nonempty).card) :
    n ≤ r * ((n-r)/(r-1)) := by
  classical
  let J := (H.erase T).filter fun A => (T ∩ A).Nonempty
  let through (x : Fin n) := J.filter fun A => x ∈ A
  have rows {x : Fin n} {A : Finset (Fin n)} (h : A ∈ through x) :
      A ∈ H ∧ A ≠ T ∧ x ∈ A := by
    obtain ⟨hJ,hx⟩ := mem_filter.mp h
    obtain ⟨hne,ha⟩ := mem_erase.mp (mem_filter.mp hJ).1
    exact ⟨ha,hne,hx⟩
  have localBound (x : Fin n) (hx : x ∈ T) : (through x).card * (r - 1) ≤ n - r := by
    have dis : (through x : Set (Finset (Fin n))).PairwiseDisjoint (fun A => A \ T) := by
      intro A hA B hB hAB
      apply disjoint_left.mpr
      intro y hyA hyB
      have hxy : x ≠ y := fun heq => (mem_sdiff.mp hyA).2 (heq ▸ hx)
      have both : {x,y} ⊆ A ∩ B := by
        rw [insert_subset_iff,singleton_subset_iff]
        exact ⟨mem_inter.mpr ⟨(rows hA).2.2,(rows hB).2.2⟩,
          mem_inter.mpr ⟨(mem_sdiff.mp hyA).1,(mem_sdiff.mp hyB).1⟩⟩
      have size := (card_le_card both).trans (hlin A (rows hA).1 B (rows hB).1 hAB)
      simp [card_pair hxy] at size
    have lower (A : Finset (Fin n)) (hA : A ∈ through x) : r - 1 ≤ (A \ T).card := by
      have a := rows hA
      have := hlin A a.1 T hT a.2.1
      have := hsize A a.1
      have := card_sdiff_add_card_inter A T
      omega
    have incl : (through x).biUnion (fun A => A \ T) ⊆ univ \ T := by
      intro y hy
      obtain ⟨A,_,hyA⟩ := mem_biUnion.mp hy
      exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hyA).2⟩
    have bound := card_le_card incl
    rw [card_biUnion dis,card_sdiff_of_subset (subset_univ T),card_univ,Fintype.card_fin,hcard] at bound
    simpa only [sum_const,smul_eq_mul] using (sum_le_sum lower).trans bound
  have incl : J ⊆ T.biUnion through := by
    intro A ha
    obtain ⟨x,hx⟩ := (mem_filter.mp ha).2
    exact mem_biUnion.mpr ⟨x,(mem_inter.mp hx).1,mem_filter.mpr ⟨ha,(mem_inter.mp hx).2⟩⟩
  have count : n ≤ ∑ x ∈ T, (through x).card :=
    hmeet.trans ((card_le_card incl).trans card_biUnion_le)
  have bound (x : Fin n) (hx : x ∈ T) : (through x).card ≤ (n-r)/(r-1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (localBound x hx)
  simpa only [sum_const,smul_eq_mul,hcard] using count.trans (sum_le_sum bound)

/-- The first band strictly above the square cannot support a critical family. -/
theorem first_gap {n r : ℕ} (hr : 3 ≤ r) (sq : r*r < n)
    (bound : n ≤ r*((n-r)/(r-1))) : r*r+r-1 ≤ n := by
  let q := (n-r)/(r-1)
  have step : r+1 ≤ q := by
    by_contra! h
    have := Nat.mul_le_mul_left r (show q ≤ r by omega)
    change n ≤ r*q at bound
    omega
  have prod := (Nat.mul_le_mul_right (r-1) step).trans (Nat.div_mul_le_self (n-r) (r-1))
  have cover : r ≤ n := by nlinarith
  have a : r-1+1=r := by omega
  have b : n-r+r=n := by omega
  have id : (r+1)*(r-1)+1=r*r := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  omega

end E19Packing

end

section

open Finset

namespace E19PairColor

/-- Use one color for each independent group and a fresh color for each uncovered support. -/
theorem color_of_groups {n : ℕ} {ι : Type*} [Fintype ι] (K : Finset (Finset (Fin n)))
    (groups : ι → Finset (Finset (Fin n)))
    (independent : ∀ i, ∀ A ∈ groups i, ∀ B ∈ groups i, A ≠ B → Disjoint A B)
    (bound : (K \ univ.biUnion groups).card + Fintype.card ι ≤ n) :
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  let remaining := K \ univ.biUnion groups
  let colors := (↥remaining) ⊕ ι
  have cover (A : K) : ∃ r : colors, match r with
      | Sum.inl v => A.val = v.val
      | Sum.inr i => A.val ∈ groups i := by
    by_cases h : ∃ i, A.val ∈ groups i
    · obtain ⟨i,hi⟩ := h
      exact ⟨Sum.inr i,hi⟩
    · have hm : A.val ∈ remaining :=
        mem_sdiff.mpr ⟨A.property, fun hu =>
          let ⟨i,_,hi⟩ := mem_biUnion.mp hu
          h ⟨i,hi⟩⟩
      exact ⟨Sum.inl ⟨A.val,hm⟩,rfl⟩
  choose r hr using cover
  have size : Fintype.card colors ≤ n := by
    simpa only [colors, remaining, Fintype.card_sum, Fintype.card_coe] using bound
  let e : colors ↪ Fin n := (Fintype.equivFin colors).toEmbedding.trans (Fin.castLEEmb size)
  refine ⟨fun A => e (r A), ?_⟩
  intro A B hne meet same
  have eq := e.injective same
  have ha := hr A
  have hb := hr B
  rw [← eq] at hb
  cases h : r A with
  | inl v =>
    rw [h] at ha hb
    exact hne (Subtype.ext (ha.trans hb.symm))
  | inr i =>
    rw [h] at ha hb
    obtain ⟨p,hp⟩ := meet
    exact disjoint_left.mp (independent i _ ha _ hb (fun he => hne (Subtype.ext he)))
      (mem_inter.mp hp).1 (mem_inter.mp hp).2

/-- A matching of t disjoint pairs in the support family saves t colors. -/
theorem color_of_pairs {n t : ℕ} (K : Finset (Finset (Fin n)))
    (L R : Fin t → Finset (Fin n)) (hL : ∀ i, L i ∈ K) (hR : ∀ i, R i ∈ K)
    (injL : Function.Injective L) (injR : Function.Injective R)
    (separated : ∀ i j, L i ≠ R j) (dis : ∀ i, Disjoint (L i) (R i))
    (bound : K.card ≤ n + t) :
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  let groups (i : Fin t) : Finset (Finset (Fin n)) := {L i, R i}
  apply color_of_groups K groups
  · intro i A hA B hB hne
    simp only [groups, mem_insert, mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hne rfl).elim
    · exact dis i
    · exact (dis i).symm
    · exact (hne rfl).elim
  · have united : univ.biUnion groups = univ.image L ∪ univ.image R := by
      ext A
      simp [groups, exists_or, eq_comm]
    have apart : Disjoint (univ.image L) (univ.image R) := by
      refine disjoint_left.mpr fun A ha hb => ?_
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      obtain ⟨j,_,hj⟩ := mem_image.mp hb
      exact separated i j hj.symm
    have inside : univ.biUnion groups ⊆ K := by
      intro A hA
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hA
      rcases (show A = L i ∨ A = R i by simpa [groups] using hi) with rfl | rfl
      · exact hL i
      · exact hR i
    have count : (univ.biUnion groups).card = t+t := by
      rw [united, card_union_of_disjoint apart, card_image_of_injective _ injL,
        card_image_of_injective _ injR, card_univ, Fintype.card_fin]
    have total := card_le_card inside
    rw [count] at total
    rw [card_sdiff_of_subset inside, count, Fintype.card_fin]
    omega

/-- Merging one independent group saves one fewer color than the size of the group. -/
theorem color_of_group {n : ℕ} (K T : Finset (Finset (Fin n))) (hT : T ⊆ K)
    (independent : ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B)
    (bound : K.card + 1 ≤ n + T.card) :
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  apply color_of_groups K (fun _ : Unit => T) (fun _ => independent)
  have total := card_le_card hT
  have united : univ.biUnion (fun _ : Unit => T) = T := by
    ext A
    simp
  rw [united, card_sdiff_of_subset hT, Fintype.card_unit]
  omega


end E19PairColor

end

section

open Finset
open scoped Classical

namespace E19TwoCliques

theorem two_lists {L R : Type*} [Fintype L] [Fintype R] {n : ℕ}
    (conflict : L → R → Prop) (a : L ↪ Fin n)
    (bound : ∀ (S : Finset R) (F : Finset L), (∀ l, l ∈ F ↔ ∀ s ∈ S, conflict l s) → S.card + F.card ≤ n) :
    ∃ b : R → Fin n, Function.Injective b ∧ ∀ l r, conflict l r → a l ≠ b r := by
  classical
  let colors (r : R) := (univ : Finset (Fin n)).filter fun c =>
    ∀ l, a l = c → ¬ conflict l r
  have hall (S : Finset R) : S.card ≤ (S.biUnion colors).card := by
    by_cases empty : S = ∅
    · simp [empty]
    have someR := Finset.nonempty_iff_ne_empty.mpr empty
    let B := (univ : Finset L).filter fun l => ∀ r ∈ S, conflict l r
    have missing : (S.biUnion colors)ᶜ ⊆ B.map a := by
      intro c h
      have hc := Finset.mem_compl.mp h
      by_contra hB
      by_cases used : ∃ l, a l = c
      · obtain ⟨l,rfl⟩ := used
        have nl : l ∉ B := fun hl => hB (mem_map.mpr ⟨l,hl,rfl⟩)
        obtain ⟨r,hr,free⟩ : ∃ r ∈ S, ¬ conflict l r := by
          by_contra! all
          exact nl (mem_filter.mpr ⟨mem_univ _,all⟩)
        apply hc (mem_biUnion.mpr ⟨r,hr,mem_filter.mpr ⟨mem_univ _,?_⟩⟩)
        intro k eq
        exact a.injective eq ▸ free
      · obtain ⟨r,hr⟩ := someR
        exact hc (mem_biUnion.mpr ⟨r,hr,mem_filter.mpr ⟨mem_univ _,
          fun l hl => False.elim (used ⟨l,hl⟩)⟩⟩)
    have lower := card_le_card missing
    have total := card_compl_add_card (S.biUnion colors)
    have cap : S.card+B.card ≤ n := bound S B (by intro l; simp [B])
    simp only [card_map] at lower
    simp only [Fintype.card_fin] at total
    omega
  obtain ⟨b,inj,allowed⟩ := (all_card_le_biUnion_card_iff_existsInjective' colors).mp hall
  exact ⟨b,inj,fun l r con eq => (mem_filter.mp (allowed r)).2 l eq con⟩

private theorem neighborhood_bound {n : ℕ} (K L R : Finset (Finset (Fin n))) (unionKR : L ∪ R = K)
    (separate : Disjoint L R)
    (left : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty)
    (right : ∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)
    (width : ∀ J ⊆ K, (∀ A ∈ J, ∀ B ∈ J, A ≠ B → (A ∩ B).Nonempty) → J.card ≤ n) (S : Finset R) (F : Finset L)
    (hf : ∀ l, l ∈ F ↔ ∀ s ∈ S, (l.val ∩ s.val).Nonempty) : S.card+F.card ≤ n := by
  classical
  have subL : L ⊆ K := by rw [← unionKR]; exact subset_union_left
  have subR : R ⊆ K := by rw [← unionKR]; exact subset_union_right
  let X := F.map (Function.Embedding.subtype _)
  let Y := S.map (Function.Embedding.subtype _)
  have memX {A} : A ∈ X → A ∈ L := fun h => by
    obtain ⟨v,_,rfl⟩ := mem_map.mp h
    exact v.property
  have memY {A} : A ∈ Y → A ∈ R := fun h => by
    obtain ⟨v,_,rfl⟩ := mem_map.mp h
    exact v.property
  have cross {A B} (ha : A ∈ X) (hb : B ∈ Y) : (A ∩ B).Nonempty := by
    obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
    exact (hf u).mp hu v hv
  have dis : Disjoint Y X := disjoint_left.mpr fun y hy hx => disjoint_left.mp separate (memX hx) (memY hy)
  have cap := width (Y ∪ X) (union_subset (fun _ h => subR (memY h)) (fun _ h => subL (memX h))) (by
    intro A ha B hb ne
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact right _ (memY ha) _ (memY hb) ne
    · simpa only [inter_comm B A] using cross hb ha
    · exact cross ha hb
    · exact left _ (memX ha) _ (memX hb) ne)
  simpa only [card_union_of_disjoint dis,X,Y,card_map] using cap

set_option maxHeartbeats 550000 in
/-- Two internally intersecting classes have a common palette of n colors
whenever every mutually intersecting subfamily has at most n supports. -/
theorem two_cliques {n : ℕ} (K L R : Finset (Finset (Fin n))) (unionKR : L ∪ R = K)
    (separate : Disjoint L R)
    (left : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty)
    (right : ∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)
    (width : ∀ J ⊆ K, (∀ A ∈ J, ∀ B ∈ J, A ≠ B → (A ∩ B).Nonempty) → J.card ≤ n) :
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  have subL : L ⊆ K := by rw [← unionKR]; exact subset_union_left
  have subR : R ⊆ K := by rw [← unionKR]; exact subset_union_right
  have small : Fintype.card L ≤ n := by simpa only [Fintype.card_coe] using width L subL left
  let a : L ↪ Fin n := (Fintype.equivFin L).toEmbedding.trans (Fin.castLEEmb small)
  let adj (l : L) (s : R) := (l.val ∩ s.val).Nonempty
  obtain ⟨b,bi,good⟩ := two_lists (L := ↥L) (R := ↥R) (n := n) adj a (neighborhood_bound K L R unionKR separate left right width)
  have other (v : K) (h : v.val ∉ L) : v.val ∈ R := by
    have sub : K ⊆ L ∪ R := unionKR.ge
    exact (mem_union.mp (sub v.property)).resolve_left h
  let c (v : K) := if h : v.val ∈ L then a ⟨v.val,h⟩ else b ⟨v.val,other v h⟩
  refine ⟨c,?_⟩
  intro A B ne meet
  by_cases ha : A.val ∈ L <;> by_cases hb : B.val ∈ L <;> simp only [c,ha,hb,↓reduceDIte]
  · exact fun eq => ne (Subtype.ext (congrArg (fun l : L => l.val) (a.injective eq)))
  · exact good ⟨A.val,ha⟩ ⟨B.val,other B hb⟩ meet
  · have rev : (B.val ∩ A.val).Nonempty := by rwa [inter_comm]
    exact (good ⟨B.val,hb⟩ ⟨A.val,other A ha⟩ rev).symm
  · exact fun eq => ne (Subtype.ext (congrArg (fun r : R => r.val) (bi eq)))

end E19TwoCliques

end

open Finset
open scoped Classical
namespace OMA.R_Erdos19_erdos_19_R1_H2_R1

def H1 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r+r-1 ≤ n →
    n ≤ r*((n-r)/(r-1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →

    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) → n+2 < K.card →
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

def H2 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r+r-1 ≤ n →
    n ≤ r*((n-r)/(r-1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →

    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∃ L R : Fin (K.card-n) → Finset (Fin n), (∀ i, L i ∈ K) ∧ (∀ i, R i ∈ K) ∧
      Function.Injective L ∧ Function.Injective R ∧ (∀ i j, L i ≠ R j) ∧ ∀ i, Disjoint (L i) (R i)


section
theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1.H2 := by
  intro triples pairs n r K hr square witness sz lin degree big disorder
  classical
  obtain ⟨T,hT,hcard⟩ := witness
  have pack := E19Packing.packing_bound K (by omega : 2 ≤ r) sz lin hT hcard (degree T hT)
  have gap := E19Packing.first_gap hr square pack
  by_cases split : ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)
  · obtain ⟨L,R,covers,apart,cl,cr⟩ := split
    apply E19TwoCliques.two_cliques K L R covers apart cl cr
    intro J sub meet
    exact E19Fisher.fisher_bound J (fun A hA => (by omega : 2 ≤ r).trans (sz A (sub hA)))
      (fun A hA B hB => lin A (sub hA) B (sub hB)) meet
  by_cases three : ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B
  · by_cases small : K.card ≤ n+2
    · obtain ⟨U,hU,count,ind⟩ := three
      exact E19PairColor.color_of_group K U hU ind (by omega)
    exact triples n r K hr gap pack ⟨T,hT,hcard⟩ sz lin degree big disorder split three (by omega)
  obtain ⟨L,R,hL,hR,injL,injR,apart,dis⟩ := pairs n r K hr gap pack ⟨T,hT,hcard⟩ sz lin degree big disorder split three
  exact E19PairColor.color_of_pairs K L R hL hR injL injR apart dis (by omega)

end

end OMA.R_Erdos19_erdos_19_R1_H2_R1
