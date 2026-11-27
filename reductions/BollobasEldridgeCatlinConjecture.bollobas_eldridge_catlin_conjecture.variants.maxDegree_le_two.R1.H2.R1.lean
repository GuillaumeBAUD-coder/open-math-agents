import OMAReductions.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1

/-! Counting internal rotation obstructions and external transposition obstructions simultaneously.
The rotation and traversal lemmas are taken from mucoucah's BEC reduction (PR 2769). -/
namespace OMA.LocalPacking
open SimpleGraph Finset BollobasEldridgeCatlinConjecture
variable {V : Type} [Fintype V] [DecidableEq V]

private def red (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (x : V) : Finset V :=
  univ.filter fun b => G.Adj (σ x) (σ b)

omit [DecidableEq V] in
private lemma red_le (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (x : V) :
    (red G σ x).card ≤ G.maxDegree := by
  apply le_trans _ (G.degree_le_maxDegree (σ x))
  rw [← G.card_neighborFinset_eq_degree]
  apply card_le_card_of_injOn σ _ (σ.injective.injOn)
  intro u hu
  exact (G.mem_neighborFinset _ _).2 (mem_filter.mp hu).2

private lemma rotate_count (C G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (σ : Equiv.Perm V) (K : Finset V) (p : ℕ → V) (L : ℕ) (hl : 2 ≤ L)
    (hinj : ∀ j k, j ≤ L → k ≤ L → p j = p k → j = k)
    (hp0 : p 0 = y) (hpL : p L = x)
    (hK : ∀ j, j ≤ L → p j ∈ K)
    (hpadj : ∀ j, j < L → C.Adj (p j) (p (j + 1)))
    (hnb : ∀ j b, 1 ≤ j → j < L → C.Adj (p j) b → b = p (j-1) ∨ b = p (j+1))
    (hnbL : ∀ b, C.Adj x b → b = p (L-1) ∨ b = y)
    (hσ : ∀ a b, C.Adj a b → ¬(a=x ∧ b=y) → ¬(a=y ∧ b=x) → ¬G.Adj (σ a) (σ b))
    (hc : G.Adj (σ x) (σ y)) (hnp : ¬ Packs C G) :
    L ≤ ((red G σ x) ∩ K).card + ((red G σ y) ∩ K).card := by
  classical
  let I := Icc 1 (L-2)
  let A := I.filter fun i => G.Adj (σ x) (σ (p i))
  let B := I.filter fun i => G.Adj (σ y) (σ (p (i+1)))
  have hk0 : y ∈ K := hp0 ▸ hK 0 (Nat.zero_le _)
  have hkL : x ∈ K := hpL ▸ hK L le_rfl
  have hA : A.card ≤ (((red G σ x) ∩ K).erase y).card := by
    apply card_le_card_of_injOn p
    · intro i hi
      obtain ⟨h1,h2⟩ := mem_filter.mp hi
      obtain ⟨h1,h3⟩ := mem_Icc.mp h1
      refine mem_erase.mpr ⟨?_, mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h2⟩,hK _ (by omega)⟩⟩
      intro eq; have := hinj i 0 (by omega) (by omega) (eq.trans hp0.symm); omega
    · intro i hi j hj eq
      have hi' := (mem_Icc.mp (mem_filter.mp hi).1).2
      have hj' := (mem_Icc.mp (mem_filter.mp hj).1).2
      exact hinj _ _ (by omega) (by omega) eq
  have hB : B.card ≤ (((red G σ y) ∩ K).erase x).card := by
    apply card_le_card_of_injOn (fun i => p (i+1))
    · intro i hi
      obtain ⟨h1,h2⟩ := mem_filter.mp hi
      obtain ⟨h1,h3⟩ := mem_Icc.mp h1
      refine mem_erase.mpr ⟨?_, mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h2⟩,hK _ (by omega)⟩⟩
      intro eq; have := hinj (i+1) L (by omega) le_rfl (eq.trans hpL.symm); omega
    · intro i hi j hj eq
      have hi' := (mem_Icc.mp (mem_filter.mp hi).1).2
      have hj' := (mem_Icc.mp (mem_filter.mp hj).1).2
      have := hinj (i+1) (j+1) (by omega) (by omega) eq; omega
  have hsub : I ⊆ A ∪ B := by
    intro i hi
    by_contra H
    have hi' := mem_Icc.mp hi
    have hx : ¬G.Adj (σ x) (σ (p i)) := fun h => H (mem_union_left _ (mem_filter.mpr ⟨hi,h⟩))
    have hy : ¬G.Adj (σ y) (σ (p (i+1))) := fun h => H (mem_union_right _ (mem_filter.mpr ⟨hi,h⟩))
    exact hnp (OMA.rotate C G x y σ p L i hinj hp0 hpL hnb hnbL hpadj hi'.1 (by omega) hσ hx hy)
  have hxy : y ∈ (red G σ x) ∩ K := mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hc⟩,hk0⟩
  have hyx : x ∈ (red G σ y) ∩ K := mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hc.symm⟩,hkL⟩
  have ha := card_erase_add_one hxy
  have hb := card_erase_add_one hyx
  have hcI : I.card = L-2 := by simp [I, Nat.card_Icc]
  have hm := (card_le_card hsub).trans (card_union_le A B)
  omega


private lemma outside_count (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a=b ∨ a=c ∨ b=c)
    (x y : V) (hxy : C.Adj x y) (a : V) (ha : C.Adj x a) (hay : a ≠ y)
    (σ : Equiv.Perm V) (K : Finset V) (hx : x ∈ K) (hy : y ∈ K)
    (hclosed : ∀ u ∈ K, ∀ v, C.Adj u v → v ∈ K)
    (hσ : ∀ a b, C.Adj a b → ¬(a=x ∧ b=y) → ¬(a=y ∧ b=x) → ¬G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) :
    Kᶜ.card ≤ G.maxDegree + (red G σ y \ K).card + 2 * (red G σ x \ K).card := by
  classical
  let U := (red G σ x \ K).biUnion (fun b => C.neighborFinset b)
  have deg2 (z : V) : (C.neighborFinset z).card ≤ 2 := by
    by_contra! nh
    obtain ⟨i,hi,j,hj,k,hk,hij,hik,hjk⟩ := two_lt_card.mp nh
    simp only [mem_neighborFinset] at hi hj hk
    rcases hdeg z i j k hi hj hk with H|H|H <;> contradiction
  have hU : U.card ≤ 2 * (red G σ x \ K).card := by
    calc U.card ≤ ∑ z ∈ red G σ x \ K, (C.neighborFinset z).card := card_biUnion_le
         _ ≤ ∑ _z ∈ red G σ x \ K, 2 := sum_le_sum fun z _ => deg2 z
         _ = _ := by simp [Nat.mul_comm]
  have cover : Kᶜ ⊆ (red G σ a ∪ (red G σ y \ K)) ∪ U := by
    intro w hw
    by_contra h
    have hwK := mem_compl.mp hw
    have hwx : w ≠ x := fun e => hwK (e ▸ hx)
    have hwy : w ≠ y := fun e => hwK (e ▸ hy)
    have hwU : w ∉ U := fun hU => h (mem_union_right _ hU)
    have hT' : ∀ z, C.Adj x z → z ≠ y → ¬ G.Adj (σ w) (σ z) := by
      intro z hzx hzy hz
      have he : z = a := by rcases hdeg x z a y hzx ha hxy with e | e | e <;> tauto
      exact h (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,he ▸ hz.symm⟩)))
    have hU' : ∀ b, C.Adj w b → ¬ G.Adj (σ x) (σ b) := by
      intro b hb hred
      apply hwU
      apply mem_biUnion.mpr
      exact ⟨b,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,hred⟩,
        fun hbk => hwK (hclosed b hbk w hb.symm)⟩,(C.mem_neighborFinset b w).mpr hb.symm⟩
    have hres : ¬ G.Adj (σ w) (σ y) := fun e => h (mem_union_left _ (mem_union_right _
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,e.symm⟩,hwK⟩)))
    have hyx : y ≠ x := fun e => hxy.ne e.symm
    have hyw : y ≠ w := fun e => hwy e.symm
    have key : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
        ¬ G.Adj (σ (Equiv.swap x w a)) (σ (Equiv.swap x w b)) := by
      intro a b hab h1 h2 hadj
      by_cases hax : a = x
      · have hby : b ≠ y := fun e => h1 ⟨hax, e⟩
        rw [hax] at hab hadj
        rw [Equiv.swap_apply_left] at hadj
        by_cases hbw : b = w
        · rw [hbw] at hab hadj
          rw [Equiv.swap_apply_right] at hadj
          exact hσ x w hab (fun e => hwy e.2) (fun e => hyx e.1.symm) hadj.symm
        · have hbx : b ≠ x := fun e => hab.ne e.symm
          rw [Equiv.swap_apply_of_ne_of_ne hbx hbw] at hadj
          exact hT' b hab hby hadj
      · by_cases hbx : b = x
        · have hay : a ≠ y := fun e => h2 ⟨e, hbx⟩
          rw [hbx] at hab hadj
          rw [Equiv.swap_apply_left] at hadj
          by_cases haw : a = w
          · rw [haw] at hab hadj
            rw [Equiv.swap_apply_right] at hadj
            exact hσ x w hab.symm (fun e => hwy e.2) (fun e => hyx e.1.symm) hadj
          · rw [Equiv.swap_apply_of_ne_of_ne hax haw] at hadj
            exact hT' a hab.symm hay hadj.symm
        · by_cases haw : a = w
          · rw [haw] at hab hadj
            have hbw : b ≠ w := fun e => hab.ne e.symm
            rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbx hbw] at hadj
            exact hU' b hab hadj
          · by_cases hbw : b = w
            · rw [hbw] at hab hadj
              rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hax haw] at hadj
              exact hU' a hab.symm hadj.symm
            · rw [Equiv.swap_apply_of_ne_of_ne hax haw,
                Equiv.swap_apply_of_ne_of_ne hbx hbw] at hadj
              exact hσ a b hab h1 h2 hadj
    apply hnp
    refine OMA.packs_of_almost C G x y ((Equiv.swap x w).trans σ) (fun a b hab h1 h2 => key a b hab h1 h2) ?_
    simpa only [Equiv.trans_apply,Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyx hyw] using hres
  have h1 := card_le_card cover
  have h2 := card_union_le (red G σ a ∪ (red G σ y \ K)) U
  have h3 := card_union_le (red G σ a) (red G σ y \ K)
  have h4 := red_le G σ a
  omega

/-- In a nonpacking, the length of the conflicting cycle plus twice the order is at most
`8 * Δ + 3`. This counts the degree budget inside and outside the same cycle. -/
theorem nonpacking_cycle_bound (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a=b ∨ a=c ∨ b=c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z≠y ∧ C.Adj x z)
    (x y : V) (hxy : C.Adj x y) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a=x ∧ b=y) → ¬(a=y ∧ b=x) → ¬G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) :
    Set.ncard {v | C.Reachable y v} + 2 * Fintype.card V ≤ 8 * G.maxDegree + 3 := by
  classical
  have hc : G.Adj (σ x) (σ y) := Classical.byContradiction (fun h => hnp (OMA.packs_of_almost C G x y σ hσ h))
  let K : Finset V := univ.filter (C.Reachable y)
  have hK (u : V) : u ∈ K ↔ C.Reachable y u := by simp [K]
  have hKeq : (K : Set V) = {v | C.Reachable y v} := by ext u; exact hK u
  rw [← hKeq, Set.ncard_coe_finset]
  have hx := (hK x).mpr (hxy.symm.reachable)
  have hy := (hK y).mpr (SimpleGraph.Reachable.refl y)
  have closed : ∀ u ∈ K, ∀ v, C.Adj u v → v ∈ K :=
    fun u hu v huv => (hK v).mpr (((hK u).mp hu).trans huv.reachable)
  obtain ⟨p,L,hL,hi,h0,hL',he,hcov,hn,hnL⟩ := OMA.cycle_path C hdeg hnl x y hxy
  have path_in (j : ℕ) (hj : j ≤ L) : p j ∈ K := by
    induction j with
    | zero => simpa [h0] using hy
    | succ j ih => exact closed _ (ih (by omega)) _ (he _ (by omega))
  have size : K.card ≤ L+1 := by
    calc K.card ≤ ((range (L+1)).image p).card := by
           apply card_le_card
           intro u hu
           obtain ⟨j,hj,hj'⟩ := hcov u ((hK u).mp hu)
           exact mem_image.mpr ⟨j,mem_range.mpr (by omega),hj'⟩
         _ ≤ (range (L+1)).card := card_image_le
         _ = _ := card_range _
  have rot := rotate_count C G x y σ K p L hL hi h0 hL' path_in he hn hnL hσ hc hnp
  obtain ⟨a,hay,ha⟩ := hnl x y hxy
  obtain ⟨b,hbx,hb⟩ := hnl y x hxy.symm
  have bx := outside_count C G hdeg x y hxy a ha hay σ K hx hy closed hσ hnp
  have by' := outside_count C G hdeg y x hxy.symm b hb hbx σ K hy hx closed
    (fun i j hij h1 h2 => hσ i j hij h2 h1) hnp
  have splitX := card_sdiff_add_card_inter (red G σ x) K
  have splitY := card_sdiff_add_card_inter (red G σ y) K
  have tot := card_compl_add_card K
  have dx := red_le G σ x
  have dy := red_le G σ y
  omega

private lemma four_le_component (C : SimpleGraph V)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z≠y ∧ C.Adj x z)
    (x y : V) (hxy : C.Adj x y) (hnt : ∀ u, ¬ (C.Adj x u ∧ C.Adj y u)) :
    4 ≤ Set.ncard {u | C.Reachable y u} := by
  classical
  obtain ⟨a,hay,hxa⟩ := hnl x y hxy
  obtain ⟨b,hbx,hyb⟩ := hnl y x hxy.symm
  have hab : a ≠ b := fun e => hnt b ⟨e ▸ hxa,hyb⟩
  let S : Finset V := {x,y,a,b}
  have c4 : S.card = 4 := by simp [S, hxy.ne, hxa.ne, hyb.ne, Ne.symm hbx, Ne.symm hay,hab]
  have sub : (S : Set V) ⊆ {u | C.Reachable y u} := by
    intro v hv
    simp only [S,mem_coe,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl
    · exact hxy.symm.reachable
    · exact SimpleGraph.Reachable.refl _
    · exact hxy.symm.reachable.trans hxa.reachable
    · exact hyb.reachable
  have ub := Set.ncard_le_ncard sub (Set.toFinite _)
  rwa [Set.ncard_coe_finset,c4] at ub

end OMA.LocalPacking

namespace OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1_H2_R1
open SimpleGraph BollobasEldridgeCatlinConjecture Finset

/-- The short-cycle factor case: all nontrivial components are triangles, quadrilaterals or pentagons. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj],
    3 * (G.maxDegree+1) ≤ Fintype.card V+1 →
    3 ≤ G.maxDegree → Fintype.card V < 4*G.maxDegree →
    (∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a=b ∨ a=c ∨ b=c) →
    (∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z) →
    (∀ v, Set.ncard {u | C.Reachable v u} ≤ 5) → Packs C G

/-- The remaining range, with the derived bound on every component. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (C G₂ : SimpleGraph V) [DecidableRel G₂.Adj],
    3 * (G₂.maxDegree + 1) ≤ Fintype.card V + 1 →
    4 ≤ G₂.maxDegree →
    Fintype.card V + 2 ≤ 4 * G₂.maxDegree →
    (∃ v, 6 ≤ Set.ncard {u | C.Reachable v u}) →
    (∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c) →
    (∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z) →
    (∀ v, Set.ncard {u | C.Reachable v u} + 2 * Fintype.card V ≤ 8 * G₂.maxDegree + 3) →
    (∀ G' : SimpleGraph V,
      (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
      Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
      Packs G' G₂) →
    ∀ x y : V, C.Adj x y →
    (∀ u, ¬ (C.Adj x u ∧ C.Adj y u)) →
    ∀ σ : Equiv.Perm V,
      (∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b)) →
      G₂.Adj (σ x) (σ y) →
      (∀ z, (∀ b, ¬ C.Adj z b) → G₂.Adj (σ z) (σ y) ∨ ∃ b, C.Adj x b ∧ b ≠ y ∧ G₂.Adj (σ z) (σ b)) →
      (∀ z, (∀ b, ¬ C.Adj z b) → G₂.Adj (σ z) (σ x) ∨ ∃ b, C.Adj y b ∧ b ≠ x ∧ G₂.Adj (σ z) (σ b)) →
    ∀ w w' : V, w ≠ x → w ≠ y → w' ≠ x → w' ≠ y →
      G₂.Adj (σ w) (σ y) → G₂.Adj (σ w') (σ x) →
      (∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
        ¬ G₂.Adj (σ (Equiv.swap x w a)) (σ (Equiv.swap x w b))) →
      (∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
        ¬ G₂.Adj (σ (Equiv.swap y w' a)) (σ (Equiv.swap y w' b))) →
      (w ≠ w' → G₂.Adj (σ w) (σ w')) →
      Packs C G₂

theorem main : H1 → H2 → OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1.H2 := by
  classical
  intro short narrow V _ _ C G _ hd hn hdeg hnl _hsmall ih x y hxy hnt σ hσ hc i₁ i₂ w w' w₁ w₂ w₃ w₄ h₁ h₂ h₃ h₄ h₅
  by_contra hnp
  have comp (v : V) : Set.ncard {u | C.Reachable v u} + 2 * Fintype.card V ≤ 8 * G.maxDegree + 3 := by
    by_cases H : ∃ x, C.Adj x v
    · obtain ⟨u,hu⟩ := H
      obtain ⟨τ,hτ⟩ := OMA.almost_packing C G hdeg ih u v hu
      exact OMA.LocalPacking.nonpacking_cycle_bound C G hdeg hnl u v hu τ hτ hnp
    · have hs : {u | C.Reachable v u} ⊆ {v} := by
        intro u hu
        obtain ⟨p⟩ := hu
        cases p with
        | nil => exact Set.mem_singleton _
        | cons e _ => exact absurd ⟨_,e.symm⟩ H
      have ub := Set.ncard_le_ncard hs (Set.finite_singleton v)
      rw [Set.ncard_singleton] at ub
      omega
  have four := OMA.LocalPacking.four_le_component C hnl x y hxy hnt
  have cbxy := comp y
  by_cases hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5
  · exact hnp (short C G hd (by omega) (by omega) hdeg hnl hshort)
  push Not at hshort
  obtain ⟨v,hv⟩ := hshort
  have cb := comp v
  exact hnp (narrow C G hd (by omega) (by omega) ⟨v,by omega⟩ hdeg hnl comp ih x y hxy hnt σ hσ hc i₁ i₂ w w' w₁ w₂ w₃ w₄ h₁ h₂ h₃ h₄ h₅)

end OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1_H2_R1
