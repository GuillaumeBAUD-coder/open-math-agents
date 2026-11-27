import OMAReductions.R_Erdos559_erdos_559_variants_draganic_petrova_R1
open SimpleGraph Finset
namespace Emb559

private theorem greedy {n : ℕ} (B : Fin n → Finset (Fin n))
    (hs : ∀ x y, x ∈ B y → y ∈ B x) (hl : ∀ x, x ∉ B x) (hb : ∀ x, (B x).card ≤ 9) :
    ∃ k : Fin n → Fin 10, ∀ x y, y ∈ B x → k x ≠ k y := by
  classical
  suffices h : ∀ s : Finset (Fin n), ∃ k : Fin n → Fin 10,
      ∀ x ∈ s, ∀ y ∈ s, y ∈ B x → k x ≠ k y by simpa using h univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨k,hk⟩ := ih
    have less : ((B a).image k).card < (univ : Finset (Fin 10)).card := by
      simpa using (lt_of_le_of_lt (card_image_le.trans (hb a)) (by decide : 9 < 10))
    obtain ⟨b,_,hb⟩ := exists_mem_notMem_of_card_lt_card less
    refine ⟨Function.update k a b, ?_⟩
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx
    · have hya : y ≠ x := fun e => hl x (e ▸ hxy)
      simpa [Function.update, hya] using (show b ≠ k y from fun e => hb (e ▸ mem_image_of_mem k hxy))
    rcases mem_insert.mp hy with rfl | hy
    · have hxa : x ≠ y := fun e => hl y (e ▸ hxy)
      simpa [Function.update, hxa] using (show k x ≠ b from fun e => hb (e ▸ mem_image_of_mem k (hs _ _ hxy)))
    · simpa [Function.update, ne_of_mem_of_not_mem hx ha, ne_of_mem_of_not_mem hy ha] using hk x hx y hy hxy

private theorem squareColors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hm : G.maxDegree ≤ 3) :
    ∃ k : Fin n → Fin 10, (∀ x y, G.Adj x y → k x ≠ k y) ∧
      (∀ x y z, x ≠ z → G.Adj x y → G.Adj y z → k x ≠ k z) := by
  classical
  let B (x : Fin n) := G.neighborFinset x ∪ (G.neighborFinset x).biUnion
    (fun y => (G.neighborFinset y).erase x)
  have memB x z : z ∈ B x ↔ G.Adj x z ∨ (z ≠ x ∧ ∃ y, G.Adj x y ∧ G.Adj y z) := by
    simp only [B,mem_union,mem_biUnion,mem_erase,mem_neighborFinset]
    tauto
  have bound x : (B x).card ≤ 9 := by
    have degree (a : Fin n) := (G.degree_le_maxDegree a).trans hm
    have h := card_biUnion_le_card_mul (G.neighborFinset x) (fun y => (G.neighborFinset y).erase x) 2 (by
      intro y hy
      rw [card_erase_of_mem ((G.mem_neighborFinset y x).mpr ((G.mem_neighborFinset x y).mp hy).symm),G.card_neighborFinset_eq_degree]
      have := degree y
      omega)
    have hh := card_union_le (G.neighborFinset x) ((G.neighborFinset x).biUnion (fun y => (G.neighborFinset y).erase x))
    change _ ≤ _ at h
    rw [G.card_neighborFinset_eq_degree] at h hh
    dsimp [B]
    have := degree x
    omega
  obtain ⟨k,hk⟩ := greedy B (by
    intro x y h
    rcases (memB _ _).mp h with h | ⟨ne,w,hw1,hw2⟩
    · exact (memB _ _).mpr (Or.inl h.symm)
    · exact (memB _ _).mpr (Or.inr ⟨ne.symm,w,hw2.symm,hw1.symm⟩)) (by simp [memB]) bound
  exact ⟨k,fun x y h => hk _ _ ((memB _ _).mpr (Or.inl h)),
    fun x y z ne h1 h2 => hk _ _ ((memB _ _).mpr (Or.inr ⟨ne.symm,y,h1,h2⟩))⟩

private theorem extendStart {n N : ℕ} (A : Finset (Fin n)) (D : Finset (Fin N))
    (e : A ↪ D) (hD : 2*n ≤ D.card) :
    ∃ f : Fin n ↪ Fin N, (∀ x, f x ∈ D) ∧ ∀ x : A, f x = (e x).val := by
  classical
  let T := (univ : Finset A).image fun x => (e x).val
  have hT : T.card ≤ n := by
    have h : T.card ≤ (univ : Finset A).card := card_image_le
    exact (by simpa [T] using h : T.card ≤ A.card) |>.trans (by simpa using A.card_le_univ)
  have room : Fintype.card (Fin n) ≤ Fintype.card ↥(D \ T) := by
    simp only [Fintype.card_fin,Fintype.card_coe]
    have := card_le_card_sdiff_add_card (s := D) (t := T)
    omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le room
  let f (x : Fin n) : Fin N := if hx : x ∈ A then (e ⟨x,hx⟩).val else (g x).val
  have outside x : (g x).val ∉ T := (mem_sdiff.mp (g x).property).2
  have inside (x : A) : (e x).val ∈ T := mem_image_of_mem _ (mem_univ x)
  have inj : Function.Injective f := by
    intro x y eq
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [f,hx,hy] at eq
    · exact eq
    · exact False.elim (outside y (eq ▸ inside ⟨x,hx⟩))
    · exact False.elim (outside x (eq.symm ▸ inside ⟨y,hy⟩))
    · exact eq
  refine ⟨⟨f,inj⟩,?_,?_⟩
  · intro x
    change f x ∈ D
    by_cases hx : x ∈ A
    · simpa [f,hx] using (e ⟨x,hx⟩).property
    · simpa [f,hx] using (mem_sdiff.mp (g x).property).1
  · intro x
    change f x.val = _
    simp [f,x.property]

private theorem parameters {N n nt : ℕ} (F : SimpleGraph (Fin N)) [DecidableRel F.Adj]
    (V : Finset (Fin N)) (u : Fin N) {c p d K : ℝ} (hn : (n:ℝ) ≤ c*N)
    (hn1 : 1 ≤ n) (hc : 0 < c) (hp : 0 < p) (hK : 0 < K)
    (hdens : 16*c*N*p < nt*d) (hscale : 3*K/p ≤ nt*d/4)
    (hnb : nt*d/2 ≤ (V.filter (F.Adj u)).card)
    (uniform : ∀ U X : Finset (Fin N), K/p ≤ U.card → (X.card:ℝ) ≤ c*N →
      (((U ×ˢ X).filter fun e => F.Adj e.1 e.2).card : ℝ) ≤ 4*U.card*X.card*p) :
    (n:ℝ) < nt*d/4 := by
  classical
  let W := V.filter (F.Adj u)
  have scale : K/p ≤ W.card := by rw [mul_div_assoc] at hscale; linarith [div_pos hK hp]
  have pos : 0 < (W.card:ℝ) := lt_of_lt_of_le (div_pos hK hp) scale
  have big : (1:ℝ) ≤ c*N := le_trans (by exact_mod_cast hn1) hn
  have b := uniform W {u} scale (by simpa using big)
  have allEdges : ((W ×ˢ {u}).filter (fun e => F.Adj e.1 e.2)) = W ×ˢ {u} := by
    apply filter_true_of_mem
    rintro ⟨v,y⟩ h
    obtain ⟨hv,hy⟩ := mem_product.mp h
    obtain rfl : y = u := mem_singleton.mp hy
    exact (mem_filter.mp hv).2.symm
  rw [allEdges] at b
  simp at b
  have quarter : 1 ≤ 4*p := by by_contra! z; nlinarith [mul_pos pos (sub_pos.mpr z)]
  nlinarith [mul_nonneg (sub_nonneg.mpr quarter) (show 0 ≤ c*(N:ℝ) by positivity)]


end Emb559
open Emb559

set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R1.H3 := by
  classical
  intro N n ℓ c p d K nt F V D G V₀ parts emb hℓ hn hnN hdeg hc hp hd hK dens scale hunit
    sizeD sizeV disjV nb uniform cycle cover baseDisj apart core rings prior
  obtain ⟨color,c₁,c₂⟩ := squareColors G hdeg
  have sizeDn : 2*n ≤ D.card := by exact_mod_cast (show (2:ℝ)*n ≤ D.card by linarith)
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < D.card by omega)
  have room := parameters F (V 0 0) u hnN hn hc hp hK dens scale (nb u 0 0 (Or.inl hu)) uniform
  let A (i : ℕ) := univ.filter fun x => x ∈ V₀ ∨ ∃ j : ℕ, ∃ hj : j < parts.length, j < i ∧ x ∈ parts[j]
  have memA i x : x ∈ A i ↔ x ∈ V₀ ∨ ∃ j : ℕ, ∃ hj : j < parts.length, j < i ∧ x ∈ parts[j] := by simp [A]
  let P (i : ℕ) := ∃ f : Fin n ↪ Fin N,
    (∀ x, f x ∈ D ∨ (x ∈ A i ∧ f x ∈ V (color x) 0)) ∧
    (∀ x ∈ A i, ∀ y ∈ A i, G.Adj x y → F.Adj (f x) (f y))
  have start : P 0 := by
    obtain ⟨f,hD,he⟩ := extendStart V₀ D emb sizeDn
    refine ⟨f,fun x => Or.inl (hD x),?_⟩
    intro x hx y hy edge
    have hx' : x ∈ V₀ := by simpa [A] using hx
    have hy' : y ∈ V₀ := by simpa [A] using hy
    rw [he ⟨x,hx'⟩,he ⟨y,hy'⟩]
    exact core ⟨x,hx'⟩ ⟨y,hy'⟩ edge
  have step (i : ℕ) (hi : i < parts.length) (before : P i) : P (i+1) := by
    obtain ⟨f,loc,ok⟩ := before
    let C := parts[i]
    have hC : C ∈ parts := List.getElem_mem hi
    have clear x (hx : x ∈ C) : x ∉ A i := by
      intro h
      rcases (memA i x).mp h with h | ⟨j,hj,lt,h⟩
      · exact disjoint_left.mp (baseDisj C hC) h hx
      · exact disjoint_left.mp ((List.pairwise_iff_getElem.mp apart) j i hj hi lt) h hx
    have extendA x : x ∈ A (i+1) ↔ x ∈ A i ∨ x ∈ C := by
      rw [memA,memA]
      constructor
      · rintro (h | ⟨j,hj,lt,h⟩)
        · exact Or.inl (Or.inl h)
        · by_cases e : j = i
          · subst j; exact Or.inr h
          · exact Or.inl (Or.inr ⟨j,hj,by omega,h⟩)
      · rintro ((h | ⟨j,hj,lt,h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨j,hj,by omega,h⟩
        · exact Or.inr ⟨i,hi,by omega,h⟩
    obtain ⟨long,idx,ringEdges⟩ := rings C hC
    haveI : NeZero C.card := ⟨by omega⟩
    let v (r : Fin C.card) : Fin n := (idx.symm r).val
    have vin r : v r ∈ C := (idx.symm r).property
    have vi : Function.Injective v := fun _ _ h => idx.symm.injective (Subtype.ext h)
    have follows (r : Fin C.card) : G.Adj (v r) (v (r+1)) := by
      apply (ringEdges (idx.symm r) (idx.symm (r+1))).mpr
      left
      simp only [Equiv.apply_symm_apply,Fin.val_add]
      rw [show (1 : Fin C.card).val = 1 by change 1 % C.card = 1; exact Nat.mod_eq_of_lt (by omega)]
    let earlier (r : Fin C.card) (x : Fin n) := x ∈ A i ∧ G.Adj (v r) x
    have unique r x y (hx : earlier r x) (hy : earlier r y) : x = y := by
      apply card_le_one.mp (prior i hi (v r) (vin r))
      all_goals
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
      · refine ⟨hx.2,?_⟩
        rcases (memA _ _).mp hx.1 with h | ⟨j,hj,lt,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j,lt,h⟩
      · refine ⟨hy.2,?_⟩
        rcases (memA _ _).mp hy.1 with h | ⟨j,hj,lt,h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j,lt,h⟩
    let a (r : Fin C.card) := if h : ∃ x, earlier r x then h.choose else v r
    have anchor r : earlier r (a r) ∨ a r = v r := by
      dsimp [a]; split
      · exact Or.inl (Exists.choose_spec ‹_›)
      · exact Or.inr rfl
    have anchor_eq r x (hx : earlier r x) : a r = x := by
      have hex : ∃ y, earlier r y := ⟨x,hx⟩
      exact (by simpa [a,hex] using unique r _ x hex.choose_spec hx)
    have multiplicity (z : Fin N) : (univ.filter (fun r => f (a r) = z)).card ≤ 3 := by
      by_cases hz : ∃ x, f x = z
      · obtain ⟨x,rfl⟩ := hz
        by_cases hx : x ∈ A i
        · apply le_trans (card_le_card_of_injOn v (t := G.neighborFinset x) ?_ vi.injOn) ((G.degree_le_maxDegree x).trans hdeg)
          intro r hr
          have e := f.injective (mem_filter.mp hr).2
          rcases anchor r with h | h
          · exact (G.mem_neighborFinset _ _).mpr (e ▸ h.2.symm)
          · exact False.elim (clear _ (vin r) ((h.symm.trans e).symm ▸ hx))
        · suffices (univ.filter (fun r => f (a r) = f x)).card ≤ 1 by omega
          apply card_le_one.mpr
          have eqv r (hr : f (a r) = f x) : v r = x := by
            have e := f.injective hr
            rcases anchor r with h | h
            · exact False.elim (hx (e ▸ h.1))
            · exact h.symm.trans e
          intro r hr s hs
          exact vi ((eqv _ (mem_filter.mp hr).2).trans (eqv _ (mem_filter.mp hs).2).symm)
      · have emp : (univ.filter (fun r => f (a r) = z)) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          exact fun r hr => hz ⟨_,(mem_filter.mp hr).2⟩
        simp [emp]
    let col (r : Fin C.card) := color (v r)
    have eligible r : f (a r) ∈ D ∨ ∃ a' b', a' ≠ col r ∧ a' ≠ col (r+1) ∧
        a' ≠ col (r-1) ∧ f (a r) ∈ V a' b' := by
      rcases loc (a r) with h | ⟨inA,hpart⟩
      · exact Or.inl h
      right
      have ne (s : Fin C.card) : a r ≠ v s := fun eq => clear _ (vin s) (eq ▸ inA)
      have ear : earlier r (a r) := (anchor r).resolve_right (ne r)
      refine ⟨_,0,c₁ _ _ ear.2.symm,c₂ _ _ _ (ne _) ear.2.symm (follows r),?_,hpart⟩
      apply c₂ _ _ _ (ne _) ear.2.symm
      simpa using (follows (r-1)).symm
    let used := univ.image f
    let W r := (V (col r) 0).filter (F.Adj (f (a r)))
    let S r := W r \ used
    have sizeS r : nt*d/20 ≤ (S r).card := by
      have okU : f (a r) ∈ D ∨ ∃ a' b', a' ≠ col r ∧ f (a r) ∈ V a' b' := by
        rcases eligible r with h | ⟨a',b',h,_,_,hV⟩
        · exact Or.inl h
        · exact Or.inr ⟨a',b',h,hV⟩
      have lower : nt*d/2 ≤ (W r).card := nb _ _ _ okU
      have cnt : (W r).card ≤ (S r).card + used.card := card_le_card_sdiff_add_card
      have hused : used.card ≤ n := by simpa [used] using (card_image_le (s := univ) (f := f))
      have rcnt : ((W r).card:ℝ) ≤ (S r).card + (used.card:ℝ) := by exact_mod_cast cnt
      have ru : (used.card:ℝ) ≤ n := by exact_mod_cast hused
      linarith
    have csize : (C.card:ℝ) ≤ c*N := le_trans (by exact_mod_cast (show C.card ≤ n by simpa using C.card_le_univ)) hnN
    obtain ⟨b,memB,edges⟩ := cycle C.card long csize col (fun _ => 0) (fun r => f (a r)) S
      (fun r => c₁ _ _ (follows r)) multiplicity eligible (fun r => ⟨sdiff_subset,sizeS r⟩)
    have fresh r x : b r ≠ f x := fun eq => (mem_sdiff.mp (memB r)).2 (eq ▸ mem_image_of_mem f (mem_univ x))
    have link r : F.Adj (f (a r)) (b r) := (mem_filter.mp (mem_sdiff.mp (memB r)).1).2
    let g (x : Fin n) := if hx : x ∈ C then b (idx ⟨x,hx⟩) else f x
    have stay x (hx : x ∈ A i) : g x = f x := by
      have out : x ∉ C := fun h => clear x h hx
      simp [g,out]
    have onCycle (x : C) : g x.val = b (idx x) := by simp [g,x.property]
    have ginj : Function.Injective g := by
      intro x y eq
      by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> simp only [g,hx,hy,dif_pos,dif_neg] at eq
      · exact congrArg Subtype.val (idx.injective (b.injective eq))
      · exact False.elim (fresh _ _ eq)
      · exact False.elim (fresh _ _ eq.symm)
      · exact f.injective eq
    have across (x : C) (y : Fin n) (hy : y ∈ A i) (edge : G.Adj x.val y) : F.Adj (g x.val) (g y) := by
      have vx : v (idx x) = x.val := by simp [v]
      have ey : earlier (idx x) y := ⟨hy,vx.symm ▸ edge⟩
      rw [onCycle,stay _ hy]
      simpa only [anchor_eq _ _ ey] using (link (idx x)).symm
    have oneval : (1 : Fin C.card).val = 1 := by change 1 % C.card = 1; exact Nat.mod_eq_of_lt (by omega)
    have next (r s : Fin C.card) (h : (r.val+1)%C.card = s.val) : r+1 = s := by
      apply Fin.ext
      simpa only [Fin.val_add,oneval] using h
    refine ⟨⟨g,ginj⟩,?_,?_⟩
    · intro x
      change g x ∈ D ∨ _
      by_cases hx : x ∈ C
      · let z : C := ⟨x,hx⟩
        refine Or.inr ⟨(extendA x).mpr (Or.inr hx),?_⟩
        change g z.val ∈ V (color z.val) 0
        rw [onCycle]
        simpa [col,v] using (mem_filter.mp (mem_sdiff.mp (memB (idx z))).1).1
      · have eq : g x = f x := by simp [g,hx]
        rcases loc x with h | ⟨h,hv⟩
        · exact Or.inl (eq.symm ▸ h)
        · exact Or.inr ⟨(extendA x).mpr (Or.inl h),show g x ∈ V (color x) 0 by rwa [eq]⟩
    · intro x hx y hy edge
      change F.Adj (g x) (g y)
      rcases (extendA x).mp hx with hx | hx <;> rcases (extendA y).mp hy with hy | hy
      · rw [stay _ hx,stay _ hy]
        exact ok _ hx _ hy edge
      · exact (across ⟨y,hy⟩ x hx edge.symm).symm
      · exact across ⟨x,hx⟩ y hy edge
      · let X : C := ⟨x,hx⟩
        let Y : C := ⟨y,hy⟩
        change F.Adj (g X.val) (g Y.val)
        rw [onCycle,onCycle]
        rcases (ringEdges X Y).mp edge with h | h
        · rw [← next _ _ h]; exact edges _
        · rw [← next _ _ h]; exact (edges _).symm
  have allP : ∀ i, i ≤ parts.length → P i := by
    intro i
    induction i with
    | zero => exact fun _ => start
    | succ i ih => exact fun h => step i (by omega) (ih (by omega))
  obtain ⟨f,_,maps⟩ := allP _ le_rfl
  have mem x : x ∈ A parts.length := by
    apply (memA _ _).mpr
    rcases cover x with h | ⟨C,hC,h⟩
    · exact Or.inl h
    · obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hC
      exact Or.inr ⟨j,hj,hj,he.symm ▸ h⟩
  exact isContained_iff_exists_le_comap.mpr ⟨f,fun {x y} e => maps _ (mem _) _ (mem _) e⟩

