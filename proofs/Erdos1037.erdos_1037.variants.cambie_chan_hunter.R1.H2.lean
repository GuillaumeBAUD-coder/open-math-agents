import OMAReductions.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1

/-! # An eight-copy graph with three quarters as many distinct degrees as vertices -/
-- Credit: @steveDOTdigital
-- The four-block arrangement follows Cambie, Chan and Hunter (Erdős Problems, thread 1037).
namespace OMA.EightCopies
open Finset Set
open scoped Classical

private abbrev Slots (m : ℕ) := Bool × Bool × Fin m
private abbrev Vert (m : ℕ) := Bool × Slots m

private noncomputable def rank (m : ℕ) : Slots m ≃ Fin (4*m) :=
  Fintype.equivFinOfCardEq (by simp [Slots]; omega)

-- Between the sides, use a staircase according to the slot ranks. Within
-- a side, join its two blocks exactly when the side is high. Within a block,
-- opposite layers use the complement on distinct original vertices.
private def within {m : ℕ} (G : SimpleGraph (Fin m)) (side : Bool) (a b : Slots m) : Prop :=
  if a.1 = b.1 then
    a.2.2 ≠ b.2.2 ∧ (if a.2.1 = b.2.1 then G.Adj a.2.2 b.2.2 else ¬ G.Adj a.2.2 b.2.2)
  else side = true

private noncomputable def graph {m : ℕ} (G : SimpleGraph (Fin m)) : SimpleGraph (Vert m) where
  Adj x y := if x.1 = y.1 then within G x.1 x.2 y.2
    else (rank m x.2).val + (rank m y.2).val < 4*m
  symm := ⟨by
    rintro ⟨s,a,i,x⟩ ⟨t,b,j,y⟩
    dsimp
    by_cases st : s = t
    · subst t
      simp only [within]
      by_cases ab : a=b <;> by_cases ij : i=j <;>
        simp [ab,ij,eq_comm,SimpleGraph.adj_comm] 
    · simp [st,Ne.symm st,Nat.add_comm]⟩
  loopless := ⟨by rintro ⟨s,b,i,x⟩; simp [within]⟩

private lemma sum_bits (p : Bool → ℕ) : (∑ b : Bool,p b) = p false+p true := by
  simp [add_comm]

private lemma within_count {m : ℕ} (G : SimpleGraph (Fin m)) (side : Bool) (a : Slots m) :
    (∑ b : Slots m, if within G side a b then (1:ℕ) else 0) =
      (m-1) + (if side then 2*m else 0) := by
  classical
  rcases a with ⟨block,layer,i⟩
  have col (j : Fin m) :
      (if within G side (block,layer,i) (block,false,j) then (1:ℕ) else 0) +
      (if within G side (block,layer,i) (block,true,j) then (1:ℕ) else 0) =
      (if i ≠ j then 1 else 0) := by
    cases layer <;> by_cases eq : i = j <;> by_cases adj : G.Adj i j <;> simp [within,eq,adj]
  have self : (∑ j : Fin m, (if i ≠ j then 1 else 0 : ℕ)) = m-1 := by
    rw [Finset.sum_boole]
    have eq : (univ.filter fun j : Fin m => i ≠ j) = univ.erase i := by ext j; simp [eq_comm]
    rw [eq,card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
    simp
  have same :
      (∑ p : Bool × Fin m, if within G side (block,layer,i) (block,p) then (1:ℕ) else 0) = m-1 := by
    rw [Fintype.sum_prod_type,sum_bits,←Finset.sum_add_distrib]
    simpa only [col] using self
  have other (b : Bool) (ne : block ≠ b) :
      (∑ p : Bool × Fin m, if within G side (block,layer,i) (b,p) then (1:ℕ) else 0) =
      (if side then 2*m else 0) := by
    cases side <;> simp [within,ne]
  rw [Fintype.sum_prod_type,sum_bits]
  cases block
  · rw [same,other true (by decide)]
  · rw [same,other false (by decide),add_comm]

private lemma cross_count (m : ℕ) (a : Slots m) :
    (∑ b : Slots m, if (rank m a).val + (rank m b).val < 4*m then (1:ℕ) else 0) =
      4*m-(rank m a).val := by
  classical
  let i := rank m a
  let f (j : Fin (4*m)) : ℕ := if j ≤ i.rev then 1 else 0
  have cmp (j : Fin (4*m)) : i.val+j.val < 4*m ↔ j ≤ i.rev := by
    change _ ↔ j.val ≤ 4*m-(i.val+1)
    have := i.isLt
    omega
  change (∑ b : Slots m, if i.val+(rank m b).val < 4*m then (1:ℕ) else 0) = _
  simp only [cmp]
  change (∑ b : Slots m, f (rank m b)) = _
  rw [(rank m).sum_comp f]
  have filt : univ.filter (fun j : Fin (4*m) => j ≤ i.rev) = Finset.Iic i.rev := by ext; simp
  rw [show (∑ j, f j) = (univ.filter (fun j : Fin (4*m) => j ≤ i.rev)).card by simp [f],filt,Fin.card_Iic]
  change 4*m-(i.val+1)+1 = 4*m-i.val
  have := i.isLt
  omega

private noncomputable def degree {V : Type*} (G : SimpleGraph V) (v : V) := (G.neighborSet v).ncard
private def val {m : ℕ} (v : Vert m) (i : ℕ) :=
  (m-1) + (if v.1 then 2*m else 0) + (4*m-i)

private lemma count_ones {V : Type*} [Fintype V] (s : Set V) :
    s.ncard = ∑ v : V, if v ∈ s then (1 : ℕ) else 0 := by
  classical
  rw [Finset.sum_boole,Set.ncard_eq_toFinset_card']
  congr 1
  ext v
  simp

private lemma degrees {m : ℕ} (G : SimpleGraph (Fin m)) (v : Vert m) :
    degree (graph G) v = val v (rank m v.2).val := by
  rcases v with ⟨side,a⟩
  rw [degree,count_ones,Fintype.sum_prod_type,sum_bits]
  have inside := within_count G side a
  have cross := cross_count m a
  simp only [Finset.sum_boole] at inside cross
  cases side <;> simp [SimpleGraph.mem_neighborSet,graph,val] at inside cross ⊢ <;> omega

private lemma unique_on_side {m : ℕ} (G : SimpleGraph (Fin m)) (side : Bool) (a b : Slots m)
    (h : degree (graph G) (side,a) = degree (graph G) (side,b)) : a = b := by
  rw [degrees,degrees] at h
  dsimp [val] at h
  apply (rank m).injective
  apply Fin.ext
  have := (rank m a).isLt
  have := (rank m b).isLt
  omega

private lemma at_most_two {m : ℕ} (G : SimpleGraph (Fin m)) (d : ℕ) :
    {v | degree (graph G) v = d}.ncard ≤ 2 := by
  have inj : Set.InjOn Prod.fst {v : Vert m | degree (graph G) v = d} := by
    rintro ⟨side,a⟩ ha ⟨side',b⟩ hb e
    change side = side' at e
    subst side'
    exact Prod.ext rfl (unique_on_side G side a b (ha.trans hb.symm))
  have h := Set.ncard_le_ncard (Set.subset_univ (Prod.fst '' {v : Vert m | degree (graph G) v = d}))
  rw [inj.ncard_image,Set.ncard_univ] at h
  simpa using h

private lemma many_degrees {m : ℕ} (hm : 2 ≤ m) (G : SimpleGraph (Fin m)) :
    6*m ≤ (Set.range (degree (graph G))).ncard := by
  have cover : (↑(Finset.Icc m (7*m-1)) : Set ℕ) ⊆ Set.range (degree (graph G)) := by
    intro d hd
    obtain ⟨lb,ub⟩ := Finset.mem_Icc.mp hd
    by_cases low : d ≤ 5*m-1
    · let i : Fin (4*m) := ⟨5*m-1-d,by omega⟩
      refine ⟨(false,(rank m).symm i),?_⟩
      rw [degrees]
      simp only [val,Equiv.apply_symm_apply,Bool.false_eq_true,if_false,add_zero]
      change m-1+(4*m-(5*m-1-d)) = d
      omega
    · let i : Fin (4*m) := ⟨7*m-1-d,by omega⟩
      refine ⟨(true,(rank m).symm i),?_⟩
      rw [degrees]
      simp only [val,Equiv.apply_symm_apply,if_true]
      change m-1+2*m+(4*m-(7*m-1-d)) = d
      omega
  have h := Set.ncard_le_ncard cover
  rw [Set.ncard_coe_finset,Nat.card_Icc] at h
  omega

-- Each fixed side, block and layer induces the original graph.
private lemma homogeneous_slice {m : ℕ} (G : SimpleGraph (Fin m)) (s : Set (Vert m))
    (hs : (graph G).IsHomogeneous s) (side block layer : Bool) :
    G.IsHomogeneous {i | (side,block,layer,i) ∈ s} := by
  have adj (i j : Fin m) (ne : i ≠ j) :
      (graph G).Adj (side,block,layer,i) (side,block,layer,j) ↔ G.Adj i j := by
    simp [graph,within,ne]
  rcases hs with h | h
  · left
    intro i hi j hj ne
    exact (adj i j ne).mp (h hi hj (by intro e; exact ne (congrArg (fun z : Vert m => z.2.2.2) e)))
  · right
    intro i hi j hj ne a
    exact h hi hj (by intro e; exact ne (congrArg (fun z : Vert m => z.2.2.2) e)) ((adj i j ne).mpr a)

private lemma small {m : ℕ} (G : SimpleGraph (Fin m)) (t : ℝ)
    (bound : ∀ s : Set (Fin m), G.IsHomogeneous s → (s.ncard : ℝ) ≤ t)
    (s : Set (Vert m)) (hs : (graph G).IsHomogeneous s) : (s.ncard : ℝ) ≤ 8*t := by
  let A (x y z : Bool) := {i : Fin m | (x,y,z,i) ∈ s}
  have slices (x y z : Bool) : ((A x y z).ncard : ℝ) ≤ t := bound _ (homogeneous_slice G s hs x y z)
  have total : s.ncard = ∑ x : Bool, ∑ y : Bool, ∑ z : Bool, (A x y z).ncard := by
    rw [count_ones]
    simp only [Fintype.sum_prod_type, count_ones, A, Set.mem_ofPred_eq]
  simp only [sum_bits] at total
  rw [total]
  push_cast
  linarith [slices false false false,slices false false true,slices false true false,
    slices false true true,slices true false false,slices true false true,
    slices true true false,slices true true true]

private noncomputable def renumber (m : ℕ) : Vert m ≃ Fin (8*m) :=
  Fintype.equivFinOfCardEq (by simp [Vert,Slots]; omega)

private lemma transfer_degree {m : ℕ} (F : SimpleGraph (Vert m)) (v : Vert m) :
    degree (F.map (renumber m).toEmbedding) (renumber m v) = degree F v := by
  change ((F.map (renumber m).toEmbedding).neighborSet ((renumber m).toEmbedding v)).ncard = _
  rw [F.neighborSet_map,Set.ncard_image_of_injective _ (renumber m).toEmbedding.injective]
  rfl

private lemma transfer_hom {m : ℕ} (F : SimpleGraph (Vert m)) (s : Set (Fin (8*m)))
    (h : (F.map (renumber m).toEmbedding).IsHomogeneous s) : F.IsHomogeneous (renumber m ⁻¹' s) := by
  let e := (renumber m).toEmbedding
  rcases h with h | h
  · left
    intro x hx y hy ne
    exact (SimpleGraph.map_adj_apply (f := e)).mp (h hx hy (e.injective.ne ne))
  · right
    intro x hx y hy ne adj
    exact h hx hy (e.injective.ne ne) ((SimpleGraph.map_adj_apply (f := e)).mpr adj)


theorem eight_copies (m : ℕ) (hm : 2 ≤ m) (G : SimpleGraph (Fin m)) (t : ℝ)
    (bound : ∀ s : Set (Fin m), G.IsHomogeneous s → (s.ncard : ℝ) ≤ t) :
    ∃ J : SimpleGraph (Fin (8*m)),
      (∀ d : ℕ, {v | degree J v = d}.ncard ≤ 2) ∧
      (3/4 * ((8*m : ℕ) : ℝ) ≤ ((Set.range (degree J)).ncard : ℝ)) ∧
      (∀ s : Set (Fin (8*m)), J.IsHomogeneous s → (s.ncard : ℝ) ≤ 8*t) ∧
      ∀ v, 0 < degree J v := by
  let F := graph G
  let e := renumber m
  let J := F.map e.toEmbedding
  have eq (x : Vert m) : degree J (e x) = degree F x := transfer_degree F x
  refine ⟨J,?_,?_,?_,?_⟩
  · intro d
    have fibers : {v | degree J v = d} = e '' {x | degree F x = d} := by
      ext v
      obtain ⟨x,rfl⟩ := e.surjective v
      simp [eq]
    rw [fibers,Set.ncard_image_of_injective _ e.injective]
    exact at_most_two G d
  · have ran : Set.range (degree J) = Set.range (degree F) := by
      ext d
      constructor
      · rintro ⟨v,rfl⟩
        obtain ⟨x,rfl⟩ := e.surjective v
        exact ⟨x,(eq x).symm⟩
      · rintro ⟨x,rfl⟩
        exact ⟨e x,eq x⟩
    rw [ran]
    have h : 6*(m : ℝ) ≤ ((Set.range (degree F)).ncard : ℝ) := by exact_mod_cast many_degrees hm G
    push_cast
    linarith
  · intro s hs
    have ho := transfer_hom F s hs
    have result := small G t bound (e ⁻¹' s) ho
    rwa [Set.ncard_preimage_of_injective_subset_range e.injective (by simp)] at result
  · intro v
    obtain ⟨x,rfl⟩ := e.surjective v
    rw [eq]
    change 0 < degree (graph G) x
    rw [degrees,val]
    omega

end OMA.EightCopies

theorem OMA.solution : OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1.H2 := OMA.EightCopies.eight_copies
