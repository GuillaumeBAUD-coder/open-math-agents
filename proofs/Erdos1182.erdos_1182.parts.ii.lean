import FormalConjectures.ErdosProblems.«1182»

-- Problem: Erdős Problem 1182, part ii: F(n) = Θ(n)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1182.lean:130 (declaration Erdos1182.erdos_1182.parts.ii)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
--
-- As the upstream docstring says, this follows from F(n) ≥ n - 1 and a linear upper bound.
-- Both ingredients are reused unchanged from proofs already merged in this repository:
--   section OMA1182Lower: proofs/Erdos1182.erdos_1182.variants.F_ge_pred.lean (Ian Qvist)
--   namespace OMA.FiveCycleBound: proofs/Erdos1182.erdos_1182.variants.brandt.lean (@steveDOTdigital)
-- Only the final combination (OMA.solution) is new.

section OMA1182Lower

/-! The tree case of the triangle Ramsey bound, using a leaf extension and a bipartite coloring. -/

open SimpleGraph

lemma OMA.tree_copy_of_degree {V : Type} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Type) [Fintype U] (T : SimpleGraph U)
    (hT : T.IsTree) (hd : ∀ v, Fintype.card U - 1 ≤ H.degree v) : T ⊑ H := by
  classical
  have hall (k : ℕ) : ∀ (A : Type) [Fintype A] (G : SimpleGraph A),
      Fintype.card A = k → G.IsTree → (∀ v, k - 1 ≤ H.degree v) → G ⊑ H := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro A _ G hcard hG hdeg
      by_cases hk : k ≤ 1
      · let : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (hcard.trans_le hk)
        obtain ⟨w⟩ := ‹Nonempty V›
        refine ⟨⟨⟨fun _ => w, ?_⟩, ?_⟩⟩
        · intro a b hab
          exact (hab.ne (Subsingleton.elim a b)).elim
        · intro a b _
          exact Subsingleton.elim a b
      have hk' : 1 < k := by omega
      let : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hk')
      obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      let S : Set A := {v}ᶜ
      have hS : (G.induce S).IsTree :=
        ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv, hG.isAcyclic.induce S⟩
      have hS_card : Fintype.card S = k - 1 := by
        change Fintype.card (({v} : Set A)ᶜ : Set A) = k - 1
        rw [Fintype.card_compl_set, hcard]
        simp
      obtain ⟨f⟩ := ih (Fintype.card S) (by omega) S (G.induce S) rfl hS
        (fun w => (Nat.sub_le _ _).trans (hS_card.symm ▸ hdeg w))
      let u' : S := ⟨u, hu.ne.symm⟩
      let used : Finset V := Finset.univ.image (fun a : S => f a)
      have hused : used.card = Fintype.card S := by
        calc
          used.card = (Finset.univ : Finset S).card :=
            Finset.card_image_of_injective _ f.injective
          _ = _ := Finset.card_univ
      have hcenter : f u' ∈ used := Finset.mem_image.mpr ⟨u', Finset.mem_univ _, rfl⟩
      let N := H.neighborFinset (f u')
      have hN : N.card = H.degree (f u') := H.card_neighborFinset_eq_degree _
      have hNself : f u' ∉ N := H.notMem_neighborFinset_self _
      have hlarge : used.card < (insert (f u') N).card := by
        rw [Finset.card_insert_of_notMem hNself, hused, hS_card, hN]
        exact Nat.lt_succ_of_le (hdeg _)
      obtain ⟨w, hw, hnew⟩ := Finset.exists_mem_notMem_of_card_lt_card hlarge
      have hwN : w ∈ N := (Finset.mem_insert.mp hw).resolve_left
        (fun h => hnew (h.symm ▸ hcenter))
      have hwadj : H.Adj (f u') w := (H.mem_neighborFinset _ _).mp hwN
      let g (a : A) : V := if ha : a = v then w else f ⟨a, ha⟩
      have gv : g v = w := by simp [g]
      have gn (a : A) (ha : a ≠ v) : g a = f ⟨a, ha⟩ := by simp [g, ha]
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro a b hab
        by_cases ha : a = v
        · subst a
          have hbu : b = u := huniq b hab
          rw [hbu, gv, gn u hu.ne.symm]
          exact hwadj.symm
        · by_cases hb : b = v
          · subst b
            have hau : a = u := huniq a hab.symm
            rw [hau, gn u hu.ne.symm, gv]
            exact hwadj
          · rw [gn a ha, gn b hb]
            exact f.toHom.map_adj (show (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      · intro a b heq
        change g a = g b at heq
        by_cases ha : a = v
        · by_cases hb : b = v
          · exact ha.trans hb.symm
          · subst a
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _,
              by simpa only [gv, gn b hb] using heq.symm⟩
        · by_cases hb : b = v
          · subst b
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _,
              by simpa only [gv, gn a ha] using heq⟩
          · rw [gn a ha, gn b hb] at heq
            exact congrArg Subtype.val (f.injective heq)
  exact hall (Fintype.card U) U T rfl hT hd

lemma OMA.tree_ramsey_upper (n : ℕ) (hn : 2 ≤ n) {T : SimpleGraph (Fin n)}
    (hT : T.IsTree) (C : SimpleGraph (Fin (2 * n - 1))) :
    (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ := by
  classical
  by_cases htri : (⊤ : SimpleGraph (Fin 3)) ⊑ C
  · exact Or.inl htri
  right
  have hcf : C.CliqueFree 3 := by
    by_contra hc
    exact htri (by simpa only [completeGraph_eq_top] using
      (not_cliqueFree_iff_top_isContained 3).mp hc)
  by_cases hdegree : ∀ v, n - 1 ≤ Cᶜ.degree v
  · have : Nonempty (Fin (2 * n - 1)) := ⟨⟨0, by omega⟩⟩
    exact OMA.tree_copy_of_degree Cᶜ (Fin n) T hT (by simpa using hdegree)
  push Not at hdegree
  obtain ⟨v, hv⟩ := hdegree
  let S := C.neighborFinset v
  have hcard : n ≤ Fintype.card S := by
    have h := C.degree_compl v
    rw [Fintype.card_fin] at h
    rw [Fintype.card_coe, C.card_neighborFinset_eq_degree]
    omega
  have hclique : Cᶜ.IsClique (S : Set (Fin (2 * n - 1))) := by
    rw [isClique_compl]
    simpa only [S, coe_neighborFinset] using isIndepSet_neighborSet_of_triangleFree C hcf v
  let f : Fin n ↪ S := (Fin.castLEEmb hcard).trans (Fintype.equivFin S).symm.toEmbedding
  refine ⟨⟨⟨fun a => (f a).val, ?_⟩, ?_⟩⟩
  · intro a b hab
    exact hclique (f a).property (f b).property
      (fun he => hab.ne (f.injective (Subtype.ext he)))
  · intro a b he
    exact f.injective (Subtype.ext he)

lemma OMA.tree_ramsey_lower_witness (n N : ℕ) (hn : 2 ≤ n) (hN : N < 2 * n - 1)
    (T : SimpleGraph (Fin n)) (hT : T.Connected) :
    ∃ C : SimpleGraph (Fin N), ¬ ((⊤ : SimpleGraph (Fin 3)) ⊑ C) ∧ ¬ (T ⊑ Cᶜ) := by
  classical
  let color (v : Fin N) : Bool := decide (v.val < n - 1)
  let C : SimpleGraph (Fin N) := (⊤ : SimpleGraph Bool).comap color
  refine ⟨C, ?_, ?_⟩
  · rintro ⟨f⟩
    have hinj : Function.Injective (fun i : Fin 3 => color (f i)) := by
      intro i j he
      by_contra hij
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj i j := hij
      have himg : C.Adj (f i) (f j) := f.toHom.map_adj hadj
      exact himg he
    have hcard := Fintype.card_le_of_injective _ hinj
    norm_num at hcard
  · rintro ⟨f⟩
    have hlab (i j : Fin n) : color (f i) = color (f j) := by
      obtain ⟨w⟩ := hT.preconnected i j
      induction w with
      | nil => rfl
      | cons h _ ih =>
        exact (not_ne_iff.mp (f.toHom.map_adj h).2).trans ih
    have hclass (i j : Fin n) : ((f i).val < n - 1) ↔ ((f j).val < n - 1) :=
      decide_eq_decide.mp (hlab i j)
    let g (i : Fin n) : Fin (n - 1) :=
      ⟨if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1), by
        have hi := (f i).isLt
        split <;> omega⟩
    have hg : Function.Injective g := by
      intro i j he
      have heq := congrArg Fin.val he
      change (if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1)) =
        (if (f j).val < n - 1 then (f j).val else (f j).val - (n - 1)) at heq
      apply f.injective
      change f i = f j
      apply Fin.ext
      by_cases hi : (f i).val < n - 1
      · simpa only [if_pos hi, if_pos ((hclass i j).mp hi)] using heq
      · have hj : ¬ (f j).val < n - 1 := fun h => hi ((hclass i j).mpr h)
        simp only [if_neg hi, if_neg hj] at heq
        omega
    have hcard := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hcard
    omega

lemma OMA.tree_triangle_good (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : Erdos1182.IsTriangleGood T := by
  unfold Erdos1182.IsTriangleGood graphRamsey
  let good : Set ℕ := {N | ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ}
  change sInf good = 2 * n - 1
  have h : 2 * n - 1 ∈ good := OMA.tree_ramsey_upper n hn (T := T) hT
  apply le_antisymm (Nat.sInf_le h)
  refine le_csInf ⟨2 * n - 1, h⟩ ?_
  intro N hN
  by_contra! hlt
  obtain ⟨C, hC1, hC2⟩ := OMA.tree_ramsey_lower_witness n N hn hlt T hT.connected
  change ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ at hN
  exact (hN C).elim hC1 hC2

theorem OMA.fge1182 : type_of% @Erdos1182.erdos_1182.variants.F_ge_pred := by
  classical
  intro n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply Erdos1182.le_F
  · have htop := (connected_top (V := Fin n)).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at htop
    have hcard : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
      rw [Set.ncard_eq_toFinset_card']
      change (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2
      rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    change n ≤ (⊤ : SimpleGraph (Fin n)).edgeSet.ncard + 1 at htop
    rw [hcard] at htop
    omega
  · intro T hconn hbound
    have hmin := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at hmin
    apply OMA.tree_triangle_good n hn T
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_fin, Nat.card_coe_set_eq]
    omega
end OMA1182Lower


/-! # A linear bound for the triangle-goodness threshold -/
-- Credit: @steveDOTdigital
namespace OMA.FiveCycleBound
open Erdos1182 Filter
open scoped Classical

private def near (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i
private lemma irref : ∀ i : Fin 5, ¬ near i i := by unfold near; decide
private lemma noTriangle : ∀ i j l : Fin 5, near i j → near j l → ¬ near i l := by
  unfold near
  decide

private noncomputable def cls {n : ℕ} (c : Fin n → Fin 5) (i : Fin 5) : Finset (Fin n) :=
  Finset.univ.filter fun x => c x = i

private noncomputable def forbidden {n : ℕ} (c : Fin n → Fin 5) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => near (c e.1) (c e.2)

-- Both orientations of a crossing edge count. The sets of oriented edges
-- are disjoint since the two vertex classes are disjoint.
private lemma rectangle {n : ℕ} (c : Fin n → Fin 5) (A B : Finset (Fin n))
    (h : ∀ a ∈ A, ∀ b ∈ B, near (c a) (c b)) :
    2 * A.card * B.card ≤ (forbidden c).card := by
  classical
  have inc : (A ×ˢ B) ∪ (B ×ˢ A) ⊆ forbidden c := by
    rintro ⟨a,b⟩ hab
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hab with ab | ba
    · exact h a (Finset.mem_product.mp ab).1 b (Finset.mem_product.mp ab).2
    · exact Or.symm (h b (Finset.mem_product.mp ba).2 a (Finset.mem_product.mp ba).1)
  have dis : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨a,b⟩ ab ba
    exact irref _ (h a (Finset.mem_product.mp ab).1 a (Finset.mem_product.mp ba).1)
  have card := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint dis,Finset.card_product,Finset.card_product] at card
  nlinarith only [card]

-- Center at the largest class. Either its two neighbors together contain
-- a tenth of all vertices, or the two opposite (adjacent) classes are large.
private lemma manyForbidden {n : ℕ} (hn : 200 ≤ n) (c : Fin n → Fin 5)
    (cap : ∀ i, (cls c i).card ≤ (2*n+4)/5) : n^2 ≤ 25*(forbidden c).card := by
  classical
  obtain ⟨i,_,largest⟩ := Finset.exists_max_image Finset.univ (fun j => (cls c j).card)
    ⟨(0 : Fin 5),Finset.mem_univ _⟩
  let A (j : Fin 5) := cls c (i+j)
  let a (j : Fin 5) := (A j).card
  have mx (j : Fin 5) : a j ≤ a 0 := by
    simpa [a,A] using largest (i+j) (Finset.mem_univ _)
  have cap' (j : Fin 5) : 200*a j ≤ 81*n := by
    have : a j ≤ (2*n+4)/5 := cap (i+j)
    omega
  have total : ∑ j, a j = n := by
    have fib := Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ (fun x => c x - i)
    have eq (j : Fin 5) : A j = Finset.univ.filter (fun x => c x - i = j) := by
      ext x
      simp [A,cls,sub_eq_iff_eq_add,add_comm]
    simpa [a,eq] using fib
  simp [Fin.sum_univ_succ] at total
  have m0 := mx 1
  have m1 := mx 2
  have m2 := mx 3
  have m3 := mx 4
  have maxbig : n ≤ 5*a 0 := by omega
  have member {x j} (hx : x ∈ A j) : c x = i+j := (Finset.mem_filter.mp hx).2
  by_cases h : n ≤ 10*(a 1 + a 4)
  · have cross := rectangle c (A 0) (A 1 ∪ A 4) (by
      intro x hx y hy
      obtain h1 | h4 := Finset.mem_union.mp hy
      · rw [member hx,member h1]
        exact (by unfold near; decide : ∀ i : Fin 5, near (i+0) (i+1)) i
      · rw [member hx,member h4]
        exact (by unfold near; decide : ∀ i : Fin 5, near (i+0) (i+4)) i)
    have dis : Disjoint (A 1) (A 4) := Finset.disjoint_left.mpr fun x h1 h4 =>
      (by decide : (1 : Fin 5) ≠ 4) (add_left_cancel ((member h1).symm.trans (member h4)))
    rw [Finset.card_union_of_disjoint dis] at cross
    change 2*a 0*(a 1+a 4) ≤ _ at cross
    have mult := Nat.mul_le_mul maxbig h
    nlinarith only [mult,cross]
  · have cap0 := cap' 0
    have cap2 := cap' 2
    have cap3 := cap' 3
    have cross := rectangle c (A 2) (A 3) (by
      intro x hx y hy
      rw [member hx,member hy]
      exact (by unfold near; decide : ∀ i : Fin 5, near (i+2) (i+3)) i)
    change 2*a 2*a 3 ≤ _ at cross
    have cases : (n ≤ 12*a 2 ∧ 6*n ≤ 25*a 3) ∨ (n ≤ 12*a 3 ∧ 6*n ≤ 25*a 2) := by omega
    rcases cases with p | p <;> have mult := Nat.mul_le_mul p.1 p.2 <;> nlinarith only [mult,cross]

-- Count all ordered lists of 45n edges. For each admissible partition,
-- at most 24/25 of the ordered pairs avoid its forbidden edges, and
-- there are at most 5^n partitions.
private lemma hitting {n : ℕ} (hn : 200 ≤ n) :
    ∃ L : Fin (45*n) → Fin n × Fin n, ∀ c : Fin n → Fin 5,
      (∀ i, (cls c i).card ≤ (2*n+4)/5) → ∃ t, L t ∈ forbidden c := by
  classical
  let m := 45*n
  let K := 24*n^2/25
  let P := Finset.univ.filter (fun c : Fin n → Fin 5 => ∀ i, (cls c i).card ≤ (2*n+4)/5)
  let miss (c : Fin n → Fin 5) := Fintype.piFinset (fun _ : Fin m => (forbidden c)ᶜ)
  have one (c) (hc : c ∈ P) : (miss c).card ≤ K^m := by
    have hf := manyForbidden hn c (Finset.mem_filter.mp hc).2
    have rest := Finset.card_compl_add_card (forbidden c)
    rw [Fintype.card_prod,Fintype.card_fin,← pow_two] at rest
    have bound : (forbidden c)ᶜ.card ≤ K := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
      omega
    simpa [miss] using Nat.pow_le_pow_left bound m
  have pcount : P.card ≤ 5^n := by simpa using (Finset.card_filter_le _ _ : P.card ≤ _)
  have union : (P.biUnion miss).card ≤ 5^n * K^m := by
    calc
      _ ≤ ∑ c ∈ P, (miss c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ P, K^m := Finset.sum_le_sum one
      _ = P.card * K^m := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ pcount
  have gap : 5^n * K^m < (n^2)^m := by
    have base : 5*(24:ℕ)^45 < 25^45 := by norm_num1
    have exp := Nat.pow_lt_pow_left base (show n ≠ 0 by omega)
    rw [mul_pow, ← pow_mul, ← pow_mul] at exp
    have keep : K*25 ≤ 24*n^2 := Nat.div_mul_le_self _ _
    have powers := Nat.pow_le_pow_left keep m
    rw [mul_pow,mul_pow] at powers
    have scaled : (5^n * K^m)*25^m < (n^2)^m*25^m := calc
      _ = 5^n*(K^m*25^m) := Nat.mul_assoc ..
      _ ≤ 5^n*(24^m*(n^2)^m) := Nat.mul_le_mul_left _ powers
      _ = (5^n*24^m)*(n^2)^m := (Nat.mul_assoc ..).symm
      _ < 25^m*(n^2)^m := Nat.mul_lt_mul_of_pos_right exp (pow_pos (pow_pos (by omega : 0 < n) _) _)
      _ = _ := Nat.mul_comm ..
    exact Nat.lt_of_mul_lt_mul_right scaled
  have all : (Finset.univ : Finset (Fin m → Fin n × Fin n)).card = (n^2)^m := by simp [pow_two]
  obtain ⟨L,_,out⟩ := Finset.exists_mem_notMem_of_card_lt_card (union.trans_lt (gap.trans_eq all.symm))
  refine ⟨L,fun c cap => ?_⟩
  by_contra! avoid
  apply out
  exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,cap⟩,
    Fintype.mem_piFinset.mpr fun t => Finset.mem_compl.mpr (avoid t)⟩

private lemma graph_exists {n : ℕ} (hn : 200 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard ≤ 46*n ∧ ¬ IsTriangleGood G := by
  classical
  obtain ⟨L,hit⟩ := hitting hn
  let root : Fin n := ⟨0,by omega⟩
  let listed := Finset.univ.image fun t => s((L t).1,(L t).2)
  let spokes := Finset.univ.image fun v => s(root,v)
  let E := listed ∪ spokes
  let G := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))
  refine ⟨G, SimpleGraph.Connected.of_isUniversal (v := root) ?_, ?_, ?_⟩
  · intro w h
    exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ w)),h⟩
  · have bound : G.edgeSet.ncard ≤ E.card := by
      change (SimpleGraph.fromEdgeSet _).edgeSet.ncard ≤ _
      rw [SimpleGraph.edgeSet_fromEdgeSet, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard Set.sdiff_subset
    have a : listed.card ≤ 45*n := (Finset.card_image_le).trans_eq (by simp)
    have b : spokes.card ≤ n := (Finset.card_image_le).trans_eq (by simp)
    have union := Finset.card_union_le listed spokes
    dsimp [E] at bound
    omega
  · intro good
    let N := 2*n-1
    let sizes : Set ℕ := {m | ∀ D : SimpleGraph (Fin m),
      (⊤ : SimpleGraph (Fin 3)).IsContained D ∨ G.IsContained Dᶜ}
    change sInf sizes = N at good
    have ne : sizes.Nonempty := by
      by_contra! hempty
      rw [hempty] at good
      simp [N] at good
      omega
    have minimal := csInf_mem ne
    rw [good] at minimal
    obtain ⟨e⟩ : Nonempty (Fin N ↪ Fin 5 × Fin ((2*n+4)/5)) :=
      Function.Embedding.nonempty_of_card_le (by simp [N]; omega)
    let D : SimpleGraph (Fin N) := {
      Adj := fun a b => near (e a).1 (e b).1
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun _ => irref _⟩ }
    rcases minimal D with red | blue
    · let T := red.some
      exact noTriangle _ _ _
        (T.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide))
        (T.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide))
        (T.toHom.map_rel' (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by decide))
    · let f := blue.some
      let c (x : Fin n) := (e (f x)).1
      have cap (i : Fin 5) : (cls c i).card ≤ (2*n+4)/5 := by
        have bound := Finset.card_le_card_of_injOn
          (s := cls c i) (t := (Finset.univ : Finset (Fin ((2*n+4)/5))))
          (fun x => (e (f x)).2) (fun _ _ => Finset.mem_univ _) (by
            intro x hx y hy heq
            apply f.injective
            apply e.injective
            exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) heq)
        simpa using bound
      obtain ⟨t,ht⟩ := hit c cap
      have adj : near (c (L t).1) (c (L t).2) := (Finset.mem_filter.mp ht).2
      have diff : (L t).1 ≠ (L t).2 := by intro h; rw [h] at adj; exact irref _ adj
      have edge : G.Adj (L t).1 (L t).2 := (SimpleGraph.fromEdgeSet_adj _).mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)),diff⟩
      exact (f.toHom.map_rel' edge).2 adj

theorem linear_bound {n : ℕ} (hn : 200 ≤ n) : F n ≤ 46*n := by
  obtain ⟨G,conn,small,bad⟩ := graph_exists hn
  unfold F
  apply csSup_le'
  rintro q ⟨_,hq⟩
  by_contra! h
  exact bad (hq G conn (small.trans h.le))
end OMA.FiveCycleBound

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.parts.ii := by
  constructor
  · refine Asymptotics.IsBigO.of_bound 46 ?_
    filter_upwards [Filter.eventually_ge_atTop 200] with n hn
    have h := OMA.FiveCycleBound.linear_bound hn
    show ‖(Erdos1182.F n : ℝ)‖ ≤ 46 * ‖(n : ℝ)‖
    simp only [Real.norm_eq_abs, Nat.abs_cast]
    exact_mod_cast h
  · refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have h := OMA.fge1182 hn
    have h2 : n ≤ 2 * Erdos1182.F n := by omega
    show ‖(n : ℝ)‖ ≤ 2 * ‖(Erdos1182.F n : ℝ)‖
    simp only [Real.norm_eq_abs, Nat.abs_cast]
    exact_mod_cast h2
