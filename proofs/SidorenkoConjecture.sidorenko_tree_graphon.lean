import FormalConjectures.Wikipedia.SidorenkoConjecture

/-!
# Sidorenko's Inequality for Trees (Graphon Version)

We prove `SidorenkoConjecture.sidorenko_tree_graphon`: for every finite tree `H` on `V` and every
graphon `W : LimitObjects.Graphon`,
`(graphonEdgeDensity W) ^ H.edgeFinset.card ≤ graphonHomDensity H W`.

1. Transport `H` along `Fintype.equivFin V` to a tree on `Fin m` (`m = Fintype.card V`). For `m = 1`,
   `H` has no edges and both sides equal `1`.
2. For `m ≥ 2` and any strictly positive symmetric matrix `A : Fin N → Fin N → ℝ`, define the
   closed-form tree Markov measure `μ_H(φ) = (∏_{e ∈ E} A(φ(e))) / (S · ∏_{v} d(φ(v))^{deg(v) - 1})`.
   Leaf-removal induction on `|V|` shows every vertex marginal of `μ_H` equals `d(x) / S`, and
   two applications of Jensen's inequality for concave `Real.log` give
   `(S / N^2) ^ |E| ≤ (1 / N^|V|) ∑_φ ∏_{e ∈ E} A(φ(e))`.
3. Passing `ε → 0⁺` on `A + ε` extends this to nonnegative symmetric matrices. Evaluating on
   random samples `A(u)_{a,b} = W(u a, u b)` (`u : Fin N → UnitInterval`), integrating over `u`
   via `convexOn_pow`, bounding non-injective `m`-tuples by `m^2 / N`, and letting `N → ∞` finishes.
-/

-- Problem: Case: `H` is a tree (Sidorenko 1993, graphon version).
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SidorenkoConjecture.lean:108 (declaration SidorenkoConjecture.sidorenko_tree_graphon)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace SidorenkoTreeGraphonProof

open MeasureTheory Finset SimpleGraph LimitObjects Filter

private abbrev U := LimitObjects.UnitInterval

private noncomputable abbrev piVol (r : ℕ) : Measure (Fin r → U) :=
  Measure.pi (fun _ : Fin r => (volume : Measure U))

/- ### Section 1: Tree Markov measure and finite positive symmetric matrix inequality -/

private def evalSym2A {V : Type*} {N : ℕ} (A : Fin N → Fin N → ℝ)
    (hA : ∀ a b, A a b = A b a) (φ : V → Fin N) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun u v => A (φ u) (φ v), fun u v => hA (φ u) (φ v)⟩ e

private lemma evalSym2A_mk {V : Type*} {N : ℕ} (A : Fin N → Fin N → ℝ)
    (hA : ∀ a b, A a b = A b a) (φ : V → Fin N) (u v : V) :
    evalSym2A A hA φ s(u, v) = A (φ u) (φ v) := rfl

private lemma isTree_induce_compl_of_degree_one {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] (hTree : H.IsTree) {v : V} (hdeg : H.degree v = 1) :
    (H.induce ({v}ᶜ : Set V)).IsTree := by
  refine ⟨hTree.connected.induce_compl_singleton_of_degree_eq_one hdeg, ?_⟩
  intro u p hp
  let emb : (H.induce ({v}ᶜ : Set V)) ↪g H := SimpleGraph.Embedding.induce ({v}ᶜ : Set V)
  have hcyc : (p.map emb.toHom).IsCycle := hp.map emb.injective
  exact hTree.isAcyclic (p.map emb.toHom) hcyc

private lemma degree_pos_of_isTree {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] (hTree : H.IsTree) (hcard : 2 ≤ Fintype.card V)
    (u : V) : 1 ≤ H.degree u := by
  have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hw⟩ := exists_ne u
  obtain ⟨p, _⟩ := hTree.connected.exists_isPath u w
  have hnil : ¬ p.Nil := fun h => hw (SimpleGraph.Walk.Nil.eq h).symm
  have hadj : H.Adj u (p.snd) := p.adj_snd hnil
  have hmem : p.snd ∈ H.neighborFinset u := (SimpleGraph.mem_neighborFinset H u p.snd).mpr hadj
  exact Finset.one_le_card.mpr ⟨p.snd, hmem⟩

private noncomputable def treeMeasure {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {N : ℕ} (A : Fin N → Fin N → ℝ) (hA : ∀ a b, A a b = A b a) (φ : V → Fin N) : ℝ :=
  (∏ e ∈ H.edgeFinset, evalSym2A A hA φ e) /
    ((∑ a : Fin N, ∑ b : Fin N, A a b) *
      ∏ v : V, (∑ b : Fin N, A (φ v) b) ^ (H.degree v - 1))

private lemma treeMeasure_pos {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {N : ℕ} (hN : 1 ≤ N) (A : Fin N → Fin N → ℝ) (hA : ∀ a b, A a b = A b a)
    (hApos : ∀ a b, 0 < A a b) (φ : V → Fin N) :
    0 < treeMeasure H A hA φ := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hd_pos : ∀ a : Fin N, 0 < ∑ b : Fin N, A a b := fun a =>
    Finset.sum_pos (fun b _ => hApos a b) hne
  have hS_pos : 0 < ∑ a : Fin N, ∑ b : Fin N, A a b :=
    Finset.sum_pos (fun a _ => hd_pos a) hne
  unfold treeMeasure
  refine div_pos ?_ (mul_pos hS_pos ?_)
  · refine Finset.prod_pos fun e _ => ?_
    induction e using Sym2.ind with
    | _ u v => exact hApos (φ u) (φ v)
  · exact Finset.prod_pos fun v _ => pow_pos (hd_pos (φ v)) _

private lemma tree_marginal_aux {N : ℕ} (hN : 1 ≤ N) (A : Fin N → Fin N → ℝ)
    (hA : ∀ a b, A a b = A b a) (hApos : ∀ a b, 0 < A a b) :
    ∀ n : ℕ, 2 ≤ n →
      ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = n →
        ∀ (H : SimpleGraph V) [DecidableRel H.Adj], H.IsTree →
          ∀ (w : V) (x : Fin N),
            (∑ φ : V → Fin N, if φ w = x then treeMeasure H A hA φ else 0) =
              (∑ b : Fin N, A x b) / (∑ a : Fin N, ∑ b : Fin N, A a b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn2 V _ _ hcard H _ hTree w x
    have hneN : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hd_pos : ∀ a : Fin N, 0 < ∑ b : Fin N, A a b := fun a =>
      Finset.sum_pos (fun b _ => hApos a b) hneN
    have hS_pos : 0 < ∑ a : Fin N, ∑ b : Fin N, A a b :=
      Finset.sum_pos (fun a _ => hd_pos a) hneN
    by_cases hn2eq : n = 2
    · subst hn2eq
      have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨u, huw⟩ := exists_ne w
      have hV_eq : ∀ z : V, z = w ∨ z = u := by
        have hpair : ({w, u} : Finset V) = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          rw [Finset.card_univ, hcard, Finset.card_pair huw.symm]
        intro z
        have hz : z ∈ ({w, u} : Finset V) := by rw [hpair]; exact Finset.mem_univ z
        simpa using hz
      have hadj_wu : H.Adj w u := by
        obtain ⟨p, _⟩ := hTree.connected.exists_isPath w u
        have hnil : ¬ p.Nil := fun h => huw (SimpleGraph.Walk.Nil.eq h).symm
        have hsnd : H.Adj w p.snd := p.adj_snd hnil
        rcases hV_eq p.snd with h | h
        · rw [h] at hsnd
          exact absurd hsnd (H.loopless.irrefl w)
        · rwa [← h]
      have hedges : H.edgeFinset = {s(w, u)} := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_singleton]
          constructor
          · intro hab
            rcases hV_eq a with rfl | rfl <;> rcases hV_eq b with rfl | rfl
            · exact absurd hab (H.loopless.irrefl _)
            · rfl
            · exact Sym2.eq_swap
            · exact absurd hab (H.loopless.irrefl _)
          · intro he
            rw [Sym2.eq_iff] at he
            rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hadj_wu
            · exact hadj_wu.symm
      have hdeg_w : H.degree w = 1 := by
        have hnb : H.neighborFinset w = {u} := by
          ext z
          simp only [mem_neighborFinset, Finset.mem_singleton]
          constructor
          · intro hz
            rcases hV_eq z with rfl | rfl
            · exact absurd hz (H.loopless.irrefl _)
            · rfl
          · rintro rfl; exact hadj_wu
        rw [SimpleGraph.degree, hnb, Finset.card_singleton]
      have hdeg_u : H.degree u = 1 := by
        have hnb : H.neighborFinset u = {w} := by
          ext z
          simp only [mem_neighborFinset, Finset.mem_singleton]
          constructor
          · intro hz
            rcases hV_eq z with rfl | rfl
            · rfl
            · exact absurd hz (H.loopless.irrefl _)
          · rintro rfl; exact hadj_wu.symm
        rw [SimpleGraph.degree, hnb, Finset.card_singleton]
      have hmu : ∀ φ : V → Fin N,
          treeMeasure H A hA φ = A (φ w) (φ u) / (∑ a : Fin N, ∑ b : Fin N, A a b) := by
        intro φ
        unfold treeMeasure
        rw [hedges, Finset.prod_singleton, evalSym2A_mk]
        have hprod1 : (∏ z : V, (∑ b : Fin N, A (φ z) b) ^ (H.degree z - 1)) = 1 := by
          refine Finset.prod_eq_one fun z _ => ?_
          rcases hV_eq z with rfl | rfl
          · simp [hdeg_w]
          · simp [hdeg_u]
        rw [hprod1, mul_one]
      simp_rw [hmu]
      let eqv : (Fin N × Fin N) ≃ (V → Fin N) :=
        { toFun := fun p z => if z = w then p.1 else p.2
          invFun := fun φ => (φ w, φ u)
          left_inv := fun ⟨a, b⟩ => Prod.ext (if_pos rfl) (if_neg huw)
          right_inv := fun φ => by
            funext z
            rcases hV_eq z with rfl | rfl <;> simp [huw] }
      rw [← Equiv.sum_comp eqv, Fintype.sum_prod_type]
      simp only [eqv, Equiv.coe_fn_mk, ↓reduceIte, huw]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, ← Finset.sum_div]
    · have hn3 : 3 ≤ n := by omega
      have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v₁, v₂, hv12, hdeg1, hdeg2⟩ := hTree.exists_ne_and_degree_eq_one
      have hex_leaf : ∃ v : V, v ≠ w ∧ H.degree v = 1 := by
        by_cases h1 : v₁ = w
        · exact ⟨v₂, fun h => hv12 (h1.trans h.symm), hdeg2⟩
        · exact ⟨v₁, h1, hdeg1⟩
      obtain ⟨v, hvw, hdegv⟩ := hex_leaf
      obtain ⟨p, hp_adj, hp_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegv
      have hpv : p ≠ v := (H.ne_of_adj hp_adj).symm
      let V' := { z : V // z ∈ ({v}ᶜ : Set V) }
      let H' : SimpleGraph V' := H.induce ({v}ᶜ : Set V)
      have hcard' : Fintype.card V' = n - 1 := by
        have hcompl : Fintype.card V' = Fintype.card V - 1 := by
          dsimp only [V']
          rw [Fintype.card_congr (Equiv.subtypeEquivRight fun z => Set.mem_compl_singleton_iff),
            Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        omega
      have hTree' : H'.IsTree := isTree_induce_compl_of_degree_one hTree hdegv
      let w' : V' := ⟨w, by simp [hvw.symm]⟩
      let p' : V' := ⟨p, by simp [hpv]⟩
      have hdeg_p' : 1 ≤ H'.degree p' := degree_pos_of_isTree hTree' (by omega) p'
      have hdeg_p : H.degree p = H'.degree p' + 1 := by
        have hnb : H.neighborFinset p =
            insert v ((H'.neighborFinset p').image Subtype.val) := by
          ext z
          simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_image]
          constructor
          · intro hpz
            by_cases hzv : z = v
            · exact Or.inl hzv
            · right
              refine ⟨⟨z, by simp [hzv]⟩, ?_, rfl⟩
              exact hpz
          · rintro (rfl | ⟨⟨z, hz⟩, hpz, rfl⟩)
            · exact hp_adj.symm
            · exact hpz
        have hv_not : v ∉ (H'.neighborFinset p').image Subtype.val := by
          simp only [Finset.mem_image, not_exists, not_and]
          intro z _ hzv
          exact z.2 hzv
        rw [SimpleGraph.degree, hnb, Finset.card_insert_of_notMem hv_not,
          Finset.card_image_of_injective _ Subtype.val_injective]
        rfl
      have hdeg_other : ∀ z' : V', z' ≠ p' → H.degree z'.1 = H'.degree z' := by
        intro z' hz'p
        have hzv_not_adj : ¬ H.Adj z'.1 v := by
          intro hadj
          exact hz'p (Subtype.ext (hp_uniq z'.1 hadj.symm))
        have hnb : H.neighborFinset z'.1 = (H'.neighborFinset z').image Subtype.val := by
          ext u
          simp only [mem_neighborFinset, Finset.mem_image]
          constructor
          · intro hu
            have huv : u ≠ v := fun h => hzv_not_adj (h ▸ hu)
            exact ⟨⟨u, by simp [huv]⟩, hu, rfl⟩
          · rintro ⟨⟨u, _⟩, hu, rfl⟩
            exact hu
        rw [SimpleGraph.degree, hnb, Finset.card_image_of_injective _ Subtype.val_injective]
        rfl
      have hedges : H.edgeFinset =
          insert s(p, v) (H'.edgeFinset.image (Sym2.map Subtype.val)) := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_insert, Finset.mem_image]
          constructor
          · intro hab
            by_cases hav : a = v
            · subst hav
              have hbp : b = p := hp_uniq b hab
              subst hbp
              exact Or.inl Sym2.eq_swap
            · by_cases hbv : b = v
              · subst hbv
                have hap : a = p := hp_uniq a hab.symm
                subst hap
                exact Or.inl rfl
              · right
                refine ⟨s(⟨a, by simp [hav]⟩, ⟨b, by simp [hbv]⟩), hab, rfl⟩
          · rintro (he | ⟨e', he', hmap⟩)
            · rw [Sym2.eq_iff] at he
              rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hp_adj.symm
              · exact hp_adj
            · induction e' using Sym2.ind with
              | _ a' b' =>
                simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
                rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact he'
                · exact he'.symm
      have hpv_notMem : s(p, v) ∉ H'.edgeFinset.image (Sym2.map Subtype.val) := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro e' _ he'
        induction e' using Sym2.ind with
        | _ a' b' =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at he'
          rcases he' with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact b'.2 hb
          · exact a'.2 ha
      have hmap_inj : Function.Injective (Sym2.map (Subtype.val : V' → V)) :=
        Sym2.map.injective Subtype.val_injective
      have hfactor : ∀ φ : V → Fin N,
          treeMeasure H A hA φ =
            treeMeasure H' A hA (fun z' => φ z'.1) *
              (A (φ p) (φ v) / (∑ b : Fin N, A (φ p) b)) := by
        intro φ
        have hnum : (∏ e ∈ H.edgeFinset, evalSym2A A hA φ e) =
            A (φ p) (φ v) * ∏ e' ∈ H'.edgeFinset, evalSym2A A hA (fun z' => φ z'.1) e' := by
          rw [hedges, Finset.prod_insert hpv_notMem,
            Finset.prod_image (fun _ _ _ _ h => hmap_inj h), evalSym2A_mk]
          congr 1
          refine Finset.prod_congr rfl fun e' _ => ?_
          induction e' using Sym2.ind with
          | _ a' b' => rfl
        have hden : (∏ z : V, (∑ b : Fin N, A (φ z) b) ^ (H.degree z - 1)) =
            (∑ b : Fin N, A (φ p) b) *
              ∏ z' : V', (∑ b : Fin N, A (φ z'.1) b) ^ (H'.degree z' - 1) := by
          have hsplitV : (∏ z : V, (∑ b : Fin N, A (φ z) b) ^ (H.degree z - 1)) =
              (∑ b : Fin N, A (φ v) b) ^ (H.degree v - 1) *
                ∏ z' : V', (∑ b : Fin N, A (φ z'.1) b) ^ (H.degree z'.1 - 1) := by
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
            congr 1
            refine Finset.prod_bij (fun z hz => (⟨z, by simpa using (Finset.mem_erase.mp hz).1⟩ : V'))
              (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => congrArg Subtype.val h)
              (fun z' _ => ⟨z'.1, Finset.mem_erase.mpr
                ⟨Set.mem_compl_singleton_iff.mp z'.2, Finset.mem_univ _⟩, rfl⟩)
              (fun _ _ => rfl)
          rw [hsplitV, hdegv, Nat.sub_self, pow_zero, one_mul]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p'),
            ← Finset.mul_prod_erase Finset.univ
              (fun z' : V' => (∑ b : Fin N, A (φ z'.1) b) ^ (H'.degree z' - 1)) (Finset.mem_univ p')]
          have hrest :
              ∏ z' ∈ Finset.univ.erase p', (∑ b : Fin N, A (φ z'.1) b) ^ (H.degree z'.1 - 1) =
              ∏ z' ∈ Finset.univ.erase p', (∑ b : Fin N, A (φ z'.1) b) ^ (H'.degree z' - 1) := by
            refine Finset.prod_congr rfl fun z' hz' => ?_
            rw [hdeg_other z' (Finset.ne_of_mem_erase hz')]
          rw [hrest, ← mul_assoc]
          congr 1
          change (∑ b : Fin N, A (φ p) b) ^ (H.degree p - 1) =
            (∑ b : Fin N, A (φ p) b) * (∑ b : Fin N, A (φ p) b) ^ (H'.degree p' - 1)
          have hexp : H.degree p - 1 = (H'.degree p' - 1) + 1 := by omega
          rw [hexp, pow_succ']
        unfold treeMeasure
        rw [hnum, hden]
        have hdp_ne : (∑ b : Fin N, A (φ p) b) ≠ 0 := ne_of_gt (hd_pos (φ p))
        have hS_ne : (∑ a : Fin N, ∑ b : Fin N, A a b) ≠ 0 := ne_of_gt hS_pos
        have hP_ne : (∏ z' : V', (∑ b : Fin N, A (φ z'.1) b) ^ (H'.degree z' - 1)) ≠ 0 :=
          ne_of_gt (Finset.prod_pos fun z' _ => pow_pos (hd_pos (φ z'.1)) _)
        field_simp [hdp_ne, hS_ne, hP_ne]
      let eqv : ((V' → Fin N) × Fin N) ≃ (V → Fin N) :=
        { toFun := fun q z => if h : z = v then q.2 else q.1 ⟨z, by simp [h]⟩
          invFun := fun φ => (fun z' => φ z'.1, φ v)
          left_inv := fun ⟨φ', y⟩ => by
            ext z
            · have hz : z.1 ≠ v := Set.mem_compl_singleton_iff.mp z.2
              simp [hz]
            · simp
          right_inv := fun φ => by
            funext z
            by_cases h : z = v
            · subst h; simp
            · simp [h] }
      rw [← Equiv.sum_comp eqv, Fintype.sum_prod_type]
      have hterm : ∀ (φ' : V' → Fin N),
          (∑ y : Fin N, if eqv (φ', y) w = x then treeMeasure H A hA (eqv (φ', y)) else 0) =
            if φ' w' = x then treeMeasure H' A hA φ' else 0 := by
        intro φ'
        have hw_eq : ∀ y : Fin N, eqv (φ', y) w = φ' w' := fun y => by
          simp [eqv, hvw.symm, w']
        have hp_eq : ∀ y : Fin N, eqv (φ', y) p = φ' p' := fun y => by
          simp [eqv, hpv, p']
        have hv_eq : ∀ y : Fin N, eqv (φ', y) v = y := fun y => by simp [eqv]
        have hrest_eq : ∀ y : Fin N, (fun z' : V' => eqv (φ', y) z'.1) = φ' := fun y => by
          funext z'
          have hz : z'.1 ≠ v := Set.mem_compl_singleton_iff.mp z'.2
          simp [eqv, hz]
        simp_rw [hw_eq]
        by_cases hwx : φ' w' = x
        · simp only [hwx, ↓reduceIte]
          have hfac : ∀ y : Fin N,
              treeMeasure H A hA (eqv (φ', y)) =
                treeMeasure H' A hA φ' * (A (φ' p') y / (∑ b : Fin N, A (φ' p') b)) := by
            intro y
            rw [hfactor, hrest_eq y, hp_eq y, hv_eq y]
          simp_rw [hfac, ← Finset.mul_sum, ← Finset.sum_div,
            div_self (ne_of_gt (hd_pos (φ' p'))), mul_one]
        · simp [hwx]
      simp_rw [hterm]
      exact ih (n - 1) (by omega) (by omega) V' hcard' H' hTree' w' x

private lemma tree_pos_matrix_sidorenko {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hTree : H.IsTree) (hV : 2 ≤ Fintype.card V)
    {N : ℕ} (hN : 1 ≤ N) (A : Fin N → Fin N → ℝ)
    (hA : ∀ a b, A a b = A b a) (hApos : ∀ a b, 0 < A a b) :
    ((1 / (N : ℝ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ H.edgeFinset.card ≤
      (1 / (N : ℝ) ^ Fintype.card V) *
        ∑ φ : V → Fin N, ∏ e ∈ H.edgeFinset, evalSym2A A hA φ e := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hneN : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let d : Fin N → ℝ := fun a => ∑ b : Fin N, A a b
  have hd_pos : ∀ a : Fin N, 0 < d a := fun a => Finset.sum_pos (fun b _ => hApos a b) hneN
  let S : ℝ := ∑ a : Fin N, d a
  have hS_pos : 0 < S := Finset.sum_pos (fun a _ => hd_pos a) hneN
  let μ : (V → Fin N) → ℝ := treeMeasure H A hA
  have hμ_pos : ∀ φ, 0 < μ φ := fun φ => treeMeasure_pos H hN A hA hApos φ
  have hmarg : ∀ (w : V) (x : Fin N), (∑ φ : V → Fin N, if φ w = x then μ φ else 0) = d x / S :=
    fun w x => tree_marginal_aux hN A hA hApos (Fintype.card V) hV V rfl H hTree w x
  have hneV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w₀⟩ := hneV
  have hμ_sum : ∑ φ : V → Fin N, μ φ = 1 := by
    calc ∑ φ : V → Fin N, μ φ
        = ∑ φ : V → Fin N, ∑ x : Fin N, if φ w₀ = x then μ φ else 0 := by
          refine Finset.sum_congr rfl fun φ _ => ?_
          simp
      _ = ∑ x : Fin N, ∑ φ : V → Fin N, if φ w₀ = x then μ φ else 0 := Finset.sum_comm
      _ = ∑ x : Fin N, d x / S := by simp_rw [hmarg w₀]
      _ = S / S := by rw [← Finset.sum_div]
      _ = 1 := div_self (ne_of_gt hS_pos)
  let Z : ℝ := ∑ φ : V → Fin N, ∏ e ∈ H.edgeFinset, evalSym2A A hA φ e
  have hZ_pos : 0 < Z := by
    have hneF : (Finset.univ : Finset (V → Fin N)).Nonempty :=
      ⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _⟩
    refine Finset.sum_pos (fun φ _ => Finset.prod_pos fun e _ => ?_) hneF
    induction e using Sym2.ind with
    | _ u v => exact hApos (φ u) (φ v)
  let Wf : (V → Fin N) → ℝ := fun φ => S * ∏ v : V, d (φ v) ^ (H.degree v - 1)
  have hWf_pos : ∀ φ, 0 < Wf φ := fun φ =>
    mul_pos hS_pos (Finset.prod_pos fun v _ => pow_pos (hd_pos (φ v)) _)
  have hμW : ∀ φ, μ φ * Wf φ = ∏ e ∈ H.edgeFinset, evalSym2A A hA φ e := by
    intro φ
    dsimp only [μ, treeMeasure, Wf, S, d]
    exact div_mul_cancel₀ _ (ne_of_gt (hWf_pos φ))
  have hjensen1 : ∑ φ : V → Fin N, μ φ * Real.log (Wf φ) ≤ Real.log Z := by
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ) (w := μ) (p := Wf)
      (fun φ _ => le_of_lt (hμ_pos φ)) hμ_sum (fun φ _ => hWf_pos φ)
    simp only [smul_eq_mul] at h
    simpa [Z, hμW] using h
  have hlog_Wf : ∀ φ : V → Fin N,
      Real.log (Wf φ) = Real.log S + ∑ v : V, ((H.degree v - 1 : ℕ) : ℝ) * Real.log (d (φ v)) := by
    intro φ
    dsimp only [Wf]
    rw [Real.log_mul (ne_of_gt hS_pos)
        (ne_of_gt (Finset.prod_pos fun v _ => pow_pos (hd_pos (φ v)) _)),
      Real.log_prod (fun v _ => ne_of_gt (pow_pos (hd_pos (φ v)) _))]
    congr 1
    refine Finset.sum_congr rfl fun v _ => Real.log_pow _ _
  have hsum_marg : ∀ v : V,
      ∑ φ : V → Fin N, μ φ * Real.log (d (φ v)) = ∑ x : Fin N, (d x / S) * Real.log (d x) := by
    intro v
    calc ∑ φ : V → Fin N, μ φ * Real.log (d (φ v))
        = ∑ φ : V → Fin N, ∑ x : Fin N, if φ v = x then μ φ * Real.log (d x) else 0 := by
          refine Finset.sum_congr rfl fun φ _ => ?_
          simp
      _ = ∑ x : Fin N, ∑ φ : V → Fin N, if φ v = x then μ φ * Real.log (d x) else 0 :=
          Finset.sum_comm
      _ = ∑ x : Fin N, (∑ φ : V → Fin N, if φ v = x then μ φ else 0) * Real.log (d x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun φ _ => ?_
          split_ifs <;> simp
      _ = ∑ x : Fin N, (d x / S) * Real.log (d x) := by simp_rw [hmarg v]
  have hdeg_sum_nat : ∑ v : V, (H.degree v - 1) + 1 = H.edgeFinset.card := by
    have hge1 : ∀ v : V, 1 ≤ H.degree v := fun v => degree_pos_of_isTree hTree hV v
    have h1 : ∑ v : V, (H.degree v - 1) + Fintype.card V = ∑ v : V, H.degree v := by
      have hcardV : Fintype.card V = ∑ _v : V, 1 := by simp
      rw [hcardV, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => Nat.sub_add_cancel (hge1 v)
    have h2 : ∑ v : V, H.degree v = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    have h3 : H.edgeFinset.card + 1 = Fintype.card V := hTree.card_edgeFinset
    omega
  have hdeg_sum_real : ∑ v : V, ((H.degree v - 1 : ℕ) : ℝ) = (H.edgeFinset.card : ℝ) - 1 := by
    have hcast : (∑ v : V, ((H.degree v - 1 : ℕ) : ℝ)) + 1 = (H.edgeFinset.card : ℝ) := by
      exact_mod_cast hdeg_sum_nat
    linarith
  have hentropy : Real.log (S / (N : ℝ)) ≤ ∑ x : Fin N, (d x / S) * Real.log (d x) := by
    have hw_nn : ∀ x ∈ (Finset.univ : Finset (Fin N)), 0 ≤ d x / S :=
      fun x _ => div_nonneg (le_of_lt (hd_pos x)) (le_of_lt hS_pos)
    have hw_sum : ∑ x : Fin N, d x / S = 1 := by
      rw [← Finset.sum_div, div_self (ne_of_gt hS_pos)]
    have hj2 := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ) (w := fun x => d x / S) (p := fun x => (d x)⁻¹)
      hw_nn hw_sum (fun x _ => inv_pos.mpr (hd_pos x))
    simp only [smul_eq_mul, Real.log_inv] at hj2
    have hsum_inv : ∑ x : Fin N, d x / S * (d x)⁻¹ = (N : ℝ) / S := by
      have hterm : ∀ x : Fin N, d x / S * (d x)⁻¹ = 1 / S := by
        intro x
        field_simp [ne_of_gt (hd_pos x), ne_of_gt hS_pos]
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
    rw [hsum_inv] at hj2
    have hlog_neg : Real.log ((N : ℝ) / S) = -Real.log (S / (N : ℝ)) := by
      rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hS_pos),
        Real.log_div (ne_of_gt hS_pos) (ne_of_gt hNpos)]
      ring
    have hneg_sum : ∑ x : Fin N, d x / S * -Real.log (d x) =
        -(∑ x : Fin N, d x / S * Real.log (d x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hlog_neg, hneg_sum] at hj2
    linarith
  have hlog_lhs_eq :
      ∑ φ : V → Fin N, μ φ * Real.log (Wf φ) =
        Real.log S + ((H.edgeFinset.card : ℝ) - 1) * ∑ x : Fin N, (d x / S) * Real.log (d x) := by
    simp_rw [hlog_Wf, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμ_sum, one_mul]
    congr 1
    calc ∑ φ : V → Fin N, μ φ * ∑ v : V, ((H.degree v - 1 : ℕ) : ℝ) * Real.log (d (φ v))
        = ∑ φ : V → Fin N, ∑ v : V, μ φ * (((H.degree v - 1 : ℕ) : ℝ) * Real.log (d (φ v))) :=
          Finset.sum_congr rfl fun φ _ => Finset.mul_sum _ _ _
      _ = ∑ v : V, ∑ φ : V → Fin N, μ φ * (((H.degree v - 1 : ℕ) : ℝ) * Real.log (d (φ v))) :=
          Finset.sum_comm
      _ = ∑ v : V, ((H.degree v - 1 : ℕ) : ℝ) * ∑ x : Fin N, (d x / S) * Real.log (d x) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← hsum_marg v, Finset.mul_sum]
          refine Finset.sum_congr rfl fun φ _ => by ring
      _ = ((H.edgeFinset.card : ℝ) - 1) * ∑ x : Fin N, (d x / S) * Real.log (d x) := by
          rw [← Finset.sum_mul, hdeg_sum_real]
  have he_ge1 : (1 : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
    have : H.edgeFinset.card + 1 = Fintype.card V := hTree.card_edgeFinset
    exact_mod_cast (by omega : 1 ≤ H.edgeFinset.card)
  have hlog_bound :
      Real.log ((N : ℝ) ^ Fintype.card V * ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card) ≤
        Real.log Z := by
    have h1 : Real.log S + ((H.edgeFinset.card : ℝ) - 1) * Real.log (S / (N : ℝ)) ≤ Real.log Z := by
      have hmul := mul_le_mul_of_nonneg_left hentropy (by linarith : (0 : ℝ) ≤ (H.edgeFinset.card : ℝ) - 1)
      linarith [hjensen1, hlog_lhs_eq]
    have hVeq : (Fintype.card V : ℝ) = (H.edgeFinset.card : ℝ) + 1 := by
      exact_mod_cast hTree.card_edgeFinset.symm
    have hlog_target :
        Real.log ((N : ℝ) ^ Fintype.card V * ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card) =
          Real.log S + ((H.edgeFinset.card : ℝ) - 1) * Real.log (S / (N : ℝ)) := by
      have hpos1 : 0 < (N : ℝ) ^ Fintype.card V := pow_pos hNpos _
      have hpos2 : 0 < ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card :=
        pow_pos (mul_pos (by positivity) hS_pos) _
      rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2), Real.log_pow, Real.log_pow,
        one_div_mul_eq_div, Real.log_div (ne_of_gt hS_pos) (ne_of_gt (pow_pos hNpos 2)),
        Real.log_pow, Real.log_div (ne_of_gt hS_pos) (ne_of_gt hNpos), hVeq]
      push_cast
      ring
    linarith
  have hpos_lhs : 0 < (N : ℝ) ^ Fintype.card V * ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card :=
    mul_pos (pow_pos hNpos _) (pow_pos (mul_pos (by positivity) hS_pos) _)
  have hexp_le : (N : ℝ) ^ Fintype.card V * ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card ≤ Z := by
    have := Real.exp_le_exp.mpr hlog_bound
    rwa [Real.exp_log hpos_lhs, Real.exp_log hZ_pos] at this
  have hdiv_le := mul_le_mul_of_nonneg_left hexp_le (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ Fintype.card V)
  have hcancel : (1 / (N : ℝ) ^ Fintype.card V) *
      ((N : ℝ) ^ Fintype.card V * ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card) =
      ((1 / (N : ℝ) ^ 2) * S) ^ H.edgeFinset.card := by
    have hne : (N : ℝ) ^ Fintype.card V ≠ 0 := ne_of_gt (pow_pos hNpos _)
    field_simp [hne]
  rwa [hcancel] at hdiv_le

private lemma tree_nonneg_matrix_sidorenko {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hTree : H.IsTree) (hV : 2 ≤ Fintype.card V)
    {N : ℕ} (hN : 1 ≤ N) (A : Fin N → Fin N → ℝ)
    (hA : ∀ a b, A a b = A b a) (hAnn : ∀ a b, 0 ≤ A a b) :
    ((1 / (N : ℝ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ H.edgeFinset.card ≤
      (1 / (N : ℝ) ^ Fintype.card V) *
        ∑ φ : V → Fin N, ∏ e ∈ H.edgeFinset, evalSym2A A hA φ e := by
  let eps : ℕ → ℝ := fun r => 1 / ((r : ℝ) + 1)
  have heps_pos : ∀ r : ℕ, 0 < eps r := fun r => by positivity
  have heps_tendsto : Tendsto eps atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hAeps_symm : ∀ r a b, A a b + eps r = A b a + eps r := fun r a b => by rw [hA a b]
  have hstep : ∀ r : ℕ,
      ((1 / (N : ℝ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, (A a b + eps r)) ^ H.edgeFinset.card ≤
        (1 / (N : ℝ) ^ Fintype.card V) *
          ∑ φ : V → Fin N, ∏ e ∈ H.edgeFinset,
            evalSym2A (fun a b => A a b + eps r) (hAeps_symm r) φ e := by
    intro r
    exact tree_pos_matrix_sidorenko H hTree hV hN (fun a b => A a b + eps r) (hAeps_symm r)
      (fun a b => by linarith [hAnn a b, heps_pos r])
  have hlhs : Tendsto
      (fun r => ((1 / (N : ℝ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, (A a b + eps r)) ^ H.edgeFinset.card)
      atTop (nhds (((1 / (N : ℝ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ H.edgeFinset.card)) := by
    have h1 : Tendsto (fun r => ∑ a : Fin N, ∑ b : Fin N, (A a b + eps r))
        atTop (nhds (∑ a : Fin N, ∑ b : Fin N, (A a b + 0))) :=
      tendsto_finsetSum _ fun a _ =>
        tendsto_finsetSum _ fun b _ => tendsto_const_nhds.add heps_tendsto
    simpa using (tendsto_const_nhds.mul h1).pow H.edgeFinset.card
  have hrhs : Tendsto
      (fun r => (1 / (N : ℝ) ^ Fintype.card V) *
        ∑ φ : V → Fin N, ∏ e ∈ H.edgeFinset,
          evalSym2A (fun a b => A a b + eps r) (hAeps_symm r) φ e)
      atTop (nhds ((1 / (N : ℝ) ^ Fintype.card V) *
        ∑ φ : V → Fin N, ∏ e ∈ H.edgeFinset, evalSym2A A hA φ e)) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun φ _ => ?_)
    refine tendsto_finsetProd _ fun e _ => ?_
    induction e using Sym2.ind with
    | _ u v =>
      simpa [evalSym2A_mk] using (tendsto_const_nhds (x := A (φ u) (φ v))).add heps_tendsto
  exact le_of_tendsto_of_tendsto' hlhs hrhs hstep

/- ### Section 2: Measure-preserving random-sampling reduction -/

private lemma measurePreserving_comp_injective {m N : ℕ} (a : Fin m → Fin N)
    (ha : Function.Injective a) :
    MeasurePreserving (fun u : Fin N → U => u ∘ a) (piVol N) (piVol m) := by
  let R := { j : Fin N // j ∉ Set.range a }
  let e : Fin m ⊕ R ≃ Fin N :=
    ((Equiv.ofInjective a ha).sumCongr (Equiv.refl R)).trans (Equiv.Set.sumCompl (Set.range a))
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => U) e).symm
      (piVol N) (Measure.pi fun _ : Fin m ⊕ R => (volume : Measure U)) :=
    (measurePreserving_piCongrLeft (fun _ : Fin N => (volume : Measure U)) e).symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ R => U))
      (Measure.pi fun _ : Fin m ⊕ R => (volume : Measure U))
      ((piVol m).prod (Measure.pi fun _ : R => (volume : Measure U))) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ R => (volume : Measure U))
  have h3 : MeasurePreserving Prod.fst
      ((piVol m).prod (Measure.pi fun _ : R => (volume : Measure U))) (piVol m) :=
    MeasureTheory.measurePreserving_fst
  have hcomp := h3.comp (h2.comp h1)
  have hfun : (Prod.fst ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ R => U)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => U) e).symm) = (fun u : Fin N → U => u ∘ a) := by
    funext u i
    rfl
  rwa [hfun] at hcomp

private lemma measurePreserving_pair_ne {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    MeasurePreserving (fun u : Fin N → U => (u a, u b)) (piVol N)
      ((volume : Measure U).prod (volume : Measure U)) := by
  let idx : Fin 2 → Fin N := fun i => if i = 0 then a else b
  have hinj : Function.Injective idx := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hab
    · exact absurd hij.symm hab
    · rfl
  have h1 := measurePreserving_comp_injective idx hinj
  have h2 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := U))
      (piVol 2) ((volume : Measure U).prod (volume : Measure U)) :=
    measurePreserving_finTwoArrow (volume : Measure U)
  have hcomp := h2.comp h1
  have hfun : (MeasurableEquiv.finTwoArrow (α := U) ∘ (fun u : Fin N → U => u ∘ idx)) =
      (fun u : Fin N → U => (u a, u b)) := by
    funext u
    simp [MeasurableEquiv.finTwoArrow, idx]
  rwa [hfun] at hcomp

private lemma graphon_entry_measurable (W : Graphon) {N : ℕ} (a b : Fin N) :
    Measurable (fun u : Fin N → U => (W (u a, u b) : ℝ)) :=
  measurable_subtype_coe.comp (W.measurable.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b)))

private lemma graphon_entry_integrable (W : Graphon) {N : ℕ} (a b : Fin N) :
    Integrable (fun u : Fin N → U => (W (u a, u b) : ℝ)) (piVol N) := by
  refine Integrable.of_bound (graphon_entry_measurable W a b).aestronglyMeasurable 1 ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (W (u a, u b)).2.1]
  exact (W (u a, u b)).2.2

private lemma integral_graphon_pair_ne (W : Graphon) {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    ∫ u, (W (u a, u b) : ℝ) ∂(piVol N) = graphonEdgeDensity W := by
  have hmp := measurePreserving_pair_ne hab
  have hmeas : AEStronglyMeasurable (fun p : U × U => (W p : ℝ))
      ((volume : Measure U).prod (volume : Measure U)) :=
    (measurable_subtype_coe.comp W.measurable).aestronglyMeasurable
  unfold graphonEdgeDensity
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hmeas)]

private lemma graphonEdgeDensity_nonneg (W : Graphon) : 0 ≤ graphonEdgeDensity W :=
  integral_nonneg fun p => (W p).2.1

private lemma evalEdge_measurable {m N : ℕ} (W : Graphon) (φ : Fin m → Fin N) (e : Sym2 (Fin m)) :
    Measurable (fun u : Fin N → U => W.evalEdge (u ∘ φ) e) := by
  induction e using Sym2.ind with
  | _ a b => exact graphon_entry_measurable W (φ a) (φ b)

private lemma evalEdge_bounds {V : Type*} (W : Graphon) (x : V → U) (e : Sym2 V) :
    0 ≤ W.evalEdge x e ∧ W.evalEdge x e ≤ 1 := by
  induction e using Sym2.ind with
  | _ a b => exact (W (x a, x b)).2

private lemma homIntegrand_comp_integrable {m N : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (W : Graphon) (φ : Fin m → Fin N) :
    Integrable (fun u : Fin N → U => graphonHomIntegrand H W (u ∘ φ)) (piVol N) := by
  have hmeas : Measurable (fun u : Fin N → U => graphonHomIntegrand H W (u ∘ φ)) :=
    Finset.measurable_prod H.edgeFinset fun e _ => evalEdge_measurable W φ e
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards with u
  have hnn : 0 ≤ graphonHomIntegrand H W (u ∘ φ) :=
    Finset.prod_nonneg fun e _ => (evalEdge_bounds W (u ∘ φ) e).1
  have hle : graphonHomIntegrand H W (u ∘ φ) ≤ 1 :=
    Finset.prod_le_one (fun e _ => (evalEdge_bounds W (u ∘ φ) e).1)
      (fun e _ => (evalEdge_bounds W (u ∘ φ) e).2)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

private lemma integral_homIntegrand_of_injective {m N : ℕ} (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (W : Graphon) (φ : Fin m → Fin N) (hφ : Function.Injective φ) :
    ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N) = graphonHomDensity H W := by
  have hmp := measurePreserving_comp_injective φ hφ
  have hFmeas : Measurable (fun x : Fin m → U => graphonHomIntegrand H W x) :=
    Finset.measurable_prod H.edgeFinset fun e _ => by
      induction e using Sym2.ind with
      | _ a b => exact graphon_entry_measurable W a b
  unfold graphonHomDensity
  change ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N) =
    ∫ x, graphonHomIntegrand H W x ∂(piVol m)
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hFmeas.aestronglyMeasurable)]

private lemma integral_homIntegrand_le_one {m N : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (W : Graphon) (φ : Fin m → Fin N) :
    ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N) ≤ 1 := by
  have hle : ∀ u : Fin N → U, graphonHomIntegrand H W (u ∘ φ) ≤ (1 : ℝ) := fun u =>
    Finset.prod_le_one (fun e _ => (evalEdge_bounds W (u ∘ φ) e).1)
      (fun e _ => (evalEdge_bounds W (u ∘ φ) e).2)
  calc ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N)
      ≤ ∫ _u : Fin N → U, (1 : ℝ) ∂(piVol N) :=
        integral_mono (homIntegrand_comp_integrable H W φ) (integrable_const 1) hle
    _ = 1 := by simp

private lemma graphonHomDensity_nonneg {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (W : Graphon) : 0 ≤ graphonHomDensity H W :=
  integral_nonneg fun x => Finset.prod_nonneg fun e _ => (evalEdge_bounds W x e).1

private lemma card_nonInjective_le (m N : ℕ) :
    (Finset.univ.filter (fun f : Fin m → Fin N => ¬ Function.Injective f)).card ≤
      m ^ 2 * N ^ (m - 1) := by
  classical
  let nonInj := Finset.univ.filter (fun f : Fin m → Fin N => ¬ Function.Injective f)
  let pairs := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2)
  let badPair (p : Fin m × Fin m) : Finset (Fin m → Fin N) :=
    Finset.univ.filter (fun f => f p.1 = f p.2)
  have hsub : nonInj ⊆ pairs.biUnion badPair := by
    intro f hf
    simp only [nonInj, Finset.mem_filter, Finset.mem_univ, true_and, Function.Injective,
      not_forall] at hf
    rcases hf with ⟨i, j, h⟩
    push Not at h
    refine Finset.mem_biUnion.mpr ⟨(i, j), ?_, ?_⟩
    · simp [pairs, h.2]
    · simp [badPair, h.1]
  have hpair_card : ∀ p ∈ pairs, (badPair p).card ≤ N ^ (m - 1) := by
    intro p hp
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let res : (Fin m → Fin N) → ({ r : Fin m // r ≠ p.2 } → Fin N) := fun f r => f r.1
    have hinj : Set.InjOn res (badPair p) := by
      intro f₁ hf₁ f₂ hf₂ heq
      simp only [Finset.mem_coe, badPair, Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
      funext r
      by_cases hr : r = p.2
      · subst hr
        rw [← hf₁, ← hf₂]
        exact congrFun heq ⟨p.1, hp⟩
      · exact congrFun heq ⟨r, hr⟩
    have hle := Finset.card_le_card_of_injOn res (fun _ _ => Finset.mem_univ _) hinj
    have hcard_dom : Fintype.card { r : Fin m // r ≠ p.2 } = m - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard_dom] using hle
  have hpairs_le : pairs.card ≤ m ^ 2 := by
    calc pairs.card
        ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_filter_le _ _
      _ = m ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  calc nonInj.card
      ≤ (pairs.biUnion badPair).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs, (badPair p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, N ^ (m - 1) := Finset.sum_le_sum hpair_card
    _ = pairs.card * N ^ (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ m ^ 2 * N ^ (m - 1) := Nat.mul_le_mul_right _ hpairs_le

private lemma tree_fin_sample_bound {m : ℕ} (hm : 2 ≤ m) (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj] (hTree : H.IsTree) (W : Graphon) {N : ℕ} (hN : 1 ≤ N) :
    ((1 - 1 / (N : ℝ)) * graphonEdgeDensity W) ^ H.edgeFinset.card ≤
      graphonHomDensity H W + (m : ℝ) ^ 2 / (N : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let avg (u : Fin N → U) : ℝ :=
    (1 / ((N : ℝ) ^ 2)) * ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ)
  let homScaled (u : Fin N → U) : ℝ :=
    (1 / ((N : ℝ) ^ m)) * ∑ φ : Fin m → Fin N, graphonHomIntegrand H W (u ∘ φ)
  have hpt : ∀ u : Fin N → U, avg u ^ H.edgeFinset.card ≤ homScaled u := by
    intro u
    have hmat := tree_nonneg_matrix_sidorenko H hTree (by simpa using hm) hN
      (fun a b => (W (u a, u b) : ℝ)) (fun a b => by simp [W.symmetric])
      (fun a b => (W (u a, u b)).2.1)
    have hprod_eq : ∀ φ : Fin m → Fin N,
        (∏ e ∈ H.edgeFinset,
          evalSym2A (fun a b => (W (u a, u b) : ℝ)) (fun a b => by simp [W.symmetric]) φ e) =
        graphonHomIntegrand H W (u ∘ φ) := by
      intro φ
      unfold graphonHomIntegrand
      refine Finset.prod_congr rfl fun e _ => ?_
      induction e using Sym2.ind with
      | _ a b => rfl
    simpa [avg, homScaled, hprod_eq, Fintype.card_fin] using hmat
  have havg_meas : Measurable avg := by
    refine measurable_const.mul ?_
    refine Finset.measurable_sum Finset.univ fun a _ => ?_
    exact Finset.measurable_sum Finset.univ fun b _ => graphon_entry_measurable W a b
  have havg_bounds : ∀ u : Fin N → U, 0 ≤ avg u ∧ avg u ≤ 1 := by
    intro u
    have hsum_nn : 0 ≤ ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => (W (u a, u b)).2.1
    have hsum_le : ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ) ≤ (N : ℝ) ^ 2 := by
      calc ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ)
          ≤ ∑ _a : Fin N, ∑ _b : Fin N, (1 : ℝ) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (W (u a, u b)).2.2
        _ = (N : ℝ) ^ 2 := by simp [sq]
    refine ⟨mul_nonneg (by positivity) hsum_nn, ?_⟩
    dsimp only [avg]
    rw [one_div_mul_eq_div, div_le_one (by positivity)]
    exact hsum_le
  have havg_int : Integrable avg (piVol N) := by
    refine Integrable.of_bound havg_meas.aestronglyMeasurable 1 ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (havg_bounds u).1]
    exact (havg_bounds u).2
  have havg_pow_int : Integrable (fun u => avg u ^ H.edgeFinset.card) (piVol N) := by
    refine Integrable.of_bound (havg_meas.pow_const H.edgeFinset.card).aestronglyMeasurable 1 ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (havg_bounds u).1 _)]
    exact pow_le_one₀ (havg_bounds u).1 (havg_bounds u).2
  have hhom_int : Integrable homScaled (piVol N) :=
    Integrable.const_mul (integrable_finsetSum Finset.univ fun φ _ => homIntegrand_comp_integrable H W φ) _
  have hjensen : (∫ u, avg u ∂(piVol N)) ^ H.edgeFinset.card ≤
      ∫ u, avg u ^ H.edgeFinset.card ∂(piVol N) :=
    (convexOn_pow H.edgeFinset.card).map_integral_le
      (continuous_pow H.edgeFinset.card).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun u => (havg_bounds u).1) havg_int havg_pow_int
  have hint_mono : ∫ u, avg u ^ H.edgeFinset.card ∂(piVol N) ≤ ∫ u, homScaled u ∂(piVol N) :=
    integral_mono havg_pow_int hhom_int hpt
  have havg_lb : (1 - 1 / (N : ℝ)) * graphonEdgeDensity W ≤ ∫ u, avg u ∂(piVol N) := by
    have hsum_int : ∫ u, avg u ∂(piVol N) =
        (1 / ((N : ℝ) ^ 2)) * ∑ a : Fin N, ∑ b : Fin N, ∫ u, (W (u a, u b) : ℝ) ∂(piVol N) := by
      dsimp only [avg]
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum Finset.univ fun a _ =>
        integrable_finsetSum Finset.univ fun b _ => graphon_entry_integrable W a b]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact integral_finsetSum Finset.univ fun b _ => graphon_entry_integrable W a b
    rw [hsum_int]
    have hterm_lb : ∀ a b : Fin N,
        (if a = b then (0 : ℝ) else graphonEdgeDensity W) ≤
          ∫ u, (W (u a, u b) : ℝ) ∂(piVol N) := by
      intro a b
      by_cases hab : a = b
      · rw [if_pos hab]
        exact integral_nonneg fun u => (W (u a, u b)).2.1
      · rw [if_neg hab, integral_graphon_pair_ne W hab]
    have hsum_lb : ∑ a : Fin N, ∑ b : Fin N, (if a = b then (0 : ℝ) else graphonEdgeDensity W) =
        ((N : ℝ) ^ 2 - (N : ℝ)) * graphonEdgeDensity W := by
      have hinner : ∀ a : Fin N,
          ∑ b : Fin N, (if a = b then (0 : ℝ) else graphonEdgeDensity W) =
            ((N : ℝ) - 1) * graphonEdgeDensity W := by
        intro a
        have hsplit : ∑ b : Fin N, (if a = b then (0 : ℝ) else graphonEdgeDensity W) +
            graphonEdgeDensity W = ∑ _b : Fin N, graphonEdgeDensity W := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_comm]
          have h0 : ∑ b ∈ Finset.univ.erase a,
              (if a = b then (0 : ℝ) else graphonEdgeDensity W) =
              ∑ _b ∈ Finset.univ.erase a, graphonEdgeDensity W := by
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hb))]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, zero_add, h0]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsplit
        linarith
      simp_rw [hinner]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hge := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hterm_lb a b
    rw [hsum_lb] at hge
    have hmul := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ 2))
    have heq : (1 / ((N : ℝ) ^ 2)) * (((N : ℝ) ^ 2 - (N : ℝ)) * graphonEdgeDensity W) =
        (1 - 1 / (N : ℝ)) * graphonEdgeDensity W := by
      field_simp [ne_of_gt hNpos]
    rwa [heq] at hmul
  have hlhs : ((1 - 1 / (N : ℝ)) * graphonEdgeDensity W) ^ H.edgeFinset.card ≤
      (∫ u, avg u ∂(piVol N)) ^ H.edgeFinset.card := by
    have hnn : 0 ≤ (1 - 1 / (N : ℝ)) * graphonEdgeDensity W := by
      refine mul_nonneg ?_ (graphonEdgeDensity_nonneg W)
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have : 1 / (N : ℝ) ≤ 1 := (div_le_one hNpos).mpr h1
      linarith
    exact pow_le_pow_left₀ hnn havg_lb H.edgeFinset.card
  have hrhs : ∫ u, homScaled u ∂(piVol N) ≤ graphonHomDensity H W + (m : ℝ) ^ 2 / (N : ℝ) := by
    have hhom_eq : ∫ u, homScaled u ∂(piVol N) =
        (1 / ((N : ℝ) ^ m)) *
          ∑ φ : Fin m → Fin N, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N) := by
      dsimp only [homScaled]
      rw [integral_const_mul,
        integral_finsetSum Finset.univ fun φ _ => homIntegrand_comp_integrable H W φ]
    rw [hhom_eq]
    let injSet := Finset.univ.filter (fun φ : Fin m → Fin N => Function.Injective φ)
    let nonInjSet := Finset.univ.filter (fun φ : Fin m → Fin N => ¬ Function.Injective φ)
    have hsplit :
        ∑ φ : Fin m → Fin N, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N) =
        (∑ φ ∈ injSet, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N)) +
        (∑ φ ∈ nonInjSet, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N)) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun φ : Fin m → Fin N => Function.Injective φ) _).symm
    have hinj_le :
        (∑ φ ∈ injSet, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N)) ≤
        ((N : ℝ) ^ m) * graphonHomDensity H W := by
      have hcongr : ∀ φ ∈ injSet,
          ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N) = graphonHomDensity H W := by
        intro φ hφ
        simp only [injSet, Finset.mem_filter, Finset.mem_univ, true_and] at hφ
        exact integral_homIntegrand_of_injective H W φ hφ
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
      have hcard_le : (injSet.card : ℝ) ≤ (N : ℝ) ^ m := by
        have hnat : injSet.card ≤ N ^ m := by
          calc injSet.card
              ≤ (Finset.univ : Finset (Fin m → Fin N)).card := Finset.card_filter_le _ _
            _ = N ^ m := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right hcard_le (graphonHomDensity_nonneg H W)
    have hnonInj_le :
        (∑ φ ∈ nonInjSet, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N)) ≤
        (m : ℝ) ^ 2 * (N : ℝ) ^ (m - 1) := by
      calc (∑ φ ∈ nonInjSet, ∫ u, graphonHomIntegrand H W (u ∘ φ) ∂(piVol N))
          ≤ ∑ _φ ∈ nonInjSet, (1 : ℝ) :=
            Finset.sum_le_sum fun φ _ => integral_homIntegrand_le_one H W φ
        _ = (nonInjSet.card : ℝ) := by simp
        _ ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ (m - 1) := by
            have hnat := card_nonInjective_le m N
            exact_mod_cast hnat
    rw [hsplit]
    have htot := add_le_add hinj_le hnonInj_le
    have hmul := mul_le_mul_of_nonneg_left htot (by positivity : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ m))
    have hpow_split : (N : ℝ) ^ m = (N : ℝ) * (N : ℝ) ^ (m - 1) := by
      have hexp : m = 1 + (m - 1) := by omega
      conv_lhs => rw [hexp, pow_add, pow_one]
    have hsimp :
        (1 / ((N : ℝ) ^ m)) *
          (((N : ℝ) ^ m) * graphonHomDensity H W + (m : ℝ) ^ 2 * (N : ℝ) ^ (m - 1)) =
        graphonHomDensity H W + (m : ℝ) ^ 2 / (N : ℝ) := by
      have hpow_ne : (N : ℝ) ^ (m - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hNpos)
      rw [mul_add, hpow_split]
      field_simp [ne_of_gt hNpos, hpow_ne]
    rwa [hsimp] at hmul
  exact le_trans hlhs (le_trans hjensen (le_trans hint_mono hrhs))

private lemma sidorenko_tree_fin {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (hTree : H.IsTree) (W : Graphon) :
    (graphonEdgeDensity W) ^ H.edgeFinset.card ≤ graphonHomDensity H W := by
  have hm1 : 1 ≤ m := by
    have hpos : 0 < Fintype.card (Fin m) := Fintype.card_pos_iff.mpr hTree.connected.nonempty
    rw [Fintype.card_fin] at hpos
    omega
  by_cases hm : m = 1
  · subst hm
    have hedges : H.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        exact H.ne_of_adj he (Subsingleton.elim a b)
    rw [hedges, Finset.card_empty, pow_zero]
    unfold graphonHomDensity graphonHomIntegrand
    simp [hedges]
  · have hm2 : 2 ≤ m := by omega
    have h1 : Tendsto
        (fun N : ℕ => ((1 - 1 / (N : ℝ)) * graphonEdgeDensity W) ^ H.edgeFinset.card)
        atTop (nhds ((graphonEdgeDensity W) ^ H.edgeFinset.card)) := by
      have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hsub : Tendsto (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub h0
      have hmul : Tendsto (fun N : ℕ => (1 - 1 / (N : ℝ)) * graphonEdgeDensity W)
          atTop (nhds ((1 - 0) * graphonEdgeDensity W)) :=
        hsub.mul tendsto_const_nhds
      simpa using hmul.pow H.edgeFinset.card
    have h2 : Tendsto (fun N : ℕ => graphonHomDensity H W + (m : ℝ) ^ 2 / (N : ℝ))
        atTop (nhds (graphonHomDensity H W)) := by
      have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hdiv : Tendsto (fun N : ℕ => (m : ℝ) ^ 2 / (N : ℝ)) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (m : ℝ) ^ 2)).mul h0
      simpa using tendsto_const_nhds.add hdiv
    exact le_of_tendsto_of_tendsto h1 h2
      (Filter.eventually_atTop.mpr ⟨1, fun N hN => tree_fin_sample_bound hm2 H hTree W hN⟩)

private lemma graphonHomDensity_congr_iso {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (H : SimpleGraph V) [DecidableRel H.Adj]
    (H' : SimpleGraph (Fin m)) [DecidableRel H'.Adj]
    (iso : H ≃g H') (W : Graphon) :
    H'.edgeFinset.card = H.edgeFinset.card ∧ graphonHomDensity H' W = graphonHomDensity H W := by
  let e : V ≃ Fin m := iso.toEquiv
  have hedges : H'.edgeFinset = H.edgeFinset.image (Sym2.map e) := by
    ext s
    induction s using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_image]
      constructor
      · intro hab
        refine ⟨s(e.symm a, e.symm b), ?_, by simp⟩
        have hrel : H'.Adj (iso (e.symm a)) (iso (e.symm b)) := by
          rw [show iso (e.symm a) = a from iso.apply_symm_apply a,
            show iso (e.symm b) = b from iso.apply_symm_apply b]
          exact hab
        exact (iso.map_rel_iff).mp hrel
      · rintro ⟨s', hs', hmap⟩
        induction s' using Sym2.ind with
        | _ u v =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
          rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (iso.map_rel_iff).mpr hs'
          · exact ((iso.map_rel_iff).mpr hs').symm
  have hcard : H'.edgeFinset.card = H.edgeFinset.card := by
    rw [hedges, Finset.card_image_of_injective _ (Sym2.map.injective e.injective)]
  refine ⟨hcard, ?_⟩
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin m => U) e)
      (Measure.pi fun _ : V => (volume : Measure U)) (piVol m) :=
    measurePreserving_piCongrLeft (fun _ : Fin m => (volume : Measure U)) e
  have hFmeas : Measurable (fun x : Fin m → U => graphonHomIntegrand H' W x) :=
    Finset.measurable_prod H'.edgeFinset fun s _ => by
      induction s using Sym2.ind with
      | _ a b => exact graphon_entry_measurable W a b
  have hint_eq : ∀ x : V → U,
      graphonHomIntegrand H' W (MeasurableEquiv.piCongrLeft (fun _ : Fin m => U) e x) =
        graphonHomIntegrand H W x := by
    intro x
    unfold graphonHomIntegrand
    rw [hedges, Finset.prod_image (fun _ _ _ _ h => Sym2.map.injective e.injective h)]
    refine Finset.prod_congr rfl fun s _ => ?_
    induction s using Sym2.ind with
    | _ u v =>
      simp [Graphon.evalEdge, MeasurableEquiv.piCongrLeft]
  unfold graphonHomDensity
  change ∫ x, graphonHomIntegrand H' W x ∂(piVol m) =
    ∫ x, graphonHomIntegrand H W x ∂(Measure.pi fun _ : V => (volume : Measure U))
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hFmeas.aestronglyMeasurable)]
  exact integral_congr_ae (Filter.Eventually.of_forall hint_eq)

end SidorenkoTreeGraphonProof

theorem OMA.solution : type_of% @SidorenkoConjecture.sidorenko_tree_graphon := by
  intro V _ _ H _ hTree W
  classical
  let m : ℕ := Fintype.card V
  let e : V ≃ Fin m := Fintype.equivFin V
  let H' : SimpleGraph (Fin m) := H.comap e.symm
  let iso : H ≃g H' :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        simp [H'] }
  have hTree' : H'.IsTree := (SimpleGraph.Iso.isTree_iff iso).mp hTree
  have ⟨hcard, hden⟩ := SidorenkoTreeGraphonProof.graphonHomDensity_congr_iso H H' iso W
  rw [← hcard, ← hden]
  exact SidorenkoTreeGraphonProof.sidorenko_tree_fin H' hTree' W
