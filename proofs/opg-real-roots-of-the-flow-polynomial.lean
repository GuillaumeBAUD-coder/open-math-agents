import OMAStatements.S_opg_real_roots_of_the_flow_polynomial

namespace FlowDisproof

open OMA.S_opg_real_roots_of_the_flow_polynomial
open scoped BigOperators

-- =========================================================================
-- Part 1: Tutte's Subset Formula for nzFlowCount on any finite multigraph
-- =========================================================================

section TutteFormula

variable {V E : Type} (src tgt : E → V)

private def IsFlow {k : ℕ} [Fintype E] [DecidableEq V] (f : E → ZMod k) : Prop :=
  ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => tgt e = v), f e) =
    ∑ e ∈ Finset.univ.filter (fun e => src e = v), f e

private def SuppFlow [Fintype E] [DecidableEq V] (A : Finset E) (k : ℕ) : Type :=
  {f : E → ZMod k // (∀ e, e ∉ A → f e = 0) ∧ IsFlow src tgt f}

private def AdjStep (A : Finset E) (u v : V) : Prop :=
  ∃ e ∈ A, (src e = u ∧ tgt e = v) ∨ (src e = v ∧ tgt e = u)

private def EdgeRel (A : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (AdjStep src tgt A)

private lemma adjStep_symm {A : Finset E} {u v : V} (h : AdjStep src tgt A u v) :
    AdjStep src tgt A v u := by
  rcases h with ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact ⟨e, he, Or.inr ⟨h1, h2⟩⟩
  · exact ⟨e, he, Or.inl ⟨h1, h2⟩⟩

private lemma edgeRel_refl (A : Finset E) (u : V) : EdgeRel src tgt A u u :=
  Relation.ReflTransGen.refl

private lemma edgeRel_trans {A : Finset E} {u v w : V}
    (h1 : EdgeRel src tgt A u v) (h2 : EdgeRel src tgt A v w) : EdgeRel src tgt A u w :=
  Relation.ReflTransGen.trans h1 h2

private lemma edgeRel_symm {A : Finset E} {u v : V} (h : EdgeRel src tgt A u v) :
    EdgeRel src tgt A v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head (adjStep_symm src tgt hstep) ih

private def edgeSetoid (A : Finset E) : Setoid V where
  r := EdgeRel src tgt A
  iseqv := ⟨edgeRel_refl src tgt A, fun h => edgeRel_symm src tgt h,
    fun h1 h2 => edgeRel_trans src tgt h1 h2⟩

private noncomputable def compCount [Fintype V] (A : Finset E) : ℕ :=
  letI := Classical.decRel (edgeSetoid src tgt A).r
  Fintype.card (Quotient (edgeSetoid src tgt A))

private lemma edgeRel_mono {A B : Finset E} (hAB : A ⊆ B) {u v : V}
    (h : EdgeRel src tgt A u v) : EdgeRel src tgt B u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨e, he, hst⟩
    exact Relation.ReflTransGen.tail ih ⟨e, hAB he, hst⟩

private lemma edgeRel_insert_iff [DecidableEq E] (A : Finset E) (e : E) (x y : V) :
    EdgeRel src tgt (insert e A) x y ↔
      EdgeRel src tgt A x y ∨
      (EdgeRel src tgt A x (src e) ∧ EdgeRel src tgt A (tgt e) y) ∨
      (EdgeRel src tgt A x (tgt e) ∧ EdgeRel src tgt A (src e) y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (edgeRel_refl src tgt A _)
    | @tail b c _ hbc ih =>
      rcases hbc with ⟨e', he', hst⟩
      rcases Finset.mem_insert.mp he' with rfl | heA
      · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inr (Or.inl ⟨h1, edgeRel_refl src tgt A _⟩)
          · exact Or.inr (Or.inl ⟨h1, edgeRel_refl src tgt A _⟩)
          · exact Or.inl h1
        · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inr (Or.inr ⟨h1, edgeRel_refl src tgt A _⟩)
          · exact Or.inl h1
          · exact Or.inr (Or.inr ⟨h1, edgeRel_refl src tgt A _⟩)
      · have hbcA : EdgeRel src tgt A b c := Relation.ReflTransGen.single ⟨e', heA, hst⟩
        rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (edgeRel_trans src tgt h1 hbcA)
        · exact Or.inr (Or.inl ⟨h1, edgeRel_trans src tgt h2 hbcA⟩)
        · exact Or.inr (Or.inr ⟨h1, edgeRel_trans src tgt h2 hbcA⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact edgeRel_mono src tgt (Finset.subset_insert e A) h
    · exact edgeRel_trans src tgt
        (edgeRel_mono src tgt (Finset.subset_insert e A) h1)
        (Relation.ReflTransGen.head ⟨e, Finset.mem_insert_self e A, Or.inl ⟨rfl, rfl⟩⟩
          (edgeRel_mono src tgt (Finset.subset_insert e A) h2))
    · exact edgeRel_trans src tgt
        (edgeRel_mono src tgt (Finset.subset_insert e A) h1)
        (Relation.ReflTransGen.head ⟨e, Finset.mem_insert_self e A, Or.inr ⟨rfl, rfl⟩⟩
          (edgeRel_mono src tgt (Finset.subset_insert e A) h2))

private lemma edgeRel_insert_of_rel [DecidableEq E] {A : Finset E} {e : E}
    (hrel : EdgeRel src tgt A (src e) (tgt e)) (x y : V) :
    EdgeRel src tgt (insert e A) x y ↔ EdgeRel src tgt A x y := by
  rw [edgeRel_insert_iff]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact edgeRel_trans src tgt (edgeRel_trans src tgt h1 hrel) h2
    · exact edgeRel_trans src tgt (edgeRel_trans src tgt h1 (edgeRel_symm src tgt hrel)) h2
  · exact Or.inl

private lemma compCount_empty [Fintype V] : compCount src tgt (∅ : Finset E) = Fintype.card V := by
  classical
  unfold compCount
  have hiff : ∀ u v : V, EdgeRel src tgt ∅ u v ↔ u = v := by
    intro u v
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail _ hstep _ =>
        rcases hstep with ⟨e, he, _⟩
        exact absurd he (Finset.notMem_empty e)
    · rintro rfl; exact edgeRel_refl src tgt ∅ u
  let e : Quotient (edgeSetoid src tgt ∅) ≃ V :=
    { toFun := Quotient.lift id (fun a b hab => (hiff a b).mp hab)
      invFun := Quotient.mk (edgeSetoid src tgt ∅)
      left_inv := fun q => Quotient.inductionOn q (fun _ => rfl)
      right_inv := fun _ => rfl }
  exact Fintype.card_congr e

private lemma compCount_insert_of_rel [Fintype V] [DecidableEq E] {A : Finset E} {e : E}
    (hrel : EdgeRel src tgt A (src e) (tgt e)) :
    compCount src tgt (insert e A) = compCount src tgt A := by
  classical
  unfold compCount
  let eqv : Quotient (edgeSetoid src tgt (insert e A)) ≃ Quotient (edgeSetoid src tgt A) :=
    { toFun := Quotient.lift (Quotient.mk (edgeSetoid src tgt A)) (fun a b hab =>
        Quotient.sound ((edgeRel_insert_of_rel src tgt hrel a b).mp hab))
      invFun := Quotient.lift (Quotient.mk (edgeSetoid src tgt (insert e A))) (fun a b hab =>
        Quotient.sound ((edgeRel_insert_of_rel src tgt hrel a b).mpr hab))
      left_inv := fun q => Quotient.inductionOn q (fun _ => rfl)
      right_inv := fun q => Quotient.inductionOn q (fun _ => rfl) }
  exact Fintype.card_congr eqv

private lemma compCount_insert_of_not_rel [Fintype V] [DecidableEq E] {A : Finset E} {e : E}
    (hnot : ¬ EdgeRel src tgt A (src e) (tgt e)) :
    compCount src tgt (insert e A) + 1 = compCount src tgt A := by
  classical
  unfold compCount
  let sA := edgeSetoid src tgt A
  let sB := edgeSetoid src tgt (insert e A)
  let qu : Quotient sA := Quotient.mk sA (src e)
  let qv : Quotient sA := Quotient.mk sA (tgt e)
  have hne : qu ≠ qv := fun h => hnot (Quotient.exact h)
  let toB : {q : Quotient sA // q ≠ qv} → Quotient sB :=
    fun q => Quotient.liftOn q.1 (Quotient.mk sB)
      (fun a b hab => Quotient.sound (edgeRel_mono src tgt (Finset.subset_insert e A) hab))
  have hsurj : Function.Surjective toB := by
    intro qb
    refine Quotient.inductionOn qb (fun x => ?_)
    by_cases hx : Quotient.mk sA x = qv
    · refine ⟨⟨qu, hne⟩, ?_⟩
      change Quotient.mk sB (src e) = Quotient.mk sB x
      apply Quotient.sound
      have hxv : EdgeRel src tgt A x (tgt e) := Quotient.exact hx
      exact (edgeRel_insert_iff src tgt A e (src e) x).mpr
        (Or.inr (Or.inl ⟨edgeRel_refl src tgt A _, edgeRel_symm src tgt hxv⟩))
    · exact ⟨⟨Quotient.mk sA x, hx⟩, rfl⟩
  have hinj : Function.Injective toB := by
    rintro ⟨q1, hq1⟩ ⟨q2, hq2⟩ heq
    apply Subtype.ext
    refine Quotient.inductionOn₂ q1 q2 (fun a b hq1 hq2 heq => ?_) hq1 hq2 heq
    have hab : EdgeRel src tgt (insert e A) a b := Quotient.exact heq
    rcases (edgeRel_insert_iff src tgt A e a b).mp hab with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Quotient.sound h
    · exfalso; exact hq2 (Quotient.sound (edgeRel_symm src tgt h2))
    · exfalso; exact hq1 (Quotient.sound h1)
  have hcard1 : Fintype.card {q : Quotient sA // q ≠ qv} = Fintype.card (Quotient sB) :=
    Fintype.card_of_bijective ⟨hinj, hsurj⟩
  have hcard2 : Fintype.card {q : Quotient sA // q ≠ qv} + 1 = Fintype.card (Quotient sA) := by
    have hc : Fintype.card {q : Quotient sA // q ≠ qv} =
        Fintype.card (Quotient sA) - Fintype.card {q : Quotient sA // q = qv} :=
      Fintype.card_subtype_compl (fun q => q = qv)
    rw [hc, Fintype.card_subtype_eq]
    have hpos : 0 < Fintype.card (Quotient sA) := Fintype.card_pos_iff.mpr ⟨qv⟩
    omega
  change Fintype.card (Quotient sB) + 1 = Fintype.card (Quotient sA)
  omega

private lemma compCount_le_card [Fintype V] (A : Finset E) : compCount src tgt A ≤ Fintype.card V := by
  classical
  unfold compCount
  exact Fintype.card_le_of_surjective (Quotient.mk (edgeSetoid src tgt A)) Quotient.mk_surjective

private lemma card_le_add_compCount [Fintype V] [DecidableEq E] (A : Finset E) :
    Fintype.card V ≤ A.card + compCount src tgt A := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.card_empty, zero_add, compCount_empty]
  | @insert e A he ih =>
    rw [Finset.card_insert_of_notMem he]
    by_cases hrel : EdgeRel src tgt A (src e) (tgt e)
    · rw [compCount_insert_of_rel src tgt hrel]; omega
    · have hc := compCount_insert_of_not_rel src tgt hrel; omega

private noncomputable def nullity [Fintype V] (A : Finset E) : ℕ :=
  A.card + compCount src tgt A - Fintype.card V

private lemma nullity_empty [Fintype V] : nullity src tgt (∅ : Finset E) = 0 := by
  unfold nullity
  rw [Finset.card_empty, zero_add, compCount_empty, Nat.sub_self]

private lemma nullity_le_card [Fintype V] (A : Finset E) : nullity src tgt A ≤ A.card := by
  unfold nullity
  have := compCount_le_card src tgt A
  omega

private lemma nullity_insert_of_rel [Fintype V] [DecidableEq E] {A : Finset E} {e : E} (he : e ∉ A)
    (hrel : EdgeRel src tgt A (src e) (tgt e)) :
    nullity src tgt (insert e A) = nullity src tgt A + 1 := by
  unfold nullity
  rw [Finset.card_insert_of_notMem he, compCount_insert_of_rel src tgt hrel]
  have := card_le_add_compCount src tgt A
  omega

private lemma nullity_insert_of_not_rel [Fintype V] [DecidableEq E] {A : Finset E} {e : E} (he : e ∉ A)
    (hnot : ¬ EdgeRel src tgt A (src e) (tgt e)) :
    nullity src tgt (insert e A) = nullity src tgt A := by
  unfold nullity
  rw [Finset.card_insert_of_notMem he]
  have hc := compCount_insert_of_not_rel src tgt hnot
  have hle := card_le_add_compCount src tgt A
  omega

private lemma sum_filter_ite_single [Fintype E] [DecidableEq V] [DecidableEq E]
    {k : ℕ} (fn : E → V) (e' : E) (w : V) :
    (∑ e ∈ Finset.univ.filter (fun e => fn e = w), (if e = e' then (1 : ZMod k) else 0)) =
      if w = fn e' then 1 else 0 := by
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single e']
  · simp [eq_comm]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ e') h

private lemma sum_flow_balance [Fintype E] [DecidableEq V] {k : ℕ} (f : E → ZMod k) (C : Finset V) :
    ∑ w ∈ C, ((∑ e ∈ Finset.univ.filter (fun e => tgt e = w), f e) -
              (∑ e ∈ Finset.univ.filter (fun e => src e = w), f e)) =
    ∑ e : E, ((if tgt e ∈ C then f e else 0) - (if src e ∈ C then f e else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  · calc ∑ w ∈ C, ∑ e ∈ Finset.univ.filter (fun e => tgt e = w), f e
        = ∑ w ∈ C, ∑ e : E, (if tgt e = w then f e else 0) := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            rw [Finset.sum_filter]
      _ = ∑ e : E, ∑ w ∈ C, (if tgt e = w then f e else 0) := Finset.sum_comm
      _ = ∑ e : E, (if tgt e ∈ C then f e else 0) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            exact Finset.sum_ite_eq C (tgt e) (fun _ => f e)
  · calc ∑ w ∈ C, ∑ e ∈ Finset.univ.filter (fun e => src e = w), f e
        = ∑ w ∈ C, ∑ e : E, (if src e = w then f e else 0) := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            rw [Finset.sum_filter]
      _ = ∑ e : E, ∑ w ∈ C, (if src e = w then f e else 0) := Finset.sum_comm
      _ = ∑ e : E, (if src e ∈ C then f e else 0) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            exact Finset.sum_ite_eq C (src e) (fun _ => f e)

private lemma exists_walk_flow [Fintype E] [DecidableEq V] [DecidableEq E]
    {k : ℕ} {A : Finset E} {s t : V} (h : EdgeRel src tgt A s t) :
    ∃ g : E → ZMod k, (∀ e, e ∉ A → g e = 0) ∧
      ∀ w : V, (∑ e ∈ Finset.univ.filter (fun e => tgt e = w), g e) -
               (∑ e ∈ Finset.univ.filter (fun e => src e = w), g e) =
               (if w = t then (1 : ZMod k) else 0) - (if w = s then 1 else 0) := by
  induction h with
  | refl =>
    refine ⟨0, fun _ _ => rfl, fun w => by simp⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨g, hsupp, hbal⟩
    rcases hbc with ⟨e', he', ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
    · refine ⟨fun e => g e + if e = e' then 1 else 0, ?_, ?_⟩
      · intro e he
        have hne : e ≠ e' := fun h => he (h ▸ he')
        simp [hsupp e he, hne]
      · intro w
        simp only [Finset.sum_add_distrib]
        have h1 := sum_filter_ite_single (k := k) tgt e' w
        have h2 := sum_filter_ite_single (k := k) src e' w
        rw [ht] at h1; rw [hs] at h2
        have := hbal w
        linear_combination this + h1 - h2
    · refine ⟨fun e => g e - if e = e' then 1 else 0, ?_, ?_⟩
      · intro e he
        have hne : e ≠ e' := fun h => he (h ▸ he')
        simp [hsupp e he, hne]
      · intro w
        simp only [Finset.sum_sub_distrib]
        have h1 := sum_filter_ite_single (k := k) tgt e' w
        have h2 := sum_filter_ite_single (k := k) src e' w
        rw [ht] at h1; rw [hs] at h2
        have := hbal w
        linear_combination this - h1 + h2

private lemma card_suppFlow_eq_pow_nullity [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (A : Finset E) (k : ℕ) [NeZero k] :
    Nat.card (SuppFlow src tgt A k) = k ^ (nullity src tgt A) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [nullity_empty, pow_zero]
    have huniq : Unique (SuppFlow src tgt ∅ k) :=
      { default := ⟨0, fun _ _ => rfl, fun _ => by simp⟩
        uniq := fun ⟨f, hf, _⟩ => Subtype.ext (funext (fun e => hf e (Finset.notMem_empty e))) }
    exact Nat.card_unique
  | @insert e A he ih =>
    by_cases hrel : EdgeRel src tgt A (src e) (tgt e)
    · rw [nullity_insert_of_rel src tgt he hrel, pow_succ, ← ih]
      rcases exists_walk_flow src tgt (k := k) (edgeRel_symm src tgt hrel) with ⟨g, hg_supp, hg_bal⟩
      let δ : E → ZMod k := fun x => g x + if x = e then 1 else 0
      have hδ_e : δ e = 1 := by simp [δ, hg_supp e he]
      have hδ_supp : ∀ x, x ∉ insert e A → δ x = 0 := by
        intro x hx
        rw [Finset.mem_insert, not_or] at hx
        simp [δ, hg_supp x hx.2, hx.1]
      have hδ_flow : IsFlow src tgt δ := by
        intro w
        have h1 := sum_filter_ite_single (k := k) tgt e w
        have h2 := sum_filter_ite_single (k := k) src e w
        have hsub : (∑ x ∈ Finset.univ.filter (fun x => tgt x = w), δ x) -
            (∑ x ∈ Finset.univ.filter (fun x => src x = w), δ x) = 0 := by
          simp only [δ, Finset.sum_add_distrib]
          have := hg_bal w
          linear_combination this + h1 - h2
        exact sub_eq_zero.mp hsub
      let eqv : SuppFlow src tgt A k × ZMod k ≃ SuppFlow src tgt (insert e A) k :=
        { toFun := fun ⟨⟨f, hf_s, hf_f⟩, c⟩ =>
            ⟨fun x => f x + c * δ x,
              fun x hx => by
                rw [Finset.mem_insert, not_or] at hx
                simp [hf_s x hx.2, hδ_supp x (by simp [hx.1, hx.2])],
              fun w => by
                simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hf_f w, hδ_flow w]⟩
          invFun := fun ⟨f, hf_s, hf_f⟩ =>
            ⟨⟨fun x => f x - f e * δ x,
              fun x hx => by
                by_cases hxe : x = e
                · subst hxe; simp [hδ_e]
                · have hx' : x ∉ insert e A := by simp [hxe, hx]
                  simp [hf_s x hx', hδ_supp x hx'],
              fun w => by
                simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hf_f w, hδ_flow w]⟩,
              f e⟩
          left_inv := fun ⟨⟨f, hf_s, _⟩, c⟩ => by
            have hfe : f e = 0 := hf_s e he
            have hval : f e + c * δ e = c := by rw [hfe, hδ_e]; ring
            refine Prod.ext (Subtype.ext (funext (fun x => ?_))) hval
            change f x + c * δ x - (f e + c * δ e) * δ x = f x
            rw [hval]
            ring
          right_inv := fun ⟨f, _, _⟩ => by
            refine Subtype.ext (funext (fun x => ?_))
            change f x - f e * δ x + f e * δ x = f x
            ring }
      have hz : Nat.card (ZMod k) = k := by
        rw [Nat.card_eq_fintype_card, ZMod.card]
      rw [← Nat.card_congr eqv, Nat.card_prod, hz]
    · rw [nullity_insert_of_not_rel src tgt he hrel, ← ih]
      have hzero : ∀ f : SuppFlow src tgt (insert e A) k, f.1 e = 0 := by
        rintro ⟨f, hf_s, hf_f⟩
        let C : Finset V := Finset.univ.filter (fun w => EdgeRel src tgt A (src e) w)
        have hsum0 : ∑ w ∈ C, ((∑ x ∈ Finset.univ.filter (fun x => tgt x = w), f x) -
            (∑ x ∈ Finset.univ.filter (fun x => src x = w), f x)) = 0 :=
          Finset.sum_eq_zero (fun w _ => sub_eq_zero.mpr (hf_f w))
        rw [sum_flow_balance] at hsum0
        have hterm : ∀ x : E,
            (if tgt x ∈ C then f x else 0) - (if src x ∈ C then f x else 0) =
            if x = e then -f e else 0 := by
          intro x
          by_cases hxe : x = e
          · subst hxe
            have hsrc : src x ∈ C := by simp [C, edgeRel_refl]
            have htgt : tgt x ∉ C := by simp [C, hrel]
            simp [hsrc, htgt]
          · simp only [hxe, ↓reduceIte]
            by_cases hxA : x ∈ A
            · have hiff : tgt x ∈ C ↔ src x ∈ C := by
                simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro ht
                  exact edgeRel_trans src tgt ht
                    (Relation.ReflTransGen.single ⟨x, hxA, Or.inr ⟨rfl, rfl⟩⟩)
                · intro hs
                  exact edgeRel_trans src tgt hs
                    (Relation.ReflTransGen.single ⟨x, hxA, Or.inl ⟨rfl, rfl⟩⟩)
              by_cases h : src x ∈ C
              · simp [h, hiff.mpr h]
              · simp [h, mt hiff.mp h]
            · have hx' : x ∉ insert e A := by simp [hxe, hxA]
              simp [hf_s x hx']
        simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum0
        exact neg_eq_zero.mp hsum0
      let eqv : SuppFlow src tgt (insert e A) k ≃ SuppFlow src tgt A k :=
        { toFun := fun f => ⟨f.1, fun x hx => by
            by_cases hxe : x = e
            · exact hxe ▸ hzero f
            · exact f.2.1 x (by simp [hxe, hx]), f.2.2⟩
          invFun := fun f => ⟨f.1, fun x hx =>
            f.2.1 x (fun hxA => hx (Finset.mem_insert_of_mem hxA)), f.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Nat.card_congr eqv

private lemma sum_powerset_neg_one_pow {α : Type*} [DecidableEq α] (S : Finset α) :
    ∑ B ∈ S.powerset, (-1 : ℤ) ^ B.card = if S = ∅ then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · have hcard : ∀ B ∈ S.powerset, (-1 : ℤ) ^ (insert a B).card = -((-1 : ℤ) ^ B.card) := by
          intro B hB
          have haB : a ∉ B := fun h => ha (Finset.mem_powerset.mp hB h)
          rw [Finset.card_insert_of_notMem haB, pow_succ]
          ring
        rw [Finset.sum_congr rfl hcard, Finset.sum_neg_distrib, add_neg_cancel]
        simp [Finset.insert_ne_empty]
      · intro B1 hB1 B2 hB2 heq
        have ha1 : a ∉ B1 := fun h => ha (Finset.mem_powerset.mp hB1 h)
        have ha2 : a ∉ B2 := fun h => ha (Finset.mem_powerset.mp hB2 h)
        have := congrArg (fun T => T.erase a) heq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
    · rw [Finset.disjoint_left]
      intro B hB1 hB2
      rcases Finset.mem_image.mp hB2 with ⟨B', _, rfl⟩
      exact ha (Finset.mem_powerset.mp hB1 (Finset.mem_insert_self a B'))

private lemma nzFlowCount_eq_sum_int [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (k : ℕ) (hk : 1 ≤ k) :
    (nzFlowCount src tgt k : ℤ) =
      ∑ A : Finset E, (-1 : ℤ) ^ (Fintype.card E - A.card) * (k : ℤ) ^ (nullity src tgt A) := by
  classical
  have : NeZero k := ⟨by omega⟩
  let AllFlows := {f : E → ZMod k // IsFlow src tgt f}
  have h1 : ∀ A : Finset E, (k : ℤ) ^ (nullity src tgt A) =
      ∑ f : AllFlows, if (∀ e, f.1 e ≠ 0 → e ∈ A) then (1 : ℤ) else 0 := by
    intro A
    have hcard := card_suppFlow_eq_pow_nullity src tgt A k
    have hbij : SuppFlow src tgt A k ≃ {f : AllFlows // ∀ e, f.1 e ≠ 0 → e ∈ A} :=
      { toFun := fun ⟨f, hs, hf⟩ => ⟨⟨f, hf⟩, fun e hne => by_contra (fun h => hne (hs e h))⟩
        invFun := fun ⟨⟨f, hf⟩, hs⟩ => ⟨f, fun e hnot => by_contra (fun hne => hnot (hs e hne)), hf⟩
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    have hnat : k ^ nullity src tgt A =
        (Finset.univ.filter (fun f : AllFlows => ∀ e, f.1 e ≠ 0 → e ∈ A)).card := by
      rw [← hcard, Nat.card_congr hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hint : ((k : ℤ) ^ nullity src tgt A) =
        ((Finset.univ.filter (fun f : AllFlows => ∀ e, f.1 e ≠ 0 → e ∈ A)).card : ℤ) := by
      exact_mod_cast hnat
    rw [hint, Finset.card_filter]
    push_cast
    rfl
  symm
  calc ∑ A : Finset E, (-1 : ℤ) ^ (Fintype.card E - A.card) * (k : ℤ) ^ (nullity src tgt A)
      = ∑ A : Finset E, ∑ f : AllFlows,
          if (∀ e, f.1 e ≠ 0 → e ∈ A) then (-1 : ℤ) ^ (Fintype.card E - A.card) else 0 := by
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [h1 A, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun f _ => by split_ifs <;> ring)
    _ = ∑ f : AllFlows, ∑ A : Finset E,
          if (∀ e, f.1 e ≠ 0 → e ∈ A) then (-1 : ℤ) ^ (Fintype.card E - A.card) else 0 :=
        Finset.sum_comm
    _ = ∑ f : AllFlows, if (∀ e, f.1 e ≠ 0) then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        let Z : Finset E := Finset.univ.filter (fun e => f.1 e = 0)
        rw [← Finset.sum_filter]
        have hbij : ∑ A ∈ Finset.univ.filter (fun A : Finset E => ∀ e, f.1 e ≠ 0 → e ∈ A),
              (-1 : ℤ) ^ (Fintype.card E - A.card) =
            ∑ B ∈ Z.powerset, (-1 : ℤ) ^ B.card := by
          refine Finset.sum_bij (fun A _ => Finset.univ \ A) ?_ ?_ ?_ ?_
          · intro A hA
            rw [Finset.mem_filter] at hA
            rw [Finset.mem_powerset]
            intro e he
            rw [Finset.mem_sdiff] at he
            simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
            exact by_contra (fun hne => he.2 (hA.2 e hne))
          · intro A1 _ A2 _ heq
            ext e
            have := Finset.ext_iff.mp heq e
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
            tauto
          · intro B hB
            refine ⟨Finset.univ \ B, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, fun e hne => ?_⟩
              rw [Finset.mem_sdiff]
              refine ⟨Finset.mem_univ _, fun heB => ?_⟩
              have heZ := Finset.mem_powerset.mp hB heB
              simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at heZ
              exact hne heZ
            · ext e; simp
          · intro A _
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A), Finset.card_univ]
        rw [hbij, sum_powerset_neg_one_pow]
        have hZ : Z = ∅ ↔ ∀ e, f.1 e ≠ 0 := by
          simp [Z, Finset.eq_empty_iff_forall_notMem]
        by_cases hnz : ∀ e, f.1 e ≠ 0
        · simp [hZ.mpr hnz, hnz]
        · simp [mt hZ.mp hnz, hnz]
    _ = (nzFlowCount src tgt k : ℤ) := by
        unfold nzFlowCount
        have hbij : {f : E → ZMod k // (∀ e, f e ≠ 0) ∧
              ∀ v : V, (∑ e ∈ @Finset.filter E (fun e => tgt e = v) (Classical.decPred _) Finset.univ, f e) =
                ∑ e ∈ @Finset.filter E (fun e => src e = v) (Classical.decPred _) Finset.univ, f e} ≃
            {f : AllFlows // ∀ e, f.1 e ≠ 0} :=
          { toFun := fun ⟨f, hnz, hf⟩ => ⟨⟨f, fun v => by convert hf v⟩, hnz⟩
            invFun := fun ⟨⟨f, hf⟩, hnz⟩ => ⟨f, hnz, fun v => by convert hf v⟩
            left_inv := fun ⟨_, _, _⟩ => rfl
            right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        have hnat : Nat.card {f : E → ZMod k // (∀ e, f e ≠ 0) ∧
              ∀ v : V, (∑ e ∈ @Finset.filter E (fun e => tgt e = v) (Classical.decPred _) Finset.univ, f e) =
                ∑ e ∈ @Finset.filter E (fun e => src e = v) (Classical.decPred _) Finset.univ, f e} =
            (Finset.univ.filter (fun f : AllFlows => ∀ e, f.1 e ≠ 0)).card := by
          rw [Nat.card_congr hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
        have hcard_eq : (∑ f : AllFlows, if ∀ e : E, f.1 e ≠ 0 then (1 : ℤ) else 0) =
            ((Finset.univ.filter (fun f : AllFlows => ∀ e, f.1 e ≠ 0)).card : ℤ) := by
          rw [Finset.card_filter]; push_cast; rfl
        rw [hcard_eq, ← hnat]

private noncomputable def flowPoly [Fintype V] [Fintype E] : Polynomial ℝ :=
  ∑ A : Finset E, Polynomial.C ((-1 : ℝ) ^ (Fintype.card E - A.card)) *
    Polynomial.X ^ (nullity src tgt A)

private lemma flowPoly_eval_nat [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (k : ℕ) (hk : 1 ≤ k) :
    (flowPoly src tgt).eval (k : ℝ) = (nzFlowCount src tgt k : ℝ) := by
  have hint := nzFlowCount_eq_sum_int src tgt k hk
  have hreal : (nzFlowCount src tgt k : ℝ) =
      ∑ A : Finset E, (-1 : ℝ) ^ (Fintype.card E - A.card) * (k : ℝ) ^ (nullity src tgt A) := by
    exact_mod_cast hint
  rw [hreal, flowPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

private lemma scaled_flowPoly_eval [Fintype V] [Fintype E] (a b : ℤ) (hb : (b : ℝ) ≠ 0) :
    (b : ℝ) ^ (Fintype.card E) * (flowPoly src tgt).eval ((a : ℝ) / (b : ℝ)) =
    ((∑ A : Finset E,
      (-b) ^ (Fintype.card E - A.card) * b ^ (A.card - nullity src tgt A) *
      a ^ (nullity src tgt A) : ℤ) : ℝ) := by
  rw [flowPoly, Polynomial.eval_finsetSum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun A _ => ?_)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hle1 : A.card ≤ Fintype.card E := Finset.card_le_univ A
  have hle2 : nullity src tgt A ≤ A.card := nullity_le_card src tgt A
  have h1 : Fintype.card E - A.card + (A.card - nullity src tgt A) + nullity src tgt A =
      Fintype.card E := by omega
  have hpow : (b : ℝ) ^ (Fintype.card E) =
      (b : ℝ) ^ (Fintype.card E - A.card) * (b : ℝ) ^ (A.card - nullity src tgt A) *
      (b : ℝ) ^ (nullity src tgt A) := by
    rw [← pow_add, ← pow_add, h1]
  rw [hpow, div_pow]
  have hbn : (b : ℝ) ^ (nullity src tgt A) ≠ 0 := pow_ne_zero _ hb
  have hneg : (-(b : ℝ)) ^ (Fintype.card E - A.card) =
      (-1 : ℝ) ^ (Fintype.card E - A.card) * (b : ℝ) ^ (Fintype.card E - A.card) := by
    rw [← mul_pow]; ring_nf
  rw [hneg]
  field_simp [hbn]

end TutteFormula

-- =========================================================================
-- Part 2: Recursive Edge-List Flow Sum & Equivalence with Scaled Flow Poly
-- =========================================================================

private def mergeRel (R : ℕ → ℕ → Prop) (u v : ℕ) (x y : ℕ) : Prop :=
  R x y ∨ (R x u ∧ R v y) ∨ (R x v ∧ R u y)

private lemma mergeRel_equiv {R : ℕ → ℕ → Prop} (hR : Equivalence R) (u v : ℕ) :
    Equivalence (mergeRel R u v) where
  refl x := Or.inl (hR.refl x)
  symm := by
    rintro x y (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (hR.symm h)
    · exact Or.inr (Or.inr ⟨hR.symm h2, hR.symm h1⟩)
    · exact Or.inr (Or.inl ⟨hR.symm h2, hR.symm h1⟩)
  trans := by
    rintro x y z (hxy | ⟨h1, h2⟩ | ⟨h1, h2⟩) (hyz | ⟨h3, h4⟩ | ⟨h3, h4⟩)
    · exact Or.inl (hR.trans hxy hyz)
    · exact Or.inr (Or.inl ⟨hR.trans hxy h3, h4⟩)
    · exact Or.inr (Or.inr ⟨hR.trans hxy h3, h4⟩)
    · exact Or.inr (Or.inl ⟨h1, hR.trans h2 hyz⟩)
    · exact Or.inr (Or.inl ⟨h1, h4⟩)
    · exact Or.inl (hR.trans h1 h4)
    · exact Or.inr (Or.inr ⟨h1, hR.trans h2 hyz⟩)
    · exact Or.inl (hR.trans h1 h4)
    · exact Or.inr (Or.inr ⟨h1, h4⟩)

private noncomputable def listFlowSum (a b : ℤ) (R : ℕ → ℕ → Prop) : List (ℕ × ℕ) → ℤ
  | [] => 1
  | (u, v) :: rest =>
    letI := Classical.propDecidable (R u v)
    (-b) * listFlowSum a b R rest +
    if R u v then a * listFlowSum a b R rest
    else b * listFlowSum a b (mergeRel R u v) rest

private def appearsIn (x : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | (u, v) :: rest => Nat.beq u x || Nat.beq v x || appearsIn x rest

private lemma appearsIn_iff (x : ℕ) (es : List (ℕ × ℕ)) :
    appearsIn x es = true ↔ ∃ p ∈ es, p.1 = x ∨ p.2 = x := by
  induction es with
  | nil => simp [appearsIn]
  | cons p rest ih =>
    rcases p with ⟨u, v⟩
    simp only [appearsIn, Bool.or_eq_true, Nat.beq_eq, ih, List.mem_cons, exists_eq_or_imp]

private lemma listFlowSum_congr (a b : ℤ) {R₁ R₂ : ℕ → ℕ → Prop} (es : List (ℕ × ℕ))
    (h : ∀ x y, appearsIn x es = true → appearsIn y es = true → (R₁ x y ↔ R₂ x y)) :
    listFlowSum a b R₁ es = listFlowSum a b R₂ es := by
  induction es generalizing R₁ R₂ with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨u, v⟩
    have hu : appearsIn u ((u, v) :: rest) = true := by simp [appearsIn]
    have hv : appearsIn v ((u, v) :: rest) = true := by simp [appearsIn]
    have hsub : ∀ x, appearsIn x rest = true → appearsIn x ((u, v) :: rest) = true := by
      intro x hx; simp [appearsIn, hx]
    have huv : R₁ u v ↔ R₂ u v := h u v hu hv
    have ih1 : listFlowSum a b R₁ rest = listFlowSum a b R₂ rest :=
      ih (fun x y hx hy => h x y (hsub x hx) (hsub y hy))
    have ih2 : listFlowSum a b (mergeRel R₁ u v) rest = listFlowSum a b (mergeRel R₂ u v) rest := by
      apply ih
      intro x y hx hy
      have hxy := h x y (hsub x hx) (hsub y hy)
      have hxu := h x u (hsub x hx) hu
      have hvy := h v y hv (hsub y hy)
      have hxv := h x v (hsub x hx) hv
      have huy := h u y hu (hsub y hy)
      simp only [mergeRel, hxy, hxu, hvy, hxv, huy]
    unfold listFlowSum
    by_cases h1 : R₁ u v
    · have h2 : R₂ u v := huv.mp h1
      simp only [h1, h2, ↓reduceIte, ih1]
    · have h2 : ¬ R₂ u v := mt huv.mpr h1
      simp only [h1, h2, ↓reduceIte, ih1, ih2]

-- Generalized relation-based edge closure on Fin N
section RelFinSum

private def ListEdgesLt (N : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ es, p.1 < N ∧ p.2 < N

private def ExtStep (R₀ : ℕ → ℕ → Prop) (es : List (ℕ × ℕ)) (A : Finset (Fin es.length))
    (x y : Fin N) : Prop :=
  R₀ x.val y.val ∨
  ∃ e ∈ A, ((es.get e).1 = x.val ∧ (es.get e).2 = y.val) ∨
           ((es.get e).1 = y.val ∧ (es.get e).2 = x.val)

private def ExtRel (N : ℕ) (R₀ : ℕ → ℕ → Prop) (es : List (ℕ × ℕ)) (A : Finset (Fin es.length)) :
    Fin N → Fin N → Prop :=
  Relation.ReflTransGen (ExtStep R₀ es A)

private lemma extStep_symm {N : ℕ} {R₀ : ℕ → ℕ → Prop} (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (A : Finset (Fin es.length)) {x y : Fin N}
    (h : ExtStep R₀ es A x y) : ExtStep R₀ es A y x := by
  rcases h with h0 | ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact Or.inl (hR.symm h0)
  · exact Or.inr ⟨e, he, Or.inr ⟨h1, h2⟩⟩
  · exact Or.inr ⟨e, he, Or.inl ⟨h1, h2⟩⟩

private def extSetoid (N : ℕ) (R₀ : ℕ → ℕ → Prop) (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (A : Finset (Fin es.length)) : Setoid (Fin N) where
  r := ExtRel N R₀ es A
  iseqv :=
    ⟨fun _ => Relation.ReflTransGen.refl,
     fun h => by
       induction h with
       | refl => exact Relation.ReflTransGen.refl
       | tail _ hs ih => exact Relation.ReflTransGen.head (extStep_symm hR es A hs) ih,
     fun h1 h2 => Relation.ReflTransGen.trans h1 h2⟩

private noncomputable def extCompCount (N : ℕ) (R₀ : ℕ → ℕ → Prop) (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (A : Finset (Fin es.length)) : ℕ :=
  letI := Classical.decRel (extSetoid N R₀ hR es A).r
  Fintype.card (Quotient (extSetoid N R₀ hR es A))

private lemma extRel_empty_iff {N : ℕ} {R₀ : ℕ → ℕ → Prop} (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (x y : Fin N) :
    ExtRel N R₀ es ∅ x y ↔ R₀ x.val y.val := by
  constructor
  · intro h
    induction h with
    | refl => exact hR.refl _
    | tail _ hs ih =>
      rcases hs with h0 | ⟨e, he, _⟩
      · exact hR.trans ih h0
      · exact absurd he (Finset.notMem_empty e)
  · intro h
    exact Relation.ReflTransGen.single (Or.inl h)

private lemma extRel_cons_notMem {N : ℕ} (R₀ : ℕ → ℕ → Prop) (e0 : ℕ × ℕ) (rest : List (ℕ × ℕ))
    (A' : Finset (Fin rest.length)) (x y : Fin N) :
    ExtRel N R₀ (e0 :: rest) (A'.map ⟨Fin.succ, Fin.succ_injective _⟩) x y ↔
      ExtRel N R₀ rest A' x y := by
  have hstep : ∀ a b : Fin N,
      ExtStep R₀ (e0 :: rest) (A'.map ⟨Fin.succ, Fin.succ_injective _⟩) a b ↔
        ExtStep R₀ rest A' a b := by
    intro a b
    simp only [ExtStep, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro (h | ⟨e, ⟨i, hi, rfl⟩, hst⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, hst⟩
    · rintro (h | ⟨i, hi, hst⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i.succ, ⟨i, hi, rfl⟩, hst⟩
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact Relation.ReflTransGen.tail ih ((hstep _ _).mp hs)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact Relation.ReflTransGen.tail ih ((hstep _ _).mpr hs)

private lemma extRel_cons_mem {N : ℕ} {R₀ : ℕ → ℕ → Prop} (hR : Equivalence R₀)
    (u v : ℕ) (hu : u < N) (hv : v < N) (rest : List (ℕ × ℕ))
    (A' : Finset (Fin rest.length)) (x y : Fin N) :
    ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) x y ↔
      ExtRel N (mergeRel R₀ u v) rest A' x y := by
  let uF : Fin N := ⟨u, hu⟩
  let vF : Fin N := ⟨v, hv⟩
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine Relation.ReflTransGen.trans ih ?_
      rcases hbc with h0 | ⟨e, he, hst⟩
      · exact Relation.ReflTransGen.single (Or.inl (Or.inl h0))
      · rcases Finset.mem_insert.mp he with rfl | hm
        · rcases hst with ⟨hb, hc⟩ | ⟨hb, hc⟩
          · exact Relation.ReflTransGen.single (Or.inl (Or.inr (Or.inl ⟨hb ▸ hR.refl _, hc ▸ hR.refl _⟩)))
          · exact Relation.ReflTransGen.single (Or.inl (Or.inr (Or.inr ⟨hc ▸ hR.refl _, hb ▸ hR.refl _⟩)))
        · rcases Finset.mem_map.mp hm with ⟨i, hi, rfl⟩
          exact Relation.ReflTransGen.single (Or.inr ⟨i, hi, hst⟩)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine Relation.ReflTransGen.trans ih ?_
      rcases hbc with (h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨i, hi, hst⟩
      · exact Relation.ReflTransGen.single (Or.inl h0)
      · have hbu : ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) b uF :=
          Relation.ReflTransGen.single (Or.inl h1)
        have huv : ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) uF vF :=
          Relation.ReflTransGen.single (Or.inr ⟨0, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩)
        have hvc : ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) vF c :=
          Relation.ReflTransGen.single (Or.inl h2)
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans hbu huv) hvc
      · have hbv : ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) b vF :=
          Relation.ReflTransGen.single (Or.inl h1)
        have hvu : ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) vF uF :=
          Relation.ReflTransGen.single (Or.inr ⟨0, Finset.mem_insert_self _ _, Or.inr ⟨rfl, rfl⟩⟩)
        have huc : ExtRel N R₀ ((u, v) :: rest) (insert 0 (A'.map ⟨Fin.succ, Fin.succ_injective _⟩)) uF c :=
          Relation.ReflTransGen.single (Or.inl h2)
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans hbv hvu) huc
      · exact Relation.ReflTransGen.single
          (Or.inr ⟨i.succ, Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨i, hi, rfl⟩), hst⟩)

private lemma extCompCount_congr {N : ℕ} {R₁ R₂ : ℕ → ℕ → Prop}
    (h1 : Equivalence R₁) (h2 : Equivalence R₂)
    (es₁ es₂ : List (ℕ × ℕ)) (A₁ : Finset (Fin es₁.length)) (A₂ : Finset (Fin es₂.length))
    (hiff : ∀ x y : Fin N, ExtRel N R₁ es₁ A₁ x y ↔ ExtRel N R₂ es₂ A₂ x y) :
    extCompCount N R₁ h1 es₁ A₁ = extCompCount N R₂ h2 es₂ A₂ := by
  classical
  unfold extCompCount
  let eqv : Quotient (extSetoid N R₁ h1 es₁ A₁) ≃ Quotient (extSetoid N R₂ h2 es₂ A₂) :=
    { toFun := Quotient.lift (Quotient.mk _) (fun a b hab => Quotient.sound ((hiff a b).mp hab))
      invFun := Quotient.lift (Quotient.mk _) (fun a b hab => Quotient.sound ((hiff a b).mpr hab))
      left_inv := fun q => Quotient.inductionOn q (fun _ => rfl)
      right_inv := fun q => Quotient.inductionOn q (fun _ => rfl) }
  exact Fintype.card_congr eqv

private lemma extCompCount_empty_merge {N : ℕ} {R₀ : ℕ → ℕ → Prop} (hR : Equivalence R₀)
    (u v : ℕ) (hu : u < N) (hv : v < N) (hnot : ¬ R₀ u v)
    (es₁ es₂ : List (ℕ × ℕ)) :
    extCompCount N (mergeRel R₀ u v) (mergeRel_equiv hR u v) es₂ ∅ + 1 =
      extCompCount N R₀ hR es₁ ∅ := by
  classical
  unfold extCompCount
  let sA := extSetoid N R₀ hR es₁ ∅
  let sB := extSetoid N (mergeRel R₀ u v) (mergeRel_equiv hR u v) es₂ ∅
  let uF : Fin N := ⟨u, hu⟩
  let vF : Fin N := ⟨v, hv⟩
  let qu : Quotient sA := Quotient.mk sA uF
  let qv : Quotient sA := Quotient.mk sA vF
  have hne : qu ≠ qv := fun h => hnot ((extRel_empty_iff hR es₁ uF vF).mp (Quotient.exact h))
  let toB : {q : Quotient sA // q ≠ qv} → Quotient sB :=
    fun q => Quotient.liftOn q.1 (Quotient.mk sB) (fun a b hab => by
      apply Quotient.sound
      exact (extRel_empty_iff (mergeRel_equiv hR u v) es₂ a b).mpr
        (Or.inl ((extRel_empty_iff hR es₁ a b).mp hab)))
  have hsurj : Function.Surjective toB := by
    intro qb
    refine Quotient.inductionOn qb (fun x => ?_)
    by_cases hx : Quotient.mk sA x = qv
    · refine ⟨⟨qu, hne⟩, ?_⟩
      change Quotient.mk sB uF = Quotient.mk sB x
      apply Quotient.sound
      have hxv : R₀ x.val v := (extRel_empty_iff hR es₁ x vF).mp (Quotient.exact hx)
      exact (extRel_empty_iff (mergeRel_equiv hR u v) es₂ uF x).mpr
        (Or.inr (Or.inl ⟨hR.refl _, hR.symm hxv⟩))
    · exact ⟨⟨Quotient.mk sA x, hx⟩, rfl⟩
  have hinj : Function.Injective toB := by
    rintro ⟨q1, hq1⟩ ⟨q2, hq2⟩ heq
    apply Subtype.ext
    refine Quotient.inductionOn₂ q1 q2 (fun a b hq1 hq2 heq => ?_) hq1 hq2 heq
    have hab : mergeRel R₀ u v a.val b.val :=
      (extRel_empty_iff (mergeRel_equiv hR u v) es₂ a b).mp (Quotient.exact heq)
    rcases hab with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Quotient.sound ((extRel_empty_iff hR es₁ a b).mpr h)
    · exfalso; exact hq2 (Quotient.sound ((extRel_empty_iff hR es₁ b vF).mpr (hR.symm h2)))
    · exfalso; exact hq1 (Quotient.sound ((extRel_empty_iff hR es₁ a vF).mpr h1))
  have hcard1 : Fintype.card {q : Quotient sA // q ≠ qv} = Fintype.card (Quotient sB) :=
    Fintype.card_of_bijective ⟨hinj, hsurj⟩
  have hcard2 : Fintype.card {q : Quotient sA // q ≠ qv} + 1 = Fintype.card (Quotient sA) := by
    have hc : Fintype.card {q : Quotient sA // q ≠ qv} =
        Fintype.card (Quotient sA) - Fintype.card {q : Quotient sA // q = qv} :=
      Fintype.card_subtype_compl (fun q => q = qv)
    rw [hc, Fintype.card_subtype_eq]
    have hpos : 0 < Fintype.card (Quotient sA) := Fintype.card_pos_iff.mpr ⟨qv⟩
    omega
  change Fintype.card (Quotient sB) + 1 = Fintype.card (Quotient sA)
  omega

private lemma extCompCount_le_empty {N : ℕ} {R₀ : ℕ → ℕ → Prop} (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (A : Finset (Fin es.length)) :
    extCompCount N R₀ hR es A ≤ extCompCount N R₀ hR es ∅ := by
  classical
  unfold extCompCount
  let f : Quotient (extSetoid N R₀ hR es ∅) → Quotient (extSetoid N R₀ hR es A) :=
    Quotient.lift (Quotient.mk _) (fun a b hab => by
      apply Quotient.sound
      have h0 : R₀ a.val b.val := (extRel_empty_iff hR es a b).mp hab
      exact Relation.ReflTransGen.single (Or.inl h0))
  have hsurj : Function.Surjective f := fun q =>
    Quotient.inductionOn q (fun x => ⟨Quotient.mk _ x, rfl⟩)
  exact Fintype.card_le_of_surjective f hsurj

private lemma extCompCount_empty_le_add {N : ℕ} {R₀ : ℕ → ℕ → Prop} (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (hlt : ListEdgesLt N es) (A : Finset (Fin es.length)) :
    extCompCount N R₀ hR es ∅ ≤ A.card + extCompCount N R₀ hR es A := by
  classical
  induction es generalizing R₀ with
  | nil =>
    have hA : A = ∅ := by ext i; exact Fin.elim0 i
    subst hA
    simp
  | cons e0 rest ih =>
    rcases e0 with ⟨u, v⟩
    have huv : u < N ∧ v < N := hlt (u, v) (List.mem_cons_self ..)
    have hrest : ListEdgesLt N rest := fun p hp => hlt p (List.mem_cons_of_mem _ hp)
    let emb : Fin rest.length ↪ Fin (rest.length + 1) := ⟨Fin.succ, Fin.succ_injective _⟩
    let A' : Finset (Fin rest.length) := A.preimage Fin.succ (fun x _ y _ h => Fin.succ_injective _ h)
    by_cases h0 : (0 : Fin (rest.length + 1)) ∈ A
    · have hAeq : A = insert 0 (A'.map emb) := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [h0, emb]
        · intro j; simp only [Finset.mem_insert, Fin.succ_ne_zero, false_or, Finset.mem_map,
            emb, Function.Embedding.coeFn_mk, Fin.succ_inj, exists_eq_right]
          exact Finset.mem_preimage.symm
      have h0not : (0 : Fin (rest.length + 1)) ∉ A'.map emb := by simp [emb]
      have hcard : A.card = A'.card + 1 := by
        rw [hAeq, Finset.card_insert_of_notMem h0not, Finset.card_map]
      rw [hcard]
      have hceq : extCompCount N R₀ hR ((u, v) :: rest) A =
          extCompCount N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest A' := by
        rw [hAeq]
        exact extCompCount_congr hR (mergeRel_equiv hR u v) _ _ _ _
          (extRel_cons_mem hR u v huv.1 huv.2 rest A')
      rw [hceq]
      by_cases hrel : R₀ u v
      · have hmerge_iff : ∀ x y, mergeRel R₀ u v x y ↔ R₀ x y := by
          intro x y; unfold mergeRel; constructor
          · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact h
            · exact hR.trans (hR.trans h1 hrel) h2
            · exact hR.trans (hR.trans h1 (hR.symm hrel)) h2
          · exact Or.inl
        have he0 : extCompCount N R₀ hR ((u, v) :: rest) ∅ =
            extCompCount N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest ∅ :=
          extCompCount_congr hR (mergeRel_equiv hR u v) _ _ ∅ ∅ (fun x y => by
            rw [extRel_empty_iff hR, extRel_empty_iff (mergeRel_equiv hR u v), hmerge_iff])
        have hih := ih (mergeRel_equiv hR u v) hrest A'
        omega
      · have he0 := extCompCount_empty_merge hR u v huv.1 huv.2 hrel ((u, v) :: rest) rest
        have hih := ih (mergeRel_equiv hR u v) hrest A'
        omega
    · have hAeq : A = A'.map emb := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [h0, emb]
        · intro j; simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk, Fin.succ_inj, exists_eq_right]
          exact Finset.mem_preimage.symm
      have hcard : A.card = A'.card := by rw [hAeq, Finset.card_map]
      have hceq : extCompCount N R₀ hR ((u, v) :: rest) A = extCompCount N R₀ hR rest A' := by
        rw [hAeq]
        exact extCompCount_congr hR hR _ _ _ _ (extRel_cons_notMem R₀ (u, v) rest A')
      have he0 : extCompCount N R₀ hR ((u, v) :: rest) ∅ = extCompCount N R₀ hR rest ∅ :=
        extCompCount_congr hR hR _ _ ∅ ∅ (fun x y => by rw [extRel_empty_iff hR, extRel_empty_iff hR])
      rw [hcard, hceq, he0]
      exact ih hR hrest A'

private noncomputable def extNullity (N : ℕ) (R₀ : ℕ → ℕ → Prop) (hR : Equivalence R₀)
    (es : List (ℕ × ℕ)) (A : Finset (Fin es.length)) : ℕ :=
  A.card + extCompCount N R₀ hR es A - extCompCount N R₀ hR es ∅

private lemma listFlowSum_eq_extSum (a b : ℤ) (N : ℕ) (es : List (ℕ × ℕ)) (hlt : ListEdgesLt N es)
    (R₀ : ℕ → ℕ → Prop) (hR : Equivalence R₀) :
    listFlowSum a b R₀ es =
      ∑ A : Finset (Fin es.length),
        (-b) ^ (es.length - A.card) *
        b ^ (A.card - extNullity N R₀ hR es A) *
        a ^ (extNullity N R₀ hR es A) := by
  classical
  induction es generalizing R₀ with
  | nil =>
    have huniv : (Finset.univ : Finset (Finset (Fin (([] : List (ℕ × ℕ)).length)))) = {∅} := by
      ext A
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      ext i
      exact Fin.elim0 i
    rw [huniv, Finset.sum_singleton]
    simp [listFlowSum, extNullity]
  | cons e0 rest ih =>
    rcases e0 with ⟨u, v⟩
    have huv : u < N ∧ v < N := hlt (u, v) (List.mem_cons_self ..)
    have hrest : ListEdgesLt N rest := fun p hp => hlt p (List.mem_cons_of_mem _ hp)
    let emb : Fin rest.length ↪ Fin (rest.length + 1) := ⟨Fin.succ, Fin.succ_injective _⟩
    let S0 : Finset (Finset (Fin (rest.length + 1))) :=
      Finset.univ.filter (fun A => (0 : Fin (rest.length + 1)) ∉ A)
    let S1 : Finset (Finset (Fin (rest.length + 1))) :=
      Finset.univ.filter (fun A => (0 : Fin (rest.length + 1)) ∈ A)
    have hsplit : (∑ A : Finset (Fin (rest.length + 1)),
        (-b) ^ (rest.length + 1 - A.card) *
        b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
        a ^ (extNullity N R₀ hR ((u, v) :: rest) A)) =
      (∑ A ∈ S0, (-b) ^ (rest.length + 1 - A.card) *
        b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
        a ^ (extNullity N R₀ hR ((u, v) :: rest) A)) +
      (∑ A ∈ S1, (-b) ^ (rest.length + 1 - A.card) *
        b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
        a ^ (extNullity N R₀ hR ((u, v) :: rest) A)) := by
      rw [← Finset.sum_union]
      · congr 1; ext A; simp [S0, S1]; tauto
      · rw [Finset.disjoint_left]; intro A hA0 hA1
        simp only [S0, S1, Finset.mem_filter] at hA0 hA1; exact hA0.2 hA1.2
    -- Sum over S0 equals (-b) * listFlowSum a b R₀ rest
    have hS0 : (∑ A ∈ S0, (-b) ^ (rest.length + 1 - A.card) *
        b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
        a ^ (extNullity N R₀ hR ((u, v) :: rest) A)) =
      (-b) * listFlowSum a b R₀ rest := by
      rw [ih hrest R₀ hR, Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun A' _ => A'.map emb) ?_ ?_ ?_ ?_
      · intro A' _; simp [S0, emb]
      · intro A1 _ A2 _ heq
        ext i; have := Finset.ext_iff.mp heq (emb i); simpa [emb] using this
      · intro A hA
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hA
        refine ⟨A.preimage Fin.succ (fun x _ y _ h => Fin.succ_injective _ h), Finset.mem_univ _, ?_⟩
        ext i; refine Fin.cases ?_ ?_ i
        · simp [hA, emb]
        · intro j; simp only [Finset.mem_map, emb, Function.Embedding.coeFn_mk, Fin.succ_inj, exists_eq_right]
          exact Finset.mem_preimage
      · intro A' _
        have hcard : (A'.map emb).card = A'.card := Finset.card_map emb
        have hle : A'.card ≤ rest.length := by
          have := Finset.card_le_univ A'; simpa using this
        have hsub : rest.length + 1 - A'.card = (rest.length - A'.card) + 1 := by omega
        have hn : extNullity N R₀ hR ((u, v) :: rest) (A'.map emb) = extNullity N R₀ hR rest A' := by
          unfold extNullity
          rw [hcard,
            extCompCount_congr hR hR _ _ _ _ (extRel_cons_notMem R₀ (u, v) rest A'),
            extCompCount_congr hR hR _ _ ∅ ∅ (fun x y => by simp only [extRel_empty_iff hR])]
        rw [hcard, hn, hsub, pow_succ]
        ring
    -- Sum over S1 equals (if R₀ u v then a * listFlowSum R₀ else b * listFlowSum (mergeRel R₀ u v))
    have hS1 : (∑ A ∈ S1, (-b) ^ (rest.length + 1 - A.card) *
        b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
        a ^ (extNullity N R₀ hR ((u, v) :: rest) A)) =
      (letI := Classical.propDecidable (R₀ u v)
       if R₀ u v then a * listFlowSum a b R₀ rest
       else b * listFlowSum a b (mergeRel R₀ u v) rest) := by
      have hS1_eq : ∀ (g : Finset (Fin rest.length) → ℤ),
          (∀ A' : Finset (Fin rest.length),
            let A := insert 0 (A'.map emb)
            (-b) ^ (rest.length + 1 - A.card) *
            b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
            a ^ (extNullity N R₀ hR ((u, v) :: rest) A) = g A') →
          (∑ A ∈ S1, (-b) ^ (rest.length + 1 - A.card) *
            b ^ (A.card - extNullity N R₀ hR ((u, v) :: rest) A) *
            a ^ (extNullity N R₀ hR ((u, v) :: rest) A)) = ∑ A' : Finset (Fin rest.length), g A' := by
        intro g hg
        symm
        refine Finset.sum_bij (fun A' _ => insert 0 (A'.map emb)) ?_ ?_ ?_ ?_
        · intro A' _; simp [S1]
        · intro A1 _ A2 _ heq
          ext i
          have := Finset.ext_iff.mp heq (emb i)
          have hne : emb i ≠ 0 := Fin.succ_ne_zero i
          simpa [emb, hne] using this
        · intro A hA
          simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hA
          refine ⟨A.preimage Fin.succ (fun x _ y _ h => Fin.succ_injective _ h), Finset.mem_univ _, ?_⟩
          ext i; refine Fin.cases ?_ ?_ i
          · simp [hA, emb]
          · intro j; simp only [Finset.mem_insert, Fin.succ_ne_zero, false_or, Finset.mem_map,
              emb, Function.Embedding.coeFn_mk, Fin.succ_inj, exists_eq_right]
            exact Finset.mem_preimage
        · intro A' _; exact (hg A').symm
      by_cases hrel : R₀ u v
      · simp only [hrel, ↓reduceIte]
        rw [ih hrest R₀ hR, Finset.mul_sum]
        apply hS1_eq
        intro A'
        dsimp only
        have h0not : (0 : Fin (rest.length + 1)) ∉ A'.map emb := by simp [emb]
        have hcard : (insert 0 (A'.map emb)).card = A'.card + 1 := by
          rw [Finset.card_insert_of_notMem h0not, Finset.card_map]
        have hmerge_iff : ∀ x y, mergeRel R₀ u v x y ↔ R₀ x y := by
          intro x y; unfold mergeRel; constructor
          · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact h
            · exact hR.trans (hR.trans h1 hrel) h2
            · exact hR.trans (hR.trans h1 (hR.symm hrel)) h2
          · exact Or.inl
        have hc1 : extCompCount N R₀ hR ((u, v) :: rest) (insert 0 (A'.map emb)) =
            extCompCount N R₀ hR rest A' := by
          trans extCompCount N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest A'
          · exact extCompCount_congr hR (mergeRel_equiv hR u v) _ _ _ _
              (extRel_cons_mem hR u v huv.1 huv.2 rest A')
          · exact extCompCount_congr (mergeRel_equiv hR u v) hR _ _ _ _ (fun x y => by
              constructor
              · intro h; induction h with
                | refl => exact Relation.ReflTransGen.refl
                | tail _ hs ih =>
                  rcases hs with h0 | h1
                  · exact Relation.ReflTransGen.tail ih (Or.inl ((hmerge_iff _ _).mp h0))
                  · exact Relation.ReflTransGen.tail ih (Or.inr h1)
              · intro h; induction h with
                | refl => exact Relation.ReflTransGen.refl
                | tail _ hs ih =>
                  rcases hs with h0 | h1
                  · exact Relation.ReflTransGen.tail ih (Or.inl ((hmerge_iff _ _).mpr h0))
                  · exact Relation.ReflTransGen.tail ih (Or.inr h1))
        have hc0 : extCompCount N R₀ hR ((u, v) :: rest) ∅ = extCompCount N R₀ hR rest ∅ :=
          extCompCount_congr hR hR _ _ ∅ ∅ (fun x y => by rw [extRel_empty_iff hR, extRel_empty_iff hR])
        have hle := extCompCount_empty_le_add hR rest hrest A'
        have hn : extNullity N R₀ hR ((u, v) :: rest) (insert 0 (A'.map emb)) =
            extNullity N R₀ hR rest A' + 1 := by
          unfold extNullity; rw [hcard, hc1, hc0]; omega
        rw [hcard, hn]
        have hsub1 : rest.length + 1 - (A'.card + 1) = rest.length - A'.card := by omega
        have hsub2 : A'.card + 1 - (extNullity N R₀ hR rest A' + 1) =
            A'.card - extNullity N R₀ hR rest A' := by omega
        rw [hsub1, hsub2, pow_succ]
        ring
      · simp only [hrel, ↓reduceIte]
        rw [ih hrest (mergeRel R₀ u v) (mergeRel_equiv hR u v), Finset.mul_sum]
        apply hS1_eq
        intro A'
        dsimp only
        have h0not : (0 : Fin (rest.length + 1)) ∉ A'.map emb := by simp [emb]
        have hcard : (insert 0 (A'.map emb)).card = A'.card + 1 := by
          rw [Finset.card_insert_of_notMem h0not, Finset.card_map]
        have hc1 : extCompCount N R₀ hR ((u, v) :: rest) (insert 0 (A'.map emb)) =
            extCompCount N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest A' :=
          extCompCount_congr hR (mergeRel_equiv hR u v) _ _ _ _
            (extRel_cons_mem hR u v huv.1 huv.2 rest A')
        have hc0 := extCompCount_empty_merge hR u v huv.1 huv.2 hrel ((u, v) :: rest) rest
        have hle := extCompCount_empty_le_add (mergeRel_equiv hR u v) rest hrest A'
        have hle2 := extCompCount_le_empty (N := N) (mergeRel_equiv hR u v) rest A'
        have hn : extNullity N R₀ hR ((u, v) :: rest) (insert 0 (A'.map emb)) =
            extNullity N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest A' := by
          unfold extNullity; rw [hcard, hc1]; omega
        rw [hcard, hn]
        have hsub1 : rest.length + 1 - (A'.card + 1) = rest.length - A'.card := by omega
        have hsub2 : A'.card + 1 - extNullity N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest A' =
            (A'.card - extNullity N (mergeRel R₀ u v) (mergeRel_equiv hR u v) rest A') + 1 := by
          unfold extNullity; omega
        rw [hsub1, hsub2, pow_succ]
        ring
    unfold listFlowSum
    simp only [List.length_cons]
    rw [hsplit, hS0, hS1]

private lemma listFlowSum_eq_scaled_flowPoly (a b : ℤ) (hb : (b : ℝ) ≠ 0)
    (N : ℕ) (es : List (ℕ × ℕ)) (hlt : ListEdgesLt N es) :
    let src : Fin es.length → Fin N := fun e => ⟨(es.get e).1, (hlt _ (List.get_mem es e)).1⟩
    let tgt : Fin es.length → Fin N := fun e => ⟨(es.get e).2, (hlt _ (List.get_mem es e)).2⟩
    (b : ℝ) ^ es.length * (flowPoly src tgt).eval ((a : ℝ) / (b : ℝ)) =
      (listFlowSum a b Eq es : ℝ) := by
  intro src tgt
  have h1 := scaled_flowPoly_eval src tgt a b hb
  rw [Fintype.card_fin] at h1
  rw [h1]
  congr 1
  rw [listFlowSum_eq_extSum a b N es hlt Eq ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  have hn : nullity src tgt A = extNullity N Eq ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ es A := by
    unfold nullity extNullity
    have hcA : compCount src tgt A = extCompCount N Eq ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ es A := by
      classical
      unfold compCount extCompCount
      have hiff : ∀ x y : Fin N, EdgeRel src tgt A x y ↔ ExtRel N Eq es A x y := by
        intro x y
        constructor
        · intro h
          induction h with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hs ih =>
            rcases hs with ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
            · exact Relation.ReflTransGen.tail ih
                (Or.inr ⟨e, he, Or.inl ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩⟩)
            · exact Relation.ReflTransGen.tail ih
                (Or.inr ⟨e, he, Or.inr ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩⟩)
        · intro h
          induction h with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hs ih =>
            rcases hs with h0 | ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
            · have heq : _ = _ := Fin.ext h0
              exact heq ▸ ih
            · exact Relation.ReflTransGen.tail ih
                (⟨e, he, Or.inl ⟨Fin.ext h1, Fin.ext h2⟩⟩)
            · exact Relation.ReflTransGen.tail ih
                (⟨e, he, Or.inr ⟨Fin.ext h1, Fin.ext h2⟩⟩)
      let eqv : Quotient (edgeSetoid src tgt A) ≃
          Quotient (extSetoid N Eq ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ es A) :=
        { toFun := Quotient.lift (Quotient.mk _) (fun a b hab => Quotient.sound ((hiff a b).mp hab))
          invFun := Quotient.lift (Quotient.mk _) (fun a b hab => Quotient.sound ((hiff a b).mpr hab))
          left_inv := fun q => Quotient.inductionOn q (fun _ => rfl)
          right_inv := fun q => Quotient.inductionOn q (fun _ => rfl) }
      exact Fintype.card_congr eqv
    have hc0 : Fintype.card (Fin N) = extCompCount N Eq ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ es ∅ := by
      classical
      unfold extCompCount
      let eqv : Quotient (extSetoid N Eq ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ es ∅) ≃ Fin N :=
        { toFun := Quotient.lift id (fun a b hab => Fin.ext ((extRel_empty_iff ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ es a b).mp hab))
          invFun := Quotient.mk _
          left_inv := fun q => Quotient.inductionOn q (fun _ => rfl)
          right_inv := fun _ => rfl }
      exact (Fintype.card_congr eqv).symm
    rw [hcA, hc0]
  rw [hn]

end RelFinSum

-- =========================================================================
-- Part 3: Fast Computable Frontier DP & Potential-Function Soundness Proof
-- =========================================================================

private lemma nat_ble_true {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

private lemma nat_ble_false {a b : ℕ} (h : Nat.ble a b = false) : b < a :=
  Nat.lt_of_not_le (fun hc => by rw [Nat.ble_eq_true_of_le hc] at h; cases h)

private lemma nat_beq_true {a b : ℕ} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

private lemma nat_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b :=
  fun hc => by subst hc; simp at h

private lemma nat_beq_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private def isZeroInt : Int → Bool
  | Int.ofNat 0 => true
  | _ => false

private lemma isZeroInt_eq_true (v : Int) : isZeroInt v = true ↔ v = 0 := by
  cases v with
  | ofNat n =>
    cases n with
    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | succ m => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | negSucc n => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

private def mergeFuel : Nat → List (Nat × Int) → List (Nat × Int) → List (Nat × Int)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, (k1, v1) :: xs, (k2, v2) :: ys =>
    match Nat.ble k1 k2 with
    | false => (k2, v2) :: mergeFuel n ((k1, v1) :: xs) ys
    | true =>
      match Nat.beq k1 k2 with
      | false => (k1, v1) :: mergeFuel n xs ((k2, v2) :: ys)
      | true =>
        let v := Int.add v1 v2
        match isZeroInt v with
        | true => mergeFuel n xs ys
        | false => (k1, v) :: mergeFuel n xs ys

private def mergeSum (xs ys : List (Nat × Int)) : List (Nat × Int) :=
  mergeFuel 8192 xs ys

private def pairUp : List (Nat × Int) → List (List (Nat × Int))
  | (k1, v1) :: (k2, v2) :: rest =>
    match Nat.ble k1 k2 with
    | false => [(k2, v2), (k1, v1)] :: pairUp rest
    | true =>
      match Nat.beq k1 k2 with
      | false => [(k1, v1), (k2, v2)] :: pairUp rest
      | true =>
        let v := Int.add v1 v2
        match isZeroInt v with
        | true => pairUp rest
        | false => [(k1, v)] :: pairUp rest
  | [p] => [[p]]
  | [] => []

private def mergePairs : List (List (Nat × Int)) → List (List (Nat × Int))
  | a :: b :: rest => mergeSum a b :: mergePairs rest
  | xs => xs

private def mergeAll : Nat → List (List (Nat × Int)) → List (Nat × Int)
  | _, [] => []
  | _, [xs] => xs
  | 0, xss => xss.foldl mergeSum []
  | n + 1, xss => mergeAll n (mergePairs xss)

private def sortSum (xs : List (Nat × Int)) : List (Nat × Int) :=
  mergeAll 13 (pairUp xs)

private def evalList (G : ℕ → ℤ) (xs : List (ℕ × ℤ)) : ℤ :=
  (xs.map (fun p => p.2 * G p.1)).sum

private lemma evalList_nil (G : ℕ → ℤ) : evalList G [] = 0 := rfl

private lemma evalList_cons (G : ℕ → ℤ) (k : ℕ) (v : ℤ) (xs : List (ℕ × ℤ)) :
    evalList G ((k, v) :: xs) = v * G k + evalList G xs := rfl

private lemma evalList_append (G : ℕ → ℤ) (xs ys : List (ℕ × ℤ)) :
    evalList G (xs ++ ys) = evalList G xs + evalList G ys := by
  simp [evalList]

private lemma evalList_reverse (G : ℕ → ℤ) (xs : List (ℕ × ℤ)) :
    evalList G xs.reverse = evalList G xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, v⟩
    simp only [List.reverse_cons, evalList_append, ih, evalList_cons, evalList_nil]
    ring

private lemma evalList_mergeFuel (G : ℕ → ℤ) (n : ℕ) (xs ys : List (ℕ × ℤ)) :
    evalList G (mergeFuel n xs ys) = evalList G xs + evalList G ys := by
  induction n generalizing xs ys with
  | zero => exact evalList_append G xs ys
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel, evalList]
    | cons p1 xs =>
      rcases p1 with ⟨k1, v1⟩
      cases ys with
      | nil => simp [mergeFuel, evalList]
      | cons p2 ys =>
        rcases p2 with ⟨k2, v2⟩
        unfold mergeFuel
        cases h1 : Nat.ble k1 k2
        · simp only [evalList_cons, ih]; ring
        · cases h2 : Nat.beq k1 k2
          · simp only [evalList_cons, ih]; ring
          · have heq : k1 = k2 := nat_beq_true h2
            subst heq
            dsimp only
            cases hz : isZeroInt (Int.add v1 v2)
            · simp only [evalList_cons, ih]
              change (v1 + v2) * G k1 + (evalList G xs + evalList G ys) =
                v1 * G k1 + evalList G xs + (v2 * G k1 + evalList G ys)
              ring
            · have hv0 : v1 + v2 = 0 := (isZeroInt_eq_true _).mp hz
              rw [ih, evalList_cons, evalList_cons]
              have : v1 * G k1 + evalList G xs + (v2 * G k1 + evalList G ys) =
                  (v1 + v2) * G k1 + (evalList G xs + evalList G ys) := by ring
              rw [this, hv0]; ring

private lemma evalList_mergeSum (G : ℕ → ℤ) (xs ys : List (ℕ × ℤ)) :
    evalList G (mergeSum xs ys) = evalList G xs + evalList G ys :=
  evalList_mergeFuel G _ xs ys

private lemma evalList_pairUp (G : ℕ → ℤ) (xs : List (ℕ × ℤ)) :
    ((pairUp xs).map (evalList G)).sum = evalList G xs := by
  match xs with
  | [] => rfl
  | [(k, v)] => simp [pairUp, evalList]
  | (k1, v1) :: (k2, v2) :: rest =>
    unfold pairUp
    have ih := evalList_pairUp G rest
    cases h1 : Nat.ble k1 k2
    · simp only [List.map_cons, List.sum_cons, evalList_cons, evalList_nil, ih]; ring
    · cases h2 : Nat.beq k1 k2
      · simp only [List.map_cons, List.sum_cons, evalList_cons, evalList_nil, ih]; ring
      · have heq : k1 = k2 := nat_beq_true h2
        subst heq
        dsimp only
        cases hz : isZeroInt (Int.add v1 v2)
        · simp only [List.map_cons, List.sum_cons, evalList_cons, evalList_nil, ih]
          change (v1 + v2) * G k1 + 0 + evalList G rest =
            v1 * G k1 + (v2 * G k1 + evalList G rest)
          ring
        · have hv0 : v1 + v2 = 0 := (isZeroInt_eq_true _).mp hz
          rw [ih, evalList_cons, evalList_cons]
          have : v1 * G k1 + (v2 * G k1 + evalList G rest) =
              (v1 + v2) * G k1 + evalList G rest := by ring
          rw [this, hv0]; ring

private lemma evalList_mergePairs (G : ℕ → ℤ) (xss : List (List (ℕ × ℤ))) :
    ((mergePairs xss).map (evalList G)).sum = (xss.map (evalList G)).sum := by
  match xss with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    simp only [mergePairs, List.map_cons, List.sum_cons, evalList_mergeSum,
      evalList_mergePairs G rest]
    ring

private lemma evalList_foldl_mergeSum (G : ℕ → ℤ) (acc : List (ℕ × ℤ)) (xss : List (List (ℕ × ℤ))) :
    evalList G (xss.foldl mergeSum acc) = evalList G acc + (xss.map (evalList G)).sum := by
  induction xss generalizing acc with
  | nil => simp
  | cons xs rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, evalList_mergeSum]
    ring

private lemma evalList_mergeAll (G : ℕ → ℤ) (n : ℕ) (xss : List (List (ℕ × ℤ))) :
    evalList G (mergeAll n xss) = (xss.map (evalList G)).sum := by
  induction n generalizing xss with
  | zero =>
    cases xss with
    | nil => rfl
    | cons xs rest =>
      cases rest with
      | nil => simp [mergeAll]
      | cons ys rest2 =>
        simp only [mergeAll, evalList_foldl_mergeSum, evalList_nil, zero_add]
  | succ n ih =>
    cases xss with
    | nil => rfl
    | cons xs rest =>
      cases rest with
      | nil => simp [mergeAll]
      | cons ys rest2 =>
        simp only [mergeAll, ih, evalList_mergePairs]

private lemma evalList_sortSum (G : ℕ → ℤ) (xs : List (ℕ × ℤ)) :
    evalList G (sortSum xs) = evalList G xs := by
  unfold sortSum
  rw [evalList_mergeAll, evalList_pairUp]

private lemma mem_mergeFuel_keys {n : ℕ} {xs ys : List (ℕ × ℤ)} {p : ℕ × ℤ}
    (hp : p ∈ mergeFuel n xs ys) :
    (∃ q ∈ xs, q.1 = p.1) ∨ (∃ q ∈ ys, q.1 = p.1) := by
  induction n generalizing xs ys with
  | zero =>
    rcases List.mem_append.mp hp with h | h
    · exact Or.inl ⟨p, h, rfl⟩
    · exact Or.inr ⟨p, h, rfl⟩
  | succ n ih =>
    cases xs with
    | nil => exact Or.inr ⟨p, hp, rfl⟩
    | cons p1 xs =>
      rcases p1 with ⟨k1, v1⟩
      cases ys with
      | nil => exact Or.inl ⟨p, hp, rfl⟩
      | cons p2 ys =>
        rcases p2 with ⟨k2, v2⟩
        unfold mergeFuel at hp
        cases h1 : Nat.ble k1 k2
        · rw [h1] at hp; dsimp only at hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Or.inr ⟨(k2, v2), List.mem_cons_self .., rfl⟩
          · rcases ih hp' with ⟨q, hq, hq1⟩ | ⟨q, hq, hq1⟩
            · exact Or.inl ⟨q, hq, hq1⟩
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
        · rw [h1] at hp; dsimp only at hp
          cases h2 : Nat.beq k1 k2
          · rw [h2] at hp; dsimp only at hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact Or.inl ⟨(k1, v1), List.mem_cons_self .., rfl⟩
            · rcases ih hp' with ⟨q, hq, hq1⟩ | ⟨q, hq, hq1⟩
              · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
              · exact Or.inr ⟨q, hq, hq1⟩
          · rw [h2] at hp; dsimp only at hp
            cases hz : isZeroInt (Int.add v1 v2)
            · rw [hz] at hp; dsimp only at hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact Or.inl ⟨(k1, v1), List.mem_cons_self .., rfl⟩
              · rcases ih hp' with ⟨q, hq, hq1⟩ | ⟨q, hq, hq1⟩
                · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
                · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
            · rw [hz] at hp; dsimp only at hp
              rcases ih hp with ⟨q, hq, hq1⟩ | ⟨q, hq, hq1⟩
              · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
              · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq1⟩

private lemma allKeys_mergeSum {P : ℕ → Prop} {xs ys : List (ℕ × ℤ)}
    (hx : ∀ p ∈ xs, P p.1) (hy : ∀ p ∈ ys, P p.1) :
    ∀ p ∈ mergeSum xs ys, P p.1 := by
  intro p hp
  rcases mem_mergeFuel_keys hp with ⟨q, hq, hq1⟩ | ⟨q, hq, hq1⟩
  · exact hq1 ▸ hx q hq
  · exact hq1 ▸ hy q hq

private lemma allKeys_pairUp {P : ℕ → Prop} {xs : List (ℕ × ℤ)}
    (h : ∀ p ∈ xs, P p.1) :
    ∀ ys ∈ pairUp xs, ∀ p ∈ ys, P p.1 := by
  match xs with
  | [] => intro ys hys; cases hys
  | [q] =>
    intro ys hys p hp
    rcases List.mem_singleton.mp hys with rfl
    rcases List.mem_singleton.mp hp with rfl
    exact h q (List.mem_singleton_self _)
  | (k1, v1) :: (k2, v2) :: rest =>
    have h1 : P k1 := h (k1, v1) (List.mem_cons_self ..)
    have h2 : P k2 := h (k2, v2) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hrest : ∀ ys ∈ pairUp rest, ∀ p ∈ ys, P p.1 :=
      allKeys_pairUp (fun q hq => h q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))
    intro ys hys p hp
    unfold pairUp at hys
    cases hb : Nat.ble k1 k2
    · rw [hb] at hys; dsimp only at hys
      rcases List.mem_cons.mp hys with rfl | htl
      · rcases List.mem_cons.mp hp with rfl | hp'
        · exact h2
        · rcases List.mem_singleton.mp hp' with rfl; exact h1
      · exact hrest ys htl p hp
    · rw [hb] at hys; dsimp only at hys
      cases hq : Nat.beq k1 k2
      · rw [hq] at hys; dsimp only at hys
        rcases List.mem_cons.mp hys with rfl | htl
        · rcases List.mem_cons.mp hp with rfl | hp'
          · exact h1
          · rcases List.mem_singleton.mp hp' with rfl; exact h2
        · exact hrest ys htl p hp
      · rw [hq] at hys; dsimp only at hys
        cases hz : isZeroInt (Int.add v1 v2)
        · rw [hz] at hys; dsimp only at hys
          rcases List.mem_cons.mp hys with rfl | htl
          · rcases List.mem_singleton.mp hp with rfl; exact h1
          · exact hrest ys htl p hp
        · rw [hz] at hys; dsimp only at hys
          exact hrest ys hys p hp

private lemma allKeys_mergePairs {P : ℕ → Prop} {xss : List (List (ℕ × ℤ))}
    (h : ∀ xs ∈ xss, ∀ p ∈ xs, P p.1) :
    ∀ xs ∈ mergePairs xss, ∀ p ∈ xs, P p.1 := by
  match xss with
  | [] => intro xs hxs; cases hxs
  | [xs] => exact h
  | a :: b :: rest =>
    intro xs hxs
    rcases List.mem_cons.mp hxs with rfl | hrest
    · exact allKeys_mergeSum (h a (List.mem_cons_self ..))
        (h b (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact allKeys_mergePairs (fun ys hys => h ys (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hys))) xs hrest

private lemma allKeys_foldl_mergeSum {P : ℕ → Prop} {acc : List (ℕ × ℤ)} {xss : List (List (ℕ × ℤ))}
    (ha : ∀ p ∈ acc, P p.1) (hx : ∀ xs ∈ xss, ∀ p ∈ xs, P p.1) :
    ∀ p ∈ xss.foldl mergeSum acc, P p.1 := by
  induction xss generalizing acc with
  | nil => exact ha
  | cons xs rest ih =>
    exact ih (allKeys_mergeSum ha (hx xs (List.mem_cons_self ..)))
      (fun ys hys => hx ys (List.mem_cons_of_mem _ hys))

private lemma allKeys_mergeAll {P : ℕ → Prop} {n : ℕ} {xss : List (List (ℕ × ℤ))}
    (h : ∀ xs ∈ xss, ∀ p ∈ xs, P p.1) :
    ∀ p ∈ mergeAll n xss, P p.1 := by
  induction n generalizing xss with
  | zero =>
    cases xss with
    | nil => intro p hp; cases hp
    | cons xs rest =>
      cases rest with
      | nil => exact h xs (List.mem_cons_self ..)
      | cons ys rest2 =>
        exact allKeys_foldl_mergeSum (fun p hp => by cases hp) h
  | succ n ih =>
    cases xss with
    | nil => intro p hp; cases hp
    | cons xs rest =>
      cases rest with
      | nil => exact h xs (List.mem_cons_self ..)
      | cons ys rest2 =>
        exact ih (allKeys_mergePairs h)

private lemma allKeys_sortSum {P : ℕ → Prop} {xs : List (ℕ × ℤ)}
    (h : ∀ p ∈ xs, P p.1) :
    ∀ p ∈ sortSum xs, P p.1 :=
  allKeys_mergeAll (allKeys_pairUp h)

-- Partition encoding/decoding & operations
private def unpackPart : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, c => Nat.mod c 16 :: unpackPart k (Nat.div c 16)

private def packRaw : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.add x (Nat.mul 16 (packRaw xs))

private def findOrAdd (x nxt : Nat) : List (Nat × Nat) → Nat × Nat × List (Nat × Nat)
  | [] => (nxt, Nat.add nxt 1, [(x, nxt)])
  | (k, v) :: rest =>
    match Nat.beq k x with
    | true => (v, nxt, (k, v) :: rest)
    | false =>
      let (res, nxt', rest') := findOrAdd x nxt rest
      (res, nxt', (k, v) :: rest')

private def packCanonAux (mp : List (Nat × Nat)) (nxt : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs =>
    let (v, nxt', mp') := findOrAdd x nxt mp
    Nat.add v (Nat.mul 16 (packCanonAux mp' nxt' xs))

private def packCanon (p : List Nat) : Nat := packCanonAux [] 0 p

private def canonListAux (mp : List (Nat × Nat)) (nxt : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let (v, nxt', mp') := findOrAdd x nxt mp
    v :: canonListAux mp' nxt' xs

private lemma packCanonAux_eq_packRaw (mp : List (Nat × Nat)) (nxt : Nat) (p : List Nat) :
    packCanonAux mp nxt p = packRaw (canonListAux mp nxt p) := by
  induction p generalizing mp nxt with
  | nil => rfl
  | cons x xs ih =>
    unfold packCanonAux canonListAux
    simp only [packRaw, ih]

private def getNth : Nat → List Nat → Nat
  | _, [] => 0
  | 0, x :: _ => x
  | n + 1, _ :: xs => getNth n xs

private def mergeColorList (lo hi : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs =>
    (match Nat.beq c hi with
      | true => lo
      | false => match Nat.ble (Nat.add hi 1) c with | true => Nat.sub c 1 | false => c) ::
    mergeColorList lo hi cs

private def mergeColorPack (lo hi : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs =>
    let c' := match Nat.beq c hi with
      | true => lo
      | false => match Nat.ble (Nat.add hi 1) c with | true => Nat.sub c 1 | false => c
    Nat.add c' (Nat.mul 16 (mergeColorPack lo hi cs))

private lemma mergeColorPack_eq_packRaw (lo hi : Nat) (p : List Nat) :
    mergeColorPack lo hi p = packRaw (mergeColorList lo hi p) := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [mergeColorPack, mergeColorList, packRaw, ih]

private def replaceColor (oldC newC : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (match Nat.beq x oldC with | true => newC | false => x) :: replaceColor oldC newC xs

private def projectList (keep : List Bool) (p : List Nat) : List Nat :=
  match keep, p with
  | true :: ks, x :: xs => x :: projectList ks xs
  | false :: ks, _ :: xs => projectList ks xs
  | _, _ => []

private def allTrue : List Bool → Bool
  | [] => true
  | b :: bs => match b with | true => allTrue bs | false => false

private def maxPlusOne : List Nat → Nat
  | [] => 0
  | x :: xs =>
    let m := maxPlusOne xs
    let x1 := Nat.add x 1
    match Nat.ble (Nat.add x1 1) m with | true => m | false => x1

private def AllLt (m : ℕ) (p : List ℕ) : Prop := ∀ d ∈ p, d < m

private lemma unpackPart_length (k c : ℕ) : (unpackPart k c).length = k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => simp [unpackPart, ih]

private lemma unpackPart_packRaw (p : List ℕ) (hp : AllLt 16 p) :
    unpackPart p.length (packRaw p) = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    have hx : x < 16 := hp x (List.mem_cons_self ..)
    have hxs : AllLt 16 xs := fun d hd => hp d (List.mem_cons_of_mem _ hd)
    simp only [List.length_cons, unpackPart, packRaw]
    have hmod : Nat.mod (Nat.add x (Nat.mul 16 (packRaw xs))) 16 = x := by
      change (x + 16 * packRaw xs) % 16 = x; omega
    have hdiv : Nat.div (Nat.add x (Nat.mul 16 (packRaw xs))) 16 = packRaw xs := by
      change (x + 16 * packRaw xs) / 16 = packRaw xs; omega
    rw [hmod, hdiv, ih hxs]

private lemma maxPlusOne_gt {p : List ℕ} {d : ℕ} (hd : d ∈ p) : d < maxPlusOne p := by
  induction p with
  | nil => cases hd
  | cons x xs ih =>
    unfold maxPlusOne
    dsimp only
    rcases List.mem_cons.mp hd with rfl | hxs
    · cases h : Nat.ble (Nat.add (Nat.add d 1) 1) (maxPlusOne xs)
      · dsimp only; change d < d + 1; omega
      · dsimp only
        have : d + 1 + 1 ≤ maxPlusOne xs := nat_ble_true h
        omega
    · have hih := ih hxs
      cases h : Nat.ble (Nat.add (Nat.add x 1) 1) (maxPlusOne xs)
      · dsimp only
        have : maxPlusOne xs < x + 1 + 1 := nat_ble_false h
        change d < x + 1; omega
      · dsimp only; exact hih

private lemma maxPlusOne_le {p : List ℕ} {m : ℕ} (hp : AllLt m p) : maxPlusOne p ≤ m := by
  induction p with
  | nil => simp [maxPlusOne]
  | cons x xs ih =>
    have hx : x < m := hp x (List.mem_cons_self ..)
    have hxs : maxPlusOne xs ≤ m := ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))
    unfold maxPlusOne
    dsimp only
    cases h : Nat.ble (Nat.add (Nat.add x 1) 1) (maxPlusOne xs)
    · dsimp only; change x + 1 ≤ m; omega
    · dsimp only; exact hxs

private lemma allLt_append_maxPlusOne {p : List ℕ} {k : ℕ} (hp : AllLt k p) :
    AllLt (k + 1) (p ++ [maxPlusOne p]) := by
  intro d hd
  rcases List.mem_append.mp hd with h1 | h2
  · have := hp d h1; omega
  · rcases List.mem_singleton.mp h2 with rfl
    have := maxPlusOne_le hp; omega

private lemma mergeColorList_length (lo hi : ℕ) (p : List ℕ) :
    (mergeColorList lo hi p).length = p.length := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [mergeColorList, ih]

private lemma mergeColorList_allLt {lo hi k : ℕ} (hlo : lo < k) (p : List ℕ) (hp : AllLt k p) :
    AllLt k (mergeColorList lo hi p) := by
  induction p with
  | nil => intro d hd; cases hd
  | cons c cs ih =>
    intro d hd
    have hc : c < k := hp c (List.mem_cons_self ..)
    have hcs := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    rcases List.mem_cons.mp hd with rfl | hrest
    · cases Nat.beq c hi
      · cases Nat.ble (Nat.add hi 1) c
        · exact hc
        · change c - 1 < k; omega
      · exact hlo
    · exact hcs d hrest

private lemma getNth_mergeColorList {lo hi : ℕ} (p : List ℕ) (i : ℕ) (hi_lt : i < p.length) :
    getNth i (mergeColorList lo hi p) =
      let c := getNth i p
      if c = hi then lo else if hi < c then c - 1 else c := by
  induction p generalizing i with
  | nil => simp at hi_lt
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [mergeColorList, getNth]
      cases hb : Nat.beq c hi
      · have hne : c ≠ hi := nat_beq_false hb
        cases hl : Nat.ble (Nat.add hi 1) c
        · have hnl : ¬ (hi < c) := by have : c < hi + 1 := nat_ble_false hl; omega
          simp [hne, hnl]
        · have hlt : hi < c := by have : hi + 1 ≤ c := nat_ble_true hl; omega
          simp [hne, hlt]
      · have heq : c = hi := nat_beq_true hb
        simp [heq]
    | succ i =>
      simp only [mergeColorList, getNth]
      exact ih i (by simpa using hi_lt)

private lemma mergeColor_eq_iff {lo hi a b : ℕ} (hlh : lo < hi) :
    (if a = hi then lo else if hi < a then a - 1 else a) =
    (if b = hi then lo else if hi < b then b - 1 else b) ↔
    a = b ∨ (a = lo ∧ b = hi) ∨ (a = hi ∧ b = lo) := by
  split_ifs <;> omega

private lemma getNth_replaceColor (oldC newC : ℕ) (p : List ℕ) (i : ℕ) (hi : i < p.length) :
    getNth i (replaceColor oldC newC p) =
      if getNth i p = oldC then newC else getNth i p := by
  induction p generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [replaceColor, getNth]
      cases hb : Nat.beq x oldC
      · have : x ≠ oldC := nat_beq_false hb
        simp [this]
      · have : x = oldC := nat_beq_true hb
        simp [this]
    | succ i =>
      simp only [replaceColor, getNth]
      exact ih i (by simpa using hi)

private lemma replaceColor_length (oldC newC : ℕ) (p : List ℕ) :
    (replaceColor oldC newC p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [replaceColor, ih]

private def MapInv (mp : List (ℕ × ℕ)) (nxt : ℕ) : Prop :=
  (∀ k v, (k, v) ∈ mp → v < nxt) ∧
  (∀ k1 v1 k2 v2, (k1, v1) ∈ mp → (k2, v2) ∈ mp → (k1 = k2 ↔ v1 = v2))

private lemma findOrAdd_nxt_le (x nxt : ℕ) (mp : List (ℕ × ℕ)) :
    nxt ≤ (findOrAdd x nxt mp).2.1 := by
  induction mp with
  | nil => change nxt ≤ nxt + 1; omega
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    unfold findOrAdd
    cases Nat.beq k x
    · exact ih
    · exact le_refl nxt

private lemma findOrAdd_spec (x nxt : ℕ) (mp : List (ℕ × ℕ)) (hinv : MapInv mp nxt) :
    let r := findOrAdd x nxt mp
    MapInv r.2.2 r.2.1 ∧ r.2.1 ≤ nxt + 1 ∧ (x, r.1) ∈ r.2.2 ∧
      ∀ a b, (a, b) ∈ mp → (a, b) ∈ r.2.2 := by
  induction mp with
  | nil =>
    refine ⟨⟨?_, ?_⟩, le_refl _, List.mem_cons_self .., fun _ _ h => by cases h⟩
    · intro k v hkv
      rcases Prod.mk.inj (List.mem_singleton.mp hkv) with ⟨_, hvn⟩
      change v < nxt + 1
      omega
    · intro k1 v1 k2 v2 h1 h2
      rcases Prod.mk.inj (List.mem_singleton.mp h1) with ⟨rfl, rfl⟩
      rcases Prod.mk.inj (List.mem_singleton.mp h2) with ⟨rfl, rfl⟩
      simp
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    have hrest : MapInv rest nxt :=
      ⟨fun a b h => hinv.1 a b (List.mem_cons_of_mem _ h),
       fun a1 b1 a2 b2 h1 h2 => hinv.2 a1 b1 a2 b2 (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)⟩
    unfold findOrAdd
    cases hkx : Nat.beq k x
    · have hne : k ≠ x := nat_beq_false hkx
      dsimp only
      have hr := ih hrest
      have hnew : ∀ a b, (a, b) ∈ (findOrAdd x nxt rest).2.2 →
          (a, b) ∈ rest ∨ (a = x ∧ b = nxt) := by
        clear hr ih hinv hrest hne hkx k v
        induction rest with
        | nil =>
          intro a b hab
          rcases Prod.mk.inj (List.mem_singleton.mp hab) with ⟨rfl, rfl⟩
          exact Or.inr ⟨rfl, rfl⟩
        | cons kv2 r2 ihr =>
          rcases kv2 with ⟨k2, v2⟩
          intro a b hab
          unfold findOrAdd at hab
          cases h2 : Nat.beq k2 x
          · rw [h2] at hab; dsimp only at hab
            rcases List.mem_cons.mp hab with h | h
            · exact Or.inl (h ▸ List.mem_cons_self ..)
            · rcases ihr a b h with h' | h'
              · exact Or.inl (List.mem_cons_of_mem _ h')
              · exact Or.inr h'
          · rw [h2] at hab; dsimp only at hab
            exact Or.inl hab
      have hnxt_le : nxt ≤ (findOrAdd x nxt rest).2.1 := findOrAdd_nxt_le x nxt rest
      refine ⟨⟨?_, ?_⟩, hr.2.1, List.mem_cons_of_mem _ hr.2.2.1, ?_⟩
      · intro a b hab
        rcases List.mem_cons.mp hab with h | h
        · rcases Prod.mk.inj h with ⟨_, hb⟩
          have hvlt : v < nxt := hinv.1 k v (List.mem_cons_self ..)
          exact Nat.lt_of_lt_of_le (hb ▸ hvlt) hnxt_le
        · exact hr.1.1 a b h
      · intro k1 v1 k2 v2 h1 h2
        rcases List.mem_cons.mp h1 with h1' | h1' <;> rcases List.mem_cons.mp h2 with h2' | h2'
        · rcases Prod.mk.inj h1' with ⟨rfl, rfl⟩; rcases Prod.mk.inj h2' with ⟨rfl, rfl⟩; simp
        · rcases Prod.mk.inj h1' with ⟨hk1, hv1⟩
          rcases hnew k2 v2 h2' with h2r | ⟨hk2, hv2⟩
          · rw [hk1, hv1]
            exact hinv.2 k v k2 v2 (List.mem_cons_self ..) (List.mem_cons_of_mem _ h2r)
          · have hvlt : v < nxt := hinv.1 k v (List.mem_cons_self ..)
            rw [hk1, hv1, hk2, hv2]
            constructor
            · intro hk; exact absurd hk hne
            · intro hv; omega
        · rcases Prod.mk.inj h2' with ⟨hk2, hv2⟩
          rcases hnew k1 v1 h1' with h1r | ⟨hk1, hv1⟩
          · rw [hk2, hv2]
            exact hinv.2 k1 v1 k v (List.mem_cons_of_mem _ h1r) (List.mem_cons_self ..)
          · have hvlt : v < nxt := hinv.1 k v (List.mem_cons_self ..)
            rw [hk1, hv1, hk2, hv2]
            constructor
            · intro hk; exact absurd hk.symm hne
            · intro hv; omega
        · exact hr.1.2 k1 v1 k2 v2 h1' h2'
      · intro a b hab
        rcases List.mem_cons.mp hab with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hr.2.2.2 a b h)
    · have heq : k = x := nat_beq_true hkx
      subst heq
      exact ⟨hinv, Nat.le_succ nxt, List.mem_cons_self .., fun _ _ h => h⟩

private lemma canonListAux_length (mp : List (ℕ × ℕ)) (nxt : ℕ) (p : List ℕ) :
    (canonListAux mp nxt p).length = p.length := by
  induction p generalizing mp nxt with
  | nil => rfl
  | cons x xs ih => simp [canonListAux, ih]

private lemma canonListAux_spec (mp : List (ℕ × ℕ)) (nxt : ℕ) (p : List ℕ) (hinv : MapInv mp nxt) :
    ∃ mp' nxt', MapInv mp' nxt' ∧ nxt' ≤ nxt + p.length ∧
      (∀ a b, (a, b) ∈ mp → (a, b) ∈ mp') ∧
      (∀ i, i < p.length → (getNth i p, getNth i (canonListAux mp nxt p)) ∈ mp') := by
  induction p generalizing mp nxt with
  | nil => exact ⟨mp, nxt, hinv, by simp, fun _ _ h => h, fun _ hi => by simp at hi⟩
  | cons x xs ih =>
    have hf := findOrAdd_spec x nxt mp hinv
    rcases ih (findOrAdd x nxt mp).2.2 (findOrAdd x nxt mp).2.1 hf.1 with
      ⟨mp', nxt', hinv', hnxt', hext', hget'⟩
    refine ⟨mp', nxt', hinv', by simp; omega, fun a b h => hext' a b (hf.2.2.2 a b h), ?_⟩
    intro i hi
    cases i with
    | zero =>
      simp only [canonListAux, getNth]
      exact hext' x _ hf.2.2.1
    | succ i =>
      simp only [canonListAux, getNth]
      exact hget' i (by simpa using hi)

private lemma canonList_spec (p : List ℕ) :
    (canonListAux [] 0 p).length = p.length ∧
    AllLt p.length (canonListAux [] 0 p) ∧
    (∀ i j, i < p.length → j < p.length →
      (getNth i (canonListAux [] 0 p) = getNth j (canonListAux [] 0 p) ↔
       getNth i p = getNth j p)) := by
  have h0 : MapInv [] 0 := ⟨fun _ _ h => (by cases h), fun _ _ _ _ h => (by cases h)⟩
  rcases canonListAux_spec [] 0 p h0 with ⟨mp', nxt', hinv', hnxt', _, hget'⟩
  have hlen : (canonListAux [] 0 p).length = p.length := canonListAux_length [] 0 p
  refine ⟨hlen, ?_, ?_⟩
  · intro d hd
    have hmem_idx : ∀ (l : List ℕ), d ∈ l → ∃ i, i < l.length ∧ getNth i l = d := by
      intro l hl
      induction l with
      | nil => cases hl
      | cons y ys ih =>
        rcases List.mem_cons.mp hl with rfl | hys
        · exact ⟨0, by simp, rfl⟩
        · rcases ih hys with ⟨i, hi, rfl⟩
          exact ⟨i + 1, by simp; omega, rfl⟩
    rcases hmem_idx (canonListAux [] 0 p) hd with ⟨i, hi, hdi⟩
    rw [hlen] at hi
    rw [← hdi]
    have hlt := hinv'.1 _ _ (hget' i hi)
    omega
  · intro i j hi hj
    exact (hinv'.2 _ _ _ _ (hget' i hi) (hget' j hj)).symm

private lemma getNth_append_left (p q : List ℕ) (i : ℕ) (hi : i < p.length) :
    getNth i (p ++ q) = getNth i p := by
  induction p generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

private lemma getNth_append_right (p : List ℕ) (v : ℕ) :
    getNth p.length (p ++ [v]) = v := by
  induction p with
  | nil => rfl
  | cons x xs ih => exact ih

private lemma mem_of_getNth {p : List ℕ} {i : ℕ} (hi : i < p.length) : getNth i p ∈ p := by
  induction p generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => exact List.mem_cons_self ..
    | succ i => exact List.mem_cons_of_mem _ (ih (by simpa using hi))

private def indexOf (x : Nat) : List Nat → Option Nat
  | [] => none
  | y :: ys => match Nat.beq x y with | true => some 0 | false => (indexOf x ys).map (Nat.add · 1)

private lemma indexOf_eq_none (x : ℕ) (F : List ℕ) : indexOf x F = none ↔ x ∉ F := by
  induction F with
  | nil => simp [indexOf]
  | cons y ys ih =>
    unfold indexOf
    cases h : Nat.beq x y
    · have hne : x ≠ y := nat_beq_false h
      simp [hne, ih]
    · have heq : x = y := nat_beq_true h
      simp [heq]

private lemma indexOf_lt_length {x i : ℕ} {F : List ℕ} (h : indexOf x F = some i) : i < F.length := by
  induction F generalizing i with
  | nil => simp [indexOf] at h
  | cons y ys ih =>
    unfold indexOf at h
    cases hb : Nat.beq x y
    · rw [hb] at h; dsimp only at h
      rcases Option.map_eq_some_iff.mp h with ⟨j, hj, rfl⟩
      simp; exact ih hj
    · rw [hb] at h; cases h; simp

private lemma indexOf_getNth {x i : ℕ} {F : List ℕ} (h : indexOf x F = some i) :
    getNth i F = x := by
  induction F generalizing i with
  | nil => simp [indexOf] at h
  | cons y ys ih =>
    unfold indexOf at h
    cases hb : Nat.beq x y
    · rw [hb] at h; dsimp only at h
      rcases Option.map_eq_some_iff.mp h with ⟨j, hj, rfl⟩
      exact ih hj
    · rw [hb] at h; cases h
      have heq : x = y := nat_beq_true hb
      exact heq.symm

private lemma indexOf_eq_some_of_nodup {x : ℕ} {F : List ℕ} (hnd : F.Nodup) {i : ℕ}
    (hi : i < F.length) (hget : getNth i F = x) : indexOf x F = some i := by
  induction F generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
    rcases List.nodup_cons.mp hnd with ⟨hynot, hnd'⟩
    cases i with
    | zero =>
      simp only [getNth] at hget
      subst hget
      simp [indexOf]
    | succ i =>
      simp only [getNth] at hget
      have hne : x ≠ y := fun h => hynot (h ▸ hget ▸ mem_of_getNth (by simpa using hi))
      have hb : Nat.beq x y = false := nat_beq_of_ne hne
      simp [indexOf, hb, ih hnd' (by simpa using hi) hget]

private lemma indexOf_append_of_mem {x i : ℕ} {F : List ℕ} (u : ℕ) (h : indexOf x F = some i) :
    indexOf x (F ++ [u]) = some i := by
  induction F generalizing i with
  | nil => simp [indexOf] at h
  | cons y ys ih =>
    simp only [List.cons_append]
    unfold indexOf at h ⊢
    cases hb : Nat.beq x y
    · rw [hb] at h; dsimp only at h ⊢
      rcases Option.map_eq_some_iff.mp h with ⟨j, hj, rfl⟩
      simp [ih hj]
    · rw [hb] at h; dsimp only at h ⊢; cases h; rfl

private lemma indexOf_append_self {u : ℕ} {F : List ℕ} (hnot : u ∉ F) :
    indexOf u (F ++ [u]) = some F.length := by
  induction F with
  | nil => simp [indexOf]
  | cons y ys ih =>
    have hne : u ≠ y := fun h => hnot (h ▸ List.mem_cons_self ..)
    have hnot' : u ∉ ys := fun h => hnot (List.mem_cons_of_mem _ h)
    have hb : Nat.beq u y = false := nat_beq_of_ne hne
    simp [indexOf, hb, ih hnot']

private lemma indexOf_append_none {x u : ℕ} {F : List ℕ} (hnot : x ∉ F) (hne : x ≠ u) :
    indexOf x (F ++ [u]) = none := by
  rw [indexOf_eq_none]
  intro h
  rcases List.mem_append.mp h with h1 | h2
  · exact hnot h1
  · exact hne (List.mem_singleton.mp h2)

private lemma projectList_length (keep : List Bool) (p : List ℕ) (hlen : keep.length = p.length) :
    (projectList keep p).length = (keep.filter id).length := by
  induction keep generalizing p with
  | nil => cases p <;> simp [projectList] at hlen ⊢
  | cons b ks ih =>
    cases p with
    | nil => simp at hlen
    | cons x xs =>
      cases b <;> simp [projectList, ih xs (by simpa using hlen)]

private lemma filter_length_eq (pred : ℕ → Bool) (F : List ℕ) :
    (F.filter pred).length = ((F.map pred).filter id).length := by
  induction F with
  | nil => rfl
  | cons y ys ih =>
    cases h : pred y <;> simp [h, ih]

private lemma projectList_getNth_filter (pred : ℕ → Bool) (F p : List ℕ) (hlen : F.length = p.length)
    (x : ℕ) (hpred : pred x = true) :
    match indexOf x (F.filter pred), indexOf x F with
    | some j, some i => j < (projectList (F.map pred) p).length ∧ i < p.length ∧
        getNth j (projectList (F.map pred) p) = getNth i p
    | none, none => True
    | _, _ => False := by
  induction F generalizing p with
  | nil =>
    cases p <;> simp [indexOf] at hlen ⊢
  | cons y ys ih =>
    cases p with
    | nil => simp at hlen
    | cons c cs =>
      have ih' := ih cs (by simpa using hlen)
      by_cases hxy : x = y
      · subst hxy
        simp only [List.filter_cons, hpred, ↓reduceIte, List.map_cons, projectList,
          indexOf, Nat.beq_refl, getNth, List.length_cons]
        exact ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, trivial⟩
      · have hbx : Nat.beq x y = false := nat_beq_of_ne hxy
        cases hpy : pred y
        · simp only [List.filter_cons, hpy, Bool.false_eq_true, ↓reduceIte, List.map_cons,
            projectList, indexOf, hbx]
          cases h1 : indexOf x (ys.filter pred) with
          | none =>
            cases h2 : indexOf x ys with
            | none => simp
            | some i => rw [h1, h2] at ih'; exact False.elim ih'
          | some j =>
            cases h2 : indexOf x ys with
            | none => rw [h1, h2] at ih'; exact False.elim ih'
            | some i =>
              rw [h1, h2] at ih'
              dsimp only [Option.map_some, getNth, List.length_cons] at ih' ⊢
              exact ⟨ih'.1, Nat.succ_lt_succ ih'.2.1, ih'.2.2⟩
        · simp only [List.filter_cons, hpy, ↓reduceIte, List.map_cons, projectList,
            indexOf, hbx]
          cases h1 : indexOf x (ys.filter pred) with
          | none =>
            cases h2 : indexOf x ys with
            | none => simp
            | some i => rw [h1, h2] at ih'; exact False.elim ih'
          | some j =>
            cases h2 : indexOf x ys with
            | none => rw [h1, h2] at ih'; exact False.elim ih'
            | some i =>
              rw [h1, h2] at ih'
              dsimp only [Option.map_some, getNth, List.length_cons] at ih' ⊢
              exact ⟨Nat.succ_lt_succ ih'.1, Nat.succ_lt_succ ih'.2.1, ih'.2.2⟩

private lemma projectList_allTrue (keep : List Bool) (p : List ℕ)
    (ht : allTrue keep = true) (hlen : keep.length = p.length) :
    projectList keep p = p := by
  induction keep generalizing p with
  | nil => cases p <;> simp [projectList] at hlen ⊢
  | cons b ks ih =>
    cases p with
    | nil => simp at hlen
    | cons x xs =>
      cases b with
      | false => simp [allTrue] at ht
      | true => simp [projectList, ih xs ht (by simpa using hlen)]

private lemma filter_allTrue (pred : ℕ → Bool) (F : List ℕ)
    (ht : allTrue (F.map pred) = true) : F.filter pred = F := by
  induction F with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, allTrue] at ht
    cases h : pred y
    · rw [h] at ht; simp at ht
    · rw [h] at ht; simp [h, ih ht]

-- Relation induced by a frontier list F and color list p
private def relOfList (F p : List ℕ) (x y : ℕ) : Prop :=
  x = y ∨ match indexOf x F, indexOf y F with
    | some i, some j => getNth i p = getNth j p
    | _, _ => False

private def relOfCode (F : List ℕ) (code : ℕ) : ℕ → ℕ → Prop :=
  relOfList F (unpackPart F.length code)

private lemma relOfList_append_fresh {F p : List ℕ} {u : ℕ} (hu : u ∉ F)
    (hlen : p.length = F.length) (x y : ℕ) :
    relOfList (F ++ [u]) (p ++ [maxPlusOne p]) x y ↔ relOfList F p x y := by
  unfold relOfList
  by_cases hxy : x = y
  · simp [hxy]
  simp only [hxy, false_or]
  cases hx : indexOf x F with
  | none =>
    have hxnot : x ∉ F := (indexOf_eq_none x F).mp hx
    by_cases hxu : x = u
    · subst hxu
      rw [indexOf_append_self hu]
      cases hy : indexOf y F with
      | none =>
        have hynot : y ∉ F := (indexOf_eq_none y F).mp hy
        have hyu : y ≠ x := fun h => hxy h.symm
        rw [indexOf_append_none hynot hyu]
      | some j =>
        rw [indexOf_append_of_mem x hy]
        dsimp only
        have hj : j < p.length := hlen ▸ indexOf_lt_length hy
        rw [← hlen, getNth_append_right, getNth_append_left _ _ _ hj]
        have hgt := maxPlusOne_gt (mem_of_getNth hj)
        exact ⟨fun h => by omega, False.elim⟩
    · rw [indexOf_append_none hxnot hxu]
  | some i =>
    rw [indexOf_append_of_mem u hx]
    have hi : i < p.length := hlen ▸ indexOf_lt_length hx
    cases hy : indexOf y F with
    | none =>
      have hynot : y ∉ F := (indexOf_eq_none y F).mp hy
      by_cases hyu : y = u
      · subst hyu
        rw [indexOf_append_self hu]
        dsimp only
        rw [getNth_append_left _ _ _ hi, ← hlen, getNth_append_right]
        have hgt := maxPlusOne_gt (mem_of_getNth hi)
        exact ⟨fun h => by omega, False.elim⟩
      · rw [indexOf_append_none hynot hyu]
    | some j =>
      rw [indexOf_append_of_mem u hy]
      dsimp only
      have hj : j < p.length := hlen ▸ indexOf_lt_length hy
      rw [getNth_append_left _ _ _ hi, getNth_append_left _ _ _ hj]

private lemma relOfList_filter_eq (pred : ℕ → Bool) (F p : List ℕ) (hlen : F.length = p.length)
    {x y : ℕ} (hx : pred x = true) (hy : pred y = true) :
    relOfList (F.filter pred) (projectList (F.map pred) p) x y ↔ relOfList F p x y := by
  unfold relOfList
  by_cases hxy : x = y
  · simp [hxy]
  simp only [hxy, false_or]
  have hpx := projectList_getNth_filter pred F p hlen x hx
  have hpy := projectList_getNth_filter pred F p hlen y hy
  cases hfx : indexOf x (F.filter pred) with
  | none =>
    cases hox : indexOf x F with
    | none => rfl
    | some _ => rw [hfx, hox] at hpx; exact False.elim hpx
  | some jx =>
    cases hox : indexOf x F with
    | none => rw [hfx, hox] at hpx; exact False.elim hpx
    | some ix =>
      rw [hfx, hox] at hpx
      cases hfy : indexOf y (F.filter pred) with
      | none =>
        cases hoy : indexOf y F with
        | none => rfl
        | some _ => rw [hfy, hoy] at hpy; exact False.elim hpy
      | some jy =>
        cases hoy : indexOf y F with
        | none => rw [hfy, hoy] at hpy; exact False.elim hpy
        | some iy =>
          rw [hfy, hoy] at hpy
          dsimp only
          rw [hpx.2.2, hpy.2.2]

private lemma relOfList_canon (F p : List ℕ) (hlen : p.length = F.length) (x y : ℕ) :
    relOfList F (canonListAux [] 0 p) x y ↔ relOfList F p x y := by
  unfold relOfList
  by_cases hxy : x = y
  · simp [hxy]
  simp only [hxy, false_or]
  cases hx : indexOf x F with
  | none => rfl
  | some i =>
    cases hy : indexOf y F with
    | none => rfl
    | some j =>
      have hi : i < p.length := hlen ▸ indexOf_lt_length hx
      have hj : j < p.length := hlen ▸ indexOf_lt_length hy
      exact (canonList_spec p).2.2 i j hi hj

private lemma relOfList_mergeColor {F p : List ℕ} {u v iu iv : ℕ}
    (hlen : p.length = F.length)
    (hu : indexOf u F = some iu) (hv : indexOf v F = some iv)
    (hlo_lt : getNth iu p < getNth iv p) (x y : ℕ) :
    relOfList F (mergeColorList (getNth iu p) (getNth iv p) p) x y ↔
      mergeRel (relOfList F p) u v x y := by
  unfold mergeRel relOfList
  by_cases hxy : x = y
  · simp [hxy]
  simp only [hxy, false_or]
  have hiu : iu < p.length := hlen ▸ indexOf_lt_length hu
  have hiv : iv < p.length := hlen ▸ indexOf_lt_length hv
  cases hx : indexOf x F with
  | none =>
    have hxne_u : x ≠ u := fun h => by rw [h, hu] at hx; cases hx
    have hxne_v : x ≠ v := fun h => by rw [h, hv] at hx; cases hx
    simp [hxne_u, hxne_v]
  | some i =>
    have hi : i < p.length := hlen ▸ indexOf_lt_length hx
    cases hy : indexOf y F with
    | none =>
      have hyne_u : y ≠ u := fun h => by rw [h, hu] at hy; cases hy
      have hyne_v : y ≠ v := fun h => by rw [h, hv] at hy; cases hy
      simp [hyne_u.symm, hyne_v.symm]
    | some j =>
      have hj : j < p.length := hlen ▸ indexOf_lt_length hy
      dsimp only
      rw [getNth_mergeColorList p i hi, getNth_mergeColorList p j hj, mergeColor_eq_iff hlo_lt]
      simp only [hu, hv]
      have hxu : x = u → getNth i p = getNth iu p := fun h => by rw [h, hu] at hx; cases hx; rfl
      have hxv : x = v → getNth i p = getNth iv p := fun h => by rw [h, hv] at hx; cases hx; rfl
      have hyu : y = u → getNth j p = getNth iu p := fun h => by rw [h, hu] at hy; cases hy; rfl
      have hyv : y = v → getNth j p = getNth iv p := fun h => by rw [h, hv] at hy; cases hy; rfl
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Or.inr h1, Or.inr h2.symm⟩)
        · exact Or.inr (Or.inr ⟨Or.inr h1, Or.inr h2.symm⟩)
      · rintro (h | ⟨hx', hy'⟩ | ⟨hx', hy'⟩)
        · exact Or.inl h
        · have h1 : getNth i p = getNth iu p := hx'.elim hxu id
          have h2 : getNth j p = getNth iv p := hy'.elim (fun h => hyv h.symm) Eq.symm
          exact Or.inr (Or.inl ⟨h1, h2⟩)
        · have h1 : getNth i p = getNth iv p := hx'.elim hxv id
          have h2 : getNth j p = getNth iu p := hy'.elim (fun h => hyu h.symm) Eq.symm
          exact Or.inr (Or.inr ⟨h1, h2⟩)

private lemma relOfList_replaceColor {F p : List ℕ} {u v iu iv : ℕ}
    (hlen : p.length = F.length)
    (hu : indexOf u F = some iu) (hv : indexOf v F = some iv) (x y : ℕ) :
    relOfList F (replaceColor (getNth iv p) (getNth iu p) p) x y ↔
      mergeRel (relOfList F p) u v x y := by
  unfold mergeRel relOfList
  by_cases hxy : x = y
  · simp [hxy]
  simp only [hxy, false_or]
  cases hx : indexOf x F with
  | none =>
    have hxne_u : x ≠ u := fun h => by rw [h, hu] at hx; cases hx
    have hxne_v : x ≠ v := fun h => by rw [h, hv] at hx; cases hx
    simp [hxne_u, hxne_v]
  | some i =>
    have hi : i < p.length := hlen ▸ indexOf_lt_length hx
    cases hy : indexOf y F with
    | none =>
      have hyne_u : y ≠ u := fun h => by rw [h, hu] at hy; cases hy
      have hyne_v : y ≠ v := fun h => by rw [h, hv] at hy; cases hy
      simp [hyne_u.symm, hyne_v.symm]
    | some j =>
      have hj : j < p.length := hlen ▸ indexOf_lt_length hy
      dsimp only
      rw [getNth_replaceColor _ _ p i hi, getNth_replaceColor _ _ p j hj]
      simp only [hu, hv]
      have hxu : x = u → getNth i p = getNth iu p := fun h => by rw [h, hu] at hx; cases hx; rfl
      have hxv : x = v → getNth i p = getNth iv p := fun h => by rw [h, hv] at hx; cases hx; rfl
      have hyu : y = u → getNth j p = getNth iu p := fun h => by rw [h, hu] at hy; cases hy; rfl
      have hyv : y = v → getNth j p = getNth iv p := fun h => by rw [h, hv] at hy; cases hy; rfl
      constructor
      · intro heq
        by_cases h1 : getNth i p = getNth iv p <;> by_cases h2 : getNth j p = getNth iv p
        · exact Or.inl (h1.trans h2.symm)
        · simp only [h1, h2, ↓reduceIte] at heq
          exact Or.inr (Or.inr ⟨Or.inr h1, Or.inr heq⟩)
        · simp only [h1, h2, ↓reduceIte] at heq
          exact Or.inr (Or.inl ⟨Or.inr heq, Or.inr h2.symm⟩)
        · simp only [h1, h2, ↓reduceIte] at heq
          exact Or.inl heq
      · rintro (h | ⟨hx', hy'⟩ | ⟨hx', hy'⟩)
        · rw [h]
        · have h1 : getNth i p = getNth iu p := hx'.elim hxu id
          have h2 : getNth j p = getNth iv p := hy'.elim (fun h => hyv h.symm) Eq.symm
          simp [h1, h2]
        · have h1 : getNth i p = getNth iv p := hx'.elim hxv id
          have h2 : getNth j p = getNth iu p := hy'.elim (fun h => hyu h.symm) Eq.symm
          simp [h1, h2]

-- Computable frontier dynamic programming evaluator
private def stepGo (b aSubB negB : Int) (k_in : Nat) (addU addV noForget keepSorted : Bool)
    (idxU idxV : Nat) (keep : List Bool)
    (acc1 acc2 : List (Nat × Int)) : List (Nat × Int) → List (Nat × Int) × List (Nat × Int)
  | [] => (acc1, acc2)
  | (code, val) :: rest =>
    let p0 := unpackPart k_in code
    let p1 := match addU with | true => p0 ++ [maxPlusOne p0] | false => p0
    let p2 := match addV with | true => p1 ++ [maxPlusOne p1] | false => p1
    let cu := getNth idxU p2
    let cv := getNth idxV p2
    match Nat.beq cu cv with
    | true =>
      let cOut := match keepSorted with
        | true => code
        | false => match noForget with | true => packRaw p2 | false => packCanon (projectList keep p2)
      stepGo b aSubB negB k_in addU addV noForget keepSorted idxU idxV keep
        ((cOut, Int.mul val aSubB) :: acc1) acc2 rest
    | false =>
      let cExcl := match keepSorted with
        | true => code
        | false => match noForget with | true => packRaw p2 | false => packCanon (projectList keep p2)
      let cIncl := match noForget with
        | true =>
          match Nat.ble (Nat.add cu 1) cv with
          | true => mergeColorPack cu cv p2
          | false => mergeColorPack cv cu p2
        | false => packCanon (projectList keep (replaceColor cv cu p2))
      match Nat.beq cExcl cIncl with
      | true =>
        stepGo b aSubB negB k_in addU addV noForget keepSorted idxU idxV keep acc1 acc2 rest
      | false =>
        stepGo b aSubB negB k_in addU addV noForget keepSorted idxU idxV keep
          ((cExcl, Int.mul val negB) :: acc1) ((cIncl, Int.mul val b) :: acc2) rest

private def stepEdge (a b : Int) (k_in : Nat) (addU addV : Bool) (idxU idxV : Nat) (keep : List Bool)
    (dp : List (Nat × Int)) : List (Nat × Int) :=
  let noForget := allTrue keep
  let keepSorted := noForget && !addU && !addV
  let (l1, l2) := stepGo b (Int.sub a b) (Int.neg b) k_in addU addV noForget keepSorted idxU idxV keep [] [] dp
  let s1 := match keepSorted with | true => l1.reverse | false => sortSum l1
  mergeSum s1 (sortSum l2)

private def runEdges (a b : Int) (frontier : List Nat) (dp : List (Nat × Int)) :
    List (Nat × Nat) → List (Nat × Int)
  | [] => dp
  | (u, v) :: rest =>
    let k0 := frontier.length
    let (addU, idxU, f1) := match indexOf u frontier with
      | some i => (false, i, frontier)
      | none => (true, k0, frontier ++ [u])
    let k1 := f1.length
    let (addV, idxV, f2) := match indexOf v f1 with
      | some i => (false, i, f1)
      | none => (true, k1, f1 ++ [v])
    let keep := f2.map (fun w => appearsIn w rest)
    let f3 := f2.filter (fun w => appearsIn w rest)
    let dp' := stepEdge a b k0 addU addV idxU idxV keep dp
    runEdges a b f3 dp' rest

private def maxFront (frontier : List Nat) : List (Nat × Nat) → Nat
  | [] => frontier.length
  | (u, v) :: rest =>
    let f1 := match indexOf u frontier with | some _ => frontier | none => frontier ++ [u]
    let f2 := match indexOf v f1 with | some _ => f1 | none => f1 ++ [v]
    let f3 := f2.filter (fun w => appearsIn w rest)
    Nat.max f2.length (maxFront f3 rest)

private def ValidCodes (k : ℕ) (dp : List (ℕ × ℤ)) : Prop :=
  ∀ p ∈ dp, AllLt k (unpackPart k p.1)

private lemma stepGo_sound (a b : ℤ) (F f1 f2 f3 : List ℕ) (u v : ℕ) (rest : List (ℕ × ℕ))
    (addU addV : Bool) (idxU idxV : ℕ)
    (hf1 : f1 = if addU then F ++ [u] else F)
    (haddU : (addU = true ∧ u ∉ F ∧ idxU = F.length) ∨ (addU = false ∧ indexOf u F = some idxU))
    (hf2 : f2 = if addV then f1 ++ [v] else f1)
    (haddV : (addV = true ∧ v ∉ f1 ∧ idxV = f1.length) ∨ (addV = false ∧ indexOf v f1 = some idxV))
    (hf3 : f3 = f2.filter (fun w => appearsIn w rest))
    (hf2_lt : f2.length < 16)
    (acc1 acc2 dp : List (ℕ × ℤ))
    (hdp : ValidCodes F.length dp)
    (ha1 : ValidCodes f3.length acc1) (ha2 : ValidCodes f3.length acc2) :
    let keep := f2.map (fun w => appearsIn w rest)
    let noForget := allTrue keep
    let keepSorted := noForget && !addU && !addV
    let res := stepGo b (Int.sub a b) (Int.neg b) F.length addU addV noForget keepSorted idxU idxV keep acc1 acc2 dp
    ValidCodes f3.length res.1 ∧ ValidCodes f3.length res.2 ∧
    evalList (fun c => listFlowSum a b (relOfCode f3 c) rest) res.1 +
    evalList (fun c => listFlowSum a b (relOfCode f3 c) rest) res.2 =
      evalList (fun c => listFlowSum a b (relOfCode f3 c) rest) acc1 +
      evalList (fun c => listFlowSum a b (relOfCode f3 c) rest) acc2 +
      evalList (fun c => listFlowSum a b (relOfCode F c) ((u, v) :: rest)) dp := by
  induction dp generalizing acc1 acc2 with
  | nil =>
    dsimp only [stepGo]
    refine ⟨ha1, ha2, ?_⟩
    simp [evalList]
  | cons entry tl ih =>
    rcases entry with ⟨code, val⟩
    have hcode : AllLt F.length (unpackPart F.length code) := hdp (code, val) (List.mem_cons_self ..)
    have htl : ValidCodes F.length tl := fun p hp => hdp p (List.mem_cons_of_mem _ hp)
    let p0 := unpackPart F.length code
    have hp0_len : p0.length = F.length := unpackPart_length F.length code
    let p1 := match addU with | true => p0 ++ [maxPlusOne p0] | false => p0
    let p2 := match addV with | true => p1 ++ [maxPlusOne p1] | false => p1
    have hp1_len : p1.length = f1.length := by
      cases addU <;> simp [p1, hf1, hp0_len]
    have hp1_lt : AllLt f1.length p1 := by
      rcases haddU with ⟨rfl, _, _⟩ | ⟨rfl, _⟩
      · simpa [p1, hf1] using allLt_append_maxPlusOne hcode
      · simpa [p1, hf1] using hcode
    have hp2_len : p2.length = f2.length := by
      cases addV <;> simp [p2, hf2, hp1_len]
    have hp2_lt : AllLt f2.length p2 := by
      rcases haddV with ⟨rfl, _, _⟩ | ⟨rfl, _⟩
      · simpa [p2, hf2] using allLt_append_maxPlusOne hp1_lt
      · simpa [p2, hf2] using hp1_lt
    have hp2_lt16 : AllLt 16 p2 := fun d hd => Nat.lt_trans (hp2_lt d hd) hf2_lt
    have hrel_p1 : ∀ x y, relOfList f1 p1 x y ↔ relOfList F p0 x y := by
      intro x y
      rcases haddU with ⟨rfl, hunot, _⟩ | ⟨rfl, _⟩
      · simp only [p1, hf1, ↓reduceIte]
        exact relOfList_append_fresh hunot hp0_len x y
      · simp [p1, hf1]
    have hrel_p2 : ∀ x y, relOfList f2 p2 x y ↔ relOfList F p0 x y := by
      intro x y
      rw [← hrel_p1 x y]
      rcases haddV with ⟨rfl, hvnot, _⟩ | ⟨rfl, _⟩
      · simp only [p2, hf2, ↓reduceIte]
        exact relOfList_append_fresh hvnot hp1_len x y
      · simp [p2, hf2]
    have hidxU : indexOf u f2 = some idxU := by
      have hu1 : indexOf u f1 = some idxU := by
        rcases haddU with ⟨rfl, hunot, rfl⟩ | ⟨rfl, hu⟩
        · simpa [hf1] using indexOf_append_self hunot
        · simpa [hf1] using hu
      rcases haddV with ⟨rfl, _, _⟩ | ⟨rfl, _⟩
      · simpa [hf2] using indexOf_append_of_mem v hu1
      · simpa [hf2] using hu1
    have hidxV : indexOf v f2 = some idxV := by
      rcases haddV with ⟨rfl, hvnot, rfl⟩ | ⟨rfl, hv⟩
      · simpa [hf2] using indexOf_append_self hvnot
      · simpa [hf2] using hv
    let keep := f2.map (fun w => appearsIn w rest)
    let noForget := allTrue keep
    let keepSorted := noForget && !addU && !addV
    have hproj_len : (projectList keep p2).length = f3.length := by
      rw [projectList_length keep p2 (by simp [keep, hp2_len]), hf3, filter_length_eq]
    have hf3_le : f3.length ≤ f2.length := by rw [hf3]; exact List.length_filter_le _ _
    have hf3_lt16 : f3.length < 16 := Nat.lt_of_le_of_lt hf3_le hf2_lt
    -- Helper: cExcl properties
    let cExcl := match keepSorted with
      | true => code
      | false => match noForget with | true => packRaw p2 | false => packCanon (projectList keep p2)
    have hcExcl_valid : AllLt f3.length (unpackPart f3.length cExcl) := by
      dsimp only [cExcl]
      cases hks : keepSorted
      · cases hnf : noForget
        · have hcan := canonList_spec (projectList keep p2)
          have h16 : AllLt 16 (canonListAux [] 0 (projectList keep p2)) :=
            fun d hd => Nat.lt_trans (hcan.2.1 d hd) (hproj_len ▸ hf3_lt16)
          have hunp : unpackPart f3.length (packCanon (projectList keep p2)) =
              canonListAux [] 0 (projectList keep p2) := by
            rw [packCanon, packCanonAux_eq_packRaw, ← hproj_len, ← hcan.1]
            exact unpackPart_packRaw _ h16
          rw [hunp]
          exact hproj_len ▸ hcan.2.1
        · have hf3_eq : f3 = f2 := by rw [hf3]; exact filter_allTrue _ _ hnf
          rw [hf3_eq, ← hp2_len, unpackPart_packRaw p2 hp2_lt16, hp2_len]
          exact hp2_lt
      · have hnf : noForget = true := by
          dsimp only [keepSorted] at hks; revert hks; cases noForget <;> simp
        have haU : addU = false := by
          dsimp only [keepSorted] at hks; revert hks; cases noForget <;> cases addU <;> simp
        have haV : addV = false := by
          dsimp only [keepSorted] at hks; revert hks; cases noForget <;> cases addU <;> cases addV <;> simp
        have hf3_eq : f3 = F := by
          rw [hf3, filter_allTrue _ _ hnf, hf2, haV, hf1, haU]; rfl
        rw [hf3_eq]; exact hcode
    have hcExcl_sum : listFlowSum a b (relOfCode f3 cExcl) rest =
        listFlowSum a b (relOfCode F code) rest := by
      apply listFlowSum_congr
      intro x y hx hy
      have hrelF : relOfCode F code x y ↔ relOfList f2 p2 x y := (hrel_p2 x y).symm
      rw [hrelF]
      dsimp only [relOfCode, cExcl]
      cases hks : keepSorted
      · cases hnf : noForget
        · have hcan := canonList_spec (projectList keep p2)
          have h16 : AllLt 16 (canonListAux [] 0 (projectList keep p2)) :=
            fun d hd => Nat.lt_trans (hcan.2.1 d hd) (hproj_len ▸ hf3_lt16)
          have hunp : unpackPart f3.length (packCanon (projectList keep p2)) =
              canonListAux [] 0 (projectList keep p2) := by
            rw [packCanon, packCanonAux_eq_packRaw, ← hproj_len, ← hcan.1]
            exact unpackPart_packRaw _ h16
          rw [hunp, relOfList_canon f3 (projectList keep p2) hproj_len, hf3]
          exact relOfList_filter_eq (fun w => appearsIn w rest) f2 p2 hp2_len.symm hx hy
        · have hf3_eq : f3 = f2 := by rw [hf3]; exact filter_allTrue _ _ hnf
          rw [hf3_eq, ← hp2_len, unpackPart_packRaw p2 hp2_lt16]
      · have hnf : noForget = true := by
          dsimp only [keepSorted] at hks; revert hks; cases noForget <;> simp
        have haU : addU = false := by
          dsimp only [keepSorted] at hks; revert hks; cases noForget <;> cases addU <;> simp
        have haV : addV = false := by
          dsimp only [keepSorted] at hks; revert hks; cases noForget <;> cases addU <;> cases addV <;> simp
        have hf3_eq : f3 = F := by
          rw [hf3, filter_allTrue _ _ hnf, hf2, haV, hf1, haU]; rfl
        rw [hf3_eq]
        exact (hrel_p2 x y).symm
    let cu := getNth idxU p2
    let cv := getNth idxV p2
    have hrel_uv : relOfCode F code u v ↔ cu = cv := by
      rw [show relOfCode F code u v ↔ relOfList f2 p2 u v from (hrel_p2 u v).symm]
      unfold relOfList
      simp only [hidxU, hidxV]
      constructor
      · rintro (rfl | h)
        · rw [hidxU] at hidxV; cases hidxV; rfl
        · exact h
      · exact Or.inr
    unfold stepGo
    dsimp only
    cases hcc : Nat.beq cu cv
    · -- cu ≠ cv
      have hne : cu ≠ cv := nat_beq_false hcc
      have hnot_rel : ¬ relOfCode F code u v := fun h => hne (hrel_uv.mp h)
      let cIncl := match noForget with
        | true =>
          match Nat.ble (Nat.add cu 1) cv with
          | true => mergeColorPack cu cv p2
          | false => mergeColorPack cv cu p2
        | false => packCanon (projectList keep (replaceColor cv cu p2))
      have hcIncl_valid : AllLt f3.length (unpackPart f3.length cIncl) := by
        dsimp only [cIncl]
        cases hnf : noForget
        · let p2' := replaceColor cv cu p2
          have hp2'_len : (projectList keep p2').length = f3.length := by
            rw [projectList_length keep p2' (by simp [keep, p2', replaceColor_length, hp2_len]),
              hf3, filter_length_eq]
          have hcan := canonList_spec (projectList keep p2')
          have h16 : AllLt 16 (canonListAux [] 0 (projectList keep p2')) :=
            fun d hd => Nat.lt_trans (hcan.2.1 d hd) (hp2'_len ▸ hf3_lt16)
          have hunp : unpackPart f3.length (packCanon (projectList keep p2')) =
              canonListAux [] 0 (projectList keep p2') := by
            rw [packCanon, packCanonAux_eq_packRaw, ← hp2'_len, ← hcan.1]
            exact unpackPart_packRaw _ h16
          rw [hunp]
          exact hp2'_len ▸ hcan.2.1
        · have hf3_eq : f3 = f2 := by rw [hf3]; exact filter_allTrue _ _ hnf
          have hcu_lt : cu < f2.length := hp2_lt cu (mem_of_getNth (hp2_len ▸ indexOf_lt_length hidxU))
          have hcv_lt : cv < f2.length := hp2_lt cv (mem_of_getNth (hp2_len ▸ indexOf_lt_length hidxV))
          cases hlt : Nat.ble (Nat.add cu 1) cv
          · dsimp only
            have hml := mergeColorList_allLt (hi := cu) hcv_lt p2 hp2_lt
            have h16 : AllLt 16 (mergeColorList cv cu p2) := fun d hd => Nat.lt_trans (hml d hd) hf2_lt
            rw [hf3_eq, mergeColorPack_eq_packRaw, ← hp2_len, ← mergeColorList_length cv cu p2,
              unpackPart_packRaw _ h16, mergeColorList_length, hp2_len]
            exact hml
          · dsimp only
            have hml := mergeColorList_allLt (hi := cv) hcu_lt p2 hp2_lt
            have h16 : AllLt 16 (mergeColorList cu cv p2) := fun d hd => Nat.lt_trans (hml d hd) hf2_lt
            rw [hf3_eq, mergeColorPack_eq_packRaw, ← hp2_len, ← mergeColorList_length cu cv p2,
              unpackPart_packRaw _ h16, mergeColorList_length, hp2_len]
            exact hml
      have hcIncl_sum : listFlowSum a b (relOfCode f3 cIncl) rest =
          listFlowSum a b (mergeRel (relOfCode F code) u v) rest := by
        apply listFlowSum_congr
        intro x y hx hy
        have hmr : mergeRel (relOfCode F code) u v x y ↔ mergeRel (relOfList f2 p2) u v x y := by
          change mergeRel (relOfList F p0) u v x y ↔ mergeRel (relOfList f2 p2) u v x y
          simp only [mergeRel, hrel_p2]
        rw [hmr]
        dsimp only [relOfCode, cIncl]
        cases hnf : noForget
        · let p2' := replaceColor cv cu p2
          have hp2'_len : (projectList keep p2').length = f3.length := by
            rw [projectList_length keep p2' (by simp [keep, p2', replaceColor_length, hp2_len]),
              hf3, filter_length_eq]
          have hcan := canonList_spec (projectList keep p2')
          have h16 : AllLt 16 (canonListAux [] 0 (projectList keep p2')) :=
            fun d hd => Nat.lt_trans (hcan.2.1 d hd) (hp2'_len ▸ hf3_lt16)
          have hunp : unpackPart f3.length (packCanon (projectList keep p2')) =
              canonListAux [] 0 (projectList keep p2') := by
            rw [packCanon, packCanonAux_eq_packRaw, ← hp2'_len, ← hcan.1]
            exact unpackPart_packRaw _ h16
          rw [hunp, relOfList_canon f3 (projectList keep p2') hp2'_len, hf3,
            relOfList_filter_eq (fun w => appearsIn w rest) f2 p2' (by rw [replaceColor_length, hp2_len]) hx hy]
          exact relOfList_replaceColor hp2_len hidxU hidxV x y
        · have hf3_eq : f3 = f2 := by rw [hf3]; exact filter_allTrue _ _ hnf
          have hcu_lt : cu < f2.length := hp2_lt cu (mem_of_getNth (hp2_len ▸ indexOf_lt_length hidxU))
          have hcv_lt : cv < f2.length := hp2_lt cv (mem_of_getNth (hp2_len ▸ indexOf_lt_length hidxV))
          cases hlt : Nat.ble (Nat.add cu 1) cv
          · dsimp only
            have hcvu : cv < cu := by have : cv < cu + 1 := nat_ble_false hlt; omega
            have hml := mergeColorList_allLt (hi := cu) hcv_lt p2 hp2_lt
            have h16 : AllLt 16 (mergeColorList cv cu p2) := fun d hd => Nat.lt_trans (hml d hd) hf2_lt
            rw [hf3_eq, mergeColorPack_eq_packRaw, ← hp2_len, ← mergeColorList_length cv cu p2,
              unpackPart_packRaw _ h16, relOfList_mergeColor hp2_len hidxV hidxU hcvu x y]
            unfold mergeRel; tauto
          · dsimp only
            have hcuv : cu < cv := by have : cu + 1 ≤ cv := nat_ble_true hlt; omega
            have hml := mergeColorList_allLt (hi := cv) hcu_lt p2 hp2_lt
            have h16 : AllLt 16 (mergeColorList cu cv p2) := fun d hd => Nat.lt_trans (hml d hd) hf2_lt
            rw [hf3_eq, mergeColorPack_eq_packRaw, ← hp2_len, ← mergeColorList_length cu cv p2,
              unpackPart_packRaw _ h16, relOfList_mergeColor hp2_len hidxU hidxV hcuv x y]
      have hstep_val : listFlowSum a b (relOfCode F code) ((u, v) :: rest) =
          (-b) * listFlowSum a b (relOfCode f3 cExcl) rest +
          b * listFlowSum a b (relOfCode f3 cIncl) rest := by
        rw [listFlowSum]
        simp only [hnot_rel, ↓reduceIte, hcExcl_sum, hcIncl_sum]
      cases heq_c : Nat.beq cExcl cIncl
      · have ha1' : ValidCodes f3.length ((cExcl, Int.mul val (Int.neg b)) :: acc1) := by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp'; exact hcExcl_valid; exact ha1 p hp'
        have ha2' : ValidCodes f3.length ((cIncl, Int.mul val b) :: acc2) := by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp'; exact hcIncl_valid; exact ha2 p hp'
        rcases ih ((cExcl, Int.mul val (Int.neg b)) :: acc1) ((cIncl, Int.mul val b) :: acc2) htl ha1' ha2' with
          ⟨hv1, hv2, hsum⟩
        refine ⟨hv1, hv2, ?_⟩
        rw [hsum, evalList_cons, evalList_cons, evalList_cons, hstep_val]
        change val * -b * listFlowSum a b (relOfCode f3 cExcl) rest + _ +
          (val * b * listFlowSum a b (relOfCode f3 cIncl) rest + _) + _ = _
        ring
      · have hceq : cExcl = cIncl := nat_beq_true heq_c
        rcases ih acc1 acc2 htl ha1 ha2 with ⟨hv1, hv2, hsum⟩
        refine ⟨hv1, hv2, ?_⟩
        rw [hsum, evalList_cons, hstep_val, hceq]
        ring
    · -- cu = cv
      have heq_uv : cu = cv := nat_beq_true hcc
      have hrel : relOfCode F code u v := hrel_uv.mpr heq_uv
      have hstep_val : listFlowSum a b (relOfCode F code) ((u, v) :: rest) =
          (a - b) * listFlowSum a b (relOfCode f3 cExcl) rest := by
        rw [listFlowSum]
        simp only [hrel, ↓reduceIte, hcExcl_sum]
        ring
      have ha1' : ValidCodes f3.length ((cExcl, Int.mul val (Int.sub a b)) :: acc1) := by
        intro p hp; rcases List.mem_cons.mp hp with rfl | hp'; exact hcExcl_valid; exact ha1 p hp'
      rcases ih ((cExcl, Int.mul val (Int.sub a b)) :: acc1) acc2 htl ha1' ha2 with ⟨hv1, hv2, hsum⟩
      refine ⟨hv1, hv2, ?_⟩
      rw [hsum, evalList_cons, evalList_cons, hstep_val]
      have hmul : Int.mul val (Int.sub a b) = val * (a - b) := rfl
      rw [hmul]
      ring

private lemma runEdges_sound (a b : ℤ) (F : List ℕ) (dp : List (ℕ × ℤ)) (es : List (ℕ × ℕ))
    (hmax : maxFront F es < 16) (hdp : ValidCodes F.length dp) :
    evalList (fun c => listFlowSum a b (relOfCode F c) es) dp =
      ((runEdges a b F dp es).map Prod.snd).sum := by
  induction es generalizing F dp with
  | nil =>
    simp only [runEdges, evalList, listFlowSum, mul_one]
  | cons e rest ih =>
    rcases e with ⟨u, v⟩
    dsimp only [maxFront] at hmax
    dsimp only [runEdges]
    set k0 := F.length
    let rU := match indexOf u F with
      | some i => (false, i, F)
      | none => (true, k0, F ++ [u])
    let addU := rU.1
    let idxU := rU.2.1
    let f1 := rU.2.2
    have haddU : (addU = true ∧ u ∉ F ∧ idxU = F.length) ∨ (addU = false ∧ indexOf u F = some idxU) := by
      dsimp only [addU, idxU, rU]
      cases hu : indexOf u F with
      | none => exact Or.inl ⟨rfl, (indexOf_eq_none u F).mp hu, rfl⟩
      | some i => exact Or.inr ⟨rfl, rfl⟩
    have hf1 : f1 = if addU then F ++ [u] else F := by
      cases h : indexOf u F <;> simp [f1, addU, rU, h]
    have hf1_eq : (match indexOf u F with | some _ => F | none => F ++ [u]) = f1 := by
      cases h : indexOf u F <;> simp [f1, rU, h]
    let rV := match indexOf v f1 with
      | some i => (false, i, f1)
      | none => (true, f1.length, f1 ++ [v])
    let addV := rV.1
    let idxV := rV.2.1
    let f2 := rV.2.2
    have haddV : (addV = true ∧ v ∉ f1 ∧ idxV = f1.length) ∨ (addV = false ∧ indexOf v f1 = some idxV) := by
      dsimp only [addV, idxV, rV]
      cases hv : indexOf v f1 with
      | none => exact Or.inl ⟨rfl, (indexOf_eq_none v f1).mp hv, rfl⟩
      | some i => exact Or.inr ⟨rfl, rfl⟩
    have hf2 : f2 = if addV then f1 ++ [v] else f1 := by
      cases h : indexOf v f1 <;> simp [f2, addV, rV, h]
    have hf2_eq : (match indexOf v f1 with | some _ => f1 | none => f1 ++ [v]) = f2 := by
      cases h : indexOf v f1 <;> simp [f2, rV, h]
    let f3 := f2.filter (fun w => appearsIn w rest)
    rw [hf1_eq, hf2_eq] at hmax
    have hf2_lt : f2.length < 16 := lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest : maxFront f3 rest < 16 := lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hstep := stepGo_sound a b F f1 f2 f3 u v rest addU addV idxU idxV
      hf1 haddU hf2 haddV rfl hf2_lt [] [] dp hdp (fun _ h => by cases h) (fun _ h => by cases h)
    rcases hstep with ⟨hv1, hv2, hsum⟩
    let keep := f2.map (fun w => appearsIn w rest)
    let dp' := stepEdge a b k0 addU addV idxU idxV keep dp
    have hdp'_valid : ValidCodes f3.length dp' := by
      unfold ValidCodes dp' stepEdge
      dsimp only
      apply allKeys_mergeSum (P := fun c => AllLt f3.length (unpackPart f3.length c))
      · cases hks : allTrue keep && !addU && !addV
        · dsimp only
          have hv1' : ValidCodes f3.length
              (stepGo b (Int.sub a b) (Int.neg b) k0 addU addV (allTrue keep) false idxU idxV keep [] [] dp).1 := by
            simpa only [keep, k0, hks] using hv1
          exact allKeys_sortSum (P := fun c => AllLt f3.length (unpackPart f3.length c)) hv1'
        · dsimp only
          have hv1' : ValidCodes f3.length
              (stepGo b (Int.sub a b) (Int.neg b) k0 addU addV (allTrue keep) true idxU idxV keep [] [] dp).1 := by
            simpa only [keep, k0, hks] using hv1
          intro p hp; exact hv1' p (List.mem_reverse.mp hp)
      · exact allKeys_sortSum (P := fun c => AllLt f3.length (unpackPart f3.length c)) hv2
    have hdp'_eval : evalList (fun c => listFlowSum a b (relOfCode f3 c) rest) dp' =
        evalList (fun c => listFlowSum a b (relOfCode F c) ((u, v) :: rest)) dp := by
      unfold dp' stepEdge
      dsimp only
      rw [evalList_mergeSum, evalList_sortSum]
      have hs1 : evalList (fun c => listFlowSum a b (relOfCode f3 c) rest)
          (match allTrue keep && !addU && !addV with
           | true => (stepGo b (Int.sub a b) (Int.neg b) k0 addU addV (allTrue keep)
               (allTrue keep && !addU && !addV) idxU idxV keep [] [] dp).1.reverse
           | false => sortSum (stepGo b (Int.sub a b) (Int.neg b) k0 addU addV (allTrue keep)
               (allTrue keep && !addU && !addV) idxU idxV keep [] [] dp).1) =
          evalList (fun c => listFlowSum a b (relOfCode f3 c) rest)
            (stepGo b (Int.sub a b) (Int.neg b) k0 addU addV (allTrue keep)
              (allTrue keep && !addU && !addV) idxU idxV keep [] [] dp).1 := by
        cases allTrue keep && !addU && !addV
        · exact evalList_sortSum _ _
        · exact evalList_reverse _ _
      rw [hs1, hsum]
      simp [evalList]
    rw [← hdp'_eval]
    exact ih f3 dp' hmax_rest hdp'_valid

private lemma runEdges_eq_listFlowSum (a b : ℤ) (es : List (ℕ × ℕ)) (hmax : maxFront [] es < 16) :
    listFlowSum a b Eq es = ((runEdges a b [] [(0, 1)] es).map Prod.snd).sum := by
  have hsound := runEdges_sound a b [] [(0, 1)] es hmax (by
    intro p hp; rcases List.mem_singleton.mp hp with rfl; intro d hd; cases hd)
  rw [← hsound]
  simp only [evalList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
  apply listFlowSum_congr
  intro x y _ _
  simp [relOfCode, relOfList, indexOf]

-- =========================================================================
-- Part 4: 28-Vertex Counterexample Witness & Disproof of Welsh's Conjecture
-- =========================================================================

private def edges28 : List (ℕ × ℕ) :=
  [(2,16), (1,2), (2,3), (3,4), (3,23), (4,5), (4,19), (0,1), (1,10), (27,0),
   (5,27), (5,6), (26,27), (0,21), (16,17), (17,26), (17,18), (18,19), (19,20),
   (11,18), (10,11), (15,16), (11,12), (20,21), (14,20), (14,15), (13,14), (12,13),
   (6,12), (21,22), (22,23), (6,7), (7,22), (13,24), (23,24), (25,26), (24,25),
   (8,15), (7,8), (9,25), (9,10), (8,9)]

private lemma edges28_lt : ListEdgesLt 28 edges28 := by
  intro p hp
  simp only [edges28, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl <;> decide

set_option maxRecDepth 20000 in
private lemma edges28_maxFront : maxFront [] edges28 < 16 := by decide

private def src28 (e : Fin edges28.length) : Fin 28 :=
  ⟨(edges28.get e).1, (edges28_lt _ (List.get_mem edges28 e)).1⟩

private def tgt28 (e : Fin edges28.length) : Fin 28 :=
  ⟨(edges28.get e).2, (edges28_lt _ (List.get_mem edges28 e)).2⟩

private def flow4Vals : List (ZMod 4) :=
  [1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1,
   2, 2, 1, 3, 3, 2, 1, 3, 2, 3, 3, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3]

private def flow4_28 (e : Fin edges28.length) : ZMod 4 :=
  flow4Vals.get (e.cast (by decide))

private lemma flow4_28_nz : ∀ e : Fin edges28.length, flow4_28 e ≠ 0 := by decide

private lemma flow4_28_bal :
    ∀ v : Fin 28,
      (∑ e ∈ Finset.univ.filter (fun e => tgt28 e = v), flow4_28 e) =
      ∑ e ∈ Finset.univ.filter (fun e => src28 e = v), flow4_28 e := by decide

private lemma nzFlowCount_edges28_four_pos : 0 < nzFlowCount src28 tgt28 4 := by
  unfold nzFlowCount
  rw [Nat.card_pos_iff]
  refine ⟨⟨flow4_28, flow4_28_nz, fun v => by convert flow4_28_bal v⟩, inferInstance⟩

private lemma disproof_of_dp_val
    (hdp : ((runEdges 41 10 [] [(0, 1)] edges28).map Prod.snd).sum =
      -13546133249059719000000000000000000000000000) :
    ¬ (∀ (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V) (F : Polynomial ℝ),
        (∀ k : ℕ, 1 ≤ k → F.eval (k : ℝ) = nzFlowCount src tgt k) → F ≠ 0 →
        ∀ x : ℝ, F.IsRoot x → x ≤ 4) := by
  intro hmain
  let F : Polynomial ℝ := flowPoly src28 tgt28
  have hFeval : ∀ k : ℕ, 1 ≤ k → F.eval (k : ℝ) = (nzFlowCount src28 tgt28 k : ℝ) :=
    fun k hk => flowPoly_eval_nat src28 tgt28 k hk
  have hF4 : 0 < F.eval (4 : ℝ) := by
    have h4 := hFeval 4 (by omega)
    have hpos : (0 : ℝ) < (nzFlowCount src28 tgt28 4 : ℝ) :=
      Nat.cast_pos.mpr nzFlowCount_edges28_four_pos
    simpa using h4.symm ▸ hpos
  have hFne : F ≠ 0 := by
    intro h0
    rw [h0, Polynomial.eval_zero] at hF4
    exact lt_irrefl 0 hF4
  have hF41 : F.eval ((41 : ℝ) / (10 : ℝ)) < 0 := by
    have hscaled : (10 : ℝ) ^ edges28.length * F.eval ((41 : ℝ) / (10 : ℝ)) =
        (listFlowSum 41 10 Eq edges28 : ℝ) :=
      listFlowSum_eq_scaled_flowPoly 41 10 (by norm_num : ((10 : ℤ) : ℝ) ≠ 0) 28 edges28 edges28_lt
    have hrun : listFlowSum 41 10 Eq edges28 =
        -13546133249059719000000000000000000000000000 := by
      rw [runEdges_eq_listFlowSum 41 10 edges28 edges28_maxFront, hdp]
    rw [hrun] at hscaled
    have hneg : (10 : ℝ) ^ edges28.length * F.eval ((41 : ℝ) / (10 : ℝ)) < 0 := by
      rw [hscaled]
      norm_num
    have hpow : (0 : ℝ) < (10 : ℝ) ^ edges28.length := by positivity
    nlinarith
  have hmem : (0 : ℝ) ∈ Set.Icc (F.eval ((41 : ℝ) / (10 : ℝ))) (F.eval (4 : ℝ)) :=
    ⟨le_of_lt hF41, le_of_lt hF4⟩
  have hcont : ContinuousOn (fun x : ℝ => F.eval x) (Set.Icc (4 : ℝ) ((41 : ℝ) / (10 : ℝ))) :=
    F.continuous.continuousOn
  rcases intermediate_value_Icc' (by norm_num : (4 : ℝ) ≤ (41 : ℝ) / (10 : ℝ)) hcont hmem with
    ⟨x, hxIcc, hx0⟩
  have hxle : x ≤ 4 := hmain (Fin 28) (Fin edges28.length) src28 tgt28 F hFeval hFne x hx0
  have hxeq : x = 4 := le_antisymm hxle hxIcc.1
  rw [hxeq] at hx0
  linarith

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
private lemma edges28_dp_eval :
    ((runEdges 41 10 [] [(0, 1)] edges28).map Prod.snd).sum =
      -13546133249059719000000000000000000000000000 := by decide

end FlowDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_real_roots_of_the_flow_polynomial.main) :=
  FlowDisproof.disproof_of_dp_val FlowDisproof.edges28_dp_eval

