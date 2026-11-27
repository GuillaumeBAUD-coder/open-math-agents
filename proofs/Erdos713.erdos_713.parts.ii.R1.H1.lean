import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Tactic

open SimpleGraph
open scoped Classical
namespace Forest713
theorem tree_copy {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (T : SimpleGraph A) (D : SimpleGraph B) (ht : T.IsTree)
    (hd : ∀ x, Fintype.card A ≤ D.degree x) : T ⊑ D := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl hs =>
    let b : B := Classical.choice ‹Nonempty B›
    refine ⟨⟨⟨fun _ => b, ?_⟩, ?_⟩⟩
    · intro x y h
      exact (h.ne (Subsingleton.elim _ _)).elim
    · intro x y _
      exact Subsingleton.elim _ _
  | inr hn =>
    obtain ⟨v, hv⟩ := ht.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, hu, hu_unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    let S : Set A := {v}ᶜ
    have hS : Fintype.card S < Fintype.card A := by
      change Fintype.card ↥({v}ᶜ : Set A) < _
      rw [Fintype.card_compl_set, @Fintype.card_unique ↥({v} : Set A)]
      have := Fintype.card_pos (α := A)
      omega
    have ht' : (T.induce S).IsTree :=
      ⟨ht.connected.induce_compl_singleton_of_degree_eq_one hv, ht.isAcyclic.induce S⟩
    obtain ⟨f⟩ := tree_copy (T.induce S) D ht' (fun x => hS.le.trans (hd x))
    let u' : S := ⟨u, by simpa [S] using hu.ne.symm⟩
    let used := Finset.univ.image (fun a : S => f a)
    have hused : used.card < (D.neighborFinset (f u')).card := by
      calc used.card ≤ Fintype.card S := by simpa [used] using
             (Finset.card_image_le (f := fun a : S => f a) (s := Finset.univ))
           _ < Fintype.card A := hS
           _ ≤ _ := hd _
    obtain ⟨b, hb, hbfree⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
    have fresh (a : S) : b ≠ f a := fun e => hbfree (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a))
    let g (a : A) : B := if ha : a ∈ S then f ⟨a, ha⟩ else b
    have gv : g v = b := by simp [g, S]
    have gs (a : S) : g a.val = f a := by simp [g, a.property]
    have extend {a : A} (ha : T.Adj v a) : D.Adj (g v) (g a) := by
      rw [hu_unique a ha]
      rw [gv, show g u = f u' from gs u']
      exact ((D.mem_neighborFinset _ _).mp hb).symm
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro a d had
      by_cases ha : a = v
      · exact ha ▸ extend (ha ▸ had)
      by_cases hd' : d = v
      · subst d
        exact (extend had.symm).symm
      let a' : S := ⟨a, by simpa [S] using ha⟩
      let d' : S := ⟨d, by simpa [S] using hd'⟩
      rw [show g a = f a' from gs a', show g d = f d' from gs d']
      exact f.toHom.map_adj (show (T.induce S).Adj a' d' from had)
    · intro a d heq
      change g a = g d at heq
      by_cases ha : a ∈ S <;> by_cases hd' : d ∈ S
      · exact congrArg Subtype.val (f.injective (by simpa [g, ha, hd'] using heq))
      · exact (fresh ⟨a, ha⟩ (by simpa [g, ha, hd'] using heq.symm)).elim
      · exact (fresh ⟨d, hd'⟩ (by simpa [g, ha, hd'] using heq)).elim
      · simp [S] at ha hd'
        exact ha.trans hd'.symm
termination_by Fintype.card A
decreasing_by exact hS

theorem forest_free_edges {A B : Type} [Fintype A] [Fintype B] (G : SimpleGraph A)
    (D : SimpleGraph B) (hg : G.IsAcyclic) (hf : G.Free D) :
    D.edgeFinset.card ≤ Fintype.card A * Fintype.card B := by
  classical
  cases isEmpty_or_nonempty B with
  | inl h => simp [Subsingleton.elim D ⊥]
  | inr h =>
    cases isEmpty_or_nonempty A with
    | inl h =>
      exact (hf ⟨⟨⟨isEmptyElim, fun {x} => isEmptyElim x⟩, fun {x} => isEmptyElim x⟩⟩).elim
    | inr h =>
      by_cases high : ∀ b, Fintype.card A ≤ D.degree b
      · obtain ⟨T, hGT, _, ht⟩ := connected_top.exists_isTree_le_of_le_of_isAcyclic le_top hg
        exact (hf ((IsContained.of_le hGT).trans (tree_copy T D ht high))).elim
      push Not at high
      obtain ⟨b, hb⟩ := high
      let S : Set B := {b}ᶜ
      have hS : Fintype.card S + 1 = Fintype.card B := by
        have := Fintype.card_pos (α := B)
        change Fintype.card ↥({b}ᶜ : Set B) + 1 = _
        rw [Fintype.card_compl_set, @Fintype.card_unique ↥({b} : Set B)]
        omega
      have hf' : G.Free (D.induce S) := fun hc => hf (hc.trans ⟨Copy.induce D S⟩)
      have small := forest_free_edges G (D.induce S) hg hf'
      change (D.induce {b}ᶜ).edgeFinset.card ≤ _ at small
      rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet] at small
      rw [← hS, Nat.mul_add, Nat.mul_one]
      omega
termination_by Fintype.card B
decreasing_by exact Nat.lt_of_succ_le hS.le

theorem forest_extremal_le {q : ℕ} (G : SimpleGraph (Fin q)) (hg : G.IsAcyclic) (n : ℕ) :
    extremalNumber n G ≤ q * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro D dec hD
  rw [Subsingleton.elim dec (fun a b => Classical.propDecidable (D.Adj a b))]
  simpa only [Fintype.card_fin] using forest_free_edges G D hg hD


end Forest713

namespace Peel713
theorem fresh_nbr {B : Type} [Fintype B] (D : SimpleGraph B) (p : B) (I : Finset B)
    (h : I.card < D.degree p) : ∃ z, D.Adj p z ∧ z ∉ I := by
  obtain ⟨z, hz, hzI⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show I.card < (D.neighborFinset p).card by rwa [card_neighborFinset_eq_degree])
  exact ⟨z, (D.mem_neighborFinset _ _).mp hz, hzI⟩

theorem extend_one {A B : Type} (G : SimpleGraph A) (D : SimpleGraph B) (v : A)
    (f : Copy (G.induce ({v}ᶜ : Set A)) D) (z : B)
    (hz : ∀ a : ({v}ᶜ : Set A), f a ≠ z)
    (hadj : ∀ a (ha : a ≠ v), G.Adj v a → D.Adj z (f ⟨a, ha⟩)) :
    ∃ g : Copy G D, g v = z ∧ ∀ a (ha : a ≠ v), g a = f ⟨a, ha⟩ := by
  let g (a : A) : B := if ha : a = v then z else f ⟨a, ha⟩
  have gv : g v = z := by simp [g]
  have gs (a : A) (ha : a ≠ v) : g a = f ⟨a, ha⟩ := by simp [g, ha]
  refine ⟨⟨⟨g, ?_⟩, ?_⟩, gv, gs⟩
  · intro a d had
    by_cases ha : a = v
    · subst ha
      have hd : d ≠ a := had.ne.symm
      rw [gv, gs d hd]
      exact hadj d hd had
    by_cases hd : d = v
    · subst hd
      have ha' : a ≠ d := had.ne
      rw [gv, gs a ha']
      exact (hadj a ha' had.symm).symm
    rw [gs a ha, gs d hd]
    exact f.toHom.map_adj (show (G.induce ({v}ᶜ : Set A)).Adj ⟨a, ha⟩ ⟨d, hd⟩ from had)
  · intro a d heq
    change g a = g d at heq
    by_cases ha : a = v <;> by_cases hd : d = v
    · exact ha.trans hd.symm
    · subst ha
      rw [gv, gs d hd] at heq
      exact (hz _ heq.symm).elim
    · subst hd
      rw [gv, gs a ha] at heq
      exact (hz _ heq).elim
    · rw [gs a ha, gs d hd] at heq
      exact congrArg Subtype.val (f.injective heq)

/-- The image of a copy of `G.induce {v}ᶜ` is small. -/
theorem image_card_lt {A B : Type} [Fintype A] (G : SimpleGraph A) (D : SimpleGraph B) (v : A)
    (f : Copy (G.induce ({v}ᶜ : Set A)) D) :
    (Finset.univ.image (fun a : ({v}ᶜ : Set A) => f a)).card < Fintype.card A := by
  calc (Finset.univ.image (fun a : ({v}ᶜ : Set A) => f a)).card
        ≤ Fintype.card ({v}ᶜ : Set A) := Finset.card_image_le
    _ < Fintype.card A := by
        rw [Fintype.card_compl_set, @Fintype.card_unique ↥({v} : Set A)]
        have := Fintype.card_pos_iff.mpr ⟨v⟩
        omega

theorem not_mem_image {A B : Type} [Fintype A] {G : SimpleGraph A} {D : SimpleGraph B} {v : A}
    (f : Copy (G.induce ({v}ᶜ : Set A)) D) {z : B}
    (hz : z ∉ Finset.univ.image (fun a : ({v}ᶜ : Set A) => f a)) (a : ({v}ᶜ : Set A)) :
    f a ≠ z := fun e => hz (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a))

theorem big_of_adj {A B : Type} [Fintype A] [Fintype B] {D : SimpleGraph B}
    (hd : ∀ b, D.degree b = 0 ∨ Fintype.card A ≤ D.degree b) {p y : B} (h : D.Adj p y) :
    Fintype.card A ≤ D.degree p := by
  have hpos : 0 < D.degree p := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨y, (D.mem_neighborFinset _ _).mpr h⟩
  rcases hd p with h0 | h1
  · omega
  · exact h1

/-- Core embedding step: a copy of `G - v` in a graph whose degrees are all `0` or large
extends to a copy of `G`, when `v` has degree at most one and `G - v` has an edge. -/
theorem base {A B : Type} [Fintype A] [Fintype B] (G : SimpleGraph A) (v : A)
    (hv : G.degree v ≤ 1) (x y : ({v}ᶜ : Set A)) (hxy : (G.induce ({v}ᶜ : Set A)).Adj x y)
    (D : SimpleGraph B) (hd : ∀ b, D.degree b = 0 ∨ Fintype.card A ≤ D.degree b)
    (hJ : G.induce ({v}ᶜ : Set A) ⊑ D) : G ⊑ D := by
  obtain ⟨f⟩ := hJ
  have hfx : Fintype.card A ≤ D.degree (f x) := big_of_adj hd (f.toHom.map_adj hxy)
  by_cases hn : ∃ u, G.Adj v u
  swap
  · push Not at hn
    obtain ⟨z, -, hzI⟩ := fresh_nbr D (f x) _ ((image_card_lt G D v f).trans_le hfx)
    obtain ⟨g, -⟩ := extend_one G D v f z (not_mem_image f hzI)
      (fun a _ h => (hn a h).elim)
    exact ⟨g⟩
  obtain ⟨u, hu⟩ := hn
  have huniq : ∀ a, G.Adj v a → a = u := by
    intro a ha
    have h1 : a ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr ha
    have h2 : u ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr hu
    exact Finset.card_le_one.mp (by rwa [card_neighborFinset_eq_degree]) _ h1 _ h2
  have huv : u ≠ v := hu.ne.symm
  let u' : ({v}ᶜ : Set A) := ⟨u, huv⟩
  -- extending any copy whose image of `u` has large degree
  have leaf : ∀ F : Copy (G.induce ({v}ᶜ : Set A)) D,
      Fintype.card A ≤ D.degree (F u') → G ⊑ D := by
    intro F hF
    obtain ⟨z, hzadj, hzI⟩ := fresh_nbr D (F u') _ ((image_card_lt G D v F).trans_le hF)
    obtain ⟨g, -⟩ := extend_one G D v F z (not_mem_image F hzI) (by
      intro a ha hva
      have : a = u := huniq a hva
      subst this
      exact hzadj.symm)
    exact ⟨g⟩
  rcases hd (f u') with h0 | h1
  swap
  · exact leaf f h1
  -- `f u'` is isolated, hence so is `u'` in `G - v`; re-embed `u'` next to `f x`.
  have hiso : ∀ w, ¬ (G.induce ({v}ᶜ : Set A)).Adj u' w := by
    intro w hw
    have := big_of_adj hd (f.toHom.map_adj hw)
    have hA : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨v⟩
    change Fintype.card A ≤ D.degree (f u') at this
    omega
  obtain ⟨y', hy'adj, hy'I⟩ := fresh_nbr D (f x) _ ((image_card_lt G D v f).trans_le hfx)
  let J := G.induce ({v}ᶜ : Set A)
  let f₀ : Copy (J.induce ({u'}ᶜ : Set ({v}ᶜ : Set A))) D := f.comp (Copy.induce J _)
  obtain ⟨F, hFu, -⟩ := extend_one J D u' f₀ y'
    (fun a => not_mem_image f hy'I a.val)
    (fun a _ h => (hiso a h).elim)
  apply leaf F
  rw [hFu]
  exact big_of_adj hd hy'adj.symm


theorem peel_edges {A B : Type} [Fintype A] [Fintype B] (G : SimpleGraph A) (v : A)
    (hbase : ∀ D : SimpleGraph B, (∀ b, D.degree b = 0 ∨ Fintype.card A ≤ D.degree b) →
       G.Free D → (G.induce ({v}ᶜ : Set A)).Free D) (k : ℕ) :
    ∀ D : SimpleGraph B, D.support.ncard = k → G.Free D →
    Nat.card D.edgeSet ≤ extremalNumber (Fintype.card B) (G.induce ({v}ᶜ : Set A)) +
      Fintype.card A * D.support.ncard := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
  intro D hk hf
  by_cases high : ∀ b, D.degree b = 0 ∨ Fintype.card A ≤ D.degree b
  · have := card_edgeFinset_le_extremalNumber (hbase D high hf)
    rw [edgeFinset_card, ← Nat.card_eq_fintype_card] at this
    omega
  push Not at high
  obtain ⟨b, hb0, hbA⟩ := high
  have hf' : G.Free (D.deleteIncidenceSet b) := fun h =>
    hf (h.trans (IsContained.of_le (D.deleteIncidenceSet_le b)))
  have hbmem : b ∈ D.support := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp
      (show 0 < (D.neighborFinset b).card by rw [card_neighborFinset_eq_degree]; omega)
    exact ⟨w, (D.mem_neighborFinset _ _).mp hw⟩
  have hcard : (D.deleteIncidenceSet b).support.ncard ≤ D.support.ncard - 1 := by
    rw [← Set.ncard_sdiff_singleton_of_mem hbmem]
    exact Set.ncard_le_ncard (support_deleteIncidenceSet_subset D b)
  have hpos : 0 < D.support.ncard := (Set.ncard_pos).mpr ⟨b, hbmem⟩
  have ih' := ih _ (by omega) (D.deleteIncidenceSet b) rfl hf'
  have he := card_edgeFinset_deleteIncidenceSet D b
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at he
  have hdeg := D.degree_le_card_edgeFinset (v := b)
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at hdeg
  have hmul := Nat.mul_le_mul_left (Fintype.card A)
    (show (D.deleteIncidenceSet b).support.ncard + 1 ≤ D.support.ncard by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

/-- Extremal numbers of `G` and `G - v` differ by a linear amount. -/
theorem extremal_le_peel {q : ℕ} (G : SimpleGraph (Fin q)) (v : Fin q) (hv : G.degree v ≤ 1)
    (x y : ({v}ᶜ : Set (Fin q))) (hxy : (G.induce ({v}ᶜ : Set (Fin q))).Adj x y) (n : ℕ) :
    extremalNumber n G ≤ extremalNumber n (G.induce ({v}ᶜ : Set (Fin q))) + q * n := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro D dec hD
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card]
  have := peel_edges G v (fun D hd hf hJ => hf (base G v hv x y hxy D hd hJ)) _ D rfl hD
  have hle : D.support.ncard ≤ n := by
    simpa using Set.ncard_le_card D.support
  have := Nat.mul_le_mul_left q hle
  simp only [Fintype.card_fin] at *
  omega

end Peel713

open Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_ii_R1.H1 := by
  intro q G hb he ⟨v, hv⟩
  by_cases hac : G.IsAcyclic
  · left
    refine IsBigO.of_bound (q : ℝ) (Eventually.of_forall fun n => ?_)
    simp only [Real.norm_natCast]
    exact_mod_cast Forest713.forest_extremal_le G hac n
  right
  have h3 : 3 ≤ G.edgeFinset.card := by
    simp only [IsAcyclic, not_forall, not_not] at hac
    obtain ⟨w, c, hc⟩ := hac
    have hsub : c.edges.toFinset ⊆ G.edgeFinset := by
      intro e he
      rw [List.mem_toFinset] at he
      exact mem_edgeFinset.mpr (c.edges_subset_edgeSet he)
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hc.edges_nodup, c.length_edges] at this
    have := hc.three_le_length
    omega
  have hJe : 2 ≤ (G.induce ({v}ᶜ : Set (Fin q))).edgeFinset.card := by
    have h1 := card_edgeFinset_induce_compl_singleton G v
    rw [card_edgeFinset_deleteIncidenceSet] at h1
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at h1 h3 ⊢
    omega
  obtain ⟨x, y, hxy⟩ : ∃ x y : ({v}ᶜ : Set (Fin q)), (G.induce ({v}ᶜ : Set (Fin q))).Adj x y := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega :
      0 < (G.induce ({v}ᶜ : Set (Fin q))).edgeFinset.card)
    induction e using Sym2.ind with
    | h x y => exact ⟨x, y, mem_edgeFinset.mp he⟩
  let S : Set (Fin q) := {v}ᶜ
  let e := Fintype.equivFin S
  let J := (G.induce S).map e.toEmbedding
  let iso : G.induce S ≃g J := Iso.map e (G.induce S)
  refine ⟨Fintype.card S, J, ?_, ?_, ?_, ?_⟩
  · change Fintype.card ↥({v}ᶜ : Set (Fin q)) < q
    rw [Fintype.card_compl_set, @Fintype.card_unique ↥({v} : Set (Fin q)), Fintype.card_fin]
    have : 0 < q := Fin.pos v
    omega
  · exact Colorable.of_hom ((Embedding.induce S).toHom.comp iso.symm.toHom) hb
  · have h := Nat.card_congr iso.mapEdgeSet
    change 2 ≤ (G.induce S).edgeFinset.card at hJe
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at hJe ⊢
    omega
  · refine IsBigO.of_bound (q : ℝ) (Eventually.of_forall fun n => ?_)
    have hiso : extremalNumber n J = extremalNumber n (G.induce S) :=
      extremalNumber_congr_right iso.symm
    have hlo : extremalNumber n (G.induce S) ≤ extremalNumber n G :=
      IsContained.extremalNumber_le ⟨Copy.induce G S⟩
    have hhi := Peel713.extremal_le_peel G v (by omega) x y hxy n
    rw [hiso]
    have hlo' : (extremalNumber n (G.induce S) : ℝ) ≤ extremalNumber n G := by exact_mod_cast hlo
    have hhi' : (extremalNumber n G : ℝ) ≤ extremalNumber n (G.induce S) + q * n := by
      exact_mod_cast hhi
    rw [Real.norm_eq_abs, Real.norm_natCast, abs_le]
    constructor <;> linarith

