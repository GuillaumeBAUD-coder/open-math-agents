import FormalConjectures.ErdosProblems.«1017»
import Mathlib

-- Credit: @grp06

/-!
The balanced construction starts with a complete bipartite graph and adds edges
inside one side, as in the Erdős Problem a Day report on problem 1017.
Here we allow arbitrary internal edges and any size of the independent side.
Summing a linear lower bound on the number of internal edges used by each
partition clique gives the family of estimates indexed by the slope.

Near the complete graph, adding every missing edge as one block lets us use
the de Bruijn–Erdős incidence argument. The report gives its one-missing-edge
case. See https://erdosproblemaday.com/report/1017.
-/

section

open Finset SimpleGraph

namespace OMA.CliqueLowerBound

variable {V : Type*}

private theorem samePart {G : SimpleGraph V} {P : Finset (Finset V)}
    (hP : G.IsCliqueEdgePartition P) {C D : Finset V} (hC : C ∈ P) (hD : D ∈ P)
    {u v : V} (huv : G.Adj u v) (huC : u ∈ C) (hvC : v ∈ C)
    (huD : u ∈ D) (hvD : v ∈ D) : C = D := by
  obtain ⟨F, _, hF⟩ := hP.2 u v huv
  exact (hF C ⟨hC, huC, hvC⟩).trans (hF D ⟨hD, huD, hvD⟩).symm

variable [DecidableEq V]

private def completeEdges [Fintype V] (S : Finset V) : Finset (Sym2 V) :=
  ((⊤ : SimpleGraph S).map (Function.Embedding.subtype (· ∈ S))).edgeFinset

private theorem mem_completeEdges [Fintype V] (S : Finset V) (u v : V) :
    s(u, v) ∈ completeEdges S ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  rw [completeEdges, mem_edgeFinset, mem_edgeSet, map_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨a.property, b.property, fun h => hab.ne (Subtype.ext h)⟩
  · rintro ⟨hu, hv, huv⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, (fun h => huv (congrArg Subtype.val h)), rfl, rfl⟩

private theorem card_completeEdges [Fintype V] (S : Finset V) :
    (completeEdges S).card = S.card.choose 2 := by
  rw [completeEdges, card_edgeFinset_map, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_coe]

private theorem completeEdges_subset_top [Fintype V] (S : Finset V) :
    completeEdges S ⊆ (⊤ : SimpleGraph V).edgeFinset :=
  edgeFinset_mono le_top

private def crossEdges (B A : Finset V) : Finset (Sym2 V) :=
  (B ×ˢ A).image fun p => s(p.1, p.2)

private theorem mem_crossEdges (B A : Finset V) (u v : V) :
    s(u, v) ∈ crossEdges B A ↔ (u ∈ B ∧ v ∈ A) ∨ (v ∈ B ∧ u ∈ A) := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨hv, hu⟩, Sym2.eq_swap⟩

private theorem card_crossEdges {B A : Finset V} (hBA : Disjoint B A) :
    (crossEdges B A).card = B.card * A.card := by
  rw [crossEdges, Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨u, v⟩ hp ⟨x, y⟩ hq heq
  have ⟨hu, hv⟩ := Finset.mem_product.mp hp
  have ⟨hx, hy⟩ := Finset.mem_product.mp hq
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact ((Finset.disjoint_left.mp hBA) hu hy).elim

private theorem crossEdges_subset_top [Fintype V] {B A : Finset V} (hBA : Disjoint B A) :
    crossEdges B A ⊆ (⊤ : SimpleGraph V).edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    rw [mem_edgeFinset, mem_edgeSet, top_adj]
    intro huv
    subst v
    rcases (mem_crossEdges B A u u).mp he with h | h
    all_goals exact (Finset.disjoint_left.mp hBA) h.1 h.2

private theorem disjoint_crossEdges_completeEdges [Fintype V] {B A : Finset V} (hBA : Disjoint B A) :
    Disjoint (crossEdges B A) (completeEdges B) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he hf
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨hu, hv, _⟩ := (mem_completeEdges B u v).mp hf
    rcases (mem_crossEdges B A u v).mp he with h | h
    · exact (Finset.disjoint_left.mp hBA) hv h.2
    · exact (Finset.disjoint_left.mp hBA) hu h.2

private theorem twiceChooseTwo (s : ℕ) : 2 * s.choose 2 + s = s * s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

private theorem triangularSupport (r s : ℕ) : r * s ≤ (r + 1).choose 2 + s.choose 2 := by
  have hS := twiceChooseTwo s
  have hR := twiceChooseTwo (r + 1)
  zify at hS hR ⊢
  rcases le_or_gt s r with h | h
  · have hgap : (0 : ℤ) ≤ (r : ℤ) - s := by omega
    have hgap' : (0 : ℤ) ≤ (r : ℤ) - s + 1 := by omega
    nlinarith [mul_nonneg hgap hgap']
  · have hgap : (0 : ℤ) ≤ (s : ℤ) - r := by omega
    have hgap' : (0 : ℤ) ≤ (s : ℤ) - r - 1 := by omega
    nlinarith [mul_nonneg hgap hgap']

private theorem countPartitions [Fintype V] {B A : Finset V} {G : SimpleGraph V}
    {I : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hP : G.IsCliqueEdgePartition P) (hA : A.Nonempty) (r : ℕ)
    (hcross : ∀ u ∈ B, ∀ v ∈ A, G.Adj u v)
    (hindep : ∀ u ∈ B, ∀ v ∈ B, ¬G.Adj u v)
    (hinside : ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → s(u, v) ∈ I) :
    B.card ≤ P.card ∧
      r * (B.card * A.card) ≤ P.card * (r + 1).choose 2 + I.card := by
  classical
  let X (C : Finset V) := (C ∩ B) ×ˢ (C ∩ A)
  let J (C : Finset V) := completeEdges (C ∩ A)
  have hXB : (P : Set (Finset V)).PairwiseDisjoint X := by
    intro C hC D hD hne
    apply Finset.disjoint_left.mpr
    rintro ⟨u, v⟩ hX hY
    have ⟨hu, hv⟩ := Finset.mem_product.mp hX
    have ⟨hu', hv'⟩ := Finset.mem_product.mp hY
    obtain ⟨huC, huB⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvC, hvA⟩ := Finset.mem_inter.mp hv
    exact hne (samePart hP hC hD (hcross u huB v hvA) huC hvC
      (Finset.mem_inter.mp hu').1 (Finset.mem_inter.mp hv').1)
  have hXcover : P.biUnion X = B ×ˢ A := by
    ext p
    constructor
    · intro hp
      obtain ⟨C, _, hpC⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hpC
      exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
    · intro hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      obtain ⟨C, ⟨hCP, huC, hvC⟩, _⟩ := hP.2 _ _ (hcross _ hu _ hv)
      exact Finset.mem_biUnion.mpr ⟨C, hCP,
        Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨huC, hu⟩, Finset.mem_inter.mpr ⟨hvC, hv⟩⟩⟩
  have hJB : (P : Set (Finset V)).PairwiseDisjoint J := by
    intro C hC D hD hne
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨hu, hv, huv⟩ := (mem_completeEdges _ u v).mp he
      obtain ⟨hu', hv', _⟩ := (mem_completeEdges _ u v).mp hf
      have huC := (Finset.mem_inter.mp hu).1
      have hvC := (Finset.mem_inter.mp hv).1
      have hadj := (hP.1 C hC).2 huC hvC huv
      exact hne (samePart hP hC hD hadj huC hvC
        (Finset.mem_inter.mp hu').1 (Finset.mem_inter.mp hv').1)
  have hJsub : P.biUnion J ⊆ I := by
    intro e he
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨hu, hv, huv⟩ := (mem_completeEdges _ u v).mp heC
      obtain ⟨huC, huA⟩ := Finset.mem_inter.mp hu
      obtain ⟨hvC, hvA⟩ := Finset.mem_inter.mp hv
      exact hinside u huA v hvA ((hP.1 C hC).2 huC hvC huv)
  have hBsingle (C : Finset V) (hC : C ∈ P) {u v : V}
      (hu : u ∈ C ∩ B) (hv : v ∈ C ∩ B) : u = v := by
    obtain ⟨huC, huB⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvC, hvB⟩ := Finset.mem_inter.mp hv
    by_contra huv
    exact hindep u huB v hvB ((hP.1 C hC).2 huC hvC huv)
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := hA
    have hex (u : B) : ∃ C, C ∈ P ∧ u.val ∈ C ∧ v ∈ C :=
      (hP.2 u.val v (hcross _ u.property _ hv)).exists
    choose C hC using hex
    let pick (u : B) : P := ⟨C u, (hC u).1⟩
    apply Finset.card_le_card_of_injective (f := pick)
    intro x y hxy
    have heq : C x = C y := congrArg Subtype.val hxy
    apply Subtype.ext
    exact hBsingle (C x) (hC x).1
      (Finset.mem_inter.mpr ⟨(hC x).2.1, x.property⟩)
      (Finset.mem_inter.mpr ⟨heq ▸ (hC y).2.1, y.property⟩)
  · have hcountX : ∑ C ∈ P, (X C).card = B.card * A.card := by
      rw [← Finset.card_biUnion hXB, hXcover, Finset.card_product]
    have hcountJ : ∑ C ∈ P, (J C).card ≤ I.card := by
      rw [← Finset.card_biUnion hJB]
      exact Finset.card_le_card hJsub
    have hlocal (C : Finset V) (hC : C ∈ P) :
        r * (X C).card ≤ (r + 1).choose 2 + (J C).card := by
      have hcard : (C ∩ B).card ≤ 1 :=
        Finset.card_le_one.mpr (fun _ hu _ hv => hBsingle C hC hu hv)
      have hx : (X C).card ≤ (C ∩ A).card := by
        change ((C ∩ B) ×ˢ (C ∩ A)).card ≤ _
        rw [Finset.card_product]
        simpa using Nat.mul_le_mul_right (C ∩ A).card hcard
      simpa only [J, card_completeEdges] using
        (triangularSupport r (X C).card).trans
          (Nat.add_le_add_left (Nat.choose_le_choose 2 hx) _)
    have hs := Finset.sum_le_sum hlocal
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcountX] at hs
    exact (by simpa using hs : _ ≤ _ + ∑ C ∈ P, (J C).card).trans
      (Nat.add_le_add_left hcountJ _)

private def slopeBound (r b k : ℕ) : ℕ :=
  let d := (r + 1).choose 2
  ((r + 1) * b - k + (d - 1)) / d

private theorem edgeSet_from_finset [Fintype V] (E : Finset (Sym2 V))
    (hE : E ⊆ (⊤ : SimpleGraph V).edgeFinset) :
    (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 V))).edgeSet = ↑E := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact Set.Subset.antisymm
    (fun _ he => he.1)
    (fun _ he => ⟨he, not_isDiag_of_mem_edgeFinset (G := ⊤) (hE he)⟩)

private theorem boundForSide (n k a r : ℕ) (ha : a < n) (hr : 0 < r)
    (hb : a * (n - a) ≤ k) (hcap : k + a.choose 2 ≤ n.choose 2) :
    max a (slopeBound r (a * (n - a)) k) ≤ Erdos1017.f n k := by
  classical
  obtain ⟨B, _, hB⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ (α := Fin n)) (by simpa using ha.le)
  let A : Finset (Fin n) := Bᶜ
  let T := (⊤ : SimpleGraph (Fin n)).edgeFinset
  let H := completeEdges B
  let X := crossEdges B A
  have hAcard : A.card = n - a := by simp [A, Finset.card_compl, hB]
  have hA : A.Nonempty := Finset.card_pos.mp (by rw [hAcard]; omega)
  have hBA : Disjoint B A := Finset.disjoint_left.mpr
    (fun _ hB' hA' => (Finset.mem_compl.mp hA') hB')
  have hTcard : T.card = n.choose 2 := by
    change (⊤ : SimpleGraph (Fin n)).edgeFinset.card = _
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  have hHcard : H.card = a.choose 2 := by
    change (completeEdges B).card = _
    rw [card_completeEdges, hB]
  have hXcard : X.card = a * (n - a) := by
    change (crossEdges B A).card = _
    rw [card_crossEdges hBA, hB, hAcard]
  have hXT : X ⊆ T := crossEdges_subset_top hBA
  have hHT : H ⊆ T := completeEdges_subset_top B
  have hXH : Disjoint X H := disjoint_crossEdges_completeEdges hBA
  have hXallowed : X ⊆ T \ H :=
    fun e he => Finset.mem_sdiff.mpr ⟨hXT he, fun hf => (Finset.disjoint_left.mp hXH) he hf⟩
  have hpool : k - a * (n - a) ≤ ((T \ H) \ X).card := by
    rw [Finset.card_sdiff_of_subset hXallowed, Finset.card_sdiff_of_subset hHT,
      hTcard, hHcard, hXcard]
    omega
  obtain ⟨I, hI, hIcard⟩ := Finset.exists_subset_card_eq hpool
  have hXI : Disjoint X I := Finset.disjoint_left.mpr
    (fun _ hX hI' => (Finset.mem_sdiff.mp (hI hI')).2 hX)
  have hUI : X ∪ I ⊆ T := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hXT he
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hI he)).1).1
  let G := SimpleGraph.fromEdgeSet (↑(X ∪ I) : Set (Sym2 (Fin n)))
  have hG : G.edgeSet = (↑(X ∪ I) : Set (Sym2 (Fin n))) :=
    edgeSet_from_finset _ hUI
  have hGadj (u v : Fin n) : G.Adj u v ↔ s(u, v) ∈ X ∪ I := by
    rw [← mem_edgeSet, hG]
    rfl
  have hGcard : G.edgeSet.ncard = k := by
    rw [hG, Set.ncard_coe_finset, Finset.card_union_of_disjoint hXI, hXcard, hIcard]
    omega
  obtain ⟨P, hP, hPcard⟩ := Erdos1017.partition_card_le_f n k G hGcard
  have hcross (u : Fin n) (hu : u ∈ B) (v : Fin n) (hv : v ∈ A) : G.Adj u v := by
    apply (hGadj u v).mpr
    exact Finset.mem_union_left _ ((mem_crossEdges B A u v).mpr (Or.inl ⟨hu, hv⟩))
  have hindep (u : Fin n) (hu : u ∈ B) (v : Fin n) (hv : v ∈ B) : ¬G.Adj u v := by
    intro huv
    have hem := (hGadj u v).mp huv
    have hemH : s(u, v) ∈ H := (mem_completeEdges B u v).mpr ⟨hu, hv, huv.ne⟩
    rcases Finset.mem_union.mp hem with he | he
    · exact (Finset.disjoint_left.mp hXH) he hemH
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hI he)).1).2 hemH
  have hinside (u : Fin n) (hu : u ∈ A) (v : Fin n) (hv : v ∈ A) (huv : G.Adj u v) :
      s(u, v) ∈ I := by
    have hem := (hGadj u v).mp huv
    refine (Finset.mem_union.mp hem).resolve_left ?_
    intro hemX
    rcases (mem_crossEdges B A u v).mp hemX with h | h
    · exact (Finset.disjoint_left.mp hBA) h.1 hu
    · exact (Finset.disjoint_left.mp hBA) h.1 hv
  obtain ⟨hside, hcount⟩ := countPartitions hP hA r hcross hindep hinside
  rw [hB, hAcard, hIcard] at hcount
  rw [hB] at hside
  refine max_le (hside.trans hPcard) ?_
  have hd : 0 < (r + 1).choose 2 := Nat.choose_pos (by omega)
  apply Nat.lt_succ_iff.mp
  apply (Nat.div_lt_iff_lt_mul hd).mpr
  rw [Nat.succ_mul r, Nat.succ_mul (Erdos1017.f n k)]
  have hprod := Nat.mul_le_mul_right ((r + 1).choose 2) hPcard
  omega

/-- The incidence-vector proof of the de Bruijn–Erdős inequality for finite linear spaces. -/
private theorem properCompletePartition [Fintype V] [Nontrivial V]
    {Q : Finset (Finset V)} (hQ : (⊤ : SimpleGraph V).IsCliqueEdgePartition Q)
    (hproper : ∀ C ∈ Q, C ≠ Finset.univ) : Fintype.card V ≤ Q.card := by
  classical
  let through (u : V) := Q.filter (fun C => u ∈ C)
  have hpair (u v : V) (huv : u ≠ v) : ∃! C, C ∈ Q ∧ u ∈ C ∧ v ∈ C :=
    hQ.2 u v huv
  have hdegree (u : V) : 2 ≤ (through u).card := by
    obtain ⟨v, hv⟩ := exists_ne u
    obtain ⟨C, ⟨hCQ, huC, _⟩, _⟩ := hpair u v hv.symm
    obtain ⟨w, hw⟩ : ∃ w, w ∉ C := by
      by_contra! hall
      exact hproper C hCQ (Finset.eq_univ_iff_forall.mpr hall)
    have huw : u ≠ w := fun h => hw (h ▸ huC)
    obtain ⟨D, ⟨hDQ, huD, hwD⟩, _⟩ := hpair u w huw
    have hCD : C ≠ D := fun h => hw (h ▸ hwD)
    have hsub : {C, D} ⊆ through u :=
      Finset.insert_subset (Finset.mem_filter.mpr ⟨hCQ, huC⟩)
        (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hDQ, huD⟩))
    simpa only [Finset.card_pair hCD] using Finset.card_le_card hsub
  have hgram (u v : V) :
      (∑ C ∈ through u, if v ∈ C then (1 : ℚ) else 0) =
        if v = u then ((through u).card : ℚ) else 1 := by
    rw [Finset.sum_boole]
    by_cases huv : v = u
    · subst v
      rw [if_pos rfl, Finset.filter_true_of_mem]
      exact fun C hC => (Finset.mem_filter.mp hC).2
    · obtain ⟨C, ⟨hCQ, huC, hvC⟩, huniq⟩ := hpair u v (Ne.symm huv)
      have hfilter : (through u).filter (fun D => v ∈ D) = {C} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hCQ, huC⟩, hvC⟩, ?_⟩
        intro D hD
        obtain ⟨hDu, hvD⟩ := Finset.mem_filter.mp hD
        obtain ⟨hDQ, huD⟩ := Finset.mem_filter.mp hDu
        exact huniq D ⟨hDQ, huD, hvD⟩
      rw [hfilter, if_neg huv, Finset.card_singleton, Nat.cast_one]
  let row (u : V) (C : Q) : ℚ := if u ∈ C.val then 1 else 0
  have hinj : LinearIndependent ℚ row := by
    apply Fintype.linearIndependent_iff.mpr
    intro z hz
    have hcol (C : Finset V) (hC : C ∈ Q) :
        (∑ v, z v * (if v ∈ C then (1 : ℚ) else 0)) = 0 := by
      have hzC := congrFun hz (⟨C, hC⟩ : Q)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, row] using hzC
    let S := ∑ v, z v
    let d (u : V) : ℚ := (through u).card - 1
    have hpos (u : V) : 0 < d u := by
      have h : 1 < (through u).card := by have := hdegree u; omega
      exact sub_pos.mpr (by exact_mod_cast h)
    have heq (u : V) : S + d u * z u = 0 := by
      calc
        S + d u * z u = ∑ v, (z v + if v = u then d u * z v else 0) := by
          rw [Finset.sum_add_distrib]
          simp [S]
        _ = ∑ v, z v * (∑ C ∈ through u, if v ∈ C then (1 : ℚ) else 0) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hgram]
          split_ifs with h
          · subst v
            dsimp [d]
            ring
          · ring
        _ = ∑ C ∈ through u, ∑ v, z v * (if v ∈ C then (1 : ℚ) else 0) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = 0 := Finset.sum_eq_zero (fun C hC => hcol C (Finset.mem_filter.mp hC).1)
    have hS : S = 0 := by
      rcases le_or_gt S 0 with hs | hs
      · have hzpos (v : V) : 0 ≤ z v :=
          nonneg_of_mul_nonneg_left (by linarith [heq v]) (hpos v)
        exact le_antisymm hs (Finset.sum_nonneg (fun v _ => hzpos v))
      · have hzneg (v : V) : z v ≤ 0 :=
          nonpos_of_mul_nonpos_left (by linarith [heq v]) (hpos v)
        exact (hs.not_ge (Finset.sum_nonpos (fun v _ => hzneg v))).elim
    intro u
    have hzero : d u * z u = 0 := by linarith [heq u]
    exact (mul_eq_zero.mp hzero).resolve_left (hpos u).ne'
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    hinj.fintype_card_le_finrank

private theorem completeWithMissingEdges (n k : ℕ) (hn : 2 < n) (hk : k < n.choose 2) :
    n - (n.choose 2 - k) ≤ Erdos1017.f n k := by
  classical
  let T := (⊤ : SimpleGraph (Fin n)).edgeFinset
  have hT : T.card = n.choose 2 := by
    change (⊤ : SimpleGraph (Fin n)).edgeFinset.card = _
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  obtain ⟨E, hE, hEc⟩ := Finset.exists_subset_card_eq (s := T) (n := k) (by rw [hT]; exact hk.le)
  let G := SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))
  have hG : G.edgeSet = (↑E : Set (Sym2 (Fin n))) := edgeSet_from_finset _ hE
  have hGadj (u v : Fin n) : G.Adj u v ↔ s(u, v) ∈ E := by
    rw [← mem_edgeSet, hG]
    rfl
  have hGcard : G.edgeSet.ncard = k := by rw [hG, Set.ncard_coe_finset, hEc]
  obtain ⟨P, hP, hPc⟩ := Erdos1017.partition_card_le_f n k G hGcard
  let M := T \ E
  let Q := P ∪ M.image Sym2.toFinset
  have hM : M.card = n.choose 2 - k := by
    change (T \ E).card = _
    rw [Finset.card_sdiff_of_subset hE, hT, hEc]
  have hnotTop : G ≠ ⊤ := by
    intro h
    rw [h, ← coe_edgeFinset, Set.ncard_coe_finset,
      card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hGcard
    omega
  have hmissing (u v : Fin n) (huv : u ≠ v) (h : ¬G.Adj u v) : s(u,v) ∈ M := by
    refine Finset.mem_sdiff.mpr ⟨?_, fun he => h ((hGadj u v).mpr he)⟩
    change s(u, v) ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset
    rwa [mem_edgeFinset, mem_edgeSet, top_adj]
  have honlyMissing {C : Finset (Fin n)} (hC : C ∈ M.image Sym2.toFinset)
      {u v : Fin n} (huv : u ≠ v) (huC : u ∈ C) (hvC : v ∈ C) :
      C = s(u, v).toFinset ∧ ¬G.Adj u v := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    have heq := (Sym2.mem_and_mem_iff huv).mp
      ⟨Sym2.mem_toFinset.mp huC, Sym2.mem_toFinset.mp hvC⟩
    subst e
    exact ⟨rfl, fun h => (Finset.mem_sdiff.mp he).2 ((hGadj u v).mp h)⟩
  have hQ : (⊤ : SimpleGraph (Fin n)).IsCliqueEdgePartition Q := by
    constructor
    · intro C hC
      refine ⟨?_, fun _ _ _ _ h => h⟩
      rcases Finset.mem_union.mp hC with hp | hm
      · exact (hP.1 C hp).1
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
        exact le_of_eq <| (Sym2.card_toFinset_of_not_isDiag e
          (not_isDiag_of_mem_edgeFinset (G := ⊤) (Finset.mem_sdiff.mp he).1)).symm
    · intro u v huv
      by_cases h : G.Adj u v
      · obtain ⟨C, ⟨hCP, huC, hvC⟩, huniq⟩ := hP.2 u v h
        refine ⟨C, ⟨Finset.mem_union_left _ hCP, huC, hvC⟩, ?_⟩
        intro D hD
        obtain ⟨hDQ, huD, hvD⟩ := hD
        rcases Finset.mem_union.mp hDQ with hp | hm
        · exact huniq D ⟨hp, huD, hvD⟩
        · exact ((honlyMissing hm huv.ne huD hvD).2 h).elim
      · refine ⟨s(u, v).toFinset, ⟨Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (hmissing u v huv.ne h)), by simp, by simp⟩, ?_⟩
        intro C hC
        obtain ⟨hCQ, huC, hvC⟩ := hC
        rcases Finset.mem_union.mp hCQ with hp | hm
        · exact (h ((hP.1 C hp).2 huC hvC huv.ne)).elim
        · exact (honlyMissing hm huv.ne huC hvC).1
  have hproper (C : Finset (Fin n)) (hC : C ∈ Q) : C ≠ Finset.univ := by
    rcases Finset.mem_union.mp hC with hp | hm
    · intro heq
      apply hnotTop
      ext u v
      rw [top_adj]
      exact ⟨fun h => h.ne, fun h =>
        (hP.1 C hp).2 (heq ▸ Finset.mem_univ u) (heq ▸ Finset.mem_univ v) h⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
      intro heq
      have hcard := Sym2.card_toFinset_of_not_isDiag e
        (not_isDiag_of_mem_edgeFinset (G := ⊤) (Finset.mem_sdiff.mp he).1)
      rw [heq, Finset.card_univ, Fintype.card_fin] at hcard
      omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsum : Q.card ≤ P.card + M.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have hnQ := properCompletePartition hQ hproper
  rw [Fintype.card_fin] at hnQ
  omega

end OMA.CliqueLowerBound

/-- The best split-side estimate and the incidence estimate for dense graphs. -/
def OMA.answer (n k : ℕ) : ℕ :=
  let total := n * (n - 1) / 2
  max (if k < total then n - (total - k) else 1)
    ((Finset.range n).sup fun a =>
      if a * (n - a) ≤ k ∧ k + a * (a - 1) / 2 ≤ total then
        (Finset.range (n - a)).sup fun t =>
          max a (OMA.CliqueLowerBound.slopeBound (t + 1) (a * (n - a)) k)
      else 0)

theorem OMA.solution : Erdos1017.erdos_1017.lower_bound.answer = OMA.answer →
    type_of% @Erdos1017.erdos_1017.lower_bound := by
  intro h
  rw [h]
  intro n k hk hdensity
  have hn : 2 < n := by
    by_contra! hs
    interval_cases n <;> norm_num at hk hdensity <;> omega
  simp only [OMA.answer, ← Nat.choose_two_right]
  apply max_le
  · split_ifs with hmissing
    · exact OMA.CliqueLowerBound.completeWithMissingEdges n k hn hmissing
    · have hlin : n - 1 ≤ n.choose 2 := by
        cases n with
        | zero => simp
        | succ v =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          omega
      have hcross : 1 * (n - 1) ≤ k := by omega
      have hcap : k + Nat.choose 1 2 ≤ n.choose 2 := by simpa using hk
      have hside := OMA.CliqueLowerBound.boundForSide n k 1 1 (by omega) (by decide) hcross hcap
      exact (le_max_left _ _).trans hside
  · apply Finset.sup_le
    intro a ha
    split_ifs with h
    · apply Finset.sup_le
      intro t _
      exact OMA.CliqueLowerBound.boundForSide n k a (t + 1)
        (Finset.mem_range.mp ha) (Nat.zero_lt_succ t) h.1 h.2
    · exact Nat.zero_le _

end
