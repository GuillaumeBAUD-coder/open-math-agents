import FormalConjectures.Arxiv.«2507.17780».«1»

-- Reduction Arxiv.2507.17780.tx_graffiti_conjecture_1.R1 of TxGraffiti Conjecture 1: independence, annihilation, and residue
-- Credit: @divo12
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1

/-- Favaron–Mahéo–Saclé (1991; also Griggs–Kleitman 1994, Triesch 1996): the Havel–Hakimi
residue of every finite simple graph is at most its independence number. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.residue ≤ G.indepNum

/-- The Caro–Wei bound: the independence number of every finite simple graph is at least
the sum over all vertices of `1 / (deg v + 1)`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (G.indepNum : ℝ)

open SimpleGraph Finset

theorem annih_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.annihilationNumber * G.maxDegree + #G.edgeFinset ≤ Fintype.card V * G.maxDegree := by
  unfold annihilationNumber
  have hne : ((Finset.Iic (degreeMultiset G)).filter
      (fun S ↦ Multiset.sum S ≤ #G.edgeFinset)).Nonempty :=
    ⟨0, by simp⟩
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup _ hne Multiset.card
  rw [hSeq]
  simp only [Finset.mem_filter, Finset.mem_Iic] at hS
  obtain ⟨hle, hsum⟩ := hS
  set T := degreeMultiset G - S with hT
  have hST : S + T = degreeMultiset G := add_tsub_cancel_of_le hle
  have hcard : Multiset.card S + Multiset.card T = Fintype.card V := by
    rw [← Multiset.card_add, hST]; simp [degreeMultiset]
  have hsum2 : Multiset.sum S + Multiset.sum T = 2 * #G.edgeFinset := by
    rw [← Multiset.sum_add, hST, ← G.sum_degrees_eq_twice_card_edges]
    rfl
  have hTle : Multiset.sum T ≤ Multiset.card T * G.maxDegree := by
    have := Multiset.sum_le_card_nsmul T G.maxDegree (by
      intro x hx
      have hx' : x ∈ degreeMultiset G := Multiset.mem_of_le tsub_le_self hx
      simp only [degreeMultiset, Multiset.mem_map] at hx'
      obtain ⟨v, -, rfl⟩ := hx'
      exact G.degree_le_maxDegree v)
    simpa using this
  rw [← hcard, add_mul]
  omega

theorem class_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) (E : Finset (Sym2 V))
    (hE : ∀ x ∈ X, ∀ y ∈ X, G.Adj x y → s(x, y) ∈ E) :
    #X ≤ G.indepNum + #E := by
  set B := E.image (fun e => e.out.1) with hB
  have hI : G.IsIndepSet (↑(X \ B) : Set V) := by
    intro x hx y hy _ hadj
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx hy
    have he := hE x hx.1 y hy.1 hadj
    have hm := Sym2.out_fst_mem s(x, y)
    rw [Sym2.mem_iff] at hm
    rcases hm with hm | hm
    · exact hx.2 (Finset.mem_image.mpr ⟨_, he, hm⟩)
    · exact hy.2 (Finset.mem_image.mpr ⟨_, he, hm⟩)
  have h1 := hI.card_le_indepNum
  have h2 : #B ≤ #E := Finset.card_image_le
  have h3 : #X ≤ #(X \ B) + #B := Finset.card_le_card_sdiff_add_card
  omega

theorem two_alpha_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.Connected) :
    2 * Fintype.card V ≤ 2 * G.indepNum + #G.edgeFinset + 1 := by
  classical
  obtain ⟨T, hTG, hT⟩ := h.exists_isTree_le
  obtain ⟨C⟩ := hT.isAcyclic.colorable_two
  have hTcard := hT.card_edgeFinset
  let X : Fin 2 → Finset V := fun i => Finset.univ.filter (fun x => C x = i)
  let E : Fin 2 → Finset (Sym2 V) :=
    fun i => G.edgeFinset.filter (fun e => ∀ x ∈ e, C x = i)
  have hb : ∀ i, #(X i) ≤ G.indepNum + #(E i) := by
    intro i
    apply class_bound
    intro x hx y hy hadj
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    simp only [E, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
    refine ⟨hadj, ?_⟩
    intro z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  have hX : #(X 0) + #(X 1) = Fintype.card V := by
    have := Finset.card_eq_sum_card_fiberwise (f := C) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Fin.sum_univ_two] at this
    simpa [X] using this.symm
  have hsub : E 0 ∪ E 1 ⊆ G.edgeFinset \ T.edgeFinset := by
    intro e he
    rw [Finset.mem_union] at he
    rw [Finset.mem_sdiff]
    have key : ∀ i, e ∈ E i → e ∈ G.edgeFinset ∧ e ∉ T.edgeFinset := by
      intro i hi
      simp only [E, Finset.mem_filter] at hi
      refine ⟨hi.1, ?_⟩
      intro hTe
      induction e using Sym2.ind with
      | _ x y =>
        rw [mem_edgeFinset, mem_edgeSet] at hTe
        have hx := hi.2 x (Sym2.mem_mk_left x y)
        have hy := hi.2 y (Sym2.mem_mk_right x y)
        exact C.valid hTe (hx.trans hy.symm)
    rcases he with he | he
    · exact key 0 he
    · exact key 1 he
  have hdisj : Disjoint (E 0) (E 1) := by
    rw [Finset.disjoint_left]
    intro e h0 h1
    simp only [E, Finset.mem_filter] at h0 h1
    have := (h0.2 _ (Sym2.out_fst_mem e)).symm.trans (h1.2 _ (Sym2.out_fst_mem e))
    exact absurd this (by decide)
  have hcardU := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff_of_subset (edgeFinset_mono hTG)] at hcardU
  have hTle : #T.edgeFinset ≤ #G.edgeFinset := Finset.card_le_card (edgeFinset_mono hTG)
  have h0 := hb 0
  have h1 := hb 1
  omega

theorem cw_algebra {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℕ) (hD : 3 ≤ G.maxDegree)
    (ha : a * G.maxDegree + #G.edgeFinset ≤ Fintype.card V * G.maxDegree) :
    (a : ℝ) ≤ ((G.maxDegree : ℝ) - 1) * ∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1) := by
  set D : ℝ := (G.maxDegree : ℝ) with hDdef
  have hD3 : (3 : ℝ) ≤ D := by rw [hDdef]; exact_mod_cast hD
  have hper : ∀ v, 2 * D - (G.degree v : ℝ) ≤
      2 * D * (D - 1) * (1 / ((G.degree v : ℝ) + 1)) := by
    intro v
    have hd := G.degree_le_maxDegree v
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rcases eq_or_lt_of_le hd with h | h
    · have : (G.degree v : ℝ) = D := by rw [hDdef]; exact_mod_cast h
      rw [this]; nlinarith
    · have h' : (G.degree v : ℝ) + 1 ≤ D := by rw [hDdef]; exact_mod_cast h
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ D - G.degree v)
        (by linarith : (0 : ℝ) ≤ D - G.degree v - 1)]
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hper v)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hdeg : (∑ v, (G.degree v : ℝ)) = 2 * #G.edgeFinset := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hdeg] at hsum
  have ha' : (a : ℝ) * D + #G.edgeFinset ≤ Fintype.card V * D := by
    rw [hDdef]; exact_mod_cast ha
  have hDpos : (0 : ℝ) < D := by linarith
  have : 2 * D * a ≤ 2 * D * ((D - 1) * ∑ v, (1 : ℝ) / ((G.degree v : ℝ) + 1)) := by
    nlinarith
  exact le_of_mul_le_mul_left this (by linarith)

theorem main : H1 → H2 → type_of% @Arxiv.«2507.17780».tx_graffiti_conjecture_1 := by
  intro h1 h2 V _ _ G _ hconn hD
  have hR : (residue G : ℝ) ≤ G.indepNum := by
    have := h1 V G
    exact_mod_cast (by convert this)
  have hW := h2 V G
  have hA := annih_bound G
  have hDpos : (0 : ℝ) < G.maxDegree := by exact_mod_cast (by omega : 0 < G.maxDegree)
  rw [div_le_iff₀ hDpos]
  have key : (G.annihilationNumber : ℝ) ≤ ((G.maxDegree : ℝ) - 1) * G.indepNum := by
    rcases Nat.lt_or_ge G.maxDegree 3 with h3 | h3
    · have h2' : G.maxDegree = 2 := by omega
      have hT := two_alpha_bound G hconn
      rw [h2'] at hA
      have : G.annihilationNumber ≤ G.indepNum := by omega
      rw [h2']
      have : (G.annihilationNumber : ℝ) ≤ G.indepNum := by exact_mod_cast this
      norm_num
      linarith
    · have := cw_algebra G _ h3 hA
      have hD1 : (0 : ℝ) ≤ (G.maxDegree : ℝ) - 1 := by
        have : (3 : ℝ) ≤ G.maxDegree := by exact_mod_cast h3
        linarith
      nlinarith
  nlinarith

end OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1
