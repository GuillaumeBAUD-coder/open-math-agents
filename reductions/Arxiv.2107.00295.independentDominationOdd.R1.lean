import FormalConjectures.Arxiv.«2107.00295».IndependentDomination

/-!
The proof of Corollary 1.3 in [Cho, Kim, Kim and Oum](https://arxiv.org/abs/2202.09594)
separates the subcubic bound from the argument for larger degree bounds.
The connected-component step is stated for arbitrary fixed coefficients.
-/

namespace OMA.R_Arxiv_2107_00295_independentDominationOdd_R1

/-- The independent domination bound for isolate-free subcubic graphs. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    0 < G.minDegree → G.maxDegree ≤ 3 →
    2 * G.indepDominationNumber ≤ Fintype.card V

/-- The connected case of Corollary 1.3 for an odd degree bound of at least five. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ), 5 ≤ D → Odd D → 0 < G.minDegree → G.maxDegree ≤ D → G.Connected →
    let m := (D + 2)^2 / 4
    m * G.indepDominationNumber ≤ (m - D) * Fintype.card V

/-- A uniform linear bound for connected graphs extends to their disjoint unions. -/
def H3 : Prop :=
  ∀ (D A B : ℕ),
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      0 < G.minDegree → G.maxDegree ≤ D → G.Connected →
      A * G.indepDominationNumber ≤ B * Fintype.card V) →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      0 < G.minDegree → G.maxDegree ≤ D →
      A * G.indepDominationNumber ≤ B * Fintype.card V

lemma map_indep_dominating_set {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {K : SimpleGraph W}
    (e : G ≃g K) {n : ℕ} {s : Finset V} (hs : G.IsNIndepDominatingSet n s) :
    K.IsNIndepDominatingSet n (s.map e.toEquiv.toEmbedding) := by
  have hmem {x : W} : x ∈ s.map e.toEquiv.toEmbedding ↔ e.symm x ∈ s := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  refine ⟨?_, ?_, (Finset.card_map _).trans hs.card_eq⟩
  · intro x hx y hy hne hadj
    exact hs.isIndep (hmem.mp hx) (hmem.mp hy) (fun h ↦ hne (e.symm.injective h))
      (e.symm.map_rel_iff.mpr hadj)
  · intro x
    rcases hs.isDominating (e.symm x) with hx | ⟨y, hy, hxy⟩
    · exact Or.inl (hmem.mpr hx)
    · refine Or.inr ⟨e y, hmem.mpr (by simpa using hy), e.symm.map_rel_iff.mp ?_⟩
      simpa using hxy

lemma indep_domination_number_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {K : SimpleGraph W}
    (e : G ≃g K) : G.indepDominationNumber = K.indepDominationNumber := by
  unfold SimpleGraph.indepDominationNumber
  congr 1
  ext n
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨_, map_indep_dominating_set e hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨_, map_indep_dominating_set e.symm hs⟩

lemma combine_bounds (subcubic : H1) (connected : H2) (components : H3)
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hIso : 0 < G.minDegree) (hOdd : Odd G.maxDegree) :
    (G.maxDegree + 1) * (G.maxDegree + 3) * G.indepDominationNumber ≤
      (G.maxDegree^2 + 3) * Fintype.card V := by
  let D := G.maxDegree
  let m := (D + 2)^2 / 4
  change (D + 1) * (D + 3) * G.indepDominationNumber ≤ (D^2 + 3) * Fintype.card V
  by_cases hsmall : D ≤ 3
  · have hbound := subcubic V G hIso hsmall
    obtain ⟨k, hk⟩ := hOdd
    change D = 2 * k + 1 at hk
    have hc : D = 1 ∨ D = 3 := by omega
    rcases hc with hc | hc <;> rw [hc] <;> norm_num <;> omega
  · have hlarge : 5 ≤ D := by
      obtain ⟨k, hk⟩ := hOdd
      change D = 2 * k + 1 at hk
      omega
    have hconnected (W : Type) [Fintype W] [DecidableEq W] (K : SimpleGraph W)
        [DecidableRel K.Adj] (hpos : 0 < K.minDegree) (hmax : K.maxDegree ≤ D)
        (hconn : K.Connected) :
        m * K.indepDominationNumber ≤ (m - D) * Fintype.card W :=
      connected W K D hlarge hOdd hpos hmax hconn
    have hbound := components D m (m - D) hconnected V G hIso le_rfl
    obtain ⟨k, hk⟩ := hOdd
    change D = 2 * k + 1 at hk
    have hsq : (D + 2)^2 = 4 * ((k + 1) * (k + 2)) + 1 := by rw [hk]; ring
    have hm : m = (k + 1) * (k + 2) := by
      change (D + 2)^2 / 4 = _
      omega
    have hDm : D ≤ m := by rw [hm, hk]; nlinarith
    have hleft : (D + 1) * (D + 3) = 4 * m := by rw [hm, hk]; ring
    have hright_add : D^2 + 3 + 4 * D = 4 * m := by rw [hm, hk]; ring
    have hright : D^2 + 3 = 4 * (m - D) := by omega
    rw [hleft, hright, mul_assoc, mul_assoc]
    exact Nat.mul_le_mul_left 4 hbound

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2107.00295».independentDominationOdd := by
  intro subcubic connected components V _ _ G _ hIso hOdd
  classical
  let e := Fintype.equivFin V
  let K := G.map e.toEmbedding
  have eK : G ≃g K := SimpleGraph.Iso.map e G
  have hmin := eK.minDegree_eq
  have hmax := eK.maxDegree_eq
  have hi := indep_domination_number_eq_of_iso eK
  have hpos : 0 < K.minDegree := hmin ▸ hIso
  have hodd : Odd K.maxDegree := hmax ▸ hOdd
  have hbound := combine_bounds subcubic connected components _ K hpos hodd
  change (G.maxDegree + 1) * (G.maxDegree + 3) * G.indepDominationNumber ≤
    (G.maxDegree^2 + 3) * Fintype.card V
  rw [hmax, hi]
  simpa only [K, Fintype.card_fin] using hbound

end OMA.R_Arxiv_2107_00295_independentDominationOdd_R1
