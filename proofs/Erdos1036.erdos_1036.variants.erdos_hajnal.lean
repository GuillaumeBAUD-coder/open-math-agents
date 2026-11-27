import FormalConjectures.ErdosProblems.«1036»

-- Problem: Erdős Problem 1036, Erdős–Hajnal variant
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1036.lean (declaration Erdos1036.erdos_1036.variants.erdos_hajnal)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Reference: P. Erdős and A. Hajnal, On the number of distinct induced subgraphs of a graph, Discrete Math. (1989).

/-!
# Many non-isomorphic induced subgraphs without large bicliques

Split the vertices into a set `A` of about `√n` vertices and the rest `B`, and sort `B` by trace
on `A`. If there are at least `r₀ ≈ n / (4q)` distinct traces, pick one vertex per trace to get
`C`. Then every isomorphism between `G[A ∪ Y]` and `G[A ∪ Y']` (`Y, Y' ⊆ C`) that fixes `A`
pointwise forces `Y = Y'`, so each isomorphism class among the `2^|C|` sets `A ∪ Y` has at most
`n ^ |A|` members, giving `2^|C| / n^|A| ≥ 2^(n / (8q))` classes. Otherwise few traces cover
many vertices of `B`; pigeonholing the vertices of `A` by which of those traces contain them gives
a `K_{k,k}` in `G` or its complement with `2k > c log n`, a contradiction.
-/

open SimpleGraph Finset

namespace OMA1036

variable {n : ℕ}

lemma biclique_of_sets (H : SimpleGraph (Fin n)) (k : ℕ) (E D : Finset (Fin n))
    (hdisj : Disjoint E D) (hE : k ≤ E.card) (hD : k ≤ D.card)
    (hadj : ∀ u ∈ E, ∀ v ∈ D, H.Adj u v) :
    (completeBipartiteGraph (Fin k) (Fin k)).IsContained H := by
  obtain ⟨E', hE'E, hE'c⟩ := Finset.exists_subset_card_eq hE
  obtain ⟨D', hD'D, hD'c⟩ := Finset.exists_subset_card_eq hD
  let e := E'.orderEmbOfFin hE'c
  let d := D'.orderEmbOfFin hD'c
  have he : ∀ i, e i ∈ E := fun i => hE'E (E'.orderEmbOfFin_mem hE'c i)
  have hd : ∀ i, d i ∈ D := fun i => hD'D (D'.orderEmbOfFin_mem hD'c i)
  let f : Fin k ⊕ Fin k → Fin n := Sum.elim e d
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j <;> simp at hxy
    · exact hadj _ (he i) _ (hd j)
    · exact (hadj _ (he j) _ (hd i)).symm
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j <;> simp only [f, Sum.elim_inl, Sum.elim_inr] at hxy
    · rw [e.injective hxy]
    · exact absurd hxy (Finset.disjoint_left.1 hdisj (he i) |> fun h => fun h' => h (h' ▸ hd j))
    · exact absurd hxy.symm (Finset.disjoint_left.1 hdisj (he j) |> fun h => fun h' => h (h' ▸ hd i))
    · rw [d.injective hxy]


/-- Isomorphism of `G[A ∪ Y]` and `G[A ∪ Y']`. -/
def isoSetoid (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Setoid (Finset (Fin n)) where
  r Y Y' := Nonempty (G.induce (↑(A ∪ Y) : Set (Fin n)) ≃g G.induce (↑(A ∪ Y') : Set (Fin n)))
  iseqv := ⟨fun _ => ⟨Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

lemma subset_of_fix (G : SimpleGraph (Fin n)) (A C Y Y' : Finset (Fin n)) (hAC : Disjoint A C)
    (htr : ∀ y ∈ C, ∀ z ∈ C, (∀ a ∈ A, G.Adj y a ↔ G.Adj z a) → y = z)
    (hY : Y ⊆ C) (hY' : Y' ⊆ C)
    (σ : G.induce (↑(A ∪ Y) : Set (Fin n)) ≃g G.induce (↑(A ∪ Y') : Set (Fin n)))
    (hσ : ∀ a (ha : a ∈ A), (σ ⟨a, by simp [ha]⟩ : Fin n) = a) : Y ⊆ Y' := by
  intro y hy
  have hyA : y ∉ A := fun h => Finset.disjoint_left.1 hAC h (hY hy)
  have hyU : y ∈ (↑(A ∪ Y) : Set (Fin n)) := by simp [hy]
  set z := σ ⟨y, hyU⟩ with hz
  have hzU := z.2
  simp only [coe_union, Set.mem_union, mem_coe] at hzU
  rcases hzU with hzA | hzY'
  · exfalso
    have h1 := hσ z.1 hzA
    have : (⟨z.1, by simp [hzA]⟩ : (↑(A ∪ Y) : Set (Fin n))) = ⟨y, hyU⟩ := by
      apply σ.injective
      apply Subtype.ext
      rw [h1]
    exact hyA (by have := congrArg Subtype.val this; simp at this; rw [← this]; exact hzA)
  · have hyz : y = z.1 := by
      apply htr y (hY hy) z.1 (hY' hzY')
      intro a ha
      have haU : a ∈ (↑(A ∪ Y) : Set (Fin n)) := by simp [ha]
      have h1 := σ.map_adj_iff (v := ⟨y, hyU⟩) (w := ⟨a, haU⟩)
      rw [SimpleGraph.induce_adj, SimpleGraph.induce_adj] at h1
      have h2 := hσ a ha
      rw [← h1, ← hz, h2]
    rw [hyz]; exact hzY'


lemma eq_of_fix (G : SimpleGraph (Fin n)) (A C Y Y' : Finset (Fin n)) (hAC : Disjoint A C)
    (htr : ∀ y ∈ C, ∀ z ∈ C, (∀ a ∈ A, G.Adj y a ↔ G.Adj z a) → y = z)
    (hY : Y ⊆ C) (hY' : Y' ⊆ C)
    (σ : G.induce (↑(A ∪ Y) : Set (Fin n)) ≃g G.induce (↑(A ∪ Y') : Set (Fin n)))
    (hσ : ∀ a (ha : a ∈ A), (σ ⟨a, by simp [ha]⟩ : Fin n) = a) : Y = Y' := by
  apply le_antisymm (subset_of_fix G A C Y Y' hAC htr hY hY' σ hσ)
  apply subset_of_fix G A C Y' Y hAC htr hY' hY σ.symm
  intro a ha
  have h1 : σ ⟨a, by simp [ha]⟩ = ⟨a, by simp [ha]⟩ := Subtype.ext (hσ a ha)
  rw [← h1, RelIso.symm_apply_apply]

open scoped Classical in
lemma fiber_card (G : SimpleGraph (Fin n)) (A C : Finset (Fin n)) (hAC : Disjoint A C)
    (htr : ∀ y ∈ C, ∀ z ∈ C, (∀ a ∈ A, G.Adj y a ↔ G.Adj z a) → y = z)
    (q : Quotient (isoSetoid G A)) :
    (C.powerset.filter (fun Y => Quotient.mk (isoSetoid G A) Y = q)).card ≤ n ^ A.card := by
  set F := C.powerset.filter (fun Y => Quotient.mk (isoSetoid G A) Y = q)
  rcases F.eq_empty_or_nonempty with hF | ⟨Ys, hYs⟩
  · rw [hF]; simp
  have hYs' := (mem_filter.1 hYs)
  let φ : Finset (Fin n) → ({x // x ∈ A} → Fin n) := fun Y =>
    if h : (isoSetoid G A).r Y Ys then fun a => ((Classical.choice h) ⟨a.1, by simp [a.2]⟩ : Fin n)
    else fun a => a.1
  have hrel : ∀ Y ∈ F, (isoSetoid G A).r Y Ys := by
    intro Y hY
    have h1 := (mem_filter.1 hY).2
    rw [← hYs'.2] at h1
    exact Quotient.exact h1
  have hinj : Set.InjOn φ ↑F := by
    intro Y hY Y' hY' hφ
    have hr := hrel Y hY
    have hr' := hrel Y' hY'
    simp only [φ, dif_pos hr, dif_pos hr'] at hφ
    set π := Classical.choice hr
    set π' := Classical.choice hr'
    apply eq_of_fix G A C Y Y' hAC htr (mem_powerset.1 (mem_filter.1 hY).1)
      (mem_powerset.1 (mem_filter.1 hY').1) (π.trans π'.symm)
    intro a ha
    have h1 := congrFun hφ ⟨a, ha⟩
    have h2 : π ⟨a, by simp [ha]⟩ = π' ⟨a, by simp [ha]⟩ := Subtype.ext h1
    show ((π'.symm (π ⟨a, _⟩)) : Fin n) = a
    rw [h2, RelIso.symm_apply_apply]
  calc F.card ≤ (univ : Finset ({x // x ∈ A} → Fin n)).card :=
        card_le_card_of_injOn φ (fun _ _ => mem_coe.2 (mem_univ _)) hinj
    _ = n ^ A.card := by simp


open scoped Classical in
lemma rigid (G : SimpleGraph (Fin n)) (hn : 0 < n) (A C : Finset (Fin n)) (hAC : Disjoint A C)
    (htr : ∀ y ∈ C, ∀ z ∈ C, (∀ a ∈ A, G.Adj y a ↔ G.Adj z a) → y = z) :
    Erdos1036.HasManyNonIsomorphicInducedSubgraphs G ((2 : ℝ) ^ C.card / (n : ℝ) ^ A.card) := by
  set S := isoSetoid G A
  set Q := C.powerset.image (Quotient.mk S)
  have hcount : 2 ^ C.card ≤ Q.card * n ^ A.card := by
    rw [← card_powerset, card_eq_sum_card_fiberwise (f := Quotient.mk S) (t := Q)
      (fun Y hY => mem_coe.2 (mem_image_of_mem _ hY))]
    calc ∑ q ∈ Q, (C.powerset.filter (fun Y => Quotient.mk S Y = q)).card
        ≤ ∑ _q ∈ Q, n ^ A.card := sum_le_sum fun q _ => fiber_card G A C hAC htr q
      _ = Q.card * n ^ A.card := by simp
  let g : Quotient S → Set (Fin n) := fun q => (↑(A ∪ q.out) : Set (Fin n))
  have hginj : Function.Injective g := by
    intro q q' h
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    show Nonempty (G.induce (↑(A ∪ q.out) : Set (Fin n)) ≃g G.induce (↑(A ∪ q'.out) : Set (Fin n)))
    have h' : (↑(A ∪ q.out) : Set (Fin n)) = ↑(A ∪ q'.out) := h
    rw [h']
    exact ⟨Iso.refl⟩
  refine ⟨g '' ↑Q, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩ _ ⟨q', -, rfl⟩ hne
    refine ⟨fun e => hne ?_⟩
    have : q = q' := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact Quotient.sound ⟨e⟩
    rw [this]
  · rw [Set.ncard_image_of_injective _ hginj, Set.ncard_coe_finset]
    have hnpos : (0 : ℝ) < (n : ℝ) ^ A.card := by positivity
    rw [div_le_iff₀ hnpos]
    exact_mod_cast hcount


open scoped Classical in
/-- The trace of `v` on `A`. -/
noncomputable def tr (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  A.filter (fun a => G.Adj v a)

open scoped Classical in
lemma few_classes (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (k₀ l q r₀ : ℕ) (hl : 1 ≤ l)
    (hT : (B.image (tr G A)).card < r₀)
    (h1 : 2 * k₀ ≤ l * q) (h2 : r₀ * q + l * (2 * k₀) ≤ B.card) :
    ∃ Λ ⊆ B.image (tr G A), Λ.card ≤ l ∧ 2 * k₀ ≤ (B.filter (fun v => tr G A v ∈ Λ)).card := by
  set T := B.image (tr G A)
  let cls : Finset (Fin n) → Finset (Fin n) := fun τ => B.filter (fun v => tr G A v = τ)
  have hsum : ∀ Λ ⊆ T, (B.filter (fun v => tr G A v ∈ Λ)).card = ∑ τ ∈ Λ, (cls τ).card := by
    intro Λ _
    rw [card_eq_sum_card_fiberwise (f := tr G A) (t := Λ) (fun v hv => by
      simp only [coe_filter, Set.mem_setOf_eq] at hv; exact hv.2)]
    apply sum_congr rfl
    intro τ hτ
    congr 1
    ext v
    simp only [mem_filter, cls]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hτ⟩, h2⟩
  set Λ0 := T.filter (fun τ => q ≤ (cls τ).card)
  have hBsplit : B.card = ∑ τ ∈ T, (cls τ).card := by
    have := hsum T (subset_refl _)
    rw [← this]; congr 1; ext v
    simp only [mem_filter, T, mem_image]
    exact ⟨fun h => ⟨h, v, h, rfl⟩, fun h => h.1⟩
  have hsmall : ∑ τ ∈ T.filter (fun τ => ¬ q ≤ (cls τ).card), (cls τ).card ≤ r₀ * q := by
    calc ∑ τ ∈ T.filter (fun τ => ¬ q ≤ (cls τ).card), (cls τ).card
        ≤ ∑ _τ ∈ T.filter (fun τ => ¬ q ≤ (cls τ).card), q :=
          sum_le_sum fun τ hτ => by have := (mem_filter.1 hτ).2; omega
      _ = (T.filter (fun τ => ¬ q ≤ (cls τ).card)).card * q := by simp
      _ ≤ r₀ * q := Nat.mul_le_mul_right _ ((card_filter_le _ _).trans hT.le)
  have hlarge : B.card - r₀ * q ≤ ∑ τ ∈ Λ0, (cls τ).card := by
    show B.card - r₀ * q ≤ ∑ τ ∈ T.filter (fun τ => q ≤ (cls τ).card), (cls τ).card
    have := sum_filter_add_sum_filter_not T (fun τ => q ≤ (cls τ).card) (fun τ => (cls τ).card)
    omega
  by_cases hΛ : l ≤ Λ0.card
  · obtain ⟨Λ, hΛsub, hΛc⟩ := exists_subset_card_eq hΛ
    refine ⟨Λ, hΛsub.trans (filter_subset _ _), hΛc.le, ?_⟩
    rw [hsum Λ (hΛsub.trans (filter_subset _ _))]
    calc 2 * k₀ ≤ l * q := h1
      _ = ∑ _τ ∈ Λ, q := by simp [hΛc]
      _ ≤ _ := sum_le_sum fun τ hτ => (mem_filter.1 (hΛsub hτ)).2
  · push_neg at hΛ
    by_contra hno
    push_neg at hno
    have hbig : ∀ τ ∈ Λ0, (cls τ).card < 2 * k₀ := by
      intro τ hτ
      have hτT : τ ∈ T := (mem_filter.1 hτ).1
      have := hno {τ} (singleton_subset_iff.2 hτT) (by simpa using hl)
      rw [hsum {τ} (singleton_subset_iff.2 hτT), sum_singleton] at this
      exact this
    have : ∑ τ ∈ Λ0, (cls τ).card < l * (2 * k₀) := by
      rcases Λ0.eq_empty_or_nonempty with h | h
      · rw [h, sum_empty]; have : 0 < 2 * k₀ := by
          by_contra h0; push_neg at h0
          have := hno ∅ (empty_subset _) (by simp); simp at this; omega
        positivity
      calc ∑ τ ∈ Λ0, (cls τ).card < ∑ _τ ∈ Λ0, 2 * k₀ := sum_lt_sum_of_nonempty h hbig
        _ = Λ0.card * (2 * k₀) := by simp
        _ ≤ l * (2 * k₀) := Nat.mul_le_mul_right _ hΛ.le
    omega


open scoped Classical in
lemma bic_of_Lambda (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (k₀ l : ℕ) (Λ : Finset (Finset (Fin n))) (hΛ : Λ.card ≤ l)
    (hD : 2 * k₀ ≤ (B.filter (fun v => tr G A v ∈ Λ)).card) (hA : 2 ^ l * k₀ ≤ A.card) :
    (completeBipartiteGraph (Fin k₀) (Fin k₀)).IsContained G ∨
      (completeBipartiteGraph (Fin k₀) (Fin k₀)).IsContained Gᶜ := by
  set D := B.filter (fun v => tr G A v ∈ Λ)
  let p : Fin n → Finset (Finset (Fin n)) := fun u => Λ.filter (fun τ => u ∈ τ)
  have hmaps : ∀ u ∈ A, p u ∈ Λ.powerset := fun u _ => mem_powerset.2 (filter_subset _ _)
  have hpc : Λ.powerset.card * k₀ ≤ A.card := by
    rw [card_powerset]
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hΛ)).trans hA
  obtain ⟨P, -, hP⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps
    ⟨∅, empty_mem_powerset _⟩ hpc
  set E := A.filter (fun u => p u = P)
  have hEA : E ⊆ A := filter_subset _ _
  have hDB : D ⊆ B := filter_subset _ _
  have hsplit := card_filter_add_card_filter_not (s := D) (fun v => tr G A v ∈ P)
  have hdisj : ∀ D' ⊆ D, Disjoint E D' := fun D' hD' =>
    Finset.disjoint_of_subset_left hEA (Finset.disjoint_of_subset_right (hD'.trans hDB) hAB)
  by_cases h1 : k₀ ≤ (D.filter (fun v => tr G A v ∈ P)).card
  · left
    apply biclique_of_sets G k₀ E _ (hdisj _ (filter_subset _ _)) hP h1
    intro u hu v hv
    have hu' := mem_filter.1 hu
    have hv' := mem_filter.1 hv
    have : tr G A v ∈ p u := by rw [hu'.2]; exact hv'.2
    simp only [p, mem_filter] at this
    have h3 := this.2
    simp only [tr, mem_filter] at h3
    exact h3.2.symm
  · right
    apply biclique_of_sets Gᶜ k₀ E (D.filter (fun v => tr G A v ∉ P)) (hdisj _ (filter_subset _ _)) hP (by omega)
    intro u hu v hv
    have hu' := mem_filter.1 hu
    have hv' := mem_filter.1 hv
    have hvD := mem_filter.1 hv'.1
    rw [SimpleGraph.compl_adj]
    refine ⟨fun h => Finset.disjoint_left.1 hAB hu'.1 (h ▸ hvD.1), fun hadj => hv'.2 ?_⟩
    rw [← hu'.2]
    simp only [p, mem_filter]
    refine ⟨hvD.2, ?_⟩
    simp only [tr, mem_filter]
    exact ⟨hu'.1, hadj.symm⟩


lemma hasMany_mono {G : SimpleGraph (Fin n)} {k k' : ℝ} (hk : k' ≤ k)
    (h : Erdos1036.HasManyNonIsomorphicInducedSubgraphs G k) :
    Erdos1036.HasManyNonIsomorphicInducedSubgraphs G k' := by
  obtain ⟨S, hS, hc⟩ := h
  exact ⟨S, hS, hk.trans hc⟩

open scoped Classical in
lemma structural (G : SimpleGraph (Fin n)) (hn : 0 < n) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (k₀ l q r₀ : ℕ) (m : ℝ) (hl : 1 ≤ l) (h1 : 2 * k₀ ≤ l * q) (h2 : r₀ * q + l * (2 * k₀) ≤ B.card)
    (hA : 2 ^ l * k₀ ≤ A.card) (hbic : Erdos1036.NoLargeBiclique G m) (hm : m < 2 * k₀) :
    Erdos1036.HasManyNonIsomorphicInducedSubgraphs G ((2 : ℝ) ^ r₀ / (n : ℝ) ^ A.card) := by
  set T := B.image (tr G A)
  by_cases hT : r₀ ≤ T.card
  · have hch : ∀ τ ∈ T, ∃ v ∈ B, tr G A v = τ := fun τ hτ => mem_image.1 hτ
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    choose! w hwB hwt using hch
    set C := T.image w
    have hwinj : Set.InjOn w ↑T := by
      intro τ hτ τ' hτ' h
      rw [← hwt τ hτ, ← hwt τ' hτ', h]
    have hCc : C.card = T.card := card_image_of_injOn hwinj
    have hCB : C ⊆ B := by
      intro v hv; obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hv; exact hwB τ hτ
    have htr : ∀ y ∈ C, ∀ z ∈ C, (∀ a ∈ A, G.Adj y a ↔ G.Adj z a) → y = z := by
      intro y hy z hz hyz
      obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hy
      obtain ⟨τ', hτ', rfl⟩ := mem_image.1 hz
      have : tr G A (w τ) = tr G A (w τ') := by
        unfold tr; exact filter_congr fun a ha => hyz a ha
      rw [hwt τ hτ, hwt τ' hτ'] at this
      rw [this]
    have hr := rigid G hn A C (Finset.disjoint_of_subset_right hCB hAB) htr
    apply hasMany_mono _ hr
    have hnpos : (0 : ℝ) < (n : ℝ) ^ A.card := by positivity
    apply div_le_div_of_nonneg_right _ hnpos.le
    exact pow_le_pow_right₀ (by norm_num) (by rw [hCc]; exact hT)
  · push_neg at hT
    exfalso
    obtain ⟨Λ, -, hΛc, hD⟩ := few_classes G A B k₀ l q r₀ hl hT h1 h2
    have := hbic k₀ (bic_of_Lambda G A B hAB k₀ l Λ hΛc hD hA)
    linarith


lemma polyA (c y k pw a : ℝ) (hc : 0 < c) (hy : c + 2 ≤ y) (hy1 : 1 ≤ y) (hk : k ≤ c * y + 1)
    (hpw : pw ≤ y ^ 2) (hpw0 : 0 ≤ pw) (ha : y ^ 4 - 1 < a) (hk0 : 0 ≤ k) : pw * k ≤ a := by
  have hy0 : 0 ≤ y := by linarith
  have e2 : pw * k ≤ y ^ 2 * (c * y + 1) := mul_le_mul hpw hk hk0 (by positivity)
  have f0 : (c + 2) * y ≤ y * y := mul_le_mul_of_nonneg_right hy hy0
  have f1 : c * y + 2 ≤ y ^ 2 := by nlinarith
  have f2 : y ^ 2 * (c * y + 2) ≤ y ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left f1 (sq_nonneg y)
  have f3 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
  have f4 : y ^ 2 * y ^ 2 = y ^ 4 := by ring
  have f5 : y ^ 2 * (c * y + 2) = y ^ 2 * (c * y + 1) + y ^ 2 := by ring
  linarith

lemma polyB (q y x L l2 : ℝ) (hq : 0 < q) (hy : 24 * q ≤ y) (hy1 : 1 ≤ y) (hx : y ^ 8 = x)
    (hl2 : 0.69 < l2) : y ^ 5 + l2 ≤ x * l2 / (8 * q) := by
  rw [← hx]
  have e0 : y ≤ y ^ 3 := by
    calc y = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ 3 := pow_le_pow_right₀ hy1 (by norm_num)
  have e1 : 24 * q ≤ y ^ 3 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have e2 : y ^ 8 = y ^ 5 * y ^ 3 := by ring
  have e3 : 1 ≤ y ^ 5 := one_le_pow₀ hy1
  have e4 : y ^ 5 * (24 * q) ≤ y ^ 5 * y ^ 3 := mul_le_mul_of_nonneg_left e1 (by positivity)
  have e5 : 0 ≤ l2 := by linarith
  have e6 : y ^ 5 * (24 * q) * l2 ≤ y ^ 5 * y ^ 3 * l2 := mul_le_mul_of_nonneg_right e4 e5
  have e7 : y ^ 5 * q * 0.69 ≤ y ^ 5 * q * l2 :=
    mul_le_mul_of_nonneg_left hl2.le (by positivity)
  have e8 : 1 * q ≤ y ^ 5 * q := mul_le_mul_of_nonneg_right e3 hq.le
  have e9 : l2 * q ≤ l2 * (y ^ 5 * q) := by nlinarith
  nlinarith

open Filter in
theorem main : ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      Erdos1036.NoLargeBiclique G (c * Real.log (n : ℝ)) →
        Erdos1036.HasManyNonIsomorphicInducedSubgraphs G ((2 : ℝ) ^ (δ * (n : ℝ))) := by
  intro c hc
  set q : ℕ := ⌈8 * (c + 1)⌉₊ with hqdef
  have hq : 8 * (c + 1) ≤ (q : ℝ) := Nat.le_ceil _
  have hq0 : (0 : ℝ) < q := by linarith
  refine ⟨1 / (8 * q), by positivity, ?_⟩
  set M : ℝ := 24 * q + c + 10
  have ev1 : ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev2 : ∀ᶠ n : ℕ in atTop, ‖Real.log n‖ ≤ 1 * ‖(n : ℝ) ^ (1 / 8 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound (by norm_num))
  have ev3 : ∀ᶠ n : ℕ in atTop, 4 * c + 8 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [ev1, ev2, ev3, eventually_ge_atTop 1] with n hy hlogy hL hn1 G hbic
  set x : ℝ := (n : ℝ) with hxdef
  have hx1 : (1 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hn1
  have hx0 : (0 : ℝ) < x := by linarith
  set y : ℝ := x ^ (1 / 8 : ℝ) with hydef
  set L : ℝ := Real.log x with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hx1
  have hy0 : 0 ≤ y := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0, abs_of_nonneg hy0, one_mul] at hlogy
  have hy8 : y ^ 8 = x := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hsq : Real.sqrt x = y ^ 4 := by
    rw [← hy8, show (8 : ℕ) = 4 * 2 by rfl, pow_mul, Real.sqrt_sq (by positivity)]
  have hy4 : x ^ (1 / 4 : ℝ) = y ^ 2 := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hyM : 24 * (q : ℝ) + c + 10 ≤ y := hy
  have hy1 : 1 ≤ y := by linarith
  -- parameters
  set a : ℕ := ⌊Real.sqrt x⌋₊ with hadef
  have ha1 : (a : ℝ) ≤ y ^ 4 := by rw [← hsq]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have ha2 : y ^ 4 - 1 < (a : ℝ) := by rw [← hsq]; exact Nat.sub_one_lt_floor _
  have hy4ge : y ^ 4 ≤ y ^ 8 := pow_le_pow_right₀ hy1 (by norm_num)
  have han : a ≤ n := by
    have : (a : ℝ) ≤ n := by rw [← hxdef, ← hy8]; linarith
    exact_mod_cast this
  set A : Finset (Fin n) := (Finset.univ : Finset (Fin a)).map (Fin.castLEEmb han)
  have hAc : A.card = a := by simp [A]
  set B : Finset (Fin n) := Finset.univ \ A
  have hBc : B.card = n - a := by
    rw [card_sdiff, inter_univ, card_univ, Fintype.card_fin, hAc]
  have hAB : Disjoint A B := disjoint_sdiff
  set k₀ : ℕ := ⌊c * L⌋₊ + 1 with hk₀
  have hk1 : c * L < (k₀ : ℝ) := by rw [hk₀]; push_cast; exact Nat.lt_floor_add_one _
  have hk2 : (k₀ : ℝ) ≤ c * L + 1 := by
    rw [hk₀]; push_cast; have := Nat.floor_le (show 0 ≤ c * L by positivity); linarith
  set l : ℕ := ⌊L / 4⌋₊ with hldef
  have hl1 : (l : ℝ) ≤ L / 4 := Nat.floor_le (by positivity)
  have hl2 : L / 4 - 1 < (l : ℝ) := Nat.sub_one_lt_floor _
  set r₀ : ℕ := ⌊x / (4 * q)⌋₊ with hr₀
  have hr1 : (r₀ : ℝ) ≤ x / (4 * q) := Nat.floor_le (by positivity)
  have hr2 : x / (4 * q) - 1 < (r₀ : ℝ) := Nat.sub_one_lt_floor _
  have hLy : L ≤ y := hlogy
  clear_value r₀ l k₀ B A a
  -- the hypotheses of `structural`
  have hl : 1 ≤ l := by
    rw [hldef]; exact Nat.le_floor (by push_cast; linarith)
  have h1 : 2 * k₀ ≤ l * q := by
    have hl0 : (0 : ℝ) ≤ L / 4 - 1 := by linarith
    have : (2 * k₀ : ℝ) ≤ (l : ℝ) * q := by
      have e1 : (L / 4 - 1) * (8 * (c + 1)) ≤ (l : ℝ) * q :=
        mul_le_mul hl2.le hq (by positivity) (Nat.cast_nonneg _)
      nlinarith
    exact_mod_cast this
  have h2 : r₀ * q + l * (2 * k₀) ≤ B.card := by
    rw [hBc]
    have hrq : (r₀ : ℝ) * q ≤ x / 4 := by
      have := mul_le_mul_of_nonneg_right hr1 hq0.le
      calc (r₀ : ℝ) * q ≤ x / (4 * q) * q := this
        _ = x / 4 := by field_simp
    have hlk : (l : ℝ) * (2 * k₀) ≤ (L / 4) * (2 * (c * L + 1)) :=
      mul_le_mul hl1 (by linarith) (by positivity) (by positivity)
    have hL1 : 1 ≤ L := by linarith
    have hL2 : (L / 4) * (2 * (c * L + 1)) ≤ (c + 1) * y ^ 2 := by
      have : L ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hL0 hLy 2
      nlinarith
    have hy6 : (c + 1) * y ^ 2 ≤ y ^ 8 / 8 := by
      have e1 : 8 * (c + 1) ≤ y := by linarith
      have e2 : y ^ 3 ≤ y ^ 8 := pow_le_pow_right₀ hy1 (by norm_num)
      have e4 : (c + 1) * y ^ 2 ≤ (y / 8) * y ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg y)
      have e5 : (y / 8) * y ^ 2 = y ^ 3 / 8 := by ring
      linarith
    have hy48 : y ^ 4 ≤ y ^ 8 / 8 := by
      have e0 : (2 : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      have e1 : (8 : ℝ) ≤ y ^ 4 := by norm_num at e0; linarith
      have e3 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
      have e4 : 8 * y ^ 4 ≤ y ^ 4 * y ^ 4 := mul_le_mul_of_nonneg_right e1 (by positivity)
      linarith
    have : ((r₀ * q + l * (2 * k₀) : ℕ) : ℝ) ≤ ((n - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub han]; push_cast
      have hxn : (n : ℝ) = y ^ 8 := by rw [← hxdef, hy8]
      rw [hxn]
      have : x / 4 = y ^ 8 / 4 := by rw [hy8]
      linarith
    exact_mod_cast this
  have hA : 2 ^ l * k₀ ≤ A.card := by
    rw [hAc]
    have h2l : (2 : ℝ) ^ l ≤ y ^ 2 := by
      rw [← hy4, Real.rpow_def_of_pos hx0, ← hLdef]
      calc (2 : ℝ) ^ l ≤ Real.exp 1 ^ l := pow_le_pow_left₀ (by norm_num)
            (by have := Real.add_one_le_exp 1; linarith) l
        _ = Real.exp (l : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ Real.exp (L * (1 / 4)) := Real.exp_le_exp.2 (by linarith)
    have : ((2 ^ l * k₀ : ℕ) : ℝ) ≤ (a : ℝ) := by
      push_cast
      have e0 : c * L ≤ c * y := mul_le_mul_of_nonneg_left hLy hc.le
      exact polyA c y (k₀ : ℝ) ((2 : ℝ) ^ l) (a : ℝ) hc (by linarith) hy1 (by linarith) h2l
        (by positivity) ha2 (Nat.cast_nonneg _)
    exact_mod_cast this
  have hm : c * Real.log (n : ℝ) < 2 * k₀ := by
    rw [← hxdef, ← hLdef]; have : 0 ≤ c * L := by positivity
    linarith
  have hmain := structural G (by omega) A B hAB k₀ l q r₀ _ hl h1 h2 hA hbic hm
  apply hasMany_mono _ hmain
  rw [hAc, le_div_iff₀ (by positivity)]
  -- 2^(δ x) * x^a ≤ 2^r₀
  have hxa : x ^ a = Real.exp (a * L) := by
    rw [← Real.exp_log (pow_pos hx0 a), Real.log_pow]
  have h2r : (2 : ℝ) ^ r₀ = Real.exp (r₀ * Real.log 2) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [← hxdef, hxa, h2r, Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, Real.exp_le_exp]
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have haL : (a : ℝ) * L ≤ y ^ 5 := by
    calc (a : ℝ) * L ≤ y ^ 4 * y := mul_le_mul ha1 hLy hL0 (by positivity)
      _ = y ^ 5 := by ring
  have hkey : y ^ 5 + Real.log 2 ≤ x * Real.log 2 / (8 * q) :=
    polyB (q : ℝ) y x L (Real.log 2) hq0 (by linarith) hy1 hy8 (by linarith)
  have hr3 : (x / (4 * q) - 1) * Real.log 2 ≤ (r₀ : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hr2.le (by linarith)
  have : Real.log 2 * (1 / (8 * q) * x) = x * Real.log 2 / (8 * q) := by field_simp
  have : (x / (4 * q) - 1) * Real.log 2 = 2 * (x * Real.log 2 / (8 * q)) - Real.log 2 := by
    field_simp; ring
  linarith

end OMA1036

theorem OMA.solution : type_of% @Erdos1036.erdos_1036.variants.erdos_hajnal :=
  OMA1036.main
