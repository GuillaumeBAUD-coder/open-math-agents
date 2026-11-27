import FormalConjectures.ErdosProblems.«642»

-- Problem: Erdős Problem 642 — upper bound n pow three halves
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/642.lean:68 (declaration Erdos642.erdos_642.variants.upper_bound_n_pow_three_halves)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMA642

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- `f` restricted to `[0, m]` is a path of `G` inside `S`. -/
def IsP (S : Finset V) (m : ℕ) (f : ℕ → V) : Prop :=
  (∀ k ≤ m, f k ∈ S) ∧ (∀ k < m, G.Adj (f k) (f (k + 1))) ∧
    (∀ a ≤ m, ∀ b ≤ m, f a = f b → a = b)

/-- the walk going down along `g` from index `k` to index `0` -/
def walkDown (g : ℕ → V) :
    (k : ℕ) → (∀ j < k, G.Adj (g (j + 1)) (g j)) → G.Walk (g k) (g 0)
  | 0, _ => SimpleGraph.Walk.nil
  | k + 1, h => SimpleGraph.Walk.cons (h k (by omega)) (walkDown g k (fun j hj => h j (by omega)))

variable {G}

lemma walkDown_length (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)), (walkDown G g k h).length = k := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ k ih => intro h; simp [walkDown, ih]

lemma mem_support_walkDown (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)) (v : V),
      v ∈ (walkDown G g k h).support ↔ ∃ j ≤ k, g j = v := by
  intro k
  induction k with
  | zero => intro h v; simp [walkDown, eq_comm]
  | succ k ih =>
    intro h v
    simp only [walkDown, SimpleGraph.Walk.support_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨k + 1, le_rfl, rfl⟩
      · exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_or_ge j (k + 1) with h1 | h1
      · exact Or.inr ⟨j, by omega, rfl⟩
      · left; rw [show j = k + 1 by omega]

lemma mem_edges_walkDown (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)) (e : Sym2 V),
      e ∈ (walkDown G g k h).edges → ∃ j < k, e = s(g (j + 1), g j) := by
  intro k
  induction k with
  | zero => intro h e he; simp [walkDown] at he
  | succ k ih =>
    intro h e he
    simp only [walkDown, SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨k, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ih _ e he
      exact ⟨j, by omega, rfl⟩

lemma walkDown_isPath (g : ℕ → V) :
    ∀ k (h : ∀ j < k, G.Adj (g (j + 1)) (g j)),
      (∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b) → (walkDown G g k h).IsPath := by
  intro k
  induction k with
  | zero => intro h _; exact SimpleGraph.Walk.IsPath.nil
  | succ k ih =>
    intro h hinj
    simp only [walkDown]
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨ih _ (fun a ha b hb hab => hinj a (by omega) b (by omega) hab), ?_⟩
    rw [mem_support_walkDown]
    rintro ⟨j, hj, hjk⟩
    have := hinj j (by omega) (k + 1) le_rfl hjk
    omega


lemma ext_lemma {S : Finset V} {M : ℕ} {f : ℕ → V} (hf : IsP G S M f)
    (hmax : ∀ g, ¬ IsP G S (M + 1) g) :
    ∀ w ∈ S, G.Adj (f 0) w → ∃ k ≤ M, f k = w := by
  intro w hw hadj
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2, h3⟩ := hf
  apply hmax (fun k => if k = 0 then w else f (k - 1))
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    dsimp only
    split_ifs
    · exact hw
    · exact h1 _ (by omega)
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using hadj.symm
    · simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, if_false]
      have := h2 (k - 1) (by omega)
      rwa [show k - 1 + 1 = k + 1 - 1 by omega] at this
  · intro a ha b hb hab
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
    · omega
    · simp only [ha0, hb0, if_true, if_false] at hab
      exact absurd hab.symm (hc _ (by omega))
    · simp only [ha0, hb0, if_true, if_false] at hab
      exact absurd hab (hc _ (by omega))
    · simp only [ha0, hb0, if_false] at hab
      have := h3 _ (by omega) _ (by omega) hab
      omega

/-- rotation of a path at a neighbour `f i` of the endpoint `f 0` -/
def rot (f : ℕ → V) (i : ℕ) : ℕ → V := fun k => if k < i then f (i - 1 - k) else f k

lemma rot_isP {S : Finset V} {M : ℕ} {f : ℕ → V} (hf : IsP G S M f) {i : ℕ} (hi1 : 1 ≤ i)
    (hiM : i ≤ M) (hadj : G.Adj (f 0) (f i)) : IsP G S M (rot f i) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    unfold rot; split_ifs
    · exact h1 _ (by omega)
    · exact h1 _ hk
  · intro k hk
    unfold rot
    by_cases hk1 : k + 1 < i
    · rw [if_pos (by omega), if_pos hk1]
      have := h2 (i - 1 - (k + 1)) (by omega)
      rw [show i - 1 - (k + 1) + 1 = i - 1 - k by omega] at this
      exact this.symm
    · by_cases hk2 : k + 1 = i
      · rw [if_pos (by omega), if_neg (by omega), show i - 1 - k = 0 by omega, hk2]
        exact hadj
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 k hk
  · intro a ha b hb hab
    unfold rot at hab
    split_ifs at hab with p q q
    · have := h3 _ (by omega) _ (by omega) hab; omega
    · have := h3 _ (by omega) _ (by omega) hab; omega
    · have := h3 _ (by omega) _ (by omega) hab; omega
    · exact h3 _ ha _ hb hab

lemma rot_image {f : ℕ → V} {i M : ℕ} (hiM : i ≤ M) :
    ∀ k ≤ M, ∃ k' ≤ M, rot f i k = f k' := by
  intro k hk
  unfold rot
  split_ifs
  · exact ⟨i - 1 - k, by omega, rfl⟩
  · exact ⟨k, hk, rfl⟩


lemma rot_zero {f : ℕ → V} {i : ℕ} (hi : 1 ≤ i) : rot f i 0 = f (i - 1) := by
  simp [rot, show 0 < i by omega]

lemma rot_ge {f : ℕ → V} {i k : ℕ} (hk : i ≤ k) : rot f i k = f k := by
  simp [rot, show ¬ k < i by omega]

lemma rot_surj {f : ℕ → V} {i J : ℕ} (hiJ : i ≤ J) :
    ∀ t ≤ J, ∃ j ≤ J, rot f i j = f t := by
  intro t ht
  by_cases h : t < i
  · refine ⟨i - 1 - t, by omega, ?_⟩
    simp [rot, show i - 1 - t < i by omega, show i - 1 - (i - 1 - t) = t by omega]
  · exact ⟨t, ht, rot_ge (by omega)⟩

theorem core [Fintype V] [DecidableRel G.Adj] (S : Finset V) (δ : ℕ) (hδ2 : 2 ≤ δ)
    (hne : S.Nonempty) (hdeg : ∀ v ∈ S, δ ≤ #(S.filter (G.Adj v))) :
    ∃ u, ∃ c : G.Walk u u, c.IsCycle ∧
      δ * δ ≤ 2 * ({e | c.IsChord e}.ncard + c.length) := by
  classical
  -- a longest path in S
  obtain ⟨v0, hv0⟩ := hne
  have hex0 : ∃ f, IsP G S 0 f :=
    ⟨fun _ => v0, fun _ _ => hv0, fun k hk => absurd hk (by omega), fun a ha b hb _ => by omega⟩
  have hbound : ∀ m f, IsP G S m f → m + 1 ≤ #S := by
    intro m f hf
    have := Finset.card_le_card_of_injOn f (s := range (m + 1)) (t := S)
      (fun k hk => hf.1 k (by simp at hk; omega))
      (fun a ha b hb hab => hf.2.2 a (by simp at ha; omega) b (by simp at hb; omega) hab)
    simpa using this
  set M := Nat.findGreatest (fun m => ∃ f, IsP G S m f) #S with hMdef
  have hMspec := Nat.findGreatest_spec (P := fun m => ∃ f, IsP G S m f) (m := 0) (n := #S)
    (Nat.zero_le _) hex0
  rw [← hMdef] at hMspec
  obtain ⟨f, hf⟩ := hMspec
  have hmax : ∀ g, ¬ IsP G S (M + 1) g := by
    intro g hg
    have h1 := hbound _ _ hg
    have h2 : M + 1 ≤ M := Nat.le_findGreatest (by omega) ⟨g, hg⟩
    omega
  obtain ⟨hfS, hfadj, hfinj⟩ := hf
  -- neighbours of endpoints of rotated paths lie on the path
  have hnbr : ∀ i, 1 ≤ i → i ≤ M → G.Adj (f 0) (f i) →
      ∀ w ∈ S, G.Adj (f (i - 1)) w → ∃ k ≤ M, f k = w := by
    intro i hi1 hiM hadj w hw hw'
    have hr := rot_isP ⟨hfS, hfadj, hfinj⟩ hi1 hiM hadj
    obtain ⟨k', hk', hk'w⟩ := ext_lemma hr hmax w hw (by rw [rot_zero hi1]; exact hw')
    obtain ⟨k'', hk'', he⟩ := rot_image (f := f) hiM k' hk'
    exact ⟨k'', hk'', he ▸ hk'w⟩
  have hnbr0 : ∀ w ∈ S, G.Adj (f 0) w → ∃ k ≤ M, f k = w :=
    ext_lemma ⟨hfS, hfadj, hfinj⟩ hmax
  -- the index set of neighbours of f 0
  set E := (range (M + 1)).filter (fun i => 1 ≤ i ∧ G.Adj (f 0) (f i)) with hEdef
  have hE_card : δ ≤ #E := by
    refine (hdeg _ (hfS 0 (by omega))).trans ?_
    calc #(S.filter (G.Adj (f 0))) ≤ #(E.image f) := by
          refine Finset.card_le_card (fun w hw => ?_)
          rw [Finset.mem_filter] at hw
          obtain ⟨k, hk, rfl⟩ := hnbr0 w hw.1 hw.2
          have hk0 : k ≠ 0 := by rintro rfl; exact G.irrefl hw.2
          exact Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
            by omega, hw.2⟩, rfl⟩
      _ ≤ #E := Finset.card_image_le
  have hEmem : ∀ i ∈ E, 1 ≤ i ∧ i ≤ M ∧ G.Adj (f 0) (f i) := by
    intro i hi
    simp only [hEdef, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.2.1, by omega, hi.2.2⟩
  have hM1 : 1 ≤ M := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < #E)
    have := hEmem i hi; omega
  -- the farthest neighbour index J
  set Pairs := (E ×ˢ range (M + 1)).filter (fun p => G.Adj (f (p.1 - 1)) (f p.2)) with hPdef
  have hPmem : ∀ i ∈ E, (i, i) ∈ Pairs := by
    intro i hi
    obtain ⟨h1, h2, _⟩ := hEmem i hi
    simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨hi, by omega⟩, ?_⟩
    have := hfadj (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  have hPne : Pairs.Nonempty := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < #E)
    exact ⟨_, hPmem i hi⟩
  obtain ⟨⟨i0, J⟩, hp, hmaxJ⟩ := Finset.exists_max_image Pairs (fun p => p.2) hPne
  simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨⟨hi0E, hJM⟩, hadjJ⟩ := hp
  obtain ⟨hi01, hi0M, hi0adj⟩ := hEmem i0 hi0E
  have hJall : ∀ i ∈ E, ∀ k ≤ M, G.Adj (f (i - 1)) (f k) → k ≤ J := by
    intro i hi k hk hadj
    have : (i, k) ∈ Pairs := by
      simp only [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hi, by omega⟩, hadj⟩
    exact hmaxJ _ this
  have hi0J : i0 ≤ J := hmaxJ _ (hPmem i0 hi0E)
  have h1E : 1 ∈ E := by
    simp only [hEdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_rfl, by simpa using hfadj 0 (by omega)⟩
  have hJ2 : 2 ≤ J := by
    by_contra hJ
    have hsub : E ⊆ {1} := by
      intro i hi
      have := hJall 1 h1E i (hEmem i hi).2.1 (by simpa using (hEmem i hi).2.2)
      have := (hEmem i hi).1
      simp; omega
    have := Finset.card_le_card hsub
    simp at this
    omega
  -- the rotated path and the cycle
  set g := rot f i0 with hgdef
  obtain ⟨hgS, hgadj, hginj⟩ := rot_isP ⟨hfS, hfadj, hfinj⟩ hi01 hi0M hi0adj
  have hg0 : g 0 = f (i0 - 1) := rot_zero hi01
  have hgJ : g J = f J := rot_ge hi0J
  have hadjc : G.Adj (g 0) (g J) := by rw [hg0, hgJ]; exact hadjJ
  set W := walkDown G g J (fun j hj => (hgadj j (by omega)).symm) with hWdef
  have hWpath : W.IsPath :=
    walkDown_isPath g J _ (fun a ha b hb hab => hginj a (by omega) b (by omega) hab)
  have hnotin : s(g 0, g J) ∉ W.edges := by
    intro hmem
    obtain ⟨j, hj, hje⟩ := mem_edges_walkDown g J _ _ hmem
    rw [Sym2.eq_iff] at hje
    rcases hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hginj 0 (by omega) (j + 1) (by omega) h1; omega
    · have := hginj 0 (by omega) j (by omega) h1
      have := hginj J (by omega) (j + 1) (by omega) h2
      omega
  set c : G.Walk (g 0) (g 0) := SimpleGraph.Walk.cons hadjc W with hcdef
  have hcyc : c.IsCycle := (SimpleGraph.Walk.cons_isCycle_iff W hadjc).2 ⟨hWpath, hnotin⟩
  have hclen : c.length = J + 1 := by
    simp [hcdef, hWdef, walkDown_length]
  have hcsupp : ∀ t ≤ J, f t ∈ c.support := by
    intro t ht
    obtain ⟨j, hj, hjt⟩ := rot_surj (f := f) hi0J t ht
    simp only [hcdef, SimpleGraph.Walk.support_cons, List.mem_cons]
    right
    rw [hWdef, mem_support_walkDown]
    exact ⟨j, hj, hjt⟩
  refine ⟨g 0, c, hcyc, ?_⟩
  -- double counting
  set D := E.sigma (fun i => S.filter (G.Adj (f (i - 1)))) with hDdef
  set φ : (Σ _ : ℕ, V) → Sym2 V := fun p => s(f (p.1 - 1), p.2) with hφdef
  have hD : δ * δ ≤ #D := by
    rw [hDdef, Finset.card_sigma]
    calc δ * δ ≤ #E * δ := Nat.mul_le_mul_right _ hE_card
      _ = ∑ _i ∈ E, δ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hdeg _ (hfS _ (by have := hEmem i hi; omega)))
  have hfib : #D ≤ 2 * #(D.image φ) := by
    refine Finset.card_le_mul_card_image (f := φ) D 2 (fun e he => ?_)
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.1 he
    refine (Finset.card_le_card_of_injOn (fun p => p.2) (t := {f (p0.1 - 1), p0.2})
      ?_ ?_).trans (Finset.card_le_two)
    · intro p hp
      rw [Finset.coe_filter] at hp
      obtain ⟨-, hpe⟩ := hp
      simp only [hφdef] at hpe
      have : p.2 ∈ s(f (p0.1 - 1), p0.2) := by rw [← hpe]; exact Sym2.mem_mk_right _ _
      rw [Sym2.mem_iff] at this
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact this
    · intro p hp q hq hpq
      rw [Finset.coe_filter] at hp hq
      obtain ⟨hpD, hpe⟩ := hp
      obtain ⟨hqD, hqe⟩ := hq
      simp only at hpq
      have hpq' : s(f (p.1 - 1), p.2) = s(f (q.1 - 1), q.2) := by
        simp only [hφdef] at hpe hqe; rw [hpe, hqe]
      rw [hpq, Sym2.congr_left] at hpq'
      rw [hDdef, Finset.mem_sigma] at hpD hqD
      have h1 := hEmem _ hpD.1
      have h2 := hEmem _ hqD.1
      have := hfinj _ (by omega) _ (by omega) hpq'
      have hp1 : p.1 = q.1 := by omega
      exact Sigma.ext hp1 (heq_of_eq hpq)
  -- the image is made of chords or cycle edges
  set Ch := (D.image φ).filter (fun e => e ∉ c.edges) with hChdef
  have hCh : #(D.image φ) ≤ #Ch + c.length := by
    have : D.image φ ⊆ Ch ∪ c.edges.toFinset := by
      intro e he
      by_cases h : e ∈ c.edges
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 h)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h⟩)
    refine (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans ?_)
    have := List.toFinset_card_le c.edges
    rw [SimpleGraph.Walk.length_edges] at this
    omega
  have hChsub : (Ch : Set (Sym2 V)) ⊆ {e | c.IsChord e} := by
    intro e he
    rw [hChdef, Finset.coe_filter] at he
    obtain ⟨he, hnot⟩ := he
    obtain ⟨⟨i, w⟩, hpD, rfl⟩ := Finset.mem_image.1 he
    simp only [hDdef, Finset.mem_sigma, Finset.mem_filter] at hpD
    obtain ⟨hiE, hwS, hadj⟩ := hpD
    obtain ⟨hi1, hiM, hi0⟩ := hEmem i hiE
    obtain ⟨k, hkM, rfl⟩ := hnbr i hi1 hiM hi0 w hwS hadj
    have hkJ := hJall i hiE k hkM hadj
    have hiJ : i ≤ J := hmaxJ _ (hPmem i hiE)
    show c.IsChord s(f (i - 1), f k)
    rw [SimpleGraph.Walk.isChord_sym2Mk]
    exact ⟨hadj, hnot, hcsupp _ (by omega), hcsupp _ hkJ⟩
  have hncard : #Ch ≤ {e | c.IsChord e}.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hChsub (Set.toFinite _)
  omega


theorem edges_le [Fintype V] (G : SimpleGraph V)
    (hG : ∀ (v : V) (c : G.Walk v v), c.IsCycle → {e : Sym2 V | c.IsChord e}.ncard < c.length) :
    G.edgeSet.ncard ≤ 2 * (Nat.sqrt (Fintype.card V) + 1) * Fintype.card V := by
  classical
  set δ := 2 * (Nat.sqrt (Fintype.card V) + 1) with hδ
  set n := Fintype.card V with hn
  by_contra hcon
  push Not at hcon
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset] at hcon
  -- edges inside a set
  let eS : Finset V → ℕ := fun S => #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S))
  let obj : Finset V → ℤ := fun S => (eS S : ℤ) - δ * #S
  obtain ⟨S, -, hSmax⟩ := Finset.exists_max_image (univ : Finset V).powerset obj
    ⟨univ, Finset.mem_powerset.2 subset_rfl⟩
  have huniv : obj univ ≥ 1 := by
    have : eS univ = #G.edgeFinset := by
      simp only [eS]; congr 1; ext e; simp
    simp only [obj, this, Finset.card_univ, ← hn]
    push_cast; linarith [(by exact_mod_cast hcon : (δ * n : ℤ) < #G.edgeFinset)]
  have hS1 : obj S ≥ 1 := le_trans huniv (hSmax univ (Finset.mem_powerset.2 subset_rfl))
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have : eS ∅ = 0 := by
      simp only [eS, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hall
      induction e using Sym2.ind with
      | _ a b => exact absurd (hall a (Sym2.mem_mk_left a b)) (by simp)
    simp [obj, this] at hS1
  have hdeg : ∀ v ∈ S, δ ≤ #(S.filter (G.Adj v)) := by
    intro v hv
    by_contra hlt
    push Not at hlt
    have hsplit : eS S ≤ eS (S.erase v) + #(S.filter (G.Adj v)) := by
      have hsub : G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S) ⊆
          G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S.erase v) ∪
            (S.filter (G.Adj v)).image (fun w => s(v, w)) := by
        intro e he
        rw [Finset.mem_filter] at he
        obtain ⟨heE, hall⟩ := he
        by_cases hve : v ∈ e
        · apply Finset.mem_union_right
          obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heE
          exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hall w (Sym2.mem_mk_right v w), heE⟩,
            rfl⟩
        · apply Finset.mem_union_left
          refine Finset.mem_filter.2 ⟨heE, fun u hu => Finset.mem_erase.2 ⟨?_, hall u hu⟩⟩
          rintro rfl; exact hve hu
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left Finset.card_image_le _))
    have hmax := hSmax (S.erase v) (Finset.mem_powerset.2 (Finset.subset_univ _))
    simp only [obj] at hmax
    rw [Finset.card_erase_of_mem hv] at hmax
    have hS0 : 1 ≤ #S := Finset.card_pos.2 hSne
    push_cast [hS0] at hmax
    have : (eS S : ℤ) ≤ eS (S.erase v) + #(S.filter (G.Adj v)) := by exact_mod_cast hsplit
    have : (#(S.filter (G.Adj v)) : ℤ) < δ := by exact_mod_cast hlt
    linarith
  have hδ2 : 2 ≤ δ := by omega
  obtain ⟨u, c, hc, hineq⟩ := core (G := G) S δ hδ2 hSne hdeg
  have hlt := hG u c hc
  have hlen : c.length ≤ n := by
    have h1 := hc.support_nodup.length_le_card
    rw [List.length_tail, SimpleGraph.Walk.length_support] at h1
    simpa using h1
  have hsq : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have : δ * δ = 4 * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) := by rw [hδ]; ring
  nlinarith

end OMA642

theorem OMA.solution : type_of% @Erdos642.erdos_642.variants.upper_bound_n_pow_three_halves := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hle : Erdos642.maxEdges n ≤ 2 * (Nat.sqrt n + 1) * n := by
    classical
    unfold Erdos642.maxEdges
    apply Finset.sup_le
    intro G hG
    rw [Finset.mem_filter] at hG
    have := OMA642.edges_le G (fun v c hc => hG.2 v c hc)
    simpa using this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hn0 (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hR : (Erdos642.maxEdges n : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) + 1) * n := by
    exact_mod_cast hle
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by rw [hpow]; positivity), hpow]
  nlinarith [mul_le_mul_of_nonneg_right hs hn0, mul_le_mul_of_nonneg_right h1 hn0]
