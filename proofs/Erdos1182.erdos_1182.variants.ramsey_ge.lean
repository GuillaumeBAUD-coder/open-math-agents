import FormalConjectures.ErdosProblems.«1182»

/-!
Proof of Erdos Problem 1182 (ramsey_ge): for any connected graph `G` on `n` vertices,
`2 * n - 1 ≤ SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) G`.
-/

-- Problem: Erdős Problem 1182 — ramsey ge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1182.lean:158 (declaration Erdos1182.erdos_1182.variants.ramsey_ge)
-- Credit: @Masterlincs (the owner of the agent is credited as the solver)

namespace OMA

/-- An injective map from `Fin n` whose values are pairwise non-adjacent in `C`
exhibits the containment of any graph on `Fin n` in the complement of `C`. -/
lemma inj_contained_compl {m n : ℕ} (C : SimpleGraph (Fin m)) (f : Fin n → Fin m)
    (hf : Function.Injective f) (hnd : ∀ x y : Fin n, x ≠ y → ¬ C.Adj (f x) (f y))
    (G : SimpleGraph (Fin n)) : G.IsContained Cᶜ :=
  ⟨⟨⟨f, fun {a b} hab => ⟨Function.Injective.ne hf hab.ne, hnd a b hab.ne⟩⟩, hf⟩⟩

/-- Three pairwise adjacent vertices of `C` exhibit the containment of the complete
graph on three vertices. -/
lemma triangle_contained {m : ℕ} (C : SimpleGraph (Fin m)) {v x y : Fin m}
    (hvx : C.Adj v x) (hvy : C.Adj v y) (hxy : C.Adj x y) :
    (⊤ : SimpleGraph (Fin 3)).IsContained C := by
  have e1 : v ≠ x := hvx.ne
  have e2 : v ≠ y := hvy.ne
  have e3 : x ≠ y := hxy.ne
  have e1' : x ≠ v := hvx.ne'
  have e2' : y ≠ v := hvy.ne'
  have e3' : y ≠ x := hxy.ne'
  have a1 : C.Adj x v := hvx.symm
  have a2 : C.Adj y v := hvy.symm
  have a3 : C.Adj y x := hxy.symm
  have hinj : Function.Injective (![v, x, y]) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  refine ⟨⟨⟨![v, x, y], fun {a b} hab => ?_⟩, hinj⟩⟩
  have hab' : a ≠ b := by simpa using hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- Any graph on `Fin n` is contained in the complement of `C` as soon as `C` has a
set `S` of at least `n` pairwise non-adjacent vertices. -/
lemma indep_contained_compl {m n : ℕ} (C : SimpleGraph (Fin m)) (S : Finset (Fin m))
    (hS : n ≤ Finset.card S) (hind : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ C.Adj x y)
    (G : SimpleGraph (Fin n)) : G.IsContained Cᶜ := by
  have hcard : Fintype.card (Fin n) ≤ Fintype.card ↥S := by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact hS
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine inj_contained_compl C (fun i => (e i : Fin m)) ?_ ?_ G
  · intro a b h
    exact e.injective (Subtype.ext h)
  · intro x y hxy
    exact hind _ (e x).property _ (e y).property (fun h => hxy (e.injective (Subtype.ext h)))

/-- If every vertex of `C` sends fewer than `n` edges and `n * n ≤ m`, then `C` has a
set of `k` pairwise non-adjacent vertices for every `k ≤ n`. -/
lemma exists_indep_finset {m n : ℕ} (C : SimpleGraph (Fin m)) (hmm : n * n ≤ m)
    (hdeg : ∀ v : Fin m, ∀ s : Finset (Fin m),
      (∀ w ∈ s, C.Adj v w) → Finset.card s + 1 ≤ n) :
    ∀ k : ℕ, k ≤ n → ∃ S : Finset (Fin m), Finset.card S = k ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ C.Adj x y := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    intro hk
    classical
    obtain ⟨S, hcard, hind⟩ := ih (by omega)
    have hsum : ∑ s ∈ S, Finset.card (insert s (Finset.univ.filter (fun w => C.Adj s w)))
        ≤ k * n := by
      calc ∑ s ∈ S, Finset.card (insert s (Finset.univ.filter (fun w => C.Adj s w)))
          ≤ ∑ s ∈ S, n := by
            refine Finset.sum_le_sum ?_
            intro s hs
            have hmem : ∀ w ∈ Finset.univ.filter (fun w => C.Adj s w), C.Adj s w :=
              fun w hw => (Finset.mem_filter.mp hw).2
            have h1 := hdeg s (Finset.univ.filter (fun w => C.Adj s w)) hmem
            rw [Finset.card_insert_of_notMem
              (fun hc => C.irrefl (Finset.mem_filter.mp hc).2)]
            omega
        _ = Finset.card S * n := Finset.sum_const_nat (fun _ _ => rfl)
        _ = k * n := by rw [hcard]
    have hcardU : Finset.card (S.biUnion (fun s => insert s (Finset.univ.filter (fun w => C.Adj s w))))
        ≤ k * n := le_trans Finset.card_biUnion_le hsum
    have hn : 0 < n := by omega
    have h1 : k * n ≤ (n - 1) * n := Nat.mul_le_mul (by omega) (Nat.le_refl n)
    have h2 : (n - 1) * n + n = n * n := by
      have h3 : (n - 1) + 1 = n := by omega
      calc (n - 1) * n + n = ((n - 1) + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ = n * n := by rw [h3]
    have hlt : Finset.card (S.biUnion (fun s => insert s (Finset.univ.filter (fun w => C.Adj s w))))
        < m :=
      calc Finset.card (S.biUnion (fun s => insert s (Finset.univ.filter (fun w => C.Adj s w))))
          ≤ k * n := hcardU
        _ ≤ (n - 1) * n := h1
        _ < n * n := by rw [← h2]; exact Nat.lt_add_of_pos_right hn
        _ ≤ m := hmm
    have hcu : Finset.card (Finset.univ : Finset (Fin m)) = m := by simp
    obtain ⟨v, hv⟩ : ∃ v : Fin m,
        v ∉ S.biUnion (fun s => insert s (Finset.univ.filter (fun w => C.Adj s w))) := by
      by_contra hcon
      push Not at hcon
      rw [Finset.eq_univ_of_forall hcon, hcu] at hlt
      omega
    have key1 : ∀ s ∈ S, v ≠ s := by
      intro s hs hc
      exact hv (Finset.mem_biUnion.mpr ⟨s, hs, by rw [hc]; exact Finset.mem_insert_self _ _⟩)
    have key2 : ∀ s ∈ S, ¬ C.Adj s v := by
      intro s hs hc
      exact hv (Finset.mem_biUnion.mpr ⟨s, hs,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))⟩)
    have hvS : v ∉ S := fun hmem => key1 v hmem rfl
    refine ⟨insert v S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvS, hcard]
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with hx | hx
      · rcases hy with hy | hy
        · rw [hx, hy] at hxy
          exact absurd rfl hxy
        · rw [hx]
          exact fun hc => key2 y hy hc.symm
      · rcases hy with hy | hy
        · rw [hy]
          exact key2 x hx
        · exact hind x hx y hy hxy

lemma ramsey_set_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    ({ m : ℕ | ∀ (C : SimpleGraph (Fin m)),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ }).Nonempty := by
  classical
  refine ⟨n * n, ?_⟩
  intro C
  by_cases hex : ∃ v : Fin (n * n), n ≤ Finset.card (Finset.univ.filter (fun w => C.Adj v w))
  · obtain ⟨v, hv⟩ := hex
    by_cases htri : ∃ x ∈ Finset.univ.filter (fun w => C.Adj v w),
        ∃ y ∈ Finset.univ.filter (fun w => C.Adj v w), x ≠ y ∧ C.Adj x y
    · obtain ⟨x, hx, y, hy, _, hxy⟩ := htri
      exact Or.inl (triangle_contained C (Finset.mem_filter.mp hx).2
        (Finset.mem_filter.mp hy).2 hxy)
    · push Not at htri
      exact Or.inr (indep_contained_compl C (Finset.univ.filter (fun w => C.Adj v w)) hv htri G)
  · push Not at hex
    have hdeg : ∀ v : Fin (n * n), ∀ s : Finset (Fin (n * n)),
        (∀ w ∈ s, C.Adj v w) → Finset.card s + 1 ≤ n := by
      intro v s hs
      have hsub : s ⊆ Finset.univ.filter (fun w => C.Adj v w) :=
        fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs w hw⟩
      have hle := Finset.card_le_card hsub
      have hvn := hex v
      omega
    obtain ⟨S, hcard, hind⟩ := exists_indep_finset C (Nat.le_refl (n * n)) hdeg n (Nat.le_refl n)
    exact Or.inr (indep_contained_compl C S hcard.ge hind G)

/-- The Boolean cut of `Fin m` at `k` : a vertex lands in the first part iff its
value is below `k`. -/
def cutPartition (k : ℕ) {m : ℕ} : Fin m → Bool :=
  fun u => decide (u.val < k)

/-- The complete bipartite graph on `Fin m` whose parts are the two colors of
a Boolean coloring of the vertices. -/
def bipartiteBy {m : ℕ} (p : Fin m → Bool) : SimpleGraph (Fin m) where
  Adj u v := p u ≠ p v
  symm := ⟨fun _u _v h => h.symm⟩
  loopless := ⟨fun _u h => h rfl⟩

lemma ramsey_lower_bound {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    ∀ m ∈ { m : ℕ | ∀ (C : SimpleGraph (Fin m)),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ },
    2 * n - 1 ≤ m := by
  intro m hm
  simp only [Set.mem_ofPred_eq] at hm
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀⟩ : Nonempty (Fin n) := hG.nonempty
  have hn : 0 < n := Fin.pos v₀
  have hm2 : m ≤ 2 * (n - 1) := by omega
  rcases hm (bipartiteBy (cutPartition (n - 1))) with hC | hC
  · obtain ⟨c⟩ := hC
    have hne01 : (0 : Fin 3) ≠ 1 := by decide
    have hne12 : (1 : Fin 3) ≠ 2 := by decide
    have hne02 : (0 : Fin 3) ≠ 2 := by decide
    have h01 : cutPartition (n - 1) (c 0) ≠ cutPartition (n - 1) (c 1) :=
      c.toHom.map_adj ((SimpleGraph.top_adj (0 : Fin 3) 1).mpr hne01)
    have h12 : cutPartition (n - 1) (c 1) ≠ cutPartition (n - 1) (c 2) :=
      c.toHom.map_adj ((SimpleGraph.top_adj (1 : Fin 3) 2).mpr hne12)
    have h02 : cutPartition (n - 1) (c 0) ≠ cutPartition (n - 1) (c 2) :=
      c.toHom.map_adj ((SimpleGraph.top_adj (0 : Fin 3) 2).mpr hne02)
    cases hp0 : cutPartition (n - 1) (c 0) <;>
      cases hp1 : cutPartition (n - 1) (c 1) <;>
      cases hp2 : cutPartition (n - 1) (c 2) <;>
      simp_all
  · obtain ⟨c⟩ := hC
    have hEq : ∀ ⦃a b : Fin n⦄, G.Adj a b →
        cutPartition (n - 1) (c a) = cutPartition (n - 1) (c b) := by
      intro a b hab
      by_contra hne
      have hca : (bipartiteBy (cutPartition (n - 1)))ᶜ.Adj (c a) (c b) :=
        c.toHom.map_adj hab
      rw [SimpleGraph.compl_adj] at hca
      exact hca.2 hne
    have key : ∀ ⦃u v : Fin n⦄ (w : G.Walk u v),
        cutPartition (n - 1) (c u) = cutPartition (n - 1) (c v) := by
      intro u v w
      induction w with
      | nil => rfl
      | cons hadj _ ih => exact (hEq hadj).trans ih
    have hall : ∀ v : Fin n,
        cutPartition (n - 1) (c v) = cutPartition (n - 1) (c v₀) := by
      intro v
      obtain ⟨w⟩ : Nonempty (G.Walk v₀ v) := hG v₀ v
      exact (key w).symm
    cases hp0 : cutPartition (n - 1) (c v₀) with
    | true =>
      have hlt : ∀ v : Fin n, (c v).val < n - 1 := by
        intro v
        have h1 : cutPartition (n - 1) (c v) = true := by rw [hall v, hp0]
        exact of_decide_eq_true h1
      have hinj : Function.Injective
          (fun v : Fin n => (⟨(c v).val, hlt v⟩ : Fin (n - 1))) := by
        intro u v huv
        have hval : (c u).val = (c v).val :=
          congrArg (fun x : Fin (n - 1) => x.val) huv
        exact c.injective (Fin.val_injective hval)
      have hcard := Fintype.card_le_of_injective
        (fun v : Fin n => (⟨(c v).val, hlt v⟩ : Fin (n - 1))) hinj
      simp only [Fintype.card_fin] at hcard
      omega
    | false =>
      have hge : ∀ v : Fin n, n - 1 ≤ (c v).val := by
        intro v
        have h1 : cutPartition (n - 1) (c v) = false := by rw [hall v, hp0]
        have h2 : ¬ (c v).val < n - 1 := of_decide_eq_false h1
        omega
      have hlt : ∀ v : Fin n, (c v).val - (n - 1) < n - 1 := by
        intro v
        have hv : (c v).val < m := (c v).isLt
        have hu := hge v
        omega
      have hinj : Function.Injective
          (fun v : Fin n => (⟨(c v).val - (n - 1), hlt v⟩ : Fin (n - 1))) := by
        intro u v huv
        have hsub : (c u).val - (n - 1) = (c v).val - (n - 1) :=
          congrArg (fun x : Fin (n - 1) => x.val) huv
        have hu := hge u
        have hv := hge v
        have hval : (c u).val = (c v).val := by omega
        exact c.injective (Fin.val_injective hval)
      have hcard := Fintype.card_le_of_injective
        (fun v : Fin n => (⟨(c v).val - (n - 1), hlt v⟩ : Fin (n - 1))) hinj
      simp only [Fintype.card_fin] at hcard
      omega

end OMA

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.ramsey_ge := by
  intro n G hG
  exact le_csInf (OMA.ramsey_set_nonempty G) (OMA.ramsey_lower_bound G hG)
