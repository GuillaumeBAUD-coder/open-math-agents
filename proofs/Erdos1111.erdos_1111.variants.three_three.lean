import FormalConjectures.ErdosProblems.«1111»

-- Problem: Erdős Problem 1111 — three three
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1111.lean:99 (declaration Erdos1111.erdos_1111.variants.three_three)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open SimpleGraph

/-- A segment of a walk, as a walk. -/
lemma seg {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length) :
    ∃ q : G.Walk (p.getVert i) (p.getVert j), q.length = j - i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact ⟨Walk.nil, by simp⟩
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · obtain ⟨q, hq⟩ := ih (by omega) (by omega)
      refine ⟨q.concat (p.adj_getVert_succ (by omega)), ?_⟩
      rw [Walk.length_concat, hq]; omega
    · obtain rfl : i = j + 1 := by omega
      exact ⟨Walk.nil, by simp⟩

/-- A segment of a walk, as a walk in an induced subgraph containing it. -/
lemma segInd {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (S : Set V)
    (hS : ∀ n, p.getVert n ∈ S) (j : ℕ) (hj : j ≤ p.length) :
    ∃ q : (G.induce S).Walk ⟨p.getVert 0, hS 0⟩ ⟨p.getVert j, hS j⟩, q.length = j := by
  induction j with
  | zero => exact ⟨Walk.nil, by simp⟩
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih (by omega)
    have hadj : (G.induce S).Adj ⟨p.getVert j, hS j⟩ ⟨p.getVert (j + 1), hS (j + 1)⟩ := by
      simpa using p.adj_getVert_succ (by omega : j < p.length)
    refine ⟨q.concat hadj, ?_⟩
    rw [Walk.length_concat, hq]

/-- The colour of position `i` on a closed walk of length `k`. -/
def g (k i : ℕ) : ℕ := if i + 3 < k then i % 2 else i + 5 - k

lemma g_lt (k i : ℕ) (hi : i < k) : g k i < 5 := by
  unfold g; split_ifs <;> omega

lemma g_eq {k i j : ℕ} (hij : i < j) (hj : j < k) (h : g k i = g k j) :
    j + 3 < k ∧ (j - i) % 2 = 0 := by
  unfold g at h; split_ifs at h <;> omega

end OMA

open SimpleGraph in
theorem OMA.solution : type_of% @Erdos1111.erdos_1111.variants.three_three := by
  classical
  intro V _ G hG hT
  -- G is not 2-colourable
  have h2 : ¬ G.Colorable 2 := by
    intro h
    have := hG.trans h.chromaticNumber_le
    exact absurd this (by decide)
  rw [two_colorable_iff_forall_loop_even] at h2
  push_neg at h2
  obtain ⟨u0, w0, hw0⟩ := h2
  rw [Nat.not_even_iff_odd] at hw0
  have hex : ∃ k, ∃ u, ∃ w : G.Walk u u, w.length = k ∧ Odd k := ⟨_, u0, w0, rfl, hw0⟩
  obtain ⟨x, p, hpk, hodd⟩ := Nat.find_spec hex
  have hmin : ∀ u (w : G.Walk u u), Odd w.length → Nat.find hex ≤ w.length :=
    fun u w hw => Nat.find_min' hex ⟨u, w, rfl, hw⟩
  generalize Nat.find hex = k at hpk hodd hmin
  have hk0 : 0 < k := hodd.pos
  have hck : ∀ n, k ≤ n → p.getVert n = p.getVert 0 := by
    intro n hn
    rw [Walk.getVert_of_length_le p (by omega), Walk.getVert_zero]
  set N : Set V := {v | ∃ i, i < k ∧ G.Adj v (p.getVert i)} with hN
  set A : Set V := {v | ∃ n, v = p.getVert n} with hA
  have hAN : A ⊆ N := by
    rintro v ⟨n, rfl⟩
    have key : ∀ n, n < k → p.getVert n ∈ N := by
      intro n hn
      have hadj := p.adj_getVert_succ (by omega : n < p.length)
      rcases Nat.lt_or_ge (n + 1) k with h | h
      · exact ⟨n + 1, h, hadj⟩
      · exact ⟨0, hk0, by rw [← hck (n + 1) h]; exact hadj⟩
    rcases Nat.lt_or_ge n k with h | h
    · exact key n h
    · rw [hck n h]; exact key 0 hk0
  refine ⟨A, Nᶜ, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun v hv hv' => hv' (hAN hv)
  · rintro a ⟨n, rfl⟩ b hb hab
    apply hb
    rcases Nat.lt_or_ge n k with h | h
    · exact ⟨n, h, hab.symm⟩
    · exact ⟨0, hk0, by rw [← hck n h]; exact hab.symm⟩
  · obtain ⟨q, hq⟩ := OMA.segInd p A (fun n => ⟨n, rfl⟩) k (by omega)
    have hend : (⟨p.getVert k, ⟨k, rfl⟩⟩ : A) = ⟨p.getVert 0, ⟨0, rfl⟩⟩ :=
      Subtype.ext (hck k le_rfl)
    have := (q.copy rfl hend).three_le_chromaticNumber_of_odd_loop
      (by rw [Walk.length_copy, hq]; exact hodd)
    exact this
  · by_contra hcon
    have hB : (G.induce Nᶜ).Colorable 2 := by
      rw [← chromaticNumber_le_iff_colorable]
      exact Order.le_of_lt_add_one (not_le.mp hcon)
    obtain ⟨C2⟩ := hB
    -- key property of the colouring of N
    have hkey : ∀ i j u w, i < j → j < k → G.Adj u (p.getVert i) → G.Adj w (p.getVert j) →
        G.Adj u w → OMA.g k i ≠ OMA.g k j := by
      intro i j u w hij hj hu hw huw heq
      obtain ⟨h1, h2⟩ := OMA.g_eq hij hj heq
      obtain ⟨q, hq⟩ := OMA.seg p i j hij.le (by omega)
      have := hmin _ (Walk.cons hu.symm (Walk.cons huw (Walk.cons hw q.reverse))) (by
        simp only [Walk.length_cons, Walk.length_reverse, hq]
        rw [Nat.odd_iff]; omega)
      simp only [Walk.length_cons, Walk.length_reverse, hq] at this
      omega
    have hG7 : G.Colorable 7 := by
      rw [colorable_iff_exists_bdd_nat_coloring]
      refine ⟨Coloring.mk (fun v => if h : v ∈ N then OMA.g k (Classical.choose h)
        else 5 + (C2 ⟨v, h⟩ : ℕ)) ?_, ?_⟩
      · intro v w hvw
        by_cases hv : v ∈ N <;> by_cases hw : w ∈ N
        · simp only [dif_pos hv, dif_pos hw]
          obtain ⟨hi, hvi⟩ := Classical.choose_spec hv
          obtain ⟨hj, hwj⟩ := Classical.choose_spec hw
          rcases Nat.lt_trichotomy (Classical.choose hv) (Classical.choose hw) with h | h | h
          · exact hkey _ _ v w h hj hvi hwj hvw
          · intro _
            rw [← h] at hwj
            exact hT _ (is3Clique_triple_iff.mpr ⟨hvw, hvi, hwj⟩)
          · exact (hkey _ _ w v h hi hwj hvi hvw.symm).symm
        · simp only [dif_pos hv, dif_neg hw]
          have := OMA.g_lt k _ (Classical.choose_spec hv).1
          omega
        · simp only [dif_neg hv, dif_pos hw]
          have := OMA.g_lt k _ (Classical.choose_spec hw).1
          omega
        · simp only [dif_neg hv, dif_neg hw]
          have hadj : (G.induce Nᶜ).Adj ⟨v, hv⟩ ⟨w, hw⟩ := by simpa using hvw
          have := C2.valid hadj
          intro h
          apply this
          apply Fin.ext
          omega
      · intro v
        show (if h : v ∈ N then OMA.g k (Classical.choose h) else 5 + (C2 ⟨v, h⟩ : ℕ)) < 7
        split_ifs with h
        · have := OMA.g_lt k _ (Classical.choose_spec h).1
          omega
        · omega
    have := hG.trans hG7.chromaticNumber_le
    exact absurd this (by decide)
