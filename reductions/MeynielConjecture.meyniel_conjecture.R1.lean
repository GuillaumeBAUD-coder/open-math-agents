import FormalConjectures.Wikipedia.MeynielConjecture

-- Reduction MeynielConjecture.meyniel_conjecture.R1 of Meyniel's conjecture (c. 1985).
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The split separates the high-degree case of Meyniel's conjecture, which is handled by the
classical guarding argument, from the open core, which is the case of small maximum degree.

* `H1` (guarding a closed neighbourhood, a known and elementary fact about the game, not yet
  formalized for this definition): a cop sitting on `v` catches any robber that enters the
  closed neighbourhood `N[v]`, so `k + 1` cops win on a connected graph as soon as `k` cops win
  on every connected induced subgraph of `G - N[v]`.
* `H2` (the open core): Meyniel's conjecture for connected graphs on at most `N` vertices whose
  degrees are all below `√N`. It follows from the conjecture itself, so it is not stronger.

`main` is the counting step: as long as some vertex has degree at least `√N`, spend one cop on
it and recurse into the components of the rest, each of which has at least `√N + 1` fewer
vertices. At most `n / √n = √n` cops are spent this way, and `H2` handles what is left,
giving the bound `(C + 1) √n`. The helper lemmas prove that `CopsWin` is monotone in the number
of cops and that `CopsWin G (copNumber G)` holds.
-/

namespace OMA.R_MeynielConjecture_meyniel_conjecture_R1

open MeynielConjecture

/-- One cop guards a closed neighbourhood: if `k` cops win on every connected induced subgraph
avoiding the closed neighbourhood of `v`, then `k + 1` cops win on `G` (one cop sits on `v`,
the others walk into the robber's component and play the strategy there). -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ), G.Connected →
    (∀ s : Set V, s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u} → (G.induce s).Connected →
      CopsWin (G.induce s) k) →
    CopsWin G (k + 1)

/-- Meyniel's bound for graphs of small maximum degree: every connected graph on at most `N`
vertices, all of whose degrees are below `√N`, has cop number `O(√N)`. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    Fintype.card V ≤ N → (∀ v : V, ((G.neighborSet v).ncard : ℝ) < Real.sqrt N) →
    (copNumber G : ℝ) ≤ C * Real.sqrt N

lemma catch_extend {V : Type} (G : SimpleGraph V) {k k' : ℕ} (hk : k ≤ k') (x : V) :
    ∀ (m : ℕ) (c : Fin k → V) (r : V), CopsCatchWithin G k m c r →
      CopsCatchWithin G k' m (fun i => if h : i.val < k then c ⟨i.val, h⟩ else x) r := by
  intro m
  induction m with
  | zero =>
    rintro c r ⟨i, hi⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by simp [hi]⟩
  | succ m ih =>
    rintro c r (⟨i, hi⟩ | ⟨c', hstep, ⟨i, hi⟩ | hall⟩)
    · exact Or.inl ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by simp [hi]⟩
    · refine Or.inr ⟨fun i => if h : i.val < k then c' ⟨i.val, h⟩ else x, ?_,
        Or.inl ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by simp [hi]⟩⟩
      intro j
      by_cases h : j.val < k
      · simpa [h] using hstep ⟨j.val, h⟩
      · simp only [h, dite_false]; exact Or.inl rfl
    · refine Or.inr ⟨fun i => if h : i.val < k then c' ⟨i.val, h⟩ else x, ?_,
        Or.inr fun r' hr' => ih c' r' (hall r' hr')⟩
      intro j
      by_cases h : j.val < k
      · simpa [h] using hstep ⟨j.val, h⟩
      · simp only [h, dite_false]; exact Or.inl rfl

lemma copsWin_mono {V : Type} [Nonempty V] (G : SimpleGraph V) {k k' : ℕ} (hk : k ≤ k')
    (h : CopsWin G k) : CopsWin G k' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun i => if h : i.val < k then c ⟨i.val, h⟩ else Classical.arbitrary V, fun r => ?_⟩
  obtain ⟨m, hm⟩ := hc r
  exact ⟨m, catch_extend G hk _ m c r hm⟩

lemma copsWin_copNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    CopsWin G (copNumber G) :=
  Nat.sInf_mem (s := {k | CopsWin G k}) ⟨_, copsWin_card G⟩

/-- Removing a closed neighbourhood: the vertices outside it number at most `m - deg - 1`. -/
lemma ncard_outside {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) (s : Set V)
    (hs : s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u}) :
    s.ncard + (G.neighborSet v).ncard + 1 ≤ Fintype.card V := by
  have hd : Disjoint s (insert v (G.neighborSet v)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    rcases hs hu with ⟨h1, h2⟩
    rcases hu' with h | h
    · exact h1 h
    · exact h2 h
  have hv : v ∉ G.neighborSet v := by simp
  have h1 := Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hv (Set.toFinite _)] at h1
  have h2 : (s ∪ insert v (G.neighborSet v)).ncard ≤ (Set.univ : Set V).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h2
  omega

lemma induction_step (hH1 : H1) (C : ℝ)
    (hH2 : ∀ (N : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      Fintype.card V ≤ N → (∀ v : V, ((G.neighborSet v).ncard : ℝ) < Real.sqrt N) →
      (copNumber G : ℝ) ≤ C * Real.sqrt N)
    (N : ℕ) (hN : 1 ≤ N) :
    ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      Fintype.card V = m → m ≤ N →
      CopsWin G (⌊C * Real.sqrt N⌋₊ + ⌊(m : ℝ) / Real.sqrt N⌋₊) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro V _ G hG hm hmN
  have : Nonempty V := hG.nonempty
  by_cases hdeg : ∀ v : V, ((G.neighborSet v).ncard : ℝ) < Real.sqrt N
  · have hle := hH2 N V G hG (hm ▸ hmN) hdeg
    have : copNumber G ≤ ⌊C * Real.sqrt N⌋₊ := Nat.le_floor hle
    exact copsWin_mono G (le_trans this (Nat.le_add_right _ _)) (copsWin_copNumber G)
  · push Not at hdeg
    obtain ⟨v, hv⟩ := hdeg
    have hcount := ncard_outside G v ∅ (Set.empty_subset _)
    rw [Set.ncard_empty, hm] at hcount
    have hge1 : 1 ≤ ⌊(m : ℝ) / Real.sqrt N⌋₊ := by
      rw [Nat.one_le_floor_iff, one_le_div hsN]
      have : ((G.neighborSet v).ncard : ℝ) + 1 ≤ m := by exact_mod_cast (by omega)
      linarith
    obtain ⟨j, hj⟩ : ∃ j, ⌊(m : ℝ) / Real.sqrt N⌋₊ = j + 1 := ⟨_, (Nat.sub_add_cancel hge1).symm⟩
    rw [hj, ← add_assoc]
    refine hH1 V G v _ hG fun s hs hsc => ?_
    classical
    have : Nonempty s := hsc.nonempty
    have hc := ncard_outside G v s hs
    rw [hm] at hc
    have hcard : Fintype.card s = s.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hlt : s.ncard < m := by omega
    have hIH := ih s.ncard hlt s (G.induce s) hsc hcard (by omega)
    refine copsWin_mono _ ?_ hIH
    apply Nat.add_le_add_left
    have hj' : ⌊(s.ncard : ℝ) / Real.sqrt N⌋₊ < j + 1 := by
      rw [Nat.floor_lt (by positivity)]
      have hfl := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt N)
      rw [hj] at hfl
      have hreal : (s.ncard : ℝ) + ((G.neighborSet v).ncard : ℝ) + 1 ≤ m := by
        exact_mod_cast hc
      have : (s.ncard : ℝ) / Real.sqrt N < (m : ℝ) / Real.sqrt N - 1 := by
        rw [lt_sub_iff_add_lt, div_add_one hsN.ne', div_lt_div_iff_of_pos_right hsN]
        linarith
      push_cast at hfl ⊢
      linarith
    omega

theorem main : H1 → H2 → type_of% @MeynielConjecture.meyniel_conjecture := by
  rintro hH1 ⟨C, hC, hH2⟩
  refine ⟨C + 1, by linarith, fun V _ G hG => ?_⟩
  have : Nonempty V := hG.nonempty
  set n := Fintype.card V with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have hw := induction_step hH1 C hH2 n hn1 n V G hG rfl le_rfl
  have h1 : copNumber G ≤ ⌊C * Real.sqrt n⌋₊ + ⌊(n : ℝ) / Real.sqrt n⌋₊ := Nat.sInf_le hw
  have h2 : ((⌊C * Real.sqrt n⌋₊ : ℕ) : ℝ) ≤ C * Real.sqrt n :=
    Nat.floor_le (by positivity)
  have h3 : ((⌊(n : ℝ) / Real.sqrt n⌋₊ : ℕ) : ℝ) ≤ Real.sqrt n := by
    refine le_trans (Nat.floor_le (by positivity)) ?_
    rw [div_le_iff₀ hsn, Real.mul_self_sqrt (by positivity)]
  have h1' : (copNumber G : ℝ) ≤ ((⌊C * Real.sqrt n⌋₊ + ⌊(n : ℝ) / Real.sqrt n⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h1'
  linarith

end OMA.R_MeynielConjecture_meyniel_conjecture_R1
