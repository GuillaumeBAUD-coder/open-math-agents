import FormalConjectures.Wikipedia.MeynielConjecture

-- Reduction MeynielConjecture.meyniel_conjecture.variants.soft.R1 of The soft Meyniel conjecture.
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The split separates the high-degree case of the soft Meyniel conjecture, handled by the
classical guarding argument (the first step of Frankl 1987), from the open core, the case of
small maximum degree.

* `H1` (guarding a closed neighbourhood, a known and elementary fact about the game, not yet
  formalized for this definition): a cop sitting on `v` catches any robber that enters `N[v]`.
* `H2` (the open core): the soft bound `C N^(1-ε)` for connected graphs on at most `N` vertices
  whose degrees are all at most `N^δ`. It follows from the target itself, so it is not stronger.

`main` is the counting step: while some vertex has degree above `N^δ`, spend one cop on it and
recurse into the connected pieces of the rest, each with more than `N^δ` fewer vertices. At most
`n / n^δ = n^(1-δ)` cops are spent, and `H2` handles what is left, giving
`(C + 1) n^(1 - min δ ε)`.
-/

namespace OMA.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1

open MeynielConjecture

/-- **Guarding a closed neighbourhood (known).** One cop parked on `v` catches any robber that
enters the closed neighbourhood `N[v]`; the other `k` cops walk into the robber's component of
`G - N[v]` and play a winning strategy there. So `k + 1` cops win on a connected graph as soon
as `k` cops win on every connected induced subgraph avoiding `N[v]`. This is word for word the
`H1` of reduction `MeynielConjecture.meyniel_conjecture.R1`, so one proof serves both. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ), G.Connected →
    (∀ s : Set V, s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u} → (G.induce s).Connected →
      CopsWin (G.induce s) k) →
    CopsWin G (k + 1)

/-- **Soft Meyniel for graphs of small maximum degree (open).** There are `δ, ε, C > 0` such
that every connected graph on at most `N` vertices with maximum degree at most `N ^ δ` has
cop number at most `C N ^ (1 - ε)`. -/
def H2 : Prop :=
  ∃ δ ε C : ℝ, 0 < δ ∧ 0 < ε ∧ 0 < C ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), G.Connected →
      Fintype.card V ≤ N → (∀ v, ((G.neighborSet v).ncard : ℝ) ≤ (N : ℝ) ^ δ) →
        (copNumber G : ℝ) ≤ C * (N : ℝ) ^ (1 - ε)

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

/-- More cops never hurt: the extra cops idle on a fixed vertex. -/
lemma copsWin_mono {V : Type} [Nonempty V] (G : SimpleGraph V) {k k' : ℕ} (hk : k ≤ k')
    (h : CopsWin G k) : CopsWin G k' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun i => if h : i.val < k then c ⟨i.val, h⟩ else Classical.arbitrary V, fun r => ?_⟩
  obtain ⟨m, hm⟩ := hc r
  exact ⟨m, catch_extend G hk _ m c r hm⟩

lemma copsWin_copNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    CopsWin G (copNumber G) :=
  Nat.sInf_mem (s := {k | CopsWin G k}) ⟨_, copsWin_card G⟩

/-- `N[v]` and the rest of the graph partition the vertices. -/
lemma ncard_rest {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    ({u | u ≠ v ∧ ¬ G.Adj v u} : Set V).ncard + (G.neighborSet v).ncard + 1 =
      Fintype.card V := by
  have hset : ({u | u ≠ v ∧ ¬ G.Adj v u} : Set V) = (insert v (G.neighborSet v))ᶜ := by
    ext u
    simp [SimpleGraph.mem_neighborSet, eq_comm]
  have hnot : v ∉ G.neighborSet v := by simp
  have h := Set.ncard_add_ncard_compl (insert v (G.neighborSet v))
  rw [Set.ncard_insert_of_notMem hnot, Nat.card_eq_fintype_card] at h
  rw [hset]
  omega

/-- The induction: with `n ≤ N`, the cop number is at most `C N^(1-ε) + n / N^δ`. -/
lemma key (h1 : H1) (δ ε C : ℝ) (hC : 0 < C)
    (h2 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), G.Connected →
      Fintype.card V ≤ N → (∀ v, ((G.neighborSet v).ncard : ℝ) ≤ (N : ℝ) ^ δ) →
        (copNumber G : ℝ) ≤ C * (N : ℝ) ^ (1 - ε)) :
    ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), Fintype.card V = m →
      G.Connected → m ≤ N →
        (copNumber G : ℝ) ≤ C * (N : ℝ) ^ (1 - ε) + (m : ℝ) / (N : ℝ) ^ δ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro V _ G N hm hG hmN
  have hm1 : 1 ≤ m := by
    have := Fintype.card_pos_iff.2 hG.nonempty
    omega
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans hm1 hmN
  have hNd : (0 : ℝ) < (N : ℝ) ^ δ := Real.rpow_pos_of_pos (by linarith) δ
  have hCN : (0 : ℝ) ≤ C * (N : ℝ) ^ (1 - ε) :=
    mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  by_cases hdeg : ∀ v, ((G.neighborSet v).ncard : ℝ) ≤ (N : ℝ) ^ δ
  · have hb := h2 V G N hG (hm ▸ hmN) hdeg
    have : (0 : ℝ) ≤ (m : ℝ) / (N : ℝ) ^ δ := by positivity
    linarith
  · push Not at hdeg
    obtain ⟨v, hv⟩ := hdeg
    have hrest := ncard_rest G v
    rw [hm] at hrest
    have hrestR : ((({u | u ≠ v ∧ ¬ G.Adj v u} : Set V).ncard : ℕ) : ℝ) =
        (m : ℝ) - ((G.neighborSet v).ncard : ℝ) - 1 := by
      rw [← hrest]
      push_cast
      ring
    set x : ℝ := C * (N : ℝ) ^ (1 - ε) + ((m : ℝ) - (N : ℝ) ^ δ) / (N : ℝ) ^ δ with hx
    have hmx : (0 : ℝ) < (m : ℝ) - (N : ℝ) ^ δ := by
      have : (0 : ℝ) ≤ ((({u | u ≠ v ∧ ¬ G.Adj v u} : Set V).ncard : ℕ) : ℝ) := by positivity
      linarith
    have hx0 : 0 ≤ x := by
      have : (0 : ℝ) ≤ ((m : ℝ) - (N : ℝ) ^ δ) / (N : ℝ) ^ δ := by positivity
      linarith
    have hcomp : ∀ s : Set V, s ⊆ {u | u ≠ v ∧ ¬ G.Adj v u} → (G.induce s).Connected →
        CopsWin (G.induce s) ⌊x⌋₊ := by
      intro s hs hsc
      classical
      have : Nonempty s := hsc.nonempty
      have hcard : Fintype.card s ≤ ({u | u ≠ v ∧ ¬ G.Adj v u} : Set V).ncard := by
        rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hs
      have hlt : Fintype.card s < m := by omega
      have hcR : (Fintype.card s : ℝ) ≤ (m : ℝ) - (N : ℝ) ^ δ := by
        have : (Fintype.card s : ℝ) ≤
            ((({u | u ≠ v ∧ ¬ G.Adj v u} : Set V).ncard : ℕ) : ℝ) := by exact_mod_cast hcard
        linarith
      have hih := ih (Fintype.card s) hlt s (G.induce s) N rfl hsc (by omega)
      have hle : copNumber (G.induce s) ≤ ⌊x⌋₊ := by
        apply Nat.le_floor
        have : (Fintype.card s : ℝ) / (N : ℝ) ^ δ ≤ ((m : ℝ) - (N : ℝ) ^ δ) / (N : ℝ) ^ δ :=
          div_le_div_of_nonneg_right hcR hNd.le
        linarith
      exact copsWin_mono _ hle (copsWin_copNumber _)
    have hG' : copNumber G ≤ ⌊x⌋₊ + 1 := Nat.sInf_le (h1 V G v ⌊x⌋₊ hG hcomp)
    have hfl := Nat.floor_le hx0
    have hG'R : (copNumber G : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hG'
    have hsplit : ((m : ℝ) - (N : ℝ) ^ δ) / (N : ℝ) ^ δ = (m : ℝ) / (N : ℝ) ^ δ - 1 := by
      field_simp
    linarith

theorem main : H1 → H2 → type_of% @MeynielConjecture.meyniel_conjecture.variants.soft := by
  rintro h1 ⟨δ, ε, C, hδ, hε, hC, h2⟩
  refine ⟨min δ ε, C + 1, lt_min hδ hε, by linarith, ?_⟩
  intro V _ G hG
  have hn : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 hG.nonempty
  have hk := key h1 δ ε C hC h2 (Fintype.card V) V G (Fintype.card V) rfl hG le_rfl
  have e1 : (Fintype.card V : ℝ) ^ (1 - ε) ≤ (Fintype.card V : ℝ) ^ (1 - min δ ε) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith [min_le_right δ ε])
  have e2 : (Fintype.card V : ℝ) ^ (1 - δ) = (Fintype.card V : ℝ) / (Fintype.card V : ℝ) ^ δ := by
    rw [Real.rpow_sub (by linarith) 1 δ, Real.rpow_one]
  have e3 : (Fintype.card V : ℝ) ^ (1 - δ) ≤ (Fintype.card V : ℝ) ^ (1 - min δ ε) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith [min_le_left δ ε])
  have e4 := mul_le_mul_of_nonneg_left e1 hC.le
  rw [← e2] at hk
  linarith

end OMA.R_MeynielConjecture_meyniel_conjecture_variants_soft_R1
