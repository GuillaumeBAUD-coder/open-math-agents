import FormalConjectures.Wikipedia.MeynielConjecture

-- Problem: Scott–Sudakov (2011): the best known general bound.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/MeynielConjecture.lean:141 (declaration MeynielConjecture.meyniel_conjecture.variants.scott_sudakov)
-- Credit: @tatashbar (the owner of the agent is credited as the solver)

/-!
A full proof of the Scott–Sudakov bound `c(G) ≤ n / 2 ^ ((1 - o(1)) √(log₂ n))`, following
Scott and Sudakov, *A bound for the cops and robbers problem*, SIAM J. Discrete Math. 25 (2011).

* Part 1: the counting recursion. Given the two ingredients `H1` and `H2` below, spend one cop
  on a long shortest path and recurse. The recursion and the asymptotics were first written as
  a reduction draft for this problem by another agent session of the same owner.
* Part 2 (`H1`): one cop guards a shortest path (Aigner and Fromme 1984), composed with the
  other cops. The composition follows the closed-neighbourhood guarding proof of pull request
  1262 (step `H1` of the Meyniel reduction).
* Part 3 (`H2`): the bounded-diameter lemma (Lemma 2.2 of the paper).
-/

open Filter

namespace OMA.SS

open MeynielConjecture

/-- **Guarding a shortest path (Aigner and Fromme 1984, known).** If `p` is a shortest walk in a
connected graph and `k` cops win on every connected induced subgraph avoiding the vertices of
`p`, then `k + 1` cops win on the graph. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (u v : V) (p : G.Walk u v) (k : ℕ),
    G.Connected → p.length = G.dist u v →
    (∀ s : Set V, s ⊆ {w | w ∉ p.support} → (G.induce s).Connected →
      CopsWin (G.induce s) k) →
    CopsWin G (k + 1)

/-- **The bounded-diameter case (Scott and Sudakov, Lemma 2.2, known).** Connected graphs with at most `N`
vertices and diameter at most `D N` have cop number at most `N / 2^((1 - f N) √(log₂ N))`,
where `f → 0` and `D N + 1 ≥ 2^((1 - f N) √(log₂ N))`. -/
def H2 : Prop :=
  ∃ (f : ℕ → ℝ) (D : ℕ → ℕ), Tendsto f atTop (nhds 0) ∧
    (∀ N : ℕ, (2 : ℝ) ^ ((1 - f N) * Real.sqrt (Real.logb 2 N)) ≤ (D N : ℝ) + 1) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), G.Connected →
      Fintype.card V ≤ N → (∀ u v, G.dist u v ≤ D N) →
        (copNumber G : ℝ) ≤ (N : ℝ) / 2 ^ ((1 - f N) * Real.sqrt (Real.logb 2 N))

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

/-- Removing the vertices of a path with `L + 1` vertices leaves `m - (L + 1)` vertices. -/
lemma ncard_off_path {V : Type} [Fintype V] (G : SimpleGraph V) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) :
    ({w | w ∉ p.support} : Set V).ncard + (p.length + 1) = Fintype.card V := by
  classical
  have hset : ({w | w ∉ p.support} : Set V) = ((p.support.toFinset : Finset V) : Set V)ᶜ := by
    ext w; simp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support]
  have h := Set.ncard_add_ncard_compl ((p.support.toFinset : Finset V) : Set V)
  rw [Set.ncard_coe_finset, hcard, Nat.card_eq_fintype_card] at h
  rw [hset]
  omega

/-- The induction: with `n ≤ N` vertices, the cop number is at most `B N + n / (D N + 1)`. -/
lemma key (h1 : H1) (B : ℕ → ℝ) (hB : ∀ N, 0 ≤ B N) (D : ℕ → ℕ)
    (h2 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), G.Connected →
      Fintype.card V ≤ N → (∀ u v, G.dist u v ≤ D N) → (copNumber G : ℝ) ≤ B N) :
    ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), Fintype.card V = m →
      G.Connected → m ≤ N →
        (copNumber G : ℝ) ≤ B N + (m : ℝ) / ((D N : ℝ) + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro V _ G N hm hG hmN
  have hD : (0 : ℝ) < (D N : ℝ) + 1 := by positivity
  by_cases hdiam : ∀ u v, G.dist u v ≤ D N
  · have hb := h2 V G N hG (hm ▸ hmN) hdiam
    have : (0 : ℝ) ≤ (m : ℝ) / ((D N : ℝ) + 1) := by positivity
    linarith
  · push Not at hdiam
    obtain ⟨u, v, huv⟩ := hdiam
    obtain ⟨p, hp, hlen⟩ := hG.exists_path_of_dist u v
    have hrest := ncard_off_path G p hp
    rw [hm] at hrest
    set R : Set V := {w | w ∉ p.support} with hR
    set x : ℝ := B N + ((m : ℝ) - ((D N : ℝ) + 2)) / ((D N : ℝ) + 1) with hx
    have hlenD : D N + 1 ≤ p.length := by omega
    have hmD : (D N : ℝ) + 2 ≤ (m : ℝ) := by
      have : D N + 2 ≤ m := by omega
      exact_mod_cast this
    have hx0 : 0 ≤ x := by
      have : (0 : ℝ) ≤ ((m : ℝ) - ((D N : ℝ) + 2)) / ((D N : ℝ) + 1) := by
        apply div_nonneg _ hD.le; linarith
      linarith [hB N]
    have hcomp : ∀ s : Set V, s ⊆ R → (G.induce s).Connected →
        CopsWin (G.induce s) ⌊x⌋₊ := by
      intro s hs hsc
      classical
      have : Nonempty s := hsc.nonempty
      have hcard : Fintype.card s ≤ R.ncard := by
        rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hs
      have hlt : Fintype.card s < m := by omega
      have hcR : (Fintype.card s : ℝ) ≤ (m : ℝ) - ((D N : ℝ) + 2) := by
        have h3 : Fintype.card s + (D N + 2) ≤ m := by omega
        have h4 : ((Fintype.card s + (D N + 2) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
        push_cast at h4
        linarith
      have hih := ih (Fintype.card s) hlt s (G.induce s) N rfl hsc (by omega)
      have hle : copNumber (G.induce s) ≤ ⌊x⌋₊ := by
        apply Nat.le_floor
        have : (Fintype.card s : ℝ) / ((D N : ℝ) + 1) ≤
            ((m : ℝ) - ((D N : ℝ) + 2)) / ((D N : ℝ) + 1) :=
          div_le_div_of_nonneg_right hcR hD.le
        linarith
      exact copsWin_mono _ hle (copsWin_copNumber _)
    have hG' : copNumber G ≤ ⌊x⌋₊ + 1 := Nat.sInf_le (h1 V G u v p ⌊x⌋₊ hG hlen hcomp)
    have hfl := Nat.floor_le hx0
    have hG'R : (copNumber G : ℝ) ≤ (⌊x⌋₊ : ℝ) + 1 := by exact_mod_cast hG'
    have hsplit : ((m : ℝ) - ((D N : ℝ) + 2)) / ((D N : ℝ) + 1) + 1 =
        ((m : ℝ) - 1) / ((D N : ℝ) + 1) := by
      field_simp; ring
    have hfin : ((m : ℝ) - 1) / ((D N : ℝ) + 1) ≤ (m : ℝ) / ((D N : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    linarith

lemma tendsto_inv_sqrt_logb :
    Tendsto (fun n : ℕ => (Real.sqrt (Real.logb 2 n))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop))

theorem main : H1 → H2 →
    type_of% @MeynielConjecture.meyniel_conjecture.variants.scott_sudakov := by
  rintro h1 ⟨f, D, hf, hD, h2⟩
  refine ⟨fun n => f n + (Real.sqrt (Real.logb 2 n))⁻¹, by
    simpa using hf.add tendsto_inv_sqrt_logb, ?_⟩
  intro V _ G hG
  set n := Fintype.card V with hn
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 hG.nonempty
  have hpos2 : ∀ a : ℝ, (0 : ℝ) < 2 ^ a := fun a => Real.rpow_pos_of_pos two_pos a
  set B : ℕ → ℝ := fun N => (N : ℝ) / 2 ^ ((1 - f N) * Real.sqrt (Real.logb 2 N)) with hBdef
  have hB : ∀ N, 0 ≤ B N := fun N => div_nonneg (Nat.cast_nonneg _) (hpos2 _).le
  have hk := key h1 B hB D h2 n V G n rfl hG le_rfl
  rcases Nat.lt_or_ge n 2 with h | h
  · -- a single vertex
    have hn' : n = 1 := by omega
    have hc : copNumber G ≤ 1 := by
      have h0 : copNumber G ≤ Fintype.card V :=
        Nat.sInf_le (show Fintype.card V ∈ {k | CopsWin G k} from copsWin_card G)
      omega
    rw [hn']
    simp only [Nat.cast_one, Real.logb_one, Real.sqrt_zero, mul_zero, Real.rpow_zero,
      div_one]
    exact_mod_cast hc
  · set s := Real.sqrt (Real.logb 2 n) with hs
    have hlog : 0 < Real.logb 2 n := by
      apply Real.logb_pos one_lt_two
      exact_mod_cast h
    have hs0 : 0 < s := Real.sqrt_pos.2 hlog
    set a := (1 - f n) * s with ha
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2a := hpos2 a
    have hDn : (2 : ℝ) ^ a ≤ (D n : ℝ) + 1 := hD n
    have hdiv : (n : ℝ) / ((D n : ℝ) + 1) ≤ (n : ℝ) / 2 ^ a :=
      div_le_div_of_nonneg_left hnR h2a hDn
    have hexp : (1 - (f n + s⁻¹)) * s = a - 1 := by
      rw [ha]; field_simp; ring
    rw [hexp, Real.rpow_sub two_pos, Real.rpow_one]
    have hB' : B n = (n : ℝ) / 2 ^ a := rfl
    have : (n : ℝ) / (2 ^ a / 2) = 2 * ((n : ℝ) / 2 ^ a) := by
      field_simp
    rw [this]
    linarith

end OMA.SS

/-
One cop guards a shortest path (Aigner and Fromme 1984), composed with `k` other cops.

Let `p` be a shortest walk from `u` to `v`, of length `L`, with vertices `q 0, …, q L`, and
let `a r = min (dist u r) L`. The function `a` changes by at most one when the robber moves,
and `q (a r) = r` when `r` is on the path. The guard *shadows* the robber when it stands on
`q i` with `|i - a r| ≤ 1` at the start of a round. A shadowing guard steps to `q (a r)`:
this catches a robber standing on the path, and otherwise the guard shadows again after the
robber's move.

All cops start on `u = q 0`. First the guard walks up the path until it shadows the robber
(at most `L` rounds, since the guard never overtakes `a r`). From then on a robber entering
the path is caught in the next round, so the robber is confined to one component `s` of the
graph minus the path. The other `k` cops walk to the starting squares of a winning strategy
on `s` and play it.
-/

namespace OMA

open SimpleGraph MeynielConjecture

variable {V : Type} {G : SimpleGraph V}

/-- One more round never hurts the cops. -/
theorem catch_succ {k : ℕ} : ∀ (m : ℕ) (c : Fin k → V) (r : V),
    CopsCatchWithin G k m c r → CopsCatchWithin G k (m + 1) c r := by
  intro m
  induction m with
  | zero => intro c r h; exact Or.inl h
  | succ m ih =>
    rintro c r (h | ⟨c', hs, h | h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c', hs, Or.inl h⟩
    · exact Or.inr ⟨c', hs, Or.inr fun r' hr' => ih c' r' (h r' hr')⟩

theorem catch_mono {k m m' : ℕ} (hm : m ≤ m') {c : Fin k → V} {r : V}
    (h : CopsCatchWithin G k m c r) : CopsCatchWithin G k m' c r := by
  induction hm with
  | refl => exact h
  | step _ ih => exact catch_succ _ _ _ ih

/-- From `c ≠ r` one can step to a neighbour of `c` that is closer to `r`. -/
theorem step_toward (hc : G.Connected) {c r : V} (hne : c ≠ r) :
    ∃ c', G.Adj c c' ∧ G.dist c' r + 1 = G.dist c r := by
  obtain ⟨p, hpl⟩ := hc.exists_walk_length_eq_dist c r
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ c' _ h q =>
    refine ⟨c', h, ?_⟩
    rw [Walk.length_cons] at hpl
    have h1 := dist_le q
    have h2 := hc.dist_triangle (u := c) (v := c') (w := r)
    have h3 : G.dist c c' = 1 := dist_eq_one_iff_adj.mpr h
    omega

/-- What the guard needs from a shortest path: positions `q 0, …, q L` in a row, and a height
function `a` that moves by at most one per step and is a left inverse of `q` on the path `P`. -/
structure Guard (G : SimpleGraph V) (P : Set V) (q : ℕ → V) (a : V → ℕ) (L : ℕ) : Prop where
  le : ∀ r, a r ≤ L
  lip : ∀ r r', Step G r r' → a r' ≤ a r + 1 ∧ a r ≤ a r' + 1
  adj : ∀ i, i < L → G.Adj (q i) (q (i + 1))
  sec : ∀ r ∈ P, q (a r) = r

/-- The guard on `g` shadows the robber on `r`. -/
def Shadow (q : ℕ → V) (a : V → ℕ) (L : ℕ) (g r : V) : Prop :=
  ∃ i, i ≤ L ∧ g = q i ∧ i ≤ a r + 1 ∧ a r ≤ i + 1

/-- A shadowing guard can step onto the robber's height. -/
theorem guard_move {P : Set V} {q : ℕ → V} {a : V → ℕ} {L : ℕ} (hg : Guard G P q a L)
    {g r : V} (h : Shadow q a L g r) : Step G g (q (a r)) := by
  obtain ⟨i, hiL, rfl, h1, h2⟩ := h
  have hle := hg.le r
  rcases Nat.lt_trichotomy i (a r) with h3 | h3 | h3
  · have h4 : a r = i + 1 := by omega
    rw [h4]
    exact Or.inr (hg.adj i (by omega))
  · rw [h3]
    exact Or.inl rfl
  · have h4 : i = a r + 1 := by omega
    rw [h4]
    exact Or.inr (hg.adj (a r) (by omega)).symm

/-- After stepping onto the robber's height, the guard shadows the robber again. -/
theorem shadow_next {P : Set V} {q : ℕ → V} {a : V → ℕ} {L : ℕ} (hg : Guard G P q a L)
    {r r' : V} (h : Step G r r') : Shadow q a L (q (a r)) r' :=
  ⟨a r, hg.le r, rfl, (hg.lip r r' h).2, (hg.lip r r' h).1⟩

/-- A shadowing guard catches a robber standing on the path in one round. -/
theorem catch_on_path {k : ℕ} {P : Set V} {q : ℕ → V} {a : V → ℕ} {L : ℕ}
    (hg : Guard G P q a L) (d : Fin k → V) {g r : V} (h : Shadow q a L g r) (hr : r ∈ P) :
    CopsCatchWithin G (k + 1) 1 (Fin.cons g d) r := by
  refine Or.inr ⟨Fin.cons (q (a r)) d, fun i => ?_, Or.inl ⟨0, by simp [hg.sec r hr]⟩⟩
  cases i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact guard_move hg h
  | succ j => simp only [Fin.cons_succ]; exact Or.inl rfl

/-- A strategy on the induced subgraph on `s` lifts to `G`, with one extra cop shadowing. -/
theorem transfer {k : ℕ} {P : Set V} {q : ℕ → V} {a : V → ℕ} {L : ℕ} (hg : Guard G P q a L)
    (s : Set V) (hcl : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s ∨ y ∈ P) :
    ∀ (m : ℕ) (c : Fin k → s) (r : s) (g : V), Shadow q a L g r →
      CopsCatchWithin (G.induce s) k m c r →
      CopsCatchWithin G (k + 1) (m + 1) (Fin.cons g (fun i => (c i : V))) r := by
  intro m
  induction m with
  | zero =>
    rintro c r g - ⟨i, hi⟩
    exact Or.inl ⟨i.succ, by simp [hi]⟩
  | succ m ih =>
    rintro c r g hsh (⟨i, hi⟩ | ⟨c', hs, h⟩)
    · exact Or.inl ⟨i.succ, by simp [hi]⟩
    · refine Or.inr ⟨Fin.cons (q (a r)) (fun i => (c' i : V)), fun i => ?_, ?_⟩
      · cases i using Fin.cases with
        | zero => simp only [Fin.cons_zero]; exact guard_move hg hsh
        | succ j =>
          simp only [Fin.cons_succ]
          rcases hs j with h1 | h1
          · exact Or.inl (congrArg Subtype.val h1)
          · exact Or.inr h1
      · rcases h with ⟨i, hi⟩ | h
        · exact Or.inl ⟨i.succ, by simp [hi]⟩
        · right
          intro r' hr'
          have hsh' : Shadow q a L (q (a r)) r' := shadow_next hg hr'
          by_cases hrs : r' ∈ s
          · refine ih c' ⟨r', hrs⟩ _ hsh' (h ⟨r', hrs⟩ ?_)
            rcases hr' with h2 | h2
            · exact Or.inl (Subtype.ext h2)
            · exact Or.inr h2
          · have hP : r' ∈ P := by
              rcases hr' with h2 | h2
              · exact absurd (by rw [← h2]; exact r.2) hrs
              · exact (hcl r r.2 r' h2).resolve_left hrs
            exact catch_mono (by omega) (catch_on_path hg _ hsh' hP)

/-- The other cops walk to their starting squares in `s` while the guard shadows. -/
theorem walk_in (hG : G.Connected) {k : ℕ} {P : Set V} {q : ℕ → V} {a : V → ℕ} {L : ℕ}
    (hg : Guard G P q a L) (s : Set V) (hcl : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s ∨ y ∈ P)
    (t : Fin k → s) (M : ℕ) (hM : ∀ r : s, CopsCatchWithin (G.induce s) k M t r) :
    ∀ (D : ℕ) (d : Fin k → V), (∀ i, G.dist (d i) (t i) ≤ D) →
      ∀ r ∈ s, ∀ g, Shadow q a L g r →
        CopsCatchWithin G (k + 1) (D + M + 1) (Fin.cons g d) r := by
  intro D
  induction D with
  | zero =>
    intro d hd r hr g hsh
    have hdt : d = fun i => (t i : V) :=
      funext fun i => hG.dist_eq_zero_iff.mp (by have := hd i; omega)
    subst hdt
    rw [Nat.zero_add]
    exact transfer hg s hcl M t ⟨r, hr⟩ g hsh (hM ⟨r, hr⟩)
  | succ D ih =>
    intro d hd r hr g hsh
    have hstep : ∀ i, ∃ e, Step G (d i) e ∧ G.dist e (t i) ≤ D := by
      intro i
      by_cases hi : d i = t i
      · exact ⟨d i, Or.inl rfl, by rw [hi, dist_self]; omega⟩
      · obtain ⟨e, he, hde⟩ := step_toward hG hi
        exact ⟨e, Or.inr he, by have := hd i; omega⟩
    choose e he hed using hstep
    refine Or.inr ⟨Fin.cons (q (a r)) e, fun i => ?_, Or.inr fun r' hr' => ?_⟩
    · cases i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact guard_move hg hsh
      | succ j => simp only [Fin.cons_succ]; exact he j
    · have hlev : D + 1 + M = D + M + 1 := by omega
      rw [hlev]
      have hsh' : Shadow q a L (q (a r)) r' := shadow_next hg hr'
      by_cases hrs : r' ∈ s
      · exact ih e hed r' hrs _ hsh'
      · have hP : r' ∈ P := by
          rcases hr' with h2 | h2
          · exact absurd (by rw [← h2]; exact hr) hrs
          · exact (hcl r hr r' h2).resolve_left hrs
        exact catch_mono (by omega) (catch_on_path hg _ hsh' hP)

/-- The guard walks up the path until it shadows the robber; the other cops wait. -/
theorem approach {k : ℕ} {P : Set V} {q : ℕ → V} {a : V → ℕ} {L : ℕ} (hg : Guard G P q a L)
    (d : Fin k → V) (T : ℕ)
    (hT : ∀ g r, Shadow q a L g r → CopsCatchWithin G (k + 1) T (Fin.cons g d) r) :
    ∀ (n i : ℕ) (r : V), L ≤ i + n → i ≤ a r →
      CopsCatchWithin G (k + 1) (n + T) (Fin.cons (q i) d) r := by
  intro n
  induction n with
  | zero =>
    intro i r hL hi
    have hle := hg.le r
    exact catch_mono (by omega) (hT _ _ ⟨i, by omega, rfl, by omega, by omega⟩)
  | succ n ih =>
    intro i r hL hi
    have hle := hg.le r
    by_cases hnear : a r ≤ i + 1
    · exact catch_mono (by omega) (hT _ _ ⟨i, by omega, rfl, by omega, hnear⟩)
    · have hrw : n + 1 + T = n + T + 1 := by omega
      rw [hrw]
      refine Or.inr ⟨Fin.cons (q (i + 1)) d, fun j => ?_, Or.inr fun r' hr' => ?_⟩
      · cases j using Fin.cases with
        | zero => simp only [Fin.cons_zero]; exact Or.inr (hg.adj i (by omega))
        | succ j => simp only [Fin.cons_succ]; exact Or.inl rfl
      · have hl := hg.lip r r' hr'
        exact ih (i + 1) r' (by omega) (by omega)

/-- A shortest walk gives the data the guard needs. -/
theorem guard_of_shortest (hG : G.Connected) {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) :
    Guard G {w | w ∈ p.support} p.getVert (fun r => min (G.dist u r) p.length) p.length := by
  have hadj : ∀ i, i < p.length → G.Adj (p.getVert i) (p.getVert (i + 1)) :=
    fun i hi => p.adj_getVert_succ hi
  have hup : ∀ j, j ≤ p.length → G.dist u (p.getVert j) ≤ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hG.dist_triangle (u := u) (v := p.getVert j) (w := p.getVert (j + 1))
      have h3 : G.dist (p.getVert j) (p.getVert (j + 1)) = 1 :=
        dist_eq_one_iff_adj.mpr (hadj j (by omega))
      omega
  have hdown : ∀ m, m ≤ p.length → G.dist (p.getVert (p.length - m)) v ≤ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hG.dist_triangle (u := p.getVert (p.length - (m + 1)))
        (v := p.getVert (p.length - m)) (w := v)
      have h3 : G.dist (p.getVert (p.length - (m + 1))) (p.getVert (p.length - m)) = 1 := by
        have h4 := hadj (p.length - (m + 1)) (by omega)
        rw [show p.length - (m + 1) + 1 = p.length - m by omega] at h4
        exact dist_eq_one_iff_adj.mpr h4
      omega
  have hdist : ∀ j, j ≤ p.length → G.dist u (p.getVert j) = j := by
    intro j hj
    have h1 := hup j hj
    have h2 := hdown (p.length - j) (by omega)
    rw [show p.length - (p.length - j) = j by omega] at h2
    have h3 := hG.dist_triangle (u := u) (v := p.getVert j) (w := v)
    omega
  refine ⟨fun r => min_le_right _ _, ?_, hadj, ?_⟩
  · intro r r' hr'
    have h1 := hG.dist_triangle (u := u) (v := r) (w := r')
    have h2 := hG.dist_triangle (u := u) (v := r') (w := r)
    have h3 : G.dist r r' ≤ 1 := by
      rcases hr' with h | h
      · rw [h, dist_self]; omega
      · exact (dist_eq_one_iff_adj.mpr h).le
    have h4 : G.dist r' r ≤ 1 := by rw [dist_comm]; exact h3
    constructor
    · show min (G.dist u r') p.length ≤ min (G.dist u r) p.length + 1
      omega
    · show min (G.dist u r) p.length ≤ min (G.dist u r') p.length + 1
      omega
  · intro r hr
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hr
    subst hn
    show p.getVert (min (G.dist u (p.getVert n)) p.length) = p.getVert n
    rw [hdist n hnl, min_eq_left hnl]

/-- Guarding a shortest path: the statement of step `H1`. -/
theorem path_guard (V : Type) [Fintype V] (G : SimpleGraph V) (u v : V) (p : G.Walk u v)
    (k : ℕ) (hG : G.Connected) (hlen : p.length = G.dist u v)
    (hyp : ∀ s : Set V, s ⊆ {w | w ∉ p.support} → (G.induce s).Connected →
      CopsWin (G.induce s) k) :
    CopsWin G (k + 1) := by
  classical
  have hg := guard_of_shortest hG p hlen
  have hloc : ∀ r : V, ∃ N, ∀ g,
      Shadow p.getVert (fun r => min (G.dist u r) p.length) p.length g r →
        CopsCatchWithin G (k + 1) N (Fin.cons g (fun _ => u)) r := by
    intro r
    by_cases hrP : r ∈ p.support
    · exact ⟨1, fun g hsh => catch_on_path hg _ hsh hrP⟩
    · let R : Set V := {w | w ∉ p.support}
      have hrR : r ∈ R := hrP
      let s : Set V := {w | ∃ hw : w ∈ R, (G.induce R).Reachable ⟨r, hrR⟩ ⟨w, hw⟩}
      have hsR : s ⊆ R := fun w hw => hw.1
      have hrs : r ∈ s := ⟨hrR, Reachable.refl _⟩
      have hcl : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s ∨ y ∈ {w | w ∈ p.support} := by
        rintro x ⟨hxR, hx⟩ y hxy
        by_cases hyR : y ∈ R
        · exact Or.inl ⟨hyR, hx.trans
            (Adj.reachable (show (G.induce R).Adj ⟨x, hxR⟩ ⟨y, hyR⟩ from hxy))⟩
        · exact Or.inr (not_not.mp hyR)
      have key : ∀ b : R, Relation.ReflTransGen (G.induce R).Adj ⟨r, hrR⟩ b →
          ∀ hb : (b : V) ∈ s, (G.induce s).Reachable ⟨r, hrs⟩ ⟨b, hb⟩ := by
        intro b hb
        induction hb with
        | refl => intro _; exact Reachable.refl _
        | @tail b' c' hab hbc ih =>
          intro hc
          have hb's : (b' : V) ∈ s := ⟨b'.2, (reachable_iff_reflTransGen _ _).mpr hab⟩
          exact (ih hb's).trans
            (Adj.reachable (show (G.induce s).Adj ⟨b', hb's⟩ ⟨c', hc⟩ from hbc))
      have hbase : ∀ x : s, (G.induce s).Reachable ⟨r, hrs⟩ x := fun x =>
        key ⟨x.1, x.2.1⟩ ((reachable_iff_reflTransGen _ _).mp x.2.2) x.2
      have hconn : (G.induce s).Connected := by
        rw [connected_iff]
        exact ⟨fun x y => (hbase x).symm.trans (hbase y), ⟨⟨r, hrs⟩⟩⟩
      obtain ⟨t, ht⟩ := hyp s hsR hconn
      choose f hf using ht
      have hM : ∀ r : s, CopsCatchWithin (G.induce s) k (Finset.univ.sup f) t r :=
        fun r => catch_mono (Finset.le_sup (Finset.mem_univ r)) (hf r)
      exact ⟨_, fun g hsh => walk_in hG hg s hcl t _ hM
        (Finset.univ.sup fun i => G.dist u (t i)) _
        (fun i => Finset.le_sup (f := fun i => G.dist u (t i)) (Finset.mem_univ i))
        r hrs g hsh⟩
  choose N hN using hloc
  refine ⟨Fin.cons u (fun _ => u), fun r => ⟨p.length + Finset.univ.sup N, ?_⟩⟩
  have hT : ∀ g r, Shadow p.getVert (fun r => min (G.dist u r) p.length) p.length g r →
      CopsCatchWithin G (k + 1) (Finset.univ.sup N) (Fin.cons g (fun _ => u)) r :=
    fun g r hsh => catch_mono (Finset.le_sup (Finset.mem_univ r)) (hN r g hsh)
  have hfin := approach hg (fun _ => u) _ hT p.length 0 r (by omega) (Nat.zero_le _)
  rw [Walk.getVert_zero] at hfin
  exact hfin

end OMA

/-
Part A (deterministic): cops walking to fixed targets. Follows Lemma 2.2 of Scott and Sudakov,
*A bound for the cops and robbers problem* (SIAM J. Discrete Math. 25, 2011), with one change of
timing: the cops move first, so a cop within distance `m + 1` of a vertex catches a robber who
is there after `m` robber moves. This makes the scheme uniform, with radii `2 ^ j` and robber
times `2 ^ j - 1`, and removes the separate degree case of the paper.
-/

namespace OMA

section BoundedDiameter

open SimpleGraph MeynielConjecture
open Classical

section Game

variable {V : Type} {G : SimpleGraph V}

/-- Every cop moves one step closer to its target (or stays on it). -/
theorem advance (hG : G.Connected) {k : ℕ} (c τ : Fin k → V) :
    ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
      ∀ i, G.dist (c' i) (τ i) ≤ G.dist (c i) (τ i) - 1 := by
  have h : ∀ i, ∃ e, Step G (c i) e ∧ G.dist e (τ i) ≤ G.dist (c i) (τ i) - 1 := by
    intro i
    by_cases hi : c i = τ i
    · exact ⟨c i, Or.inl rfl, by simp [hi]⟩
    · obtain ⟨e, he, hde⟩ := step_toward hG hi
      exact ⟨e, Or.inr he, by omega⟩
  choose e he hed using h
  exact ⟨e, he, hed⟩

/-- The trap lemma. Cop `i` walks to a target `τ i` at distance at most `ρ i`. If the robber's
possible positions after `m` moves, apart from targets reached in time, form sets `W m` with
`W M` empty, the robber is caught within `M + 1` rounds. -/
theorem trap (hG : G.Connected) {k : ℕ} (τ : Fin k → V) (ρ : Fin k → ℕ) (W : ℕ → Set V) (M : ℕ)
    (hW : ∀ m, ∀ r ∈ W m, ∀ r', Step G r r' →
      r' ∈ W (m + 1) ∨ ∃ i, τ i = r' ∧ ρ i ≤ m + 2)
    (hM : W M = ∅) :
    ∀ (n m : ℕ) (c : Fin k → V) (r : V), m + n = M →
      (∀ i, G.dist (c i) (τ i) ≤ ρ i - m) →
      (r ∈ W m ∨ ∃ i, τ i = r ∧ ρ i ≤ m + 1) → CopsCatchWithin G k (n + 1) c r := by
  intro n
  induction n with
  | zero =>
    intro m c r hm hc hgood
    obtain ⟨c', hstep, hd⟩ := advance hG c τ
    rcases hgood with hr | ⟨i, hi, hρ⟩
    · have hmM : m = M := by omega
      rw [hmM, hM] at hr
      exact absurd hr (Set.notMem_empty _)
    · refine Or.inr ⟨c', hstep, Or.inl ⟨i, ?_⟩⟩
      rw [← hi]
      exact hG.dist_eq_zero_iff.mp (by have := hd i; have := hc i; omega)
  | succ n ih =>
    intro m c r hm hc hgood
    obtain ⟨c', hstep, hd⟩ := advance hG c τ
    rcases hgood with hr | ⟨i, hi, hρ⟩
    · refine Or.inr ⟨c', hstep, Or.inr fun r' hr' => ?_⟩
      refine ih (m + 1) c' r' (by omega) (fun i => by have := hd i; have := hc i; omega) ?_
      rcases hW m r hr r' hr' with h | ⟨i, hi, hρ⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, by omega⟩
    · refine Or.inr ⟨c', hstep, Or.inl ⟨i, ?_⟩⟩
      rw [← hi]
      exact hG.dist_eq_zero_iff.mp (by have := hd i; have := hc i; omega)

end Game

section Strategy

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- The vertices within distance `ρ` of the set `A`. -/
noncomputable def nbhd (G : SimpleGraph V) (A : Finset V) (ρ : ℕ) : Finset V :=
  Finset.univ.filter fun w => ∃ a ∈ A, G.dist a w ≤ ρ

theorem mem_nbhd {A : Finset V} {ρ : ℕ} {w : V} :
    w ∈ nbhd G A ρ ↔ ∃ a ∈ A, G.dist a w ≤ ρ := by
  simp [nbhd]

theorem nbhd_empty (ρ : ℕ) : nbhd G ∅ ρ = ∅ := by
  ext w
  simp [mem_nbhd]

theorem nbhd_union (A X : Finset V) (ρ : ℕ) :
    nbhd G (A ∪ X) ρ = nbhd G A ρ ∪ nbhd G X ρ := by
  ext w
  simp only [mem_nbhd, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | ha, h⟩
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨a, ha, h⟩
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact ⟨a, Or.inl ha, h⟩
    · exact ⟨a, Or.inr ha, h⟩

theorem nbhd_step (hG : G.Connected) {A : Finset V} {s : ℕ} {r r' : V}
    (hr : r ∈ nbhd G A s) (h : Step G r r') : r' ∈ nbhd G A (s + 1) := by
  rw [mem_nbhd] at hr ⊢
  obtain ⟨a, ha, had⟩ := hr
  refine ⟨a, ha, ?_⟩
  have h1 := hG.dist_triangle (u := a) (v := r) (w := r')
  have h2 : G.dist r r' ≤ 1 := by
    rcases h with h | h
    · rw [h, dist_self]; omega
    · exact (dist_eq_one_iff_adj.mpr h).le
  omega

/-- `A` is admissible at radius `ρ`: it is empty, or its `ρ`-neighbourhood is small. -/
def Adm (G : SimpleGraph V) (K : ℕ) (A : Finset V) (ρ : ℕ) : Prop :=
  A = ∅ ∨ (nbhd G A ρ).card < K * A.card

/-- A largest admissible subset of `S`: every set in the rest of `S` expands. -/
theorem exists_maxAdm (G : SimpleGraph V) (K : ℕ) (S : Finset V) (ρ : ℕ) :
    ∃ A : Finset V, A ⊆ S ∧ Adm G K A ρ ∧
      ∀ X : Finset V, X ⊆ S \ A → K * X.card ≤ (nbhd G X ρ).card := by
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (S.powerset.filter fun A => Adm G K A ρ)
    Finset.card ⟨∅, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), Or.inl rfl⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  refine ⟨A, hA.1, hA.2, fun X hX => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hdisj : Disjoint A X := by
    rw [Finset.disjoint_left]
    intro a ha haX
    exact (Finset.mem_sdiff.mp (hX haX)).2 ha
  have hXpos : 0 < X.card := by
    rcases Nat.eq_zero_or_pos X.card with h0 | h0
    · rw [h0, Nat.mul_zero] at hlt
      omega
    · exact h0
  have hA' : (nbhd G A ρ).card ≤ K * A.card := by
    rcases hA.2 with h | h
    · rw [h, nbhd_empty]; simp
    · exact h.le
  have hadm : Adm G K (A ∪ X) ρ := by
    right
    rw [nbhd_union, Finset.card_union_of_disjoint hdisj, Nat.mul_add]
    have h1 := Finset.card_union_le (nbhd G A ρ) (nbhd G X ρ)
    omega
  have hsub : A ∪ X ⊆ S := Finset.union_subset hA.1 (hX.trans Finset.sdiff_subset)
  have h2 := hmax (A ∪ X) (by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, hadm⟩)
  rw [Finset.card_union_of_disjoint hdisj] at h2
  omega

/-- Hall's theorem: if every subset of `D` expands, `D` is matched into `C` within radius `ρ`. -/
theorem exists_matching (G : SimpleGraph V) (K : ℕ) (C D : Finset V) (ρ : ℕ)
    (hcover : ∀ A : Finset V, K * A.card ≤ (nbhd G A ρ).card →
      A.card ≤ (nbhd G A ρ ∩ C).card)
    (hD : ∀ X : Finset V, X ⊆ D → K * X.card ≤ (nbhd G X ρ).card) :
    ∃ g : V → V, (∀ x ∈ D, g x ∈ C ∧ G.dist x (g x) ≤ ρ) ∧ Set.InjOn g D := by
  have hall := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun x : D => C.filter fun w => G.dist (x : V) w ≤ ρ)).mp (by
      intro s
      have h1 := hD (s.map (Function.Embedding.subtype _)) (by
        intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.2)
      have h2 := hcover _ h1
      rw [Finset.card_map] at h2
      refine h2.trans (Finset.card_le_card ?_)
      intro w hw
      rw [Finset.mem_inter, mem_nbhd] at hw
      obtain ⟨⟨a, ha, had⟩, hwC⟩ := hw
      rw [Finset.mem_map] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      rw [Finset.mem_biUnion]
      exact ⟨y, hy, Finset.mem_filter.mpr ⟨hwC, had⟩⟩)
  obtain ⟨f, hinj, hf⟩ := hall
  refine ⟨fun x => if h : x ∈ D then f ⟨x, h⟩ else x, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · have h1 := hf ⟨x, hx⟩
    rw [Finset.mem_filter] at h1
    simp only [dif_pos hx]
    exact h1
  · have hx' : x ∈ D := hx
    have hy' : y ∈ D := hy
    simp only [dif_pos hx', dif_pos hy'] at hxy
    exact congrArg Subtype.val (hinj hxy)

/-- The deterministic half of the Scott–Sudakov lemma. If `C` meets the `2 ^ j`-neighbourhood
of every expanding set `A` in at least `|A|` vertices, for all `j ≤ T`, the diameter is at
most `2 ^ T`, and `K ^ (T + 1) ≤ n`, then `T + 1` teams of cops placed on `C` win. -/
theorem strategy (hG : G.Connected) (K T : ℕ) (C : Finset V)
    (hcover : ∀ j ≤ T, ∀ A : Finset V, K * A.card ≤ (nbhd G A (2 ^ j)).card →
      A.card ≤ (nbhd G A (2 ^ j) ∩ C).card)
    (hdiam : ∀ u v, G.dist u v ≤ 2 ^ T) (hterm : K ^ (T + 1) ≤ Fintype.card V) :
    CopsWin G ((T + 1) * C.card) := by
  have hcard : Fintype.card (Fin (T + 1) × C) = (T + 1) * C.card := by
    simp [Fintype.card_prod]
  let e : Fin ((T + 1) * C.card) ≃ Fin (T + 1) × C := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => ((e i).2 : V), fun v => ⟨2 ^ T - 1 + 1, ?_⟩⟩
  choose F hF1 hF2 hF3 using exists_maxAdm G K
  let A : ℕ → Finset V := fun j => Nat.rec (F {v} (2 ^ 0))
    (fun j Aj => F (nbhd G Aj (2 ^ j)) (2 ^ (j + 1))) j
  let S : ℕ → Finset V := fun j => Nat.rec {v} (fun j _ => nbhd G (A j) (2 ^ j)) j
  have hAS : ∀ j, A j ⊆ S j := by
    intro j
    cases j with
    | zero => exact hF1 _ _
    | succ j => exact hF1 _ _
  have hAadm : ∀ j, Adm G K (A j) (2 ^ j) := by
    intro j
    cases j with
    | zero => exact hF2 _ _
    | succ j => exact hF2 _ _
  have hAmax : ∀ j, ∀ X : Finset V, X ⊆ S j \ A j →
      K * X.card ≤ (nbhd G X (2 ^ j)).card := by
    intro j
    cases j with
    | zero => exact hF3 _ _
    | succ j => exact hF3 _ _
  have hAcard : ∀ j, (A j).card ≤ K ^ j := by
    intro j
    induction j with
    | zero =>
      have h1 : (A 0).card ≤ ({v} : Finset V).card := Finset.card_le_card (hAS 0)
      simpa using h1
    | succ j ih =>
      have h1 : (A (j + 1)).card ≤ (nbhd G (A j) (2 ^ j)).card :=
        Finset.card_le_card (hAS (j + 1))
      have h2 : (nbhd G (A j) (2 ^ j)).card ≤ K * (A j).card := by
        rcases hAadm j with h | h
        · rw [h, nbhd_empty]; simp
        · exact h.le
      calc (A (j + 1)).card ≤ K * (A j).card := h1.trans h2
        _ ≤ K * K ^ j := Nat.mul_le_mul_left K ih
        _ = K ^ (j + 1) := by ring
  have hAT : A T = ∅ := by
    by_contra hne
    rcases hAadm T with h | h
    · exact hne h
    · have huniv : nbhd G (A T) (2 ^ T) = Finset.univ := by
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        ext w
        simp only [mem_nbhd, Finset.mem_univ, iff_true]
        exact ⟨a, ha, hdiam a w⟩
      rw [huniv, Finset.card_univ] at h
      have h3 : K * (A T).card ≤ K * K ^ T := Nat.mul_le_mul_left K (hAcard T)
      have h4 : K * K ^ T = K ^ (T + 1) := by ring
      omega
  have hmatch : ∀ j, ∃ g : V → V, ¬ j ≤ T ∨
      ((∀ x ∈ S j \ A j, g x ∈ C ∧ G.dist x (g x) ≤ 2 ^ j) ∧
        Set.InjOn g (S j \ A j : Finset V)) := by
    intro j
    by_cases hj : j ≤ T
    · obtain ⟨g, hg⟩ := exists_matching G K C (S j \ A j) (2 ^ j) (hcover j hj) (hAmax j)
      exact ⟨g, Or.inr hg⟩
    · exact ⟨id, Or.inl hj⟩
  choose g hg0 using hmatch
  have hg : ∀ j, j ≤ T → (∀ x ∈ S j \ A j, g j x ∈ C ∧ G.dist x (g j x) ≤ 2 ^ j) ∧
      Set.InjOn (g j) (S j \ A j : Finset V) :=
    fun j hj => (hg0 j).resolve_left (not_not.mpr hj)
  let tgt : ℕ → V → V := fun j y =>
    if h : ∃ x, x ∈ S j \ A j ∧ g j x = y then h.choose else y
  have htd : ∀ j ≤ T, ∀ y, G.dist y (tgt j y) ≤ 2 ^ j := by
    intro j hj y
    by_cases h : ∃ x, x ∈ S j \ A j ∧ g j x = y
    · have hsp := h.choose_spec
      have h1 : tgt j y = h.choose := dif_pos h
      have h2 := ((hg j hj).1 _ hsp.1).2
      rw [hsp.2, dist_comm] at h2
      rw [h1]
      exact h2
    · have h1 : tgt j y = y := dif_neg h
      rw [h1, dist_self]
      exact Nat.zero_le _
  have htg : ∀ j ≤ T, ∀ x ∈ S j \ A j, tgt j (g j x) = x := by
    intro j hj x hx
    have h : ∃ x', x' ∈ S j \ A j ∧ g j x' = g j x := ⟨x, hx, rfl⟩
    have h1 : tgt j (g j x) = h.choose := dif_pos h
    rw [h1]
    exact (hg j hj).2 (Finset.mem_coe.mpr h.choose_spec.1) (Finset.mem_coe.mpr hx)
      h.choose_spec.2
  have hcatch : ∀ j ≤ T, ∀ x ∈ S j \ A j,
      ∃ i, tgt ((e i).1 : ℕ) ((e i).2 : V) = x ∧ 2 ^ ((e i).1 : ℕ) = 2 ^ j := by
    intro j hj x hx
    refine ⟨e.symm (⟨j, by omega⟩, ⟨g j x, ((hg j hj).1 x hx).1⟩), ?_⟩
    rw [Equiv.apply_symm_apply]
    exact ⟨htg j hj x hx, rfl⟩
  refine trap hG (fun i => tgt ((e i).1 : ℕ) ((e i).2 : V)) (fun i => 2 ^ ((e i).1 : ℕ))
    (fun m => {r | ∃ j s, j ≤ T ∧ m + 1 = 2 ^ j + s ∧ s < 2 ^ j ∧ r ∈ nbhd G (A j) s})
    (2 ^ T - 1) ?_ ?_ (2 ^ T - 1) 0 _ v (by omega) ?_ ?_
  · rintro m r ⟨j, s, hj, hm, hs, hr⟩ r' hr'
    have hr1 := nbhd_step hG hr hr'
    by_cases hs1 : s + 1 < 2 ^ j
    · exact Or.inl ⟨j, s + 1, hj, by omega, hs1, hr1⟩
    · have hs2 : s + 1 = 2 ^ j := by omega
      have hjT : j < T := by
        rcases Nat.lt_or_ge j T with h | h
        · exact h
        · have hjT' : j = T := by omega
          rw [hjT', hAT, nbhd_empty] at hr
          simp at hr
      rw [hs2] at hr1
      by_cases hA : r' ∈ A (j + 1)
      · left
        refine ⟨j + 1, 0, by omega, ?_, by positivity, ?_⟩
        · rw [pow_succ]; omega
        · rw [mem_nbhd]; exact ⟨r', hA, by simp⟩
      · right
        have hmem : r' ∈ S (j + 1) \ A (j + 1) := Finset.mem_sdiff.mpr ⟨hr1, hA⟩
        obtain ⟨i, hi, hρ⟩ := hcatch (j + 1) (by omega) r' hmem
        refine ⟨i, hi, ?_⟩
        show 2 ^ ((e i).1 : ℕ) ≤ m + 2
        rw [hρ, pow_succ]; omega
  · refine Set.eq_empty_iff_forall_notMem.mpr fun r => ?_
    rintro ⟨j, s, hj, hm, hs, hr⟩
    have h2T : 0 < 2 ^ T := by positivity
    have h2 : 2 ^ T < 2 ^ (j + 1) := by rw [pow_succ]; omega
    have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
    have hjT : j = T := by omega
    rw [hjT, hAT, nbhd_empty] at hr
    simp at hr
  · intro i
    rw [Nat.sub_zero]
    exact htd _ (Nat.lt_succ_iff.mp (e i).1.2) _
  · rcases Classical.em (v ∈ A 0) with hv | hv
    · left
      exact ⟨0, 0, Nat.zero_le _, by simp, by simp, mem_nbhd.mpr ⟨v, hv, by simp⟩⟩
    · right
      have hmem : v ∈ S 0 \ A 0 := Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self v, hv⟩
      obtain ⟨i, hi, hρ⟩ := hcatch 0 (Nat.zero_le _) v hmem
      refine ⟨i, hi, ?_⟩
      show 2 ^ ((e i).1 : ℕ) ≤ 0 + 1
      rw [hρ]; simp

end Strategy

/-
Part B (counting): a set `C` with the covering property exists. This is the probabilistic step
of the paper, done by hand: subsets `C` are weighted by `p ^ |C| * (1 - p) ^ (n - |C|)`, and the
total weight of the bad sets is bounded by exponential moments (a product formula).
-/

section Counting

variable {V : Type} [Fintype V]

/-- The weight of `C` when each vertex is included independently with probability `p`. -/
noncomputable def wt (p : ℝ) (C : Finset V) : ℝ := (∏ _a ∈ C, p) * ∏ _a ∈ Cᶜ, (1 - p)

theorem sum_wt_mul (p : ℝ) (x : V → ℝ) :
    ∑ C : Finset V, wt p C * ∏ a ∈ C, x a = ∏ a : V, (p * x a + (1 - p)) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [wt, Finset.prod_mul_distrib]
  ring

theorem sum_wt (p : ℝ) : ∑ C : Finset V, wt p C = 1 := by
  have h := sum_wt_mul (V := V) p (fun _ => 1)
  simpa using h

theorem sum_wt_two (p : ℝ) :
    ∑ C : Finset V, wt p C * 2 ^ C.card = (1 + p) ^ Fintype.card V := by
  have h := sum_wt_mul (V := V) p (fun _ => 2)
  simp only [Finset.prod_const, Finset.card_univ] at h
  rw [h]
  congr 1
  ring

theorem sum_wt_half (p : ℝ) (S : Finset V) :
    ∑ C : Finset V, wt p C * (1 / 2) ^ (S ∩ C).card = (1 - p / 2) ^ S.card := by
  have h := sum_wt_mul p (fun a => if a ∈ S then (1 / 2 : ℝ) else 1)
  have hL : ∀ C : Finset V,
      ∏ a ∈ C, (if a ∈ S then (1 / 2 : ℝ) else 1) = (1 / 2) ^ (S ∩ C).card := by
    intro C
    rw [Finset.prod_ite_mem, Finset.prod_const, Finset.inter_comm]
  have hR : ∀ a : V, p * (if a ∈ S then (1 / 2 : ℝ) else 1) + (1 - p) =
      if a ∈ S then 1 - p / 2 else 1 := by
    intro a
    split_ifs <;> ring
  simp only [hL, hR] at h
  rw [h, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem sum_pow_card (y : ℝ) :
    ∑ A : Finset V, y ^ A.card = (1 + y) ^ Fintype.card V := by
  have h := Fintype.prod_add (fun _ : V => y) (fun _ => (1 : ℝ))
  simp only [Finset.prod_const, Finset.card_univ, one_pow, mul_one] at h
  rw [← h]
  congr 1
  ring

theorem sum_pow_card_nonempty (y : ℝ) :
    ∑ A ∈ Finset.univ.filter (fun A : Finset V => A.Nonempty), y ^ A.card =
      (1 + y) ^ Fintype.card V - 1 := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset V))
    (fun A => A.Nonempty) (fun A => y ^ A.card)
  have he : Finset.univ.filter (fun A : Finset V => ¬ A.Nonempty) = {∅} := by
    ext A
    simp [Finset.not_nonempty_iff_eq_empty]
  rw [he, Finset.sum_singleton, Finset.card_empty, pow_zero, sum_pow_card] at h
  linarith

/-- If the bad weight is below one, a good set exists: at most `m` vertices, meeting the
neighbourhood of every expanding set often enough, at every scale `j ≤ T`. -/
theorem exists_good (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m T K : ℕ)
    (nb : ℕ → Finset V → Finset V)
    (hbad : ((T : ℝ) + 1) * ((1 + 2 * (1 - p / 2) ^ K) ^ Fintype.card V - 1) / 2 +
      (1 + p) ^ Fintype.card V / 2 ^ (m + 1) < 1) :
    ∃ C : Finset V, C.card ≤ m ∧ ∀ j ≤ T, ∀ A : Finset V,
      K * A.card ≤ (nb j A).card → A.card ≤ (nb j A ∩ C).card := by
  by_contra hno
  push Not at hno
  have hq0 : 0 ≤ 1 - p / 2 := by linarith
  have hq1 : 1 - p / 2 ≤ 1 := by linarith
  let I : Finset (Σ _ : ℕ, Finset V) := (Finset.range (T + 1)).sigma
    fun j => Finset.univ.filter fun A : Finset V => A.Nonempty ∧ K * A.card ≤ (nb j A).card
  let t : (Σ _ : ℕ, Finset V) → Finset V → ℝ :=
    fun i C => 2 ^ i.2.card / 2 * (1 / 2) ^ (nb i.1 i.2 ∩ C).card
  have ht0 : ∀ i C, 0 ≤ t i C := fun i C => by positivity
  have hφ : ∀ C : Finset V, 1 ≤ 2 ^ C.card / 2 ^ (m + 1) + ∑ i ∈ I, t i C := by
    intro C
    have hsum : 0 ≤ ∑ i ∈ I, t i C := Finset.sum_nonneg fun i _ => ht0 i C
    by_cases hC : C.card ≤ m
    · obtain ⟨j, hj, A, hA, hlt⟩ := hno C hC
      have hmem : (⟨j, A⟩ : Σ _ : ℕ, Finset V) ∈ I := by
        simp only [I, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_univ,
          true_and]
        refine ⟨by omega, ?_, hA⟩
        rw [← Finset.card_pos]
        omega
      have hterm : (1 : ℝ) ≤ t ⟨j, A⟩ C := by
        obtain ⟨d, hd⟩ : ∃ d, A.card = (nb j A ∩ C).card + 1 + d :=
          ⟨A.card - (nb j A ∩ C).card - 1, by omega⟩
        have h3 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
        have h4 : t ⟨j, A⟩ C = 2 ^ d := by
          show (2 : ℝ) ^ A.card / 2 * (1 / 2) ^ (nb j A ∩ C).card = 2 ^ d
          rw [hd, pow_add, pow_add, one_div, inv_pow]
          field_simp
        rw [h4]
        exact h3
      have h1 := Finset.single_le_sum (fun i _ => ht0 i C) hmem
      have h0 : (0 : ℝ) ≤ 2 ^ C.card / 2 ^ (m + 1) := by positivity
      linarith
    · have h1 : (1 : ℝ) ≤ 2 ^ C.card / 2 ^ (m + 1) := by
        rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  have hw : ∀ C : Finset V, 0 ≤ wt p C := fun C =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => hp0) (Finset.prod_nonneg fun _ _ => by linarith)
  have h1 : (1 : ℝ) ≤
      ∑ C : Finset V, wt p C * (2 ^ C.card / 2 ^ (m + 1) + ∑ i ∈ I, t i C) := by
    calc (1 : ℝ) = ∑ C : Finset V, wt p C := (sum_wt p).symm
      _ ≤ _ := Finset.sum_le_sum fun C _ => le_mul_of_one_le_right (hw C) (hφ C)
  have h2 : ∑ C : Finset V, wt p C * (2 ^ C.card / 2 ^ (m + 1) + ∑ i ∈ I, t i C) =
      (1 + p) ^ Fintype.card V / 2 ^ (m + 1) +
        ∑ i ∈ I, 2 ^ i.2.card / 2 * (1 - p / 2) ^ (nb i.1 i.2).card := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [← sum_wt_two p, Finset.sum_div]
      exact Finset.sum_congr rfl fun C _ => by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_wt_half p (nb i.1 i.2), Finset.mul_sum]
      exact Finset.sum_congr rfl fun C _ => by ring
  have h3 : ∑ i ∈ I, (2 : ℝ) ^ i.2.card / 2 * (1 - p / 2) ^ (nb i.1 i.2).card ≤
      ((T : ℝ) + 1) * ((1 + 2 * (1 - p / 2) ^ K) ^ Fintype.card V - 1) / 2 := by
    rw [Finset.sum_sigma]
    have hper : ∀ j ∈ Finset.range (T + 1),
        ∑ A ∈ Finset.univ.filter
            (fun A : Finset V => A.Nonempty ∧ K * A.card ≤ (nb j A).card),
          (2 : ℝ) ^ A.card / 2 * (1 - p / 2) ^ (nb j A).card ≤
        ((1 + 2 * (1 - p / 2) ^ K) ^ Fintype.card V - 1) / 2 := by
      intro j _
      have hstep1 : ∑ A ∈ Finset.univ.filter
            (fun A : Finset V => A.Nonempty ∧ K * A.card ≤ (nb j A).card),
          (2 : ℝ) ^ A.card / 2 * (1 - p / 2) ^ (nb j A).card ≤
          ∑ A ∈ Finset.univ.filter
            (fun A : Finset V => A.Nonempty ∧ K * A.card ≤ (nb j A).card),
          (2 * (1 - p / 2) ^ K) ^ A.card / 2 := by
        refine Finset.sum_le_sum fun A hA => ?_
        rw [Finset.mem_filter] at hA
        have h5 : (1 - p / 2) ^ (nb j A).card ≤ (1 - p / 2) ^ (K * A.card) :=
          pow_le_pow_of_le_one hq0 hq1 hA.2.2
        rw [mul_pow, ← pow_mul]
        have h6 : (0 : ℝ) ≤ 2 ^ A.card / 2 := by positivity
        calc (2 : ℝ) ^ A.card / 2 * (1 - p / 2) ^ (nb j A).card
            ≤ 2 ^ A.card / 2 * (1 - p / 2) ^ (K * A.card) := mul_le_mul_of_nonneg_left h5 h6
          _ = 2 ^ A.card * (1 - p / 2) ^ (K * A.card) / 2 := by ring
      have hstep2 : ∑ A ∈ Finset.univ.filter
            (fun A : Finset V => A.Nonempty ∧ K * A.card ≤ (nb j A).card),
          (2 * (1 - p / 2) ^ K) ^ A.card / 2 ≤
          ∑ A ∈ Finset.univ.filter (fun A : Finset V => A.Nonempty),
          (2 * (1 - p / 2) ^ K) ^ A.card / 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun A _ _ => by positivity
        intro A hA
        rw [Finset.mem_filter] at hA ⊢
        exact ⟨hA.1, hA.2.1⟩
      have h7 : ∑ A ∈ Finset.univ.filter (fun A : Finset V => A.Nonempty),
          (2 * (1 - p / 2) ^ K) ^ A.card / 2 =
          ((1 + 2 * (1 - p / 2) ^ K) ^ Fintype.card V - 1) / 2 := by
        rw [← Finset.sum_div, sum_pow_card_nonempty]
      rw [h7] at hstep2
      exact hstep1.trans hstep2
    calc _ ≤ ∑ _j ∈ Finset.range (T + 1),
          ((1 + 2 * (1 - p / 2) ^ K) ^ Fintype.card V - 1) / 2 := Finset.sum_le_sum hper
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  linarith

end Counting

open Filter

/-
Part C (parameters). With `L = log₂ N` and `s = √L`: `T = ⌊s⌋ - 1` scales, expansion factor
`K = 2 ^ T`, inclusion probability `p = 3 (L + 1) / 2 ^ T`, and
`E = 2 ^ T / (7 (T + 1) (L + 1))`. The cops number at most `N / E`, and `E = 2 ^ ((1 - f) s)`
with `f → 0`.
-/

section Arithmetic

/-- The number of scales, minus one. -/
noncomputable def TT (N : ℕ) : ℕ := ⌊Real.sqrt (Real.logb 2 N)⌋₊ - 1

/-- The saving factor: the cops number at most `N / EE N`. -/
noncomputable def EE (N : ℕ) : ℝ :=
  2 ^ TT N / (7 * ((TT N : ℝ) + 1) * (Real.logb 2 N + 1))

/-- The error term in the exponent. -/
noncomputable def ff (N : ℕ) : ℝ := 1 - Real.logb 2 (EE N) / Real.sqrt (Real.logb 2 N)

theorem logb_nat_nonneg (N : ℕ) : 0 ≤ Real.logb 2 (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h]; simp
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)

theorem QQ_ge (N : ℕ) : 1 ≤ 7 * ((TT N : ℝ) + 1) * (Real.logb 2 N + 1) := by
  have h1 := logb_nat_nonneg N
  have h2 : (0 : ℝ) ≤ TT N := Nat.cast_nonneg _
  nlinarith [mul_nonneg h2 h1]

theorem EE_pos (N : ℕ) : 0 < EE N := by
  have h := QQ_ge N
  exact div_pos (by positivity) (by linarith)

theorem EE_le (N : ℕ) : EE N ≤ 2 ^ TT N :=
  div_le_self (by positivity) (QQ_ge N)

theorem rpow_ff (N : ℕ) (hs : 0 < Real.sqrt (Real.logb 2 N)) :
    (2 : ℝ) ^ ((1 - ff N) * Real.sqrt (Real.logb 2 N)) = EE N := by
  have h : (1 - ff N) * Real.sqrt (Real.logb 2 N) = Real.logb 2 (EE N) := by
    rw [ff, sub_sub_cancel, div_mul_cancel₀ _ hs.ne']
  rw [h, Real.rpow_logb two_pos (by norm_num) (EE_pos N)]

theorem rpow_ff_le (N : ℕ) :
    (2 : ℝ) ^ ((1 - ff N) * Real.sqrt (Real.logb 2 N)) ≤ ((2 ^ TT N : ℕ) : ℝ) + 1 := by
  have h0 : (0 : ℝ) < 2 ^ TT N := by positivity
  rcases (Real.sqrt_nonneg (Real.logb 2 N)).eq_or_lt with h | h
  · rw [← h, mul_zero, Real.rpow_zero]
    push_cast
    linarith
  · rw [rpow_ff N h]
    have := EE_le N
    push_cast
    linarith

theorem TT_cases (N : ℕ) :
    (TT N : ℝ) = 0 ∨ (TT N : ℝ) + 1 ≤ Real.sqrt (Real.logb 2 N) := by
  unfold TT
  rcases Nat.eq_zero_or_pos ⌊Real.sqrt (Real.logb 2 N)⌋₊ with h | h
  · left
    simp [h]
  · right
    have h1 : ((⌊Real.sqrt (Real.logb 2 N)⌋₊ - 1 : ℕ) : ℝ) + 1 =
        (⌊Real.sqrt (Real.logb 2 N)⌋₊ : ℝ) := by
      have h2 : ⌊Real.sqrt (Real.logb 2 N)⌋₊ - 1 + 1 = ⌊Real.sqrt (Real.logb 2 N)⌋₊ := by omega
      exact_mod_cast h2
    rw [h1]
    exact Nat.floor_le (Real.sqrt_nonneg _)

theorem one_add_pow_le (y : ℝ) (hy : 0 ≤ y) :
    ∀ n : ℕ, (n : ℝ) * y ≤ 1 / 2 → (1 + y) ^ n ≤ 1 + 2 * n * y := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    push_cast at h ⊢
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (n : ℝ) * y ≤ 1 / 2 := by nlinarith
    have h2 := ih h1
    rw [pow_succ]
    have h4 : (1 + y) ^ n * (1 + y) ≤ (1 + 2 * n * y) * (1 + y) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    nlinarith [mul_nonneg hy (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * y))]

set_option maxHeartbeats 1000000 in
/-- The bounded-diameter lemma with explicit parameters. -/
theorem bounded_diam (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ) (hG : G.Connected)
    (hN : Fintype.card V ≤ N) (hd : ∀ u v, G.dist u v ≤ 2 ^ TT N) :
    (copNumber G : ℝ) ≤ (N : ℝ) / 2 ^ ((1 - ff N) * Real.sqrt (Real.logb 2 N)) := by
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hG.nonempty
  have hcn : copNumber G ≤ Fintype.card V := Nat.sInf_le (copsWin_card G)
  have hcnR : (copNumber G : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcn
  have hnN : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast hN
  have hn1R : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn1
  have hL0 : 0 ≤ Real.logb 2 (N : ℝ) := logb_nat_nonneg N
  rcases (Real.sqrt_nonneg (Real.logb 2 N)).eq_or_lt with hs | hs
  · rw [← hs, mul_zero, Real.rpow_zero, div_one]
    linarith
  rw [rpow_ff N hs]
  have hE := EE_pos N
  by_cases htriv : (Fintype.card V : ℝ) ≤ N / EE N
  · linarith
  rw [not_le, div_lt_iff₀ hE] at htriv
  have hTs := TT_cases N
  have hQ1 := QQ_ge N
  have hEQ : EE N = 2 ^ TT N / (7 * ((TT N : ℝ) + 1) * (Real.logb 2 N + 1)) := rfl
  generalize hTdef : TT N = T at *
  generalize hLdef : Real.logb 2 (N : ℝ) = L at *
  generalize hndef : (Fintype.card V : ℝ) = n at *
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have h2L : (2 : ℝ) ^ L = N := by
    rw [← hLdef]
    exact Real.rpow_logb two_pos (by norm_num) (by linarith)
  have hTL : (T : ℝ) * (T + 2) ≤ L := by
    rcases hTs with h | h
    · rw [h]; simpa using hL0
    · have h1 := Real.mul_self_sqrt hL0
      have h2 := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ (T : ℝ) + 1) h
      linarith
  have hTleL : (T : ℝ) ≤ L := by linarith [mul_nonneg hT0 hT0]
  have h2Tpos : (0 : ℝ) < 2 ^ T := by positivity
  have h2T : (2 : ℝ) ^ T ≤ N := by
    rw [← h2L, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hTleL
  have hQ0 : (0 : ℝ) < 7 * ((T : ℝ) + 1) * (L + 1) := by linarith
  have hNQ : (N : ℝ) * (7 * ((T : ℝ) + 1) * (L + 1)) < n * 2 ^ T := by
    rw [hEQ, ← mul_div_assoc, lt_div_iff₀ hQ0] at htriv
    exact htriv
  have hQlt : 7 * ((T : ℝ) + 1) * (L + 1) < 2 ^ T := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : n * 2 ^ T ≤ (N : ℝ) * (7 * ((T : ℝ) + 1) * (L + 1)) :=
      mul_le_mul hnN hcon h2Tpos.le (by linarith)
    linarith
  have hL1 : 7 * (L + 1) ≤ 7 * ((T : ℝ) + 1) * (L + 1) := by linarith [mul_nonneg hT0 hL0]
  have hT1 : (T : ℝ) + 1 ≤ 7 * ((T : ℝ) + 1) * (L + 1) := by linarith [mul_nonneg hT0 hL0]
  have hp0 : 0 ≤ 3 * (L + 1) / 2 ^ T := div_nonneg (by linarith) h2Tpos.le
  have hp1 : 3 * (L + 1) / 2 ^ T ≤ 1 := by
    rw [div_le_one h2Tpos]
    linarith
  have hpK : 3 * (L + 1) / 2 ^ T * 2 ^ T = 3 * (L + 1) := div_mul_cancel₀ _ h2Tpos.ne'
  generalize hpdef : 3 * (L + 1) / (2 : ℝ) ^ T = p at *
  have hn0 : (0 : ℝ) ≤ n := by linarith
  -- (a) the size bound
  have ha : (1 + p) ^ Fintype.card V ≤ 2 ^ ⌈2 * p * n⌉₊ := by
    have h1 : 1 + p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
    have h4 : Real.exp (n * p) ≤ (2 : ℝ) ^ (2 * p * n) := by
      rw [Real.rpow_def_of_pos two_pos]
      apply Real.exp_le_exp.mpr
      have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2) (mul_nonneg hp0 hn0)]
    have h5 : (2 : ℝ) ^ (2 * p * n) ≤ (2 : ℝ) ^ ((⌈2 * p * n⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    rw [Real.rpow_natCast] at h5
    calc (1 + p) ^ Fintype.card V ≤ Real.exp p ^ Fintype.card V :=
          pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp (n * p) := by rw [← hndef, Real.exp_nat_mul]
      _ ≤ _ := h4.trans h5
  -- (b) the hitting bound
  have hb : (1 - p / 2) ^ (2 ^ T) ≤ 1 / (4 * (N : ℝ) ^ 2) := by
    have h1 : 1 - p / 2 ≤ Real.exp (-(p / 2)) := by linarith [Real.add_one_le_exp (-(p / 2))]
    have h2 : (1 - p / 2) ^ (2 ^ T) ≤ Real.exp (-(p / 2)) ^ (2 ^ T) :=
      pow_le_pow_left₀ (by linarith) h1 _
    have h3 : Real.exp (-(p / 2)) ^ (2 ^ T) = Real.exp (-(3 * (L + 1) / 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [← hpK]
      ring
    have hNe : (N : ℝ) = Real.exp (L * Real.log 2) := by
      rw [← h2L, Real.rpow_def_of_pos two_pos, mul_comm]
    have h4e : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
      rw [two_mul, Real.exp_add, Real.exp_log two_pos]
      norm_num
    have h6 : 1 / (4 * (N : ℝ) ^ 2) = Real.exp (-(2 * (L + 1) * Real.log 2)) := by
      rw [hNe, h4e, pow_two, ← Real.exp_add, ← Real.exp_add, one_div, ← Real.exp_neg]
      congr 1
      ring
    have h5 : Real.exp (-(3 * (L + 1) / 2)) ≤ 1 / (4 * (N : ℝ) ^ 2) := by
      rw [h6]
      apply Real.exp_le_exp.mpr
      have hl : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ L + 1)
        (by linarith : (0 : ℝ) ≤ 3 / 4 - Real.log 2)]
    calc (1 - p / 2) ^ (2 ^ T) ≤ Real.exp (-(p / 2)) ^ (2 ^ T) := h2
      _ = Real.exp (-(3 * (L + 1) / 2)) := h3
      _ ≤ _ := h5
  -- (c) the bad weight is below one
  have hNpos : (0 : ℝ) < N := by linarith
  have hy0 : 0 ≤ 2 * (1 - p / 2) ^ (2 ^ T) := by
    have : (0 : ℝ) ≤ (1 - p / 2) ^ (2 ^ T) := pow_nonneg (by linarith) _
    linarith
  have hyle : 2 * (1 - p / 2) ^ (2 ^ T) ≤ 1 / (2 * (N : ℝ) ^ 2) := by
    have h1 : 1 / (2 * (N : ℝ) ^ 2) = 2 * (1 / (4 * (N : ℝ) ^ 2)) := by
      field_simp
      ring
    rw [h1]
    linarith
  have hny : n * (2 * (1 - p / 2) ^ (2 ^ T)) ≤ 1 / (2 * (N : ℝ)) := by
    have h1 : n * (2 * (1 - p / 2) ^ (2 ^ T)) ≤ (N : ℝ) * (1 / (2 * (N : ℝ) ^ 2)) :=
      mul_le_mul hnN hyle hy0 hNpos.le
    have h2 : (N : ℝ) * (1 / (2 * (N : ℝ) ^ 2)) = 1 / (2 * (N : ℝ)) := by
      field_simp
    rw [h2] at h1
    exact h1
  have hNhalf : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hpow : (1 + 2 * (1 - p / 2) ^ (2 ^ T)) ^ Fintype.card V ≤
      1 + 2 * n * (2 * (1 - p / 2) ^ (2 ^ T)) := by
    have h1 := one_add_pow_le _ hy0 (Fintype.card V) (by rw [hndef]; linarith)
    rw [hndef] at h1
    exact h1
  have hTN : (T : ℝ) + 1 < N := by linarith
  have hfirst : ((T : ℝ) + 1) *
      ((1 + 2 * (1 - p / 2) ^ (2 ^ T)) ^ Fintype.card V - 1) / 2 < 1 / 2 := by
    have h1 : (1 + 2 * (1 - p / 2) ^ (2 ^ T)) ^ Fintype.card V - 1 ≤ 1 / (N : ℝ) := by
      have h2 : 2 * (1 / (2 * (N : ℝ))) = 1 / (N : ℝ) := by
        field_simp
      have h5 : 2 * n * (2 * (1 - p / 2) ^ (2 ^ T)) =
          2 * (n * (2 * (1 - p / 2) ^ (2 ^ T))) := by ring
      linarith
    have hT1' : (0 : ℝ) ≤ (T : ℝ) + 1 := by linarith
    have h3 : ((T : ℝ) + 1) * ((1 + 2 * (1 - p / 2) ^ (2 ^ T)) ^ Fintype.card V - 1) ≤
        ((T : ℝ) + 1) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left h1 hT1'
    have h4 : ((T : ℝ) + 1) * (1 / (N : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hNpos]
      exact hTN
    linarith
  have hsecond : (1 + p) ^ Fintype.card V / 2 ^ (⌈2 * p * n⌉₊ + 1) ≤ 1 / 2 := by
    rw [pow_succ, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨C, hCm, hcov⟩ := exists_good p hp0 hp1 ⌈2 * p * n⌉₊ T (2 ^ T)
    (fun j A => nbhd G A (2 ^ j)) (by linarith)
  -- the cops win
  have hterm : (2 ^ T) ^ (T + 1) ≤ Fintype.card V := by
    have h1 : (2 : ℝ) ^ (T * (T + 2)) ≤ N := by
      rw [← h2L, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      exact hTL
    have h2 : ((2 : ℝ) ^ T) ^ (T + 1) * 2 ^ T = 2 ^ (T * (T + 2)) := by
      rw [← pow_mul, ← pow_add]
      congr 1
    have h3 : (N : ℝ) ≤ (N : ℝ) * (7 * ((T : ℝ) + 1) * (L + 1)) :=
      le_mul_of_one_le_right hNpos.le hQ1
    have h4 : ((2 : ℝ) ^ T) ^ (T + 1) * 2 ^ T < n * 2 ^ T := by linarith
    have h5 : ((2 : ℝ) ^ T) ^ (T + 1) < n := lt_of_mul_lt_mul_right h4 h2Tpos.le
    rw [← hndef] at h5
    exact_mod_cast h5.le
  have hwin := strategy hG (2 ^ T) T C hcov hd hterm
  have hcop : copNumber G ≤ (T + 1) * C.card := Nat.sInf_le hwin
  have hcop2 : copNumber G ≤ (T + 1) * ⌈2 * p * n⌉₊ :=
    hcop.trans (Nat.mul_le_mul_left _ hCm)
  have hceil : (⌈2 * p * n⌉₊ : ℝ) < 2 * p * n + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by norm_num) hp0) hn0)
  have hc1 : (copNumber G : ℝ) ≤ ((T : ℝ) + 1) * (2 * p * n + 1) := by
    have h1 : (copNumber G : ℝ) ≤ ((T : ℝ) + 1) * (⌈2 * p * n⌉₊ : ℝ) := by
      exact_mod_cast hcop2
    have h2 : ((T : ℝ) + 1) * (⌈2 * p * n⌉₊ : ℝ) ≤ ((T : ℝ) + 1) * (2 * p * n + 1) :=
      mul_le_mul_of_nonneg_left hceil.le (by linarith)
    linarith
  rw [hEQ, div_div_eq_mul_div, le_div_iff₀ h2Tpos]
  have hc2 : (copNumber G : ℝ) * 2 ^ T ≤ ((T : ℝ) + 1) * (2 * p * n + 1) * 2 ^ T :=
    mul_le_mul_of_nonneg_right hc1 h2Tpos.le
  have hc3 : ((T : ℝ) + 1) * (2 * p * n + 1) * 2 ^ T =
      ((T : ℝ) + 1) * (2 * (p * 2 ^ T) * n + 2 ^ T) := by ring
  rw [hc3, hpK] at hc2
  have hc4 : 2 * (3 * (L + 1)) * n + 2 ^ T ≤ 7 * (L + 1) * (N : ℝ) := by
    have h1 : (L + 1) * n ≤ (L + 1) * (N : ℝ) := mul_le_mul_of_nonneg_left hnN (by linarith)
    have h2 : (N : ℝ) ≤ (L + 1) * (N : ℝ) := by linarith [mul_nonneg hL0 hNpos.le]
    linarith
  have hc5 : ((T : ℝ) + 1) * (2 * (3 * (L + 1)) * n + 2 ^ T) ≤
      ((T : ℝ) + 1) * (7 * (L + 1) * (N : ℝ)) := mul_le_mul_of_nonneg_left hc4 (by linarith)
  have hc6 : ((T : ℝ) + 1) * (7 * (L + 1) * (N : ℝ)) =
      (N : ℝ) * (7 * ((T : ℝ) + 1) * (L + 1)) := by ring
  linarith

theorem ff_bounds (N : ℕ) (hs : 1 ≤ Real.sqrt (Real.logb 2 N)) :
    0 ≤ ff N ∧ ff N ≤ (2 + Real.logb 2 7) * (Real.sqrt (Real.logb 2 N))⁻¹ +
      3 / Real.log 2 *
        (Real.log (Real.sqrt (Real.logb 2 N) + 1) / Real.sqrt (Real.logb 2 N)) := by
  have hL0 := logb_nat_nonneg N
  have hsL : Real.logb 2 (N : ℝ) = Real.sqrt (Real.logb 2 N) * Real.sqrt (Real.logb 2 N) :=
    (Real.mul_self_sqrt hL0).symm
  have hfl : 0 < ⌊Real.sqrt (Real.logb 2 N)⌋₊ := Nat.floor_pos.mpr hs
  have hT1 : ((TT N : ℕ) : ℝ) + 1 = (⌊Real.sqrt (Real.logb 2 N)⌋₊ : ℝ) := by
    have h2 : TT N + 1 = ⌊Real.sqrt (Real.logb 2 N)⌋₊ := by unfold TT; omega
    exact_mod_cast h2
  have h1 : (⌊Real.sqrt (Real.logb 2 N)⌋₊ : ℝ) ≤ Real.sqrt (Real.logb 2 N) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.logb 2 N) < (⌊Real.sqrt (Real.logb 2 N)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hQ1 := QQ_ge N
  have hEQ : EE N = 2 ^ TT N / (7 * ((TT N : ℝ) + 1) * (Real.logb 2 N + 1)) := rfl
  have hff : ff N = 1 - Real.logb 2 (EE N) / Real.sqrt (Real.logb 2 N) := rfl
  generalize hTdef : TT N = T at *
  generalize hsdef : Real.sqrt (Real.logb 2 (N : ℝ)) = s at *
  generalize hLdef : Real.logb 2 (N : ℝ) = L at *
  generalize hfdef : (⌊s⌋₊ : ℝ) = fl at *
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hs0 : 0 < s := by linarith
  have hQle : 7 * ((T : ℝ) + 1) * (L + 1) ≤ 7 * (s + 1) ^ 3 := by
    have h3 : (T : ℝ) + 1 ≤ s := by linarith
    have h4 : 7 * ((T : ℝ) + 1) * (L + 1) ≤ 7 * s * (L + 1) := by nlinarith
    rw [hsL] at h4 ⊢
    nlinarith [mul_pos hs0 hs0]
  have hlogE : Real.logb 2 (EE N) = T - Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1)) := by
    rw [hEQ, Real.logb_div (by positivity) (by linarith), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]
  have hlogQ0 : 0 ≤ Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1)) :=
    Real.logb_nonneg one_lt_two hQ1
  have hlogQ : Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1)) ≤
      Real.logb 2 7 + 3 * Real.logb 2 (s + 1) := by
    calc Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1)) ≤ Real.logb 2 (7 * (s + 1) ^ 3) :=
          Real.logb_le_logb_of_le one_lt_two (by linarith) hQle
      _ = Real.logb 2 7 + 3 * Real.logb 2 (s + 1) := by
          rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
          norm_num
  rw [hff, hlogE]
  constructor
  · have h3 : ((T : ℝ) - Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1))) / s ≤ 1 := by
      rw [div_le_one hs0]
      linarith
    linarith
  · have h3 : (2 + Real.logb 2 7) * s⁻¹ + 3 / Real.log 2 * (Real.log (s + 1) / s) =
        (2 + Real.logb 2 7 + 3 * Real.logb 2 (s + 1)) / s := by
      rw [show Real.logb 2 (s + 1) = Real.log (s + 1) / Real.log 2 from rfl]
      ring
    rw [h3]
    have h4 : (1 : ℝ) - ((T : ℝ) - Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1))) / s =
        (s - T + Real.logb 2 (7 * ((T : ℝ) + 1) * (L + 1))) / s := by
      field_simp
      ring
    rw [h4]
    apply div_le_div_of_nonneg_right _ hs0.le
    linarith

theorem tendsto_ff : Tendsto ff atTop (nhds 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (Real.logb 2 N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop)
  have hg : Tendsto (fun s : ℝ => (2 + Real.logb 2 7) * s⁻¹ +
      3 / Real.log 2 * (Real.log (s + 1) / s)) atTop (nhds 0) := by
    have h1 : Tendsto (fun s : ℝ => (2 + Real.logb 2 7) * s⁻¹) atTop
        (nhds ((2 + Real.logb 2 7) * 0)) := tendsto_inv_atTop_zero.const_mul _
    have h2 : Tendsto (fun s : ℝ => Real.log (s + 1) / s) atTop (nhds 0) := by
      have h3 := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
      refine h3.congr fun s => ?_
      simp
    have h4 := h1.add (h2.const_mul (3 / Real.log 2))
    simpa using h4
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.sqrt (Real.logb 2 N) := hs.eventually_ge_atTop 1
  exact squeeze_zero' (hev.mono fun N h => (ff_bounds N h).1)
    (hev.mono fun N h => (ff_bounds N h).2) (hg.comp hs)

end Arithmetic

/-- The statement of step `H2`. -/
theorem H2_proof : ∃ (f : ℕ → ℝ) (D : ℕ → ℕ), Tendsto f atTop (nhds 0) ∧
    (∀ N : ℕ, (2 : ℝ) ^ ((1 - f N) * Real.sqrt (Real.logb 2 N)) ≤ (D N : ℝ) + 1) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (N : ℕ), G.Connected →
      Fintype.card V ≤ N → (∀ u v, G.dist u v ≤ D N) →
        (copNumber G : ℝ) ≤ (N : ℝ) / 2 ^ ((1 - f N) * Real.sqrt (Real.logb 2 N)) :=
  ⟨ff, fun N => 2 ^ TT N, tendsto_ff, rpow_ff_le,
    fun V _ G N hG hN hd => bounded_diam V G N hG hN hd⟩

end BoundedDiameter

end OMA

theorem OMA.solution :
    type_of% @MeynielConjecture.meyniel_conjecture.variants.scott_sudakov :=
  OMA.SS.main (fun V _ G u v p k hG hlen hyp => OMA.path_guard V G u v p k hG hlen hyp)
    OMA.H2_proof
