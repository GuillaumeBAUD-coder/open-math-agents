import FormalConjectures.ErdosProblems.«868»

-- Problem: Erdős Problem 868 — fixed ε
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/868.lean:73 (declaration Erdos868.erdos_868.variants.fixed_ε)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Formalization of the theorem of Erdős and Nathanson (Systems of distinct representatives and
minimal bases in additive number theory, LNM 751, 1979, Theorems 1 and 2): if r(n) > c log n
for all large n, with c > 1 / log (4/3), then A contains a minimal asymptotic basis of order 2.

Plan (following the paper):
* `clause_bound`: a counting estimate in the spirit of their Lemma 1, proved here by induction
  on the variables for literal-disjoint clauses; it gives at most 2^s (3/4)^t bad transversals.
* `exists_X` (their Lemma 2): a transversal of the representations of n that destroys no other
  representation count, found by a union bound against the summable series m^(-p), p > 1.
* `stage` and `main` (their Theorem 1): the decreasing sequence of sets, each element of the
  limit made essential infinitely often (scheduled with Nat.unpair).
-/

open Filter Finset

namespace OMA868

/-- weight inequality for at most one-element sets -/
lemma prod_le_one_card {κ : Type*} (K1 : Finset κ) (h1 : K1.card ≤ 1) (x : κ → ℝ) :
    (∏ k ∈ K1, (1 - 2 * x k)) = 1 - 2 * ∑ k ∈ K1, x k ∧
    (∏ k ∈ K1, (1 - x k)) = 1 - ∑ k ∈ K1, x k := by
  rcases K1.eq_empty_or_nonempty with h | ⟨k, hk⟩
  · subst h; simp
  · have : K1 = {k} := by
      ext k'
      simp only [mem_singleton]
      exact ⟨fun hk' => Finset.card_le_one.mp h1 _ hk' _ hk, fun h => h ▸ hk⟩
    subst this; simp

theorem clause_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (cl : κ → Finset (ι × Bool))
    (V : Finset ι) : ∀ (K : Finset κ),
    (∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → Disjoint (cl k) (cl k')) →
    (∀ k ∈ K, ∀ j, ¬ ((j, true) ∈ cl k ∧ (j, false) ∈ cl k)) →
    (∑ Y ∈ V.powerset,
      (if ∀ k ∈ K, ∃ l ∈ cl k, l.1 ∈ V ∧ (l.1 ∈ Y ↔ l.2 = true) then (1:ℝ) else 0))
      ≤ 2 ^ V.card * ∏ k ∈ K, (1 - (1/2 : ℝ) ^ ((cl k).filter (fun l => l.1 ∈ V)).card) := by
  induction V using Finset.induction_on with
  | empty =>
    intro K _ _
    rcases K.eq_empty_or_nonempty with h | ⟨k, hk⟩
    · subst h; simp
    · have : ¬ ∀ k ∈ K, ∃ l ∈ cl k, l.1 ∈ (∅ : Finset ι) ∧ (l.1 ∈ (∅ : Finset ι) ↔ l.2 = true) := by
        intro h; obtain ⟨l, -, hl, -⟩ := h k hk; simp at hl
      simp only [powerset_empty, sum_singleton, this, if_false]
      apply mul_nonneg (by positivity)
      apply prod_nonneg
      intro k _
      have : (1/2 : ℝ) ^ ((cl k).filter (fun l => l.1 ∈ (∅ : Finset ι))).card ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      linarith
  | @insert i V0 hi IH =>
    intro K hdisj hpol
    rw [Finset.sum_powerset_insert hi]
    set Kf := K.filter (fun k => (i, false) ∉ cl k) with hKf
    set Kt := K.filter (fun k => (i, true) ∉ cl k) with hKt
    have e1 : ∀ Y ∈ V0.powerset,
        ((∀ k ∈ K, ∃ l ∈ cl k, l.1 ∈ insert i V0 ∧ (l.1 ∈ Y ↔ l.2 = true)) ↔
        (∀ k ∈ Kf, ∃ l ∈ cl k, l.1 ∈ V0 ∧ (l.1 ∈ Y ↔ l.2 = true))) := by
      intro Y hY
      have hiY : i ∉ Y := fun h => hi (mem_powerset.mp hY h)
      constructor
      · intro h k hk
        rw [hKf, mem_filter] at hk
        obtain ⟨l, hl, hlV, hlY⟩ := h k hk.1
        rcases mem_insert.mp hlV with hli | hli
        · exfalso
          have : l.2 = false := by
            cases h2 : l.2
            · rfl
            · rw [h2] at hlY; exact absurd (hlY.mpr rfl) (hli ▸ hiY)
          exact hk.2 (by rw [← hli, ← this]; exact hl)
        · exact ⟨l, hl, hli, hlY⟩
      · intro h k hk
        by_cases hik : (i, false) ∈ cl k
        · exact ⟨(i, false), hik, mem_insert_self _ _, by simp [hiY]⟩
        · obtain ⟨l, hl, hlV, hlY⟩ := h k (by rw [hKf, mem_filter]; exact ⟨hk, hik⟩)
          exact ⟨l, hl, mem_insert_of_mem hlV, hlY⟩
    have e2 : ∀ Y ∈ V0.powerset,
        ((∀ k ∈ K, ∃ l ∈ cl k, l.1 ∈ insert i V0 ∧ (l.1 ∈ insert i Y ↔ l.2 = true)) ↔
        (∀ k ∈ Kt, ∃ l ∈ cl k, l.1 ∈ V0 ∧ (l.1 ∈ Y ↔ l.2 = true))) := by
      intro Y hY
      have hiY : i ∉ Y := fun h => hi (mem_powerset.mp hY h)
      constructor
      · intro h k hk
        rw [hKt, mem_filter] at hk
        obtain ⟨l, hl, hlV, hlY⟩ := h k hk.1
        rcases mem_insert.mp hlV with hli | hli
        · exfalso
          have : l.2 = true := hlY.mp (by rw [hli]; exact mem_insert_self _ _)
          exact hk.2 (by rw [← hli, ← this]; exact hl)
        · have hne : l.1 ≠ i := fun h => hi (h ▸ hli)
          refine ⟨l, hl, hli, ?_⟩
          rw [← hlY, mem_insert]
          simp [hne]
      · intro h k hk
        by_cases hik : (i, true) ∈ cl k
        · exact ⟨(i, true), hik, mem_insert_self _ _, by simp⟩
        · obtain ⟨l, hl, hlV, hlY⟩ := h k (by rw [hKt, mem_filter]; exact ⟨hk, hik⟩)
          have hne : l.1 ≠ i := fun h => hi (h ▸ hlV)
          refine ⟨l, hl, mem_insert_of_mem hlV, ?_⟩
          rw [← hlY, mem_insert]
          simp [hne]
    have s1 : (∑ Y ∈ V0.powerset,
        (if ∀ k ∈ K, ∃ l ∈ cl k, l.1 ∈ insert i V0 ∧ (l.1 ∈ Y ↔ l.2 = true) then (1:ℝ) else 0)) =
        ∑ Y ∈ V0.powerset,
        (if ∀ k ∈ Kf, ∃ l ∈ cl k, l.1 ∈ V0 ∧ (l.1 ∈ Y ↔ l.2 = true) then (1:ℝ) else 0) :=
      Finset.sum_congr rfl (fun Y hY => if_congr (e1 Y hY) rfl rfl)
    have s2 : (∑ Y ∈ V0.powerset,
        (if ∀ k ∈ K, ∃ l ∈ cl k, l.1 ∈ insert i V0 ∧ (l.1 ∈ insert i Y ↔ l.2 = true)
          then (1:ℝ) else 0)) =
        ∑ Y ∈ V0.powerset,
        (if ∀ k ∈ Kt, ∃ l ∈ cl k, l.1 ∈ V0 ∧ (l.1 ∈ Y ↔ l.2 = true) then (1:ℝ) else 0) :=
      Finset.sum_congr rfl (fun Y hY => if_congr (e2 Y hY) rfl rfl)
    rw [s1, s2]
    have IHf := IH Kf (fun k hk k' hk' => hdisj k (mem_filter.mp hk).1 k' (mem_filter.mp hk').1)
      (fun k hk => hpol k (mem_filter.mp hk).1)
    have IHt := IH Kt (fun k hk k' hk' => hdisj k (mem_filter.mp hk).1 k' (mem_filter.mp hk').1)
      (fun k hk => hpol k (mem_filter.mp hk).1)
    refine (add_le_add IHf IHt).trans ?_
    set w0 : κ → ℝ := fun k => 1 - (1/2 : ℝ) ^ ((cl k).filter (fun l => l.1 ∈ V0)).card with hw0
    set wV : κ → ℝ := fun k => 1 - (1/2 : ℝ) ^ ((cl k).filter (fun l => l.1 ∈ insert i V0)).card
      with hwV
    set x : κ → ℝ := fun k => (1/2 : ℝ) ^ ((cl k).filter (fun l => l.1 ∈ insert i V0)).card
      with hx
    set K1 := K.filter (fun k => (i, true) ∈ cl k) with hK1
    set K2 := K.filter (fun k => (i, false) ∈ cl k) with hK2
    set K0 := K.filter (fun k => (i, true) ∉ cl k ∧ (i, false) ∉ cl k) with hK0
    have hcard_ins : ∀ k, ((cl k).filter (fun l => l.1 ∈ insert i V0)).card =
        ((cl k).filter (fun l => l.1 ∈ V0)).card +
        ((cl k).filter (fun l => l.1 = i)).card := by
      intro k
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext l; simp only [mem_filter, mem_union, mem_insert]; tauto
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2; exact hi (h2 ▸ h1)
    have hfilt_i : ∀ k, (cl k).filter (fun l => l.1 = i) =
        (if (i, true) ∈ cl k then {(i, true)} else ∅) ∪
        (if (i, false) ∈ cl k then {(i, false)} else ∅) := by
      intro k; ext ⟨j, b⟩
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hl, rfl⟩
        cases b
        · right; simp [hl]
        · left; simp [hl]
      · intro h
        rcases h with h | h
        · split_ifs at h with hh
          · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hh, rfl⟩
          · simp at h
        · split_ifs at h with hh
          · simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hh, rfl⟩
          · simp at h
    have hK0eq : ∀ k ∈ K0, wV k = w0 k := by
      intro k hk
      rw [hK0, mem_filter] at hk
      simp only [hwV, hw0, hcard_ins k, hfilt_i k, hk.2.1, hk.2.2, if_false, union_empty,
        card_empty, add_zero]
    have hK1eq : ∀ k ∈ K1, w0 k = 1 - 2 * x k ∧ wV k = 1 - x k := by
      intro k hk
      rw [hK1, mem_filter] at hk
      have hnf : (i, false) ∉ cl k := fun h => hpol k hk.1 i ⟨hk.2, h⟩
      refine ⟨?_, rfl⟩
      simp only [hw0, hx, hcard_ins k, hfilt_i k, hk.2, hnf, if_true, if_false, union_empty,
        card_singleton, pow_succ]
      ring
    have hK2eq : ∀ k ∈ K2, w0 k = 1 - 2 * x k ∧ wV k = 1 - x k := by
      intro k hk
      rw [hK2, mem_filter] at hk
      have hnt : (i, true) ∉ cl k := fun h => hpol k hk.1 i ⟨h, hk.2⟩
      refine ⟨?_, rfl⟩
      simp only [hw0, hx, hcard_ins k, hfilt_i k, hk.2, hnt, if_true, if_false, empty_union,
        card_singleton, pow_succ]
      ring
    have hK1c : K1.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      rw [hK1, mem_filter] at ha hb
      exact Finset.disjoint_left.mp (hdisj a ha.1 b hb.1 hab) ha.2 hb.2
    have hK2c : K2.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      rw [hK2, mem_filter] at ha hb
      exact Finset.disjoint_left.mp (hdisj a ha.1 b hb.1 hab) ha.2 hb.2
    -- decompose products
    have dK : ∏ k ∈ K, wV k = (∏ k ∈ K1, wV k) * ((∏ k ∈ K2, wV k) * ∏ k ∈ K0, wV k) := by
      rw [← Finset.prod_filter_mul_prod_filter_not K (fun k => (i, true) ∈ cl k),
        ← Finset.prod_filter_mul_prod_filter_not (K.filter (fun k => (i, true) ∉ cl k))
          (fun k => (i, false) ∈ cl k)]
      congr 2
      · apply Finset.prod_congr _ (fun _ _ => rfl); ext k; simp only [hK2, mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, fun h => hpol k h1 i ⟨h, h3⟩⟩, h3⟩
      · apply Finset.prod_congr _ (fun _ _ => rfl); ext k; simp only [hK0, mem_filter]; tauto
    have dKf : ∏ k ∈ Kf, w0 k = (∏ k ∈ K1, w0 k) * ∏ k ∈ K0, w0 k := by
      rw [← Finset.prod_filter_mul_prod_filter_not Kf (fun k => (i, true) ∈ cl k)]
      congr 1
      · apply Finset.prod_congr _ (fun _ _ => rfl); ext k; simp only [hKf, hK1, mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, fun h => hpol k h1 i ⟨h3, h⟩⟩, h3⟩
      · apply Finset.prod_congr _ (fun _ _ => rfl); ext k; simp only [hKf, hK0, mem_filter]; tauto
    have dKt : ∏ k ∈ Kt, w0 k = (∏ k ∈ K2, w0 k) * ∏ k ∈ K0, w0 k := by
      rw [← Finset.prod_filter_mul_prod_filter_not Kt (fun k => (i, false) ∈ cl k)]
      congr 1
      · apply Finset.prod_congr _ (fun _ _ => rfl); ext k; simp only [hKt, hK2, mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, fun h => hpol k h1 i ⟨h, h3⟩⟩, h3⟩
      · apply Finset.prod_congr _ (fun _ _ => rfl); ext k; simp only [hKt, hK0, mem_filter]; tauto
    have e0 : ∏ k ∈ K0, wV k = ∏ k ∈ K0, w0 k := Finset.prod_congr rfl hK0eq
    have p1 := prod_le_one_card K1 hK1c x
    have p2 := prod_le_one_card K2 hK2c x
    have q1 : ∏ k ∈ K1, w0 k = 1 - 2 * ∑ k ∈ K1, x k := by
      exact (Finset.prod_congr rfl (fun k hk => (hK1eq k hk).1)).trans p1.1
    have q1' : ∏ k ∈ K1, wV k = 1 - ∑ k ∈ K1, x k := by
      exact (Finset.prod_congr rfl (fun k hk => (hK1eq k hk).2)).trans p1.2
    have q2 : ∏ k ∈ K2, w0 k = 1 - 2 * ∑ k ∈ K2, x k := by
      exact (Finset.prod_congr rfl (fun k hk => (hK2eq k hk).1)).trans p2.1
    have q2' : ∏ k ∈ K2, wV k = 1 - ∑ k ∈ K2, x k := by
      exact (Finset.prod_congr rfl (fun k hk => (hK2eq k hk).2)).trans p2.2
    have W0 : 0 ≤ ∏ k ∈ K0, w0 k := by
      apply prod_nonneg; intro k _
      have : (1/2 : ℝ) ^ ((cl k).filter (fun l => l.1 ∈ V0)).card ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      simp only [hw0]; linarith
    have X1 : 0 ≤ ∑ k ∈ K1, x k := sum_nonneg (fun k _ => by positivity)
    have X2 : 0 ≤ ∑ k ∈ K2, x k := sum_nonneg (fun k _ => by positivity)
    show 2 ^ V0.card * ∏ k ∈ Kf, w0 k + 2 ^ V0.card * ∏ k ∈ Kt, w0 k ≤
      2 ^ (insert i V0).card * ∏ k ∈ K, wV k
    rw [dK, dKf, dKt, e0, q1, q1', q2, q2', Finset.card_insert_of_notMem hi, pow_succ]
    have h2 : (0:ℝ) ≤ 2 ^ V0.card := by positivity
    have : 0 ≤ 2 ^ V0.card * (∏ k ∈ K0, w0 k) * ((∑ k ∈ K1, x k) * ∑ k ∈ K2, x k) :=
      mul_nonneg (mul_nonneg h2 W0) (mul_nonneg X1 X2)
    nlinarith [this]

/-! ## Representation counts -/

/-- Lower summands of the representations of `m` by `B`. -/
noncomputable def lows (B : Set ℕ) (m : ℕ) : Finset ℕ := by
  classical exact (Finset.range (m+1)).filter (fun y => y ∈ B ∧ m - y ∈ B ∧ 2 * y ≤ m)

/-- Number of representations of `m` as a sum of two elements of `B`. -/
noncomputable def rc (B : Set ℕ) (m : ℕ) : ℕ := (lows B m).card

/-- `m` is a sum of two elements of `B`. -/
def Rep (B : Set ℕ) (m : ℕ) : Prop := ∃ y, y ∈ B ∧ m - y ∈ B ∧ y ≤ m

lemma mem_lows {B : Set ℕ} {m z : ℕ} : z ∈ lows B m ↔ z ∈ B ∧ m - z ∈ B ∧ 2 * z ≤ m := by
  classical
  unfold lows
  rw [mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

lemma Rep.mono {B C : Set ℕ} (h : B ⊆ C) {m : ℕ} (hB : Rep B m) : Rep C m := by
  obtain ⟨y, h1, h2, h3⟩ := hB; exact ⟨y, h h1, h h2, h3⟩

lemma card_hit_le (B : Set ℕ) (m : ℕ) (Z : Finset ℕ) :
    ((lows B m).filter (fun z => z ∈ Z ∨ m - z ∈ Z)).card ≤ Z.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun z => if z ∈ Z then z else m - z)
  · intro z hz
    simp only [coe_filter, Set.mem_setOf_eq] at hz
    simp only [mem_coe]
    split_ifs with h
    · exact h
    · exact hz.2.resolve_left h
  · intro z hz z' hz' hzz
    simp only [coe_filter, Set.mem_setOf_eq, mem_lows] at hz hz'
    simp only at hzz
    split_ifs at hzz <;> omega

lemma rc_le_of_hit (B : Set ℕ) (m : ℕ) (Z : Finset ℕ)
    (h : ∀ z ∈ lows B m, z ∈ Z ∨ m - z ∈ Z) : rc B m ≤ Z.card := by
  classical
  refine le_trans (le_of_eq ?_) (card_hit_le B m Z)
  unfold rc; congr 1; ext z; simp only [mem_filter]
  exact ⟨fun hz => ⟨hz, h z hz⟩, fun hz => hz.1⟩

lemma rc_mono {B C : Set ℕ} (h : B ⊆ C) (m : ℕ) : rc B m ≤ rc C m := by
  unfold rc; apply card_le_card; intro z hz
  rw [mem_lows] at hz ⊢; exact ⟨h hz.1, h hz.2.1, hz.2.2⟩

lemma rc_le_add {B C : Set ℕ} (Z : Finset ℕ) (h : B ⊆ C ∪ ↑Z) (m : ℕ) :
    rc B m ≤ rc C m + Z.card := by
  classical
  have hsub : lows B m ⊆ lows C m ∪ (lows B m).filter (fun z => z ∈ Z ∨ m - z ∈ Z) := by
    intro z hz
    rw [mem_union, mem_filter]
    by_cases hZ : z ∈ Z ∨ m - z ∈ Z
    · exact Or.inr ⟨hz, hZ⟩
    · left
      push_neg at hZ
      rw [mem_lows] at hz ⊢
      refine ⟨?_, ?_, hz.2.2⟩
      · rcases h hz.1 with h1 | h1
        · exact h1
        · exact absurd h1 hZ.1
      · rcases h hz.2.1 with h1 | h1
        · exact h1
        · exact absurd h1 hZ.2
  unfold rc
  calc (lows B m).card ≤ (lows C m ∪ (lows B m).filter (fun z => z ∈ Z ∨ m - z ∈ Z)).card :=
        card_le_card hsub
    _ ≤ (lows C m).card + ((lows B m).filter (fun z => z ∈ Z ∨ m - z ∈ Z)).card :=
        card_union_le _ _
    _ ≤ (lows C m).card + Z.card := by have := card_hit_le B m Z; omega


/-! ## The transversal count (Erdős–Nathanson, Lemmas 1 and 2) -/

/-- Strict lower summands of representations of `n` by `B`. -/
noncomputable def Pn (B : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical exact (range n).filter (fun y => y ∈ B ∧ n - y ∈ B ∧ 2 * y < n)

/-- The middle summand `n / 2`, when it gives a representation. -/
noncomputable def Hn (B : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical exact (range (n+1)).filter (fun y => y ∈ B ∧ 2 * y = n)

/-- The transversal attached to a choice `Y`. -/
def XY (P H : Finset ℕ) (n : ℕ) (Y : Finset ℕ) : Finset ℕ :=
  Y ∪ (P \ Y).image (fun y => n - y) ∪ H

/-- Clause attached to the representation `z + (m - z)`. -/
def cl (P : Finset ℕ) (n m z : ℕ) : Finset (ℕ × Bool) :=
  (P.filter (fun y => y = z ∨ y = m - z)).image (fun y => (y, true)) ∪
  (P.filter (fun y => n - y = z ∨ n - y = m - z)).image (fun y => (y, false))

lemma mem_Pn {B : Set ℕ} {n y : ℕ} : y ∈ Pn B n ↔ y ∈ B ∧ n - y ∈ B ∧ 2 * y < n := by
  classical
  unfold Pn; rw [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

lemma mem_Hn {B : Set ℕ} {n y : ℕ} : y ∈ Hn B n ↔ y ∈ B ∧ 2 * y = n := by
  classical
  unfold Hn; rw [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

lemma mem_cl_true {P : Finset ℕ} {n m z y : ℕ} :
    (y, true) ∈ cl P n m z ↔ y ∈ P ∧ (y = z ∨ y = m - z) := by
  unfold cl; simp

lemma mem_cl_false {P : Finset ℕ} {n m z y : ℕ} :
    (y, false) ∈ cl P n m z ↔ y ∈ P ∧ (n - y = z ∨ n - y = m - z) := by
  unfold cl; simp

lemma bad_count (B : Set ℕ) (n m : ℕ) (hmn : m ≠ n) :
    (∑ Y ∈ (Pn B n).powerset,
      (if (∀ z ∈ lows B m, z ∈ XY (Pn B n) (Hn B n) n Y ∨ m - z ∈ XY (Pn B n) (Hn B n) n Y)
        then (1:ℝ) else 0))
      ≤ 2 ^ (Pn B n).card * ((16/9) * (3/4 : ℝ) ^ rc B m) := by
  set P := Pn B n with hP
  set H := Hn B n with hH
  set Q := (lows B m).filter (fun z => z ∉ H ∧ m - z ∉ H) with hQ
  have hQl : ∀ z ∈ Q, z ∈ B ∧ m - z ∈ B ∧ 2 * z ≤ m ∧ z ∉ H ∧ m - z ∉ H := by
    intro z hz
    rw [hQ, mem_filter, mem_lows] at hz
    exact ⟨hz.1.1, hz.1.2.1, hz.1.2.2, hz.2⟩
  have H1 : ∀ k ∈ Q, ∀ k' ∈ Q, k ≠ k' → Disjoint (cl P n m k) (cl P n m k') := by
    intro k hk k' hk' hne
    have a := hQl k hk
    have b := hQl k' hk'
    rw [Finset.disjoint_left]
    rintro ⟨y, bb⟩ h1 h2
    cases bb
    · rw [mem_cl_false] at h1 h2; omega
    · rw [mem_cl_true] at h1 h2; omega
  have H2 : ∀ k ∈ Q, ∀ j, ¬ ((j, true) ∈ cl P n m k ∧ (j, false) ∈ cl P n m k) := by
    intro k hk j ⟨h1, h2⟩
    have a := hQl k hk
    rw [mem_cl_true] at h1
    rw [mem_cl_false] at h2
    have := (mem_Pn.mp h1.1).2.2
    omega
  have hcb := clause_bound (cl P n m) P Q H1 H2
  -- step 1: bad choices satisfy all clauses
  have step1 : (∑ Y ∈ P.powerset,
      (if (∀ z ∈ lows B m, z ∈ XY P H n Y ∨ m - z ∈ XY P H n Y) then (1:ℝ) else 0)) ≤
      ∑ Y ∈ P.powerset,
      (if ∀ k ∈ Q, ∃ l ∈ cl P n m k, l.1 ∈ P ∧ (l.1 ∈ Y ↔ l.2 = true) then (1:ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro Y hY
    have hYP : Y ⊆ P := mem_powerset.mp hY
    by_cases hbad : ∀ z ∈ lows B m, z ∈ XY P H n Y ∨ m - z ∈ XY P H n Y
    · have : ∀ k ∈ Q, ∃ l ∈ cl P n m k, l.1 ∈ P ∧ (l.1 ∈ Y ↔ l.2 = true) := by
        intro k hk
        have hk' := hQl k hk
        have key : ∀ e, e ∈ XY P H n Y → e ∉ H → (e = k ∨ e = m - k) →
            ∃ l ∈ cl P n m k, l.1 ∈ P ∧ (l.1 ∈ Y ↔ l.2 = true) := by
          intro e he heH hek
          unfold XY at he
          rw [mem_union, mem_union, mem_image] at he
          rcases he with (he | ⟨y, hy, rfl⟩) | he
          · exact ⟨(e, true), mem_cl_true.mpr ⟨hYP he, hek⟩, hYP he, by simp [he]⟩
          · replace hy := Finset.mem_sdiff.mp hy
            exact ⟨(y, false), mem_cl_false.mpr ⟨hy.1, hek⟩, hy.1, by simp [hy.2]⟩
          · exact absurd he heH
        have hz : k ∈ lows B m := (mem_filter.mp (hQ ▸ hk)).1
        rcases hbad k hz with h | h
        · exact key k h hk'.2.2.2.1 (Or.inl rfl)
        · exact key (m - k) h hk'.2.2.2.2 (Or.inr rfl)
      rw [if_pos hbad, if_pos this]
    · rw [if_neg hbad]
      split_ifs <;> norm_num
  -- step 3: each clause has weight at most 3/4
  have step3 : ∏ k ∈ Q, (1 - (1/2 : ℝ) ^ ((cl P n m k).filter (fun l => l.1 ∈ P)).card) ≤
      (3/4 : ℝ) ^ Q.card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro k _
      have : (1/2 : ℝ) ^ ((cl P n m k).filter (fun l => l.1 ∈ P)).card ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    · intro k _
      set f : ℕ → ℕ × Bool := fun e => if 2 * e < n then (e, true) else (n - e, false)
      have hsub : cl P n m k ⊆ {f k, f (m - k)} := by
        rintro ⟨y, bb⟩ hl
        cases bb
        · rw [mem_cl_false] at hl
          have hy := (mem_Pn.mp hl.1).2.2
          rw [mem_insert, mem_singleton]
          rcases hl.2 with h | h
          · left; simp only [f]; rw [if_neg (by omega)]; congr 1; omega
          · right; simp only [f]; rw [if_neg (by omega)]; congr 1; omega
        · rw [mem_cl_true] at hl
          have hy := (mem_Pn.mp hl.1).2.2
          rw [mem_insert, mem_singleton]
          rcases hl.2 with h | h
          · left; simp only [f]; rw [if_pos (by omega)]; rw [h]
          · right; simp only [f]; rw [if_pos (by omega)]; rw [h]
      have hc : ((cl P n m k).filter (fun l => l.1 ∈ P)).card ≤ 2 := by
        calc ((cl P n m k).filter (fun l => l.1 ∈ P)).card ≤ (cl P n m k).card :=
              card_filter_le _ _
          _ ≤ ({f k, f (m - k)} : Finset (ℕ × Bool)).card := card_le_card hsub
          _ ≤ 2 := card_le_two
      have : (1/2 : ℝ) ^ 2 ≤ (1/2 : ℝ) ^ ((cl P n m k).filter (fun l => l.1 ∈ P)).card :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
      norm_num at this ⊢
      linarith
  -- step 4: few representations are lost
  have step4 : rc B m ≤ Q.card + 2 := by
    have hsub : lows B m ⊆ Q ∪ {n / 2, m - n / 2} := by
      intro z hz
      rw [mem_union]
      by_cases h : z ∉ H ∧ m - z ∉ H
      · left; rw [hQ, mem_filter]; exact ⟨hz, h⟩
      · right
        rw [mem_lows] at hz
        rw [not_and_or, not_not, not_not, hH, mem_Hn, mem_Hn] at h
        rw [mem_insert, mem_singleton]
        omega
    unfold rc
    calc (lows B m).card ≤ (Q ∪ {n / 2, m - n / 2}).card := card_le_card hsub
      _ ≤ Q.card + ({n / 2, m - n / 2} : Finset ℕ).card := card_union_le _ _
      _ ≤ Q.card + 2 := by have := (card_le_two : ({n / 2, m - n / 2} : Finset ℕ).card ≤ 2); omega
  have step5 : (3/4 : ℝ) ^ Q.card ≤ (16/9) * (3/4 : ℝ) ^ rc B m := by
    have : (3/4 : ℝ) ^ (Q.card + 2) ≤ (3/4 : ℝ) ^ rc B m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) step4
    rw [pow_add] at this
    nlinarith [this]
  calc _ ≤ _ := step1
    _ ≤ _ := hcb
    _ ≤ 2 ^ P.card * (3/4 : ℝ) ^ Q.card :=
        mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left step5 (by positivity)


lemma rpow_bound (c' : ℝ) (m r : ℕ) (hm : 0 < m) (h : c' * Real.log m < r) :
    (3/4 : ℝ) ^ r ≤ (m : ℝ) ^ (-(c' * Real.log (4/3))) := by
  have hl : 0 < Real.log (4/3) := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by exact_mod_cast hm)]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have : Real.log (3/4) = - Real.log (4/3) := by rw [← Real.log_inv]; norm_num
  rw [this]
  nlinarith

lemma exists_X (B : Set ℕ) (n W : ℕ) (c' : ℝ) (hc' : 0 < c')
    (hsum : ∀ M : Finset ℕ, (∀ m ∈ M, W < m) →
      ∑ m ∈ M, (m:ℝ) ^ (-(c' * Real.log (4/3))) < 9/16)
    (hB : ∀ m, W < m → c' * Real.log m < rc B m) :
    ∃ X : Finset ℕ, (∀ x ∈ X, ∃ y, y ∈ B ∧ n - y ∈ B ∧ y ≤ n ∧ (x = y ∨ x = n - y)) ∧
      (∀ y, y ∈ B → n - y ∈ B → y ≤ n → y ∈ X ∨ n - y ∈ X) ∧
      (∀ m, W < m → m ≠ n → ∃ z, z ∈ B ∧ m - z ∈ B ∧ z ≤ m ∧ z ∉ X ∧ m - z ∉ X) := by
  set P := Pn B n with hP
  set H := Hn B n with hH
  set M0 : ℕ := ⌈Real.exp ((n + 1 : ℝ) / c')⌉₊ with hM0
  have hbig : ∀ m : ℕ, M0 < m → (n + 1 : ℝ) < c' * Real.log m := by
    intro m hm
    have hm' : (M0 : ℝ) < m := by exact_mod_cast hm
    have h1 : Real.exp ((n+1:ℝ)/c') < m := lt_of_le_of_lt (Nat.le_ceil _) hm'
    have h2 : (n+1:ℝ)/c' < Real.log m :=
      (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) h1)).mpr h1
    rw [div_lt_iff₀ hc'] at h2; linarith
  set Ms := (range (M0 + 1)).filter (fun m => W < m ∧ m ≠ n) with hMs
  set f : ℕ → ℝ := fun m => (m:ℝ) ^ (-(c' * Real.log (4/3))) with hf
  have hMsum : ∑ m ∈ Ms, f m < 9/16 := hsum Ms (fun m hm => (mem_filter.mp hm).2.1)
  have hcount : ∑ Y ∈ P.powerset, ∑ m ∈ Ms,
      (if (∀ z ∈ lows B m, z ∈ XY P H n Y ∨ m - z ∈ XY P H n Y) then (1:ℝ) else 0) <
      ∑ Y ∈ P.powerset, (1:ℝ) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ m ∈ Ms, 2 ^ P.card * ((16/9) * f m) := by
          apply sum_le_sum; intro m hm
          have hm' := mem_filter.mp hm
          refine (bad_count B n m hm'.2.2).trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact rpow_bound c' m (rc B m) (by omega) (hB m hm'.2.1)
      _ = 2 ^ P.card * ((16/9) * ∑ m ∈ Ms, f m) := by rw [Finset.mul_sum, Finset.mul_sum]
      _ < 2 ^ P.card * ((16/9) * (9/16)) := by
          apply mul_lt_mul_of_pos_left _ (by positivity)
          exact mul_lt_mul_of_pos_left hMsum (by norm_num)
      _ = ∑ Y ∈ P.powerset, (1:ℝ) := by simp [card_powerset]
  obtain ⟨Y, hY, hlt⟩ := Finset.exists_lt_of_sum_lt hcount
  have hYP : Y ⊆ P := mem_powerset.mp hY
  have hgood : ∀ m ∈ Ms, ¬ (∀ z ∈ lows B m, z ∈ XY P H n Y ∨ m - z ∈ XY P H n Y) := by
    intro m hm hbad
    have := Finset.single_le_sum (f := fun m =>
      (if (∀ z ∈ lows B m, z ∈ XY P H n Y ∨ m - z ∈ XY P H n Y) then (1:ℝ) else 0))
      (fun m _ => by split_ifs <;> norm_num) hm
    simp only [if_pos hbad] at this
    linarith
  set X := XY P H n Y with hX
  have hXa : ∀ x ∈ X, ∃ y, y ∈ B ∧ n - y ∈ B ∧ y ≤ n ∧ (x = y ∨ x = n - y) := by
    intro x hx
    rw [hX] at hx
    unfold XY at hx
    rw [mem_union, mem_union, mem_image] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | hx
    · have := mem_Pn.mp (hYP hx)
      exact ⟨x, this.1, this.2.1, by omega, Or.inl rfl⟩
    · have := mem_Pn.mp (Finset.mem_sdiff.mp hy).1
      exact ⟨y, this.1, this.2.1, by omega, Or.inr rfl⟩
    · have := mem_Hn.mp hx
      have e : n - x = x := by omega
      exact ⟨x, this.1, by rw [e]; exact this.1, by omega, Or.inl rfl⟩
  refine ⟨X, hXa, ?_, ?_⟩
  · intro y hy1 hy2 hyn
    rcases lt_trichotomy (2 * y) n with h | h | h
    · have hyP : y ∈ P := mem_Pn.mpr ⟨hy1, hy2, h⟩
      by_cases hyY : y ∈ Y
      · left; rw [hX]; unfold XY; rw [mem_union, mem_union]; exact Or.inl (Or.inl hyY)
      · right; rw [hX]; unfold XY; rw [mem_union, mem_union, mem_image]
        exact Or.inl (Or.inr ⟨y, Finset.mem_sdiff.mpr ⟨hyP, hyY⟩, rfl⟩)
    · left; rw [hX]; unfold XY; rw [mem_union]; exact Or.inr (mem_Hn.mpr ⟨hy1, h⟩)
    · have e : n - (n - y) = y := by omega
      have hyP : n - y ∈ P := mem_Pn.mpr ⟨hy2, by rw [e]; exact hy1, by omega⟩
      by_cases hyY : n - y ∈ Y
      · right; rw [hX]; unfold XY; rw [mem_union, mem_union]; exact Or.inl (Or.inl hyY)
      · left; rw [hX]; unfold XY; rw [mem_union, mem_union, mem_image]
        exact Or.inl (Or.inr ⟨n - y, Finset.mem_sdiff.mpr ⟨hyP, hyY⟩, e⟩)
  · intro m hWm hmn
    by_cases hm0 : m ≤ M0
    · have hmMs : m ∈ Ms := mem_filter.mpr ⟨mem_range.mpr (by omega), hWm, hmn⟩
      have := hgood m hmMs
      push_neg at this
      obtain ⟨z, hz, h1, h2⟩ := this
      have hz' := mem_lows.mp hz
      exact ⟨z, hz'.1, hz'.2.1, by omega, h1, h2⟩
    · by_contra hcon
      push_neg at hcon
      have hhit : ∀ z ∈ lows B m, z ∈ X ∨ m - z ∈ X := by
        intro z hz
        have hz' := mem_lows.mp hz
        by_cases h : z ∈ X
        · exact Or.inl h
        · exact Or.inr (hcon z hz'.1 hz'.2.1 (by omega) h)
      have h1 := rc_le_of_hit B m X hhit
      have h2 : X.card ≤ n + 1 := by
        have : X ⊆ range (n + 1) := by
          intro x hx
          obtain ⟨y, -, -, hy, hxy⟩ := hXa x hx
          rw [mem_range]; omega
        simpa using card_le_card this
      have h3 := hbig m (by omega)
      have h4 := hB m hWm
      have : (rc B m : ℝ) ≤ n + 1 := by exact_mod_cast h1.trans h2
      linarith


/-! ## One stage of the Erdős–Nathanson construction -/

lemma log_gap (c c' : ℝ) (hcc : c' < c) (K : ℝ) :
    ∃ T : ℕ, ∀ m : ℕ, T ≤ m → c' * Real.log m + K < c * Real.log m := by
  refine ⟨⌈Real.exp (K / (c - c'))⌉₊ + 1, fun m hm => ?_⟩
  have hd : 0 < c - c' := by linarith
  have hm' : (⌈Real.exp (K / (c - c'))⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm
  have h1 : Real.exp (K / (c - c')) < m := by
    linarith [Nat.le_ceil (Real.exp (K / (c - c')))]
  have h2 : K / (c - c') < Real.log m :=
    (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) h1)).mpr h1
  rw [div_lt_iff₀ hd] at h2
  linarith

lemma exists_large {A' : Set ℕ} {N2 : ℕ} (hrep : ∀ m, N2 ≤ m → Rep A' m) (T : ℕ) :
    ∃ b ∈ A', T < b := by
  obtain ⟨y, h1, h2, h3⟩ := hrep (2 * T + 2 + N2) (by omega)
  by_cases h : y ≤ T
  · exact ⟨_, h2, by omega⟩
  · exact ⟨y, h1, by omega⟩

lemma stage (A A' : Set ℕ) (L v N1 N2 : ℕ) (c c' : ℝ) (hc' : 0 < c') (hcc : c' < c)
    (hN : N1 ≤ N2)
    (hsum : ∀ M : Finset ℕ, (∀ m ∈ M, N2 ≤ m) →
      ∑ m ∈ M, (m:ℝ) ^ (-(c' * Real.log (4/3))) < 9/16)
    (hA : ∀ m, N1 ≤ m → c * Real.log m < rc A m)
    (hcof : ∀ x ∈ A, L < x → x ∈ A')
    (hrep : ∀ m, N2 ≤ m → Rep A' m) (hv : v ∈ A') (hvL : v ≤ L) :
    ∃ A'' : Set ℕ, ∃ L' : ℕ, A'' ⊆ A' ∧ L < L' ∧ (∀ x ≤ L, x ∈ A'' ↔ x ∈ A') ∧
      (∀ x ∈ A, L' < x → x ∈ A'') ∧ (∀ m, N2 ≤ m → Rep A'' m) ∧
      ∃ n, L < n ∧ ¬ Rep (A'' \ {v}) n := by
  classical
  obtain ⟨T1, hT1⟩ := log_gap c c' hcc ((L:ℝ) + 1)
  set w1 := max (max (L+1) N2) T1 with hw1
  have hw1L : L < w1 := by omega
  have hw1N : N2 ≤ w1 := by omega
  have hw1T : T1 ≤ w1 := by omega
  obtain ⟨T2, hT2⟩ := log_gap c c' hcc ((L:ℝ) + 1 + (w1 + 1))
  obtain ⟨b, hbA, hb⟩ := exists_large hrep (3 * w1 + T2)
  set n := v + b with hn
  set X' : Finset ℕ :=
    ((range (w1+1)).filter (fun y => y ∈ A' ∧ n - y ∈ A')).image (fun y => n - y) with hX'
  have hX'mem : ∀ x ∈ X', n - w1 ≤ x ∧ x ≤ n := by
    intro x hx
    rw [hX', mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_filter, mem_range] at hy
    omega
  have hX'card : X'.card ≤ w1 + 1 := by
    calc X'.card ≤ ((range (w1+1)).filter (fun y => y ∈ A' ∧ n - y ∈ A')).card := card_image_le
      _ ≤ (range (w1+1)).card := card_filter_le _ _
      _ = w1 + 1 := card_range _
  set A1 := A' \ (↑X' : Set ℕ) with hA1
  have hAA' : ∀ m, rc A m ≤ rc A' m + (L + 1) := by
    intro m
    have := rc_le_add (range (L+1)) (B := A) (C := A') (by
      intro x hx
      by_cases h : x ≤ L
      · right; rw [mem_coe, mem_range]; omega
      · left; exact hcof x hx (by omega)) m
    simpa using this
  have hA'A1 : ∀ m, rc A' m ≤ rc A1 m + X'.card := by
    intro m
    refine rc_le_add X' ?_ m
    intro x hx
    by_cases h : x ∈ X'
    · right; exact h
    · left; exact ⟨hx, h⟩
  have hA1small : ∀ m, m < n - w1 → rc A' m ≤ rc A1 m := by
    intro m hm
    unfold rc; apply card_le_card; intro z hz
    rw [mem_lows] at hz ⊢
    refine ⟨⟨hz.1, fun h => ?_⟩, ⟨hz.2.1, fun h => ?_⟩, hz.2.2⟩
    · have := hX'mem z h; omega
    · have := hX'mem (m - z) h; omega
  have hB : ∀ m, w1 < m → c' * Real.log m < rc A1 m := by
    intro m hm
    have hAm := hA m (by omega)
    by_cases hmn : m < n - w1
    · have h1 := hT1 m (by omega)
      have h2 : (rc A m : ℝ) ≤ rc A1 m + (L + 1) := by
        have := (hAA' m).trans (Nat.add_le_add_right (hA1small m hmn) _)
        exact_mod_cast this
      linarith
    · have h1 := hT2 m (by omega)
      have h2 : (rc A m : ℝ) ≤ rc A1 m + (w1 + 1) + (L + 1) := by
        have := (hAA' m).trans
          (Nat.add_le_add_right ((hA'A1 m).trans (Nat.add_le_add_left hX'card _)) _)
        exact_mod_cast this
      linarith
  obtain ⟨X, hXa, hXb, hXc⟩ := exists_X A1 n w1 c' hc'
    (fun M hM => hsum M (fun m hm => le_of_lt (lt_of_le_of_lt hw1N (hM m hm)))) hB
  have hnbig : ∀ y, y ∈ A1 → n - y ∈ A1 → y ≤ n → w1 < y ∧ w1 < n - y := by
    intro y hy1 hy2 hyn
    constructor
    · by_contra h
      apply hy2.2
      rw [mem_coe, hX', mem_image]
      exact ⟨y, by rw [mem_filter, mem_range]; exact ⟨by omega, hy1.1, hy2.1⟩, rfl⟩
    · by_contra h
      apply hy1.2
      rw [mem_coe, hX', mem_image]
      have e : n - (n - y) = y := by omega
      exact ⟨n - y, by rw [mem_filter, mem_range, e]; exact ⟨by omega, hy2.1, hy1.1⟩, e⟩
  have hXbig : ∀ x ∈ X, w1 < x ∧ x ≤ n := by
    intro x hx
    obtain ⟨y, h1, h2, h3, h4⟩ := hXa x hx
    have := hnbig y h1 h2 h3
    omega
  refine ⟨insert b (A1 \ (↑X : Set ℕ)), n, ?_, ?_, ?_, ?_, ?_, n, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact hbA
    · exact hx.1.1
  · omega
  · intro x hx
    constructor
    · intro h
      rcases h with rfl | h
      · exact hbA
      · exact h.1.1
    · intro h
      right
      refine ⟨⟨h, ?_⟩, ?_⟩
      · intro hx'; have := hX'mem x hx'; omega
      · intro hx'; have := hXbig x hx'; omega
  · intro x hxA hx
    right
    refine ⟨⟨hcof x hxA (by omega), ?_⟩, ?_⟩
    · intro hx'; have := hX'mem x hx'; omega
    · intro hx'; have := hXbig x hx'; omega
  · intro m hm
    by_cases h1 : m ≤ w1
    · obtain ⟨y, hy1, hy2, hy3⟩ := hrep m hm
      refine ⟨y, Or.inr ⟨⟨hy1, ?_⟩, ?_⟩, Or.inr ⟨⟨hy2, ?_⟩, ?_⟩, hy3⟩
      · intro hx'; have := hX'mem y hx'; omega
      · intro hx'; have := hXbig y hx'; omega
      · intro hx'; have := hX'mem (m - y) hx'; omega
      · intro hx'; have := hXbig (m - y) hx'; omega
    · by_cases h2 : m = n
      · refine ⟨v, Or.inr ⟨⟨hv, ?_⟩, ?_⟩, Or.inl (by omega), by omega⟩
        · intro hx'; have := hX'mem v hx'; omega
        · intro hx'; have := hXbig v hx'; omega
      · obtain ⟨z, hz1, hz2, hz3, hz4, hz5⟩ := hXc m (by omega) h2
        exact ⟨z, Or.inr ⟨hz1, hz4⟩, Or.inr ⟨hz2, hz5⟩, hz3⟩
  · omega
  · rintro ⟨y, ⟨hy1, hyv⟩, ⟨hy2, hy2v⟩, hyn⟩
    rcases hy1 with rfl | hy1
    · apply hy2v; show n - y = v; omega
    rcases hy2 with h | hy2
    · apply hyv; show y = v; omega
    · rcases hXb y hy1.1 hy2.1 hyn with h | h
      · exact hy1.2 h
      · exact hy2.2 h


/-! ## The limit of the construction -/

theorem main (A : Set ℕ) (c : ℝ) (hc : (Real.log (4/3))⁻¹ < c) (N1 : ℕ)
    (hA : ∀ m, N1 ≤ m → c * Real.log m < rc A m) :
    ∃ B ⊆ A, (∃ N, ∀ m, N ≤ m → Rep B m) ∧ ∀ v ∈ B, ∀ M, ∃ n, M ≤ n ∧ ¬ Rep (B \ {v}) n := by
  classical
  have hl : 0 < Real.log (4/3) := Real.log_pos (by norm_num)
  have hil : 0 < (Real.log (4/3))⁻¹ := inv_pos.mpr hl
  set c' := (c + (Real.log (4/3))⁻¹) / 2 with hc'def
  have hc'1 : (Real.log (4/3))⁻¹ < c' := by linarith
  have hc'0 : 0 < c' := by linarith
  have hcc : c' < c := by linarith
  have hp : 1 < c' * Real.log (4/3) := by
    have := mul_lt_mul_of_pos_right hc'1 hl
    rwa [inv_mul_cancel₀ hl.ne'] at this
  have hsumm : Summable (fun m : ℕ => (m:ℝ) ^ (-(c' * Real.log (4/3)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  obtain ⟨s, hs⟩ := hsumm.vanishing (Iio_mem_nhds (by norm_num : (0:ℝ) < 9/16))
  set N2 := max (s.sup id + 1) (max N1 1) with hN2
  have hN : N1 ≤ N2 := by omega
  have hsum : ∀ M : Finset ℕ, (∀ m ∈ M, N2 ≤ m) →
      ∑ m ∈ M, (m:ℝ) ^ (-(c' * Real.log (4/3))) < 9/16 := by
    intro M hM
    have : Disjoint M s := by
      rw [Finset.disjoint_left]
      intro m hm hms
      have h1 := hM m hm
      have h2 : m ≤ s.sup id := Finset.le_sup (f := id) hms
      omega
    exact hs M this
  have hrep0 : ∀ m, N2 ≤ m → Rep A m := by
    intro m hm
    have h1 := hA m (by omega)
    have h2 : 0 ≤ c * Real.log m := mul_nonneg (by linarith) (Real.log_natCast_nonneg m)
    have h3 : 0 < rc A m := by exact_mod_cast (lt_of_le_of_lt h2 h1)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp h3
    have hz' := mem_lows.mp hz
    exact ⟨z, hz'.1, hz'.2.1, by omega⟩
  let Inv : Set ℕ × ℕ → Prop := fun S =>
    S.1 ⊆ A ∧ (∀ x ∈ A, S.2 < x → x ∈ S.1) ∧ (∀ m, N2 ≤ m → Rep S.1 m)
  have hstep : ∀ (S : Set ℕ × ℕ) (v : ℕ), ∃ S' : Set ℕ × ℕ, Inv S →
      (Inv S' ∧ S'.1 ⊆ S.1 ∧ S.2 < S'.2 ∧ (∀ x ≤ S.2, x ∈ S'.1 ↔ x ∈ S.1) ∧
        (v ∈ S.1 → v ≤ S.2 → ∃ n, S.2 < n ∧ ¬ Rep (S'.1 \ {v}) n)) := by
    intro S v
    by_cases hS : Inv S
    · by_cases hv : v ∈ S.1 ∧ v ≤ S.2
      · obtain ⟨A'', L', h1, h2, h3, h4, h5, n, h6, h7⟩ :=
          stage A S.1 S.2 v N1 N2 c c' hc'0 hcc hN hsum hA hS.2.1 hS.2.2 hv.1 hv.2
        refine ⟨(A'', L'), fun _ => ⟨⟨h1.trans hS.1, h4, h5⟩, h1, h2, h3, fun _ _ => ⟨n, h6, h7⟩⟩⟩
      · refine ⟨(S.1, S.2 + 1), fun _ => ⟨⟨hS.1, fun x hx hx' => hS.2.1 x hx (by
          simp only at hx'; omega), hS.2.2⟩, subset_rfl, by simp, fun x _ => Iff.rfl,
          fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩⟩
    · exact ⟨S, fun h => absurd h hS⟩
  choose g hg using hstep
  let seq : ℕ → Set ℕ × ℕ := fun k => Nat.rec (A, 0) (fun j S => g S (Nat.unpair j).1) k
  have seq_zero : seq 0 = (A, 0) := rfl
  have seq_succ : ∀ k, seq (k+1) = g (seq k) (Nat.unpair k).1 := fun k => rfl
  have hInv : ∀ k, Inv (seq k) := by
    intro k
    induction k with
    | zero => rw [seq_zero]; exact ⟨subset_rfl, fun x hx _ => hx, hrep0⟩
    | succ k ih => rw [seq_succ]; exact (hg _ _ ih).1
  have hP : ∀ k, (seq (k+1)).1 ⊆ (seq k).1 ∧ (seq k).2 < (seq (k+1)).2 ∧
      (∀ x ≤ (seq k).2, x ∈ (seq (k+1)).1 ↔ x ∈ (seq k).1) ∧
      ((Nat.unpair k).1 ∈ (seq k).1 → (Nat.unpair k).1 ≤ (seq k).2 →
        ∃ n, (seq k).2 < n ∧ ¬ Rep ((seq (k+1)).1 \ {(Nat.unpair k).1}) n) := by
    intro k; rw [seq_succ]; exact (hg _ _ (hInv k)).2
  have hLk : ∀ k, k ≤ (seq k).2 := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => have := (hP k).2.1; omega
  have hLmono : ∀ k j, k ≤ j → (seq k).2 ≤ (seq j).2 := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => have := (hP j).2.1; omega
  have hanti : ∀ k j, k ≤ j → (seq j).1 ⊆ (seq k).1 := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact subset_rfl
    | succ j _ ih => exact (hP j).1.trans ih
  have hagree : ∀ k j, k ≤ j → ∀ x ≤ (seq k).2, (x ∈ (seq j).1 ↔ x ∈ (seq k).1) := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact fun x _ => Iff.rfl
    | succ j hkj ih =>
      intro x hx
      rw [(hP j).2.2.1 x (hx.trans (hLmono k j hkj))]
      exact ih x hx
  set B := ⋂ k, (seq k).1 with hB
  have hBk : ∀ k, B ⊆ (seq k).1 := fun k => Set.iInter_subset _ k
  have hBmem : ∀ k, ∀ x ≤ (seq k).2, (x ∈ B ↔ x ∈ (seq k).1) := by
    intro k x hx
    constructor
    · exact fun h => hBk k h
    · intro h
      rw [hB, Set.mem_iInter]
      intro j
      rcases le_total k j with hkj | hjk
      · exact (hagree k j hkj x hx).mpr h
      · exact hanti j k hjk h
  refine ⟨B, ?_, ⟨N2, ?_⟩, ?_⟩
  · intro x hx; have := hBk 0 hx; rw [seq_zero] at this; exact this
  · intro m hm
    obtain ⟨y, h1, h2, h3⟩ := (hInv m).2.2 m hm
    have hm' := hLk m
    exact ⟨y, (hBmem m y (by omega)).mpr h1, (hBmem m (m - y) (by omega)).mpr h2, h3⟩
  · intro v hv M
    set k := Nat.pair v (M + v) with hk
    have hku : Nat.unpair k = (v, M + v) := Nat.unpair_pair _ _
    have hk1 : M + v ≤ k := Nat.right_le_pair _ _
    have hLk' := hLk k
    have hvk : v ∈ (seq k).1 := hBk k hv
    have := (hP k).2.2.2
    rw [hku] at this
    obtain ⟨n, hn1, hn2⟩ := this hvk (by omega)
    refine ⟨n, by omega, fun hrep => hn2 (hrep.mono ?_)⟩
    exact Set.diff_subset_diff_left (hBk (k+1))


lemma ncard_eq_rc (A : Set ℕ) (n : ℕ) : Erdos868.ncard_add_repr A 2 n = rc A n := by
  unfold Erdos868.ncard_add_repr rc
  have key : {a : Fin 2 → ℕ | Monotone a ∧ Set.range a ⊆ A ∧ ∑ i, a i = n} =
      (fun y => ![y, n - y]) '' (↑(lows A n) : Set ℕ) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_image, mem_coe, mem_lows]
    constructor
    · rintro ⟨hmono, hrange, hsum⟩
      rw [Fin.sum_univ_two] at hsum
      have h01 : a 0 ≤ a 1 := hmono (by decide)
      have h0 : a 0 ∈ A := hrange ⟨0, rfl⟩
      have h1 : a 1 ∈ A := hrange ⟨1, rfl⟩
      refine ⟨a 0, ⟨h0, by rw [show n - a 0 = a 1 by omega]; exact h1, by omega⟩, ?_⟩
      funext i
      fin_cases i
      · rfl
      · simp; omega
    · rintro ⟨y, ⟨h1, h2, h3⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all <;> omega
      · rintro x ⟨i, rfl⟩
        fin_cases i
        · simpa using h1
        · simpa using h2
      · rw [Fin.sum_univ_two]; simp; omega
  rw [key, Set.ncard_image_of_injective _ ?_, Set.ncard_coe_finset]
  intro y y' h
  have := congrFun h 0
  simpa using this

end OMA868

theorem OMA.solution : type_of% @Erdos868.erdos_868.variants.fixed_ε := by
  intro A c hc _ hev
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hev
  have hA : ∀ m, N1 ≤ m → c * Real.log m < OMA868.rc A m := by
    intro m hm
    have := hN1 m hm
    rwa [OMA868.ncard_eq_rc] at this
  obtain ⟨B, hBA, ⟨N, hN⟩, hmin⟩ := OMA868.main A c hc N1 hA
  refine ⟨B, hBA, ?_, ?_⟩
  · rw [Set.isAsymptoticAddBasisOfOrder_two_iff, Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨y, h1, h2, h3⟩ := hN m hm
    have e : m = y + (m - y) := by omega
    rw [e]
    exact Set.add_mem_add h1 h2
  · intro b hb hbasis
    rw [Set.isAsymptoticAddBasisOfOrder_two_iff, Nat.cofinite_eq_atTop,
      Filter.eventually_atTop] at hbasis
    obtain ⟨M, hM⟩ := hbasis
    obtain ⟨n, hn1, hn2⟩ := hmin b hb M
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp (hM n hn1)
    exact hn2 ⟨x, hx, by rw [show n - x = y by omega]; exact hy, by omega⟩
