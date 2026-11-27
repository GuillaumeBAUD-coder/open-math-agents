import FormalConjectures.ErdosProblems.«1013»

-- Problem: Erdős Problem 1013 — graver yackel
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1013.lean (declaration Erdos1013.erdos_1013.variants.graver_yackel)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Proof: Shearer-type bound alpha >= sqrt(m log m)/80 for triangle-free graphs (max of the
-- neighbourhood of a max-degree vertex and a Shearer induction), greedy colouring by removing
-- independent sets with the potential sqrt(m), giving chi <= 600 sqrt(n / log n); h3 k is
-- attained (Mycielski graphs from FormalConjecturesForMathlib).

open Real

namespace E1013

noncomputable def φ (y : ℝ) : ℝ := log y / y
noncomputable def g (y : ℝ) : ℝ := (1 - log y) / y ^ 2

lemma hasDerivAt_φ {y : ℝ} (hy : 0 < y) : HasDerivAt φ (g y) y := by
  have h := (hasDerivAt_log hy.ne').div (hasDerivAt_id y) hy.ne'
  refine h.congr_deriv ?_
  simp only [id]
  unfold g
  field_simp

lemma log_ge_two {y : ℝ} (hy : 8 ≤ y) : 2 ≤ log y := by
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  have : log 8 ≤ log y := Real.log_le_log (by norm_num) hy
  linarith

/-- `g` is monotone on `[8, ∞)`. -/
lemma g_mono {a b : ℝ} (ha : 8 ≤ a) (hab : a ≤ b) : g a ≤ g b := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · exact le_rfl
  have hapos : 0 < a := by linarith
  set s := b / a with hs
  have hs1 : 1 < s := by rw [hs, lt_div_iff₀ hapos]; linarith
  have hb : b = a * s := by rw [hs]; field_simp
  have hla := log_ge_two ha
  have hlogs : log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlb : log b = log a + log s := by
    rw [hb, Real.log_mul hapos.ne' (by linarith)]
  -- (log b - 1)/b^2 ≤ (log a - 1)/a^2
  have key : log s ≤ (s ^ 2 - 1) * (log a - 1) := by
    have h1 : s - 1 ≤ s ^ 2 - 1 := by nlinarith
    have h2 : (s ^ 2 - 1) * 1 ≤ (s ^ 2 - 1) * (log a - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
    linarith
  unfold g
  have hbpos : 0 < b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), hlb, hb]
  have hs0 : 0 < s := by linarith
  have : (1 - log a) * (a * s) ^ 2 - (1 - (log a + log s)) * a ^ 2
      = a ^ 2 * (log s - (s ^ 2 - 1) * (log a - 1)) := by ring
  nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sub_nonneg.2 key)]

/-- Tangent line inequality for `φ` on `[8, ∞)`. -/
lemma tangent {u w : ℝ} (hu : 8 ≤ u) (hw : 8 ≤ w) : φ u + g u * (w - u) ≤ φ w := by
  have hd : ∀ x, 8 ≤ x → HasDerivAt φ (g x) x := fun x hx => hasDerivAt_φ (by linarith)
  have hcont : ∀ a b, 8 ≤ a → ContinuousOn φ (Set.Icc a b) := by
    intro a b ha x hx
    exact (hd x (ha.trans hx.1)).continuousAt.continuousWithinAt
  rcases lt_trichotomy u w with h | rfl | h
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope φ g h (hcont u w hu)
      (fun x hx => hd x (by linarith [hx.1]))
    have hgc : g u ≤ g c := g_mono hu hc.1.le
    have : φ w - φ u = g c * (w - u) := by
      rw [hc', div_mul_cancel₀ _ (by linarith)]
    nlinarith
  · simp
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope φ g h (hcont w u hw)
      (fun x hx => hd x (by linarith [hx.1]))
    have hgc : g c ≤ g u := g_mono (by linarith [hc.1]) hc.2.le
    have : φ u - φ w = g c * (u - w) := by
      rw [hc', div_mul_cancel₀ _ (by linarith)]
    nlinarith

/-- The Shearer-type potential. -/
noncomputable def f (d : ℝ) : ℝ := φ (d + 8) / 20
noncomputable def f' (d : ℝ) : ℝ := g (d + 8) / 20

lemma f_tangent {d x : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x) : f d + f' d * (x - d) ≤ f x := by
  have := tangent (u := d + 8) (w := x + 8) (by linarith) (by linarith)
  unfold f f'
  have e : x + 8 - (d + 8) = x - d := by ring
  rw [e] at this
  linarith

lemma f'_nonpos {d : ℝ} (hd : 0 ≤ d) : f' d ≤ 0 := by
  unfold f' g
  have := log_ge_two (y := d + 8) (by linarith)
  have : (1 - log (d + 8)) / (d + 8) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

lemma f_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ f d := by
  unfold f φ
  have := log_ge_two (y := d + 8) (by linarith)
  have : 0 ≤ log (d + 8) / (d + 8) := div_nonneg (by linarith) (by linarith)
  linarith

/-- Shearer's differential inequality. -/
lemma f_ode {d : ℝ} (hd : 0 ≤ d) : 0 ≤ 1 - (d + 1) * f d + f' d * (d - d ^ 2) := by
  unfold f f' φ g
  set y := d + 8 with hy
  have hy8 : 8 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  set L := log y with hL
  have hL2 : 2 ≤ L := log_ge_two hy8
  have hLy : L ≤ y := (Real.log_le_sub_one_of_pos hypos).trans (by linarith)
  have hd' : d = y - 8 := by linarith
  have e : 1 - (d + 1) * (L / y / 20) + (1 - L) / y ^ 2 / 20 * (d - d ^ 2)
      = (20 * y ^ 2 - (L * (10 * d + 8) + d ^ 2 - d)) / (20 * y ^ 2) := by
    field_simp
    rw [hd']; ring
  rw [e]
  apply div_nonneg _ (by positivity)
  have h1 : L * (10 * d + 8) ≤ y * (10 * y) := by
    have : 10 * d + 8 ≤ 10 * y := by linarith
    have : 0 ≤ 10 * d + 8 := by linarith
    nlinarith
  have h2 : d ^ 2 ≤ y ^ 2 := by nlinarith
  nlinarith


open Finset

section Graph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def deg (W : Finset V) (x : V) : ℕ := #(W.filter (G.Adj x))

def e2 (W : Finset V) : ℕ := #((W ×ˢ W).filter (fun p => G.Adj p.1 p.2))

lemma e2_eq_sum (W : Finset V) : e2 G W = ∑ x ∈ W, deg G W x := by
  unfold e2 deg
  rw [card_filter, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [card_filter]

lemma pairs_card (N W : Finset V) :
    #((N ×ˢ W).filter (fun p => G.Adj p.1 p.2)) = ∑ x ∈ N, deg G W x := by
  unfold deg
  rw [card_filter, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [card_filter]

lemma sum_S (W : Finset V) :
    ∑ v ∈ W, ∑ w ∈ W.filter (G.Adj v), (deg G W w : ℝ) = ∑ w ∈ W, (deg G W w : ℝ) ^ 2 := by
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, sq]
  congr 1
  unfold deg
  congr 2
  ext v; simp [G.adj_comm]

lemma e2_remove (hG : G.CliqueFree 3) (W : Finset V) (v : V) :
    e2 G (W.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)) +
      2 * ∑ w ∈ W.filter (G.Adj v), deg G W w ≤ e2 G W := by
  set W' := W.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)
  set N := W.filter (G.Adj v)
  set P := (W ×ˢ W).filter (fun p => G.Adj p.1 p.2)
  set P1 := (N ×ˢ W).filter (fun p => G.Adj p.1 p.2)
  set P2 := P1.image Prod.swap
  set P3 := (W' ×ˢ W').filter (fun p => G.Adj p.1 p.2)
  have hNW : N ⊆ W := filter_subset _ _
  have hW'W : W' ⊆ W := filter_subset _ _
  have h1 : #P1 = ∑ w ∈ N, deg G W w := pairs_card G N W
  have h2 : #P2 = #P1 := card_image_of_injective _ Prod.swap_injective
  have hd12 : Disjoint P1 P2 := by
    rw [disjoint_left]
    intro p hp1 hp2
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp2
    simp only [P1, mem_filter, mem_product] at hp1 hq
    -- p = swap q, so p.1 = q.2 ∈ N and p.2 = q.1 ∈ N, adjacent
    have ha : G.Adj v q.1 := (mem_filter.1 hq.1.1).2
    have hb : G.Adj v q.2 := (mem_filter.1 hp1.1.1).2
    exact hG {v, q.1, q.2} (SimpleGraph.is3Clique_triple_iff.2 ⟨ha, hb, hq.2⟩)
  have hd3 : Disjoint (P1 ∪ P2) P3 := by
    rw [disjoint_left]
    intro p hp hp3
    simp only [P3, mem_filter, mem_product] at hp3
    have h1' := (mem_filter.1 hp3.1.1).2.2
    have h2' := (mem_filter.1 hp3.1.2).2.2
    rcases mem_union.1 hp with hp | hp
    · simp only [P1, mem_filter, mem_product] at hp
      exact h1' (mem_filter.1 hp.1.1).2
    · obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
      simp only [P1, mem_filter, mem_product] at hq
      exact h2' (mem_filter.1 hq.1.1).2
  have hsub : P1 ∪ P2 ∪ P3 ⊆ P := by
    intro p hp
    simp only [P, mem_filter, mem_product]
    rcases mem_union.1 hp with hp | hp
    · rcases mem_union.1 hp with hp | hp
      · simp only [P1, mem_filter, mem_product] at hp
        exact ⟨⟨hNW hp.1.1, hp.1.2⟩, hp.2⟩
      · obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
        simp only [P1, mem_filter, mem_product] at hq
        exact ⟨⟨hq.1.2, hNW hq.1.1⟩, hq.2.symm⟩
    · simp only [P3, mem_filter, mem_product] at hp
      exact ⟨⟨hW'W hp.1.1, hW'W hp.1.2⟩, hp.2⟩
  have := card_le_card hsub
  rw [card_union_of_disjoint hd3, card_union_of_disjoint hd12, h2, h1] at this
  have e1 : e2 G W' = #P3 := rfl
  have e3 : e2 G W = #P := rfl
  rw [e1, e3]
  omega

lemma exists_good (hG : G.CliqueFree 3) (W : Finset V) (hW : W.Nonempty) :
    ∃ v ∈ W, 0 ≤ 1 - ((deg G W v : ℝ) + 1) * f ((e2 G W : ℝ) / #W) +
      f' ((e2 G W : ℝ) / #W) * (((deg G W v : ℝ) + 1) * ((e2 G W : ℝ) / #W) -
        2 * ∑ w ∈ W.filter (G.Adj v), (deg G W w : ℝ)) := by
  set n : ℝ := ((#W : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hW.card_pos
  set d : ℝ := (e2 G W : ℝ) / n with hd
  have hd0 : 0 ≤ d := by positivity
  have he : (e2 G W : ℝ) = n * d := by rw [hd]; field_simp
  have hsumdeg : ∑ x ∈ W, (deg G W x : ℝ) = n * d := by
    rw [← he, e2_eq_sum]; push_cast; rfl
  by_contra hcon
  push Not at hcon
  have hsum := sum_lt_sum_of_nonempty hW hcon
  simp only [sum_const_zero] at hsum
  -- compute the sum
  have hS := sum_S G W
  have hCS : (∑ x ∈ W, (deg G W x : ℝ)) ^ 2 ≤ n * ∑ x ∈ W, (deg G W x : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hsumdeg] at hCS
  have hsq : n * d ^ 2 ≤ ∑ x ∈ W, (deg G W x : ℝ) ^ 2 := by
    have : n * (n * d ^ 2) ≤ n * ∑ x ∈ W, (deg G W x : ℝ) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hnpos
  have expand : ∑ v ∈ W, (1 - ((deg G W v : ℝ) + 1) * f d +
      f' d * (((deg G W v : ℝ) + 1) * d - 2 * ∑ w ∈ W.filter (G.Adj v), (deg G W w : ℝ)))
      = n - (n * d + n) * f d + f' d * ((n * d + n) * d
          - 2 * ∑ x ∈ W, (deg G W x : ℝ) ^ 2) := by
    rw [← hS]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, sum_const,
      nsmul_eq_mul, mul_one, hsumdeg]
    rw [← hn]
  rw [expand] at hsum
  have hf' := f'_nonpos hd0
  have hode := f_ode hd0
  have : f' d * ((n * d + n) * d - 2 * ∑ x ∈ W, (deg G W x : ℝ) ^ 2) ≥
      f' d * ((n * d + n) * d - 2 * (n * d ^ 2)) := by
    apply mul_le_mul_of_nonpos_left _ hf'
    linarith
  have : n * (1 - (d + 1) * f d + f' d * (d - d ^ 2)) ≥ 0 := mul_nonneg hnpos.le hode
  nlinarith

lemma ind (hG : G.CliqueFree 3) : ∀ k, ∀ W : Finset V, #W = k →
    ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧ (#W : ℝ) * f ((e2 G W : ℝ) / #W) ≤ #I := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W hWk
  rcases W.eq_empty_or_nonempty with hW | hW
  · refine ⟨∅, empty_subset _, by simp, ?_⟩
    simp [hW]
  obtain ⟨v, hvW, hgood⟩ := exists_good G hG W hW
  set W' := W.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hW'
  set N := W.filter (G.Adj v) with hN
  have hcompl : W.filter (fun x => ¬ (x ≠ v ∧ ¬ G.Adj v x)) = insert v N := by
    ext x
    simp only [mem_filter, mem_insert, hN]
    constructor
    · rintro ⟨hx, h⟩
      by_cases hxv : x = v
      · exact Or.inl hxv
      · exact Or.inr ⟨hx, by tauto⟩
    · rintro (rfl | ⟨hx, h⟩)
      · exact ⟨hvW, by simp⟩
      · exact ⟨hx, fun h' => h'.2 h⟩
  have hvN : v ∉ N := by simp [hN]
  have hcard : #W' + (#N + 1) = #W := by
    rw [← card_insert_of_notMem hvN, ← hcompl]
    exact card_filter_add_card_filter_not _
  have hlt : #W' < k := by omega
  obtain ⟨I', hI'W', hI'ind, hI'⟩ := ih _ hlt W' rfl
  have hvI' : v ∉ I' := fun h => by
    have := (mem_filter.1 (hI'W' h)).2.1; exact this rfl
  refine ⟨insert v I', ?_, ?_, ?_⟩
  · exact insert_subset hvW (hI'W'.trans (filter_subset _ _))
  · rw [coe_insert]
    refine hI'ind.insert fun u hu huv => ?_
    have := (mem_filter.1 (hI'W' hu)).2.2
    exact ⟨fun h => this h, fun h => this h.symm⟩
  · rw [card_insert_of_notMem hvI']
    push_cast
    -- real computation
    have hrem := e2_remove G hG W v
    have hremR : (e2 G W' : ℝ) + 2 * ∑ w ∈ N, (deg G W w : ℝ) ≤ e2 G W := by
      exact_mod_cast hrem
    set n : ℝ := ((#W : ℕ) : ℝ) with hn
    set n' : ℝ := ((#W' : ℕ) : ℝ) with hn'
    set D : ℝ := ((#N : ℕ) : ℝ) with hD
    have hDdeg : (deg G W v : ℝ) = D := rfl
    set S : ℝ := ∑ w ∈ N, (deg G W w : ℝ) with hS
    have hnn : n = n' + D + 1 := by
      rw [hn, hn', hD]; exact_mod_cast hcard.symm.trans (by ring)
    have hnpos : 0 < n := by rw [hn]; exact_mod_cast hW.card_pos
    set d : ℝ := (e2 G W : ℝ) / n with hd
    set d' : ℝ := (e2 G W' : ℝ) / n' with hd'
    have hd0 : 0 ≤ d := by positivity
    have hd'0 : 0 ≤ d' := by positivity
    have he : (e2 G W : ℝ) = n * d := by rw [hd]; field_simp
    have he' : n' * d' = (e2 G W' : ℝ) := by
      rcases eq_or_lt_of_le (Nat.zero_le #W') with h0 | h0
      · have hW'e : W' = ∅ := card_eq_zero.1 h0.symm
        have : e2 G W' = 0 := by unfold e2; rw [hW'e]; rfl
        rw [hn', ← h0, this]; simp
      · have : n' ≠ 0 := by rw [hn']; exact_mod_cast h0.ne'
        rw [hd']; field_simp
    have htan := f_tangent hd0 hd'0
    have hf' := f'_nonpos hd0
    have h1 : n' * (f d + f' d * (d' - d)) ≤ n' * f d' :=
      mul_le_mul_of_nonneg_left htan (Nat.cast_nonneg _)
    have h2 : f' d * (n' * d') ≥ f' d * (n * d - 2 * S - n' * d) + f' d * (n' * d) := by
      rw [← mul_add]
      apply mul_le_mul_of_nonpos_left _ hf'
      rw [he']; linarith
    rw [hDdeg] at hgood
    have hgood' : 0 ≤ 1 - (D + 1) * f d + f' d * ((D + 1) * d - 2 * S) := hgood
    have h3 : n * d - 2 * S - n' * d = (D + 1) * d - 2 * S := by rw [hnn]; ring
    rw [h3] at h2
    have h4 : n' * (f d + f' d * (d' - d)) = n' * f d + f' d * (n' * d') - f' d * (n' * d) := by
      ring
    have h5 : n * f d = n' * f d + (D + 1) * f d := by rw [hnn]; ring
    show n * f d ≤ (#I' : ℝ) + 1
    linarith

end Graph

section Graph2

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma f_anti {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) : f T ≤ f t := by
  have h := f_tangent (d := T) (x := t) (by linarith) ht
  have := f'_nonpos (d := T) (by linarith)
  nlinarith

lemma exists_deg_ge (W : Finset V) (hW : W.Nonempty) :
    ∃ v ∈ W, (e2 G W : ℝ) / #W ≤ deg G W v := by
  by_contra h
  push Not at h
  have hs := sum_lt_sum_of_nonempty hW h
  rw [sum_const, nsmul_eq_mul] at hs
  have hn : (0 : ℝ) < #W := by exact_mod_cast hW.card_pos
  rw [mul_div_cancel₀ _ hn.ne'] at hs
  have := e2_eq_sum G W
  have : (e2 G W : ℝ) = ∑ x ∈ W, (deg G W x : ℝ) := by exact_mod_cast this
  linarith

lemma nbhd_indep (hG : G.CliqueFree 3) (W : Finset V) (v : V) :
    G.IsIndepSet ((W.filter (G.Adj v) : Finset V) : Set V) := by
  intro a ha b hb hab hadj
  simp only [coe_filter, Set.mem_setOf_eq] at ha hb
  exact hG {v, a, b} (SimpleGraph.is3Clique_triple_iff.2 ⟨ha.2, hb.2, hadj⟩)

lemma alpha_big (hG : G.CliqueFree 3) (W : Finset V) (hW : 64 ≤ #W) :
    ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧
      Real.sqrt (#W * log #W) / 80 ≤ #I := by
  set m : ℝ := (#W : ℝ) with hm
  have hm64 : (64 : ℝ) ≤ m := by rw [hm]; exact_mod_cast hW
  have hlogm : 1 ≤ log m := by
    have := log_ge_two (y := m) (by linarith); linarith
  set T := Real.sqrt (m * log m) with hT
  have hT2 : T ^ 2 = m * log m := Real.sq_sqrt (by positivity)
  have hTm : Real.sqrt m ≤ T := Real.sqrt_le_sqrt (by nlinarith)
  have hsm : 8 ≤ Real.sqrt m := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hm64
  have hT8 : 8 ≤ T := le_trans hsm hTm
  have hWne : W.Nonempty := by rw [← card_pos]; omega
  set t := (e2 G W : ℝ) / #W with ht
  have ht0 : 0 ≤ t := by positivity
  rcases le_or_gt T t with h | h
  · obtain ⟨v, hv, hvdeg⟩ := exists_deg_ge G W hWne
    refine ⟨W.filter (G.Adj v), filter_subset _ _, nbhd_indep G hG W v, ?_⟩
    have : (deg G W v : ℝ) = #(W.filter (G.Adj v)) := rfl
    rw [← this]
    linarith
  · obtain ⟨I, hIW, hI, hIc⟩ := ind G hG _ W rfl
    refine ⟨I, hIW, hI, ?_⟩
    have hfa := f_anti ht0 h.le
    have hmf : m * f T ≤ #I := le_trans (mul_le_mul_of_nonneg_left hfa (by positivity)) hIc
    unfold f φ at hmf
    -- m * (log (T+8)/(T+8)/20) ≥ T/80
    have hlogT : log m / 2 ≤ log (T + 8) := by
      have : log (Real.sqrt m) = log m / 2 := by
        rw [Real.log_sqrt (by positivity)]
      rw [← this]
      exact Real.log_le_log (by positivity) (by linarith)
    have key : T / 80 ≤ m * (log (T + 8) / (T + 8) / 20) := by
      rw [div_le_iff₀ (by norm_num)]
      have e : m * (log (T + 8) / (T + 8) / 20) * 80 = 4 * m * log (T + 8) / (T + 8) := by
        field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      have : T * (T + 8) ≤ 2 * T ^ 2 := by nlinarith
      nlinarith
    linarith

lemma alpha_all (hG : G.CliqueFree 3) (W : Finset V) (hW : 1 ≤ #W) :
    ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧ Real.sqrt #W / 80 ≤ #I := by
  rcases le_or_gt 64 #W with h | h
  · obtain ⟨I, hIW, hI, hc⟩ := alpha_big G hG W h
    refine ⟨I, hIW, hI, le_trans ?_ hc⟩
    have hm : (64 : ℝ) ≤ #W := by exact_mod_cast h
    have := log_ge_two (y := (#W : ℝ)) (by linarith)
    gcongr
    nlinarith
  · obtain ⟨v, hv⟩ : W.Nonempty := by rw [← card_pos]; omega
    refine ⟨{v}, by simpa using hv, by simp, ?_⟩
    simp only [card_singleton, Nat.cast_one]
    have : Real.sqrt #W ≤ 8 := by
      rw [show (8 : ℝ) = Real.sqrt 64 by
        rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast h.le)
    linarith

/-- `W` can be properly coloured with `r` colours. -/
def Cov (W : Finset V) (r : ℕ) : Prop :=
  ∃ col : V → ℕ, (∀ v ∈ W, col v < r) ∧ ∀ v ∈ W, ∀ w ∈ W, G.Adj v w → col v ≠ col w

lemma Cov.mono {W : Finset V} {r r' : ℕ} (h : Cov G W r) (hr : r ≤ r') : Cov G W r' := by
  obtain ⟨col, h1, h2⟩ := h
  exact ⟨col, fun v hv => lt_of_lt_of_le (h1 v hv) hr, h2⟩

lemma Cov.add_indep {W I : Finset V} {r : ℕ} (h : Cov G (W \ I) r)
    (hI : G.IsIndepSet (I : Set V)) : Cov G W (r + 1) := by
  classical
  obtain ⟨col, h1, h2⟩ := h
  refine ⟨fun v => if v ∈ I then r else col v, fun v hv => ?_, fun v hv w hw hvw => ?_⟩
  · by_cases hvI : v ∈ I
    · simp [hvI]
    · simp only [hvI, if_false]
      exact Nat.lt_succ_of_lt (h1 v (mem_sdiff.2 ⟨hv, hvI⟩))
  · by_cases hvI : v ∈ I <;> by_cases hwI : w ∈ I
    · exact absurd hvw (hI hvI hwI (G.ne_of_adj hvw))
    · simp only [hvI, hwI, if_true, if_false]
      exact (h1 w (mem_sdiff.2 ⟨hw, hwI⟩)).ne'
    · simp only [hvI, hwI, if_true, if_false]
      exact (h1 v (mem_sdiff.2 ⟨hv, hvI⟩)).ne
    · simp only [hvI, hwI, if_false]
      exact h2 v (mem_sdiff.2 ⟨hv, hvI⟩) w (mem_sdiff.2 ⟨hw, hwI⟩) hvw

lemma phase (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : 0 < δ) (R : ℕ)
    (hsmall : ∀ W : Finset V, #W < T → Cov G W R)
    (hbig : ∀ W : Finset V, T ≤ #W → ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧
      2 * δ * Real.sqrt #W ≤ #I) :
    ∀ k, ∀ W : Finset V, #W = k → Cov G W (⌊Real.sqrt #W / δ⌋₊ + 1 + R) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro W hWk
  rcases lt_or_ge #W T with h | h
  · exact (hsmall W h).mono G (by omega)
  obtain ⟨I, hIW, hI, hIc⟩ := hbig W h
  have hcard : #(W \ I) = #W - #I := card_sdiff_of_subset hIW
  have hIle : #I ≤ #W := card_le_card hIW
  have hm0 : (0 : ℝ) < #W := by exact_mod_cast (show 0 < #W by omega)
  have hsm : 0 < Real.sqrt #W := Real.sqrt_pos.2 hm0
  have hIpos : 0 < #I := by
    have : (0 : ℝ) < #I := lt_of_lt_of_le (by positivity) hIc
    exact_mod_cast this
  have hlt : #(W \ I) < k := by omega
  have hrec := ih _ hlt (W \ I) rfl
  -- sqrt decreases by at least δ
  have hcR : ((#(W \ I) : ℕ) : ℝ) = #W - #I := by
    rw [hcard, Nat.cast_sub hIle]
  have hdec : Real.sqrt #(W \ I) ≤ Real.sqrt #W - δ := by
    set a := Real.sqrt #W
    set b := Real.sqrt #(W \ I)
    have ha2 : a ^ 2 = #W := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = #(W \ I) := Real.sq_sqrt (by positivity)
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hba : b ≤ a := Real.sqrt_le_sqrt (by exact_mod_cast card_le_card sdiff_subset)
    -- a^2 - b^2 = #I ≥ 2 δ a, and a + b ≤ 2a
    have h1 : a ^ 2 - b ^ 2 = #I := by rw [ha2, hb2, hcR]; ring
    have h2 : (a - b) * (2 * a) ≥ 2 * δ * a := by nlinarith
    have h3 : a - b ≥ δ := by
      have h5 : 2 * a * δ ≤ 2 * a * (a - b) := by nlinarith
      exact le_of_mul_le_mul_left h5 (by linarith)
    linarith
  have hfl : ⌊Real.sqrt #(W \ I) / δ⌋₊ + 1 ≤ ⌊Real.sqrt #W / δ⌋₊ := by
    have hge : 1 ≤ Real.sqrt #W / δ := by
      rw [le_div_iff₀ hδ, one_mul]
      have : 0 ≤ Real.sqrt #(W \ I) := Real.sqrt_nonneg _
      linarith
    have : Real.sqrt #(W \ I) / δ ≤ Real.sqrt #W / δ - 1 := by
      rw [div_sub_one hδ.ne']
      exact div_le_div_of_nonneg_right hdec hδ.le
    have h4 := Nat.floor_le_floor this
    rw [Nat.floor_sub_one] at h4
    have : 1 ≤ ⌊Real.sqrt #W / δ⌋₊ := Nat.le_floor (by simpa using hge)
    omega
  have := hrec.add_indep G hI
  exact this.mono G (by omega)

end Graph2


lemma colorable_of_cov {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : Cov G (univ : Finset (Fin n)) r) : G.Colorable r := by
  obtain ⟨col, h1, h2⟩ := h
  exact ⟨SimpleGraph.Coloring.mk (fun v => (⟨col v, h1 v (mem_univ v)⟩ : Fin r))
    (fun {v w} hvw heq => h2 v (mem_univ v) w (mem_univ w) hvw (by simpa using heq))⟩

lemma chi_bounds {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hk : G.chromaticNumber = k) :
    (k : ℝ) ≤ 160 * Real.sqrt n + 1 ∧
    (4096 ≤ n → (k : ℝ) ≤ 600 * (Real.sqrt n / Real.sqrt (log n))) := by
  have hkle : ∀ r, Cov G (univ : Finset (Fin n)) r → k ≤ r := by
    intro r hr
    have := (SimpleGraph.chromaticNumber_le_iff_colorable).2 (colorable_of_cov G hr)
    rw [hk] at this
    exact_mod_cast this
  have hcard : (#(univ : Finset (Fin n)) : ℝ) = n := by simp
  -- phase 1
  have P1 := phase G 1 le_rfl (1 / 160) (by norm_num) 0
    (fun W hW => ⟨fun _ => 0, fun v hv => by
      have : W = ∅ := card_eq_zero.1 (by omega)
      simp [this] at hv, fun v hv => by
      have : W = ∅ := card_eq_zero.1 (by omega)
      simp [this] at hv⟩)
    (fun W hW => by
      obtain ⟨I, hIW, hI, hc⟩ := alpha_all G hG W hW
      exact ⟨I, hIW, hI, by linarith⟩)
  have hP1 : ∀ W : Finset (Fin n), Cov G W (⌊160 * Real.sqrt #W⌋₊ + 1) := by
    intro W
    have := P1 _ W rfl
    simpa [div_eq_mul_inv, mul_comm] using this
  refine ⟨?_, fun hn => ?_⟩
  · have h1 := hkle _ (hP1 univ)
    simp only [card_univ, Fintype.card_fin] at h1
    have h2 : (k : ℝ) ≤ ((⌊160 * Real.sqrt n⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : (⌊160 * Real.sqrt n⌋₊ : ℝ) ≤ 160 * Real.sqrt n := Nat.floor_le (by positivity)
    push_cast at h2
    linarith
  -- phase 2
  set T2 := Nat.sqrt n with hT2
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  set a := Real.sqrt n with ha
  have ha2 : a ^ 2 = n := Real.sq_sqrt (by positivity)
  have ha64 : 64 ≤ a := by
    rw [ha, show (64 : ℝ) = Real.sqrt 4096 by
      rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hnR
  have hT2a : (T2 : ℝ) ≤ a := Real.nat_sqrt_le_real_sqrt
  have haT2 : a ≤ T2 + 1 := Real.real_sqrt_le_nat_sqrt_succ
  have hT2_64 : 64 ≤ T2 := by
    have : (63 : ℝ) ≤ T2 := by linarith
    have : (63 : ℕ) < T2 + 1 := by exact_mod_cast (show (63 : ℝ) < T2 + 1 by linarith)
    have h64 : 64 ≤ T2 := by
      by_contra hc; push Not at hc
      have : T2 * T2 ≤ 63 * 63 := Nat.mul_le_mul (by omega) (by omega)
      have := Nat.lt_succ_sqrt n
      rw [← hT2] at this
      have : n < 64 * 64 := by nlinarith
      omega
    exact h64
  have hT2R : (64 : ℝ) ≤ T2 := by exact_mod_cast hT2_64
  have hlogT2 : log n ≤ 4 * log T2 := by
    have h1 : a / 2 ≤ T2 := by linarith
    have h2 : (n : ℝ) ≤ (T2 : ℝ) ^ 4 := by
      have : (a / 2) ^ 4 ≤ (T2 : ℝ) ^ 4 := by
        apply pow_le_pow_left₀ (by linarith) h1
      have : (a / 2) ^ 4 = (a ^ 2) ^ 2 / 16 := by ring
      nlinarith
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlogT2pos : 0 < log (T2 : ℝ) := Real.log_pos (by linarith)
  set δ2 := Real.sqrt (log T2) / 160 with hδ2
  have hδ2pos : 0 < δ2 := by rw [hδ2]; have := Real.sqrt_pos.2 hlogT2pos; positivity
  have P2 := phase G T2 (by omega) δ2 hδ2pos (⌊160 * Real.sqrt T2⌋₊ + 1)
    (fun W hW => by
      refine (hP1 W).mono G ?_
      have : ⌊160 * Real.sqrt #W⌋₊ ≤ ⌊160 * Real.sqrt T2⌋₊ := by
        apply Nat.floor_le_floor
        have : ((#W : ℕ) : ℝ) ≤ T2 := by exact_mod_cast hW.le
        have := Real.sqrt_le_sqrt this
        linarith
      omega)
    (fun W hW => by
      obtain ⟨I, hIW, hI, hc⟩ := alpha_big G hG W (le_trans hT2_64 hW)
      refine ⟨I, hIW, hI, le_trans ?_ hc⟩
      · rw [hδ2, Real.sqrt_mul (by positivity)]
        have hWR : (T2 : ℝ) ≤ #W := by exact_mod_cast hW
        have : Real.sqrt (log T2) ≤ Real.sqrt (log #W) :=
          Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hWR)
        have h0 : 0 ≤ Real.sqrt (#W : ℝ) := Real.sqrt_nonneg _
        nlinarith)
  have hK := hkle _ (P2 _ univ rfl)
  rw [hcard] at hK
  have hKR : (k : ℝ) ≤ ⌊a / δ2⌋₊ + 1 + (⌊160 * Real.sqrt T2⌋₊ + 1) := by exact_mod_cast hK
  have f1 : (⌊a / δ2⌋₊ : ℝ) ≤ a / δ2 := Nat.floor_le (by positivity)
  have f2 : (⌊160 * Real.sqrt T2⌋₊ : ℝ) ≤ 160 * Real.sqrt T2 := Nat.floor_le (by positivity)
  set ℓ := Real.sqrt (log n) with hℓ
  have hlogn : 0 < log (n : ℝ) := Real.log_pos (by linarith)
  have hℓpos : 0 < ℓ := Real.sqrt_pos.2 hlogn
  have hℓ2 : ℓ ^ 2 = log n := Real.sq_sqrt hlogn.le
  have hlogle : log (n : ℝ) ≤ 2 * a := by
    have : log (n : ℝ) = 2 * log a := by
      rw [← ha2, Real.log_pow]; push_cast; ring
    rw [this]
    have := Real.log_le_sub_one_of_pos (show 0 < a by linarith)
    linarith
  -- term 1
  have t1 : a / δ2 ≤ 320 * (a / ℓ) := by
    have hs : ℓ / 2 ≤ Real.sqrt (log T2) := by
      rw [show ℓ / 2 = Real.sqrt (log n / 4) by
        rw [Real.sqrt_div' _ (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [hδ2, div_div_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.2 hlogT2pos)]
    have : 320 * (a / ℓ) * (ℓ / 2) = a * 160 := by field_simp; ring
    have h0 : 0 ≤ 320 * (a / ℓ) := by positivity
    nlinarith
  -- term 2
  have t2 : 160 * Real.sqrt T2 ≤ 240 * (a / ℓ) := by
    have hs1 : Real.sqrt T2 ≤ Real.sqrt a := Real.sqrt_le_sqrt hT2a
    have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
    have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
    -- (sqrt a * ℓ)^2 = a log n ≤ 2 a^2  so sqrt a * ℓ ≤ 1.5 a
    have hX : Real.sqrt a * ℓ ≤ 3 / 2 * a := by
      have hsq : (Real.sqrt a * ℓ) ^ 2 ≤ (3 / 2 * a) ^ 2 := by
        rw [mul_pow, hsa, hℓ2]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).1 hsq
    rw [mul_div_assoc', le_div_iff₀ hℓpos]
    have : 160 * Real.sqrt T2 * ℓ ≤ 160 * (Real.sqrt a * ℓ) := by nlinarith
    linarith
  have t3 : 2 ≤ 2 * (a / ℓ) := by
    have : ℓ ≤ a := by
      have : ℓ ^ 2 ≤ a ^ 2 := by rw [hℓ2, ha2]; nlinarith
      nlinarith
    rw [le_mul_iff_one_le_right (by norm_num), le_div_iff₀ hℓpos]; linarith
  have : (k : ℝ) ≤ 562 * (a / ℓ) := by linarith
  have h0 : 0 ≤ a / ℓ := by positivity
  linarith


open Filter in
theorem main : ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      c * (Real.log k / Real.log (Real.log k)) * k ^ 2 ≤ (Erdos1013.h3 k : ℝ) := by
  refine ⟨1 / 360000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 51201] with k hk
  have hne : {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k}.Nonempty := by
    obtain ⟨n, G, hω, hχ⟩ := SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq k (by omega)
    refine ⟨n, G, fun s hs => ?_, hχ⟩
    have := hs.isClique.card_le_cliqueNum
    rw [hs.card_eq, hω] at this
    omega
  obtain ⟨G, hG, hχ⟩ := Nat.sInf_mem hne
  classical
  obtain ⟨b1, b2⟩ := chi_bounds G hG hχ
  set n := sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k}
    with hn
  have hh : Erdos1013.h3 k = n := rfl
  rw [hh]
  have hkR : (51201 : ℝ) ≤ k := by exact_mod_cast hk
  have hsn : 320 ≤ Real.sqrt n := by linarith
  have hn2 : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (by positivity)).symm
  have hnR : (102400 : ℝ) ≤ n := by rw [hn2]; nlinarith
  have hn4096 : 4096 ≤ n := by exact_mod_cast (show (4096 : ℝ) ≤ n by linarith)
  have b2' := b2 hn4096
  have hlogn : 0 < log (n : ℝ) := Real.log_pos (by linarith)
  have hℓ := Real.sqrt_pos.2 hlogn
  have hk2 : (k : ℝ) ^ 2 * log n ≤ 360000 * n := by
    have h1 : (k : ℝ) * Real.sqrt (log n) ≤ 600 * Real.sqrt n := by
      rw [mul_div_assoc', le_div_iff₀ hℓ] at b2'; exact b2'
    have h2 := mul_self_le_mul_self (by positivity) h1
    have e1 : Real.sqrt (log n) * Real.sqrt (log n) = log n := Real.mul_self_sqrt hlogn.le
    have e2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
    nlinarith
  have hkn : (k : ℝ) ≤ n := by nlinarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hlogk : log (k : ℝ) ≤ log n := Real.log_le_log hk0 hkn
  have hlk : 2.75 ≤ log (k : ℝ) := by
    have := log_ge_two (y := (k : ℝ)) (by linarith)
    have h16 : log (16 : ℝ) ≤ log k := Real.log_le_log (by norm_num) (by linarith)
    have : log (16 : ℝ) = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hllk : 1 ≤ log (log (k : ℝ)) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hq : log (k : ℝ) / log (log k) ≤ log k := div_le_self (by linarith) hllk
  have : 1 / 360000 * (log (k : ℝ) / log (log k)) * k ^ 2 ≤ 1 / 360000 * log n * k ^ 2 := by
    have : log (k : ℝ) / log (log k) ≤ log n := hq.trans hlogk
    have : (0 : ℝ) ≤ k ^ 2 := by positivity
    nlinarith
  linarith

end E1013

theorem OMA.solution : type_of% @Erdos1013.erdos_1013.variants.graver_yackel :=
  E1013.main
