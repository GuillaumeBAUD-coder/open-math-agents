import FormalConjectures.ErdosProblems.«802»

-- Problem: Erdős Problem 802 — r eq three (Ajtai–Komlós–Szemerédi for triangle-free graphs)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/802.lean (declaration Erdos802.erdos_802.variants.r_eq_three)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Proof: Shearer-style induction (delete a vertex and its neighbourhood) with the convex
-- potential f(d) = log(d+8)/(20(d+8)); the vertex is chosen by averaging and Cauchy-Schwarz.

open Real

namespace E802

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

open scoped Classical in
theorem main : ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree 3 →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  refine ⟨1 / 180, by norm_num, fun n G hG => ?_⟩
  obtain ⟨I, -, hI, hIc⟩ := ind G hG _ (univ : Finset (Fin n)) rfl
  have hα : (#I : ℝ) ≤ G.indepNum := by exact_mod_cast hI.card_le_indepNum
  set t : ℝ := ((G.averageDegree : ℚ) : ℝ) with ht
  have hdeg : ∀ x, deg G univ x = G.degree x := by
    intro x
    unfold deg
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have he2 : (e2 G (univ : Finset (Fin n)) : ℝ) = ∑ x, (G.degree x : ℝ) := by
    rw [e2_eq_sum]; push_cast; simp [hdeg]
  have hcard : (#(univ : Finset (Fin n)) : ℝ) = n := by simp
  have hdt : (e2 G (univ : Finset (Fin n)) : ℝ) / #(univ : Finset (Fin n)) = t := by
    rw [he2, hcard, ht, SimpleGraph.averageDegree]
    push_cast
    simp
  rw [hdt, hcard] at hIc
  have ht0 : 0 ≤ t := by
    rw [ht, SimpleGraph.averageDegree]
    have : (0 : ℚ) ≤ (∑ v, (G.degree v : ℚ)) / (Fintype.card (Fin n) : ℚ) := by positivity
    exact_mod_cast this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hf0 := f_nonneg ht0
  rcases le_or_gt t 1 with h1 | h1
  · have : log t / t ≤ 0 := by
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · rw [← h0]; simp
      · exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ht0 h1) ht0
    have : 1 / 180 * (log t / t) * n ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg this hn0
      nlinarith
    have : (0 : ℝ) ≤ G.indepNum := Nat.cast_nonneg _
    linarith
  · have htpos : 0 < t := by linarith
    have hlog : 0 ≤ log t := Real.log_nonneg h1.le
    have hlog8 : log t ≤ log (t + 8) := Real.log_le_log htpos (by linarith)
    have key : 1 / 180 * (log t / t) ≤ f t := by
      unfold f φ
      have h9 : log t / t ≤ (9 * log (t + 8)) / (t + 8) := by
        rw [div_le_div_iff₀ htpos (by linarith)]
        have a1 : log t * (t + 8) ≤ log (t + 8) * (t + 8) :=
          mul_le_mul_of_nonneg_right hlog8 (by linarith)
        have a2 : log (t + 8) * (t + 8) ≤ log (t + 8) * (9 * t) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      have e : log (t + 8) / (t + 8) / 20 = (9 * log (t + 8)) / (t + 8) / 180 := by ring
      rw [e]
      linarith
    have := mul_le_mul_of_nonneg_right key hn0
    linarith

end E802

theorem OMA.solution : type_of% @Erdos802.erdos_802.variants.r_eq_three :=
  E802.main
