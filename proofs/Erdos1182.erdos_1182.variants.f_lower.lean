import FormalConjectures.ErdosProblems.«1182»
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Set.Card

/-!
# Erdős Problem 1182, lower bound on `f`

Formalization work towards the BEFRS80 lower bound for `f`, via Shearer's
independence-number theorem for triangle-free graphs and an explicit star of cliques
Ramsey construction.

Status: the analytic weight function `g`, its convexity and monotonicity, Shearer's
differential inequality, the finite averaging lemma, and Shearer's theorem itself
(`shearer_finset`, by strong induction on the finite vertex set using the per-vertex
degree identity `sum_degIn_delNbr`) are proved below, together with the resulting
independence-number bound `exists_indep_large`.

The remaining work is the graph-theoretic construction: the explicit star of cliques on
`Fin n`, its edge count, and the two `graphRamsey` bounds that give triangle-goodness.
-/

-- Problem: Erdős Problem 1182 — f lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1182.lean:245 (declaration Erdos1182.erdos_1182.variants.f_lower)
-- Credit: @Masterlincs (the owner of the agent is credited as the solver)

open Filter Asymptotics

namespace Erdos1182F

/-- The smooth weight function used in Shearer's argument. -/
noncomputable def g (x : ℝ) : ℝ := Real.log (x + 8) / (10 * (x + 8))

/-- The derivative of `g`. -/
noncomputable def g' (x : ℝ) : ℝ := (1 - Real.log (x + 8)) / (10 * (x + 8) ^ 2)

/-- The second derivative of `g`. -/
noncomputable def g'' (x : ℝ) : ℝ := (2 * Real.log (x + 8) - 3) / (10 * (x + 8) ^ 3)

lemma hasDerivAt_g (x : ℝ) (hx : 0 < x + 8) : HasDerivAt g (g' x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y + 8) (1 : ℝ) x := by
    simpa using (hasDerivAt_id x).add_const (8 : ℝ)
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y + 8)) ((x + 8)⁻¹) x := by
    have := h1.log (ne_of_gt hx)
    simpa [div_eq_inv_mul] using this
  have hden : HasDerivAt (fun y : ℝ => 10 * (y + 8)) (10 : ℝ) x := by
    simpa using h1.const_mul (10 : ℝ)
  have hden0 : (10 * (x + 8)) ≠ 0 := by positivity
  have hd := hlog.div hden hden0
  have hfun : g = ((fun y : ℝ => Real.log (y + 8)) / fun y : ℝ => 10 * (y + 8)) := by
    funext y; unfold g; simp [Pi.div_apply]
  rw [hfun]
  exact hd.congr_deriv (by unfold g'; field_simp; try ring)

lemma hasDerivAt_g' (x : ℝ) (hx : 0 < x + 8) : HasDerivAt g' (g'' x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y + 8) (1 : ℝ) x := by
    simpa using (hasDerivAt_id x).add_const (8 : ℝ)
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y + 8)) ((x + 8)⁻¹) x := by
    have := h1.log (ne_of_gt hx)
    simpa [div_eq_inv_mul] using this
  have hnum := hlog.const_sub (1 : ℝ)
  have hden : HasDerivAt (fun y : ℝ => 10 * (y + 8) ^ 2)
      (10 * (2 * (x + 8) ^ (2 - 1) * 1)) x := by
    have := (h1.pow 2).const_mul (10 : ℝ)
    simpa using this
  have hden0 : (10 * (x + 8) ^ 2) ≠ 0 := by positivity
  have hd := hnum.div hden hden0
  have hfun : g' = ((fun y : ℝ => 1 - Real.log (y + 8)) / fun y : ℝ => 10 * (y + 8) ^ 2) := by
    funext y; unfold g'; simp [Pi.div_apply]
  rw [hfun]
  exact hd.congr_deriv (by unfold g''; field_simp; try ring)

lemma deriv_g (x : ℝ) (hx : 0 < x + 8) : deriv g x = g' x := (hasDerivAt_g x hx).deriv

lemma log_eight_gt_three_halves : (3/2 : ℝ) < Real.log 8 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    have : (8:ℝ) = 2 ^ 3 := by norm_num
    rw [this, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  rw [h]
  linarith

lemma log_eight_gt_one : (1 : ℝ) < Real.log 8 := log_eight_gt_three_halves.trans' (by norm_num)

lemma log_le_half {u : ℝ} (hu : 4 ≤ u) : Real.log u ≤ u / 2 := by
  have h2 : Real.log (u/2) + Real.log 2 = Real.log u := by
    rw [← Real.log_mul (by linarith) (by norm_num)]
    ring_nf
  rw [← h2]
  have h1 : Real.log (u/2) ≤ u/2 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  linarith

lemma g''_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g'' x := by
  unfold g''
  apply div_nonneg
  · have h8 : Real.log 8 ≤ Real.log (x + 8) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [log_eight_gt_three_halves]
  · positivity

lemma g'_nonpos {x : ℝ} (hx : 0 ≤ x) : g' x ≤ 0 := by
  unfold g'
  apply div_nonpos_of_nonpos_of_nonneg
  · have h8 : Real.log 8 ≤ Real.log (x + 8) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [log_eight_gt_one]
  · positivity

lemma differentiableOn_g : DifferentiableOn ℝ g (Set.Ici (0 : ℝ)) := by
  intro x hx
  have hx0 : (0:ℝ) ≤ x := Set.mem_Ici.mp hx
  exact (hasDerivAt_g x (by linarith)).differentiableAt.differentiableWithinAt

lemma continuousOn_g : ContinuousOn g (Set.Ici (0 : ℝ)) := differentiableOn_g.continuousOn

lemma convexOn_g : ConvexOn ℝ (Set.Ici (0 : ℝ)) g := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Ici (0:ℝ)) (f' := g') (f'' := g'')
    (convex_Ici (0:ℝ)) continuousOn_g ?_ ?_ ?_
  · intro x hx
    have hx0 : (0:ℝ) < x := by rwa [interior_Ici] at hx
    exact (hasDerivAt_g x (by linarith)).hasDerivWithinAt
  · intro x hx
    have hx0 : (0:ℝ) < x := by rwa [interior_Ici] at hx
    exact (hasDerivAt_g' x (by linarith)).hasDerivWithinAt
  · intro x hx
    have hx0 : (0:ℝ) < x := by rwa [interior_Ici] at hx
    exact g''_nonneg (le_of_lt hx0)

lemma antitoneOn_g : AntitoneOn g (Set.Ici (0 : ℝ)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ)) continuousOn_g ?_ ?_
  · intro x hx
    have hx0 : (0:ℝ) < x := by rwa [interior_Ici] at hx
    exact (hasDerivAt_g x (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : (0:ℝ) < x := by rwa [interior_Ici] at hx
    rw [deriv_g x (by linarith)]
    exact g'_nonpos (le_of_lt hx0)

lemma g_zero_le_one : g 0 ≤ 1 := by
  unfold g
  simp only [zero_add]
  rw [div_le_one (by norm_num)]
  have : Real.log 8 ≤ 8 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  linarith

lemma g_lower {x : ℝ} (hx : 8 ≤ x) : Real.log x / (20 * x) ≤ g x := by
  unfold g
  have hpx : (0:ℝ) < x := by linarith
  have h8 : (0:ℝ) < x + 8 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hlogmono : Real.log x ≤ Real.log (x + 8) :=
    Real.log_le_log hpx (by linarith)
  have hle8 : Real.log 8 ≤ Real.log (x + 8) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogpos : 0 ≤ Real.log (x + 8) := by linarith [log_eight_gt_one, hle8]
  calc Real.log x * (10 * (x + 8)) ≤ Real.log (x + 8) * (10 * (x + 8)) :=
        mul_le_mul_of_nonneg_right hlogmono (by positivity)
    _ ≤ Real.log (x + 8) * (20 * x) :=
        mul_le_mul_of_nonneg_left (by linarith) hlogpos

/-- Shearer's differential inequality. -/
lemma g_ineq {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) * g x + (x ^ 2 - x) * g' x ≤ 1 := by
  set u : ℝ := x + 8 with hu_def
  have hu : (8:ℝ) ≤ u := by rw [hu_def]; linarith
  have hlog : Real.log u ≤ u / 2 := log_le_half (by linarith)
  have hkey : (x + 1) * g x + (x ^ 2 - x) * g' x
      = ((10 * u - 72) * Real.log u + (u ^ 2 - 17 * u + 72)) / (10 * u ^ 2) := by
    rw [hu_def]
    unfold g g'
    field_simp
    ring
  rw [hkey]
  rw [div_le_one (by positivity)]
  have hmul : (10 * u - 72) * Real.log u ≤ (10 * u - 72) * (u / 2) :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  nlinarith [hmul]

/-- Tangent-line inequality: `g` lies above its tangent at every point of `[0,∞)`. -/
lemma convex_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    g x + (y - x) * g' x ≤ g y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hs := convexOn_g.deriv_le_slope (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hlt
      (hasDerivAt_g x (by linarith)).differentiableAt
    rw [deriv_g x (by linarith), slope_def_field] at hs
    have hpos : (0:ℝ) < y - x := by linarith
    have hh := (le_div_iff₀ hpos).mp hs
    nlinarith
  · subst heq; ring_nf; linarith
  · have hs := convexOn_g.slope_le_deriv (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) hgt
      (hasDerivAt_g x (by linarith)).differentiableAt
    rw [deriv_g x (by linarith), slope_def_field] at hs
    have hpos : (0:ℝ) < x - y := by linarith
    have hh := (div_le_iff₀ hpos).mp hs
    nlinarith

section GraphCore

open Classical

/-- Sum of degrees equals twice the number of edges, cast to `ℝ`. -/
lemma deg_sum_real {V : Type*} [Fintype V] (H : SimpleGraph V) :
    (∑ v, (H.degree v : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by
  classical
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (G := H)
  rw [← Nat.cast_sum, h]
  push_cast
  ring

/-- Some value of `f` is at least the average of `f`. -/
lemma exists_ge_avg {ι : Type*} [Fintype ι] (f : ι → ℝ) (h : 0 < Fintype.card ι) :
    ∃ i, (∑ i, f i) / (Fintype.card ι : ℝ) ≤ f i := by
  classical
  by_contra hc
  push Not at hc
  have hlt : (∑ i, f i) < ∑ _i : ι, (∑ j, f j) / (Fintype.card ι : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _; exact le_of_lt (hc i)
    · obtain ⟨i⟩ := Fintype.card_pos_iff.mp h
      exact ⟨i, Finset.mem_univ i, hc i⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have heq : (Fintype.card ι : ℝ) * ((∑ j, f j) / (Fintype.card ι : ℝ)) = ∑ j, f j := by
    field_simp
  linarith [heq]

end GraphCore

/- ## Shearer's theorem for triangle-free graphs -/

section Shearer

open Classical

variable {V : Type*} [DecidableEq V]

/-- The number of neighbours of `v` inside the finite vertex set `S`. -/
def degIn (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (H.Adj v)).card

/-- `S` with `v` and all neighbours of `v` removed. -/
def delNbr (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (v : V) : Finset V :=
  (S.erase v).filter (fun w => ¬ H.Adj v w)

/-- Sum of the in-set degrees, as a real number. -/
noncomputable def degSum (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, (degIn H S x : ℝ)

/-- Sum of the in-set degrees of `delNbr H S v`, as a real number. -/
noncomputable def subDegSum (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (v : V) : ℝ :=
  ∑ w ∈ delNbr H S v, (degIn H (delNbr H S v) w : ℝ)

/-- Cardinality of `delNbr H S v`, as a real number. -/
noncomputable def subCard (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (v : V) : ℝ :=
  ((delNbr H S v).card : ℝ)

variable {H : SimpleGraph V} [DecidableRel H.Adj]

lemma delNbr_subset {S : Finset V} {v : V} : delNbr H S v ⊆ S := by
  intro x hx
  exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1

lemma delNbr_subset_erase {S : Finset V} {v : V} : delNbr H S v ⊆ S.erase v :=
  Finset.filter_subset _ _

lemma not_adj_of_mem_delNbr {S : Finset V} {v w : V} (hw : w ∈ delNbr H S v) :
    ¬ H.Adj v w :=
  (Finset.mem_filter.mp hw).2

lemma ne_of_mem_delNbr {S : Finset V} {v w : V} (hw : w ∈ delNbr H S v) : w ≠ v :=
  (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).1

lemma mem_delNbr {S : Finset V} {v w : V} :
    w ∈ delNbr H S v ↔ w ∈ S ∧ w ≠ v ∧ ¬ H.Adj v w := by
  simp [delNbr, and_assoc, and_left_comm, and_comm]

lemma delNbr_ssubset {S : Finset V} {v : V} (hv : v ∈ S) : delNbr H S v ⊂ S := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨delNbr_subset, ?_⟩
  intro h
  have : v ∈ delNbr H S v := by rw [h]; exact hv
  exact ne_of_mem_delNbr this rfl

lemma disjoint_filter_delNbr (S : Finset V) (v : V) :
    Disjoint (S.filter (H.Adj v)) (delNbr H S v) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact (not_adj_of_mem_delNbr hx') (Finset.mem_filter.mp hx).2

lemma filter_union_delNbr (S : Finset V) (v : V) :
    S.filter (H.Adj v) ∪ delNbr H S v = S.erase v := by
  ext x
  simp only [delNbr, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro (⟨hxS, hadj⟩ | ⟨⟨hxv, hxS⟩, -⟩)
    · exact ⟨hadj.ne.symm, hxS⟩
    · exact ⟨hxv, hxS⟩
  · rintro ⟨hxv, hxS⟩
    by_cases hadj : H.Adj v x
    · exact Or.inl ⟨hxS, hadj⟩
    · exact Or.inr ⟨⟨hxv, hxS⟩, hadj⟩

lemma sum_partition (S : Finset V) {v : V} (hv : v ∈ S) (f : V → ℕ) :
    ∑ x ∈ S, f x = f v + ∑ u ∈ S.filter (H.Adj v), f u + ∑ w ∈ delNbr H S v, f w := by
  calc ∑ x ∈ S, f x = ∑ x ∈ insert v (S.erase v), f x := by rw [Finset.insert_erase hv]
    _ = f v + ∑ x ∈ S.erase v, f x := Finset.sum_insert (Finset.notMem_erase v S)
    _ = f v + ∑ x ∈ S.filter (H.Adj v) ∪ delNbr H S v, f x := by rw [filter_union_delNbr]
    _ = f v + (∑ u ∈ S.filter (H.Adj v), f u + ∑ w ∈ delNbr H S v, f w) :=
        by rw [Finset.sum_union (disjoint_filter_delNbr S v)]
    _ = f v + ∑ u ∈ S.filter (H.Adj v), f u + ∑ w ∈ delNbr H S v, f w := by ring

lemma degSum_nonneg (S : Finset V) : 0 ≤ degSum H S := by
  unfold degSum
  positivity

lemma subDegSum_nonneg (S : Finset V) (v : V) : 0 ≤ subDegSum H S v := by
  unfold subDegSum
  positivity

lemma subCard_nonneg (S : Finset V) (v : V) : 0 ≤ subCard H S v := by
  unfold subCard
  positivity

lemma subCard_mul_div (S : Finset V) (v : V) :
    subCard H S v * (subDegSum H S v / subCard H S v) = subDegSum H S v := by
  show ((delNbr H S v).card : ℝ) *
      ((∑ w ∈ delNbr H S v, (degIn H (delNbr H S v) w : ℝ)) / ((delNbr H S v).card : ℝ))
    = ∑ w ∈ delNbr H S v, (degIn H (delNbr H S v) w : ℝ)
  rcases eq_or_ne (((delNbr H S v).card : ℝ)) 0 with h0 | h0
  · have hc : (delNbr H S v).card = 0 := by exact_mod_cast h0
    have hempty : delNbr H S v = ∅ := Finset.card_eq_zero.mp hc
    rw [hempty]
    simp
  · field_simp [h0]

/-- The per-vertex degree identity behind Shearer's induction. -/
lemma sum_degIn_delNbr (hH : H.CliqueFree 3) {S : Finset V} {v : V} (hv : v ∈ S) :
    (∑ w ∈ delNbr H S v, degIn H (delNbr H S v) w)
      + 2 * (∑ u ∈ S.filter (H.Adj v), degIn H S u) = ∑ x ∈ S, degIn H S x := by
  classical
  have hNind : H.IsIndepSet ((S.filter (H.Adj v) : Finset V) : Set V) := by
    intro x hx y hy hxy hAdj
    have hx' : x ∈ S ∧ H.Adj v x := by
      simpa only [Finset.mem_coe, Finset.mem_filter] using hx
    have hy' : y ∈ S ∧ H.Adj v y := by
      simpa only [Finset.mem_coe, Finset.mem_filter] using hy
    exact (SimpleGraph.isIndepSet_neighborSet_of_triangleFree (G := H) hH v)
      (by simpa using hx'.2) (by simpa using hy'.2) hxy hAdj
  have hdeg_u : ∀ u ∈ S.filter (H.Adj v),
      degIn H S u = 1 + ((delNbr H S v).filter (H.Adj u)).card := by
    intro u hu
    obtain ⟨huS, hvu⟩ := Finset.mem_filter.mp hu
    have hset : S.filter (H.Adj u) = insert v ((delNbr H S v).filter (H.Adj u)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxS, hxu⟩ := Finset.mem_filter.mp hx
        by_cases hxv : x = v
        · exact Finset.mem_insert.mpr (Or.inl hxv)
        · have hnvx : ¬ H.Adj v x := by
            intro hvx
            have hxN : x ∈ S.filter (H.Adj v) := Finset.mem_filter.mpr ⟨hxS, hvx⟩
            exact (hNind hxN hu (by intro h; exact hxu.ne h.symm) : ¬ H.Adj x u) hxu.symm
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxS⟩, hnvx⟩, hxu⟩))
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact Finset.mem_filter.mpr ⟨hv, hvu.symm⟩
        · exact Finset.mem_filter.mpr ⟨delNbr_subset (Finset.mem_filter.mp hx').1,
            (Finset.mem_filter.mp hx').2⟩
    have hvnot : v ∉ (delNbr H S v).filter (H.Adj u) := by
      intro h
      exact ne_of_mem_delNbr (Finset.mem_filter.mp h).1 rfl
    rw [degIn, hset, Finset.card_insert_of_notMem hvnot]
    omega
  have hdeg_w : ∀ w ∈ delNbr H S v,
      degIn H S w = degIn H (delNbr H S v) w + ((S.filter (H.Adj v)).filter (H.Adj w)).card := by
    intro w hw
    obtain ⟨hwS, hwv, hnot⟩ := mem_delNbr.mp hw
    have hset : S.filter (H.Adj w)
        = ((delNbr H S v).filter (H.Adj w)) ∪ ((S.filter (H.Adj v)).filter (H.Adj w)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxS, hxw⟩ := Finset.mem_filter.mp hx
        by_cases hxv : x = v
        · subst hxv
          exact absurd hxw.symm hnot
        · by_cases hvx : H.Adj v x
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨hxS, hvx⟩, hxw⟩))
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxS⟩, hvx⟩, hxw⟩))
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_filter.mpr ⟨delNbr_subset (Finset.mem_filter.mp hx).1,
            (Finset.mem_filter.mp hx).2⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
            (Finset.mem_filter.mp hx).2⟩
    have hdisj : Disjoint ((delNbr H S v).filter (H.Adj w)) ((S.filter (H.Adj v)).filter (H.Adj w)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hx').1).2
    rw [degIn, degIn, hset, Finset.card_union_of_disjoint hdisj]
  have hsum_u : ∑ u ∈ S.filter (H.Adj v), degIn H S u
      = (S.filter (H.Adj v)).card
        + ∑ u ∈ S.filter (H.Adj v), ((delNbr H S v).filter (H.Adj u)).card := by
    calc ∑ u ∈ S.filter (H.Adj v), degIn H S u
        = ∑ u ∈ S.filter (H.Adj v),
            (1 + ((delNbr H S v).filter (H.Adj u)).card) := Finset.sum_congr rfl hdeg_u
      _ = (∑ _u ∈ S.filter (H.Adj v), (1 : ℕ))
            + ∑ u ∈ S.filter (H.Adj v), ((delNbr H S v).filter (H.Adj u)).card :=
          Finset.sum_add_distrib
      _ = (S.filter (H.Adj v)).card
            + ∑ u ∈ S.filter (H.Adj v), ((delNbr H S v).filter (H.Adj u)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          simp
  have hsum_w : ∑ w ∈ delNbr H S v, degIn H S w
      = (∑ w ∈ delNbr H S v, degIn H (delNbr H S v) w)
        + ∑ w ∈ delNbr H S v, ((S.filter (H.Adj v)).filter (H.Adj w)).card := by
    calc ∑ w ∈ delNbr H S v, degIn H S w
        = ∑ w ∈ delNbr H S v,
            (degIn H (delNbr H S v) w + ((S.filter (H.Adj v)).filter (H.Adj w)).card) :=
          Finset.sum_congr rfl hdeg_w
      _ = (∑ w ∈ delNbr H S v, degIn H (delNbr H S v) w)
            + ∑ w ∈ delNbr H S v, ((S.filter (H.Adj v)).filter (H.Adj w)).card :=
          Finset.sum_add_distrib
  have hswap : ∑ w ∈ delNbr H S v, ((S.filter (H.Adj v)).filter (H.Adj w)).card
      = ∑ u ∈ S.filter (H.Adj v), ((delNbr H S v).filter (H.Adj u)).card := by
    have h1 : ∀ w, ((S.filter (H.Adj v)).filter (H.Adj w)).card
        = ∑ u ∈ S.filter (H.Adj v), if H.Adj w u then 1 else 0 := by
      intro w
      rw [Finset.card_filter]
    have h2 : ∀ u, ((delNbr H S v).filter (H.Adj u)).card
        = ∑ w ∈ delNbr H S v, if H.Adj u w then 1 else 0 := by
      intro u
      rw [Finset.card_filter]
    calc ∑ w ∈ delNbr H S v, ((S.filter (H.Adj v)).filter (H.Adj w)).card
        = ∑ w ∈ delNbr H S v,
            ∑ u ∈ S.filter (H.Adj v), if H.Adj w u then 1 else 0 := by simp_rw [h1]
      _ = ∑ u ∈ S.filter (H.Adj v),
            ∑ w ∈ delNbr H S v, if H.Adj w u then 1 else 0 := Finset.sum_comm
      _ = ∑ u ∈ S.filter (H.Adj v),
            ∑ w ∈ delNbr H S v, if H.Adj u w then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro w _
          by_cases h : H.Adj w u
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun h' => h h'.symm)]
      _ = ∑ u ∈ S.filter (H.Adj v), ((delNbr H S v).filter (H.Adj u)).card := by simp_rw [h2]
  have hpart := sum_partition (H := H) S hv (fun x => degIn H S x)
  rw [hpart, hsum_u, hsum_w, hswap]
  have : degIn H S v = (S.filter (H.Adj v)).card := rfl
  rw [this]
  omega

/-- The summed form of the per-vertex degree identity. -/
lemma sum_subDegSum (hH : H.CliqueFree 3) (S : Finset V) :
    ∑ v ∈ S, subDegSum H S v
      = (S.card : ℝ) * degSum H S - 2 * ∑ x ∈ S, (degIn H S x : ℝ) ^ 2 := by
  classical
  have hpt : ∀ v ∈ S, subDegSum H S v + 2 * (∑ u ∈ S.filter (H.Adj v), (degIn H S u : ℝ))
      = degSum H S := by
    intro v hv
    have h := sum_degIn_delNbr (H := H) hH hv
    have h' : ((∑ w ∈ delNbr H S v, degIn H (delNbr H S v) w : ℕ) : ℝ)
        + 2 * ((∑ u ∈ S.filter (H.Adj v), degIn H S u : ℕ) : ℝ)
        = ((∑ x ∈ S, degIn H S x : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [subDegSum, degSum] using h'
  have h1 : ∑ v ∈ S, (subDegSum H S v
      + 2 * (∑ u ∈ S.filter (H.Adj v), (degIn H S u : ℝ)))
      = ∑ _v ∈ S, degSum H S := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have h2 : ∑ v ∈ S, (∑ u ∈ S.filter (H.Adj v), (degIn H S u : ℝ))
      = ∑ x ∈ S, (degIn H S x : ℝ) ^ 2 := by
    have hstep : ∀ v : V, (∑ u ∈ S.filter (H.Adj v), (degIn H S u : ℝ))
        = ∑ u ∈ S, if H.Adj v u then (degIn H S u : ℝ) else 0 := by
      intro v
      rw [Finset.sum_filter]
    calc ∑ v ∈ S, (∑ u ∈ S.filter (H.Adj v), (degIn H S u : ℝ))
        = ∑ v ∈ S, ∑ u ∈ S, if H.Adj v u then (degIn H S u : ℝ) else 0 := by simp_rw [hstep]
      _ = ∑ u ∈ S, ∑ v ∈ S, if H.Adj v u then (degIn H S u : ℝ) else 0 := Finset.sum_comm
      _ = ∑ u ∈ S, (∑ v ∈ S, if H.Adj v u then (degIn H S u : ℝ) else 0) := rfl
      _ = ∑ u ∈ S, (degIn H S u : ℝ) * (degIn H S u : ℝ) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hcard : (S.filter (fun v => H.Adj v u)).card = degIn H S u := by
            rw [degIn]
            congr 1
            ext v
            simp [SimpleGraph.adj_comm]
          rw [hcard]
      _ = ∑ x ∈ S, (degIn H S x : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sq]
  rw [h2] at h1
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  linarith

/-- The cardinality sum: the total of `delNbr` sizes. -/
lemma sum_subCard {S : Finset V} (hne : S.Nonempty) :
    ∑ v ∈ S, subCard H S v = (S.card : ℝ) * ((S.card : ℝ) - 1) - degSum H S := by
  have hkey : ∀ v ∈ S, (delNbr H S v).card + degIn H S v = S.card - 1 := by
    intro v hv
    have hdisj := disjoint_filter_delNbr (H := H) S v
    have hunion := filter_union_delNbr (H := H) S v
    have h1 : (S.filter (H.Adj v)).card + (delNbr H S v).card = (S.erase v).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [Finset.card_erase_of_mem hv] at h1
    rw [degIn]
    omega
  have hpt : ∀ v ∈ S, subCard H S v = ((S.card : ℝ) - 1) - (degIn H S v : ℝ) := by
    intro v hv
    have h := hkey v hv
    have hcast : ((delNbr H S v).card : ℝ) + (degIn H S v : ℝ) = ((S.card - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    have hc : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
      rw [Nat.cast_sub (Finset.card_pos.mpr hne)]
      norm_num
    rw [hc] at hcast
    show ((delNbr H S v).card : ℝ) = (S.card : ℝ) - 1 - (degIn H S v : ℝ)
    linarith
  calc ∑ v ∈ S, subCard H S v
      = ∑ v ∈ S, (((S.card : ℝ) - 1) - (degIn H S v : ℝ)) := Finset.sum_congr rfl hpt
    _ = (∑ _v ∈ S, ((S.card : ℝ) - 1)) - ∑ v ∈ S, (degIn H S v : ℝ) := by
        rw [Finset.sum_sub_distrib]
    _ = (S.card : ℝ) * ((S.card : ℝ) - 1) - degSum H S := by
        rw [Finset.sum_const, nsmul_eq_mul, degSum]

/-- An averaging lemma for finite sets. -/
lemma exists_ge_avg_finset {ι : Type*} (s : Finset ι) (h : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, (∑ i ∈ s, f i) / (s.card : ℝ) ≤ f i := by
  classical
  by_contra hc
  push Not at hc
  have hlt : ∑ i ∈ s, f i < ∑ i ∈ s, (∑ j ∈ s, f j) / (s.card : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i hi; exact le_of_lt (hc i hi)
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, hi, hc i hi⟩
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h
  have heq : (s.card : ℝ) * ((∑ j ∈ s, f j) / (s.card : ℝ)) = ∑ j ∈ s, f j := by
    field_simp
  linarith

/-- The core averaged inequality of Shearer's argument. -/
lemma shearer_key (hH : H.CliqueFree 3) {S : Finset V} (hne : S.Nonempty) :
    (S.card : ℝ) * ((S.card : ℝ) * g (degSum H S / (S.card : ℝ)))
      ≤ ∑ v ∈ S, (1 + subCard H S v * g (subDegSum H S v / subCard H S v)) := by
  classical
  have hpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  set D : ℝ := degSum H S with hD
  set m : ℝ := (S.card : ℝ) with hm
  set d : ℝ := D / m with hd
  have hmpos : 0 < m := by rw [hm]; exact hpos
  have hd0 : 0 ≤ d := by
    rw [hd]
    exact div_nonneg (degSum_nonneg S) (le_of_lt hmpos)
  have hterm : ∀ v ∈ S,
      1 + subCard H S v * (g d + (subDegSum H S v / subCard H S v - d) * g' d)
        ≤ 1 + subCard H S v * g (subDegSum H S v / subCard H S v) := by
    intro v hv
    have hM0 : 0 ≤ subCard H S v := subCard_nonneg S v
    have hq0 : 0 ≤ subDegSum H S v / subCard H S v :=
      div_nonneg (subDegSum_nonneg S v) (subCard_nonneg S v)
    have ht := convex_tangent hd0 hq0
    nlinarith [mul_le_mul_of_nonneg_left ht hM0]
  have hsum_le : ∑ v ∈ S,
      (1 + subCard H S v * (g d + (subDegSum H S v / subCard H S v - d) * g' d))
        ≤ ∑ v ∈ S, (1 + subCard H S v * g (subDegSum H S v / subCard H S v)) :=
    Finset.sum_le_sum hterm
  have hpt : ∀ v ∈ S,
      1 + subCard H S v * (g d + (subDegSum H S v / subCard H S v - d) * g' d)
        = 1 + subCard H S v * g d + (subDegSum H S v - d * subCard H S v) * g' d := by
    intro v hv
    have hq := subCard_mul_div (H := H) S v
    calc 1 + subCard H S v * (g d + (subDegSum H S v / subCard H S v - d) * g' d)
        = 1 + subCard H S v * g d
          + (subCard H S v * (subDegSum H S v / subCard H S v)
            - subCard H S v * d) * g' d := by ring
      _ = 1 + subCard H S v * g d + (subDegSum H S v - d * subCard H S v) * g' d := by
          rw [hq]
          ring
  rw [Finset.sum_congr rfl hpt] at hsum_le
  have hlast : ∀ a : ℝ, ∑ x ∈ S, (subDegSum H S x - d * subCard H S x) * a
      = ((∑ v ∈ S, subDegSum H S v) - d * (∑ v ∈ S, subCard H S v)) * a := by
    intro a
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hval : ∑ v ∈ S, (1 + subCard H S v * g d + (subDegSum H S v - d * subCard H S v) * g' d)
      = m + (∑ v ∈ S, subCard H S v) * g d
        + ((∑ v ∈ S, subDegSum H S v) - d * (∑ v ∈ S, subCard H S v)) * g' d := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← hm]
    rw [Finset.sum_mul, hlast]
  rw [hval] at hsum_le
  have hsub : (∑ v ∈ S, subDegSum H S v) = m * D - 2 * ∑ x ∈ S, (degIn H S x : ℝ) ^ 2 := by
    rw [sum_subDegSum (H := H) hH S, hD, hm]
  have hcard : (∑ v ∈ S, subCard H S v) = m * (m - 1) - D := by
    rw [sum_subCard (H := H) hne, hD, hm]
  have hQ : D ^ 2 ≤ m * ∑ x ∈ S, (degIn H S x : ℝ) ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun x => (degIn H S x : ℝ))
    have hSm : (S.card : ℝ) = m := hm.symm
    rw [hSm] at hcs
    show degSum H S ^ 2 ≤ m * ∑ x ∈ S, (degIn H S x : ℝ) ^ 2
    simpa [degSum] using hcs
  have hdm : d * m = D := by
    rw [hd]
    field_simp
  have hbr : m * ((∑ v ∈ S, subDegSum H S v) - d * (∑ v ∈ S, subCard H S v)) ≤ m * D - D ^ 2 := by
    rw [hsub, hcard]
    have hkey : m * (d * (m * (m - 1) - D)) = D * (m * (m - 1) - D) := by
      rw [← mul_assoc, mul_comm m d, hdm]
    have hexp : m * (m * D - 2 * ∑ x ∈ S, (degIn H S x : ℝ) ^ 2 - d * (m * (m - 1) - D))
        = m * (m * D) - m * (2 * ∑ x ∈ S, (degIn H S x : ℝ) ^ 2)
          - m * (d * (m * (m - 1) - D)) := by ring
    rw [hexp, hkey]
    nlinarith [hQ]
  have hXY : (∑ v ∈ S, subDegSum H S v) - d * (∑ v ∈ S, subCard H S v) ≤ D - D ^ 2 / m := by
    have hY : D - D ^ 2 / m = (m * D - D ^ 2) / m := by
      field_simp
    rw [hY, le_div_iff₀ hmpos]
    linarith [hbr]
  have hbr2 : (D - D ^ 2 / m) * g' d
      ≤ ((∑ v ∈ S, subDegSum H S v) - d * (∑ v ∈ S, subCard H S v)) * g' d :=
    mul_le_mul_of_nonpos_right hXY (g'_nonpos hd0)
  have hD2 : (m * d) ^ 2 / m = m * d ^ 2 := by
    field_simp
  have hDM : D = m * d := by
    rw [hd]
    field_simp
  have htarget : m * (m * g d)
      ≤ m + (∑ v ∈ S, subCard H S v) * g d + (D - D ^ 2 / m) * g' d := by
    have hSM : (∑ v ∈ S, subCard H S v) = m * (m - 1) - D := hcard
    rw [hSM, hDM, hD2]
    have hgd' : 0 ≤ 1 - (d + 1) * g d - (d ^ 2 - d) * g' d := by linarith [g_ineq hd0]
    nlinarith [hgd', hmpos]
  calc m * (m * g d)
      ≤ m + (∑ v ∈ S, subCard H S v) * g d + (D - D ^ 2 / m) * g' d := htarget
    _ ≤ m + (∑ v ∈ S, subCard H S v) * g d
          + ((∑ v ∈ S, subDegSum H S v) - d * (∑ v ∈ S, subCard H S v)) * g' d :=
        by linarith [hbr2]
    _ ≤ ∑ v ∈ S, (1 + subCard H S v * g (subDegSum H S v / subCard H S v)) := hsum_le

/-- A vertex whose removal leaves an independent set of the guaranteed size. -/
lemma exists_good_vertex (hH : H.CliqueFree 3) {S : Finset V} (hne : S.Nonempty) :
    ∃ v ∈ S, (S.card : ℝ) * g (degSum H S / (S.card : ℝ))
      ≤ 1 + subCard H S v * g (subDegSum H S v / subCard H S v) := by
  classical
  obtain ⟨v, hv, hle⟩ := exists_ge_avg_finset S hne
    (fun v => 1 + subCard H S v * g (subDegSum H S v / subCard H S v))
  refine ⟨v, hv, ?_⟩
  have hkey := shearer_key (H := H) hH hne
  have hpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hquot : (S.card : ℝ) * g (degSum H S / (S.card : ℝ))
      ≤ (∑ v ∈ S, (1 + subCard H S v * g (subDegSum H S v / subCard H S v)))
        / (S.card : ℝ) := by
    rw [le_div_iff₀ hpos]
    calc (S.card : ℝ) * g (degSum H S / (S.card : ℝ)) * (S.card : ℝ)
        = (S.card : ℝ) * ((S.card : ℝ) * g (degSum H S / (S.card : ℝ))) := by ring
      _ ≤ _ := hkey
  linarith

/-- Shearer's theorem, stated for finite vertex sets of a triangle-free graph. -/
theorem shearer_finset (hH : H.CliqueFree 3) (S : Finset V) :
    ∃ I : Finset V, I ⊆ S ∧ H.IsIndepSet (I : Set V) ∧
      (S.card : ℝ) * g (degSum H S / (S.card : ℝ)) ≤ (I.card : ℝ) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, by simp, ?_, ?_⟩
      · intro a ha
        exact absurd ha (Finset.notMem_empty a)
      · simp [degSum]
    · obtain ⟨v, hv, hbound⟩ := exists_good_vertex (H := H) hH hne
      obtain ⟨I₀, hI₀sub, hI₀ind, hI₀card⟩ := ih (delNbr H S v) (delNbr_ssubset hv)
      have hvI₀ : v ∉ I₀ := by
        intro h
        exact ne_of_mem_delNbr (hI₀sub h) rfl
      refine ⟨insert v I₀, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv
        · exact delNbr_subset (hI₀sub hx)
      · intro a ha b hb hab hAdj
        simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact hab rfl
        · exact not_adj_of_mem_delNbr (hI₀sub hb) hAdj
        · exact not_adj_of_mem_delNbr (hI₀sub ha) hAdj.symm
        · exact hI₀ind ha hb hab hAdj
      · have hsubeq : subCard H S v * g (subDegSum H S v / subCard H S v)
            = ((delNbr H S v).card : ℝ)
              * g (degSum H (delNbr H S v) / ((delNbr H S v).card : ℝ)) := rfl
        have h1 : (1 : ℝ) + subCard H S v * g (subDegSum H S v / subCard H S v)
            ≤ 1 + (I₀.card : ℝ) := by
          rw [hsubeq]
          linarith [hI₀card]
        have hcard : ((insert v I₀).card : ℝ) = (I₀.card : ℝ) + 1 := by
          rw [Finset.card_insert_of_notMem hvI₀]
          push_cast
          ring
        linarith

/-- The independence-number lower bound `alpha >= (1/40) sqrt(m log m)`. -/
theorem exists_indep_large (hH : H.CliqueFree 3) {S : Finset V} (hS : 100 ≤ S.card) :
    ∃ I : Finset V, I ⊆ S ∧ H.IsIndepSet (I : Set V) ∧
      (1 / 40 : ℝ) * Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) ≤ (I.card : ℝ) := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hm100 : (100 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS
  have hmpos : (0 : ℝ) < (S.card : ℝ) := by linarith
  have hlog100 : (1 : ℝ) ≤ Real.log 100 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogm : (1 : ℝ) ≤ Real.log (S.card : ℝ) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 100) hm100
    linarith
  have hmlog : (64 : ℝ) ≤ (S.card : ℝ) * Real.log (S.card : ℝ) := by
    have h100 : (100 : ℝ) * 1 ≤ (S.card : ℝ) * Real.log (S.card : ℝ) :=
      mul_le_mul hm100 hlogm (by norm_num) (by linarith)
    linarith
  have hx8 : 8 ≤ Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) := by
    have h64 : (8 : ℝ) ^ 2 ≤ (S.card : ℝ) * Real.log (S.card : ℝ) := by nlinarith
    calc (8 : ℝ) = Real.sqrt (8 ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) := Real.sqrt_le_sqrt h64
  obtain ⟨v₀, hv₀, hmax⟩ := Finset.exists_max_image S (fun v => degIn H S v) hne
  by_cases hcase : Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) ≤ (degIn H S v₀ : ℝ)
  · refine ⟨S.filter (H.Adj v₀), Finset.filter_subset _ _, ?_, ?_⟩
    · intro x hx y hy hxy hAdj
      have hx' : H.Adj v₀ x := (Finset.mem_filter.mp (by simpa using hx)).2
      have hy' : H.Adj v₀ y := (Finset.mem_filter.mp (by simpa using hy)).2
      exact (SimpleGraph.isIndepSet_neighborSet_of_triangleFree (G := H) hH v₀)
        (by simpa using hx') (by simpa using hy') hxy hAdj
    · have hcard : (S.filter (H.Adj v₀)).card = degIn H S v₀ := rfl
      rw [hcard]
      have hx0 : 0 ≤ Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) :=
        Real.sqrt_nonneg _
      nlinarith
  · push Not at hcase
    obtain ⟨I, hIsub, hIind, hIcard⟩ := shearer_finset (H := H) hH S
    refine ⟨I, hIsub, hIind, ?_⟩
    have hDle : degSum H S / (S.card : ℝ) ≤ (degIn H S v₀ : ℝ) := by
      rw [div_le_iff₀ hmpos]
      rw [degSum]
      calc ∑ x ∈ S, (degIn H S x : ℝ) ≤ ∑ _x ∈ S, (degIn H S v₀ : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            exact_mod_cast hmax x hx
        _ = (degIn H S v₀ : ℝ) * (S.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    have hq0 : 0 ≤ degSum H S / (S.card : ℝ) :=
      div_nonneg (degSum_nonneg S) (le_of_lt hmpos)
    have hDel0 : 0 ≤ (degIn H S v₀ : ℝ) := by positivity
    have hx0 : 0 ≤ Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) := Real.sqrt_nonneg _
    have hant1 : g (degIn H S v₀ : ℝ) ≤ g (degSum H S / (S.card : ℝ)) :=
      antitoneOn_g (Set.mem_Ici.mpr hq0) (Set.mem_Ici.mpr hDel0) hDle
    have hant2 : g (Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)))
        ≤ g (degIn H S v₀ : ℝ) :=
      antitoneOn_g (Set.mem_Ici.mpr hDel0) (Set.mem_Ici.mpr hx0) (le_of_lt hcase)
    have hgl := g_lower hx8
    have hnumeric : (1 / 40 : ℝ) * Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ))
        ≤ (S.card : ℝ) * g (Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ))) := by
      set x : ℝ := Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) with hxdef
      have hxpos : 0 < x := by rw [hxdef]; linarith
      have hxx : x * x = (S.card : ℝ) * Real.log (S.card : ℝ) := by
        rw [hxdef]
        exact Real.mul_self_sqrt (by positivity)
      have hlogx : Real.log x
          = Real.log ((S.card : ℝ) * Real.log (S.card : ℝ)) / 2 := by
        rw [hxdef]
        exact Real.log_sqrt (by positivity)
      have hL : Real.log (S.card : ℝ) ≤ Real.log ((S.card : ℝ) * Real.log (S.card : ℝ)) := by
        apply Real.log_le_log hmpos
        nlinarith
      have hmL : (S.card : ℝ) * Real.log (S.card : ℝ)
          ≤ (S.card : ℝ) * Real.log ((S.card : ℝ) * Real.log (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hL (le_of_lt hmpos)
      have hstep : (1 / 40) * x ≤ (S.card : ℝ) * (Real.log x / (20 * x)) := by
        rw [hlogx]
        have hden : (0 : ℝ) < 40 * x := by positivity
        rw [show (S.card : ℝ)
            * (Real.log ((S.card : ℝ) * Real.log (S.card : ℝ)) / 2 / (20 * x))
            = (S.card : ℝ) * Real.log ((S.card : ℝ) * Real.log (S.card : ℝ))
              / (40 * x) by field_simp; ring]
        rw [le_div_iff₀ hden]
        nlinarith [hxx, hmL]
      calc (1 / 40) * Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ)) = (1 / 40) * x := by
            rw [hxdef]
        _ ≤ (S.card : ℝ) * (Real.log x / (20 * x)) := hstep
        _ ≤ (S.card : ℝ) * g x := by
            apply mul_le_mul_of_nonneg_left hgl (le_of_lt hmpos)
        _ = (S.card : ℝ) * g (Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ))) := by
            rw [hxdef]
    calc (1 / 40 : ℝ) * Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ))
        ≤ (S.card : ℝ) * g (Real.sqrt ((S.card : ℝ) * Real.log (S.card : ℝ))) := hnumeric
      _ ≤ (S.card : ℝ) * g (degIn H S v₀ : ℝ) :=
          mul_le_mul_of_nonneg_left hant2 (le_of_lt hmpos)
      _ ≤ (S.card : ℝ) * g (degSum H S / (S.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hant1 (le_of_lt hmpos)
      _ ≤ (I.card : ℝ) := hIcard

end Shearer

end Erdos1182F

/- ## The star of cliques -/

namespace Erdos1182F

open Classical

section StarCliques

/-- The star of `m` cliques of size `s`: on `Fin n`, the vertex `0` is joined to every other
vertex, the vertices `1, …, m*s` are split into `m` consecutive blocks of `s` vertices, each block
being a clique, and the remaining vertices are joined only to the vertex `0`. -/
def starCliques (n s m : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val = 0 ∨ v.val = 0 ∨
    (1 ≤ u.val ∧ u.val ≤ m * s ∧ 1 ≤ v.val ∧ v.val ≤ m * s ∧
      (u.val - 1) / s = (v.val - 1) / s))
  symm := ⟨by
    intro u v huv
    obtain ⟨hne, h | h | ⟨h1, h2, h3, h4, h5⟩⟩ := huv
    · exact ⟨hne.symm, Or.inr (Or.inl h)⟩
    · exact ⟨hne.symm, Or.inl h⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨h3, h4, h1, h2, h5.symm⟩)⟩⟩
  loopless := ⟨by
    intro u huu
    exact huu.1 rfl⟩

variable {n s m : ℕ}

lemma starCliques_adj_zero {u v : Fin n} (hu : u.val = 0) :
    (starCliques n s m).Adj u v ↔ v.val ≠ 0 := by
  constructor
  · rintro ⟨hne, h | h | ⟨h1, h2, h3, h4, h5⟩⟩
    · intro hv
      exact hne (Fin.ext (by rw [hu, hv]))
    · intro hv
      exact hne (Fin.ext (by rw [hu, hv]))
    · exact fun _ => absurd h1 (by omega)
  · intro hv
    exact ⟨fun h => hv (by rw [← h]; exact hu), Or.inl hu⟩

lemma starCliques_adj_of_block {u v : Fin n} (hne : u ≠ v)
    (hu1 : 1 ≤ u.val) (hu2 : u.val ≤ m * s)
    (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ m * s)
    (hb : (u.val - 1) / s = (v.val - 1) / s) : (starCliques n s m).Adj u v :=
  ⟨hne, Or.inr (Or.inr ⟨hu1, hu2, hv1, hv2, hb⟩)⟩

lemma starCliques_block_of_adj {u v : Fin n} (h : (starCliques n s m).Adj u v)
    (hu : u.val ≠ 0) (hv : v.val ≠ 0) : (u.val - 1) / s = (v.val - 1) / s := by
  obtain ⟨-, h | h | h⟩ := h
  · exact absurd h hu
  · exact absurd h hv
  · exact h.2.2.2.2

lemma starCliques_connected (hn : 0 < n) : (starCliques n s m).Connected := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have huniv : (starCliques n s m).IsUniversal ⟨0, hn⟩ := by
    intro v hv
    exact (starCliques_adj_zero (s := s) (m := m) (u := ⟨0, hn⟩) (v := v) rfl).mpr (by
      intro h
      exact hv (Fin.ext (by rw [h])))
  refine ⟨fun u v => ?_⟩
  exact (SimpleGraph.Reachable.of_isUniversal u huniv).symm.trans
    (SimpleGraph.Reachable.of_isUniversal v huniv)

/-- `(a-1)/s = j` characterises the `j`-th block of size `s`. -/
lemma div_pred_eq_iff {a j : ℕ} (hs : 0 < s) (ha : 1 ≤ a) :
    (a - 1) / s = j ↔ j * s + 1 ≤ a ∧ a ≤ j * s + s := by
  constructor
  · intro h
    have h1 : s * ((a - 1) / s) + (a - 1) % s = a - 1 := Nat.div_add_mod (a - 1) s
    have h2 : (a - 1) % s < s := Nat.mod_lt (a - 1) hs
    rw [h, Nat.mul_comm s j] at h1
    omega
  · rintro ⟨h1, h2⟩
    have h1' : j * s ≤ a - 1 := by omega
    have h2' : a - 1 < (j + 1) * s := by
      rw [Nat.succ_mul]
      omega
    exact Nat.div_eq_of_lt_le h1' h2'

/-- The vertices `1, …, m*s`. -/
def blkSet (n m s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => 1 ≤ u.val ∧ u.val ≤ m * s)

/-- The `j`-th block of `s` vertices. -/
def blkPart (n m s j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => 1 ≤ u.val ∧ u.val ≤ m * s ∧ (u.val - 1) / s = j)

lemma blkSet_card (hn : m * s < n) : (blkSet n m s).card = m * s := by
  have himg : (blkSet n m s).image Fin.val = Finset.Icc 1 (m * s) := by
    ext x
    simp only [blkSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    exact ⟨fun ⟨u, ⟨h1, h2⟩, hx⟩ => ⟨hx ▸ h1, hx ▸ h2⟩,
      fun ⟨h1, h2⟩ => ⟨⟨x, by omega⟩, ⟨h1, h2⟩, rfl⟩⟩
  calc (blkSet n m s).card = ((blkSet n m s).image Fin.val).card := by
        rw [Finset.card_image_of_injective _ Fin.val_injective]
    _ = (Finset.Icc 1 (m * s)).card := by rw [himg]
    _ = m * s := by rw [Nat.card_Icc]; omega

lemma blkPart_card (hn : m * s < n) (hs : 0 < s) {j : ℕ} (hj : j < m) :
    (blkPart n m s j).card = s := by
  have hle : j * s + s ≤ m * s := by
    have : j + 1 ≤ m := by omega
    calc j * s + s = (j + 1) * s := by ring
      _ ≤ m * s := Nat.mul_le_mul_right s this
  have himg : (blkPart n m s j).image Fin.val = Finset.Icc (j * s + 1) (j * s + s) := by
    ext x
    simp only [blkPart, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    exact ⟨fun ⟨u, ⟨h1, h2, h3⟩, hx⟩ => hx ▸ (div_pred_eq_iff hs h1).mp h3,
      fun ⟨h1, h2⟩ => by
        have hxn : x < n := by omega
        have hx1 : 1 ≤ x := by omega
        have hx2 : x ≤ m * s := by omega
        exact ⟨⟨x, hxn⟩, ⟨hx1, hx2, (div_pred_eq_iff hs hx1).mpr ⟨h1, h2⟩⟩, rfl⟩⟩
  calc (blkPart n m s j).card = ((blkPart n m s j).image Fin.val).card := by
        rw [Finset.card_image_of_injective _ Fin.val_injective]
    _ = (Finset.Icc (j * s + 1) (j * s + s)).card := by rw [himg]
    _ = s := by rw [Nat.card_Icc]; omega

lemma starCliques_degree_ge (hn : m * s < n) (hs : 0 < s) {u : Fin n}
    (hu1 : 1 ≤ u.val) (hu2 : u.val ≤ m * s) :
    s ≤ (starCliques n s m).degree u := by
  have hn0 : 0 < n := by omega
  have hjm : (u.val - 1) / s < m := by
    rw [Nat.div_lt_iff_lt_mul hs]
    omega
  have hcard : (blkPart n m s ((u.val - 1) / s)).card = s := blkPart_card hn hs hjm
  have hu_mem : u ∈ blkPart n m s ((u.val - 1) / s) := by
    simp only [blkPart, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu1, hu2, trivial⟩
  have hcenter : (⟨0, hn0⟩ : Fin n) ∉ blkPart n m s ((u.val - 1) / s) := by
    simp only [blkPart, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact absurd h.1 (by simp)
  have hsub : insert (⟨0, hn0⟩ : Fin n) ((blkPart n m s ((u.val - 1) / s)).erase u)
      ⊆ (starCliques n s m).neighborFinset u := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · refine SimpleGraph.mem_neighborFinset _ _ _ |>.mpr ?_
      exact ((starCliques_adj_zero (s := s) (m := m) (u := ⟨0, hn0⟩) (v := u) rfl).mpr
        (by omega)).symm
    · have hw' := Finset.mem_of_mem_erase hw
      have hne : w ≠ u := Finset.ne_of_mem_erase hw
      simp only [blkPart, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
      refine SimpleGraph.mem_neighborFinset _ _ _ |>.mpr ?_
      exact starCliques_adj_of_block (s := s) (m := m) (u := u) (v := w) hne.symm hu1 hu2
        hw'.1 hw'.2.1 (by rw [hw'.2.2])
  have hcard2 : (insert (⟨0, hn0⟩ : Fin n)
      ((blkPart n m s ((u.val - 1) / s)).erase u)).card = s := by
    rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem hu_mem, hcard]
    · omega
    · exact fun h => hcenter (Finset.mem_of_mem_erase h)
  calc s = _ := hcard2.symm
    _ ≤ ((starCliques n s m).neighborFinset u).card := Finset.card_le_card hsub
    _ = (starCliques n s m).degree u := SimpleGraph.card_neighborFinset_eq_degree _ _

lemma edgeSet_ncard_eq_edgeFinset (G : SimpleGraph (Fin n)) :
    G.edgeSet.ncard = G.edgeFinset.card :=
  Set.ncard_eq_toFinset_card' _

lemma starCliques_edge_lower (hn : m * s < n) (hs : 0 < s) :
    (m : ℝ) * s * ((s : ℝ) - 1) / 2 ≤ ((starCliques n s m).edgeSet.ncard : ℝ) := by
  have hsum_ge : m * s * s ≤ ∑ u ∈ blkSet n m s, (starCliques n s m).degree u := by
    have hstep : ∑ u ∈ blkSet n m s, s ≤ ∑ u ∈ blkSet n m s, (starCliques n s m).degree u := by
      refine Finset.sum_le_sum ?_
      intro u hu
      simp only [blkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      exact starCliques_degree_ge hn hs hu.1 hu.2
    rw [Finset.sum_const, blkSet_card hn, smul_eq_mul] at hstep
    exact hstep
  have hsum_le : ∑ u ∈ blkSet n m s, (starCliques n s m).degree u
      ≤ ∑ u : Fin n, (starCliques n s m).degree u := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro u _ _
    exact Nat.zero_le _
  have htwice : ∑ u : Fin n, (starCliques n s m).degree u
      = 2 * (starCliques n s m).edgeSet.ncard := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, edgeSet_ncard_eq_edgeFinset]
  have hmain : m * s * s ≤ 2 * (starCliques n s m).edgeSet.ncard := by
    rw [← htwice] at *
    omega
  have hcast : (m : ℝ) * s * s ≤ 2 * ((starCliques n s m).edgeSet.ncard : ℝ) := by
    exact_mod_cast hmain
  have hs' : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hm' : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hsub : ((s : ℝ) - 1) ≤ (s : ℝ) := by linarith
  have step : (m : ℝ) * s * ((s : ℝ) - 1) ≤ (m : ℝ) * s * s := by
    refine mul_le_mul_of_nonneg_left hsub (by positivity)
  linarith

end StarCliques

end Erdos1182F

/- ## Embedding a star of cliques into the complement -/

namespace Erdos1182F

open Classical

section Embed

variable {N : ℕ}

/-- If `x` is in the block with index `(x-1)/s` and that index is less than `m`, then `x` is one
of the vertices `1, …, m*s`. -/
lemma val_le_of_div_eq {n s m : ℕ} {x : Fin n} {j : ℕ} (hs : 0 < s) (hx : x.val ≠ 0)
    (hj : (x.val - 1) / s = j) (hjm : j < m) : x.val ≤ m * s := by
  have h1 : x.val ≤ j * s + s := ((div_pred_eq_iff (s := s) hs (by omega)).mp hj).2
  have h3 : j * s + s ≤ m * s := by
    have hjm' : j + 1 ≤ m := by omega
    calc j * s + s = (j + 1) * s := by ring
      _ ≤ m * s := Nat.mul_le_mul_right s hjm'
  omega

/-- The block index of a vertex inside the block range. -/
lemma div_pred_lt {n s m : ℕ} {x : Fin n} (hs : 0 < s) (hx : x.val ≠ 0) (h : x.val ≤ m * s) :
    (x.val - 1) / s < m := by
  rw [Nat.div_lt_iff_lt_mul hs]
  have hx1 : 1 ≤ x.val := Nat.one_le_iff_ne_zero.mpr hx
  omega

/-- Two positive naturals with the same quotient and remainder on division by `s` are equal. -/
lemma val_eq_of_div_mod_eq {a b s : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : (a - 1) / s = (b - 1) / s) (h2 : (a - 1) % s = (b - 1) % s) : a = b := by
  have e1 : s * ((a - 1) / s) + (a - 1) % s = a - 1 := Nat.div_add_mod (a - 1) s
  have e2 : s * ((b - 1) / s) + (b - 1) % s = b - 1 := Nat.div_add_mod (b - 1) s
  have h : a - 1 = b - 1 := by rw [← e1, ← e2, h1, h2]
  omega

/-- Cancelling the common truncated subtraction `- 1 - m*s`. -/
lemma sub_eq_of_mul_lt {a b m s : ℕ} (ha : m * s < a) (hb : m * s < b)
    (h : a - 1 - m * s = b - 1 - m * s) : a = b := by
  omega

/-- If a triangle-free `H` on `Fin N` has a vertex `u`, `m` pairwise disjoint `H`-independent
`s`-sets inside the non-neighbourhood `U` of `u`, and a further subset of `U` of size
`n - 1 - m*s` disjoint from them, then `Hᶜ` contains the star of `m` cliques of size `s`. -/
lemma starCliques_embed (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    {n s m : ℕ} (hs : 0 < s) (hm : 0 < m) (hms : m * s < n)
    (u : Fin N) (U : Finset (Fin N)) (hu : u ∉ U)
    (hU : ∀ w ∈ U, ¬ H.Adj u w)
    (I : Fin m → Finset (Fin N)) (hIsub : ∀ j, I j ⊆ U) (hIcard : ∀ j, (I j).card = s)
    (hIind : ∀ j, H.IsIndepSet ((I j : Finset (Fin N)) : Set (Fin N)))
    (hIdis : ∀ j j', j ≠ j' → Disjoint (I j) (I j'))
    (rest : Finset (Fin N)) (hrestsub : rest ⊆ U)
    (hrestdis : ∀ j, Disjoint rest (I j))
    (hrestcard : n - 1 - m * s ≤ rest.card) :
    Nonempty (SimpleGraph.Copy (starCliques n s m) Hᶜ) := by
  have hn0 : 0 < n := by omega
  let φ : Fin n → Fin N := fun x =>
    if h0 : x.val = 0 then u
    else if h1 : x.val ≤ m * s then
      ((I ⟨(x.val - 1) / s, by rw [Nat.div_lt_iff_lt_mul hs]; omega⟩).equivFin.symm
        ⟨(x.val - 1) % s, by rw [hIcard]; exact Nat.mod_lt _ hs⟩ : Fin N)
    else
      (rest.equivFin.symm ⟨x.val - 1 - m * s, by
        have hlt : x.val ≤ n - 1 := by omega
        omega⟩ : Fin N)
  have hφ0 : φ ⟨0, hn0⟩ = u := by
    simp only [φ]
    exact dif_pos trivial
  have hφblk : ∀ (x : Fin n) (j : Fin m), x.val ≠ 0 → (x.val - 1) / s = j → φ x ∈ I j := by
    intro x j hx hj
    have hxm : x.val ≤ m * s := val_le_of_div_eq hs hx hj j.isLt
    have hidx : (⟨(x.val - 1) / s, by rw [Nat.div_lt_iff_lt_mul hs]; omega⟩ : Fin m) = j :=
      Fin.ext hj
    have hEq : φ x = ((I j).equivFin.symm
        ⟨(x.val - 1) % s, by rw [hIcard]; exact Nat.mod_lt _ hs⟩ : Fin N) := by
      simp only [φ]
      rw [dif_neg hx, dif_pos hxm, hidx]
    rw [hEq]
    exact (I j).equivFin.symm ⟨_, _⟩ |>.2
  have hφrest : ∀ x : Fin n, ¬ x.val ≤ m * s → φ x ∈ rest := by
    intro x hx
    have hx0 : x.val ≠ 0 := by omega
    simp only [φ]
    rw [dif_neg hx0, dif_neg hx]
    exact (rest.equivFin.symm _).2
  have hφidx : ∀ (x : Fin n) (j : Fin m) (hx : x.val ≠ 0) (hj : (x.val - 1) / s = j),
      ((I j).equivFin ⟨φ x, hφblk x j hx hj⟩).val = (x.val - 1) % s := by
    intro x j hx hj
    have hxm : x.val ≤ m * s := val_le_of_div_eq hs hx hj j.isLt
    have hidx : (⟨(x.val - 1) / s, by rw [Nat.div_lt_iff_lt_mul hs]; omega⟩ : Fin m) = j :=
      Fin.ext hj
    have hEq : (⟨φ x, hφblk x j hx hj⟩ : ↥(I j)) = (I j).equivFin.symm
        ⟨(x.val - 1) % s, by rw [hIcard]; exact Nat.mod_lt _ hs⟩ := by
      refine Subtype.ext ?_
      simp only [φ]
      rw [dif_neg hx, dif_pos hxm, hidx]
    rw [hEq]
    simp
  have hφridx : ∀ (x : Fin n) (hx : ¬ x.val ≤ m * s),
      ((rest.equivFin ⟨φ x, hφrest x hx⟩).val) = x.val - 1 - m * s := by
    intro x hx
    have hx0 : x.val ≠ 0 := by omega
    have hEq : (⟨φ x, hφrest x hx⟩ : ↥rest)
        = rest.equivFin.symm ⟨x.val - 1 - m * s, by
            have hlt : x.val ≤ n - 1 := by omega
            omega⟩ := by
      refine Subtype.ext ?_
      simp only [φ]
      rw [dif_neg hx0, dif_neg hx]
    rw [hEq]
    simp
  have hφmem : ∀ z : Fin n, z.val ≠ 0 → φ z ∈ U := by
    intro z hz
    by_cases hz1 : z.val ≤ m * s
    · have hjm : (z.val - 1) / s < m := div_pred_lt hs hz hz1
      exact hIsub ⟨(z.val - 1) / s, hjm⟩ (hφblk z ⟨_, hjm⟩ hz rfl)
    · exact hrestsub (hφrest z hz1)
  have hblock_eq : ∀ (x y : Fin n) (j : Fin m) (hx : x.val ≠ 0) (hy : y.val ≠ 0)
      (hxj : (x.val - 1) / s = j) (hyj : (y.val - 1) / s = j), φ x = φ y → x = y := by
    intro x y j hx hy hxj hyj hxy
    have hsub : (⟨φ x, hφblk x j hx hxj⟩ : ↥(I j)) = ⟨φ y, hφblk y j hy hyj⟩ := Subtype.ext hxy
    have h3 : ((I j).equivFin ⟨φ x, hφblk x j hx hxj⟩).val
        = ((I j).equivFin ⟨φ y, hφblk y j hy hyj⟩).val := by rw [hsub]
    rw [hφidx x j hx hxj, hφidx y j hy hyj] at h3
    exact Fin.ext (val_eq_of_div_mod_eq (Nat.one_le_iff_ne_zero.mpr hx)
      (Nat.one_le_iff_ne_zero.mpr hy) (by rw [hxj, hyj]) h3)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    by_cases hx0 : x.val = 0
    · by_cases hy0 : y.val = 0
      · exact Fin.ext (by omega)
      · have hx' : φ x = u := by
          rw [show x = ⟨0, hn0⟩ from Fin.ext (by omega), hφ0]
        exact absurd ((hxy ▸ hx' : φ y = u) ▸ hφmem y hy0) hu
    · by_cases hy0 : y.val = 0
      · have hy' : φ y = u := by
          rw [show y = ⟨0, hn0⟩ from Fin.ext (by omega), hφ0]
        exact absurd ((hxy.symm ▸ hy' : φ x = u) ▸ hφmem x hx0) hu
      · by_cases hxb : x.val ≤ m * s
        · by_cases hyb : y.val ≤ m * s
          · by_cases hb : (x.val - 1) / s = (y.val - 1) / s
            · have hxm : (x.val - 1) / s < m := div_pred_lt hs hx0 hxb
              exact hblock_eq x y ⟨(x.val - 1) / s, hxm⟩ hx0 hy0 rfl (by simpa using hb.symm) hxy
            · have hxm : (x.val - 1) / s < m := div_pred_lt hs hx0 hxb
              have hym : (y.val - 1) / s < m := div_pred_lt hs hy0 hyb
              have hne' : (⟨(x.val - 1) / s, hxm⟩ : Fin m) ≠ ⟨(y.val - 1) / s, hym⟩ := by
                intro h
                exact hb (by simpa using congrArg Fin.val h)
              have hmy : φ y ∈ I ⟨(x.val - 1) / s, hxm⟩ := hxy ▸ hφblk x _ hx0 rfl
              exact absurd (hφblk y _ hy0 rfl)
                (Finset.disjoint_left.mp (hIdis _ _ hne') hmy)
          · have hxm : (x.val - 1) / s < m := div_pred_lt hs hx0 hxb
            have hmy : φ y ∈ rest := hφrest y hyb
            exact absurd hmy (Finset.disjoint_right.mp (hrestdis ⟨_, hxm⟩)
              (hxy ▸ hφblk x _ hx0 rfl))
        · by_cases hyb : y.val ≤ m * s
          · have hmy : φ y ∈ I ⟨(y.val - 1) / s, div_pred_lt hs hy0 hyb⟩ := hφblk y _ hy0 rfl
            exact absurd (hxy.symm ▸ hφrest x hxb)
              (Finset.disjoint_right.mp (hrestdis ⟨_, div_pred_lt hs hy0 hyb⟩) hmy)
          · have hsub : (⟨φ x, hφrest x hxb⟩ : ↥rest) = ⟨φ y, hφrest y hyb⟩ := Subtype.ext hxy
            have h3 : ((rest.equivFin ⟨φ x, hφrest x hxb⟩).val)
                = ((rest.equivFin ⟨φ y, hφrest y hyb⟩).val) := by rw [hsub]
            rw [hφridx x hxb, hφridx y hyb] at h3
            exact Fin.ext (sub_eq_of_mul_lt (not_le.mp hxb) (not_le.mp hyb) h3)
  have hφadj : ∀ a b : Fin n, (starCliques n s m).Adj a b → Hᶜ.Adj (φ a) (φ b) := by
    intro a b hab
    have hnab : a ≠ b := hab.1
    have hne : φ a ≠ φ b := fun h => hnab (hφinj h)
    refine (SimpleGraph.compl_adj H (φ a) (φ b)).mpr ⟨hne, ?_⟩
    obtain ⟨-, h | h | ⟨h1, h2, h3, h4, h5⟩⟩ := hab
    · have hb0 : b.val ≠ 0 := fun hb => hnab (Fin.ext (by rw [h, hb]))
      rw [show a = ⟨0, hn0⟩ from Fin.ext h, hφ0]
      exact hU (φ b) (hφmem b hb0)
    · have ha0 : a.val ≠ 0 := fun ha => hnab (Fin.ext (by rw [h, ha]))
      rw [show b = ⟨0, hn0⟩ from Fin.ext h, hφ0]
      exact fun hh => hU (φ a) (hφmem a ha0) hh.symm
    · have ha0 : a.val ≠ 0 := Nat.one_le_iff_ne_zero.mp h1
      have hb0 : b.val ≠ 0 := Nat.one_le_iff_ne_zero.mp h3
      have ham : (a.val - 1) / s < m := div_pred_lt hs ha0 h2
      have hma : φ a ∈ I ⟨(a.val - 1) / s, ham⟩ := hφblk a _ ha0 rfl
      have hmb : φ b ∈ I ⟨(a.val - 1) / s, ham⟩ :=
        hφblk b _ hb0 (by simpa using h5.symm)
      exact (SimpleGraph.isIndepSet_iff H).mp (hIind _) hma hmb hne
  refine ⟨⟨⟨φ, ?_⟩, hφinj⟩⟩
  intro a b hab
  exact hφadj a b hab

end Embed

end Erdos1182F

/- ## Extracting independent sets and the Ramsey bounds -/

namespace Erdos1182F

open Classical

section Extract

variable {α : Type*} [DecidableEq α]

/-- From a finite set of size at least `t*s` one can extract `t` pairwise disjoint subsets of
size `s`. -/
lemma exists_disjoint_sets :
    ∀ (t s : ℕ) (U : Finset α), t * s ≤ U.card →
      ∃ I : Fin t → Finset α, (∀ j, I j ⊆ U) ∧ (∀ j, (I j).card = s) ∧
        (∀ j j', j ≠ j' → Disjoint (I j) (I j')) := by
  intro t
  induction t with
  | zero =>
    intro s U _
    exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ t ih =>
    intro s U hU
    have hs : s ≤ U.card := by
      have : s ≤ (t + 1) * s := Nat.le_mul_of_pos_left s (by omega)
      omega
    obtain ⟨A, hAU, hAcard⟩ := Finset.exists_subset_card_eq hs
    have hU' : t * s ≤ (U \ A).card := by
      rw [Finset.card_sdiff_of_subset hAU, hAcard]
      have h1 : (t + 1) * s = t * s + s := by ring
      omega
    obtain ⟨J, hJsub, hJcard, hJdis⟩ := ih s (U \ A) hU'
    have hJA : ∀ i, Disjoint A (J i) := by
      intro i
      refine Finset.disjoint_left.mpr ?_
      intro a ha haJ
      exact (Finset.mem_sdiff.mp (hJsub i haJ)).2 ha
    have hJsubU : ∀ i, J i ⊆ U := fun i => (hJsub i).trans (Finset.sdiff_subset)
    refine ⟨Fin.cons A J, ?_, ?_, ?_⟩
    · intro j
      match j with
      | ⟨0, hp⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          rw [h0, Fin.cons_zero]
          exact hAU
      | ⟨i + 1, hp⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [hj, Fin.cons_succ]
          exact hJsubU ⟨i, by omega⟩
    · intro j
      match j with
      | ⟨0, hp⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          rw [h0, Fin.cons_zero]
          exact hAcard
      | ⟨i + 1, hp⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [hj, Fin.cons_succ]
          exact hJcard ⟨i, by omega⟩
    · intro j j' hne
      match j, j' with
      | ⟨0, hp⟩, ⟨0, hp'⟩ => exact absurd (Fin.ext rfl) hne
      | ⟨0, hp⟩, ⟨i' + 1, hp'⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          have hj : (⟨i' + 1, hp'⟩ : Fin (t + 1)) = (⟨i', by omega⟩ : Fin t).succ := rfl
          rw [h0, hj, Fin.cons_zero, Fin.cons_succ]
          exact hJA ⟨i', by omega⟩
      | ⟨i + 1, hp⟩, ⟨0, hp'⟩ =>
          have h0 : (⟨0, hp'⟩ : Fin (t + 1)) = 0 := rfl
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [h0, hj, Fin.cons_zero, Fin.cons_succ]
          exact (hJA ⟨i, by omega⟩).symm
      | ⟨i + 1, hp⟩, ⟨i' + 1, hp'⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          have hj' : (⟨i' + 1, hp'⟩ : Fin (t + 1)) = (⟨i', by omega⟩ : Fin t).succ := rfl
          rw [hj, hj', Fin.cons_succ, Fin.cons_succ]
          refine hJdis ⟨i, by omega⟩ ⟨i', by omega⟩ ?_
          intro h
          exact hne (by rw [hj, hj', h])

end Extract

/-- `x ↦ √(x log x)` is monotone on `[1, ∞)`. -/
lemma sqrt_mul_log_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.sqrt (a * Real.log a) ≤ Real.sqrt (b * Real.log b) := by
  apply Real.sqrt_le_sqrt
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  exact mul_le_mul hab hlb hla (by linarith)

section Shear

variable {N : ℕ}

/-- An `H`-independent subset of `U` of size `s`, where `#U ≥ n/2` and `s` is below the Shearer
bound at scale `n/2`. -/
lemma exists_indep_subset (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (hH : H.CliqueFree 3) {n s : ℕ}
    (hsn : (s : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)))
    (hn100 : 100 ≤ n / 2) {U : Finset (Fin N)} (hU : n / 2 ≤ U.card) :
    ∃ A : Finset (Fin N), A ⊆ U ∧ A.card = s ∧
      H.IsIndepSet ((A : Finset (Fin N)) : Set (Fin N)) := by
  have hUn : (100 : ℕ) ≤ U.card := le_trans hn100 hU
  obtain ⟨I, hIsub, hIind, hIcard⟩ := exists_indep_large (H := H) hH (S := U) hUn
  have hnR : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ n / 2 := le_trans (by norm_num) hn100
    exact_mod_cast h1
  have hUR : ((n / 2 : ℕ) : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hU
  have hmono := sqrt_mul_log_mono hnR hUR
  have hle : (s : ℝ) ≤ (I.card : ℝ) := by
    refine le_trans hsn ?_
    refine le_trans ?_ hIcard
    exact mul_le_mul_of_nonneg_left hmono (by norm_num)
  have hscard : s ≤ I.card := by exact_mod_cast hle
  obtain ⟨A, hAI, hAcard⟩ := Finset.exists_subset_card_eq hscard
  refine ⟨A, hAI.trans hIsub, hAcard, ?_⟩
  intro x hx y hy hxy hadj
  exact hIind (hAI hx) (hAI hy) hxy hadj

/-- Shearer's bound, iterated: `t` pairwise disjoint `H`-independent `s`-sets can be found in any
vertex set of size at least `n/2 + t*s`. -/
lemma extract_indep_sets (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (hH : H.CliqueFree 3) {n s : ℕ}
    (hsn : (s : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)))
    (hn100 : 100 ≤ n / 2) :
    ∀ (t : ℕ) (U : Finset (Fin N)), n / 2 + t * s ≤ U.card →
      ∃ I : Fin t → Finset (Fin N), (∀ j, I j ⊆ U) ∧ (∀ j, (I j).card = s) ∧
        (∀ j, H.IsIndepSet ((I j : Finset (Fin N)) : Set (Fin N))) ∧
        (∀ j j', j ≠ j' → Disjoint (I j) (I j')) := by
  intro t
  induction t with
  | zero =>
    intro U _
    exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0⟩
  | succ t ih =>
    intro U hU
    have hUc : n / 2 ≤ U.card := by omega
    obtain ⟨A, hAU, hAcard, hAind⟩ := exists_indep_subset (H := H) hH hsn hn100 hUc
    have hU' : n / 2 + t * s ≤ (U \ A).card := by
      rw [Finset.card_sdiff_of_subset hAU, hAcard]
      have h1 : n / 2 + t * s + s ≤ U.card := by
        have h2 : (t + 1) * s = t * s + s := by ring
        omega
      omega
    obtain ⟨J, hJsub, hJcard, hJind, hJdis⟩ := ih (U \ A) hU'
    have hJA : ∀ i, Disjoint A (J i) := by
      intro i
      refine Finset.disjoint_left.mpr ?_
      intro a ha haJ
      exact (Finset.mem_sdiff.mp (hJsub i haJ)).2 ha
    have hJsubU : ∀ i, J i ⊆ U := fun i => (hJsub i).trans (Finset.sdiff_subset)
    refine ⟨Fin.cons A J, ?_, ?_, ?_, ?_⟩
    · intro j
      match j with
      | ⟨0, hp⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          rw [h0, Fin.cons_zero]
          exact hAU
      | ⟨i + 1, hp⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [hj, Fin.cons_succ]
          exact hJsubU ⟨i, by omega⟩
    · intro j
      match j with
      | ⟨0, hp⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          rw [h0, Fin.cons_zero]
          exact hAcard
      | ⟨i + 1, hp⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [hj, Fin.cons_succ]
          exact hJcard ⟨i, by omega⟩
    · intro j
      match j with
      | ⟨0, hp⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          rw [h0, Fin.cons_zero]
          exact hAind
      | ⟨i + 1, hp⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [hj, Fin.cons_succ]
          exact hJind ⟨i, by omega⟩
    · intro j j' hne
      match j, j' with
      | ⟨0, hp⟩, ⟨0, hp'⟩ => exact absurd (Fin.ext rfl) hne
      | ⟨0, hp⟩, ⟨i' + 1, hp'⟩ =>
          have h0 : (⟨0, hp⟩ : Fin (t + 1)) = 0 := rfl
          have hj : (⟨i' + 1, hp'⟩ : Fin (t + 1)) = (⟨i', by omega⟩ : Fin t).succ := rfl
          rw [h0, hj, Fin.cons_zero, Fin.cons_succ]
          exact hJA ⟨i', by omega⟩
      | ⟨i + 1, hp⟩, ⟨0, hp'⟩ =>
          have h0 : (⟨0, hp'⟩ : Fin (t + 1)) = 0 := rfl
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          rw [h0, hj, Fin.cons_zero, Fin.cons_succ]
          exact (hJA ⟨i, by omega⟩).symm
      | ⟨i + 1, hp⟩, ⟨i' + 1, hp'⟩ =>
          have hj : (⟨i + 1, hp⟩ : Fin (t + 1)) = (⟨i, by omega⟩ : Fin t).succ := rfl
          have hj' : (⟨i' + 1, hp'⟩ : Fin (t + 1)) = (⟨i', by omega⟩ : Fin t).succ := rfl
          rw [hj, hj', Fin.cons_succ, Fin.cons_succ]
          refine hJdis ⟨i, by omega⟩ ⟨i', by omega⟩ ?_
          intro h
          exact hne (by rw [hj, hj', h])

end Shear

end Erdos1182F

/- ## The two Ramsey bounds -/

namespace Erdos1182F

open Classical

section Ramsey

/-- If `H` has an independent set with at least `n` vertices, then `Hᶜ` contains every star of
cliques on `n` vertices. -/
lemma embed_of_indep {N n s m : ℕ} (H : SimpleGraph (Fin N)) {S : Finset (Fin N)}
    (hS : H.IsIndepSet ((S : Finset (Fin N)) : Set (Fin N))) (hcard : n ≤ S.card) :
    Nonempty (SimpleGraph.Copy (starCliques n s m) Hᶜ) := by
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let φ : Fin n → Fin N := fun i => ((T.equivFin.symm ((finCongr hTcard).symm i) : T) : Fin N)
  have hφT : ∀ i, φ i ∈ T := fun i => (T.equivFin.symm ((finCongr hTcard).symm i)).2
  have hφinj : Function.Injective φ := by
    intro i j hij
    have h1 : (T.equivFin.symm ((finCongr hTcard).symm i) : T)
        = T.equivFin.symm ((finCongr hTcard).symm j) := Subtype.ext hij
    have h2 := congrArg T.equivFin h1
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
    exact (finCongr hTcard).symm.injective h2
  have hSind : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ H.Adj x y :=
    fun x hx y hy hxy => hS (hTS hx) (hTS hy) hxy
  refine ⟨⟨⟨φ, ?_⟩, hφinj⟩⟩
  intro a b hab
  refine (SimpleGraph.compl_adj H (φ a) (φ b)).mpr ⟨fun h => hab.1 (hφinj h), ?_⟩
  exact hSind (φ a) (hφT a) (φ b) (hφT b) (fun h => hab.1 (hφinj h))

/-- The complete bipartite graph with parts `{x | x < n-1}` and `{x | n-1 ≤ x}`. -/
def bipGraph (b n : ℕ) : SimpleGraph (Fin b) where
  Adj x y := (x.val < n - 1 ∧ n - 1 ≤ y.val) ∨ (y.val < n - 1 ∧ n - 1 ≤ x.val)
  symm := ⟨fun x y h => h.symm⟩
  loopless := ⟨fun x h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

/-- Adjacency in the bipartite graph puts the two endpoints on opposite sides. -/
lemma bipGraph_opp {b n : ℕ} {x y : Fin b} (h : (bipGraph b n).Adj x y) :
    (x.val < n - 1 ↔ ¬ (y.val < n - 1)) := by
  constructor
  · intro hx hy
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · intro hy
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- `bipGraph` has no triangle. -/
lemma bipGraph_cliqueFree {b n : ℕ} (hn : 2 ≤ n) : (bipGraph b n).CliqueFree 3 := by
  rintro t ⟨hclique, hcard⟩
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hcard
  have hpq' : (bipGraph b n).Adj p q := hclique (by simp) (by simp) hpq
  have hqr' : (bipGraph b n).Adj q r := hclique (by simp) (by simp) hqr
  have hpr' : (bipGraph b n).Adj p r := hclique (by simp) (by simp) hpr
  have h1 : (p.val < n - 1) ↔ ¬ (q.val < n - 1) := bipGraph_opp hpq'
  have h2 : (q.val < n - 1) ↔ ¬ (r.val < n - 1) := bipGraph_opp hqr'
  have h3 : (p.val < n - 1) ↔ ¬ (r.val < n - 1) := bipGraph_opp hpr'
  by_cases hp : p.val < n - 1
  · have hq : ¬ (q.val < n - 1) := h1.mp hp
    have hr : r.val < n - 1 := by
      by_contra hr
      exact hq (h2.mpr hr)
    exact h3.mp hp hr
  · have hq : q.val < n - 1 := by
      by_contra hq
      exact hp (h1.mpr hq)
    have hr : ¬ (r.val < n - 1) := h2.mp hq
    exact hp (h3.mpr hr)

/-- The bipartite graph contains no triangle, so it does not contain `K₃`. -/
lemma bipGraph_not_contained {b n : ℕ} (hn : 2 ≤ n) :
    ¬ SimpleGraph.IsContained (⊤ : SimpleGraph (Fin 3)) (bipGraph b n) := by
  intro h
  have h' : SimpleGraph.IsContained (SimpleGraph.completeGraph (Fin 3)) (bipGraph b n) := by
    rwa [SimpleGraph.completeGraph_eq_top]
  exact (SimpleGraph.IsContained.not_cliqueFree (G := bipGraph b n) h')
    (bipGraph_cliqueFree hn)

/-- Adjacency in the complement of the bipartite graph keeps the side. -/
lemma bipGraph_step {b n : ℕ} {x y : Fin b} (h : (bipGraph b n)ᶜ.Adj x y) :
    (x.val < n - 1 ↔ y.val < n - 1) := by
  have hna : ¬ (bipGraph b n).Adj x y := ((SimpleGraph.compl_adj (bipGraph b n) x y).mp h).2
  constructor
  · intro hx
    by_contra hy
    exact hna (Or.inl ⟨hx, by omega⟩)
  · intro hy
    by_contra hx
    exact hna (Or.inr ⟨hy, by omega⟩)

/-- Along a walk of the complement of the bipartite graph the side of a vertex does not change. -/
lemma bipGraph_walk_side {b n : ℕ} {x y : Fin b} (p : (bipGraph b n)ᶜ.Walk x y) :
    (x.val < n - 1 ↔ y.val < n - 1) := by
  induction p with
  | nil => exact Iff.rfl
  | @cons u v w hxy p' ih => exact (bipGraph_step hxy).trans ih

/-- The set of small vertices is bounded by `n - 1`. -/
lemma card_filter_lt {b n : ℕ} :
    (Finset.univ.filter (fun x : Fin b => x.val < n - 1)).card ≤ n - 1 := by
  have himg : (Finset.univ.filter (fun x : Fin b => x.val < n - 1)).image Fin.val
      ⊆ Finset.range (n - 1) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp [hu]
  calc (Finset.univ.filter (fun x : Fin b => x.val < n - 1)).card
      = ((Finset.univ.filter (fun x : Fin b => x.val < n - 1)).image Fin.val).card := by
        rw [Finset.card_image_of_injective _ Fin.val_injective]
    _ ≤ (Finset.range (n - 1)).card := Finset.card_le_card himg
    _ = n - 1 := Finset.card_range _

/-- The set of large vertices is bounded by `n - 1` as soon as `b ≤ 2n-2`. -/
lemma card_filter_ge {b n : ℕ} (hb : b ≤ 2 * n - 2) (hn : 2 ≤ n) :
    (Finset.univ.filter (fun x : Fin b => ¬ x.val < n - 1)).card ≤ n - 1 := by
  have himg : (Finset.univ.filter (fun x : Fin b => ¬ x.val < n - 1)).image Fin.val
      ⊆ Finset.Ico (n - 1) b := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨-, hu2⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_Ico.mpr ⟨by omega, u.isLt⟩
  calc (Finset.univ.filter (fun x : Fin b => ¬ x.val < n - 1)).card
      = ((Finset.univ.filter (fun x : Fin b => ¬ x.val < n - 1)).image Fin.val).card := by
        rw [Finset.card_image_of_injective _ Fin.val_injective]
    _ ≤ (Finset.Ico (n - 1) b).card := Finset.card_le_card himg
    _ = b - (n - 1) := Nat.card_Ico _ _
    _ ≤ n - 1 := by
      have h2 : (n - 1) + (n - 1) = 2 * n - 2 := by omega
      omega

/-- On `2n-2` vertices the complement of the bipartite graph does not contain the star of
cliques on `n` vertices. -/
lemma starCliques_not_contained {n s m b : ℕ} (hn : 2 ≤ n) (hb : b ≤ 2 * n - 2) :
    ¬ SimpleGraph.IsContained (starCliques n s m) ((bipGraph b n)ᶜ) := by
  rintro ⟨φ⟩
  have hn0 : 0 < n := by omega
  have hconn : (starCliques n s m).Connected := starCliques_connected (s := s) (m := m) hn0
  obtain ⟨x0⟩ : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hreach : ∀ z : Fin n, (bipGraph b n)ᶜ.Reachable (φ x0) (φ z) := by
    intro z
    obtain ⟨p⟩ := hconn x0 z
    exact ⟨p.map φ.toHom⟩
  have hside : ∀ z : Fin n, (((φ z : Fin b)).val < n - 1 ↔ ((φ x0 : Fin b)).val < n - 1) := by
    intro z
    obtain ⟨q⟩ := hreach z
    exact (bipGraph_walk_side q).symm
  have himgcard : (Finset.univ.image (fun z : Fin n => (φ z : Fin b))).card = n := by
    have hinj : Function.Injective (fun z : Fin n => (φ z : Fin b)) := fun a b h => φ.injective h
    rw [Finset.card_image_of_injective _ hinj]
    simp
  by_cases hc : ((φ x0 : Fin b)).val < n - 1
  · have himg : (Finset.univ.image (fun z : Fin n => (φ z : Fin b)))
        ⊆ Finset.univ.filter (fun x : Fin b => x.val < n - 1) := by
      intro x hx
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hside z).mpr hc
    have h1 := Finset.card_le_card himg
    rw [himgcard] at h1
    have h2 := card_filter_lt (b := b) (n := n)
    omega
  · have himg : (Finset.univ.image (fun z : Fin n => (φ z : Fin b)))
        ⊆ Finset.univ.filter (fun x : Fin b => ¬ x.val < n - 1) := by
      intro x hx
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hc ((hside z).mp h)
    have h1 := Finset.card_le_card himg
    rw [himgcard] at h1
    have h2 := card_filter_ge hb hn
    omega

/-- **Upper Ramsey bound**: on `2n-1` vertices every graph either contains `K₃` or its complement
contains the star of cliques. -/
lemma ramsey_mem {n s m : ℕ} (hn : 2 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (hms2 : m * s ≤ (n - 1) / 2)
    (hsn : (s : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)))
    (hn100 : 100 ≤ n / 2) :
    ∀ C : SimpleGraph (Fin (2 * n - 1)),
      SimpleGraph.IsContained (⊤ : SimpleGraph (Fin 3)) C ∨
        SimpleGraph.IsContained (starCliques n s m) Cᶜ := by
  intro C
  by_cases hC : SimpleGraph.IsContained (⊤ : SimpleGraph (Fin 3)) C
  · exact Or.inl hC
  · right
    have hH : C.CliqueFree 3 := by
      by_contra hcc
      have h2 : SimpleGraph.IsContained (SimpleGraph.completeGraph (Fin 3)) C :=
        (SimpleGraph.not_cliqueFree_iff_top_isContained (G := C) 3).mp hcc
      exact hC (by rwa [SimpleGraph.completeGraph_eq_top] at h2)
    by_cases hdeg : ∃ v : Fin (2 * n - 1), n ≤ C.degree v
    · obtain ⟨v, hv⟩ := hdeg
      have hNind : C.IsIndepSet (C.neighborSet v) :=
        SimpleGraph.isIndepSet_neighborSet_of_triangleFree C hH v
      have hNcard : n ≤ (C.neighborFinset v).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact hv
      exact embed_of_indep C (by simpa using hNind) hNcard
    · push Not at hdeg
      have hn0 : 0 < n := by omega
      have hN0 : 0 < 2 * n - 1 := by omega
      set u : Fin (2 * n - 1) := ⟨0, hN0⟩ with hu_def
      set U : Finset (Fin (2 * n - 1)) := (Finset.univ.erase u) \ C.neighborFinset u with hU_def
      have hsub : C.neighborFinset u ⊆ Finset.univ.erase u := by
        intro x hx
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
        intro hxu
        have hadj : C.Adj u x := (SimpleGraph.mem_neighborFinset C u x).mp hx
        rw [hxu] at hadj
        exact C.loopless.irrefl u hadj
      have hdegU : (C.neighborFinset u).card ≤ n - 1 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact Nat.le_sub_one_of_lt (hdeg u)
      have huU : u ∉ U := by simp [hU_def]
      have hUneigh : ∀ w ∈ U, ¬ C.Adj u w := by
        intro w hw hadj
        have h1 : w ∈ C.neighborFinset u := (SimpleGraph.mem_neighborFinset C u w).mpr hadj
        simp only [hU_def, Finset.mem_sdiff] at hw
        exact hw.2 h1
      have hUcard_eq : U.card = (2 * n - 1 - 1) - (C.neighborFinset u).card := by
        rw [hU_def, Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem (Finset.mem_univ u)]
        simp
      have hUcard : n - 1 ≤ U.card := by
        rw [hUcard_eq]
        omega
      obtain ⟨I, hIsub, hIcard, hIind, hIdis⟩ :=
        extract_indep_sets (H := C) hH hsn hn100 m U (by omega)
      set B : Finset (Fin (2 * n - 1)) := Finset.univ.biUnion I with hB_def
      have hBcard : B.card = m * s := by
        rw [hB_def, Finset.card_biUnion]
        · simp [hIcard]
        · intro j _ j' _ hne
          exact hIdis j j' hne
      have hBU : B ⊆ U := by
        intro x hx
        rw [hB_def] at hx
        obtain ⟨j, -, hxj⟩ := Finset.mem_biUnion.mp hx
        exact hIsub j hxj
      have hrestcard : n - 1 - m * s ≤ (U \ B).card := by
        rw [Finset.card_sdiff_of_subset hBU, hBcard]
        omega
      have hBdis : ∀ j, Disjoint (U \ B) (I j) := by
        intro j
        refine Finset.disjoint_left.mpr ?_
        intro x hx hxj
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hxj⟩)
      exact starCliques_embed C hs hm (by omega) u U huU hUneigh I hIsub hIcard hIind hIdis
        (U \ B) Finset.sdiff_subset hBdis hrestcard

/-- **Upper Ramsey bound** for the star of cliques. -/
theorem ramsey_upper {n s m : ℕ} (hn : 2 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (hms2 : m * s ≤ (n - 1) / 2)
    (hsn : (s : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)))
    (hn100 : 100 ≤ n / 2) :
    SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (starCliques n s m) ≤ 2 * n - 1 :=
  Nat.sInf_le (ramsey_mem hn hs hm hms2 hsn hn100)

/-- **Lower Ramsey bound** for the star of cliques. -/
theorem ramsey_lower {n s m : ℕ} (hn : 2 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (hms2 : m * s ≤ (n - 1) / 2)
    (hsn : (s : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)))
    (hn100 : 100 ≤ n / 2) :
    2 * n - 1 ≤ SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (starCliques n s m) := by
  refine le_csInf ⟨2 * n - 1, ramsey_mem hn hs hm hms2 hsn hn100⟩ ?_
  intro b hb
  by_contra hlt
  push Not at hlt
  have hb' : b ≤ 2 * n - 2 := by omega
  rcases hb (bipGraph b n) with h1 | h1
  · exact bipGraph_not_contained hn h1
  · exact starCliques_not_contained hn hb' h1

end Ramsey

end Erdos1182F

/- ## The numerical choice of parameters and the asymptotic estimate -/

open Erdos1182

namespace Erdos1182F

open Filter

noncomputable def sOf (n : ℕ) : ℕ :=
  ⌊(1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ))⌋₊

noncomputable def mOf (n : ℕ) : ℕ := (n - 1) / (2 * sOf n)

lemma sOf_le (n : ℕ) :
    (sOf n : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) :=
  Nat.floor_le (by positivity)

lemma sOf_gt (n : ℕ) :
    (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) < (sOf n : ℝ) + 1 :=
  Nat.lt_floor_add_one _

lemma mOf_lower (n : ℕ) (hn : 1 ≤ n) (hs : 0 < sOf n) :
    ((n : ℝ) - 1) / (2 * (sOf n : ℝ)) - 1 < (mOf n : ℝ) := by
  have hSpos : (0 : ℝ) < 2 * (sOf n : ℝ) := by
    have : (0 : ℝ) < sOf n := by exact_mod_cast hs
    linarith
  have hnat : (n - 1 : ℕ) < (mOf n + 1) * (2 * sOf n) := by
    have hdm : 2 * sOf n * (mOf n) + (n - 1) % (2 * sOf n) = n - 1 :=
      Nat.div_add_mod (n - 1) (2 * sOf n)
    have hmod : (n - 1) % (2 * sOf n) < 2 * sOf n := Nat.mod_lt _ (by omega)
    have hm : mOf n = (n - 1) / (2 * sOf n) := rfl
    rw [hm] at hdm ⊢
    nlinarith
  have hcast : ((n : ℝ) - 1) < ((mOf n : ℝ) + 1) * (2 * (sOf n : ℝ)) := by
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]
      norm_num
    have := hnat
    have h2 : ((n - 1 : ℕ) : ℝ) < (((mOf n + 1) * (2 * sOf n) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith
  have hstep : ((n : ℝ) - 1) / (2 * (sOf n : ℝ)) < (mOf n : ℝ) + 1 := by
    rw [div_lt_iff₀ hSpos]
    linarith
  linarith

lemma log_four_le_two : Real.log 4 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [h2]
  nlinarith [Real.exp_one_lt_three, Real.exp_one_gt_d9, Real.exp_pos 1]

lemma four_le_log {n : ℕ} (hn : 10 ^ 6 ≤ n) : (4 : ℝ) ≤ Real.log n := by
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h4]
  have h81 : Real.exp 1 ^ 4 < 81 := by
    have h := pow_lt_pow_left₀ (show Real.exp 1 < 3 by linarith [Real.exp_one_lt_three])
      (le_of_lt (Real.exp_pos 1)) (by norm_num : (4 : ℕ) ≠ 0)
    have h3 : (3 : ℝ) ^ 4 = 81 := by norm_num
    linarith
  linarith

theorem asymp :
    ∀ᶠ n : ℕ in atTop, (1 / 100000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
      ≤ (mOf n : ℝ) * (sOf n : ℝ) * ((sOf n : ℝ) - 1) / 2 := by
  filter_upwards [eventually_ge_atTop (10 ^ 6 : ℕ)] with n hn
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set N : ℝ := ((n / 2 : ℕ) : ℝ) with hNdef
  set L : ℝ := Real.log N with hLdef
  set T : ℝ := Real.sqrt (N * L) with hTdef
  set S : ℝ := (sOf n : ℝ) with hSdef
  set M : ℝ := (mOf n : ℝ) with hMdef
  have hN1 : (500000 : ℝ) ≤ N := by
    have h2 : 500000 ≤ n / 2 := by omega
    rw [hNdef]
    exact_mod_cast h2
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have hexp : Real.exp 1 ≤ N := by
      have := Real.exp_one_lt_three
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hT1 : (700 : ℝ) ≤ T := by
    rw [hTdef]
    have h1 : (700 : ℝ) ^ 2 ≤ N * L := by nlinarith
    calc (700 : ℝ) = Real.sqrt (700 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (N * L) := Real.sqrt_le_sqrt h1
  have harg : ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ) = N * L := by
    rw [← hNdef, ← hLdef]
  have hSlow : T / 40 - 1 < S := by
    have h := sOf_gt n
    rw [harg, ← hSdef, ← hTdef] at h
    linarith
  have hSup : S ≤ T / 40 := by
    have h := sOf_le n
    rw [harg, ← hSdef, ← hTdef] at h
    linarith
  have hSpos : (0 : ℝ) < S := by linarith
  have hS2 : (2 : ℝ) ≤ S := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hNle : N ≤ (n : ℝ) := by
    rw [hNdef]
    exact_mod_cast Nat.div_le_self n 2
  have hLle : L ≤ N := by
    rw [hLdef]
    exact Real.log_le_self (le_of_lt hNpos)
  have hTle : T ≤ 5 * (n : ℝ) := by
    rw [hTdef]
    have h1 : N * L ≤ (5 * (n : ℝ)) ^ 2 := by
      have h2 : N * L ≤ N * N := mul_le_mul_of_nonneg_left hLle (le_of_lt hNpos)
      nlinarith
    calc Real.sqrt (N * L) ≤ Real.sqrt ((5 * (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 5 * (n : ℝ) := Real.sqrt_sq (by linarith)
  have hNge : (n : ℝ) / 4 ≤ N := by
    have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hdm : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
    have he : ((n / 2 : ℕ) : ℝ) = ((n : ℝ) - ((n % 2 : ℕ) : ℝ)) / 2 := by
      have h2 : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by
        have h3 : ((n : ℕ) : ℝ) = ((2 * (n / 2) + n % 2 : ℕ) : ℝ) := by rw [hdm]
        push_cast at h3 ⊢
        linarith
      linarith
    rw [hNdef, he]
    have : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      have h2 : n % 2 ≤ 1 := by omega
      exact_mod_cast h2
    linarith
  have hlogN : Real.log n / 2 ≤ L := by
    rw [hLdef]
    have h1 : Real.log ((n : ℝ) / 4) ≤ Real.log N :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log ((n : ℝ) / 4) = Real.log n - Real.log 4 :=
      Real.log_div (by linarith) (by norm_num)
    have h3 : Real.log 4 ≤ 2 := log_four_le_two
    have h4 : (4 : ℝ) ≤ Real.log n := four_le_log hn
    linarith
  have hMlow : ((n : ℝ) - 1) / (2 * S) - 1 < M := by
    rw [hMdef]
    have hsR : (0 : ℝ) < (sOf n : ℝ) := by rw [← hSdef]; exact hSpos
    have hs : 0 < sOf n := by exact_mod_cast hsR
    exact mOf_lower n hn1 hs
  have hA : (n : ℝ) / 4 ≤ M * S := by
    have h1 : (((n : ℝ) - 1) / (2 * S) - 1) * S < M * S :=
      mul_lt_mul_of_pos_right hMlow hSpos
    have h2 : (((n : ℝ) - 1) / (2 * S) - 1) * S = ((n : ℝ) - 1) / 2 - S := by
      field_simp
    rw [h2] at h1
    have h3 : S ≤ (n : ℝ) / 8 := by
      have h4 : T / 40 ≤ (n : ℝ) / 8 := by linarith
      linarith
    nlinarith
  have hB : T / 80 ≤ S - 1 := by linarith
  have hC : Real.sqrt ((n : ℝ) * Real.log n / 8) ≤ T := by
    rw [hTdef]
    apply Real.sqrt_le_sqrt
    have h1 : (n : ℝ) / 4 ≤ N := hNge
    have h2 : Real.log n / 2 ≤ L := hlogN
    have h3 : (0 : ℝ) < (n : ℝ) / 4 := by linarith
    have h4 : (0 : ℝ) < Real.log n / 2 := by
      have := four_le_log hn
      linarith
    have hprod := mul_le_mul h1 h2 (le_of_lt h4) (le_of_lt hNpos)
    nlinarith
  have hn32 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hAeq : (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
      = (n : ℝ) * Real.sqrt ((n : ℝ) * Real.log n / 8) * Real.sqrt 8 := by
    rw [hn32, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    have h8 : Real.sqrt 8 ≠ 0 := by positivity
    field_simp
  have hsqrt8 : 640 * Real.sqrt 8 ≤ 100000 := by
    have h1 : Real.sqrt 8 ≤ 3 := by
      calc Real.sqrt 8 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
        _ = 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    nlinarith
  have hY : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt ((n : ℝ) * Real.log n / 8) := by positivity
  have hstep1 : (1 / 100000 : ℝ) * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n))
      ≤ (n : ℝ) * Real.sqrt ((n : ℝ) * Real.log n / 8) / 640 := by
    rw [hAeq]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 640)]
    nlinarith [hsqrt8, hY]
  have hstep2 : (n : ℝ) * Real.sqrt ((n : ℝ) * Real.log n / 8) / 640
      ≤ M * S * (S - 1) / 2 := by
    have h1 : (n : ℝ) / 4 * (T / 80) / 2 ≤ M * S * (S - 1) / 2 := by
      have hmul : (n : ℝ) / 4 * (T / 80) ≤ M * S * (S - 1) :=
        mul_le_mul hA hB (by linarith) (by linarith)
      linarith
    have h2 : (n : ℝ) / 4 * (T / 80) / 2 = (n : ℝ) * T / 640 := by ring
    have h3 : (n : ℝ) * Real.sqrt ((n : ℝ) * Real.log n / 8) / 640 ≤ (n : ℝ) * T / 640 := by
      have h4 : (n : ℝ) * Real.sqrt ((n : ℝ) * Real.log n / 8) ≤ (n : ℝ) * T :=
        mul_le_mul_of_nonneg_left hC (le_of_lt hnpos)
      linarith
    linarith
  calc (1 / 100000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
      = (1 / 100000 : ℝ) * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) := by ring
    _ ≤ M * S * (S - 1) / 2 := hstep1.trans hstep2



/-- The edge count of a connected `3`-good graph on `n` vertices is at most `f n`. -/
theorem edgeSet_ncard_le_f {n : ℕ} {G : SimpleGraph (Fin n)} (hconn : G.Connected)
    (hgood : IsTriangleGood G) : G.edgeSet.ncard ≤ f n := by
  classical
  unfold f
  refine le_csSup ?_ ⟨G, hconn, rfl, hgood⟩
  refine ⟨n.choose 2, ?_⟩
  rintro q ⟨H, -, hq, -⟩
  rw [← hq, edgeSet_ncard_eq_edgeFinset H]
  simpa using SimpleGraph.card_edgeFinset_le_card_choose_two (G := H)

theorem sOf_le' (n : ℕ) :
    (sOf n : ℝ) ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) :=
  sOf_le n

/-- All the numerical facts about the chosen parameters, eventually in `n`. -/
theorem starCliques_ready : ∀ᶠ n : ℕ in atTop,
    ((1 / 100000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
        ≤ (mOf n : ℝ) * (sOf n : ℝ) * ((sOf n : ℝ) - 1) / 2
      ∧ 0 < sOf n ∧ 0 < mOf n ∧ mOf n * sOf n ≤ (n - 1) / 2) := by
  filter_upwards [asymp, eventually_ge_atTop (10 ^ 6 : ℕ)] with n hest hn
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set N : ℝ := ((n / 2 : ℕ) : ℝ) with hNdef
  set L : ℝ := Real.log N with hLdef
  set T : ℝ := Real.sqrt (N * L) with hTdef
  set S : ℝ := (sOf n : ℝ) with hSdef
  set M : ℝ := (mOf n : ℝ) with hMdef
  have harg : ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ) = N * L := by
    rw [← hNdef, ← hLdef]
  have hSlow : T / 40 - 1 < S := by
    have h := sOf_gt n
    rw [harg, ← hSdef, ← hTdef] at h
    linarith
  have hSup : S ≤ T / 40 := by
    have h := sOf_le n
    rw [harg, ← hSdef, ← hTdef] at h
    linarith
  have hN1 : (500000 : ℝ) ≤ N := by
    have h2 : 500000 ≤ n / 2 := by omega
    rw [hNdef]
    exact_mod_cast h2
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have hexp : Real.exp 1 ≤ N := by
      have := Real.exp_one_lt_three
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hT1 : (700 : ℝ) ≤ T := by
    rw [hTdef]
    have h1 : (700 : ℝ) ^ 2 ≤ N * L := by nlinarith
    calc (700 : ℝ) = Real.sqrt (700 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (N * L) := Real.sqrt_le_sqrt h1
  have hTpos : (0 : ℝ) < T := by linarith
  have hSpos : (0 : ℝ) < S := by linarith
  have hS16 : (16 : ℝ) ≤ S := by linarith
  have hLle : L ≤ N := by
    rw [hLdef]
    exact Real.log_le_self (le_of_lt hNpos)
  have hNle : N ≤ (n : ℝ) := by
    rw [hNdef]
    exact_mod_cast Nat.div_le_self n 2
  have hTle : T ≤ 5 * (n : ℝ) := by
    rw [hTdef]
    have h1 : N * L ≤ (5 * (n : ℝ)) ^ 2 := by
      have h2 : N * L ≤ N * N := mul_le_mul_of_nonneg_left hLle (le_of_lt hNpos)
      nlinarith
    calc Real.sqrt (N * L) ≤ Real.sqrt ((5 * (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 5 * (n : ℝ) := Real.sqrt_sq (by linarith)
  have hSle : S ≤ (n : ℝ) / 8 := by
    have h4 : T / 40 ≤ (n : ℝ) / 8 := by linarith
    linarith
  have hMlow : ((n : ℝ) - 1) / (2 * S) - 1 < M := by
    rw [hMdef]
    have hsR : (0 : ℝ) < (sOf n : ℝ) := by rw [← hSdef]; exact hSpos
    have hs : 0 < sOf n := by exact_mod_cast hsR
    exact mOf_lower n (by omega) hs
  have hMpos : (0 : ℝ) < M := by
    have h1 : (3 : ℝ) ≤ ((n : ℝ) - 1) / (2 * S) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  have hsOf : 0 < sOf n := by
    have hsR : (0 : ℝ) < (sOf n : ℝ) := by rw [← hSdef]; exact hSpos
    exact_mod_cast hsR
  have hmOf : 0 < mOf n := by
    have hmR : (0 : ℝ) < (mOf n : ℝ) := by rw [← hMdef]; exact hMpos
    exact_mod_cast hmR
  have hms2 : mOf n * sOf n ≤ (n - 1) / 2 := by
    have h := Nat.div_mul_le_self ((n - 1) / 2) (sOf n)
    have h2 : mOf n = ((n - 1) / 2) / sOf n := by
      rw [mOf, ← Nat.div_div_eq_div_mul]
    rw [h2]
    exact h
  exact ⟨hest, hsOf, hmOf, hms2⟩

/-- The main lower bound, eventually in `n`. -/
theorem f_lower_asymp : ∀ᶠ n : ℕ in atTop,
    (1 / 200000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) < (f n : ℝ) := by
  filter_upwards [starCliques_ready, eventually_ge_atTop (10 ^ 6 : ℕ)] with n hready hn
  obtain ⟨hest, hsOf, hmOf, hms2⟩ := hready
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn2 : 2 ≤ n := by omega
  have hn100 : 100 ≤ n / 2 := by omega
  have hms : mOf n * sOf n < n := by omega
  have hsn : (sOf n : ℝ)
      ≤ (1 / 40) * Real.sqrt (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) := sOf_le n
  have hgood : IsTriangleGood (starCliques n (sOf n) (mOf n)) := by
    unfold IsTriangleGood
    exact le_antisymm (ramsey_upper hn2 hsOf hmOf hms2 hsn hn100)
      (ramsey_lower hn2 hsOf hmOf hms2 hsn hn100)
  have hconn : (starCliques n (sOf n) (mOf n)).Connected :=
    starCliques_connected (s := sOf n) (m := mOf n) (by omega)
  have hfle : ((starCliques n (sOf n) (mOf n)).edgeSet.ncard : ℝ) ≤ (f n : ℝ) := by
    have h := edgeSet_ncard_le_f hconn hgood
    exact_mod_cast h
  have hedge := starCliques_edge_lower (n := n) (s := sOf n) (m := mOf n) hms hsOf
  have hXpos : (0 : ℝ) < (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by
    have h1 : (0 : ℝ) < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have h2 : (0 : ℝ) < Real.sqrt (Real.log n) := by
      rw [Real.sqrt_pos]
      have := four_le_log hn
      linarith
    positivity
  have hlt : (1 / 200000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
      < (1 / 100000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by
    have h1 : (1 / 200000 : ℝ) < 1 / 100000 := by norm_num
    calc (1 / 200000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
        = (1 / 200000) * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) := by ring
      _ < (1 / 100000) * ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)) :=
          mul_lt_mul_of_pos_right h1 hXpos
      _ = (1 / 100000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := by ring
  calc (1 / 200000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n)
      < (1 / 100000 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n) := hlt
    _ ≤ (mOf n : ℝ) * (sOf n : ℝ) * ((sOf n : ℝ) - 1) / 2 := hest
    _ ≤ ((starCliques n (sOf n) (mOf n)).edgeSet.ncard : ℝ) := hedge
    _ ≤ (f n : ℝ) := hfle


end Erdos1182F


theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.f_lower := by
  refine ⟨1 / 200000, by norm_num, ?_⟩
  exact Erdos1182F.f_lower_asymp
