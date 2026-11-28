/-
Four cuts for the fixed three-agent demand multiset (1,2,4)/7.
Source: Erel Segal-Halevi, Cake-Cutting with Different Entitlements,
arXiv:1803.05470v3, final Conjecture of Section 4.
https://arxiv.org/abs/1803.05470

For three nonatomic probability measures supported on [0,1], the theorem
constructs a division with at most four cuts and own-measure guarantees
2/7, 1/7, 4/7 in agent order B,C,H. The complete closed theorem is
CakeSevenUnconditional.fixed_three_agent_division. It has no certificate
or other auxiliary mathematical premise.

The proof uses two seven-mark quantile systems, all 1716 circular run orders,
and exact finite rational certificates checked by ordinary Lean decide.
The source body below is preserved unchanged. See README.txt for the proof
outline and reproduction steps, and verification.json for audit receipts.
This establishes the specifically identified demand case, not the full
all-agent conjecture or the stronger circle Conjecture 3.1 of arXiv:1909.07141.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.FinCases
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Aesop
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin

open Set MeasureTheory
open scoped BigOperators Topology

namespace CakeWeightedChoice

open scoped BigOperators

theorem weighted_cost_swap {P J : Type*} [Fintype P] [Fintype J] [DecidableEq J]
    (w : P → ℝ) (a : P → Finset J) (g : J → ℝ) :
    (∑ p, w p * ∑ j ∈ a p, g j) =
      ∑ j, g j * ∑ p, if j ∈ a p then w p else 0 := by
  classical
  calc
    (∑ p, w p * ∑ j ∈ a p, g j) =
        ∑ p, ∑ j, if j ∈ a p then w p * g j else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Fintype.sum_ite_mem]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = ∑ j, ∑ p, if j ∈ a p then w p * g j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j, g j * ∑ p, if j ∈ a p then w p else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp [mul_comm]

theorem exists_supported_cost_le {P J : Type*} [Fintype P] [Fintype J]
    [DecidableEq J] (w : P → ℝ) (a : P → Finset J) (g : J → ℝ)
    (q t : ℝ) (hw : ∀ p, 0 ≤ w p) (hq : 0 < q)
    (hweights : ∑ p, w p = q) (hg : ∀ j, 0 ≤ g j)
    (hgap : ∑ j, g j = 1)
    (hcover : ∀ j, (∑ p, if j ∈ a p then w p else 0) ≤ t * q) :
    ∃ p, 0 < w p ∧ (∑ j ∈ a p, g j) ≤ t := by
  classical
  have hsum : (∑ p, w p * ∑ j ∈ a p, g j) ≤ t * q := by
    rw [weighted_cost_swap]
    calc
      (∑ j, g j * ∑ p, if j ∈ a p then w p else 0) ≤
          ∑ j, g j * (t * q) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcover j) (hg j)
      _ = t * q := by rw [← Finset.sum_mul, hgap, one_mul]
  have hpos : ∃ p, 0 < w p := by
    by_contra! h
    have hz : (∑ p, w p) ≤ 0 := Finset.sum_nonpos (fun p hp => h p)
    linarith
  obtain ⟨p₀, hp₀⟩ := hpos
  by_contra! hfail
  have hlt : (∑ p, w p * t) < ∑ p, w p * ∑ j ∈ a p, g j := by
    apply Finset.sum_lt_sum
    · intro p hp
      by_cases hwp : 0 < w p
      · exact (mul_lt_mul_of_pos_left (hfail p hwp) hwp).le
      · have hz : w p = 0 := le_antisymm (le_of_not_gt hwp) (hw p)
        simp [hz]
    · exact ⟨p₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hfail p₀ hp₀) hp₀⟩
  rw [← Finset.sum_mul, hweights] at hlt
  linarith

theorem choose_of_natural_cover {P J : Type*} [Fintype P] [Fintype J]
    [DecidableEq J] (n : P → ℕ) (a : P → Finset J) (g : J → ℝ) (q : ℕ)
    (hq : 0 < q) (hweights : ∑ p, n p = q) (hg : ∀ j, 0 ≤ g j)
    (hgap : ∑ j, g j = 1)
    (hcover : ∀ j, 7 * (∑ p, if j ∈ a p then n p else 0) ≤ 3 * q) :
    ∃ p, 0 < n p ∧ (∑ j ∈ a p, g j) ≤ (3 / 7 : ℝ) := by
  classical
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hwR : ∑ p, (n p : ℝ) = (q : ℝ) := by exact_mod_cast hweights
  have hcR : ∀ j, (∑ p, if j ∈ a p then (n p : ℝ) else 0) ≤ (3 / 7 : ℝ) * q := by
    intro j
    have hz : (7 : ℝ) * (∑ p, if j ∈ a p then (n p : ℝ) else 0) ≤ 3 * (q : ℝ) := by
      exact_mod_cast hcover j
    linarith
  obtain ⟨p, hp, hcost⟩ := exists_supported_cost_le
    (fun p => (n p : ℝ)) a g q (3 / 7) (fun p => Nat.cast_nonneg _) hqR hwR hg hgap hcR
  exact ⟨p, by exact_mod_cast hp, hcost⟩

end CakeWeightedChoice


namespace CakeQuantileSeven

open scoped BigOperators


abbrev Certificate := List ℕ × ℕ × List (ℕ × ℕ × ℕ)

def compositions : ℕ → ℕ → List (List ℕ)
  | n, 0 => if n = 0 then [[]] else []
  | n, k + 1 => (List.range (n + 1)).flatMap fun a =>
      (compositions (n - a) k).map (a :: ·)

def redPositions (runs : List ℕ) : List ℕ :=
  (runs.scanl (fun p a => p + a + 1) 0).take 7

def bluePositions (runs : List ℕ) : List ℕ :=
  (List.range 14).filter fun p => !(redPositions runs).contains p

def gapInArc (start stop gap : ℕ) : Bool :=
  if start < stop then decide (start ≤ gap ∧ gap < stop)
  else decide (start ≤ gap ∨ gap < stop)

def checkCertificate (c : Certificate) : Bool :=
  let red := redPositions c.1
  let blue := bluePositions c.1
  let denominator := c.2.1
  let entries := c.2.2
  let redArc := fun e : ℕ × ℕ × ℕ => fun g : ℕ =>
    gapInArc (red.getD e.1 0) (red.getD ((e.1 + 2) % 7) 0) g
  let blueArc := fun e : ℕ × ℕ × ℕ => fun g : ℕ =>
    gapInArc (blue.getD e.2.1 0) (blue.getD ((e.2.1 + 1) % 7) 0) g
  decide (c.1.length = 7 ∧ c.1.sum = 7 ∧ 0 < denominator) &&
    entries.all (fun e => decide (e.1 < 7 ∧ e.2.1 < 7 ∧ 0 < e.2.2) &&
      (List.range 14).all (fun g => !(redArc e g && blueArc e g))) &&
    decide ((entries.map (fun e => e.2.2)).sum = denominator) &&
    (List.range 14).all (fun g => decide
      (7 * (entries.map (fun e => if redArc e g || blueArc e g then e.2.2 else 0)).sum
        ≤ 3 * denominator))

def redGap (runs : List ℕ) (i gap : ℕ) : Bool :=
  gapInArc ((redPositions runs).getD i 0)
    ((redPositions runs).getD ((i + 2) % 7) 0) gap

def blueGap (runs : List ℕ) (j gap : ℕ) : Bool :=
  gapInArc ((bluePositions runs).getD j 0)
    ((bluePositions runs).getD ((j + 1) % 7) 0) gap

theorem sum_get_map {E R : Type*} [AddCommMonoid R] (l : List E) (f : E → R) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = (l.map f).sum
  rw [← List.map_ofFn, List.ofFn_get]

theorem certificate_gap_choice (c : Certificate) (hc : checkCertificate c = true)
    (g : Fin 14 → ℝ) (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    ∃ i j : Fin 7,
      (∀ k : Fin 14, (redGap c.1 i.val k.val && blueGap c.1 j.val k.val) = false) ∧
      (∑ k : Fin 14, if redGap c.1 i.val k.val || blueGap c.1 j.val k.val
        then g k else 0) ≤ (3 / 7 : ℝ) := by
  classical
  have H := hc
  unfold checkCertificate at H
  dsimp only at H
  obtain ⟨H₃, hcoverAll⟩ := Bool.and_eq_true_iff.mp H
  obtain ⟨H₂, hweightsDec⟩ := Bool.and_eq_true_iff.mp H₃
  obtain ⟨hshapeDec, hentriesAll⟩ := Bool.and_eq_true_iff.mp H₂
  have hshape : c.1.length = 7 ∧ c.1.sum = 7 ∧ 0 < c.2.1 :=
    of_decide_eq_true hshapeDec
  have hweights : (c.2.2.map (fun e => e.2.2)).sum = c.2.1 :=
    of_decide_eq_true hweightsDec
  have hentry : ∀ e ∈ c.2.2,
      e.1 < 7 ∧ e.2.1 < 7 ∧ 0 < e.2.2 ∧
        ∀ k : Fin 14, (redGap c.1 e.1 k.val && blueGap c.1 e.2.1 k.val) = false := by
    intro e he
    have raw := List.all_eq_true.mp hentriesAll e he
    obtain ⟨hboundDec, hdisjointAll⟩ := Bool.and_eq_true_iff.mp raw
    have hbound : e.1 < 7 ∧ e.2.1 < 7 ∧ 0 < e.2.2 :=
      of_decide_eq_true hboundDec
    refine ⟨hbound.1, hbound.2.1, hbound.2.2, ?_⟩
    intro k
    have hd := List.all_eq_true.mp hdisjointAll k.val (List.mem_range.mpr k.isLt)
    simpa only [redGap, blueGap, Bool.not_eq_true'] using hd
  have hcoverage : ∀ k : Fin 14,
      7 * (c.2.2.map (fun e => if redGap c.1 e.1 k.val || blueGap c.1 e.2.1 k.val
        then e.2.2 else 0)).sum ≤ 3 * c.2.1 := by
    intro k
    have ht := List.all_eq_true.mp hcoverAll k.val (List.mem_range.mpr k.isLt)
    exact of_decide_eq_true ht
  let n : Fin c.2.2.length → ℕ := fun p => (c.2.2.get p).2.2
  let masks : Fin c.2.2.length → Finset (Fin 14) := fun p =>
    Finset.univ.filter fun k =>
      (redGap c.1 (c.2.2.get p).1 k.val || blueGap c.1 (c.2.2.get p).2.1 k.val) = true
  have hn : ∑ p, n p = c.2.1 := by
    change (∑ p : Fin c.2.2.length, (c.2.2.get p).2.2) = c.2.1
    exact (sum_get_map c.2.2 (fun e => e.2.2)).trans hweights
  have hcov : ∀ k, 7 * (∑ p, if k ∈ masks p then n p else 0) ≤ 3 * c.2.1 := by
    intro k
    have ht := hcoverage k
    rw [← sum_get_map] at ht
    simpa [masks, n] using ht
  obtain ⟨p, hp, hcost⟩ := CakeWeightedChoice.choose_of_natural_cover
    n masks g c.2.1 hshape.2.2 hn hg hsum hcov
  obtain ⟨hi, hj, hnpos, hdisjoint⟩ :=
    hentry (c.2.2.get p) (List.get_mem c.2.2 p)
  let i : Fin 7 := ⟨(c.2.2.get p).1, hi⟩
  let j : Fin 7 := ⟨(c.2.2.get p).2.1, hj⟩
  refine ⟨i, j, ?_, ?_⟩
  · simpa only [i, j] using hdisjoint
  · simpa [masks, i, j, Finset.sum_filter] using hcost

theorem table_gap_choice (table : List Certificate)
    (hchecked : table.all checkCertificate = true)
    (hcomplete : table.map Prod.fst = compositions 7 7)
    (runs : List ℕ) (hruns : runs ∈ compositions 7 7)
    (g : Fin 14 → ℝ) (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    ∃ i j : Fin 7,
      (∀ k : Fin 14, (redGap runs i.val k.val && blueGap runs j.val k.val) = false) ∧
      (∑ k : Fin 14, if redGap runs i.val k.val || blueGap runs j.val k.val
        then g k else 0) ≤ (3 / 7 : ℝ) := by
  have hm : runs ∈ table.map Prod.fst := by rw [hcomplete]; exact hruns
  obtain ⟨c, hc, hcr⟩ := List.mem_map.mp hm
  have hcheck : checkCertificate c = true := List.all_eq_true.mp hchecked c hc
  simpa only [hcr] using certificate_gap_choice c hcheck g hg hsum

end CakeQuantileSeven



namespace CakeQuantiles

noncomputable def cakeCDF (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real (Icc 0 x)

theorem cakeCDF_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (cakeCDF μ) := by
  intro a b hab
  exact measureReal_mono (Icc_subset_Icc_right hab)

theorem cakeCDF_continuousOn (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : ContinuousOn (cakeCDF μ) (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_Icc
    (μ := μ) (f := fun _ : ℝ => (1 : ℝ))
    (a := 0) (b := 1) (integrable_const 1).integrableOn
  change ContinuousOn (fun x => (μ (Icc 0 x)).toReal) (Icc 0 1)
  simpa [setIntegral_const, measureReal_def] using h

@[simp] theorem cakeCDF_zero (μ : Measure ℝ) [NullSingletonClass μ] : cakeCDF μ 0 = 0 := by
  simp [cakeCDF, measureReal_def]

theorem cakeCDF_one (μ : Measure ℝ) (hμ : μ (Icc 0 1) = 1) : cakeCDF μ 1 = 1 := by
  simp [cakeCDF, measureReal_def, hμ]

theorem measureReal_Ioc_eq_cakeCDF_sub (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    μ.real (Ioc a b) = cakeCDF μ b - cakeCDF μ a := by
  have hset : Icc (0 : ℝ) b \ Icc 0 a = Ioc a b := by
    ext x
    simp only [mem_sdiff, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨hx0, hxb⟩, hna⟩
      exact ⟨lt_of_not_ge (fun hxa => hna ⟨hx0, hxa⟩), hxb⟩
    · rintro ⟨hax, hxb⟩
      exact ⟨⟨ha.trans hax.le, hxb⟩, fun h => (not_le_of_gt hax) h.2⟩
  rw [← hset, measureReal_sdiff (Icc_subset_Icc_right hab) measurableSet_Icc]
  rfl

theorem measureReal_Icc_eq_cakeCDF_sub (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    μ.real (Icc a b) = cakeCDF μ b - cakeCDF μ a := by
  rw [← measureReal_congr (Ioc_ae_eq_Icc (μ := μ))]
  exact measureReal_Ioc_eq_cakeCDF_sub μ ha hab

theorem measureReal_wrapped_arc (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (hμ : μ (Icc 0 1) = 1)
    {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hba : b < a) :
    μ.real (Icc a 1 ∪ Icc 0 b) = 1 - cakeCDF μ a + cakeCDF μ b := by
  have hd : Disjoint (Icc a 1) (Icc 0 b) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.1, hy.2]
  rw [measureReal_union hd measurableSet_Icc,
    measureReal_Icc_eq_cakeCDF_sub μ ha.1 ha.2,
    measureReal_Icc_eq_cakeCDF_sub μ (by norm_num : (0 : ℝ) ≤ 0) hb.1,
    cakeCDF_zero, cakeCDF_one μ hμ]
  ring

theorem exists_quantile {F : ℝ → ℝ} (hcont : ContinuousOn F (Icc 0 1))
    (hzero : F 0 = 0) (hone : F 1 = 1) {y : ℝ} (hy : y ∈ Icc 0 1) :
    ∃ x ∈ Icc 0 1, F x = y := by
  have hy' : y ∈ Icc (F 0) (F 1) := by simpa [hzero, hone] using hy
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hy'

theorem lt_of_value_lt {F : ℝ → ℝ} (hmono : Monotone F)
    {x y : ℝ} (h : F x < F y) : x < y := by
  by_contra hxy
  exact (not_le_of_gt h) (hmono (le_of_not_gt hxy))

theorem exists_phase_avoiding (G : ℝ → ℝ) (b : Fin 7 → ℝ) :
    ∃ θ ∈ Ioo (0 : ℝ) (1 / 7),
      ∀ i j : Fin 7, G (b i) ≠ θ + (j : ℝ) / 7 := by
  classical
  let bad : Finset ℝ := Finset.univ.biUnion fun i : Fin 7 =>
    Finset.univ.image fun j : Fin 7 => G (b i) - (j : ℝ) / 7
  obtain ⟨θ, hθ, hnot⟩ := (Ioo_infinite (by norm_num : (0 : ℝ) < 1 / 7)).exists_notMem_finset bad
  refine ⟨θ, hθ, ?_⟩
  intro i j heq
  apply hnot
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  refine ⟨j, Finset.mem_univ _, ?_⟩
  linarith

theorem exists_seven_marks {F G : ℝ → ℝ}
    (hcF : ContinuousOn F (Icc 0 1)) (hmF : Monotone F)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hcG : ContinuousOn G (Icc 0 1)) (hmG : Monotone G)
    (hG0 : G 0 = 0) (hG1 : G 1 = 1) :
    ∃ (b c : Fin 7 → ℝ) (θ : ℝ),
      StrictMono b ∧ StrictMono c ∧ b 0 = 0 ∧
      (∀ j, b j ∈ Ico 0 1) ∧ (∀ j, c j ∈ Ioo 0 1) ∧
      θ ∈ Ioo 0 (1 / 7) ∧
      (∀ j, F (b j) = (j : ℝ) / 7) ∧
      (∀ j, G (c j) = θ + (j : ℝ) / 7) ∧
      (∀ i j, b i ≠ c j) := by
  classical
  have hlev (j : Fin 7) : (j : ℝ) / 7 ∈ Ico (0 : ℝ) 1 := by
    have hj : (j : ℝ) < 7 := by exact_mod_cast j.isLt
    constructor
    · positivity
    · linarith
  have hbex (j : Fin 7) : ∃ x ∈ Icc (0 : ℝ) 1, F x = (j : ℝ) / 7 :=
    exists_quantile hcF hF0 hF1 ⟨(hlev j).1, (hlev j).2.le⟩
  choose b' hbmem hbval using hbex
  let b : Fin 7 → ℝ := fun j => if j = 0 then 0 else b' j
  have hbF (j : Fin 7) : F (b j) = (j : ℝ) / 7 := by
    by_cases hj : j = 0
    · simp [b, hj, hF0]
    · simp [b, hj, hbval]
  have hbm (j : Fin 7) : b j ∈ Ico (0 : ℝ) 1 := by
    have hbc : b j ∈ Icc (0 : ℝ) 1 := by
      by_cases hj : j = 0
      · simp [b, hj]
      · simpa [b, hj] using hbmem j
    refine ⟨hbc.1, lt_of_le_of_ne hbc.2 ?_⟩
    intro heq
    have := hbF j
    rw [heq, hF1] at this
    linarith [(hlev j).2]
  have hbs : StrictMono b := by
    intro i j hij
    apply lt_of_value_lt hmF
    rw [hbF, hbF]
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by norm_num)
  obtain ⟨θ, hθ, havoid⟩ := exists_phase_avoiding G b
  have hclev (j : Fin 7) : θ + (j : ℝ) / 7 ∈ Ioo (0 : ℝ) 1 := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast (show (j : ℕ) ≤ 6 by omega)
    constructor <;> linarith [hθ.1, hθ.2]
  have hcex (j : Fin 7) : ∃ x ∈ Icc (0 : ℝ) 1, G x = θ + (j : ℝ) / 7 :=
    exists_quantile hcG hG0 hG1 ⟨(hclev j).1.le, (hclev j).2.le⟩
  choose c hcmem hcval using hcex
  have hcm (j : Fin 7) : c j ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · apply lt_of_value_lt hmG
      rw [hG0, hcval]
      exact (hclev j).1
    · apply lt_of_value_lt hmG
      rw [hcval, hG1]
      exact (hclev j).2
  have hcs : StrictMono c := by
    intro i j hij
    apply lt_of_value_lt hmG
    rw [hcval, hcval]
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    linarith
  refine ⟨b, c, θ, hbs, hcs, by simp [b], hbm, hcm, hθ, hbF, hcval, ?_⟩
  intro i j heq
  apply havoid i j
  rw [heq, hcval]

theorem nonatomic_seven_marks (μB μC : Measure ℝ)
    [IsProbabilityMeasure μB] [IsProbabilityMeasure μC]
    [NullSingletonClass μB] [NullSingletonClass μC]
    (hB : μB (Icc 0 1) = 1) (hC : μC (Icc 0 1) = 1) :
    ∃ (b c : Fin 7 → ℝ) (θ : ℝ),
      StrictMono b ∧ StrictMono c ∧ b 0 = 0 ∧
      (∀ j, b j ∈ Ico 0 1) ∧ (∀ j, c j ∈ Ioo 0 1) ∧
      θ ∈ Ioo 0 (1 / 7) ∧
      (∀ j, cakeCDF μB (b j) = (j : ℝ) / 7) ∧
      (∀ j, cakeCDF μC (c j) = θ + (j : ℝ) / 7) ∧
      (∀ i j, b i ≠ c j) := by
  exact exists_seven_marks (cakeCDF_continuousOn μB) (cakeCDF_monotone μB)
    (cakeCDF_zero μB) (cakeCDF_one μB hB)
    (cakeCDF_continuousOn μC) (cakeCDF_monotone μC)
    (cakeCDF_zero μC) (cakeCDF_one μC hC)

end CakeQuantiles


namespace CakeOrderedMarks

/-- The actual two quantile families form one sorted fourteen-mark vector. -/
theorem exists_ordered_union (b c : Fin 7 → ℝ)
    (hb : StrictMono b) (hc : StrictMono c) (hb0 : b 0=0)
    (hbmem : ∀ i, b i∈Ico 0 1) (hcmem : ∀ i, c i∈Ioo 0 1)
    (hne : ∀ i j, b i≠c j) :
    ∃ (x : Fin 14 → ℝ) (r d : Fin 7 → Fin 14),
      StrictMono x ∧ StrictMono r ∧ StrictMono d ∧ x 0=0 ∧ r 0=0 ∧
      (∀ i, x (r i)=b i) ∧ (∀ j, x (d j)=c j) ∧
      (∀ z, x z∈Ico 0 1) ∧ (∀ i j, r i≠d j) ∧
      (∀ z, (∃ i, r i=z) ∨ (∃ j, d j=z)) := by
  classical
  let R : Finset ℝ := Finset.univ.image b
  let C : Finset ℝ := Finset.univ.image c
  let S : Finset ℝ := R∪C
  have hdisj : Disjoint R C := by
    apply Finset.disjoint_left.mpr
    intro z hzr hzc
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hzr
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hzc
    exact hne i j (hi.trans hj.symm)
  have hcard : S.card=14 := by
    rw [Finset.card_union_of_disjoint hdisj]
    dsimp [R,C]
    rw [Finset.card_image_of_injective _ hb.injective,
      Finset.card_image_of_injective _ hc.injective]
    norm_num
  have hbm (i : Fin 7) : b i∈S :=
    Finset.mem_union_left C (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hcm (j : Fin 7) : c j∈S :=
    Finset.mem_union_right R (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩)
  let e : Fin 14 ≃o S := S.orderIsoOfFin hcard
  let x : Fin 14→ℝ := fun z=>(e z).val
  let r : Fin 7→Fin 14 := fun i=>e.symm ⟨b i,hbm i⟩
  let d : Fin 7→Fin 14 := fun j=>e.symm ⟨c j,hcm j⟩
  have hxm : StrictMono x := by
    intro i j hij
    exact e.strictMono hij
  have hrm : StrictMono r := by
    intro i j hij
    exact e.symm.strictMono (show (⟨b i,hbm i⟩:S)<⟨b j,hbm j⟩ from hb hij)
  have hdm : StrictMono d := by
    intro i j hij
    exact e.symm.strictMono (show (⟨c i,hcm i⟩:S)<⟨c j,hcm j⟩ from hc hij)
  have hrx (i : Fin 7) : x (r i)=b i := by simp [x,r]
  have hdx (j : Fin 7) : x (d j)=c j := by simp [x,d]
  have hcover (z : Fin 14) : (∃ i,r i=z) ∨ (∃ j,d j=z) := by
    have hz : x z∈S := (e z).property
    rcases Finset.mem_union.mp hz with hzr|hzc
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hzr
      exact Or.inl ⟨i,hxm.injective ((hrx i).trans hi)⟩
    · obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hzc
      exact Or.inr ⟨j,hxm.injective ((hdx j).trans hj)⟩
  have hxmem (z : Fin 14) : x z∈Ico 0 1 := by
    rcases hcover z with ⟨i,hi⟩|⟨j,hj⟩
    · rw [←hi,hrx]
      exact hbmem i
    · rw [←hj,hdx]
      exact ⟨(hcmem j).1.le,(hcmem j).2⟩
  have hx0 : x 0=0 := by
    have hlo := (hxmem 0).1
    have hle := hxm.monotone (Fin.zero_le (r 0))
    rw [hrx,hb0] at hle
    exact le_antisymm hle hlo
  have hr0 : r 0=0 := by
    apply hxm.injective
    rw [hrx,hb0,hx0]
  have hrd (i j : Fin 7) : r i≠d j := by
    intro heq
    apply hne i j
    rw [←hrx i,←hdx j,heq]
  exact ⟨x,r,d,hxm,hrm,hdm,hx0,hr0,hrx,hdx,hxmem,hrd,hcover⟩

/-- Append the physical cake endpoint to the sorted mark vector. -/
theorem exists_cut_vector (x : Fin 14→ℝ) (hx : StrictMono x) (hx0 : x 0=0)
    (hxmem : ∀i,x i∈Ico 0 1) :
    ∃y : Fin 15→ℝ, StrictMono y ∧ y 0=0 ∧ y (Fin.last 14)=1 ∧
      (∀i,y i.castSucc=x i) ∧ (∀z,y z∈Icc 0 1) := by
  have hm : StrictMono (Fin.snoc x (1:ℝ)) := by
    rw [←Fin.insertNth_last',Fin.strictMono_insertNth_iff]
    refine ⟨hx,fun i _=>(hxmem i).2,?_⟩
    intro i hi
    exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last i)) hi)
  refine ⟨Fin.snoc x 1,hm,?_,by norm_num [Fin.snoc],by simp,?_⟩
  · simpa using hx0
  · intro z
    refine Fin.lastCases ?_ (fun i=>?_) z
    · norm_num [Fin.snoc]
    · simpa using (show x i∈Icc (0:ℝ) 1 from ⟨(hxmem i).1,(hxmem i).2.le⟩)

/-- The recursive enumeration contains exactly the nonnegative compositions. -/
theorem mem_compositions_iff (runs : List ℕ) (n k : ℕ) :
    runs∈CakeQuantileSeven.compositions n k ↔ runs.length=k ∧ runs.sum=n := by
  induction k generalizing n runs with
  | zero =>
    by_cases hn : n=0
    · subst n
      cases runs <;> simp [CakeQuantileSeven.compositions]
    · cases runs <;> simp [CakeQuantileSeven.compositions,hn,eq_comm]
  | succ k ih =>
    rw [CakeQuantileSeven.compositions]
    constructor
    · intro h
      obtain ⟨a,ha,hmap⟩ := List.mem_flatMap.mp h
      obtain ⟨tail,ht,heq⟩ := List.mem_map.mp hmap
      subst runs
      have hh := (ih tail (n-a)).mp ht
      have ha' := List.mem_range.mp ha
      simp only [List.length_cons,List.sum_cons]
      omega
    · rintro ⟨hlen,hsum⟩
      cases runs with
      | nil => simp at hlen
      | cons a tail =>
        simp only [List.length_cons,List.sum_cons] at hlen hsum
        apply List.mem_flatMap.mpr
        refine ⟨a,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨tail,?_,rfl⟩⟩
        exact (ih tail (n-a)).mpr ⟨by omega,by omega⟩

/-- Numbers of blue marks following each successive red mark. -/
def runsFor (r : Fin 7→Fin 14) : List ℕ :=
  [(r 1).val-(r 0).val-1,(r 2).val-(r 1).val-1,
   (r 3).val-(r 2).val-1,(r 4).val-(r 3).val-1,
   (r 5).val-(r 4).val-1,(r 6).val-(r 5).val-1,
   14-(r 6).val-1]

lemma runsFor_length (r : Fin 7→Fin 14) : (runsFor r).length=7 := rfl

lemma runsFor_sum (r : Fin 7→Fin 14) (hr : StrictMono r) (hr0 : r 0=0) :
    (runsFor r).sum=7 := by
  have h01 : (r 0).val<(r 1).val := hr (by decide)
  have h12 : (r 1).val<(r 2).val := hr (by decide)
  have h23 : (r 2).val<(r 3).val := hr (by decide)
  have h34 : (r 3).val<(r 4).val := hr (by decide)
  have h45 : (r 4).val<(r 5).val := hr (by decide)
  have h56 : (r 5).val<(r 6).val := hr (by decide)
  have h0 : (r 0).val=0 := congrArg Fin.val hr0
  have h6 := (r 6).isLt
  simp only [runsFor,List.sum_cons,List.sum_nil]
  omega

lemma runsFor_mem_compositions (r : Fin 7→Fin 14) (hr : StrictMono r) (hr0 : r 0=0) :
    runsFor r∈CakeQuantileSeven.compositions 7 7 :=
  (mem_compositions_iff _ _ _).mpr ⟨runsFor_length r,runsFor_sum r hr hr0⟩

lemma runsFor_redPositions (r : Fin 7→Fin 14) (hr : StrictMono r) (hr0 : r 0=0) :
    CakeQuantileSeven.redPositions (runsFor r)=List.ofFn (fun i : Fin 7=>(r i).val) := by
  have h01 : (r 0).val<(r 1).val := hr (by decide)
  have h12 : (r 1).val<(r 2).val := hr (by decide)
  have h23 : (r 2).val<(r 3).val := hr (by decide)
  have h34 : (r 3).val<(r 4).val := hr (by decide)
  have h45 : (r 4).val<(r 5).val := hr (by decide)
  have h56 : (r 5).val<(r 6).val := hr (by decide)
  have h0 : (r 0).val=0 := congrArg Fin.val hr0
  have hof : List.ofFn (fun i : Fin 7=>(r i).val)=
      [(r 0).val,(r 1).val,(r 2).val,(r 3).val,(r 4).val,(r 5).val,(r 6).val] := by rfl
  rw [hof]
  simp only [CakeQuantileSeven.redPositions,runsFor,List.scanl_cons,List.scanl_nil,
    List.take_succ_cons,List.take_zero,h0,Nat.sub_zero,Nat.zero_add]
  congr <;> omega

lemma runsFor_bluePositions (r d : Fin 7→Fin 14)
    (hr : StrictMono r) (hd : StrictMono d) (hr0 : r 0=0)
    (hne : ∀i j,r i≠d j)
    (hcover : ∀z,(∃i,r i=z) ∨ (∃j,d j=z)) :
    CakeQuantileSeven.bluePositions (runsFor r)=List.ofFn (fun j : Fin 7=>(d j).val) := by
  have hleft : (CakeQuantileSeven.bluePositions (runsFor r)).SortedLT := by
    exact ((List.sortedLT_range 14).pairwise.filter _).sortedLT
  have hright : (List.ofFn (fun j : Fin 7=>(d j).val)).SortedLT := by
    apply List.sortedLT_ofFn_iff.mpr
    intro i j hij
    exact hd hij
  apply hleft.eq_of_mem_iff hright
  intro p
  have hmem : p∈CakeQuantileSeven.bluePositions (runsFor r) ↔
      p<14 ∧ ¬∃i : Fin 7,(r i).val=p := by
    simp only [CakeQuantileSeven.bluePositions,runsFor_redPositions r hr hr0,
      List.mem_filter,List.mem_range,List.contains_eq_mem,List.mem_ofFn,
      not_decide_eq_true]
  rw [hmem,List.mem_ofFn]
  constructor
  · rintro ⟨hp,hnot⟩
    let z : Fin 14 := ⟨p,hp⟩
    rcases hcover z with ⟨i,hi⟩|⟨j,hj⟩
    · exact False.elim (hnot ⟨i,congrArg Fin.val hi⟩)
    · exact ⟨j,congrArg Fin.val hj⟩
  · rintro ⟨j,hj⟩
    refine ⟨?_,?_⟩
    · rw [←hj]
      exact (d j).isLt
    · rintro ⟨i,hi⟩
      exact hne i j (Fin.ext (hi.trans hj.symm))

/-- Every actual pair of quantile families has an enumerated run encoding. -/
theorem exists_ordered_run_encoding (b c : Fin 7→ℝ)
    (hb : StrictMono b) (hc : StrictMono c) (hb0 : b 0=0)
    (hbmem : ∀i,b i∈Ico 0 1) (hcmem : ∀j,c j∈Ioo 0 1)
    (hne : ∀i j,b i≠c j) :
    ∃(x : Fin 14→ℝ)(r d : Fin 7→Fin 14)(runs : List ℕ),
      StrictMono x ∧ StrictMono r ∧ StrictMono d ∧ x 0=0 ∧ r 0=0 ∧
      (∀i,x (r i)=b i) ∧ (∀j,x (d j)=c j) ∧
      (∀z,x z∈Ico 0 1) ∧ (∀i j,r i≠d j) ∧
      (∀z,(∃i,r i=z) ∨ (∃j,d j=z)) ∧
      runs.length=7 ∧ runs.sum=7 ∧ runs∈CakeQuantileSeven.compositions 7 7 ∧
      CakeQuantileSeven.redPositions runs=List.ofFn (fun i : Fin 7=>(r i).val) ∧
      CakeQuantileSeven.bluePositions runs=List.ofFn (fun j : Fin 7=>(d j).val) := by
  obtain ⟨x,r,d,hx,hr,hd,hx0,hr0,hxr,hxd,hxm,hrd,hcover⟩ :=
    exists_ordered_union b c hb hc hb0 hbmem hcmem hne
  exact ⟨x,r,d,runsFor r,hx,hr,hd,hx0,hr0,hxr,hxd,hxm,hrd,hcover,
    runsFor_length r,runsFor_sum r hr hr0,runsFor_mem_compositions r hr hr0,
    runsFor_redPositions r hr hr0,runsFor_bluePositions r d hr hd hr0 hrd hcover⟩

end CakeOrderedMarks


namespace CakeGapWeights

noncomputable def gap (μ : Measure ℝ) (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  μ.real (Ioc (x j) (x (j + 1)))

theorem gap_nonneg (μ : Measure ℝ) (x : ℕ → ℝ) (j : ℕ) : 0 ≤ gap μ x j :=
  measureReal_nonneg

theorem integral_one_eq_gap_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    (∫ _ in a..b, (1 : ℝ) ∂μ) = μ.real (Ioc a b) := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_const]
  simp

theorem sum_gap_Ico (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ℕ → ℝ) (hx : Monotone x) {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, gap μ x j) = μ.real (Ioc (x a) (x b)) := by
  calc
    (∑ j ∈ Finset.Ico a b, gap μ x j) =
        ∑ j ∈ Finset.Ico a b, ∫ _ in x j..x (j + 1), (1 : ℝ) ∂μ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_one_eq_gap_mass μ (hx (Nat.le_succ j))).symm
    _ = ∫ _ in x a..x b, (1 : ℝ) ∂μ :=
      intervalIntegral.sum_integral_adjacent_intervals_Ico hab
        (fun j hj => intervalIntegrable_const)
    _ = μ.real (Ioc (x a) (x b)) := integral_one_eq_gap_mass μ (hx hab)

theorem sum_gap_Ico_closed (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (x : ℕ → ℝ) (hx : Monotone x)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, gap μ x j) = μ.real (Icc (x a) (x b)) := by
  rw [sum_gap_Ico μ x hx hab, measureReal_congr Ioc_ae_eq_Icc]

theorem sum_gap_eq_one (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (x : ℕ → ℝ) (hx : Monotone x)
    (N : ℕ) (hzero : x 0 = 0) (hN : x N = 1)
    (hμ : μ (Icc 0 1) = 1) :
    (∑ j ∈ Finset.range N, gap μ x j) = 1 := by
  have h := sum_gap_Ico_closed μ x hx (Nat.zero_le N)
  simpa [Nat.Ico_zero_eq_range, hzero, hN, measureReal_def, hμ] using h

theorem sum_gap_wrapped_parts (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (x : ℕ → ℝ) (hx : Monotone x)
    {N a b : ℕ} (ha : a ≤ N) (hzero : x 0 = 0) (hN : x N = 1) :
    (∑ j ∈ Finset.Ico a N, gap μ x j) +
      (∑ j ∈ Finset.Ico 0 b, gap μ x j) =
      μ.real (Icc (x a) 1) + μ.real (Icc 0 (x b)) := by
  rw [sum_gap_Ico_closed μ x hx ha,
    sum_gap_Ico_closed μ x hx (Nat.zero_le b), hzero, hN]

end CakeGapWeights


namespace CakeArcOrder

def Hit (a b g : ℕ) : Prop :=
  if a < b then a ≤ g ∧ g < b else a ≤ g ∨ g < b

theorem nonwrapped_separated {N a b c d : ℕ}
    (ha : a < N) (hc : c < N) (hab : a < b) (hcd : c < d)
    (hdisj : ∀ g, g < N → Hit a b g → Hit c d g → False) :
    b ≤ c ∨ d ≤ a := by
  by_cases hac : a ≤ c
  · by_cases hbc : b ≤ c
    · exact Or.inl hbc
    · have hA : Hit a b c := by rw [Hit, if_pos hab]; omega
      have hB : Hit c d c := by rw [Hit, if_pos hcd]; omega
      exact False.elim (hdisj c hc hA hB)
  · by_cases hda : d ≤ a
    · exact Or.inr hda
    · have hA : Hit a b a := by rw [Hit, if_pos hab]; omega
      have hB : Hit c d a := by rw [Hit, if_pos hcd]; omega
      exact False.elim (hdisj a ha hA hB)

theorem wrapped_contains_complement {N a b c d : ℕ}
    (hc : c < N) (hd : d < N) (hba : b < a) (hcd : c < d)
    (hdisj : ∀ g, g < N → Hit a b g → Hit c d g → False) :
    b ≤ c ∧ d ≤ a := by
  have hab : ¬ a < b := by omega
  have hBstart : Hit c d c := by rw [Hit, if_pos hcd]; omega
  have hAstart : ¬ Hit a b c := fun h => hdisj c hc h hBstart
  have hBend : Hit c d (d - 1) := by rw [Hit, if_pos hcd]; omega
  have hend : d - 1 < N := by omega
  have hAend : ¬ Hit a b (d - 1) := fun h => hdisj (d - 1) hend h hBend
  simp only [Hit, if_neg hab, not_or] at hAstart hAend
  omega

theorem both_wrapped_impossible {N a b c d : ℕ}
    (ha : a < N) (hc : c < N) (hba : b ≤ a) (hdc : d ≤ c)
    (hdisj : ∀ g, g < N → Hit a b g → Hit c d g → False) : False := by
  have hab : ¬ a < b := by omega
  have hcd : ¬ c < d := by omega
  by_cases hac : a ≤ c
  · apply hdisj c hc
    · rw [Hit, if_neg hab]; exact Or.inl hac
    · rw [Hit, if_neg hcd]; exact Or.inl (Nat.le_refl c)
  · apply hdisj a ha
    · rw [Hit, if_neg hab]; exact Or.inl (Nat.le_refl a)
    · rw [Hit, if_neg hcd]; exact Or.inl (by omega)

theorem classify_disjoint_arcs {N a b c d : ℕ}
    (ha : a < N) (hb : b < N) (hc : c < N) (hd : d < N)
    (habne : a ≠ b) (hcdne : c ≠ d)
    (hdisj : ∀ g, g < N → Hit a b g → Hit c d g → False) :
    (a < b ∧ c < d ∧ (b ≤ c ∨ d ≤ a)) ∨
    (b < a ∧ c < d ∧ b ≤ c ∧ d ≤ a) ∨
    (a < b ∧ d < c ∧ d ≤ a ∧ b ≤ c) := by
  by_cases hab : a < b
  · by_cases hcd : c < d
    · exact Or.inl ⟨hab, hcd, nonwrapped_separated ha hc hab hcd hdisj⟩
    · have hdc : d < c := by omega
      have hsep := wrapped_contains_complement ha hb hdc hab
        (fun g hg hC hA => hdisj g hg hA hC)
      exact Or.inr (Or.inr ⟨hab, hdc, hsep.1, hsep.2⟩)
  · have hba : b < a := by omega
    by_cases hcd : c < d
    · have hsep := wrapped_contains_complement hc hd hba hcd hdisj
      exact Or.inr (Or.inl ⟨hba, hcd, hsep.1, hsep.2⟩)
    · exact False.elim (both_wrapped_impossible ha hc (by omega) (by omega) hdisj)

end CakeArcOrder


namespace CakeArcSums

def Hit (a b g : ℕ) : Prop :=
  if a < b then a ≤ g ∧ g < b else a ≤ g ∨ g < b

instance decidableHit (a b g : ℕ) : Decidable (Hit a b g) := by
  by_cases hab : a < b
  · rw [Hit, if_pos hab]
    infer_instance
  · rw [Hit, if_neg hab]
    infer_instance

theorem filter_range_Hit_of_lt (N a b : ℕ) (hb : b ≤ N) (hab : a < b) :
    (Finset.range N).filter (Hit a b) = Finset.Ico a b := by
  classical
  ext g
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Hit, if_pos hab]
  omega

theorem filter_range_Hit_of_ge (N a b : ℕ) (_ha : a ≤ N) (hb : b ≤ N)
    (hba : b ≤ a) :
    (Finset.range N).filter (Hit a b) = Finset.Ico a N ∪ Finset.Ico 0 b := by
  classical
  have hab : ¬ a < b := by omega
  ext g
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
    Finset.mem_Ico, Hit, if_neg hab]
  omega

theorem disjoint_wrapped_intervals (a b N : ℕ) (hba : b ≤ a) :
    Disjoint (Finset.Ico a N) (Finset.Ico 0 b) := by
  apply Finset.disjoint_left.mpr
  intro g hga hgb
  simp only [Finset.mem_Ico] at hga hgb
  omega

theorem sum_Hit_indicator_of_lt (f : ℕ → ℝ) (N a b : ℕ)
    (hb : b ≤ N) (hab : a < b) :
    (∑ g ∈ Finset.range N, if Hit a b g then f g else 0) =
      ∑ g ∈ Finset.Ico a b, f g := by
  classical
  rw [← Finset.sum_filter, filter_range_Hit_of_lt N a b hb hab]

theorem sum_Hit_indicator_of_ge (f : ℕ → ℝ) (N a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) (hba : b ≤ a) :
    (∑ g ∈ Finset.range N, if Hit a b g then f g else 0) =
      (∑ g ∈ Finset.Ico a N, f g) + (∑ g ∈ Finset.Ico 0 b, f g) := by
  classical
  rw [← Finset.sum_filter, filter_range_Hit_of_ge N a b ha hb hba,
    Finset.sum_union (disjoint_wrapped_intervals a b N hba)]

theorem sum_Hit_indicator (f : ℕ → ℝ) (N a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) :
    (∑ g ∈ Finset.range N, if Hit a b g then f g else 0) =
      if a < b then ∑ g ∈ Finset.Ico a b, f g
      else (∑ g ∈ Finset.Ico a N, f g) + (∑ g ∈ Finset.Ico 0 b, f g) := by
  classical
  by_cases hab : a < b
  · rw [if_pos hab]
    exact sum_Hit_indicator_of_lt f N a b hb hab
  · rw [if_neg hab]
    exact sum_Hit_indicator_of_ge f N a b ha hb (by omega)

theorem sum_indicator_or_of_disjoint {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ g ∈ s, P g → Q g → False) :
    (∑ g ∈ s, if P g ∨ Q g then f g else 0) =
      (∑ g ∈ s, if P g then f g else 0) +
      (∑ g ∈ s, if Q g then f g else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hp : P g
  · have hq : ¬ Q g := hdisj g hg hp
    simp only [hp, hq, true_or, if_true, if_false, add_zero]
  · by_cases hq : Q g <;> simp [hp, hq]

theorem sum_bool_or_of_and_false {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (P Q : ι → Bool) (hdisj : ∀ g ∈ s, (P g && Q g) = false) :
    (∑ g ∈ s, if P g || Q g then f g else 0) =
      (∑ g ∈ s, if P g then f g else 0) +
      (∑ g ∈ s, if Q g then f g else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  have hd := hdisj g hg
  cases hp : P g <;> cases hq : Q g <;> simp_all

theorem sum_Hit_union_eq_add (f : ℕ → ℝ) (N a b c d : ℕ)
    (hdisj : ∀ g, g < N → Hit a b g → Hit c d g → False) :
    (∑ g ∈ Finset.range N, if Hit a b g ∨ Hit c d g then f g else 0) =
      (∑ g ∈ Finset.range N, if Hit a b g then f g else 0) +
      (∑ g ∈ Finset.range N, if Hit c d g then f g else 0) := by
  classical
  exact sum_indicator_or_of_disjoint (Finset.range N) f (Hit a b) (Hit c d)
    (fun g hg => hdisj g (Finset.mem_range.mp hg))

theorem sum_fin_indicator_eq_range (N : ℕ) (f : ℕ → ℝ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ g : Fin N, if P g.val then f g.val else 0) =
      ∑ g ∈ Finset.range N, if P g then f g else 0 :=
  Fin.sum_univ_eq_sum_range (fun g => if P g then f g else 0) N

theorem sum_fin_bool_indicator_eq_range (N : ℕ) (f : ℕ → ℝ) (P : ℕ → Bool) :
    (∑ g : Fin N, if P g.val then f g.val else 0) =
      ∑ g ∈ Finset.range N, if P g then f g else 0 :=
  Fin.sum_univ_eq_sum_range (fun g => if P g then f g else 0) N

theorem sum_fin_Hit_indicator (f : ℕ → ℝ) (N a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) :
    (∑ g : Fin N, if Hit a b g.val then f g.val else 0) =
      if a < b then ∑ g ∈ Finset.Ico a b, f g
      else (∑ g ∈ Finset.Ico a N, f g) + (∑ g ∈ Finset.Ico 0 b, f g) := by
  classical
  rw [sum_fin_indicator_eq_range]
  exact sum_Hit_indicator f N a b ha hb

/-- Boolean form used by the certificate decoder. -/
theorem decide_Hit_eq_mask (a b g : ℕ) :
    decide (Hit a b g) =
      if a < b then decide (a ≤ g ∧ g < b) else decide (a ≤ g ∨ g < b) := by
  by_cases hab : a < b <;> simp [Hit, hab]

theorem sum_bool_arc_indicator (f : ℕ → ℝ) (N a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) :
    (∑ g ∈ Finset.range N,
      if (if a < b then decide (a ≤ g ∧ g < b) else decide (a ≤ g ∨ g < b))
      then f g else 0) =
      if a < b then ∑ g ∈ Finset.Ico a b, f g
      else (∑ g ∈ Finset.Ico a N, f g) + (∑ g ∈ Finset.Ico 0 b, f g) := by
  classical
  by_cases hab : a < b <;> simpa [Hit, hab] using sum_Hit_indicator f N a b ha hb

theorem sum_fin_bool_arc_indicator (f : ℕ → ℝ) (N a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) :
    (∑ g : Fin N,
      if (if a < b then decide (a ≤ g.val ∧ g.val < b)
          else decide (a ≤ g.val ∨ g.val < b)) then f g.val else 0) =
      if a < b then ∑ g ∈ Finset.Ico a b, f g
      else (∑ g ∈ Finset.Ico a N, f g) + (∑ g ∈ Finset.Ico 0 b, f g) := by
  rw [sum_fin_bool_indicator_eq_range N f
    (fun g => if a < b then decide (a ≤ g ∧ g < b) else decide (a ≤ g ∨ g < b))]
  exact sum_bool_arc_indicator f N a b ha hb

end CakeArcSums


namespace OMA.S_arxiv_1909_07141

open MeasureTheory

def DivisionWithCuts {n : ℕ} (μ : Fin n → Measure ℝ) (α : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ (c : Fin (k + 2) → ℝ) (owner : Fin (k + 1) → Fin n),
    Monotone c ∧ c 0 = 0 ∧ c (Fin.last (k + 1)) = 1 ∧
      ∀ i : Fin n, ENNReal.ofReal (α i) ≤
        μ i (⋃ j ∈ {j : Fin (k + 1) | owner j = i}, Set.Icc (c j.castSucc) (c j.succ))

end OMA.S_arxiv_1909_07141


namespace CakeFourCuts

open Set MeasureTheory
open scoped ENNReal

noncomputable def cutVector (a b c d : ℝ) : Fin 6 → ℝ := ![0, a, b, c, d, 1]

def ownerBC : Fin 5 → Fin 3 := ![2, 0, 2, 1, 2]
def ownerCB : Fin 5 → Fin 3 := ![2, 1, 2, 0, 2]
def ownerWrappedB : Fin 5 → Fin 3 := ![0, 2, 1, 2, 0]
def ownerWrappedC : Fin 5 → Fin 3 := ![1, 2, 0, 2, 1]

def piece (cuts : Fin 6 → ℝ) (owner : Fin 5 → Fin 3) (i : Fin 3) : Set ℝ :=
  ⋃ j ∈ {j : Fin 5 | owner j = i}, Icc (cuts j.castSucc) (cuts j.succ)

theorem monotone_cutVector (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) : Monotone (cutVector a b c d) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i
  · simpa [cutVector] using ha
  · simpa [cutVector] using hab
  · simpa [cutVector] using hbc
  · simpa [cutVector] using hcd
  · simpa [cutVector] using hd

theorem five_intervals_cover (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    Icc (0 : ℝ) 1 ⊆ Icc 0 a ∪ Icc a b ∪ Icc b c ∪ Icc c d ∪ Icc d 1 := by
  rw [Icc_union_Icc_eq_Icc ha hab,
    Icc_union_Icc_eq_Icc (ha.trans hab) hbc,
    Icc_union_Icc_eq_Icc ((ha.trans hab).trans hbc) hcd,
    Icc_union_Icc_eq_Icc (((ha.trans hab).trans hbc).trans hcd) hd]

theorem piece_ownerBC (a b c d : ℝ) (i : Fin 3) :
    piece (cutVector a b c d) ownerBC i =
      ![Icc a b, Icc c d, Icc 0 a ∪ Icc b c ∪ Icc d 1] i := by
  fin_cases i <;> ext x <;>
    simp [piece, cutVector, ownerBC, Fin.exists_fin_succ, or_assoc]

theorem piece_ownerCB (a b c d : ℝ) (i : Fin 3) :
    piece (cutVector a b c d) ownerCB i =
      ![Icc c d, Icc a b, Icc 0 a ∪ Icc b c ∪ Icc d 1] i := by
  fin_cases i <;> ext x <;>
    simp [piece, cutVector, ownerCB, Fin.exists_fin_succ, or_assoc]

theorem piece_ownerWrappedB (a b c d : ℝ) (i : Fin 3) :
    piece (cutVector a b c d) ownerWrappedB i =
      ![Icc 0 a ∪ Icc d 1, Icc b c, Icc a b ∪ Icc c d] i := by
  fin_cases i <;> ext x <;>
    simp [piece, cutVector, ownerWrappedB, Fin.exists_fin_succ]

theorem piece_ownerWrappedC (a b c d : ℝ) (i : Fin 3) :
    piece (cutVector a b c d) ownerWrappedC i =
      ![Icc b c, Icc 0 a ∪ Icc d 1, Icc a b ∪ Icc c d] i := by
  fin_cases i <;> ext x <;>
    simp [piece, cutVector, ownerWrappedC, Fin.exists_fin_succ]

theorem leftover_mass {μ : Measure ℝ} {A H : Set ℝ}
    (hcake : μ (Icc (0 : ℝ) 1) = 1)
    (hcover : Icc (0 : ℝ) 1 ⊆ A ∪ H)
    (hcost : μ A ≤ ENNReal.ofReal (3 / 7 : ℝ)) :
    ENNReal.ofReal (4 / 7 : ℝ) ≤ μ H := by
  have hsum : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 7 : ℝ) + μ H := by
    calc
      _ = μ (Icc (0 : ℝ) 1) := hcake.symm
      _ ≤ μ (A ∪ H) := measure_mono hcover
      _ ≤ μ A + μ H := measure_union_le A H
      _ ≤ ENNReal.ofReal (3 / 7 : ℝ) + μ H := add_le_add hcost le_rfl
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (3 / 7 : ℝ) ≤ μ H :=
    tsub_le_iff_right.mpr (by simpa only [add_comm] using hsum)
  calc
    ENNReal.ofReal (4 / 7 : ℝ) = ENNReal.ofReal ((1 : ℝ) - 3 / 7) := by norm_num
    _ = (1 : ℝ≥0∞) - ENNReal.ofReal (3 / 7 : ℝ) := by
      rw [ENNReal.ofReal_sub _ (by norm_num), ENNReal.ofReal_one]
    _ ≤ μ H := hsub

theorem division_of_three_pieces (μ : Fin 3 → Measure ℝ) (a b c d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1)
    (owner : Fin 5 → Fin 3) (P : Fin 3 → Set ℝ)
    (hpieces : ∀ i, piece (cutVector a b c d) owner i = P i)
    (hB : ENNReal.ofReal (2 / 7 : ℝ) ≤ μ 0 (P 0))
    (hC : ENNReal.ofReal (1 / 7 : ℝ) ≤ μ 1 (P 1))
    (hcake : μ 2 (Icc (0 : ℝ) 1) = 1)
    (hcover : Icc (0 : ℝ) 1 ⊆ (P 0 ∪ P 1) ∪ P 2)
    (hcost : μ 2 (P 0 ∪ P 1) ≤ ENNReal.ofReal (3 / 7 : ℝ)) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2 / 7 : ℝ), 1 / 7, 4 / 7] 4 := by
  refine ⟨cutVector a b c d, owner, monotone_cutVector a b c d ha hab hbc hcd hd,
    by simp [cutVector], by simp [cutVector], ?_⟩
  have hH := leftover_mass hcake hcover hcost
  intro i
  change ENNReal.ofReal ((![(2 / 7 : ℝ), 1 / 7, 4 / 7] : Fin 3 → ℝ) i) ≤
    μ i (piece (cutVector a b c d) owner i)
  rw [hpieces i]
  fin_cases i
  · simpa using hB
  · simpa using hC
  · simpa using hH

theorem nonwrapped_BC (μ : Fin 3 → Measure ℝ) (a b c d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1)
    (hB : ENNReal.ofReal (2 / 7 : ℝ) ≤ μ 0 (Icc a b))
    (hC : ENNReal.ofReal (1 / 7 : ℝ) ≤ μ 1 (Icc c d))
    (hcake : μ 2 (Icc (0 : ℝ) 1) = 1)
    (hcost : μ 2 (Icc a b ∪ Icc c d) ≤ ENNReal.ofReal (3 / 7 : ℝ)) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2 / 7 : ℝ), 1 / 7, 4 / 7] 4 := by
  apply division_of_three_pieces μ a b c d ha hab hbc hcd hd ownerBC
    ![Icc a b, Icc c d, Icc 0 a ∪ Icc b c ∪ Icc d 1]
    (piece_ownerBC a b c d) hB hC hcake
  · intro x hx
    have hv := five_intervals_cover a b c d ha hab hbc hcd hd hx
    simp only [Set.mem_union] at hv ⊢
    aesop
  · exact hcost

theorem nonwrapped_CB (μ : Fin 3 → Measure ℝ) (a b c d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1)
    (hB : ENNReal.ofReal (2 / 7 : ℝ) ≤ μ 0 (Icc c d))
    (hC : ENNReal.ofReal (1 / 7 : ℝ) ≤ μ 1 (Icc a b))
    (hcake : μ 2 (Icc (0 : ℝ) 1) = 1)
    (hcost : μ 2 (Icc c d ∪ Icc a b) ≤ ENNReal.ofReal (3 / 7 : ℝ)) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2 / 7 : ℝ), 1 / 7, 4 / 7] 4 := by
  apply division_of_three_pieces μ a b c d ha hab hbc hcd hd ownerCB
    ![Icc c d, Icc a b, Icc 0 a ∪ Icc b c ∪ Icc d 1]
    (piece_ownerCB a b c d) hB hC hcake
  · intro x hx
    have hv := five_intervals_cover a b c d ha hab hbc hcd hd hx
    simp only [Set.mem_union] at hv ⊢
    aesop
  · exact hcost

theorem wrapped_B (μ : Fin 3 → Measure ℝ) (a b c d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1)
    (hB : ENNReal.ofReal (2 / 7 : ℝ) ≤ μ 0 (Icc 0 a ∪ Icc d 1))
    (hC : ENNReal.ofReal (1 / 7 : ℝ) ≤ μ 1 (Icc b c))
    (hcake : μ 2 (Icc (0 : ℝ) 1) = 1)
    (hcost : μ 2 ((Icc 0 a ∪ Icc d 1) ∪ Icc b c) ≤ ENNReal.ofReal (3 / 7 : ℝ)) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2 / 7 : ℝ), 1 / 7, 4 / 7] 4 := by
  apply division_of_three_pieces μ a b c d ha hab hbc hcd hd ownerWrappedB
    ![Icc 0 a ∪ Icc d 1, Icc b c, Icc a b ∪ Icc c d]
    (piece_ownerWrappedB a b c d) hB hC hcake
  · intro x hx
    have hv := five_intervals_cover a b c d ha hab hbc hcd hd hx
    simp only [Set.mem_union] at hv ⊢
    aesop
  · exact hcost

theorem wrapped_C (μ : Fin 3 → Measure ℝ) (a b c d : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hd : d ≤ 1)
    (hB : ENNReal.ofReal (2 / 7 : ℝ) ≤ μ 0 (Icc b c))
    (hC : ENNReal.ofReal (1 / 7 : ℝ) ≤ μ 1 (Icc 0 a ∪ Icc d 1))
    (hcake : μ 2 (Icc (0 : ℝ) 1) = 1)
    (hcost : μ 2 (Icc b c ∪ (Icc 0 a ∪ Icc d 1)) ≤ ENNReal.ofReal (3 / 7 : ℝ)) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2 / 7 : ℝ), 1 / 7, 4 / 7] 4 := by
  apply division_of_three_pieces μ a b c d ha hab hbc hcd hd ownerWrappedC
    ![Icc b c, Icc 0 a ∪ Icc d 1, Icc a b ∪ Icc c d]
    (piece_ownerWrappedC a b c d) hB hC hcake
  · intro x hx
    have hv := five_intervals_cover a b c d ha hab hbc hcd hd hx
    simp only [Set.mem_union] at hv ⊢
    aesop
  · exact hcost

end CakeFourCuts


namespace CakeQuantileArcMasses

open Set MeasureTheory

/-- The actual closed circular arc, possibly crossing the cake endpoint. -/
def circleArc (a b : ℝ) : Set ℝ :=
  if a<b then Icc a b else Icc a 1 ∪ Icc 0 b

/-- Any positive cyclic step through seven exact quantiles has its exact mass. -/
theorem cyclic_quantile_arc_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (hμ : μ (Icc 0 1)=1)
    (b : Fin 7→ℝ) (θ : ℝ) (hb : StrictMono b)
    (hbmem : ∀j,b j∈Icc 0 1)
    (hlevel : ∀j,CakeQuantiles.cakeCDF μ (b j)=θ+(j:ℝ)/7)
    (i d : Fin 7) (hd : 0<d.val) :
    μ.real (circleArc (b i) (b (i+d)))=(d:ℝ)/7 := by
  let j : Fin 7 := i+d
  have hi7 := i.isLt
  have hd7 := d.isLt
  have hjval : j.val=(i.val+d.val)%7 := by exact Fin.val_add i d
  by_cases hwrap : i.val+d.val<7
  · have hj : j.val=i.val+d.val := by rw [hjval,Nat.mod_eq_of_lt hwrap]
    have hij : i<j := by change i.val<j.val; omega
    have hbij : b i<b j := hb hij
    change μ.real (circleArc (b i) (b j))=(d:ℝ)/7
    rw [circleArc,if_pos hbij,
      CakeQuantiles.measureReal_Icc_eq_cakeCDF_sub μ (hbmem i).1 hbij.le,
      hlevel j,hlevel i]
    have hcast : (j:ℝ)=(i:ℝ)+(d:ℝ) := by exact_mod_cast hj
    linarith
  · have hj : j.val+7=i.val+d.val := by omega
    have hji : j < i := by change j.val < i.val; omega
    have hbji : b j<b i := hb hji
    change μ.real (circleArc (b i) (b j))=(d:ℝ)/7
    rw [circleArc,if_neg (not_lt_of_gt hbji),
      CakeQuantiles.measureReal_wrapped_arc μ hμ (hbmem i) (hbmem j) hbji,
      hlevel i,hlevel j]
    have hcast : (j:ℝ)+7=(i:ℝ)+(d:ℝ) := by exact_mod_cast hj
    linarith

/-- The red two-step quantile arc has mass 2/7, including wrapping starts. -/
theorem red_arc_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (hμ : μ (Icc 0 1)=1)
    (b : Fin 7→ℝ) (hb : StrictMono b) (hbmem : ∀i,b i∈Ico 0 1)
    (hlevel : ∀i,CakeQuantiles.cakeCDF μ (b i)=(i:ℝ)/7) (i : Fin 7) :
    μ.real (circleArc (b i) (b (i+2)))=(2:ℝ)/7 := by
  have h := cyclic_quantile_arc_mass μ hμ b 0 hb
    (fun j=>⟨(hbmem j).1,(hbmem j).2.le⟩)
    (fun j=>by simpa using hlevel j) i 2 (by decide)
  simpa using h

/-- The phase-shifted blue one-step quantile arc has mass 1/7. -/
theorem blue_arc_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (hμ : μ (Icc 0 1)=1)
    (c : Fin 7→ℝ) (θ : ℝ) (hc : StrictMono c) (hcmem : ∀j,c j∈Ioo 0 1)
    (hlevel : ∀j,CakeQuantiles.cakeCDF μ (c j)=θ+(j:ℝ)/7) (j : Fin 7) :
    μ.real (circleArc (c j) (c (j+1)))=(1:ℝ)/7 := by
  have h := cyclic_quantile_arc_mass μ hμ c θ hc
    (fun i=>⟨(hcmem i).1.le,(hcmem i).2.le⟩) hlevel j 1 (by decide)
  simpa using h

end CakeQuantileArcMasses


namespace CakeSevenMaskTransport
open CakeQuantileSeven

lemma getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn f).getD i.val a = f i := by
  rw [List.getD_eq_getElem (List.ofFn f) a (by simp)]
  simp

theorem redGap_of_positions (r : Fin 7 → Fin 14) (runs : List ℕ)
    (hred : redPositions runs = List.ofFn (fun i : Fin 7 => (r i).val))
    (i : Fin 7) (g : ℕ) :
    redGap runs i.val g = gapInArc (r i).val (r (i + 2)).val g := by
  unfold redGap
  rw [hred, getD_ofFn]
  change gapInArc (r i).val
    ((List.ofFn (fun i : Fin 7 => (r i).val)).getD (i + 2).val 0) g = _
  rw [getD_ofFn]

theorem blueGap_of_positions (d : Fin 7 → Fin 14) (runs : List ℕ)
    (hblue : bluePositions runs = List.ofFn (fun j : Fin 7 => (d j).val))
    (j : Fin 7) (g : ℕ) :
    blueGap runs j.val g = gapInArc (d j).val (d (j + 1)).val g := by
  unfold blueGap
  rw [hblue, getD_ofFn]
  change gapInArc (d j).val
    ((List.ofFn (fun j : Fin 7 => (d j).val)).getD (j + 1).val 0) g = _
  rw [getD_ofFn]

lemma step_one_ne (i : Fin 7) : i + 1 ≠ i := by
  fin_cases i <;> decide

lemma step_two_ne (i : Fin 7) : i + 2 ≠ i := by
  fin_cases i <;> decide

end CakeSevenMaskTransport


namespace CakeSevenComplete
open CakeGapWeights CakeQuantileSeven

noncomputable def extendCut (y : Fin 15 → ℝ) (n : ℕ) : ℝ :=
  y ⟨min n 14, by omega⟩

theorem extendCut_monotone (y : Fin 15 → ℝ) (hy : Monotone y) : Monotone (extendCut y) := by
  intro a b hab
  apply hy
  exact min_le_min_right 14 hab

theorem extendCut_fin (y : Fin 15 → ℝ) (i : Fin 15) : extendCut y i.val = y i := by
  have hi : i.val ≤ 14 := by omega
  simp only [extendCut, Nat.min_eq_left hi]

noncomputable def indexArc (X : ℕ → ℝ) (a b : ℕ) : Set ℝ :=
  if a < b then Set.Icc (X a) (X b) else Set.Icc 0 (X b) ∪ Set.Icc (X a) 1

theorem gap_weights_sum (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (X : ℕ → ℝ) (hX : Monotone X) (h0 : X 0=0) (h14 : X 14=1)
    (hμ : μ (Set.Icc 0 1)=1) :
    (∑ k : Fin 14, gap μ X k.val)=1 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_gap_eq_one μ X hX 14 h0 h14 hμ

theorem indexArc_mass_le_cost (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (X : ℕ → ℝ) (hX : Monotone X) (h0 : X 0=0) (h14 : X 14=1)
    (a b : ℕ) (ha : a<14) (hb : b<14) :
    μ.real (indexArc X a b) ≤
      ∑ k : Fin 14, if gapInArc a b k.val then gap μ X k.val else 0 := by
  have hsum := CakeArcSums.sum_fin_bool_arc_indicator (gap μ X) 14 a b ha.le hb.le
  change (∑ k : Fin 14, if gapInArc a b k.val then gap μ X k.val else 0) = _ at hsum
  rw [hsum]
  by_cases hab : a<b
  · rw [if_pos hab, indexArc, if_pos hab, sum_gap_Ico_closed μ X hX hab.le]
  · rw [if_neg hab, indexArc, if_neg hab,
      sum_gap_wrapped_parts μ X hX ha.le h0 h14]
    simpa only [add_comm] using
      (measureReal_union_le (μ:=μ) (Set.Icc 0 (X b)) (Set.Icc (X a) 1))

theorem two_arc_cost_bound (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (X : ℕ → ℝ) (hX : Monotone X) (h0 : X 0=0) (h14 : X 14=1)
    (a b c d : ℕ) (ha : a<14) (hb : b<14) (hc : c<14) (hd : d<14)
    (hdisj : ∀ k : Fin 14, (gapInArc a b k.val && gapInArc c d k.val)=false)
    (hcost : (∑ k : Fin 14, if gapInArc a b k.val || gapInArc c d k.val then gap μ X k.val else 0)≤(3/7:ℝ)) :
    μ (indexArc X a b ∪ indexArc X c d) ≤ ENNReal.ofReal (3/7:ℝ) := by
  have hsplit := CakeArcSums.sum_bool_or_of_and_false Finset.univ
    (fun k : Fin 14=>gap μ X k.val) (fun k=>gapInArc a b k.val) (fun k=>gapInArc c d k.val)
    (fun k _=>hdisj k)
  have hmass : μ.real (indexArc X a b ∪ indexArc X c d)≤(3/7:ℝ) := by
    calc
      _ ≤ μ.real (indexArc X a b)+μ.real (indexArc X c d) := measureReal_union_le _ _
      _ ≤ (∑ k : Fin 14, if gapInArc a b k.val then gap μ X k.val else 0)+
          (∑ k : Fin 14, if gapInArc c d k.val then gap μ X k.val else 0) :=
        add_le_add (indexArc_mass_le_cost μ X hX h0 h14 a b ha hb)
          (indexArc_mass_le_cost μ X hX h0 h14 c d hc hd)
      _ = _ := hsplit.symm
      _ ≤ _ := hcost
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hmass

theorem disjoint_hits_of_masks (a b c d : ℕ)
    (hdisj : ∀ k : Fin 14, (gapInArc a b k.val && gapInArc c d k.val)=false) :
    ∀ g, g<14 → CakeArcOrder.Hit a b g → CakeArcOrder.Hit c d g → False := by
  intro g hg hA hB
  have hm := hdisj ⟨g,hg⟩
  have ha : gapInArc a b g=true := by simpa [gapInArc, CakeArcOrder.Hit] using hA
  have hb : gapInArc c d g=true := by simpa [gapInArc, CakeArcOrder.Hit] using hB
  simp only [ha,hb,Bool.and_self,Bool.true_eq_false] at hm

end CakeSevenComplete

namespace CakeSevenComplete
open CakeQuantileSeven CakeQuantiles CakeOrderedMarks CakeQuantileArcMasses
  CakeSevenMaskTransport

theorem division_from_index_arcs (μ : Fin 3 → Measure ℝ)
    (X : ℕ → ℝ) (hX : Monotone X) (h0 : X 0=0) (h14 : X 14=1)
    (a b c d : ℕ) (ha : a<14) (hb : b<14) (hc : c<14) (hd : d<14)
    (habne : a≠b) (hcdne : c≠d)
    (hdisj : ∀ g, g<14 → CakeArcOrder.Hit a b g → CakeArcOrder.Hit c d g → False)
    (hB : ENNReal.ofReal (2/7:ℝ)≤μ 0 (indexArc X a b))
    (hC : ENNReal.ofReal (1/7:ℝ)≤μ 1 (indexArc X c d))
    (hH : μ 2 (Set.Icc 0 1)=1)
    (hcost : μ 2 (indexArc X a b ∪ indexArc X c d)≤ENNReal.ofReal (3/7:ℝ)) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2/7:ℝ),1/7,4/7] 4 := by
  have hlo (k : ℕ) : 0≤X k := by rw [←h0]; exact hX (Nat.zero_le k)
  have hhi (k : ℕ) (hk : k≤14) : X k≤1 := by rw [←h14]; exact hX hk
  rcases CakeArcOrder.classify_disjoint_arcs ha hb hc hd habne hcdne hdisj with
    ⟨hab,hcd,hsep⟩|⟨hba,hcd,hbc,hda⟩|⟨hab,hdc,hda,hbc⟩
  · rcases hsep with hbc|hda
    · apply CakeFourCuts.nonwrapped_BC μ (X a) (X b) (X c) (X d)
        (hlo a) (hX hab.le) (hX hbc) (hX hcd.le) (hhi d hd.le)
      · simpa only [indexArc,if_pos hab] using hB
      · simpa only [indexArc,if_pos hcd] using hC
      · exact hH
      · simpa only [indexArc,if_pos hab,if_pos hcd] using hcost
    · apply CakeFourCuts.nonwrapped_CB μ (X c) (X d) (X a) (X b)
        (hlo c) (hX hcd.le) (hX hda) (hX hab.le) (hhi b hb.le)
      · simpa only [indexArc,if_pos hab] using hB
      · simpa only [indexArc,if_pos hcd] using hC
      · exact hH
      · simpa only [indexArc,if_pos hab,if_pos hcd] using hcost
  · have hnab : ¬a<b := by omega
    apply CakeFourCuts.wrapped_B μ (X b) (X c) (X d) (X a)
      (hlo b) (hX hbc) (hX hcd.le) (hX hda) (hhi a ha.le)
    · simpa only [indexArc,if_neg hnab] using hB
    · simpa only [indexArc,if_pos hcd] using hC
    · exact hH
    · simpa only [indexArc,if_neg hnab,if_pos hcd] using hcost
  · have hncd : ¬c<d := by omega
    apply CakeFourCuts.wrapped_C μ (X d) (X a) (X b) (X c)
      (hlo d) (hX hda) (hX hab.le) (hX hbc) (hhi c hc.le)
    · simpa only [indexArc,if_pos hab] using hB
    · simpa only [indexArc,if_neg hncd] using hC
    · exact hH
    · simpa only [indexArc,if_pos hab,if_neg hncd] using hcost

theorem indexArc_of_embedding (X : ℕ → ℝ) (r : Fin 7 → Fin 14) (b : Fin 7 → ℝ)
    (hr : StrictMono r) (hb : StrictMono b) (hXr : ∀i,X (r i).val=b i) (i j : Fin 7) :
    indexArc X (r i).val (r j).val = circleArc (b i) (b j) := by
  have hcmp : (r i).val<(r j).val ↔ b i<b j := by
    change r i<r j ↔ b i<b j
    rw [hr.lt_iff_lt,hb.lt_iff_lt]
  unfold indexArc circleArc
  rw [hXr i,hXr j]
  by_cases hij : (r i).val<(r j).val
  · rw [if_pos hij,if_pos (hcmp.mp hij)]
  · rw [if_neg hij,if_neg (fun h=>hij (hcmp.mpr h))]
    exact Set.union_comm _ _

/-- Every checked, covering seven-mark certificate table yields an actual
four-cut division for the fixed three-agent demands (2,1,4)/7. -/
theorem division_of_checked_table (table : List Certificate)
    (hchecked : table.all checkCertificate=true)
    (hcomplete : table.map Prod.fst=compositions 7 7)
    (μ : Fin 3 → Measure ℝ) (hprob : ∀i,IsProbabilityMeasure (μ i))
    (hatom : ∀i,NullSingletonClass (μ i)) (hcake : ∀i,μ i (Set.Icc 0 1)=1) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2/7:ℝ),1/7,4/7] 4 := by
  classical
  have : IsProbabilityMeasure (μ 0) := hprob 0
  have : IsProbabilityMeasure (μ 1) := hprob 1
  have : IsProbabilityMeasure (μ 2) := hprob 2
  have : NullSingletonClass (μ 0) := hatom 0
  have : NullSingletonClass (μ 1) := hatom 1
  have : NullSingletonClass (μ 2) := hatom 2
  obtain ⟨b,c,θ,hb,hc,hb0,hbm,hcm,hθ,hbval,hcval,hne⟩ :=
    nonatomic_seven_marks (μ 0) (μ 1) (hcake 0) (hcake 1)
  obtain ⟨x,r,d,runs,hx,hr,hd,hx0,hr0,hxr,hxd,hxm,hrd,hcover,hlen,hsum,hruns,hred,hblue⟩ :=
    exists_ordered_run_encoding b c hb hc hb0 hbm hcm hne
  obtain ⟨y,hy,hy0,hy14,hyx,hymem⟩ := exists_cut_vector x hx hx0 hxm
  let X : ℕ→ℝ := extendCut y
  have hX : Monotone X := extendCut_monotone y hy.monotone
  have hX0 : X 0=0 := by simpa using (extendCut_fin y (0:Fin 15)).trans hy0
  have hX14 : X 14=1 := by simpa using (extendCut_fin y (Fin.last 14)).trans hy14
  have hXr (i : Fin 7) : X (r i).val=b i := by
    exact (extendCut_fin y (r i).castSucc).trans ((hyx (r i)).trans (hxr i))
  have hXd (j : Fin 7) : X (d j).val=c j := by
    exact (extendCut_fin y (d j).castSucc).trans ((hyx (d j)).trans (hxd j))
  let g : Fin 14→ℝ := fun k=>CakeGapWeights.gap (μ 2) X k.val
  have hg : ∀k,0≤g k := fun k=>CakeGapWeights.gap_nonneg (μ 2) X k.val
  have hgsum : ∑k,g k=1 := gap_weights_sum (μ 2) X hX hX0 hX14 (hcake 2)
  obtain ⟨i,j,hdisjoint,hcost⟩ := table_gap_choice table hchecked hcomplete runs hruns g hg hgsum
  let a : ℕ := (r i).val
  let b' : ℕ := (r (i+2)).val
  let c' : ℕ := (d j).val
  let d' : ℕ := (d (j+1)).val
  have hA (k : Fin 14) : redGap runs i.val k.val=gapInArc a b' k.val :=
    redGap_of_positions r runs hred i k.val
  have hC (k : Fin 14) : blueGap runs j.val k.val=gapInArc c' d' k.val :=
    blueGap_of_positions d runs hblue j k.val
  have hdisj : ∀k:Fin 14,(gapInArc a b' k.val && gapInArc c' d' k.val)=false := by
    intro k
    rw [←hA k,←hC k]
    exact hdisjoint k
  have hcost' : (∑k:Fin 14,if gapInArc a b' k.val || gapInArc c' d' k.val then g k else 0)≤(3/7:ℝ) := by
    simpa only [hA,hC] using hcost
  have hBmass : (μ 0).real (indexArc X a b')=(2/7:ℝ) := by
    change (μ 0).real (indexArc X (r i).val (r (i+2)).val)=(2/7:ℝ)
    rw [indexArc_of_embedding X r b hr hb hXr i (i+2)]
    exact red_arc_mass (μ 0) (hcake 0) b hb hbm hbval i
  have hCmass : (μ 1).real (indexArc X c' d')=(1/7:ℝ) := by
    change (μ 1).real (indexArc X (d j).val (d (j+1)).val)=(1/7:ℝ)
    rw [indexArc_of_embedding X d c hd hc hXd j (j+1)]
    exact blue_arc_mass (μ 1) (hcake 1) c θ hc hcm hcval j
  have hBquota : ENNReal.ofReal (2/7:ℝ)≤μ 0 (indexArc X a b') := by
    rw [←ofReal_measureReal,hBmass]
  have hCquota : ENNReal.ofReal (1/7:ℝ)≤μ 1 (indexArc X c' d') := by
    rw [←ofReal_measureReal,hCmass]
  have habne : a≠b' := by
    intro heq
    have h := hr.injective (Fin.ext heq)
    exact step_two_ne i h.symm
  have hcdne : c'≠d' := by
    intro heq
    have h := hd.injective (Fin.ext heq)
    exact step_one_ne j h.symm
  exact division_from_index_arcs μ X hX hX0 hX14 a b' c' d'
    (r i).isLt (r (i+2)).isLt (d j).isLt (d (j+1)).isLt habne hcdne
    (disjoint_hits_of_masks a b' c' d' hdisj) hBquota hCquota (hcake 2)
    (two_arc_cost_bound (μ 2) X hX hX0 hX14 a b' c' d'
      (r i).isLt (r (i+2)).isLt (d j).isLt (d (j+1)).isLt hdisj hcost')

end CakeSevenComplete


/-! Actual kernel-verified 1716-entry table, shared checker definitions above. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CakeQuantileSeven

def chunk_000 : List Certificate := [
  ([0, 0, 0, 0, 0, 0, 7], 3, [(2, 0, 1), (0, 1, 1), (4, 4, 1)]),
  ([0, 0, 0, 0, 0, 1, 6], 3, [(4, 1, 1), (0, 2, 1), (2, 5, 1)]),
  ([0, 0, 0, 0, 0, 2, 5], 3, [(2, 2, 1), (4, 4, 1), (0, 5, 1)]),
  ([0, 0, 0, 0, 0, 3, 4], 6, [(3, 1, 1), (0, 2, 1), (4, 3, 1), (2, 4, 1), (1, 5, 1), (6, 0, 1)]),
  ([0, 0, 0, 0, 0, 4, 3], 6, [(3, 0, 1), (0, 1, 1), (1, 3, 1), (4, 4, 1), (2, 5, 1), (6, 2, 1)]),
  ([0, 0, 0, 0, 0, 5, 2], 9, [(0, 1, 1), (3, 1, 1), (2, 2, 1), (3, 2, 1), (1, 3, 2), (4, 5, 1), (6, 0, 2)]),
  ([0, 0, 0, 0, 0, 6, 1], 3, [(1, 0, 1), (3, 1, 1), (6, 2, 1)]),
  ([0, 0, 0, 0, 0, 7, 0], 3, [(3, 0, 1), (1, 1, 1), (6, 4, 1)]),
  ([0, 0, 0, 0, 1, 0, 6], 3, [(2, 1, 1), (4, 2, 1), (0, 3, 1)]),
  ([0, 0, 0, 0, 1, 1, 5], 3, [(4, 2, 1), (2, 3, 1), (0, 4, 1)]),
  ([0, 0, 0, 0, 1, 2, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 0, 0, 0, 1, 3, 3], 26, [(0, 1, 1), (1, 1, 4), (2, 2, 2), (2, 3, 3), (3, 3, 2), (3, 4, 1), (4, 4, 4), (0, 5, 4), (3, 5, 1), (6, 0, 1), (6, 2, 3)]),
  ([0, 0, 0, 0, 1, 4, 2], 3, [(3, 2, 1), (1, 3, 1), (6, 1, 1)]),
  ([0, 0, 0, 0, 1, 5, 1], 3, [(1, 1, 1), (3, 3, 1), (6, 2, 1)]),
  ([0, 0, 0, 0, 1, 6, 0], 3, [(3, 1, 1), (1, 2, 1), (6, 3, 1)]),
  ([0, 0, 0, 0, 2, 0, 5], 3, [(0, 2, 1), (2, 3, 1), (4, 5, 1)]),
  ([0, 0, 0, 0, 2, 1, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([0, 0, 0, 0, 2, 2, 3], 42, [(0, 0, 3), (1, 1, 3), (2, 2, 7), (0, 3, 7), (0, 4, 1), (1, 4, 1), (2, 4, 4), (3, 4, 1), (3, 5, 3), (4, 5, 4), (6, 1, 4), (5, 0, 4)]),
  ([0, 0, 0, 0, 2, 3, 2], 28, [(0, 0, 1), (2, 0, 1), (1, 1, 5), (2, 2, 2), (0, 3, 4), (3, 3, 3), (2, 4, 2), (3, 5, 2), (6, 2, 5), (5, 0, 3)]),
  ([0, 0, 0, 0, 2, 4, 1], 3, [(3, 2, 1), (1, 4, 1), (6, 3, 1)]),
  ([0, 0, 0, 0, 2, 5, 0], 9, [(1, 2, 2), (3, 3, 2), (0, 4, 1), (2, 4, 1), (6, 1, 1), (6, 5, 1), (5, 0, 1)]),
  ([0, 0, 0, 0, 3, 0, 4], 3, [(0, 3, 1), (4, 4, 1), (2, 5, 1)]),
  ([0, 0, 0, 0, 3, 1, 3], 42, [(0, 0, 1), (2, 0, 2), (1, 1, 4), (2, 1, 3), (2, 2, 3), (2, 3, 3), (3, 3, 4), (0, 4, 3), (4, 4, 4), (0, 5, 7), (6, 2, 4), (5, 0, 4)]),
  ([0, 0, 0, 0, 3, 2, 2], 14, [(0, 0, 2), (1, 1, 2), (0, 2, 1), (2, 2, 2), (3, 3, 1), (3, 4, 1), (2, 5, 1), (6, 3, 2), (5, 0, 1), (5, 1, 1)]),
  ([0, 0, 0, 0, 3, 3, 1], 26, [(0, 0, 1), (0, 1, 1), (1, 1, 4), (0, 2, 1), (2, 2, 4), (0, 3, 1), (3, 3, 4), (0, 4, 1), (2, 5, 1), (6, 4, 4), (5, 0, 4)]),
  ([0, 0, 0, 0, 3, 4, 0], 6, [(0, 1, 1), (1, 3, 1), (3, 4, 1), (2, 5, 1), (6, 2, 1), (5, 0, 1)]),
  ([0, 0, 0, 0, 4, 0, 3], 3, [(0, 1, 1), (2, 2, 1), (5, 0, 1)]),
  ([0, 0, 0, 0, 4, 1, 2], 3, [(0, 1, 1), (2, 2, 1), (5, 0, 1)]),
  ([0, 0, 0, 0, 4, 2, 1], 3, [(0, 1, 1), (2, 2, 1), (5, 0, 1)]),
  ([0, 0, 0, 0, 4, 3, 0], 6, [(0, 1, 1), (1, 2, 1), (3, 4, 1), (2, 5, 1), (6, 3, 1), (5, 0, 1)]),
  ([0, 0, 0, 0, 5, 0, 2], 3, [(0, 0, 1), (2, 2, 1), (5, 1, 1)]),
  ([0, 0, 0, 0, 5, 1, 1], 3, [(0, 0, 1), (2, 2, 1), (5, 1, 1)])
]
theorem chunk_000_checked : chunk_000.all checkCertificate = true := by
  decide

def chunk_001 : List Certificate := [
  ([0, 0, 0, 0, 5, 2, 0], 6, [(0, 0, 1), (1, 2, 1), (2, 3, 1), (3, 5, 1), (6, 4, 1), (5, 1, 1)]),
  ([0, 0, 0, 0, 6, 0, 1], 3, [(2, 1, 1), (0, 3, 1), (5, 2, 1)]),
  ([0, 0, 0, 0, 6, 1, 0], 3, [(0, 0, 1), (2, 3, 1), (5, 2, 1)]),
  ([0, 0, 0, 0, 7, 0, 0], 3, [(2, 1, 1), (0, 2, 1), (5, 4, 1)]),
  ([0, 0, 0, 1, 0, 0, 6], 3, [(0, 1, 1), (4, 2, 1), (2, 3, 1)]),
  ([0, 0, 0, 1, 0, 1, 5], 3, [(0, 2, 1), (2, 3, 1), (4, 5, 1)]),
  ([0, 0, 0, 1, 0, 2, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([0, 0, 0, 1, 0, 3, 3], 20, [(1, 1, 3), (2, 1, 1), (3, 2, 1), (2, 3, 2), (3, 3, 2), (3, 4, 1), (4, 4, 3), (0, 5, 4), (6, 2, 3)]),
  ([0, 0, 0, 1, 0, 4, 2], 3, [(3, 2, 1), (1, 3, 1), (6, 1, 1)]),
  ([0, 0, 0, 1, 0, 5, 1], 3, [(1, 1, 1), (3, 3, 1), (6, 2, 1)]),
  ([0, 0, 0, 1, 0, 6, 0], 3, [(1, 1, 1), (3, 2, 1), (6, 3, 1)]),
  ([0, 0, 0, 1, 1, 0, 5], 3, [(2, 2, 1), (0, 3, 1), (4, 5, 1)]),
  ([0, 0, 0, 1, 1, 1, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([0, 0, 0, 1, 1, 2, 3], 22, [(1, 2, 3), (2, 2, 1), (0, 3, 5), (2, 4, 4), (4, 4, 1), (3, 5, 3), (4, 5, 2), (6, 1, 2), (6, 2, 1)]),
  ([0, 0, 0, 1, 1, 3, 2], 11, [(2, 1, 1), (3, 2, 1), (1, 3, 2), (3, 3, 2), (1, 4, 1), (0, 5, 1), (6, 2, 3)]),
  ([0, 0, 0, 1, 1, 4, 1], 3, [(3, 2, 1), (1, 4, 1), (6, 3, 1)]),
  ([0, 0, 0, 1, 1, 5, 0], 3, [(3, 2, 1), (1, 3, 1), (6, 4, 1)]),
  ([0, 0, 0, 1, 2, 0, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([0, 0, 0, 1, 2, 1, 3], 11, [(2, 1, 1), (0, 2, 1), (2, 3, 1), (0, 4, 3), (4, 4, 1), (2, 5, 2), (4, 5, 2)]),
  ([0, 0, 0, 1, 2, 2, 2], 35, [(2, 1, 4), (0, 2, 5), (2, 2, 2), (0, 3, 4), (1, 4, 3), (2, 4, 4), (0, 5, 1), (3, 5, 3), (4, 5, 3), (6, 3, 3), (5, 1, 3)]),
  ([0, 0, 0, 1, 2, 3, 1], 22, [(0, 0, 1), (1, 1, 1), (2, 1, 1), (1, 2, 2), (1, 3, 3), (3, 3, 5), (1, 4, 1), (3, 5, 1), (6, 4, 7)]),
  ([0, 0, 0, 1, 2, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 0, 0, 1, 3, 0, 3], 11, [(0, 1, 3), (2, 2, 1), (2, 3, 1), (2, 4, 2), (0, 5, 1), (4, 5, 1), (5, 2, 2)]),
  ([0, 0, 0, 1, 3, 1, 2], 11, [(0, 1, 4), (2, 2, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 2, 3)]),
  ([0, 0, 0, 1, 3, 2, 1], 11, [(0, 1, 3), (2, 2, 2), (1, 3, 1), (2, 4, 1), (6, 1, 1), (5, 0, 1), (5, 2, 2)]),
  ([0, 0, 0, 1, 3, 3, 0], 26, [(0, 1, 4), (2, 1, 1), (2, 2, 2), (1, 3, 5), (2, 5, 1), (3, 5, 4), (6, 4, 5), (5, 0, 1), (5, 2, 3)]),
  ([0, 0, 0, 1, 4, 0, 2], 3, [(2, 2, 1), (0, 3, 1), (5, 1, 1)]),
  ([0, 0, 0, 1, 4, 1, 1], 3, [(2, 2, 1), (0, 3, 1), (5, 1, 1)]),
  ([0, 0, 0, 1, 4, 2, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 1, 1)]),
  ([0, 0, 0, 1, 5, 0, 1], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([0, 0, 0, 1, 5, 1, 0], 3, [(2, 1, 1), (0, 3, 1), (5, 2, 1)]),
  ([0, 0, 0, 1, 6, 0, 0], 3, [(2, 2, 1), (0, 4, 1), (5, 3, 1)])
]
theorem chunk_001_checked : chunk_001.all checkCertificate = true := by
  decide

def chunk_002 : List Certificate := [
  ([0, 0, 0, 2, 0, 0, 5], 3, [(2, 2, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 0, 0, 2, 0, 1, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 0, 0, 2, 0, 2, 3], 16, [(0, 0, 1), (1, 2, 3), (0, 3, 2), (3, 3, 1), (4, 4, 3), (2, 5, 3), (6, 0, 1), (6, 1, 2)]),
  ([0, 0, 0, 2, 0, 3, 2], 8, [(1, 0, 1), (1, 1, 1), (1, 3, 1), (3, 3, 2), (6, 2, 3)]),
  ([0, 0, 0, 2, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 0, 0, 2, 0, 5, 0], 3, [(1, 2, 1), (3, 3, 1), (6, 4, 1)]),
  ([0, 0, 0, 2, 1, 0, 4], 3, [(0, 3, 1), (4, 4, 1), (2, 5, 1)]),
  ([0, 0, 0, 2, 1, 1, 3], 24, [(0, 0, 2), (0, 1, 2), (1, 2, 1), (2, 3, 3), (1, 4, 1), (4, 4, 6), (0, 5, 3), (2, 5, 4), (6, 2, 2)]),
  ([0, 0, 0, 2, 1, 2, 2], 21, [(0, 0, 2), (1, 0, 1), (0, 1, 2), (1, 2, 3), (2, 3, 1), (2, 4, 3), (3, 4, 1), (4, 5, 4), (6, 1, 1), (6, 3, 3)]),
  ([0, 0, 0, 2, 1, 3, 1], 11, [(1, 0, 1), (1, 2, 1), (1, 3, 1), (3, 3, 3), (1, 4, 1), (6, 1, 1), (6, 4, 3)]),
  ([0, 0, 0, 2, 1, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 0, 0, 2, 2, 0, 3], 8, [(0, 2, 1), (4, 0, 1), (1, 3, 1), (0, 4, 1), (4, 4, 1), (2, 5, 2), (6, 1, 1)]),
  ([0, 0, 0, 2, 2, 1, 2], 21, [(1, 1, 2), (0, 2, 4), (2, 3, 3), (4, 0, 1), (1, 4, 2), (2, 4, 1), (4, 5, 3), (6, 0, 2), (6, 1, 2), (5, 0, 1)]),
  ([0, 0, 0, 2, 2, 2, 1], 35, [(1, 1, 3), (0, 2, 3), (1, 3, 7), (2, 4, 3), (3, 4, 3), (4, 0, 3), (6, 0, 1), (6, 1, 4), (6, 2, 4), (6, 4, 1), (5, 0, 3)]),
  ([0, 0, 0, 2, 2, 3, 0], 14, [(0, 2, 2), (2, 2, 1), (2, 3, 1), (1, 4, 3), (3, 5, 2), (6, 3, 2), (6, 5, 1), (5, 0, 1), (5, 1, 1)]),
  ([0, 0, 0, 2, 3, 0, 2], 8, [(0, 0, 1), (1, 2, 1), (2, 2, 1), (0, 3, 1), (4, 0, 1), (6, 3, 1), (5, 1, 2)]),
  ([0, 0, 0, 2, 3, 1, 1], 11, [(0, 0, 1), (2, 2, 2), (0, 3, 1), (1, 3, 2), (4, 0, 1), (6, 2, 1), (6, 4, 1), (5, 1, 2)]),
  ([0, 0, 0, 2, 3, 2, 0], 14, [(0, 0, 1), (0, 1, 1), (2, 2, 2), (1, 3, 3), (4, 0, 2), (6, 2, 1), (6, 4, 1), (6, 5, 1), (5, 1, 2)]),
  ([0, 0, 0, 2, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([0, 0, 0, 2, 4, 1, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([0, 0, 0, 2, 5, 0, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 4, 1)]),
  ([0, 0, 0, 3, 0, 0, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([0, 0, 0, 3, 0, 1, 3], 16, [(0, 0, 3), (4, 1, 2), (2, 3, 2), (1, 4, 3), (2, 5, 1), (4, 5, 2), (6, 1, 1), (6, 2, 2)]),
  ([0, 0, 0, 3, 0, 2, 2], 8, [(1, 0, 1), (1, 1, 1), (1, 2, 1), (4, 0, 2), (6, 1, 2), (6, 3, 1)]),
  ([0, 0, 0, 3, 0, 3, 1], 11, [(1, 0, 1), (1, 1, 1), (1, 2, 1), (1, 3, 1), (3, 3, 3), (6, 4, 4)]),
  ([0, 0, 0, 3, 0, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 0, 0, 3, 1, 0, 3], 8, [(1, 1, 1), (0, 2, 1), (0, 3, 1), (4, 4, 2), (2, 5, 2), (6, 0, 1)]),
  ([0, 0, 0, 3, 1, 1, 2], 8, [(1, 1, 1), (0, 2, 1), (1, 3, 1), (4, 1, 1), (2, 4, 1), (4, 5, 1), (6, 0, 2)]),
  ([0, 0, 0, 3, 1, 2, 1], 11, [(1, 1, 2), (1, 2, 1), (1, 4, 1), (4, 0, 1), (4, 1, 2), (6, 0, 3), (6, 3, 1)]),
  ([0, 0, 0, 3, 1, 3, 0], 42, [(1, 1, 1), (0, 2, 4), (1, 2, 3), (1, 3, 7), (2, 4, 3), (3, 4, 4), (2, 5, 1), (4, 0, 3), (4, 1, 1), (6, 1, 5), (6, 5, 6), (5, 0, 4)]),
  ([0, 0, 0, 3, 2, 0, 2], 24, [(0, 0, 5), (1, 2, 4), (2, 3, 2), (4, 0, 2), (4, 1, 2), (6, 2, 1), (6, 3, 3), (5, 1, 5)]),
  ([0, 0, 0, 3, 2, 1, 1], 22, [(0, 0, 3), (1, 1, 1), (1, 2, 2), (1, 3, 2), (2, 3, 3), (4, 0, 2), (4, 1, 1), (6, 2, 3), (6, 4, 2), (5, 1, 3)])
]
theorem chunk_002_checked : chunk_002.all checkCertificate = true := by
  decide

def chunk_003 : List Certificate := [
  ([0, 0, 0, 3, 2, 2, 0], 14, [(0, 0, 2), (1, 2, 1), (1, 3, 1), (2, 3, 2), (1, 4, 1), (4, 0, 1), (4, 1, 1), (6, 2, 2), (6, 5, 1), (5, 1, 2)]),
  ([0, 0, 0, 3, 3, 0, 1], 20, [(0, 0, 4), (1, 3, 1), (2, 3, 3), (1, 4, 2), (4, 1, 3), (6, 1, 1), (6, 4, 2), (5, 2, 4)]),
  ([0, 0, 0, 3, 3, 1, 0], 26, [(0, 0, 4), (1, 2, 1), (1, 3, 1), (2, 3, 4), (1, 4, 3), (4, 1, 4), (6, 0, 1), (6, 1, 1), (6, 4, 2), (6, 5, 1), (5, 2, 4)]),
  ([0, 0, 0, 3, 4, 0, 0], 6, [(0, 2, 1), (1, 3, 1), (2, 5, 1), (4, 1, 1), (6, 4, 1), (5, 0, 1)]),
  ([0, 0, 0, 4, 0, 0, 3], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 4, 0, 1, 2], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 4, 0, 2, 1], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 4, 0, 3, 0], 3, [(1, 2, 1), (4, 0, 1), (6, 1, 1)]),
  ([0, 0, 0, 4, 1, 0, 2], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 4, 1, 1, 1], 3, [(1, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 0, 0, 4, 1, 2, 0], 3, [(1, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 0, 0, 4, 2, 0, 1], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 4, 2, 1, 0], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 4, 3, 0, 0], 6, [(0, 2, 1), (1, 3, 1), (2, 5, 1), (4, 1, 1), (6, 4, 1), (5, 0, 1)]),
  ([0, 0, 0, 5, 0, 0, 2], 9, [(0, 0, 1), (1, 2, 1), (1, 3, 1), (4, 1, 2), (4, 2, 1), (2, 5, 1), (6, 0, 1), (6, 3, 1)]),
  ([0, 0, 0, 5, 0, 1, 1], 3, [(1, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 0, 5, 0, 2, 0], 9, [(1, 0, 1), (1, 3, 2), (3, 5, 1), (4, 1, 2), (6, 0, 1), (6, 2, 2)]),
  ([0, 0, 0, 5, 1, 0, 1], 3, [(1, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 0, 5, 1, 1, 0], 3, [(1, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 5, 2, 0, 0], 3, [(1, 3, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 6, 0, 0, 1], 3, [(1, 4, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 0, 6, 0, 1, 0], 3, [(1, 4, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 0, 0, 6, 1, 0, 0], 3, [(1, 3, 1), (4, 0, 1), (6, 1, 1)]),
  ([0, 0, 0, 7, 0, 0, 0], 3, [(1, 2, 1), (4, 0, 1), (6, 5, 1)]),
  ([0, 0, 1, 0, 0, 0, 6], 3, [(0, 1, 1), (2, 2, 1), (4, 5, 1)]),
  ([0, 0, 1, 0, 0, 1, 5], 3, [(4, 2, 1), (0, 3, 1), (2, 4, 1)]),
  ([0, 0, 1, 0, 0, 2, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([0, 0, 1, 0, 0, 3, 3], 20, [(3, 1, 4), (1, 2, 1), (0, 3, 3), (1, 3, 1), (1, 4, 1), (2, 4, 3), (1, 5, 1), (4, 5, 3), (6, 2, 3)]),
  ([0, 0, 1, 0, 0, 4, 2], 3, [(1, 2, 1), (3, 3, 1), (6, 1, 1)]),
  ([0, 0, 1, 0, 0, 5, 1], 3, [(3, 1, 1), (1, 3, 1), (6, 2, 1)]),
  ([0, 0, 1, 0, 0, 6, 0], 3, [(3, 1, 1), (1, 2, 1), (6, 4, 1)]),
  ([0, 0, 1, 0, 1, 0, 5], 3, [(2, 2, 1), (0, 3, 1), (4, 5, 1)])
]
theorem chunk_003_checked : chunk_003.all checkCertificate = true := by
  decide

def chunk_004 : List Certificate := [
  ([0, 0, 1, 0, 1, 1, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([0, 0, 1, 0, 1, 2, 3], 22, [(1, 2, 3), (3, 2, 1), (0, 3, 5), (3, 4, 2), (4, 4, 3), (2, 5, 5), (6, 1, 2), (6, 2, 1)]),
  ([0, 0, 1, 0, 1, 3, 2], 11, [(1, 1, 1), (1, 2, 1), (0, 3, 1), (2, 3, 1), (3, 3, 2), (3, 4, 1), (1, 5, 1), (6, 2, 3)]),
  ([0, 0, 1, 0, 1, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 0, 1, 0, 1, 5, 0], 3, [(1, 2, 1), (3, 3, 1), (6, 5, 1)]),
  ([0, 0, 1, 0, 2, 0, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([0, 0, 1, 0, 2, 1, 3], 11, [(2, 1, 1), (2, 2, 1), (2, 3, 1), (0, 4, 1), (4, 4, 3), (0, 5, 3), (2, 5, 1)]),
  ([0, 0, 1, 0, 2, 2, 2], 35, [(0, 1, 3), (2, 1, 1), (1, 2, 3), (2, 2, 4), (2, 3, 4), (0, 4, 7), (2, 5, 1), (3, 5, 3), (4, 5, 3), (6, 3, 3), (5, 1, 3)]),
  ([0, 0, 1, 0, 2, 3, 1], 11, [(0, 1, 1), (1, 2, 2), (2, 3, 2), (3, 3, 1), (0, 4, 1), (3, 5, 1), (6, 4, 2), (5, 1, 1)]),
  ([0, 0, 1, 0, 2, 4, 0], 3, [(3, 3, 1), (1, 5, 1), (6, 4, 1)]),
  ([0, 0, 1, 0, 3, 0, 3], 11, [(0, 1, 4), (2, 2, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 2, 3)]),
  ([0, 0, 1, 0, 3, 1, 2], 11, [(0, 1, 1), (0, 2, 1), (2, 2, 3), (0, 3, 1), (0, 4, 1), (2, 5, 1), (5, 1, 3)]),
  ([0, 0, 1, 0, 3, 2, 1], 11, [(0, 1, 4), (2, 2, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 2, 3)]),
  ([0, 0, 1, 0, 3, 3, 0], 20, [(0, 1, 4), (1, 2, 1), (1, 3, 2), (2, 3, 2), (2, 4, 2), (3, 5, 3), (6, 4, 2), (6, 5, 1), (5, 2, 3)]),
  ([0, 0, 1, 0, 4, 0, 2], 3, [(2, 2, 1), (0, 3, 1), (5, 1, 1)]),
  ([0, 0, 1, 0, 4, 1, 1], 3, [(2, 2, 1), (0, 3, 1), (5, 1, 1)]),
  ([0, 0, 1, 0, 4, 2, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 1, 1)]),
  ([0, 0, 1, 0, 5, 0, 1], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([0, 0, 1, 0, 5, 1, 0], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([0, 0, 1, 0, 6, 0, 0], 3, [(2, 3, 1), (0, 5, 1), (5, 4, 1)]),
  ([0, 0, 1, 1, 0, 0, 5], 3, [(2, 2, 1), (0, 3, 1), (4, 5, 1)]),
  ([0, 0, 1, 1, 0, 1, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 0, 1, 1, 0, 2, 3], 16, [(1, 2, 2), (4, 0, 1), (2, 3, 3), (3, 4, 2), (4, 4, 2), (0, 5, 4), (6, 1, 1), (6, 2, 1)]),
  ([0, 0, 1, 1, 0, 3, 2], 16, [(0, 0, 1), (1, 1, 1), (1, 2, 1), (1, 3, 3), (3, 3, 3), (3, 4, 1), (3, 5, 1), (6, 2, 5)]),
  ([0, 0, 1, 1, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 0, 1, 1, 0, 5, 0], 3, [(1, 2, 1), (3, 3, 1), (6, 5, 1)]),
  ([0, 0, 1, 1, 1, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 0, 1, 1, 1, 1, 3], 16, [(0, 0, 1), (0, 1, 1), (2, 2, 1), (2, 3, 1), (2, 4, 3), (4, 4, 3), (0, 5, 4), (4, 5, 2)]),
  ([0, 0, 1, 1, 1, 2, 2], 18, [(0, 2, 1), (1, 2, 2), (2, 3, 3), (0, 4, 3), (3, 4, 2), (0, 5, 1), (2, 5, 2), (4, 5, 2), (6, 3, 2)]),
  ([0, 0, 1, 1, 1, 3, 1], 8, [(1, 2, 1), (2, 3, 1), (3, 3, 2), (0, 4, 1), (1, 5, 1), (6, 4, 2)]),
  ([0, 0, 1, 1, 1, 4, 0], 3, [(1, 4, 1), (3, 5, 1), (6, 3, 1)]),
  ([0, 0, 1, 1, 2, 0, 3], 16, [(0, 1, 1), (2, 2, 1), (4, 0, 1), (2, 3, 1), (0, 4, 5), (4, 4, 1), (2, 5, 3), (4, 5, 3)])
]
theorem chunk_004_checked : chunk_004.all checkCertificate = true := by
  decide

def chunk_005 : List Certificate := [
  ([0, 0, 1, 1, 2, 1, 2], 28, [(0, 2, 5), (0, 3, 3), (1, 3, 2), (0, 4, 1), (2, 4, 4), (3, 4, 2), (2, 5, 5), (4, 5, 2), (6, 3, 2), (5, 2, 2)]),
  ([0, 0, 1, 1, 2, 2, 1], 18, [(0, 1, 2), (1, 1, 1), (2, 2, 1), (1, 3, 4), (2, 3, 1), (3, 4, 2), (6, 2, 2), (6, 4, 3), (5, 2, 2)]),
  ([0, 0, 1, 1, 2, 3, 0], 22, [(0, 1, 2), (0, 2, 1), (2, 2, 1), (1, 4, 5), (2, 5, 2), (3, 5, 3), (6, 3, 5), (5, 2, 3)]),
  ([0, 0, 1, 1, 3, 0, 2], 8, [(0, 0, 1), (2, 2, 2), (0, 3, 2), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([0, 0, 1, 1, 3, 1, 1], 8, [(0, 0, 1), (0, 2, 1), (2, 2, 2), (0, 3, 1), (5, 1, 1), (5, 3, 2)]),
  ([0, 0, 1, 1, 3, 2, 0], 11, [(2, 2, 2), (0, 3, 2), (1, 3, 1), (0, 4, 1), (2, 5, 1), (6, 2, 1), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([0, 0, 1, 1, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([0, 0, 1, 1, 4, 1, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([0, 0, 1, 1, 5, 0, 0], 3, [(2, 2, 1), (0, 4, 1), (5, 3, 1)]),
  ([0, 0, 1, 2, 0, 0, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([0, 0, 1, 2, 0, 1, 3], 16, [(0, 0, 1), (0, 2, 1), (4, 1, 1), (0, 3, 1), (0, 4, 2), (4, 4, 4), (0, 5, 1), (2, 5, 5)]),
  ([0, 0, 1, 2, 0, 2, 2], 33, [(0, 0, 3), (1, 2, 3), (1, 3, 2), (3, 3, 1), (4, 1, 3), (2, 4, 5), (3, 4, 3), (0, 5, 5), (3, 5, 1), (4, 5, 2), (6, 3, 5)]),
  ([0, 0, 1, 2, 0, 3, 1], 8, [(1, 1, 1), (1, 2, 1), (1, 3, 1), (3, 3, 2), (6, 4, 3)]),
  ([0, 0, 1, 2, 0, 4, 0], 3, [(3, 4, 1), (1, 5, 1), (6, 3, 1)]),
  ([0, 0, 1, 2, 1, 0, 3], 8, [(0, 1, 1), (4, 0, 1), (0, 4, 1), (4, 4, 2), (0, 5, 1), (2, 5, 2)]),
  ([0, 0, 1, 2, 1, 1, 2], 5, [(0, 1, 1), (2, 3, 1), (1, 4, 1), (4, 5, 1), (6, 2, 1)]),
  ([0, 0, 1, 2, 1, 2, 1], 28, [(0, 1, 2), (1, 2, 6), (1, 4, 3), (2, 4, 2), (3, 4, 2), (4, 1, 2), (6, 1, 1), (6, 2, 1), (6, 3, 7), (5, 1, 2)]),
  ([0, 0, 1, 2, 1, 3, 0], 11, [(1, 1, 1), (1, 2, 1), (1, 3, 1), (1, 5, 1), (3, 5, 3), (6, 4, 4)]),
  ([0, 0, 1, 2, 2, 0, 2], 18, [(0, 0, 3), (0, 2, 2), (1, 2, 2), (2, 3, 2), (4, 1, 2), (6, 3, 2), (5, 1, 3), (5, 2, 1), (5, 3, 1)]),
  ([0, 0, 1, 2, 2, 1, 1], 18, [(0, 0, 3), (0, 2, 1), (1, 2, 2), (0, 3, 1), (2, 3, 2), (4, 1, 2), (6, 3, 2), (5, 1, 3), (5, 2, 2)]),
  ([0, 0, 1, 2, 2, 2, 0], 35, [(1, 2, 3), (0, 3, 3), (2, 3, 3), (1, 4, 7), (3, 5, 3), (4, 1, 3), (6, 1, 1), (6, 2, 4), (6, 3, 1), (6, 5, 4), (5, 1, 3)]),
  ([0, 0, 1, 2, 3, 0, 1], 22, [(0, 0, 2), (1, 1, 2), (2, 3, 3), (0, 4, 3), (1, 4, 1), (4, 1, 3), (6, 3, 2), (6, 4, 1), (5, 2, 5)]),
  ([0, 0, 1, 2, 3, 1, 0], 22, [(0, 0, 2), (1, 1, 2), (2, 3, 2), (0, 4, 3), (1, 4, 1), (2, 4, 1), (4, 1, 3), (6, 3, 3), (5, 2, 5)]),
  ([0, 0, 1, 2, 4, 0, 0], 3, [(2, 4, 1), (0, 5, 1), (5, 3, 1)]),
  ([0, 0, 1, 3, 0, 0, 3], 11, [(0, 1, 2), (1, 2, 1), (4, 2, 2), (4, 4, 2), (1, 5, 1), (2, 5, 1), (6, 0, 1), (6, 1, 1)]),
  ([0, 0, 1, 3, 0, 1, 2], 16, [(0, 1, 1), (1, 2, 3), (1, 3, 1), (4, 1, 1), (4, 2, 3), (1, 4, 1), (4, 5, 1), (6, 0, 1), (6, 1, 4)]),
  ([0, 0, 1, 3, 0, 2, 1], 16, [(0, 1, 1), (1, 1, 3), (1, 3, 1), (4, 2, 5), (1, 5, 1), (6, 0, 1), (6, 1, 2), (6, 2, 1), (6, 4, 1)]),
  ([0, 0, 1, 3, 0, 3, 0], 11, [(1, 1, 1), (1, 2, 2), (1, 3, 1), (4, 1, 3), (6, 2, 2), (6, 4, 1), (6, 5, 1)]),
  ([0, 0, 1, 3, 1, 0, 2], 8, [(0, 0, 1), (1, 1, 2), (4, 2, 2), (6, 2, 1), (6, 3, 1), (5, 1, 1)]),
  ([0, 0, 1, 3, 1, 1, 1], 8, [(0, 0, 1), (1, 1, 1), (1, 2, 1), (4, 2, 2), (6, 1, 1), (6, 3, 1), (5, 1, 1)]),
  ([0, 0, 1, 3, 1, 2, 0], 11, [(1, 2, 1), (1, 3, 1), (1, 4, 1), (1, 5, 1), (4, 2, 3), (6, 1, 4)]),
  ([0, 0, 1, 3, 2, 0, 1], 22, [(0, 0, 2), (1, 1, 2), (0, 3, 3), (1, 4, 1), (2, 4, 3), (4, 1, 3), (6, 3, 2), (6, 4, 1), (5, 2, 5)])
]
theorem chunk_005_checked : chunk_005.all checkCertificate = true := by
  decide

def chunk_006 : List Certificate := [
  ([0, 0, 1, 3, 2, 1, 0], 22, [(0, 0, 2), (1, 1, 2), (0, 3, 3), (1, 4, 1), (2, 4, 3), (4, 1, 3), (6, 3, 2), (6, 4, 1), (5, 2, 5)]),
  ([0, 0, 1, 3, 3, 0, 0], 26, [(0, 0, 1), (1, 1, 1), (0, 2, 1), (1, 4, 1), (2, 4, 4), (0, 5, 3), (1, 5, 2), (4, 2, 4), (6, 1, 4), (5, 3, 5)]),
  ([0, 0, 1, 4, 0, 0, 2], 3, [(1, 1, 1), (4, 2, 1), (6, 3, 1)]),
  ([0, 0, 1, 4, 0, 1, 1], 3, [(1, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 1, 4, 0, 2, 0], 3, [(1, 2, 1), (4, 1, 1), (6, 3, 1)]),
  ([0, 0, 1, 4, 1, 0, 1], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 0, 1, 4, 1, 1, 0], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 0, 1, 4, 2, 0, 0], 3, [(1, 3, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 0, 1, 5, 0, 0, 1], 3, [(1, 4, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 1, 5, 0, 1, 0], 3, [(1, 4, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 1, 5, 1, 0, 0], 3, [(1, 4, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 0, 1, 6, 0, 0, 0], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 0, 2, 0, 0, 0, 5], 3, [(2, 2, 1), (0, 3, 1), (4, 5, 1)]),
  ([0, 0, 2, 0, 0, 1, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 0, 2, 0, 0, 2, 3], 11, [(3, 0, 1), (0, 2, 1), (0, 3, 2), (2, 4, 2), (3, 4, 1), (1, 5, 1), (4, 5, 2), (6, 2, 1)]),
  ([0, 0, 2, 0, 0, 3, 2], 11, [(3, 0, 1), (1, 2, 1), (1, 3, 2), (3, 3, 2), (3, 4, 1), (0, 5, 1), (6, 2, 3)]),
  ([0, 0, 2, 0, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 0, 2, 0, 0, 5, 0], 3, [(1, 2, 1), (3, 3, 1), (6, 5, 1)]),
  ([0, 0, 2, 0, 1, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 0, 2, 0, 1, 1, 3], 8, [(0, 0, 1), (2, 3, 1), (0, 4, 2), (4, 4, 1), (2, 5, 1), (3, 5, 1), (4, 5, 1)]),
  ([0, 0, 2, 0, 1, 2, 2], 18, [(0, 0, 3), (2, 3, 1), (3, 3, 2), (0, 4, 2), (3, 4, 3), (1, 5, 2), (2, 5, 1), (4, 5, 2), (6, 3, 2)]),
  ([0, 0, 2, 0, 1, 3, 1], 8, [(1, 2, 1), (1, 3, 1), (3, 3, 2), (0, 4, 1), (2, 5, 1), (6, 4, 2)]),
  ([0, 0, 2, 0, 1, 4, 0], 3, [(3, 3, 1), (1, 5, 1), (6, 4, 1)]),
  ([0, 0, 2, 0, 2, 0, 3], 16, [(0, 0, 1), (0, 1, 1), (2, 2, 1), (0, 3, 1), (0, 4, 3), (2, 4, 3), (2, 5, 1), (4, 5, 5)]),
  ([0, 0, 2, 0, 2, 1, 2], 28, [(0, 2, 1), (1, 2, 2), (0, 3, 7), (2, 4, 5), (3, 4, 2), (0, 5, 1), (2, 5, 4), (4, 5, 2), (6, 2, 2), (5, 2, 2)]),
  ([0, 0, 2, 0, 2, 2, 1], 18, [(2, 2, 2), (0, 3, 4), (2, 4, 3), (3, 4, 2), (0, 5, 1), (1, 5, 2), (6, 2, 1), (6, 3, 1), (5, 2, 2)]),
  ([0, 0, 2, 0, 2, 3, 0], 16, [(0, 1, 2), (1, 2, 1), (0, 3, 1), (2, 4, 1), (3, 4, 2), (1, 5, 2), (3, 5, 1), (6, 2, 1), (6, 3, 2), (5, 0, 2), (5, 2, 1)]),
  ([0, 0, 2, 0, 3, 0, 2], 8, [(0, 0, 1), (0, 2, 1), (2, 2, 2), (0, 3, 1), (5, 1, 1), (5, 3, 2)]),
  ([0, 0, 2, 0, 3, 1, 1], 8, [(0, 0, 1), (2, 2, 1), (0, 3, 2), (2, 3, 1), (5, 1, 1), (5, 2, 2)]),
  ([0, 0, 2, 0, 3, 2, 0], 16, [(0, 0, 2), (1, 2, 2), (1, 3, 1), (2, 3, 1), (0, 4, 1), (3, 5, 3), (6, 2, 1), (6, 4, 2), (5, 1, 2), (5, 3, 1)]),
  ([0, 0, 2, 0, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([0, 0, 2, 0, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)])
]
theorem chunk_006_checked : chunk_006.all checkCertificate = true := by
  decide

def chunk_007 : List Certificate := [
  ([0, 0, 2, 0, 5, 0, 0], 3, [(2, 2, 1), (0, 4, 1), (5, 3, 1)]),
  ([0, 0, 2, 1, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 0, 2, 1, 0, 1, 3], 8, [(0, 0, 1), (0, 3, 1), (3, 4, 1), (4, 4, 2), (0, 5, 1), (2, 5, 2)]),
  ([0, 0, 2, 1, 0, 2, 2], 18, [(0, 0, 1), (3, 0, 2), (0, 3, 3), (2, 4, 2), (3, 4, 3), (0, 5, 1), (1, 5, 2), (4, 5, 2), (6, 3, 2)]),
  ([0, 0, 2, 1, 0, 3, 1], 16, [(0, 1, 1), (3, 0, 1), (1, 2, 1), (1, 3, 3), (3, 3, 3), (3, 4, 1), (1, 5, 1), (6, 4, 5)]),
  ([0, 0, 2, 1, 0, 4, 0], 3, [(1, 4, 1), (3, 5, 1), (6, 3, 1)]),
  ([0, 0, 2, 1, 1, 0, 3], 8, [(0, 0, 1), (0, 1, 1), (0, 4, 1), (2, 4, 2), (4, 5, 3)]),
  ([0, 0, 2, 1, 1, 1, 2], 42, [(0, 1, 5), (1, 2, 5), (0, 3, 7), (4, 0, 1), (2, 4, 5), (3, 4, 2), (3, 5, 3), (4, 5, 4), (6, 0, 1), (6, 1, 2), (6, 2, 2), (5, 0, 5)]),
  ([0, 0, 2, 1, 1, 2, 1], 5, [(0, 1, 1), (1, 3, 1), (3, 4, 1), (6, 2, 1), (5, 0, 1)]),
  ([0, 0, 2, 1, 1, 3, 0], 8, [(0, 1, 1), (3, 4, 2), (1, 5, 2), (6, 2, 1), (6, 3, 1), (5, 0, 1)]),
  ([0, 0, 2, 1, 2, 0, 2], 28, [(0, 0, 3), (0, 2, 1), (1, 2, 2), (0, 3, 5), (2, 3, 2), (3, 0, 2), (4, 0, 2), (6, 2, 2), (5, 1, 7), (5, 2, 2)]),
  ([0, 0, 2, 1, 2, 1, 1], 28, [(0, 0, 3), (0, 2, 1), (1, 2, 2), (0, 3, 5), (2, 3, 2), (3, 0, 2), (4, 0, 2), (6, 2, 2), (5, 1, 7), (5, 2, 2)]),
  ([0, 0, 2, 1, 2, 2, 0], 21, [(0, 0, 3), (1, 3, 3), (2, 3, 1), (0, 4, 1), (1, 4, 1), (3, 5, 4), (6, 2, 2), (6, 4, 2), (5, 1, 3), (5, 2, 1)]),
  ([0, 0, 2, 1, 3, 0, 1], 11, [(0, 0, 1), (0, 3, 3), (2, 4, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 0, 2, 1, 3, 1, 0], 11, [(0, 0, 1), (0, 1, 1), (2, 3, 3), (0, 4, 2), (5, 2, 1), (5, 3, 1), (5, 4, 2)]),
  ([0, 0, 2, 1, 4, 0, 0], 3, [(2, 4, 1), (0, 5, 1), (5, 3, 1)]),
  ([0, 0, 2, 2, 0, 0, 3], 11, [(0, 0, 1), (0, 1, 1), (0, 2, 1), (0, 4, 1), (2, 4, 3), (4, 5, 4)]),
  ([0, 0, 2, 2, 0, 1, 2], 18, [(0, 1, 5), (1, 2, 1), (4, 0, 3), (4, 2, 2), (1, 5, 1), (3, 5, 2), (6, 2, 2), (5, 0, 2)]),
  ([0, 0, 2, 2, 0, 2, 1], 33, [(0, 1, 8), (1, 2, 2), (3, 0, 2), (1, 3, 3), (4, 0, 1), (4, 2, 4), (3, 5, 3), (6, 2, 2), (6, 4, 3), (5, 0, 5)]),
  ([0, 0, 2, 2, 0, 3, 0], 8, [(0, 1, 1), (1, 2, 1), (1, 3, 1), (3, 5, 2), (6, 4, 2), (5, 0, 1)]),
  ([0, 0, 2, 2, 1, 0, 2], 18, [(0, 0, 3), (0, 2, 1), (1, 2, 2), (0, 3, 1), (3, 0, 2), (4, 2, 2), (6, 3, 2), (5, 1, 5)]),
  ([0, 0, 2, 2, 1, 1, 1], 18, [(0, 0, 3), (0, 2, 1), (0, 3, 1), (1, 3, 2), (3, 0, 2), (4, 2, 2), (6, 2, 2), (5, 1, 5)]),
  ([0, 0, 2, 2, 1, 2, 0], 21, [(0, 0, 3), (1, 2, 3), (0, 3, 1), (3, 0, 1), (1, 4, 1), (3, 5, 3), (4, 2, 1), (6, 3, 2), (6, 4, 2), (5, 1, 4)]),
  ([0, 0, 2, 2, 2, 0, 1], 35, [(0, 0, 4), (0, 1, 4), (0, 3, 2), (1, 3, 3), (2, 4, 3), (3, 0, 3), (4, 1, 3), (6, 4, 3), (5, 2, 7), (5, 3, 2), (5, 4, 1)]),
  ([0, 0, 2, 2, 2, 1, 0], 35, [(0, 0, 4), (0, 1, 1), (0, 3, 1), (1, 3, 3), (0, 4, 4), (2, 4, 3), (3, 0, 3), (4, 1, 3), (6, 3, 3), (5, 1, 3), (5, 2, 7)]),
  ([0, 0, 2, 2, 3, 0, 0], 42, [(0, 0, 3), (0, 2, 3), (1, 2, 4), (2, 4, 3), (0, 5, 5), (2, 5, 1), (3, 0, 4), (4, 1, 4), (6, 1, 3), (6, 5, 1), (5, 3, 7), (5, 4, 4)]),
  ([0, 0, 2, 3, 0, 0, 2], 22, [(0, 0, 2), (0, 1, 1), (1, 2, 3), (0, 3, 2), (3, 0, 3), (4, 1, 1), (4, 2, 2), (4, 5, 2), (6, 3, 3), (5, 1, 3)]),
  ([0, 0, 2, 3, 0, 1, 1], 8, [(0, 0, 1), (1, 2, 1), (0, 3, 1), (3, 0, 1), (4, 3, 1), (6, 2, 1), (5, 1, 2)]),
  ([0, 0, 2, 3, 0, 2, 0], 8, [(0, 0, 1), (1, 2, 1), (0, 3, 1), (3, 0, 1), (4, 3, 1), (6, 2, 1), (5, 1, 2)]),
  ([0, 0, 2, 3, 1, 0, 1], 11, [(0, 0, 1), (1, 3, 2), (0, 4, 1), (3, 0, 1), (4, 2, 1), (4, 3, 1), (6, 1, 2), (5, 2, 2)]),
  ([0, 0, 2, 3, 1, 1, 0], 22, [(0, 0, 2), (0, 1, 2), (1, 3, 2), (0, 4, 1), (1, 4, 1), (3, 0, 3), (4, 3, 3), (6, 1, 3), (5, 2, 5)]),
  ([0, 0, 2, 3, 2, 0, 0], 42, [(0, 0, 3), (1, 2, 6), (0, 3, 4), (1, 5, 2), (2, 5, 4), (4, 1, 3), (4, 2, 5), (6, 4, 7), (6, 5, 1), (5, 3, 7)])
]
theorem chunk_007_checked : chunk_007.all checkCertificate = true := by
  decide

def chunk_008 : List Certificate := [
  ([0, 0, 2, 4, 0, 0, 1], 3, [(1, 4, 1), (4, 2, 1), (6, 3, 1)]),
  ([0, 0, 2, 4, 0, 1, 0], 3, [(1, 3, 1), (4, 4, 1), (6, 2, 1)]),
  ([0, 0, 2, 4, 1, 0, 0], 3, [(1, 2, 1), (4, 4, 1), (6, 3, 1)]),
  ([0, 0, 2, 5, 0, 0, 0], 6, [(1, 2, 1), (0, 3, 1), (3, 0, 1), (4, 4, 1), (6, 1, 1), (5, 5, 1)]),
  ([0, 0, 3, 0, 0, 0, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([0, 0, 3, 0, 0, 1, 3], 11, [(0, 0, 2), (3, 1, 3), (3, 3, 1), (0, 4, 1), (0, 5, 1), (5, 0, 2), (5, 1, 1)]),
  ([0, 0, 3, 0, 0, 2, 2], 11, [(0, 0, 2), (3, 0, 2), (3, 1, 1), (3, 3, 1), (0, 4, 1), (0, 5, 1), (5, 1, 3)]),
  ([0, 0, 3, 0, 0, 3, 1], 11, [(3, 0, 1), (3, 1, 1), (1, 3, 3), (3, 3, 1), (0, 4, 1), (3, 5, 1), (6, 4, 3)]),
  ([0, 0, 3, 0, 0, 4, 0], 3, [(1, 4, 1), (3, 5, 1), (6, 3, 1)]),
  ([0, 0, 3, 0, 1, 0, 3], 16, [(0, 0, 1), (0, 1, 1), (0, 2, 1), (3, 1, 5), (0, 3, 1), (0, 4, 1), (0, 5, 1), (5, 0, 5)]),
  ([0, 0, 3, 0, 1, 1, 2], 16, [(0, 0, 1), (0, 1, 1), (0, 2, 1), (3, 1, 5), (0, 3, 1), (0, 4, 1), (0, 5, 1), (5, 0, 5)]),
  ([0, 0, 3, 0, 1, 2, 1], 16, [(0, 0, 1), (0, 1, 1), (0, 2, 1), (3, 1, 5), (0, 3, 1), (0, 4, 1), (0, 5, 1), (5, 0, 5)]),
  ([0, 0, 3, 0, 1, 3, 0], 16, [(0, 0, 1), (0, 1, 1), (3, 1, 5), (0, 3, 1), (0, 4, 1), (0, 5, 1), (6, 2, 1), (5, 0, 5)]),
  ([0, 0, 3, 0, 2, 0, 2], 16, [(0, 0, 4), (0, 2, 1), (3, 0, 2), (3, 1, 2), (0, 4, 1), (3, 5, 1), (5, 1, 4), (5, 3, 1)]),
  ([0, 0, 3, 0, 2, 1, 1], 8, [(0, 0, 3), (3, 1, 2), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([0, 0, 3, 0, 2, 2, 0], 16, [(0, 0, 4), (3, 0, 2), (3, 1, 2), (0, 4, 1), (3, 5, 1), (6, 3, 1), (5, 1, 4), (5, 2, 1)]),
  ([0, 0, 3, 0, 3, 0, 1], 11, [(0, 0, 3), (0, 1, 1), (2, 3, 1), (3, 1, 2), (5, 2, 1), (5, 3, 1), (5, 4, 2)]),
  ([0, 0, 3, 0, 3, 1, 0], 11, [(0, 0, 4), (3, 1, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 0, 3, 0, 4, 0, 0], 3, [(2, 4, 1), (0, 5, 1), (5, 3, 1)]),
  ([0, 0, 3, 1, 0, 0, 3], 11, [(0, 0, 1), (0, 1, 1), (3, 1, 3), (4, 2, 1), (0, 4, 1), (0, 5, 1), (5, 0, 3)]),
  ([0, 0, 3, 1, 0, 1, 2], 8, [(0, 0, 1), (3, 1, 3), (0, 4, 1), (0, 5, 1), (5, 0, 2)]),
  ([0, 0, 3, 1, 0, 2, 1], 16, [(0, 0, 1), (0, 1, 1), (0, 2, 1), (3, 1, 5), (0, 3, 1), (0, 4, 1), (0, 5, 1), (5, 0, 5)]),
  ([0, 0, 3, 1, 0, 3, 0], 16, [(0, 0, 1), (0, 1, 1), (0, 2, 1), (3, 1, 5), (0, 3, 1), (0, 4, 1), (0, 5, 1), (5, 0, 5)]),
  ([0, 0, 3, 1, 1, 0, 2], 8, [(0, 0, 3), (3, 1, 1), (4, 2, 1), (3, 5, 1), (5, 1, 2)]),
  ([0, 0, 3, 1, 1, 1, 1], 16, [(0, 0, 4), (0, 2, 1), (3, 0, 2), (3, 1, 2), (0, 4, 1), (3, 5, 1), (5, 1, 4), (5, 3, 1)]),
  ([0, 0, 3, 1, 1, 2, 0], 16, [(0, 0, 4), (3, 0, 2), (3, 1, 2), (0, 4, 1), (3, 5, 1), (6, 3, 1), (5, 1, 4), (5, 2, 1)]),
  ([0, 0, 3, 1, 2, 0, 1], 11, [(0, 0, 4), (3, 1, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 0, 3, 1, 2, 1, 0], 11, [(0, 0, 4), (3, 1, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 0, 3, 1, 3, 0, 0], 42, [(0, 0, 13), (0, 1, 1), (1, 4, 1), (2, 4, 1), (3, 1, 10), (4, 1, 1), (6, 1, 1), (5, 2, 4), (5, 3, 4), (5, 4, 2), (5, 5, 4)]),
  ([0, 0, 3, 2, 0, 0, 2], 11, [(0, 0, 4), (3, 1, 2), (4, 2, 1), (3, 5, 1), (5, 1, 2), (5, 3, 1)]),
  ([0, 0, 3, 2, 0, 1, 1], 8, [(0, 0, 2), (3, 0, 1), (3, 1, 1), (4, 2, 1), (6, 3, 1), (5, 1, 2)]),
  ([0, 0, 3, 2, 0, 2, 0], 8, [(0, 0, 2), (3, 0, 1), (3, 1, 1), (4, 3, 1), (6, 2, 1), (5, 1, 2)])
]
theorem chunk_008_checked : chunk_008.all checkCertificate = true := by
  decide

def chunk_009 : List Certificate := [
  ([0, 0, 3, 2, 1, 0, 1], 22, [(0, 0, 5), (1, 3, 1), (1, 4, 2), (3, 1, 3), (4, 1, 2), (4, 3, 1), (6, 3, 3), (5, 2, 5)]),
  ([0, 0, 3, 2, 1, 1, 0], 22, [(0, 0, 5), (1, 3, 2), (1, 4, 1), (3, 1, 3), (4, 3, 3), (6, 1, 2), (6, 4, 1), (5, 2, 5)]),
  ([0, 0, 3, 2, 2, 0, 0], 14, [(0, 0, 3), (1, 4, 1), (1, 5, 1), (3, 1, 2), (4, 2, 2), (6, 1, 1), (6, 2, 1), (5, 3, 3)]),
  ([0, 0, 3, 3, 0, 0, 1], 20, [(0, 0, 4), (1, 3, 1), (1, 4, 2), (3, 1, 3), (4, 1, 1), (4, 4, 2), (6, 3, 3), (5, 2, 4)]),
  ([0, 0, 3, 3, 0, 1, 0], 20, [(0, 0, 4), (1, 3, 3), (3, 1, 3), (4, 4, 3), (6, 1, 1), (6, 3, 1), (6, 4, 1), (5, 2, 4)]),
  ([0, 0, 3, 3, 1, 0, 0], 26, [(0, 0, 5), (1, 4, 4), (3, 1, 4), (4, 2, 4), (6, 1, 1), (6, 2, 1), (6, 4, 1), (6, 5, 1), (5, 3, 5)]),
  ([0, 0, 3, 4, 0, 0, 0], 6, [(1, 3, 1), (0, 5, 1), (3, 1, 1), (4, 2, 1), (6, 4, 1), (5, 0, 1)]),
  ([0, 0, 4, 0, 0, 0, 3], 3, [(0, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([0, 0, 4, 0, 0, 1, 2], 3, [(0, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([0, 0, 4, 0, 0, 2, 1], 3, [(0, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([0, 0, 4, 0, 0, 3, 0], 3, [(0, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([0, 0, 4, 0, 1, 0, 2], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 0, 1, 1, 1], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 0, 1, 2, 0], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 0, 2, 0, 1], 3, [(0, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([0, 0, 4, 0, 2, 1, 0], 3, [(0, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([0, 0, 4, 0, 3, 0, 0], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 1, 0, 0, 2], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 1, 0, 1, 1], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 1, 0, 2, 0], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 1, 1, 0, 1], 3, [(0, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([0, 0, 4, 1, 1, 1, 0], 3, [(0, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([0, 0, 4, 1, 2, 0, 0], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 2, 0, 0, 1], 3, [(0, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([0, 0, 4, 2, 0, 1, 0], 3, [(0, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([0, 0, 4, 2, 1, 0, 0], 3, [(0, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 0, 4, 3, 0, 0, 0], 6, [(0, 3, 1), (1, 5, 1), (3, 1, 1), (4, 4, 1), (6, 2, 1), (5, 0, 1)]),
  ([0, 0, 5, 0, 0, 0, 2], 3, [(0, 0, 1), (3, 3, 1), (5, 1, 1)]),
  ([0, 0, 5, 0, 0, 1, 1], 3, [(0, 0, 1), (3, 3, 1), (5, 1, 1)]),
  ([0, 0, 5, 0, 0, 2, 0], 3, [(0, 0, 1), (3, 3, 1), (5, 1, 1)]),
  ([0, 0, 5, 0, 1, 0, 1], 3, [(0, 0, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 0, 5, 0, 1, 1, 0], 3, [(0, 0, 1), (3, 3, 1), (5, 2, 1)])
]
theorem chunk_009_checked : chunk_009.all checkCertificate = true := by
  decide

def chunk_010 : List Certificate := [
  ([0, 0, 5, 0, 2, 0, 0], 3, [(0, 0, 1), (3, 1, 1), (5, 3, 1)]),
  ([0, 0, 5, 1, 0, 0, 1], 3, [(0, 0, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 0, 5, 1, 0, 1, 0], 3, [(0, 0, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 0, 5, 1, 1, 0, 0], 3, [(0, 0, 1), (3, 1, 1), (5, 3, 1)]),
  ([0, 0, 5, 2, 0, 0, 0], 3, [(0, 3, 1), (3, 1, 1), (5, 0, 1)]),
  ([0, 0, 6, 0, 0, 0, 1], 3, [(0, 0, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 0, 6, 0, 0, 1, 0], 3, [(0, 0, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 0, 6, 0, 1, 0, 0], 3, [(0, 0, 1), (3, 3, 1), (5, 4, 1)]),
  ([0, 0, 6, 1, 0, 0, 0], 3, [(0, 0, 1), (3, 1, 1), (5, 3, 1)]),
  ([0, 0, 7, 0, 0, 0, 0], 3, [(0, 5, 1), (3, 0, 1), (5, 1, 1)]),
  ([0, 1, 0, 0, 0, 0, 6], 3, [(2, 1, 1), (4, 2, 1), (0, 3, 1)]),
  ([0, 1, 0, 0, 0, 1, 5], 3, [(4, 2, 1), (0, 3, 1), (2, 4, 1)]),
  ([0, 1, 0, 0, 0, 2, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([0, 1, 0, 0, 0, 3, 3], 20, [(0, 1, 4), (2, 2, 1), (1, 3, 1), (2, 3, 3), (3, 4, 1), (4, 4, 3), (1, 5, 2), (3, 5, 2), (6, 2, 3)]),
  ([0, 1, 0, 0, 0, 4, 2], 3, [(1, 2, 1), (3, 3, 1), (6, 1, 1)]),
  ([0, 1, 0, 0, 0, 5, 1], 3, [(1, 1, 1), (3, 3, 1), (6, 2, 1)]),
  ([0, 1, 0, 0, 0, 6, 0], 3, [(3, 1, 1), (1, 2, 1), (6, 5, 1)]),
  ([0, 1, 0, 0, 1, 0, 5], 3, [(2, 2, 1), (4, 3, 1), (0, 4, 1)]),
  ([0, 1, 0, 0, 1, 1, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 1, 0, 0, 1, 2, 3], 22, [(1, 2, 3), (3, 2, 1), (2, 3, 5), (3, 4, 2), (4, 4, 3), (0, 5, 5), (6, 1, 2), (6, 2, 1)]),
  ([0, 1, 0, 0, 1, 3, 2], 11, [(1, 1, 1), (1, 2, 1), (0, 3, 1), (2, 3, 1), (3, 3, 2), (3, 4, 1), (1, 5, 1), (6, 2, 3)]),
  ([0, 1, 0, 0, 1, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 1, 0, 0, 1, 5, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 2, 1)]),
  ([0, 1, 0, 0, 2, 0, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([0, 1, 0, 0, 2, 1, 3], 11, [(0, 1, 1), (0, 2, 1), (2, 3, 1), (0, 4, 1), (2, 4, 3), (0, 5, 1), (4, 5, 3)]),
  ([0, 1, 0, 0, 2, 2, 2], 35, [(0, 1, 3), (2, 1, 1), (1, 2, 3), (2, 2, 4), (2, 3, 4), (0, 4, 7), (2, 5, 1), (3, 5, 3), (4, 5, 3), (6, 3, 3), (5, 1, 3)]),
  ([0, 1, 0, 0, 2, 3, 1], 11, [(0, 1, 1), (1, 2, 2), (2, 3, 1), (3, 3, 2), (2, 4, 1), (0, 5, 1), (6, 4, 2), (5, 1, 1)]),
  ([0, 1, 0, 0, 2, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 1, 0, 0, 3, 0, 3], 11, [(0, 1, 3), (2, 2, 1), (0, 3, 1), (2, 4, 1), (4, 4, 1), (2, 5, 2), (5, 2, 2)]),
  ([0, 1, 0, 0, 3, 1, 2], 11, [(0, 1, 3), (2, 2, 2), (2, 3, 1), (2, 4, 1), (0, 5, 1), (5, 1, 1), (5, 2, 2)]),
  ([0, 1, 0, 0, 3, 2, 1], 11, [(0, 1, 4), (2, 2, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 2, 3)]),
  ([0, 1, 0, 0, 3, 3, 0], 20, [(0, 1, 3), (2, 2, 1), (2, 3, 2), (0, 4, 1), (1, 4, 3), (2, 5, 1), (3, 5, 3), (6, 1, 1), (6, 3, 2), (5, 2, 3)])
]
theorem chunk_010_checked : chunk_010.all checkCertificate = true := by
  decide

def chunk_011 : List Certificate := [
  ([0, 1, 0, 0, 4, 0, 2], 3, [(0, 2, 1), (2, 3, 1), (5, 1, 1)]),
  ([0, 1, 0, 0, 4, 1, 1], 3, [(0, 2, 1), (2, 3, 1), (5, 1, 1)]),
  ([0, 1, 0, 0, 4, 2, 0], 3, [(0, 2, 1), (2, 3, 1), (5, 1, 1)]),
  ([0, 1, 0, 0, 5, 0, 1], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([0, 1, 0, 0, 5, 1, 0], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([0, 1, 0, 0, 6, 0, 0], 3, [(0, 1, 1), (2, 3, 1), (5, 4, 1)]),
  ([0, 1, 0, 1, 0, 0, 5], 3, [(2, 2, 1), (0, 3, 1), (4, 4, 1)]),
  ([0, 1, 0, 1, 0, 1, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 1, 0, 1, 0, 2, 3], 8, [(0, 2, 1), (1, 3, 1), (3, 3, 1), (0, 4, 1), (4, 4, 1), (2, 5, 1), (3, 5, 1), (6, 2, 1)]),
  ([0, 1, 0, 1, 0, 3, 2], 8, [(2, 2, 1), (1, 3, 1), (3, 3, 2), (1, 4, 1), (0, 5, 1), (6, 2, 2)]),
  ([0, 1, 0, 1, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 1, 0, 1, 0, 5, 0], 3, [(1, 2, 1), (3, 5, 1), (6, 4, 1)]),
  ([0, 1, 0, 1, 1, 0, 4], 3, [(0, 3, 1), (4, 4, 1), (2, 5, 1)]),
  ([0, 1, 0, 1, 1, 1, 3], 8, [(2, 2, 1), (0, 3, 1), (0, 4, 1), (4, 4, 2), (0, 5, 1), (2, 5, 2)]),
  ([0, 1, 0, 1, 1, 2, 2], 18, [(2, 2, 3), (0, 3, 1), (2, 3, 2), (0, 4, 3), (1, 4, 2), (0, 5, 1), (3, 5, 2), (4, 5, 2), (6, 3, 2)]),
  ([0, 1, 0, 1, 1, 3, 1], 16, [(0, 1, 1), (1, 2, 1), (2, 2, 1), (1, 3, 3), (3, 3, 3), (1, 4, 1), (3, 5, 1), (6, 4, 5)]),
  ([0, 1, 0, 1, 1, 4, 0], 3, [(1, 3, 1), (3, 4, 1), (6, 5, 1)]),
  ([0, 1, 0, 1, 2, 0, 3], 8, [(2, 2, 1), (2, 3, 1), (0, 4, 1), (4, 4, 2), (0, 5, 2), (2, 5, 1)]),
  ([0, 1, 0, 1, 2, 1, 2], 28, [(2, 2, 5), (0, 3, 5), (0, 4, 1), (1, 4, 2), (2, 4, 4), (0, 5, 3), (3, 5, 2), (4, 5, 2), (6, 3, 2), (5, 2, 2)]),
  ([0, 1, 0, 1, 2, 2, 1], 18, [(0, 1, 2), (2, 2, 3), (1, 3, 1), (0, 4, 1), (1, 4, 3), (3, 4, 1), (3, 5, 1), (6, 3, 4), (5, 2, 2)]),
  ([0, 1, 0, 1, 2, 3, 0], 22, [(0, 1, 2), (2, 2, 2), (0, 3, 1), (1, 3, 3), (2, 3, 1), (1, 4, 2), (3, 4, 3), (6, 5, 5), (5, 2, 3)]),
  ([0, 1, 0, 1, 3, 0, 2], 8, [(0, 2, 3), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 3, 2)]),
  ([0, 1, 0, 1, 3, 1, 1], 8, [(0, 2, 2), (1, 3, 1), (2, 3, 2), (6, 4, 1), (5, 1, 1), (5, 2, 1)]),
  ([0, 1, 0, 1, 3, 2, 0], 11, [(0, 2, 3), (1, 3, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (6, 2, 1), (5, 1, 1), (5, 3, 2)]),
  ([0, 1, 0, 1, 4, 0, 1], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([0, 1, 0, 1, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([0, 1, 0, 1, 5, 0, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 4, 1)]),
  ([0, 1, 0, 2, 0, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 1, 0, 2, 0, 1, 3], 21, [(0, 1, 1), (0, 2, 1), (4, 0, 1), (2, 3, 1), (0, 4, 5), (2, 4, 3), (2, 5, 3), (4, 5, 5), (4, 6, 1)]),
  ([0, 1, 0, 2, 0, 2, 2], 5, [(0, 1, 1), (1, 2, 1), (2, 4, 1), (4, 5, 1), (6, 3, 1)]),
  ([0, 1, 0, 2, 0, 3, 1], 8, [(1, 2, 1), (1, 3, 2), (3, 3, 1), (3, 4, 1), (6, 1, 1), (6, 4, 2)]),
  ([0, 1, 0, 2, 0, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)])
]
theorem chunk_011_checked : chunk_011.all checkCertificate = true := by
  decide

def chunk_012 : List Certificate := [
  ([0, 1, 0, 2, 1, 0, 3], 21, [(0, 2, 1), (4, 0, 1), (4, 1, 1), (0, 3, 1), (0, 4, 5), (4, 4, 3), (2, 5, 7), (4, 5, 1), (4, 6, 1)]),
  ([0, 1, 0, 2, 1, 1, 2], 5, [(0, 2, 1), (4, 1, 1), (1, 4, 1), (2, 5, 1), (6, 3, 1)]),
  ([0, 1, 0, 2, 1, 2, 1], 28, [(1, 1, 5), (0, 2, 2), (2, 3, 1), (1, 4, 4), (2, 4, 1), (3, 4, 2), (4, 1, 2), (6, 2, 3), (6, 3, 6), (5, 2, 2)]),
  ([0, 1, 0, 2, 1, 3, 0], 11, [(3, 4, 3), (1, 5, 4), (6, 1, 1), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 1, 0, 2, 2, 0, 2], 5, [(0, 2, 1), (1, 3, 1), (2, 4, 1), (4, 5, 1), (6, 1, 1)]),
  ([0, 1, 0, 2, 2, 1, 1], 18, [(1, 1, 1), (0, 2, 2), (1, 2, 1), (1, 3, 3), (2, 3, 2), (4, 1, 2), (6, 2, 2), (6, 4, 3), (5, 1, 2)]),
  ([0, 1, 0, 2, 2, 2, 0], 35, [(0, 2, 3), (1, 2, 4), (2, 3, 3), (1, 4, 6), (3, 5, 3), (4, 1, 3), (6, 1, 1), (6, 3, 4), (6, 4, 1), (6, 5, 4), (5, 1, 3)]),
  ([0, 1, 0, 2, 3, 0, 1], 8, [(0, 1, 1), (1, 3, 1), (2, 3, 1), (0, 4, 1), (4, 1, 1), (6, 4, 1), (5, 2, 2)]),
  ([0, 1, 0, 2, 3, 1, 0], 11, [(0, 1, 1), (2, 3, 1), (0, 4, 1), (1, 4, 2), (2, 5, 1), (4, 1, 1), (6, 3, 2), (5, 2, 2)]),
  ([0, 1, 0, 2, 4, 0, 0], 3, [(2, 3, 1), (0, 5, 1), (5, 4, 1)]),
  ([0, 1, 0, 3, 0, 0, 3], 16, [(0, 2, 2), (4, 1, 2), (4, 2, 2), (1, 4, 3), (2, 5, 2), (4, 5, 1), (4, 6, 1), (6, 0, 1), (6, 1, 2)]),
  ([0, 1, 0, 3, 0, 1, 2], 21, [(1, 1, 2), (1, 2, 2), (1, 3, 1), (4, 1, 6), (1, 4, 1), (1, 5, 1), (4, 6, 1), (6, 0, 1), (6, 2, 6)]),
  ([0, 1, 0, 3, 0, 2, 1], 8, [(1, 1, 2), (1, 4, 1), (4, 2, 2), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 1, 0, 3, 0, 3, 0], 11, [(1, 1, 1), (1, 4, 3), (3, 4, 1), (3, 5, 2), (6, 2, 1), (6, 3, 1), (6, 5, 2)]),
  ([0, 1, 0, 3, 1, 0, 2], 21, [(1, 1, 3), (1, 2, 1), (1, 3, 1), (4, 0, 1), (4, 1, 5), (1, 4, 1), (1, 5, 1), (4, 6, 1), (6, 2, 7)]),
  ([0, 1, 0, 3, 1, 1, 1], 8, [(1, 2, 1), (1, 3, 1), (1, 4, 1), (4, 2, 2), (6, 1, 3)]),
  ([0, 1, 0, 3, 1, 2, 0], 11, [(1, 1, 1), (1, 2, 1), (1, 3, 1), (1, 5, 1), (4, 1, 3), (6, 2, 3), (6, 4, 1)]),
  ([0, 1, 0, 3, 2, 0, 1], 24, [(0, 1, 5), (1, 3, 1), (1, 4, 3), (2, 4, 2), (4, 1, 2), (4, 2, 2), (6, 3, 4), (5, 2, 5)]),
  ([0, 1, 0, 3, 2, 1, 0], 22, [(0, 1, 3), (1, 3, 1), (1, 4, 2), (2, 4, 3), (1, 5, 2), (4, 1, 2), (4, 2, 1), (6, 2, 1), (6, 3, 4), (5, 2, 3)]),
  ([0, 1, 0, 3, 3, 0, 0], 20, [(0, 1, 1), (0, 2, 1), (0, 3, 2), (1, 3, 2), (1, 5, 1), (2, 5, 3), (4, 1, 3), (6, 2, 3), (5, 4, 4)]),
  ([0, 1, 0, 4, 0, 0, 2], 3, [(1, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([0, 1, 0, 4, 0, 1, 1], 3, [(1, 2, 1), (4, 1, 1), (6, 3, 1)]),
  ([0, 1, 0, 4, 0, 2, 0], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 1, 0, 4, 1, 0, 1], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 1, 0, 4, 1, 1, 0], 3, [(1, 1, 1), (4, 2, 1), (6, 3, 1)]),
  ([0, 1, 0, 4, 2, 0, 0], 3, [(1, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([0, 1, 0, 5, 0, 0, 1], 3, [(1, 4, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 1, 0, 5, 0, 1, 0], 3, [(1, 4, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 1, 0, 5, 1, 0, 0], 3, [(1, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 1, 0, 6, 0, 0, 0], 3, [(1, 5, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 1, 1, 0, 0, 0, 5], 3, [(2, 2, 1), (0, 3, 1), (4, 4, 1)]),
  ([0, 1, 1, 0, 0, 1, 4], 3, [(0, 3, 1), (4, 4, 1), (2, 5, 1)])
]
theorem chunk_012_checked : chunk_012.all checkCertificate = true := by
  decide

def chunk_013 : List Certificate := [
  ([0, 1, 1, 0, 0, 2, 3], 8, [(2, 2, 1), (0, 3, 1), (1, 3, 1), (0, 4, 1), (4, 4, 1), (2, 5, 1), (3, 5, 1), (6, 2, 1)]),
  ([0, 1, 1, 0, 0, 3, 2], 16, [(3, 0, 1), (3, 2, 1), (1, 3, 3), (3, 3, 3), (1, 4, 1), (1, 5, 1), (3, 6, 1), (6, 2, 5)]),
  ([0, 1, 1, 0, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([0, 1, 1, 0, 0, 5, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 2, 1)]),
  ([0, 1, 1, 0, 1, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 1, 1, 0, 1, 1, 3], 8, [(2, 2, 1), (0, 3, 1), (2, 4, 1), (4, 4, 2), (0, 5, 2), (2, 5, 1)]),
  ([0, 1, 1, 0, 1, 2, 2], 18, [(2, 2, 3), (0, 3, 3), (0, 4, 2), (1, 4, 2), (2, 4, 1), (2, 5, 1), (3, 5, 2), (4, 5, 2), (6, 3, 2)]),
  ([0, 1, 1, 0, 1, 3, 1], 8, [(2, 2, 1), (1, 3, 1), (3, 3, 2), (1, 4, 1), (0, 5, 1), (6, 4, 2)]),
  ([0, 1, 1, 0, 1, 4, 0], 3, [(1, 3, 1), (3, 4, 1), (6, 5, 1)]),
  ([0, 1, 1, 0, 2, 0, 3], 8, [(2, 2, 1), (2, 3, 1), (0, 4, 3), (2, 5, 1), (4, 5, 2)]),
  ([0, 1, 1, 0, 2, 1, 2], 28, [(0, 2, 2), (2, 2, 1), (2, 3, 7), (0, 4, 7), (1, 5, 2), (2, 5, 1), (3, 5, 2), (4, 5, 2), (6, 2, 2), (5, 2, 2)]),
  ([0, 1, 1, 0, 2, 2, 1], 18, [(1, 2, 1), (2, 2, 2), (2, 3, 3), (0, 4, 3), (3, 4, 2), (0, 5, 2), (1, 5, 1), (6, 3, 2), (5, 2, 2)]),
  ([0, 1, 1, 0, 2, 3, 0], 32, [(0, 1, 2), (0, 3, 2), (2, 3, 5), (1, 4, 5), (0, 5, 1), (3, 5, 5), (6, 2, 4), (6, 4, 2), (6, 5, 1), (5, 0, 2), (5, 2, 3)]),
  ([0, 1, 1, 0, 3, 0, 2], 8, [(0, 2, 3), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 3, 2)]),
  ([0, 1, 1, 0, 3, 1, 1], 8, [(0, 2, 3), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 3, 2)]),
  ([0, 1, 1, 0, 3, 2, 0], 16, [(0, 2, 5), (2, 3, 3), (2, 4, 1), (2, 5, 1), (6, 0, 1), (5, 1, 1), (5, 2, 1), (5, 3, 3)]),
  ([0, 1, 1, 0, 4, 0, 1], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([0, 1, 1, 0, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([0, 1, 1, 0, 5, 0, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 4, 1)]),
  ([0, 1, 1, 1, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 1, 1, 1, 0, 1, 3], 21, [(0, 1, 1), (0, 2, 1), (4, 0, 1), (0, 3, 1), (2, 4, 3), (4, 4, 5), (0, 5, 4), (2, 5, 4), (4, 6, 1)]),
  ([0, 1, 1, 1, 0, 2, 2], 42, [(0, 1, 3), (3, 0, 3), (1, 2, 3), (1, 3, 3), (0, 4, 4), (1, 4, 1), (2, 4, 4), (3, 4, 1), (3, 5, 3), (4, 5, 7), (2, 6, 3), (6, 3, 7)]),
  ([0, 1, 1, 1, 0, 3, 1], 21, [(3, 0, 1), (1, 3, 7), (3, 3, 1), (3, 4, 3), (3, 5, 1), (3, 6, 1), (6, 1, 1), (6, 2, 1), (6, 4, 5)]),
  ([0, 1, 1, 1, 0, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 1, 1, 1, 1, 0, 3], 21, [(0, 2, 1), (4, 0, 1), (4, 1, 1), (0, 3, 1), (0, 4, 5), (2, 4, 3), (2, 5, 4), (4, 5, 4), (4, 6, 1)]),
  ([0, 1, 1, 1, 1, 1, 2], 42, [(0, 1, 7), (1, 3, 2), (2, 3, 5), (4, 0, 3), (0, 4, 1), (2, 4, 4), (3, 4, 2), (0, 5, 1), (4, 5, 6), (6, 0, 2), (6, 2, 7), (5, 0, 2)]),
  ([0, 1, 1, 1, 1, 2, 1], 7, [(0, 1, 1), (1, 2, 1), (2, 4, 1), (3, 4, 1), (6, 3, 2), (5, 0, 1)]),
  ([0, 1, 1, 1, 1, 3, 0], 16, [(3, 0, 1), (3, 4, 4), (1, 5, 5), (6, 1, 1), (6, 2, 1), (6, 3, 1), (6, 4, 2), (6, 5, 1)]),
  ([0, 1, 1, 1, 2, 0, 2], 21, [(0, 2, 6), (0, 3, 1), (1, 3, 1), (2, 3, 2), (4, 0, 1), (3, 5, 1), (4, 6, 1), (6, 3, 1), (5, 1, 6), (5, 3, 1)]),
  ([0, 1, 1, 1, 2, 1, 1], 7, [(0, 2, 2), (2, 3, 1), (4, 0, 1), (6, 3, 1), (5, 1, 2)]),
  ([0, 1, 1, 1, 2, 2, 0], 18, [(0, 2, 1), (0, 4, 1), (1, 4, 2), (2, 4, 2), (1, 5, 3), (3, 5, 2), (6, 3, 5), (5, 2, 2)]),
  ([0, 1, 1, 1, 3, 0, 1], 8, [(0, 1, 1), (2, 3, 2), (0, 4, 2), (5, 2, 1), (5, 3, 1), (5, 4, 1)])
]
theorem chunk_013_checked : chunk_013.all checkCertificate = true := by
  decide

def chunk_014 : List Certificate := [
  ([0, 1, 1, 1, 3, 1, 0], 8, [(0, 1, 1), (2, 3, 2), (0, 4, 2), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 1, 1, 1, 4, 0, 0], 3, [(2, 3, 1), (0, 5, 1), (5, 4, 1)]),
  ([0, 1, 1, 2, 0, 0, 3], 16, [(4, 0, 1), (4, 1, 1), (4, 2, 1), (0, 4, 5), (2, 4, 1), (2, 5, 4), (4, 5, 2), (4, 6, 1)]),
  ([0, 1, 1, 2, 0, 1, 2], 14, [(0, 1, 2), (0, 2, 1), (1, 3, 1), (4, 2, 1), (3, 4, 1), (2, 5, 3), (4, 5, 1), (4, 6, 2), (6, 0, 1), (5, 0, 1)]),
  ([0, 1, 1, 2, 0, 2, 1], 70, [(0, 1, 9), (1, 2, 9), (2, 4, 4), (3, 4, 4), (4, 0, 6), (4, 1, 3), (2, 5, 5), (3, 6, 5), (6, 3, 12), (6, 4, 4), (5, 0, 6), (5, 2, 3)]),
  ([0, 1, 1, 2, 0, 3, 0], 8, [(1, 3, 1), (1, 4, 1), (1, 5, 1), (3, 5, 2), (6, 2, 1), (6, 4, 2)]),
  ([0, 1, 1, 2, 1, 0, 2], 21, [(0, 2, 5), (0, 3, 1), (1, 3, 2), (4, 0, 1), (2, 4, 2), (3, 5, 2), (4, 6, 1), (6, 3, 2), (5, 1, 5)]),
  ([0, 1, 1, 2, 1, 1, 1], 28, [(0, 2, 8), (1, 3, 3), (3, 0, 1), (4, 1, 2), (4, 2, 1), (3, 5, 1), (3, 6, 1), (6, 3, 2), (6, 4, 1), (5, 1, 7), (5, 3, 1)]),
  ([0, 1, 1, 2, 1, 2, 0], 28, [(0, 2, 2), (1, 4, 5), (2, 4, 2), (1, 5, 4), (3, 5, 2), (4, 2, 2), (6, 2, 3), (6, 3, 5), (6, 5, 1), (5, 3, 2)]),
  ([0, 1, 1, 2, 2, 0, 1], 18, [(0, 1, 1), (0, 3, 1), (1, 3, 2), (0, 4, 3), (2, 4, 2), (4, 1, 2), (6, 3, 2), (5, 2, 5)]),
  ([0, 1, 1, 2, 2, 1, 0], 18, [(0, 1, 1), (0, 3, 3), (1, 3, 2), (0, 4, 1), (2, 4, 2), (4, 1, 2), (6, 4, 2), (5, 2, 5)]),
  ([0, 1, 1, 2, 3, 0, 0], 11, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 5, 1), (2, 5, 3), (5, 4, 4)]),
  ([0, 1, 1, 3, 0, 0, 2], 8, [(0, 2, 1), (1, 2, 2), (4, 3, 2), (4, 5, 1), (6, 1, 1), (6, 3, 1)]),
  ([0, 1, 1, 3, 0, 1, 1], 8, [(1, 2, 1), (1, 3, 1), (4, 1, 1), (4, 3, 2), (6, 0, 1), (6, 2, 2)]),
  ([0, 1, 1, 3, 0, 2, 0], 8, [(1, 3, 2), (4, 2, 3), (6, 0, 1), (6, 1, 1), (6, 3, 1)]),
  ([0, 1, 1, 3, 1, 0, 1], 8, [(0, 1, 1), (1, 3, 2), (4, 2, 1), (4, 3, 1), (6, 2, 1), (6, 4, 1), (5, 2, 1)]),
  ([0, 1, 1, 3, 1, 1, 0], 8, [(0, 1, 1), (1, 2, 2), (4, 3, 2), (6, 3, 1), (6, 4, 1), (5, 2, 1)]),
  ([0, 1, 1, 3, 2, 0, 0], 22, [(0, 1, 2), (0, 2, 2), (1, 2, 3), (0, 5, 1), (2, 5, 3), (4, 3, 3), (6, 3, 2), (6, 5, 1), (5, 4, 5)]),
  ([0, 1, 1, 4, 0, 0, 1], 3, [(1, 3, 1), (4, 4, 1), (6, 2, 1)]),
  ([0, 1, 1, 4, 0, 1, 0], 3, [(1, 2, 1), (4, 3, 1), (6, 4, 1)]),
  ([0, 1, 1, 4, 1, 0, 0], 3, [(1, 2, 1), (4, 4, 1), (6, 3, 1)]),
  ([0, 1, 1, 5, 0, 0, 0], 3, [(1, 2, 1), (4, 4, 1), (6, 3, 1)]),
  ([0, 1, 2, 0, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 1, 2, 0, 0, 1, 3], 8, [(0, 1, 1), (2, 3, 1), (0, 4, 2), (2, 4, 1), (3, 5, 1), (4, 5, 2)]),
  ([0, 1, 2, 0, 0, 2, 2], 18, [(0, 1, 3), (0, 3, 2), (3, 3, 1), (1, 4, 2), (2, 4, 2), (3, 4, 1), (3, 5, 3), (4, 5, 2), (6, 3, 2)]),
  ([0, 1, 2, 0, 0, 3, 1], 16, [(3, 0, 1), (3, 1, 1), (1, 3, 5), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 5)]),
  ([0, 1, 2, 0, 0, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([0, 1, 2, 0, 1, 0, 3], 21, [(0, 2, 1), (4, 0, 1), (4, 1, 1), (0, 3, 1), (2, 4, 3), (4, 4, 5), (0, 5, 5), (2, 5, 3), (2, 6, 1)]),
  ([0, 1, 2, 0, 1, 1, 2], 28, [(0, 1, 4), (0, 2, 2), (3, 1, 4), (2, 4, 3), (4, 5, 3), (2, 6, 1), (3, 6, 2), (6, 3, 3), (5, 0, 6)]),
  ([0, 1, 2, 0, 1, 2, 1], 14, [(0, 1, 1), (0, 2, 1), (3, 1, 5), (0, 3, 1), (6, 4, 3), (5, 0, 3)]),
  ([0, 1, 2, 0, 1, 3, 0], 8, [(3, 1, 1), (3, 4, 2), (1, 5, 2), (6, 0, 1), (6, 4, 1), (6, 5, 1)]),
  ([0, 1, 2, 0, 2, 0, 2], 21, [(0, 2, 2), (0, 3, 1), (2, 3, 1), (3, 0, 4), (0, 4, 2), (3, 5, 1), (4, 5, 1), (2, 6, 1), (4, 6, 1), (6, 1, 2), (5, 1, 5)])
]
theorem chunk_014_checked : chunk_014.all checkCertificate = true := by
  decide

def chunk_015 : List Certificate := [
  ([0, 1, 2, 0, 2, 1, 1], 28, [(0, 1, 2), (0, 2, 2), (0, 3, 2), (2, 3, 1), (3, 0, 3), (0, 4, 3), (3, 5, 3), (3, 6, 3), (5, 1, 9)]),
  ([0, 1, 2, 0, 2, 2, 0], 33, [(2, 3, 3), (3, 0, 1), (0, 4, 3), (1, 4, 5), (0, 5, 2), (2, 5, 2), (3, 5, 4), (6, 2, 3), (6, 3, 5), (5, 0, 2), (5, 1, 3)]),
  ([0, 1, 2, 0, 3, 0, 1], 8, [(0, 1, 1), (2, 3, 2), (0, 4, 2), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 1, 2, 0, 3, 1, 0], 8, [(0, 1, 1), (2, 3, 2), (0, 4, 2), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([0, 1, 2, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 5, 1), (5, 4, 1)]),
  ([0, 1, 2, 1, 0, 0, 3], 8, [(4, 1, 1), (4, 2, 1), (2, 4, 2), (4, 4, 1), (0, 5, 3)]),
  ([0, 1, 2, 1, 0, 1, 2], 14, [(0, 1, 1), (3, 1, 2), (4, 1, 1), (2, 4, 1), (3, 4, 1), (0, 5, 2), (3, 6, 2), (6, 1, 1), (5, 0, 3)]),
  ([0, 1, 2, 1, 0, 2, 1], 42, [(0, 1, 6), (3, 1, 9), (0, 3, 1), (2, 4, 3), (3, 4, 1), (0, 5, 4), (3, 6, 1), (4, 6, 3), (6, 3, 3), (5, 0, 7), (5, 2, 4)]),
  ([0, 1, 2, 1, 0, 3, 0], 8, [(3, 0, 1), (3, 1, 1), (1, 5, 2), (3, 5, 1), (6, 4, 3)]),
  ([0, 1, 2, 1, 1, 0, 2], 21, [(0, 1, 1), (0, 2, 2), (0, 3, 1), (3, 0, 4), (4, 2, 2), (0, 4, 1), (3, 5, 1), (4, 6, 1), (6, 1, 3), (5, 1, 5)]),
  ([0, 1, 2, 1, 1, 1, 1], 21, [(0, 1, 2), (0, 2, 1), (0, 3, 2), (3, 0, 4), (4, 2, 1), (2, 5, 2), (3, 6, 1), (4, 6, 1), (6, 4, 2), (5, 1, 5)]),
  ([0, 1, 2, 1, 1, 2, 0], 5, [(3, 1, 1), (0, 4, 1), (1, 5, 1), (6, 3, 1), (5, 2, 1)]),
  ([0, 1, 2, 1, 2, 0, 1], 28, [(0, 1, 5), (0, 3, 3), (0, 4, 1), (1, 4, 2), (2, 4, 2), (3, 1, 2), (4, 2, 2), (6, 4, 2), (5, 2, 5), (5, 3, 4)]),
  ([0, 1, 2, 1, 2, 1, 0], 28, [(0, 1, 3), (0, 3, 3), (1, 3, 2), (0, 4, 3), (2, 4, 2), (3, 1, 2), (4, 1, 2), (6, 3, 2), (5, 2, 7), (5, 4, 2)]),
  ([0, 1, 2, 1, 3, 0, 0], 11, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 5, 1), (2, 5, 3), (5, 4, 4)]),
  ([0, 1, 2, 2, 0, 0, 2], 18, [(0, 3, 3), (1, 3, 1), (3, 0, 2), (4, 2, 5), (1, 5, 1), (6, 1, 3), (6, 3, 1), (5, 1, 2)]),
  ([0, 1, 2, 2, 0, 1, 1], 18, [(0, 3, 2), (1, 3, 2), (3, 0, 2), (4, 2, 4), (4, 3, 1), (6, 0, 1), (6, 1, 3), (6, 2, 1), (5, 1, 2)]),
  ([0, 1, 2, 2, 0, 2, 0], 18, [(0, 1, 2), (1, 3, 2), (3, 0, 2), (4, 1, 1), (4, 2, 1), (4, 3, 3), (6, 0, 1), (6, 2, 4), (5, 1, 2)]),
  ([0, 1, 2, 2, 1, 0, 1], 18, [(0, 1, 3), (1, 3, 2), (0, 4, 2), (3, 1, 2), (4, 3, 2), (6, 3, 1), (6, 4, 1), (5, 2, 5)]),
  ([0, 1, 2, 2, 1, 1, 0], 54, [(0, 1, 11), (0, 2, 2), (1, 3, 6), (3, 0, 2), (3, 1, 4), (4, 3, 8), (6, 3, 1), (6, 4, 7), (5, 2, 13)]),
  ([0, 1, 2, 2, 2, 0, 0], 35, [(0, 1, 4), (0, 2, 5), (1, 3, 3), (0, 5, 1), (2, 5, 3), (3, 1, 3), (4, 2, 2), (4, 3, 1), (6, 5, 3), (5, 3, 3), (5, 4, 7)]),
  ([0, 1, 2, 3, 0, 0, 1], 22, [(0, 1, 3), (1, 3, 3), (3, 0, 1), (3, 1, 2), (4, 0, 1), (4, 4, 4), (6, 2, 2), (6, 3, 2), (6, 4, 1), (5, 2, 3)]),
  ([0, 1, 2, 3, 0, 1, 0], 22, [(0, 1, 3), (1, 3, 3), (3, 0, 1), (3, 1, 2), (4, 0, 1), (4, 4, 4), (6, 2, 2), (6, 3, 2), (6, 4, 1), (5, 2, 3)]),
  ([0, 1, 2, 3, 1, 0, 0], 22, [(0, 1, 2), (0, 3, 3), (1, 3, 2), (1, 5, 1), (3, 1, 3), (4, 2, 3), (6, 2, 2), (6, 5, 1), (5, 4, 5)]),
  ([0, 1, 2, 4, 0, 0, 0], 3, [(1, 4, 1), (4, 5, 1), (6, 3, 1)]),
  ([0, 1, 3, 0, 0, 0, 3], 8, [(0, 1, 1), (3, 2, 2), (0, 4, 1), (2, 5, 1), (4, 6, 1), (5, 0, 1), (5, 1, 1)]),
  ([0, 1, 3, 0, 0, 1, 2], 16, [(0, 1, 3), (3, 2, 5), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 3), (5, 2, 1)]),
  ([0, 1, 3, 0, 0, 2, 1], 8, [(0, 1, 1), (3, 2, 3), (0, 4, 1), (6, 1, 1), (5, 0, 1), (5, 1, 1)]),
  ([0, 1, 3, 0, 0, 3, 0], 11, [(0, 1, 2), (3, 2, 4), (0, 4, 1), (6, 5, 1), (5, 0, 1), (5, 1, 2)]),
  ([0, 1, 3, 0, 1, 0, 2], 21, [(0, 1, 1), (0, 2, 3), (0, 3, 1), (3, 0, 1), (3, 2, 5), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 1, 7)]),
  ([0, 1, 3, 0, 1, 1, 1], 21, [(0, 1, 2), (0, 2, 2), (0, 3, 1), (3, 2, 6), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 6)]),
  ([0, 1, 3, 0, 1, 2, 0], 8, [(0, 1, 1), (3, 2, 3), (0, 5, 1), (6, 0, 1), (5, 1, 2)])
]
theorem chunk_015_checked : chunk_015.all checkCertificate = true := by
  decide

def chunk_016 : List Certificate := [
  ([0, 1, 3, 0, 2, 0, 1], 8, [(0, 1, 1), (0, 3, 1), (0, 4, 1), (3, 1, 2), (5, 2, 3)]),
  ([0, 1, 3, 0, 2, 1, 0], 16, [(0, 1, 3), (0, 4, 1), (3, 0, 1), (3, 1, 3), (3, 2, 1), (0, 5, 1), (6, 3, 1), (5, 2, 5)]),
  ([0, 1, 3, 0, 3, 0, 0], 11, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 5, 1), (2, 5, 3), (5, 4, 4)]),
  ([0, 1, 3, 1, 0, 0, 2], 24, [(0, 1, 2), (0, 2, 2), (0, 3, 2), (3, 2, 7), (4, 0, 1), (0, 5, 2), (4, 6, 1), (5, 1, 7)]),
  ([0, 1, 3, 1, 0, 1, 1], 8, [(0, 2, 1), (0, 3, 1), (3, 2, 2), (4, 1, 1), (6, 0, 1), (5, 1, 2)]),
  ([0, 1, 3, 1, 0, 2, 0], 8, [(0, 1, 1), (3, 2, 3), (0, 5, 1), (6, 0, 1), (5, 1, 2)]),
  ([0, 1, 3, 1, 1, 0, 1], 24, [(0, 1, 7), (3, 0, 2), (3, 1, 2), (3, 2, 2), (4, 3, 2), (6, 3, 1), (6, 4, 1), (5, 2, 7)]),
  ([0, 1, 3, 1, 1, 1, 0], 24, [(0, 1, 7), (3, 0, 2), (3, 1, 2), (3, 2, 2), (4, 3, 2), (6, 3, 1), (6, 4, 1), (5, 2, 7)]),
  ([0, 1, 3, 1, 2, 0, 0], 11, [(0, 1, 3), (0, 2, 1), (3, 2, 3), (5, 1, 1), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([0, 1, 3, 2, 0, 0, 1], 11, [(0, 1, 3), (3, 0, 1), (3, 1, 1), (3, 2, 1), (4, 4, 1), (6, 3, 1), (5, 2, 3)]),
  ([0, 1, 3, 2, 0, 1, 0], 11, [(0, 1, 3), (3, 0, 1), (3, 1, 1), (3, 2, 1), (4, 4, 1), (6, 3, 1), (5, 2, 3)]),
  ([0, 1, 3, 2, 1, 0, 0], 11, [(0, 1, 3), (1, 5, 1), (3, 2, 2), (4, 3, 1), (6, 2, 1), (5, 3, 1), (5, 4, 2)]),
  ([0, 1, 3, 3, 0, 0, 0], 26, [(0, 1, 4), (1, 4, 4), (3, 0, 1), (3, 2, 3), (4, 1, 1), (4, 5, 4), (6, 2, 2), (6, 3, 1), (6, 4, 1), (6, 5, 1), (5, 3, 4)]),
  ([0, 1, 4, 0, 0, 0, 2], 3, [(0, 3, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 1, 4, 0, 0, 1, 1], 3, [(0, 3, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 1, 4, 0, 0, 2, 0], 3, [(0, 3, 1), (3, 2, 1), (5, 1, 1)]),
  ([0, 1, 4, 0, 1, 0, 1], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 4, 0, 1, 1, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 4, 0, 2, 0, 0], 3, [(0, 1, 1), (3, 2, 1), (5, 3, 1)]),
  ([0, 1, 4, 1, 0, 0, 1], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 4, 1, 0, 1, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 4, 1, 1, 0, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 4, 2, 0, 0, 0], 3, [(0, 1, 1), (3, 2, 1), (5, 3, 1)]),
  ([0, 1, 5, 0, 0, 0, 1], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 5, 0, 0, 1, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([0, 1, 5, 0, 1, 0, 0], 3, [(0, 1, 1), (3, 2, 1), (5, 4, 1)]),
  ([0, 1, 5, 1, 0, 0, 0], 3, [(0, 1, 1), (3, 2, 1), (5, 3, 1)]),
  ([0, 1, 6, 0, 0, 0, 0], 3, [(0, 1, 1), (3, 5, 1), (5, 3, 1)]),
  ([0, 2, 0, 0, 0, 0, 5], 9, [(2, 2, 1), (4, 2, 1), (0, 3, 2), (2, 4, 2), (4, 5, 2), (6, 0, 1)]),
  ([0, 2, 0, 0, 0, 1, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([0, 2, 0, 0, 0, 2, 3], 8, [(0, 2, 1), (0, 3, 1), (1, 4, 1), (4, 4, 2), (2, 5, 2), (3, 5, 1)]),
  ([0, 2, 0, 0, 0, 3, 2], 16, [(2, 0, 1), (1, 2, 1), (1, 3, 3), (3, 3, 3), (1, 4, 1), (3, 5, 1), (3, 6, 1), (6, 2, 5)])
]
theorem chunk_016_checked : chunk_016.all checkCertificate = true := by
  decide

def chunk_017 : List Certificate := [
  ([0, 2, 0, 0, 0, 4, 1], 3, [(3, 2, 1), (1, 4, 1), (6, 3, 1)]),
  ([0, 2, 0, 0, 0, 5, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 2, 1)]),
  ([0, 2, 0, 0, 1, 0, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([0, 2, 0, 0, 1, 1, 3], 8, [(2, 0, 1), (0, 4, 2), (4, 4, 1), (2, 5, 1), (4, 5, 2), (2, 6, 1)]),
  ([0, 2, 0, 0, 1, 2, 2], 18, [(0, 2, 3), (2, 3, 3), (0, 4, 1), (1, 4, 2), (2, 4, 2), (0, 5, 1), (3, 5, 2), (4, 5, 2), (6, 3, 2)]),
  ([0, 2, 0, 0, 1, 3, 1], 8, [(2, 0, 1), (1, 2, 1), (1, 3, 1), (3, 3, 2), (6, 4, 3)]),
  ([0, 2, 0, 0, 1, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 2, 0, 0, 2, 0, 3], 8, [(4, 0, 1), (0, 4, 2), (4, 4, 1), (2, 5, 3), (4, 6, 1)]),
  ([0, 2, 0, 0, 2, 1, 2], 28, [(2, 2, 5), (0, 3, 4), (1, 3, 1), (0, 4, 5), (3, 4, 2), (1, 5, 1), (2, 5, 4), (4, 5, 2), (6, 3, 2), (5, 2, 2)]),
  ([0, 2, 0, 0, 2, 2, 1], 18, [(2, 2, 5), (0, 3, 1), (0, 4, 2), (1, 4, 2), (3, 4, 1), (3, 5, 1), (6, 3, 4), (5, 0, 2)]),
  ([0, 2, 0, 0, 2, 3, 0], 22, [(2, 3, 5), (0, 4, 3), (1, 4, 2), (1, 5, 1), (3, 5, 3), (6, 2, 4), (6, 5, 1), (5, 0, 2), (5, 2, 1)]),
  ([0, 2, 0, 0, 3, 0, 2], 16, [(2, 0, 1), (0, 2, 4), (2, 2, 2), (2, 3, 1), (0, 4, 1), (2, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([0, 2, 0, 0, 3, 1, 1], 16, [(2, 0, 1), (0, 2, 4), (2, 2, 2), (2, 3, 1), (0, 4, 1), (2, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([0, 2, 0, 0, 3, 2, 0], 11, [(2, 0, 1), (0, 2, 2), (2, 4, 2), (1, 5, 1), (3, 5, 1), (6, 2, 1), (6, 3, 1), (5, 3, 2)]),
  ([0, 2, 0, 0, 4, 0, 1], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([0, 2, 0, 0, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([0, 2, 0, 0, 5, 0, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 4, 1)]),
  ([0, 2, 0, 1, 0, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([0, 2, 0, 1, 0, 1, 3], 8, [(4, 0, 1), (0, 4, 2), (4, 4, 1), (2, 5, 3), (4, 6, 1)]),
  ([0, 2, 0, 1, 0, 2, 2], 5, [(2, 0, 1), (1, 4, 1), (3, 5, 1), (4, 6, 1), (6, 3, 1)]),
  ([0, 2, 0, 1, 0, 3, 1], 21, [(3, 0, 1), (1, 2, 1), (1, 3, 4), (3, 3, 4), (1, 4, 2), (3, 5, 1), (3, 6, 1), (6, 1, 1), (6, 4, 6)]),
  ([0, 2, 0, 1, 0, 4, 0], 3, [(3, 3, 1), (1, 4, 1), (6, 5, 1)]),
  ([0, 2, 0, 1, 1, 0, 3], 8, [(4, 0, 1), (0, 4, 2), (2, 4, 1), (2, 5, 2), (4, 5, 1), (4, 6, 1)]),
  ([0, 2, 0, 1, 1, 1, 2], 28, [(2, 0, 1), (2, 3, 5), (2, 4, 3), (3, 4, 2), (0, 5, 2), (1, 5, 2), (2, 5, 1), (4, 6, 5), (6, 0, 5), (5, 0, 2)]),
  ([0, 2, 0, 1, 1, 2, 1], 14, [(0, 3, 4), (1, 3, 1), (2, 4, 3), (2, 5, 2), (3, 5, 1), (6, 4, 2), (5, 0, 1)]),
  ([0, 2, 0, 1, 1, 3, 0], 8, [(2, 0, 1), (1, 3, 1), (1, 4, 1), (3, 4, 2), (6, 5, 3)]),
  ([0, 2, 0, 1, 2, 0, 2], 28, [(2, 0, 1), (0, 2, 5), (2, 3, 3), (4, 0, 5), (2, 4, 1), (0, 5, 1), (2, 6, 1), (6, 2, 1), (6, 3, 4), (5, 1, 6)]),
  ([0, 2, 0, 1, 2, 1, 1], 21, [(2, 0, 1), (0, 2, 4), (2, 3, 2), (2, 4, 1), (4, 0, 4), (6, 1, 1), (6, 2, 1), (6, 3, 3), (5, 1, 4)]),
  ([0, 2, 0, 1, 2, 2, 0], 18, [(2, 0, 1), (0, 2, 2), (1, 4, 4), (2, 4, 1), (2, 5, 1), (3, 5, 2), (6, 3, 3), (6, 5, 2), (5, 3, 2)]),
  ([0, 2, 0, 1, 3, 0, 1], 21, [(0, 3, 4), (0, 4, 3), (2, 4, 5), (2, 5, 1), (2, 6, 1), (5, 0, 1), (5, 1, 1), (5, 2, 1), (5, 3, 4)]),
  ([0, 2, 0, 1, 3, 1, 0], 8, [(1, 3, 1), (2, 3, 1), (0, 4, 1), (2, 4, 1), (0, 5, 1), (6, 4, 1), (5, 2, 1), (5, 3, 1)]),
  ([0, 2, 0, 1, 4, 0, 0], 3, [(2, 3, 1), (0, 5, 1), (5, 4, 1)])
]
theorem chunk_017_checked : chunk_017.all checkCertificate = true := by
  decide

def chunk_018 : List Certificate := [
  ([0, 2, 0, 2, 0, 0, 3], 16, [(0, 2, 1), (4, 0, 1), (4, 1, 1), (0, 4, 4), (2, 4, 2), (2, 5, 2), (4, 5, 4), (2, 6, 1)]),
  ([0, 2, 0, 2, 0, 1, 2], 21, [(0, 2, 4), (4, 0, 3), (4, 1, 2), (1, 4, 1), (2, 4, 2), (2, 5, 2), (3, 5, 1), (6, 1, 2), (6, 3, 3), (5, 0, 1)]),
  ([0, 2, 0, 2, 0, 2, 1], 35, [(0, 2, 4), (2, 0, 1), (1, 3, 4), (2, 4, 3), (3, 4, 4), (4, 1, 1), (4, 2, 3), (6, 0, 2), (6, 1, 6), (6, 3, 3), (5, 0, 4)]),
  ([0, 2, 0, 2, 0, 3, 0], 16, [(1, 2, 1), (1, 4, 3), (1, 5, 1), (3, 5, 5), (6, 0, 1), (6, 1, 1), (6, 3, 1), (6, 4, 3)]),
  ([0, 2, 0, 2, 1, 0, 2], 7, [(0, 2, 1), (2, 0, 1), (4, 0, 1), (4, 1, 1), (6, 2, 1), (6, 3, 1), (5, 1, 1)]),
  ([0, 2, 0, 2, 1, 1, 1], 7, [(0, 2, 1), (2, 0, 1), (4, 0, 1), (4, 1, 1), (6, 2, 1), (6, 3, 1), (5, 1, 1)]),
  ([0, 2, 0, 2, 1, 2, 0], 28, [(0, 2, 2), (1, 4, 4), (2, 4, 2), (1, 5, 5), (3, 5, 2), (4, 2, 2), (6, 2, 3), (6, 3, 5), (6, 4, 1), (5, 3, 2)]),
  ([0, 2, 0, 2, 2, 0, 1], 5, [(0, 3, 1), (2, 4, 1), (4, 1, 1), (6, 0, 1), (5, 2, 1)]),
  ([0, 2, 0, 2, 2, 1, 0], 18, [(1, 3, 5), (2, 4, 2), (0, 5, 2), (4, 2, 2), (6, 2, 1), (6, 4, 3), (6, 5, 1), (5, 2, 2)]),
  ([0, 2, 0, 2, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 5, 1), (2, 5, 2), (5, 4, 3)]),
  ([0, 2, 0, 3, 0, 0, 2], 8, [(1, 2, 2), (4, 0, 1), (4, 3, 2), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 2, 0, 3, 0, 1, 1], 8, [(1, 2, 2), (4, 0, 1), (4, 3, 2), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 2, 0, 3, 0, 2, 0], 8, [(1, 2, 2), (4, 0, 1), (4, 3, 2), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 2, 0, 3, 1, 0, 1], 8, [(1, 2, 2), (4, 1, 1), (4, 3, 2), (6, 0, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 2, 0, 3, 1, 1, 0], 8, [(1, 2, 2), (4, 1, 1), (4, 2, 1), (4, 3, 1), (6, 0, 1), (6, 3, 2)]),
  ([0, 2, 0, 3, 2, 0, 0], 8, [(0, 2, 2), (1, 3, 1), (2, 5, 1), (4, 3, 1), (6, 5, 1), (5, 4, 2)]),
  ([0, 2, 0, 4, 0, 0, 1], 3, [(1, 4, 1), (4, 3, 1), (6, 2, 1)]),
  ([0, 2, 0, 4, 0, 1, 0], 3, [(1, 3, 1), (4, 2, 1), (6, 4, 1)]),
  ([0, 2, 0, 4, 1, 0, 0], 3, [(1, 2, 1), (4, 4, 1), (6, 3, 1)]),
  ([0, 2, 0, 5, 0, 0, 0], 3, [(1, 4, 1), (4, 3, 1), (6, 2, 1)]),
  ([0, 2, 1, 0, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 2, 1, 0, 0, 1, 3], 16, [(2, 0, 1), (4, 1, 1), (0, 3, 1), (0, 4, 2), (2, 4, 4), (0, 5, 2), (4, 5, 4), (3, 6, 1)]),
  ([0, 2, 1, 0, 0, 2, 2], 33, [(2, 0, 3), (1, 3, 3), (4, 1, 3), (3, 4, 8), (0, 5, 5), (1, 5, 2), (4, 5, 1), (2, 6, 2), (4, 6, 1), (6, 3, 5)]),
  ([0, 2, 1, 0, 0, 3, 1], 16, [(3, 0, 1), (3, 1, 1), (1, 3, 3), (3, 3, 3), (1, 4, 1), (1, 5, 1), (3, 6, 1), (6, 4, 5)]),
  ([0, 2, 1, 0, 0, 4, 0], 3, [(3, 4, 1), (1, 5, 1), (6, 3, 1)]),
  ([0, 2, 1, 0, 1, 0, 3], 8, [(2, 0, 1), (0, 4, 2), (4, 4, 1), (2, 5, 2), (4, 5, 1), (4, 6, 1)]),
  ([0, 2, 1, 0, 1, 1, 2], 56, [(3, 1, 11), (2, 3, 7), (0, 4, 4), (2, 4, 3), (0, 5, 7), (2, 6, 1), (4, 6, 6), (6, 0, 2), (6, 1, 2), (6, 2, 2), (5, 0, 11)]),
  ([0, 2, 1, 0, 1, 2, 1], 14, [(3, 1, 3), (2, 3, 2), (0, 4, 1), (0, 5, 2), (2, 6, 1), (4, 6, 1), (6, 4, 1), (5, 0, 3)]),
  ([0, 2, 1, 0, 1, 3, 0], 8, [(3, 0, 1), (3, 1, 1), (3, 4, 1), (1, 5, 2), (6, 4, 2), (6, 5, 1)]),
  ([0, 2, 1, 0, 2, 0, 2], 42, [(2, 0, 1), (0, 2, 4), (0, 3, 2), (2, 3, 2), (3, 0, 7), (2, 4, 4), (0, 5, 1), (4, 5, 3), (4, 6, 4), (6, 0, 3), (6, 1, 4), (5, 1, 7)]),
  ([0, 2, 1, 0, 2, 1, 1], 21, [(2, 0, 1), (0, 2, 1), (0, 3, 3), (2, 3, 2), (3, 0, 4), (2, 4, 1), (6, 1, 1), (6, 4, 4), (5, 1, 4)]),
  ([0, 2, 1, 0, 2, 2, 0], 18, [(2, 3, 4), (3, 0, 2), (0, 4, 2), (1, 4, 2), (2, 5, 1), (6, 4, 1), (6, 5, 4), (5, 0, 1), (5, 3, 1)])
]
theorem chunk_018_checked : chunk_018.all checkCertificate = true := by
  decide

def chunk_019 : List Certificate := [
  ([0, 2, 1, 0, 3, 0, 1], 21, [(0, 3, 7), (2, 3, 1), (2, 4, 4), (2, 5, 1), (2, 6, 1), (5, 0, 1), (5, 1, 1), (5, 2, 1), (5, 4, 4)]),
  ([0, 2, 1, 0, 3, 1, 0], 16, [(0, 3, 5), (2, 3, 1), (2, 4, 3), (2, 5, 1), (6, 1, 1), (5, 0, 1), (5, 2, 1), (5, 4, 3)]),
  ([0, 2, 1, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 5, 1), (5, 4, 1)]),
  ([0, 2, 1, 1, 0, 0, 3], 8, [(2, 0, 1), (0, 4, 2), (4, 4, 1), (2, 5, 1), (4, 5, 2), (2, 6, 1)]),
  ([0, 2, 1, 1, 0, 1, 2], 7, [(3, 1, 2), (0, 4, 1), (4, 5, 1), (2, 6, 1), (6, 0, 1), (5, 0, 1)]),
  ([0, 2, 1, 1, 0, 2, 1], 7, [(2, 0, 1), (3, 1, 2), (0, 5, 1), (4, 6, 1), (6, 4, 1), (5, 0, 1)]),
  ([0, 2, 1, 1, 0, 3, 0], 8, [(3, 4, 3), (1, 5, 2), (6, 0, 1), (6, 1, 1), (6, 5, 1)]),
  ([0, 2, 1, 1, 1, 0, 2], 21, [(0, 2, 1), (2, 0, 1), (3, 0, 4), (4, 1, 1), (0, 4, 1), (0, 5, 2), (2, 5, 2), (2, 6, 1), (4, 6, 3), (6, 3, 1), (5, 1, 4)]),
  ([0, 2, 1, 1, 1, 1, 1], 56, [(0, 2, 6), (1, 3, 2), (3, 0, 9), (2, 4, 6), (4, 0, 3), (0, 5, 3), (2, 5, 3), (4, 6, 6), (6, 0, 1), (6, 1, 4), (6, 3, 4), (5, 1, 9)]),
  ([0, 2, 1, 1, 1, 2, 0], 42, [(0, 2, 4), (1, 3, 3), (3, 0, 5), (0, 4, 1), (1, 5, 2), (2, 5, 5), (4, 0, 2), (4, 2, 3), (6, 1, 2), (6, 3, 4), (6, 4, 6), (5, 1, 5)]),
  ([0, 2, 1, 1, 2, 0, 1], 5, [(0, 3, 1), (2, 4, 1), (4, 1, 1), (6, 0, 1), (5, 2, 1)]),
  ([0, 2, 1, 1, 2, 1, 0], 5, [(0, 3, 1), (2, 4, 1), (4, 0, 1), (6, 1, 1), (5, 2, 1)]),
  ([0, 2, 1, 1, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 5, 1), (2, 5, 2), (5, 4, 3)]),
  ([0, 2, 1, 2, 0, 0, 2], 28, [(0, 2, 2), (1, 3, 2), (2, 0, 2), (3, 0, 2), (4, 0, 3), (4, 2, 1), (4, 3, 5), (6, 1, 5), (6, 2, 4), (5, 1, 2)]),
  ([0, 2, 1, 2, 0, 1, 1], 28, [(0, 2, 1), (0, 3, 1), (1, 3, 2), (2, 0, 2), (3, 0, 2), (4, 1, 5), (4, 3, 4), (6, 0, 3), (6, 2, 6), (5, 1, 2)]),
  ([0, 2, 1, 2, 0, 2, 0], 28, [(0, 2, 2), (1, 3, 2), (2, 0, 2), (3, 0, 2), (4, 1, 4), (4, 2, 5), (6, 0, 3), (6, 1, 1), (6, 3, 5), (5, 1, 2)]),
  ([0, 2, 1, 2, 1, 0, 1], 28, [(0, 3, 2), (1, 3, 2), (2, 0, 2), (3, 1, 2), (4, 0, 5), (4, 2, 4), (6, 1, 5), (6, 2, 1), (6, 3, 3), (5, 2, 2)]),
  ([0, 2, 1, 2, 1, 1, 0], 28, [(0, 3, 2), (1, 3, 2), (2, 0, 2), (3, 1, 2), (4, 0, 5), (4, 2, 4), (6, 1, 5), (6, 2, 1), (6, 3, 3), (5, 2, 2)]),
  ([0, 2, 1, 2, 2, 0, 0], 21, [(0, 2, 3), (1, 3, 1), (2, 0, 1), (0, 5, 1), (2, 5, 3), (4, 0, 2), (4, 1, 2), (6, 1, 1), (6, 3, 3), (5, 4, 4)]),
  ([0, 2, 1, 3, 0, 0, 1], 11, [(1, 4, 3), (4, 3, 4), (6, 0, 1), (6, 1, 1), (6, 2, 1), (6, 4, 1)]),
  ([0, 2, 1, 3, 0, 1, 0], 11, [(1, 3, 3), (4, 0, 1), (4, 3, 1), (4, 4, 2), (6, 1, 1), (6, 2, 1), (6, 4, 2)]),
  ([0, 2, 1, 3, 1, 0, 0], 11, [(1, 3, 3), (4, 4, 4), (6, 0, 1), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 2, 1, 4, 0, 0, 0], 3, [(1, 4, 1), (4, 3, 1), (6, 5, 1)]),
  ([0, 2, 2, 0, 0, 0, 3], 8, [(3, 2, 1), (4, 1, 1), (2, 4, 1), (4, 4, 1), (0, 5, 2), (2, 6, 1), (5, 0, 1)]),
  ([0, 2, 2, 0, 0, 1, 2], 33, [(0, 2, 2), (3, 1, 2), (3, 2, 6), (4, 1, 4), (2, 4, 3), (0, 5, 3), (2, 6, 2), (4, 6, 1), (6, 0, 3), (6, 1, 2), (5, 0, 5)]),
  ([0, 2, 2, 0, 0, 2, 1], 18, [(0, 2, 2), (3, 1, 1), (3, 2, 3), (2, 4, 2), (3, 4, 1), (4, 1, 2), (6, 0, 3), (6, 1, 2), (5, 0, 2)]),
  ([0, 2, 2, 0, 0, 3, 0], 11, [(3, 2, 1), (1, 4, 1), (3, 4, 3), (1, 5, 2), (6, 0, 1), (6, 1, 1), (6, 5, 2)]),
  ([0, 2, 2, 0, 1, 0, 2], 5, [(0, 2, 1), (2, 0, 1), (4, 5, 1), (3, 6, 1), (5, 1, 1)]),
  ([0, 2, 2, 0, 1, 1, 1], 42, [(0, 2, 4), (2, 0, 1), (3, 0, 1), (3, 2, 6), (2, 4, 3), (4, 0, 4), (4, 1, 3), (0, 5, 3), (2, 6, 3), (6, 0, 4), (6, 3, 3), (5, 1, 7)]),
  ([0, 2, 2, 0, 1, 2, 0], 18, [(0, 2, 2), (2, 0, 2), (3, 2, 3), (3, 5, 2), (4, 0, 2), (6, 0, 1), (6, 1, 3), (6, 5, 1), (5, 1, 2)]),
  ([0, 2, 2, 0, 2, 0, 1], 5, [(0, 3, 1), (2, 4, 1), (4, 0, 1), (6, 1, 1), (5, 2, 1)]),
  ([0, 2, 2, 0, 2, 1, 0], 33, [(2, 0, 2), (0, 3, 3), (0, 4, 2), (3, 1, 5), (2, 5, 3), (4, 0, 2), (4, 1, 3), (6, 0, 4), (6, 2, 3), (6, 4, 1), (5, 2, 5)])
]
theorem chunk_019_checked : chunk_019.all checkCertificate = true := by
  decide

def chunk_020 : List Certificate := [
  ([0, 2, 2, 0, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 5, 1), (2, 5, 2), (5, 4, 3)]),
  ([0, 2, 2, 1, 0, 0, 2], 18, [(0, 2, 2), (2, 0, 2), (3, 2, 2), (4, 0, 2), (4, 3, 3), (6, 0, 1), (6, 1, 3), (6, 2, 1), (5, 1, 2)]),
  ([0, 2, 2, 1, 0, 1, 1], 18, [(0, 2, 2), (2, 0, 2), (3, 2, 2), (4, 0, 1), (4, 1, 3), (4, 2, 1), (6, 0, 2), (6, 3, 3), (5, 1, 2)]),
  ([0, 2, 2, 1, 0, 2, 0], 18, [(0, 2, 2), (2, 0, 2), (3, 2, 3), (4, 0, 2), (4, 3, 2), (6, 0, 1), (6, 1, 3), (6, 5, 1), (5, 1, 2)]),
  ([0, 2, 2, 1, 1, 0, 1], 18, [(0, 3, 2), (2, 0, 2), (3, 0, 1), (3, 1, 1), (4, 0, 2), (4, 2, 3), (6, 1, 4), (6, 3, 1), (5, 2, 2)]),
  ([0, 2, 2, 1, 1, 1, 0], 18, [(0, 3, 2), (2, 0, 2), (3, 0, 2), (4, 1, 1), (4, 2, 3), (4, 3, 1), (6, 0, 1), (6, 1, 4), (5, 2, 2)]),
  ([0, 2, 2, 1, 2, 0, 0], 42, [(0, 2, 6), (0, 3, 2), (2, 0, 2), (1, 5, 1), (2, 5, 6), (3, 0, 1), (4, 1, 7), (4, 3, 1), (6, 0, 4), (6, 3, 4), (5, 2, 1), (5, 4, 7)]),
  ([0, 2, 2, 2, 0, 0, 1], 35, [(0, 3, 3), (1, 4, 3), (2, 0, 3), (3, 1, 3), (4, 1, 2), (4, 2, 4), (4, 3, 4), (6, 0, 4), (6, 1, 2), (6, 4, 4), (5, 2, 3)]),
  ([0, 2, 2, 2, 0, 1, 0], 35, [(0, 3, 3), (1, 4, 3), (2, 0, 3), (3, 2, 3), (4, 0, 4), (4, 1, 1), (4, 2, 1), (4, 4, 4), (6, 1, 6), (6, 3, 4), (5, 2, 3)]),
  ([0, 2, 2, 2, 1, 0, 0], 35, [(0, 2, 3), (1, 4, 3), (2, 0, 3), (3, 1, 3), (4, 0, 4), (4, 1, 4), (4, 3, 2), (6, 2, 4), (6, 3, 5), (6, 4, 1), (5, 4, 3)]),
  ([0, 2, 2, 3, 0, 0, 0], 14, [(0, 2, 2), (1, 4, 2), (3, 0, 1), (3, 1, 1), (4, 3, 1), (4, 4, 1), (4, 5, 1), (6, 2, 1), (6, 5, 2), (5, 3, 2)]),
  ([0, 2, 3, 0, 0, 0, 2], 8, [(0, 3, 1), (2, 0, 1), (3, 2, 2), (4, 0, 1), (6, 3, 1), (5, 1, 2)]),
  ([0, 2, 3, 0, 0, 1, 1], 8, [(0, 2, 1), (2, 0, 1), (3, 2, 1), (3, 3, 1), (4, 0, 1), (6, 3, 1), (5, 1, 2)]),
  ([0, 2, 3, 0, 0, 2, 0], 22, [(0, 2, 3), (2, 0, 3), (3, 2, 2), (3, 3, 2), (3, 5, 1), (4, 3, 3), (6, 0, 2), (6, 1, 2), (6, 5, 1), (5, 1, 3)]),
  ([0, 2, 3, 0, 1, 0, 1], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([0, 2, 3, 0, 1, 1, 0], 32, [(0, 3, 9), (3, 0, 3), (3, 1, 3), (3, 2, 3), (4, 3, 2), (6, 3, 1), (6, 4, 1), (6, 5, 1), (5, 2, 9)]),
  ([0, 2, 3, 0, 2, 0, 0], 16, [(0, 2, 5), (2, 5, 1), (3, 3, 3), (4, 0, 1), (6, 5, 1), (5, 1, 1), (5, 3, 2), (5, 4, 2)]),
  ([0, 2, 3, 1, 0, 0, 1], 11, [(0, 3, 3), (3, 0, 1), (3, 1, 1), (3, 3, 1), (4, 2, 1), (6, 4, 1), (5, 2, 3)]),
  ([0, 2, 3, 1, 0, 1, 0], 11, [(0, 3, 3), (3, 0, 1), (3, 2, 1), (3, 3, 1), (4, 4, 1), (6, 1, 1), (5, 2, 3)]),
  ([0, 2, 3, 1, 1, 0, 0], 11, [(0, 2, 3), (3, 1, 1), (3, 3, 2), (4, 3, 1), (6, 3, 1), (5, 0, 1), (5, 2, 1), (5, 4, 1)]),
  ([0, 2, 3, 2, 0, 0, 0], 28, [(0, 2, 7), (2, 0, 1), (3, 0, 2), (3, 1, 3), (3, 3, 2), (4, 2, 2), (4, 5, 1), (6, 4, 2), (6, 5, 1), (5, 3, 7)]),
  ([0, 2, 4, 0, 0, 0, 1], 3, [(0, 3, 1), (3, 4, 1), (5, 2, 1)]),
  ([0, 2, 4, 0, 0, 1, 0], 3, [(0, 3, 1), (3, 4, 1), (5, 2, 1)]),
  ([0, 2, 4, 0, 1, 0, 0], 3, [(0, 2, 1), (3, 3, 1), (5, 4, 1)]),
  ([0, 2, 4, 1, 0, 0, 0], 3, [(0, 2, 1), (3, 4, 1), (5, 3, 1)]),
  ([0, 2, 5, 0, 0, 0, 0], 3, [(0, 3, 1), (3, 2, 1), (5, 4, 1)]),
  ([0, 3, 0, 0, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([0, 3, 0, 0, 0, 1, 3], 11, [(2, 1, 1), (4, 0, 3), (2, 4, 2), (0, 5, 1), (4, 5, 1), (2, 6, 1), (6, 1, 2)]),
  ([0, 3, 0, 0, 0, 2, 2], 24, [(2, 0, 8), (4, 1, 3), (1, 4, 1), (3, 4, 1), (4, 5, 2), (4, 6, 2), (6, 1, 5), (6, 3, 2)]),
  ([0, 3, 0, 0, 0, 3, 1], 8, [(2, 0, 3), (4, 1, 2), (6, 1, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 0, 0, 0, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([0, 3, 0, 0, 1, 0, 3], 11, [(2, 0, 1), (2, 1, 1), (0, 4, 3), (2, 4, 1), (4, 5, 4), (2, 6, 1)])
]
theorem chunk_020_checked : chunk_020.all checkCertificate = true := by
  decide

def chunk_021 : List Certificate := [
  ([0, 3, 0, 0, 1, 1, 2], 8, [(2, 0, 1), (2, 1, 2), (4, 1, 1), (4, 5, 1), (4, 6, 1), (6, 0, 2)]),
  ([0, 3, 0, 0, 1, 2, 1], 8, [(2, 0, 2), (2, 1, 1), (4, 1, 2), (6, 0, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 0, 0, 1, 3, 0], 11, [(2, 0, 1), (2, 1, 1), (2, 3, 1), (2, 4, 1), (4, 0, 3), (6, 1, 3), (6, 5, 1)]),
  ([0, 3, 0, 0, 2, 0, 2], 16, [(2, 0, 5), (4, 0, 1), (4, 1, 2), (2, 4, 1), (4, 5, 1), (4, 6, 1), (6, 1, 4), (6, 3, 1)]),
  ([0, 3, 0, 0, 2, 1, 1], 8, [(2, 0, 3), (4, 1, 2), (6, 1, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 0, 0, 2, 2, 0], 11, [(2, 0, 3), (2, 1, 1), (4, 1, 3), (6, 0, 1), (6, 3, 1), (6, 4, 1), (6, 5, 1)]),
  ([0, 3, 0, 0, 3, 0, 1], 16, [(2, 0, 1), (2, 1, 1), (0, 3, 5), (2, 3, 1), (2, 4, 1), (2, 5, 1), (2, 6, 1), (5, 4, 5)]),
  ([0, 3, 0, 0, 3, 1, 0], 11, [(2, 1, 1), (0, 3, 3), (2, 3, 1), (2, 4, 1), (2, 5, 1), (6, 0, 1), (5, 4, 3)]),
  ([0, 3, 0, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 5, 1), (5, 4, 1)]),
  ([0, 3, 0, 1, 0, 0, 3], 11, [(2, 0, 1), (2, 1, 1), (0, 4, 3), (2, 4, 1), (4, 5, 4), (2, 6, 1)]),
  ([0, 3, 0, 1, 0, 1, 2], 8, [(2, 0, 1), (2, 1, 2), (4, 1, 1), (4, 5, 1), (4, 6, 1), (6, 0, 2)]),
  ([0, 3, 0, 1, 0, 2, 1], 21, [(2, 0, 2), (2, 1, 3), (2, 4, 1), (4, 1, 5), (4, 2, 1), (2, 5, 1), (4, 6, 1), (6, 0, 6), (6, 3, 1)]),
  ([0, 3, 0, 1, 0, 3, 0], 16, [(2, 1, 4), (2, 4, 1), (4, 0, 3), (4, 1, 2), (6, 0, 3), (6, 2, 1), (6, 3, 1), (6, 5, 1)]),
  ([0, 3, 0, 1, 1, 0, 2], 8, [(2, 0, 3), (4, 1, 1), (4, 5, 1), (4, 6, 1), (6, 1, 2)]),
  ([0, 3, 0, 1, 1, 1, 1], 21, [(2, 0, 6), (4, 0, 2), (4, 1, 3), (4, 2, 1), (2, 5, 1), (4, 6, 1), (6, 1, 5), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 0, 1, 1, 2, 0], 8, [(2, 0, 3), (4, 1, 2), (6, 1, 1), (6, 4, 1), (6, 5, 1)]),
  ([0, 3, 0, 1, 2, 0, 1], 21, [(2, 1, 6), (4, 0, 4), (4, 1, 2), (2, 5, 1), (4, 6, 1), (6, 0, 4), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 0, 1, 2, 1, 0], 8, [(2, 1, 1), (2, 4, 1), (2, 5, 1), (4, 1, 2), (6, 0, 3)]),
  ([0, 3, 0, 1, 3, 0, 0], 8, [(2, 0, 3), (4, 1, 2), (6, 1, 1), (6, 5, 1), (5, 4, 1)]),
  ([0, 3, 0, 2, 0, 0, 2], 8, [(2, 0, 2), (4, 1, 1), (4, 2, 1), (4, 3, 1), (6, 0, 1), (6, 1, 2)]),
  ([0, 3, 0, 2, 0, 1, 1], 8, [(2, 0, 2), (4, 0, 1), (4, 1, 1), (4, 2, 1), (6, 1, 2), (6, 3, 1)]),
  ([0, 3, 0, 2, 0, 2, 0], 8, [(2, 1, 2), (4, 1, 1), (4, 2, 1), (4, 3, 1), (6, 0, 3)]),
  ([0, 3, 0, 2, 1, 0, 1], 8, [(2, 1, 2), (4, 0, 3), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([0, 3, 0, 2, 1, 1, 0], 8, [(2, 1, 2), (4, 1, 1), (4, 2, 1), (4, 3, 1), (6, 0, 3)]),
  ([0, 3, 0, 2, 2, 0, 0], 8, [(0, 3, 1), (2, 0, 1), (2, 5, 1), (4, 0, 1), (4, 2, 1), (6, 1, 2), (5, 4, 1)]),
  ([0, 3, 0, 3, 0, 0, 1], 11, [(1, 3, 1), (2, 0, 2), (4, 2, 1), (4, 3, 1), (4, 4, 2), (6, 0, 1), (6, 1, 3)]),
  ([0, 3, 0, 3, 0, 1, 0], 11, [(1, 3, 2), (2, 1, 1), (4, 3, 1), (4, 4, 3), (6, 0, 2), (6, 1, 1), (6, 2, 1)]),
  ([0, 3, 0, 3, 1, 0, 0], 11, [(2, 1, 3), (4, 0, 3), (4, 2, 1), (6, 0, 1), (6, 1, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 0, 4, 0, 0, 0], 3, [(1, 3, 1), (4, 4, 1), (6, 5, 1)]),
  ([0, 3, 1, 0, 0, 0, 3], 11, [(4, 0, 1), (4, 1, 1), (2, 4, 4), (0, 5, 3), (4, 5, 1), (4, 6, 1)]),
  ([0, 3, 1, 0, 0, 1, 2], 16, [(2, 0, 3), (3, 2, 1), (4, 1, 4), (2, 4, 1), (4, 5, 1), (2, 6, 1), (6, 0, 3), (6, 1, 2)]),
  ([0, 3, 1, 0, 0, 2, 1], 8, [(2, 0, 2), (3, 2, 1), (4, 1, 2), (6, 0, 1), (6, 1, 1), (6, 4, 1)])
]
theorem chunk_021_checked : chunk_021.all checkCertificate = true := by
  decide

def chunk_022 : List Certificate := [
  ([0, 3, 1, 0, 0, 3, 0], 11, [(2, 0, 3), (3, 2, 1), (4, 0, 1), (4, 1, 2), (6, 1, 2), (6, 4, 1), (6, 5, 1)]),
  ([0, 3, 1, 0, 1, 0, 2], 8, [(2, 0, 2), (2, 1, 1), (4, 0, 1), (4, 5, 1), (4, 6, 1), (6, 1, 2)]),
  ([0, 3, 1, 0, 1, 1, 1], 21, [(2, 0, 6), (4, 0, 2), (4, 1, 4), (2, 5, 1), (4, 6, 1), (6, 1, 4), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 1, 0, 1, 2, 0], 16, [(2, 0, 3), (2, 1, 1), (2, 5, 1), (4, 1, 5), (6, 0, 3), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 1, 0, 2, 0, 1], 21, [(2, 1, 4), (2, 4, 1), (4, 0, 2), (4, 1, 4), (4, 2, 1), (2, 5, 1), (2, 6, 1), (6, 0, 6), (6, 3, 1)]),
  ([0, 3, 1, 0, 2, 1, 0], 16, [(2, 0, 1), (2, 1, 3), (2, 5, 1), (4, 0, 5), (6, 1, 3), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 1, 0, 3, 0, 0], 8, [(2, 0, 1), (2, 1, 1), (0, 5, 2), (2, 5, 1), (5, 4, 3)]),
  ([0, 3, 1, 1, 0, 0, 2], 8, [(2, 1, 3), (4, 0, 1), (4, 5, 1), (4, 6, 1), (6, 0, 2)]),
  ([0, 3, 1, 1, 0, 1, 1], 8, [(2, 0, 2), (4, 0, 1), (4, 2, 1), (4, 3, 1), (6, 1, 3)]),
  ([0, 3, 1, 1, 0, 2, 0], 8, [(2, 0, 1), (3, 2, 1), (2, 5, 1), (4, 0, 2), (6, 1, 3)]),
  ([0, 3, 1, 1, 1, 0, 1], 8, [(2, 1, 2), (4, 1, 1), (4, 2, 1), (4, 3, 1), (6, 0, 3)]),
  ([0, 3, 1, 1, 1, 1, 0], 8, [(2, 0, 1), (2, 1, 1), (4, 0, 2), (4, 3, 1), (6, 1, 2), (6, 2, 1)]),
  ([0, 3, 1, 1, 2, 0, 0], 8, [(0, 3, 1), (2, 0, 2), (4, 1, 2), (6, 2, 1), (6, 5, 1), (5, 4, 1)]),
  ([0, 3, 1, 2, 0, 0, 1], 11, [(2, 1, 3), (4, 0, 3), (4, 3, 1), (6, 0, 1), (6, 1, 1), (6, 2, 1), (6, 4, 1)]),
  ([0, 3, 1, 2, 0, 1, 0], 11, [(2, 0, 1), (2, 1, 2), (4, 0, 3), (4, 2, 1), (6, 1, 2), (6, 3, 1), (6, 4, 1)]),
  ([0, 3, 1, 2, 1, 0, 0], 11, [(2, 0, 3), (4, 0, 1), (4, 2, 1), (4, 3, 1), (4, 4, 1), (6, 1, 4)]),
  ([0, 3, 1, 3, 0, 0, 0], 42, [(0, 4, 4), (1, 4, 3), (1, 5, 1), (2, 0, 4), (3, 0, 3), (3, 2, 1), (4, 1, 7), (4, 3, 3), (4, 5, 1), (6, 2, 6), (6, 5, 5), (5, 3, 4)]),
  ([0, 3, 2, 0, 0, 0, 2], 8, [(0, 3, 1), (2, 0, 1), (3, 2, 2), (4, 3, 1), (6, 0, 1), (5, 1, 2)]),
  ([0, 3, 2, 0, 0, 1, 1], 8, [(0, 3, 1), (2, 0, 1), (3, 2, 2), (4, 0, 1), (6, 3, 1), (5, 1, 2)]),
  ([0, 3, 2, 0, 0, 2, 0], 22, [(0, 3, 3), (2, 0, 1), (3, 2, 5), (2, 5, 2), (4, 0, 1), (4, 3, 2), (6, 0, 3), (6, 1, 2), (5, 1, 3)]),
  ([0, 3, 2, 0, 1, 0, 1], 8, [(0, 3, 1), (2, 1, 1), (3, 0, 2), (4, 3, 1), (6, 1, 1), (5, 2, 2)]),
  ([0, 3, 2, 0, 1, 1, 0], 8, [(0, 3, 1), (2, 1, 1), (3, 0, 2), (4, 3, 1), (6, 1, 1), (5, 2, 2)]),
  ([0, 3, 2, 0, 2, 0, 0], 16, [(0, 3, 3), (2, 0, 3), (3, 2, 1), (4, 1, 3), (6, 2, 2), (6, 5, 1), (5, 4, 2), (5, 5, 1)]),
  ([0, 3, 2, 1, 0, 0, 1], 22, [(0, 3, 3), (2, 1, 3), (3, 0, 3), (4, 0, 2), (4, 3, 2), (4, 4, 1), (6, 1, 2), (6, 2, 2), (6, 4, 1), (5, 2, 3)]),
  ([0, 3, 2, 1, 0, 1, 0], 22, [(0, 3, 3), (2, 1, 3), (3, 0, 3), (4, 0, 2), (4, 3, 2), (4, 4, 1), (6, 1, 2), (6, 2, 2), (6, 4, 1), (5, 2, 3)]),
  ([0, 3, 2, 1, 1, 0, 0], 22, [(0, 3, 3), (2, 0, 3), (3, 0, 2), (3, 1, 1), (4, 2, 5), (6, 1, 4), (6, 3, 1), (5, 3, 1), (5, 4, 2)]),
  ([0, 3, 2, 2, 0, 0, 0], 14, [(0, 4, 1), (0, 5, 1), (2, 0, 2), (3, 0, 1), (3, 2, 1), (4, 1, 2), (4, 3, 1), (6, 1, 1), (6, 2, 2), (5, 3, 2)]),
  ([0, 3, 3, 0, 0, 0, 1], 20, [(0, 3, 3), (2, 1, 3), (3, 0, 4), (4, 3, 1), (4, 4, 2), (6, 1, 1), (6, 4, 2), (5, 2, 4)]),
  ([0, 3, 3, 0, 0, 1, 0], 20, [(0, 3, 3), (2, 1, 3), (3, 0, 4), (4, 3, 1), (4, 4, 2), (6, 1, 1), (6, 4, 2), (5, 2, 4)]),
  ([0, 3, 3, 0, 1, 0, 0], 20, [(0, 3, 3), (2, 1, 3), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (4, 0, 3), (6, 2, 3), (5, 4, 4)]),
  ([0, 3, 3, 1, 0, 0, 0], 26, [(0, 4, 4), (2, 0, 4), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 4, 1), (4, 2, 4), (4, 3, 1), (6, 1, 4), (6, 5, 1), (5, 3, 4)]),
  ([0, 3, 4, 0, 0, 0, 0], 6, [(0, 3, 1), (2, 1, 1), (3, 2, 1), (4, 5, 1), (6, 4, 1), (5, 0, 1)])
]
theorem chunk_022_checked : chunk_022.all checkCertificate = true := by
  decide

def chunk_023 : List Certificate := [
  ([0, 4, 0, 0, 0, 0, 3], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 0, 0, 1, 2], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 0, 0, 2, 1], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 0, 0, 3, 0], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 0, 1, 0, 2], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 0, 1, 1, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 0, 1, 2, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 0, 2, 0, 1], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 0, 2, 1, 0], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 0, 3, 0, 0], 3, [(2, 2, 1), (4, 0, 1), (6, 1, 1)]),
  ([0, 4, 0, 1, 0, 0, 2], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 1, 0, 1, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 1, 0, 2, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 1, 1, 0, 1], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 0, 1, 1, 1, 0], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 0, 1, 2, 0, 0], 3, [(2, 2, 1), (4, 0, 1), (6, 1, 1)]),
  ([0, 4, 0, 2, 0, 0, 1], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 0, 2, 0, 1, 0], 3, [(2, 2, 1), (4, 0, 1), (6, 1, 1)]),
  ([0, 4, 0, 2, 1, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 0, 3, 0, 0, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 1, 0, 0, 0, 2], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 1, 0, 0, 1, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 1, 0, 0, 2, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 1, 0, 1, 0, 1], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 4, 1, 0, 1, 1, 0], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 4, 1, 0, 2, 0, 0], 3, [(2, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 4, 1, 1, 0, 0, 1], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 1, 1, 0, 1, 0], 3, [(2, 2, 1), (4, 0, 1), (6, 1, 1)]),
  ([0, 4, 1, 1, 1, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 1, 2, 0, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 2, 0, 0, 0, 1], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 2, 0, 0, 1, 0], 3, [(2, 2, 1), (4, 1, 1), (6, 0, 1)])
]
theorem chunk_023_checked : chunk_023.all checkCertificate = true := by
  decide

def chunk_024 : List Certificate := [
  ([0, 4, 2, 0, 1, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 2, 1, 0, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 0, 1)]),
  ([0, 4, 3, 0, 0, 0, 0], 6, [(0, 4, 1), (2, 1, 1), (3, 2, 1), (4, 3, 1), (6, 5, 1), (5, 0, 1)]),
  ([0, 5, 0, 0, 0, 0, 2], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 5, 0, 0, 0, 1, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 5, 0, 0, 0, 2, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 5, 0, 0, 1, 0, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 5, 0, 0, 1, 1, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 3, 1)]),
  ([0, 5, 0, 0, 2, 0, 0], 9, [(2, 0, 2), (2, 1, 1), (0, 5, 1), (4, 1, 1), (4, 3, 1), (6, 2, 1), (6, 3, 1), (5, 2, 1)]),
  ([0, 5, 0, 1, 0, 0, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 5, 0, 1, 0, 1, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 5, 0, 1, 1, 0, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 5, 0, 2, 0, 0, 0], 3, [(2, 0, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 5, 1, 0, 0, 0, 1], 3, [(2, 0, 1), (4, 2, 1), (6, 1, 1)]),
  ([0, 5, 1, 0, 0, 1, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 5, 1, 0, 1, 0, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 5, 1, 1, 0, 0, 0], 3, [(2, 0, 1), (4, 3, 1), (6, 1, 1)]),
  ([0, 5, 2, 0, 0, 0, 0], 6, [(0, 5, 1), (2, 3, 1), (3, 2, 1), (4, 4, 1), (6, 1, 1), (5, 0, 1)]),
  ([0, 6, 0, 0, 0, 0, 1], 3, [(2, 4, 1), (4, 3, 1), (6, 0, 1)]),
  ([0, 6, 0, 0, 0, 1, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 6, 0, 0, 1, 0, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 6, 0, 1, 0, 0, 0], 3, [(2, 2, 1), (4, 1, 1), (6, 0, 1)]),
  ([0, 6, 1, 0, 0, 0, 0], 3, [(2, 0, 1), (4, 1, 1), (6, 2, 1)]),
  ([0, 7, 0, 0, 0, 0, 0], 3, [(2, 5, 1), (4, 0, 1), (6, 1, 1)]),
  ([1, 0, 0, 0, 0, 0, 6], 3, [(4, 1, 1), (0, 2, 1), (2, 3, 1)]),
  ([1, 0, 0, 0, 0, 1, 5], 3, [(4, 2, 1), (2, 3, 1), (0, 5, 1)]),
  ([1, 0, 0, 0, 0, 2, 4], 3, [(4, 3, 1), (2, 4, 1), (0, 5, 1)]),
  ([1, 0, 0, 0, 0, 3, 3], 26, [(0, 1, 3), (3, 1, 2), (0, 2, 1), (1, 3, 5), (2, 4, 4), (3, 4, 1), (3, 5, 2), (4, 5, 3), (4, 6, 1), (6, 2, 4)]),
  ([1, 0, 0, 0, 0, 4, 2], 3, [(1, 2, 1), (3, 3, 1), (6, 1, 1)]),
  ([1, 0, 0, 0, 0, 5, 1], 3, [(1, 1, 1), (3, 3, 1), (6, 2, 1)]),
  ([1, 0, 0, 0, 0, 6, 0], 3, [(3, 2, 1), (1, 3, 1), (6, 1, 1)]),
  ([1, 0, 0, 0, 1, 0, 5], 3, [(4, 2, 1), (2, 3, 1), (0, 4, 1)])
]
theorem chunk_024_checked : chunk_024.all checkCertificate = true := by
  decide

def chunk_025 : List Certificate := [
  ([1, 0, 0, 0, 1, 1, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([1, 0, 0, 0, 1, 2, 3], 22, [(1, 2, 3), (3, 2, 1), (2, 3, 5), (0, 4, 5), (3, 5, 2), (4, 5, 3), (6, 1, 2), (6, 2, 1)]),
  ([1, 0, 0, 0, 1, 3, 2], 11, [(1, 1, 1), (0, 2, 1), (1, 3, 2), (3, 3, 2), (2, 4, 1), (3, 5, 1), (6, 2, 3)]),
  ([1, 0, 0, 0, 1, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([1, 0, 0, 0, 1, 5, 0], 3, [(3, 2, 1), (1, 5, 1), (6, 3, 1)]),
  ([1, 0, 0, 0, 2, 0, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([1, 0, 0, 0, 2, 1, 3], 11, [(0, 1, 1), (0, 2, 1), (2, 3, 1), (0, 4, 2), (2, 4, 2), (2, 5, 1), (4, 5, 3)]),
  ([1, 0, 0, 0, 2, 2, 2], 35, [(0, 1, 1), (2, 1, 3), (0, 2, 4), (1, 2, 3), (0, 3, 4), (2, 4, 7), (0, 5, 1), (3, 5, 3), (4, 5, 3), (6, 3, 3), (5, 1, 3)]),
  ([1, 0, 0, 0, 2, 3, 1], 11, [(0, 1, 1), (1, 2, 1), (1, 3, 2), (3, 3, 2), (3, 4, 1), (2, 5, 1), (6, 4, 3)]),
  ([1, 0, 0, 0, 2, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([1, 0, 0, 0, 3, 0, 3], 11, [(0, 1, 3), (2, 2, 1), (2, 3, 1), (2, 4, 2), (0, 5, 1), (4, 5, 1), (5, 2, 2)]),
  ([1, 0, 0, 0, 3, 1, 2], 11, [(0, 1, 1), (0, 2, 2), (2, 2, 2), (2, 3, 1), (0, 4, 1), (2, 5, 1), (5, 1, 3)]),
  ([1, 0, 0, 0, 3, 2, 1], 11, [(0, 1, 3), (2, 3, 2), (2, 4, 1), (3, 4, 1), (1, 5, 1), (6, 2, 1), (5, 2, 2)]),
  ([1, 0, 0, 0, 3, 3, 0], 20, [(0, 1, 1), (1, 2, 1), (2, 3, 4), (0, 4, 1), (3, 4, 3), (0, 5, 2), (1, 5, 2), (6, 1, 3), (5, 2, 3)]),
  ([1, 0, 0, 0, 4, 0, 2], 3, [(0, 2, 1), (2, 3, 1), (5, 1, 1)]),
  ([1, 0, 0, 0, 4, 1, 1], 3, [(0, 2, 1), (2, 3, 1), (5, 1, 1)]),
  ([1, 0, 0, 0, 4, 2, 0], 3, [(0, 2, 1), (2, 3, 1), (5, 1, 1)]),
  ([1, 0, 0, 0, 5, 0, 1], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([1, 0, 0, 0, 5, 1, 0], 3, [(0, 1, 1), (2, 3, 1), (5, 2, 1)]),
  ([1, 0, 0, 0, 6, 0, 0], 3, [(0, 1, 1), (2, 2, 1), (5, 5, 1)]),
  ([1, 0, 0, 1, 0, 0, 5], 3, [(4, 2, 1), (2, 3, 1), (0, 4, 1)]),
  ([1, 0, 0, 1, 0, 1, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([1, 0, 0, 1, 0, 2, 3], 22, [(0, 2, 2), (1, 3, 5), (0, 4, 1), (2, 4, 3), (4, 4, 1), (3, 5, 3), (4, 5, 2), (3, 6, 2), (6, 2, 3)]),
  ([1, 0, 0, 1, 0, 3, 2], 11, [(3, 2, 1), (1, 3, 2), (3, 3, 2), (1, 4, 1), (3, 5, 1), (1, 6, 1), (6, 2, 3)]),
  ([1, 0, 0, 1, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([1, 0, 0, 1, 0, 5, 0], 3, [(3, 2, 1), (1, 3, 1), (6, 4, 1)]),
  ([1, 0, 0, 1, 1, 0, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([1, 0, 0, 1, 1, 1, 3], 8, [(1, 3, 1), (0, 4, 2), (2, 4, 1), (3, 5, 1), (4, 5, 2), (2, 6, 1)]),
  ([1, 0, 0, 1, 1, 2, 2], 18, [(2, 2, 3), (0, 3, 2), (3, 3, 1), (1, 4, 2), (2, 4, 2), (3, 4, 1), (0, 5, 3), (4, 5, 2), (6, 3, 2)]),
  ([1, 0, 0, 1, 1, 3, 1], 8, [(2, 2, 1), (1, 3, 1), (3, 3, 2), (1, 4, 1), (0, 5, 1), (6, 4, 2)]),
  ([1, 0, 0, 1, 1, 4, 0], 3, [(1, 3, 1), (3, 4, 1), (6, 5, 1)]),
  ([1, 0, 0, 1, 2, 0, 3], 16, [(0, 1, 1), (1, 2, 1), (2, 3, 1), (0, 4, 1), (4, 4, 5), (0, 5, 3), (2, 5, 3), (2, 6, 1)])
]
theorem chunk_025_checked : chunk_025.all checkCertificate = true := by
  decide

def chunk_026 : List Certificate := [
  ([1, 0, 0, 1, 2, 1, 2], 28, [(1, 2, 1), (2, 2, 4), (0, 3, 5), (0, 4, 4), (1, 4, 1), (3, 4, 2), (2, 5, 5), (4, 5, 2), (6, 3, 2), (5, 2, 2)]),
  ([1, 0, 0, 1, 2, 2, 1], 18, [(0, 1, 2), (2, 2, 3), (0, 3, 1), (1, 3, 4), (3, 4, 1), (3, 5, 1), (6, 4, 4), (5, 2, 2)]),
  ([1, 0, 0, 1, 2, 3, 0], 22, [(0, 1, 2), (1, 2, 2), (1, 3, 2), (2, 3, 3), (0, 4, 1), (1, 4, 1), (3, 4, 3), (6, 5, 5), (5, 2, 3)]),
  ([1, 0, 0, 1, 3, 0, 2], 16, [(0, 2, 5), (2, 3, 3), (1, 4, 1), (2, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1), (5, 3, 3)]),
  ([1, 0, 0, 1, 3, 1, 1], 16, [(0, 2, 5), (2, 3, 3), (1, 4, 1), (2, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1), (5, 3, 3)]),
  ([1, 0, 0, 1, 3, 2, 0], 22, [(0, 2, 1), (2, 2, 3), (1, 4, 5), (0, 5, 2), (3, 5, 3), (6, 3, 5), (5, 1, 2), (5, 2, 1)]),
  ([1, 0, 0, 1, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([1, 0, 0, 1, 4, 1, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([1, 0, 0, 1, 5, 0, 0], 3, [(0, 2, 1), (2, 4, 1), (5, 5, 1)]),
  ([1, 0, 0, 2, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([1, 0, 0, 2, 0, 1, 3], 8, [(4, 1, 1), (0, 4, 2), (4, 4, 1), (1, 5, 1), (2, 5, 2), (4, 6, 1)]),
  ([1, 0, 0, 2, 0, 2, 2], 18, [(2, 3, 2), (3, 3, 1), (1, 4, 1), (3, 4, 4), (0, 5, 2), (1, 5, 1), (4, 5, 2), (1, 6, 3), (6, 3, 2)]),
  ([1, 0, 0, 2, 0, 3, 1], 8, [(1, 3, 3), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 2)]),
  ([1, 0, 0, 2, 0, 4, 0], 3, [(1, 3, 1), (3, 4, 1), (6, 5, 1)]),
  ([1, 0, 0, 2, 1, 0, 3], 8, [(1, 1, 1), (0, 4, 2), (2, 4, 1), (4, 5, 3), (2, 6, 1)]),
  ([1, 0, 0, 2, 1, 1, 2], 5, [(2, 3, 1), (4, 1, 1), (1, 4, 1), (0, 5, 1), (6, 2, 1)]),
  ([1, 0, 0, 2, 1, 2, 1], 28, [(1, 1, 3), (1, 3, 3), (2, 3, 2), (0, 4, 2), (1, 4, 3), (3, 4, 2), (4, 1, 2), (6, 2, 7), (6, 3, 2), (5, 1, 2)]),
  ([1, 0, 0, 2, 1, 3, 0], 11, [(1, 1, 1), (1, 3, 1), (3, 4, 1), (1, 5, 2), (3, 5, 2), (6, 2, 1), (6, 4, 3)]),
  ([1, 0, 0, 2, 2, 0, 2], 33, [(1, 1, 3), (0, 2, 5), (1, 3, 4), (2, 3, 2), (2, 4, 3), (1, 5, 1), (4, 5, 2), (4, 6, 3), (6, 2, 3), (6, 3, 2), (5, 1, 5)]),
  ([1, 0, 0, 2, 2, 1, 1], 18, [(0, 2, 2), (1, 2, 2), (1, 3, 3), (2, 3, 2), (4, 1, 2), (6, 1, 1), (6, 2, 1), (6, 4, 3), (5, 1, 2)]),
  ([1, 0, 0, 2, 2, 2, 0], 35, [(0, 2, 3), (1, 2, 4), (1, 4, 6), (2, 5, 3), (3, 5, 3), (4, 1, 3), (6, 1, 1), (6, 3, 7), (6, 4, 1), (6, 5, 1), (5, 1, 3)]),
  ([1, 0, 0, 2, 3, 0, 1], 8, [(0, 1, 1), (2, 3, 1), (0, 4, 1), (1, 4, 1), (4, 1, 1), (6, 3, 1), (5, 2, 2)]),
  ([1, 0, 0, 2, 3, 1, 0], 22, [(0, 1, 2), (2, 3, 2), (0, 4, 1), (1, 4, 4), (1, 5, 1), (2, 5, 1), (4, 1, 3), (6, 2, 2), (6, 3, 3), (5, 2, 3)]),
  ([1, 0, 0, 2, 4, 0, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 5, 1)]),
  ([1, 0, 0, 3, 0, 0, 3], 11, [(1, 1, 1), (0, 2, 1), (0, 4, 2), (4, 4, 2), (2, 5, 3), (4, 5, 1), (4, 6, 1)]),
  ([1, 0, 0, 3, 0, 1, 2], 16, [(1, 1, 3), (1, 3, 1), (4, 2, 4), (1, 4, 1), (1, 5, 1), (4, 6, 1), (6, 1, 3), (6, 2, 2)]),
  ([1, 0, 0, 3, 0, 2, 1], 8, [(1, 1, 2), (1, 4, 1), (4, 2, 2), (6, 1, 1), (6, 2, 1), (6, 3, 1)]),
  ([1, 0, 0, 3, 0, 3, 0], 11, [(1, 1, 3), (1, 3, 1), (4, 2, 3), (6, 1, 1), (6, 2, 1), (6, 4, 1), (6, 5, 1)]),
  ([1, 0, 0, 3, 1, 0, 2], 16, [(1, 1, 2), (1, 3, 1), (4, 1, 4), (4, 2, 1), (1, 4, 1), (1, 5, 1), (1, 6, 1), (6, 2, 5)]),
  ([1, 0, 0, 3, 1, 1, 1], 16, [(1, 1, 1), (1, 2, 2), (1, 3, 1), (1, 4, 1), (4, 2, 4), (1, 5, 1), (4, 6, 1), (6, 1, 5)]),
  ([1, 0, 0, 3, 1, 2, 0], 11, [(1, 2, 4), (4, 1, 3), (6, 1, 1), (6, 3, 1), (6, 4, 1), (6, 5, 1)]),
  ([1, 0, 0, 3, 2, 0, 1], 24, [(0, 1, 5), (1, 3, 1), (1, 4, 3), (2, 4, 2), (4, 1, 2), (4, 2, 2), (6, 3, 4), (5, 2, 5)])
]
theorem chunk_026_checked : chunk_026.all checkCertificate = true := by
  decide

def chunk_027 : List Certificate := [
  ([1, 0, 0, 3, 2, 1, 0], 22, [(0, 1, 3), (1, 3, 1), (1, 4, 2), (2, 4, 3), (1, 5, 2), (4, 1, 2), (4, 2, 1), (6, 2, 1), (6, 3, 4), (5, 2, 3)]),
  ([1, 0, 0, 3, 3, 0, 0], 20, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (1, 3, 3), (1, 4, 1), (2, 4, 3), (4, 1, 3), (6, 2, 3), (5, 5, 4)]),
  ([1, 0, 0, 4, 0, 0, 2], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([1, 0, 0, 4, 0, 1, 1], 3, [(1, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 0, 0, 4, 0, 2, 0], 3, [(1, 2, 1), (4, 1, 1), (6, 3, 1)]),
  ([1, 0, 0, 4, 1, 0, 1], 3, [(1, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 0, 0, 4, 1, 1, 0], 3, [(1, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([1, 0, 0, 4, 2, 0, 0], 3, [(1, 1, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 0, 0, 5, 0, 0, 1], 3, [(1, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 0, 0, 5, 0, 1, 0], 3, [(1, 4, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 0, 0, 5, 1, 0, 0], 3, [(1, 4, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 0, 0, 6, 0, 0, 0], 3, [(1, 4, 1), (4, 5, 1), (6, 2, 1)]),
  ([1, 0, 1, 0, 0, 0, 5], 3, [(0, 2, 1), (4, 3, 1), (2, 4, 1)]),
  ([1, 0, 1, 0, 0, 1, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([1, 0, 1, 0, 0, 2, 3], 22, [(3, 2, 2), (1, 3, 5), (0, 4, 2), (4, 4, 3), (0, 5, 1), (2, 5, 3), (3, 5, 1), (3, 6, 2), (6, 2, 3)]),
  ([1, 0, 1, 0, 0, 3, 2], 22, [(0, 2, 1), (2, 2, 1), (1, 3, 7), (3, 4, 3), (3, 5, 3), (3, 6, 1), (4, 6, 1), (6, 2, 5)]),
  ([1, 0, 1, 0, 0, 4, 1], 3, [(3, 2, 1), (1, 4, 1), (6, 3, 1)]),
  ([1, 0, 1, 0, 0, 5, 0], 3, [(3, 2, 1), (1, 3, 1), (6, 5, 1)]),
  ([1, 0, 1, 0, 1, 0, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([1, 0, 1, 0, 1, 1, 3], 8, [(0, 3, 1), (0, 4, 1), (1, 4, 1), (2, 4, 1), (3, 5, 1), (4, 5, 2), (2, 6, 1)]),
  ([1, 0, 1, 0, 1, 2, 2], 18, [(2, 2, 3), (0, 3, 2), (1, 3, 1), (1, 4, 1), (2, 4, 2), (3, 4, 2), (0, 5, 3), (4, 5, 2), (6, 3, 2)]),
  ([1, 0, 1, 0, 1, 3, 1], 8, [(1, 3, 2), (3, 3, 1), (1, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 2)]),
  ([1, 0, 1, 0, 1, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([1, 0, 1, 0, 2, 0, 3], 8, [(2, 2, 1), (2, 3, 1), (0, 4, 3), (2, 5, 1), (4, 5, 2)]),
  ([1, 0, 1, 0, 2, 1, 2], 28, [(0, 2, 3), (0, 3, 5), (1, 3, 2), (0, 4, 1), (2, 4, 4), (3, 4, 2), (2, 5, 5), (4, 5, 2), (6, 2, 2), (5, 2, 2)]),
  ([1, 0, 1, 0, 2, 2, 1], 18, [(2, 2, 2), (1, 3, 2), (2, 3, 3), (0, 4, 2), (3, 4, 2), (0, 5, 3), (6, 2, 1), (6, 4, 1), (5, 2, 2)]),
  ([1, 0, 1, 0, 2, 3, 0], 8, [(2, 3, 2), (1, 4, 1), (3, 4, 1), (0, 5, 2), (6, 2, 1), (5, 2, 1)]),
  ([1, 0, 1, 0, 3, 0, 2], 8, [(0, 2, 3), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 3, 2)]),
  ([1, 0, 1, 0, 3, 1, 1], 8, [(0, 2, 3), (2, 3, 1), (2, 4, 1), (2, 5, 1), (5, 3, 2)]),
  ([1, 0, 1, 0, 3, 2, 0], 8, [(0, 2, 2), (2, 3, 1), (1, 4, 1), (2, 5, 1), (6, 3, 1), (5, 2, 1), (5, 3, 1)]),
  ([1, 0, 1, 0, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([1, 0, 1, 0, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)])
]
theorem chunk_027_checked : chunk_027.all checkCertificate = true := by
  decide

def chunk_028 : List Certificate := [
  ([1, 0, 1, 0, 5, 0, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 5, 1)]),
  ([1, 0, 1, 1, 0, 0, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([1, 0, 1, 1, 0, 1, 3], 8, [(0, 3, 1), (1, 4, 1), (2, 4, 1), (4, 4, 1), (0, 5, 1), (3, 5, 1), (4, 5, 1), (2, 6, 1)]),
  ([1, 0, 1, 1, 0, 2, 2], 18, [(1, 3, 1), (2, 3, 2), (1, 4, 1), (3, 4, 4), (0, 5, 2), (3, 5, 1), (4, 5, 2), (1, 6, 3), (6, 3, 2)]),
  ([1, 0, 1, 1, 0, 3, 1], 8, [(1, 3, 3), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 2)]),
  ([1, 0, 1, 1, 0, 4, 0], 3, [(1, 3, 1), (3, 4, 1), (6, 5, 1)]),
  ([1, 0, 1, 1, 1, 0, 3], 21, [(0, 1, 1), (0, 2, 1), (4, 0, 1), (2, 3, 1), (0, 4, 5), (2, 4, 3), (2, 5, 2), (4, 5, 6), (2, 6, 1)]),
  ([1, 0, 1, 1, 1, 1, 2], 7, [(1, 2, 1), (2, 3, 1), (3, 4, 1), (0, 5, 1), (4, 6, 1), (6, 1, 1), (5, 0, 1)]),
  ([1, 0, 1, 1, 1, 2, 1], 7, [(1, 2, 1), (2, 3, 1), (3, 4, 1), (0, 5, 1), (4, 6, 1), (6, 1, 1), (5, 0, 1)]),
  ([1, 0, 1, 1, 1, 3, 0], 8, [(1, 2, 1), (1, 3, 1), (1, 4, 1), (3, 5, 2), (6, 4, 2), (6, 5, 1)]),
  ([1, 0, 1, 1, 2, 0, 2], 21, [(0, 2, 6), (0, 3, 1), (1, 3, 1), (2, 3, 2), (4, 0, 1), (4, 5, 1), (3, 6, 1), (6, 3, 1), (5, 1, 6), (5, 3, 1)]),
  ([1, 0, 1, 1, 2, 1, 1], 49, [(0, 2, 15), (0, 3, 2), (1, 3, 3), (2, 3, 3), (3, 0, 1), (4, 1, 3), (3, 5, 1), (3, 6, 1), (6, 3, 2), (6, 4, 1), (5, 1, 12), (5, 3, 5)]),
  ([1, 0, 1, 1, 2, 2, 0], 18, [(0, 2, 2), (1, 2, 1), (1, 3, 1), (1, 4, 3), (2, 4, 2), (3, 5, 2), (6, 3, 2), (6, 5, 3), (5, 3, 2)]),
  ([1, 0, 1, 1, 3, 0, 1], 8, [(0, 1, 1), (0, 3, 1), (2, 3, 2), (0, 4, 1), (5, 2, 1), (5, 4, 2)]),
  ([1, 0, 1, 1, 3, 1, 0], 8, [(0, 1, 1), (0, 3, 1), (2, 3, 2), (0, 4, 1), (5, 2, 1), (5, 4, 2)]),
  ([1, 0, 1, 1, 4, 0, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 5, 1)]),
  ([1, 0, 1, 2, 0, 0, 3], 16, [(4, 0, 1), (4, 1, 1), (4, 2, 1), (0, 4, 1), (2, 4, 5), (0, 5, 4), (4, 5, 2), (4, 6, 1)]),
  ([1, 0, 1, 2, 0, 1, 2], 7, [(0, 1, 1), (1, 2, 1), (3, 4, 1), (4, 5, 1), (2, 6, 1), (6, 3, 1), (5, 0, 1)]),
  ([1, 0, 1, 2, 0, 2, 1], 14, [(0, 1, 1), (1, 2, 3), (2, 4, 1), (3, 4, 2), (1, 5, 1), (4, 6, 1), (6, 3, 3), (6, 4, 1), (5, 0, 1)]),
  ([1, 0, 1, 2, 0, 3, 0], 8, [(1, 4, 3), (3, 5, 2), (6, 2, 1), (6, 3, 1), (6, 5, 1)]),
  ([1, 0, 1, 2, 1, 0, 2], 7, [(0, 2, 2), (1, 3, 1), (4, 2, 1), (6, 3, 1), (5, 1, 2)]),
  ([1, 0, 1, 2, 1, 1, 1], 21, [(0, 2, 5), (1, 3, 3), (3, 0, 1), (2, 4, 1), (3, 5, 2), (4, 6, 2), (6, 3, 1), (6, 4, 1), (5, 1, 5)]),
  ([1, 0, 1, 2, 1, 2, 0], 28, [(0, 2, 2), (1, 2, 3), (1, 3, 1), (1, 4, 5), (2, 4, 2), (3, 5, 2), (4, 2, 2), (6, 3, 4), (6, 5, 5), (5, 3, 2)]),
  ([1, 0, 1, 2, 2, 0, 1], 18, [(0, 1, 3), (0, 3, 2), (1, 3, 1), (1, 4, 1), (2, 4, 2), (4, 2, 2), (6, 4, 2), (5, 2, 3), (5, 3, 2)]),
  ([1, 0, 1, 2, 2, 1, 0], 18, [(0, 1, 1), (1, 3, 1), (1, 4, 3), (2, 4, 2), (0, 5, 2), (4, 2, 2), (6, 3, 4), (5, 2, 3)]),
  ([1, 0, 1, 2, 3, 0, 0], 11, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 3), (5, 5, 4)]),
  ([1, 0, 1, 3, 0, 0, 2], 8, [(0, 2, 1), (1, 3, 1), (4, 1, 1), (4, 2, 2), (1, 5, 1), (6, 3, 2)]),
  ([1, 0, 1, 3, 0, 1, 1], 21, [(1, 2, 6), (4, 0, 1), (4, 1, 1), (4, 3, 4), (1, 5, 1), (4, 6, 1), (6, 2, 2), (6, 3, 4), (6, 4, 1)]),
  ([1, 0, 1, 3, 0, 2, 0], 8, [(1, 3, 1), (1, 4, 1), (1, 5, 1), (4, 3, 2), (6, 2, 3)]),
  ([1, 0, 1, 3, 1, 0, 1], 8, [(0, 1, 1), (1, 3, 1), (1, 4, 1), (4, 3, 2), (6, 2, 2), (5, 2, 1)]),
  ([1, 0, 1, 3, 1, 1, 0], 8, [(0, 1, 1), (1, 3, 1), (1, 4, 1), (4, 2, 2), (6, 3, 2), (5, 2, 1)]),
  ([1, 0, 1, 3, 2, 0, 0], 22, [(0, 1, 2), (1, 2, 3), (0, 4, 3), (2, 5, 3), (4, 3, 3), (6, 2, 2), (6, 4, 1), (5, 3, 2), (5, 4, 1), (5, 5, 2)])
]
theorem chunk_028_checked : chunk_028.all checkCertificate = true := by
  decide

def chunk_029 : List Certificate := [
  ([1, 0, 1, 4, 0, 0, 1], 3, [(1, 4, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 0, 1, 4, 0, 1, 0], 3, [(1, 4, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 0, 1, 4, 1, 0, 0], 3, [(1, 4, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 0, 1, 5, 0, 0, 0], 3, [(1, 5, 1), (4, 4, 1), (6, 2, 1)]),
  ([1, 0, 2, 0, 0, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([1, 0, 2, 0, 0, 1, 3], 8, [(0, 3, 1), (0, 4, 1), (3, 4, 1), (4, 4, 1), (1, 5, 1), (2, 5, 2), (4, 6, 1)]),
  ([1, 0, 2, 0, 0, 2, 2], 18, [(3, 1, 2), (1, 3, 3), (2, 4, 2), (3, 4, 3), (0, 5, 4), (4, 5, 1), (4, 6, 1), (6, 3, 2)]),
  ([1, 0, 2, 0, 0, 3, 1], 16, [(3, 0, 1), (3, 1, 1), (1, 3, 5), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 5)]),
  ([1, 0, 2, 0, 0, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([1, 0, 2, 0, 1, 0, 3], 21, [(0, 2, 1), (4, 0, 1), (4, 1, 1), (0, 3, 1), (2, 4, 6), (4, 4, 2), (0, 5, 5), (4, 5, 3), (2, 6, 1)]),
  ([1, 0, 2, 0, 1, 1, 2], 14, [(3, 1, 4), (2, 4, 1), (0, 5, 3), (2, 6, 1), (4, 6, 2), (5, 0, 3)]),
  ([1, 0, 2, 0, 1, 2, 1], 7, [(3, 1, 1), (2, 3, 1), (1, 4, 1), (0, 5, 1), (4, 6, 1), (6, 2, 1), (5, 0, 1)]),
  ([1, 0, 2, 0, 1, 3, 0], 21, [(3, 0, 1), (3, 1, 1), (1, 4, 4), (3, 4, 4), (1, 5, 3), (6, 2, 1), (6, 3, 1), (6, 5, 5), (3, 6, 1)]),
  ([1, 0, 2, 0, 2, 0, 2], 7, [(0, 3, 1), (3, 0, 1), (0, 4, 1), (2, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([1, 0, 2, 0, 2, 1, 1], 7, [(0, 3, 1), (3, 0, 1), (2, 4, 1), (0, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([1, 0, 2, 0, 2, 2, 0], 5, [(1, 3, 1), (3, 1, 1), (0, 5, 1), (6, 4, 1), (5, 2, 1)]),
  ([1, 0, 2, 0, 3, 0, 1], 8, [(0, 1, 1), (0, 3, 2), (2, 3, 1), (2, 4, 1), (5, 2, 1), (5, 4, 2)]),
  ([1, 0, 2, 0, 3, 1, 0], 8, [(0, 1, 1), (0, 3, 1), (2, 3, 2), (0, 4, 1), (5, 2, 1), (5, 4, 2)]),
  ([1, 0, 2, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 5, 1)]),
  ([1, 0, 2, 1, 0, 0, 3], 8, [(4, 1, 1), (4, 2, 1), (2, 4, 2), (4, 4, 1), (0, 5, 3)]),
  ([1, 0, 2, 1, 0, 1, 2], 14, [(3, 1, 4), (2, 4, 1), (0, 5, 3), (2, 6, 1), (4, 6, 2), (5, 0, 3)]),
  ([1, 0, 2, 1, 0, 2, 1], 28, [(3, 1, 8), (1, 4, 1), (3, 4, 2), (0, 5, 5), (1, 6, 1), (2, 6, 2), (4, 6, 2), (6, 4, 2), (5, 0, 5)]),
  ([1, 0, 2, 1, 0, 3, 0], 21, [(3, 0, 1), (3, 1, 1), (3, 4, 4), (1, 5, 7), (6, 2, 1), (6, 3, 1), (6, 4, 4), (6, 5, 1), (3, 6, 1)]),
  ([1, 0, 2, 1, 1, 0, 2], 7, [(0, 1, 1), (0, 2, 1), (3, 0, 1), (3, 5, 1), (4, 6, 1), (5, 1, 2)]),
  ([1, 0, 2, 1, 1, 1, 1], 28, [(0, 1, 2), (0, 2, 2), (0, 3, 2), (3, 0, 3), (0, 4, 2), (2, 4, 1), (4, 2, 1), (3, 5, 3), (1, 6, 1), (3, 6, 2), (6, 3, 1), (5, 1, 8)]),
  ([1, 0, 2, 1, 1, 2, 0], 5, [(0, 2, 1), (1, 3, 1), (3, 5, 1), (6, 4, 1), (5, 1, 1)]),
  ([1, 0, 2, 1, 2, 0, 1], 28, [(0, 1, 3), (0, 3, 3), (1, 3, 2), (0, 4, 3), (2, 4, 2), (3, 1, 2), (4, 1, 2), (6, 3, 2), (5, 2, 7), (5, 4, 2)]),
  ([1, 0, 2, 1, 2, 1, 0], 28, [(0, 1, 5), (0, 3, 4), (1, 3, 2), (2, 4, 2), (3, 1, 2), (4, 2, 2), (6, 3, 1), (6, 4, 1), (5, 2, 5), (5, 4, 4)]),
  ([1, 0, 2, 1, 3, 0, 0], 11, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 3), (5, 5, 4)]),
  ([1, 0, 2, 2, 0, 0, 2], 18, [(0, 3, 2), (1, 3, 2), (3, 1, 2), (4, 2, 5), (0, 5, 3), (6, 1, 1), (6, 3, 1), (5, 1, 2)]),
  ([1, 0, 2, 2, 0, 1, 1], 42, [(0, 2, 3), (0, 3, 4), (1, 3, 2), (3, 0, 3), (1, 4, 3), (4, 2, 7), (3, 5, 3), (1, 6, 2), (3, 6, 1), (6, 1, 3), (6, 3, 4), (5, 1, 7)]),
  ([1, 0, 2, 2, 0, 2, 0], 5, [(0, 2, 1), (1, 3, 1), (3, 5, 1), (6, 4, 1), (5, 1, 1)])
]
theorem chunk_029_checked : chunk_029.all checkCertificate = true := by
  decide

def chunk_030 : List Certificate := [
  ([1, 0, 2, 2, 1, 0, 1], 18, [(0, 1, 3), (0, 3, 1), (0, 4, 1), (1, 4, 2), (3, 1, 2), (4, 3, 2), (6, 3, 2), (5, 2, 5)]),
  ([1, 0, 2, 2, 1, 1, 0], 18, [(0, 1, 3), (1, 3, 1), (0, 4, 2), (1, 4, 1), (3, 1, 2), (4, 3, 2), (6, 3, 2), (5, 2, 5)]),
  ([1, 0, 2, 2, 2, 0, 0], 35, [(0, 1, 4), (0, 2, 5), (0, 3, 1), (1, 3, 3), (2, 5, 3), (3, 1, 3), (4, 3, 3), (6, 4, 3), (5, 2, 2), (5, 4, 4), (5, 5, 4)]),
  ([1, 0, 2, 3, 0, 0, 1], 8, [(0, 1, 1), (0, 3, 1), (1, 4, 1), (3, 1, 1), (4, 4, 1), (6, 3, 1), (5, 2, 2)]),
  ([1, 0, 2, 3, 0, 1, 0], 8, [(0, 1, 1), (0, 4, 1), (1, 4, 1), (3, 1, 1), (4, 3, 1), (6, 3, 1), (5, 2, 2)]),
  ([1, 0, 2, 3, 1, 0, 0], 22, [(0, 1, 2), (1, 3, 3), (0, 4, 3), (3, 1, 3), (4, 2, 3), (6, 2, 2), (6, 4, 1), (5, 3, 2), (5, 4, 1), (5, 5, 2)]),
  ([1, 0, 2, 4, 0, 0, 0], 3, [(1, 5, 1), (4, 4, 1), (6, 3, 1)]),
  ([1, 0, 3, 0, 0, 0, 3], 8, [(0, 1, 1), (3, 2, 2), (0, 4, 1), (2, 5, 1), (4, 6, 1), (5, 0, 1), (5, 1, 1)]),
  ([1, 0, 3, 0, 0, 1, 2], 16, [(0, 1, 3), (3, 2, 5), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 3), (5, 2, 1)]),
  ([1, 0, 3, 0, 0, 2, 1], 16, [(0, 1, 3), (3, 2, 5), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 3), (5, 2, 1)]),
  ([1, 0, 3, 0, 0, 3, 0], 16, [(0, 1, 3), (3, 2, 5), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 3), (5, 2, 1)]),
  ([1, 0, 3, 0, 1, 0, 2], 21, [(0, 1, 2), (0, 2, 2), (0, 3, 1), (3, 2, 6), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 6)]),
  ([1, 0, 3, 0, 1, 1, 1], 21, [(0, 1, 2), (0, 2, 2), (0, 3, 1), (3, 2, 6), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 6)]),
  ([1, 0, 3, 0, 1, 2, 0], 21, [(0, 1, 2), (0, 2, 2), (0, 3, 1), (3, 2, 6), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 6)]),
  ([1, 0, 3, 0, 2, 0, 1], 8, [(0, 1, 1), (0, 3, 1), (0, 4, 1), (3, 1, 2), (5, 2, 3)]),
  ([1, 0, 3, 0, 2, 1, 0], 8, [(0, 1, 1), (0, 3, 1), (0, 4, 1), (3, 1, 2), (5, 2, 3)]),
  ([1, 0, 3, 0, 3, 0, 0], 11, [(0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 3), (5, 5, 4)]),
  ([1, 0, 3, 1, 0, 0, 2], 24, [(0, 1, 2), (0, 2, 2), (0, 3, 2), (3, 2, 7), (4, 0, 1), (0, 5, 2), (4, 6, 1), (5, 1, 7)]),
  ([1, 0, 3, 1, 0, 1, 1], 21, [(0, 1, 4), (0, 3, 1), (3, 2, 6), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 4), (5, 2, 2)]),
  ([1, 0, 3, 1, 0, 2, 0], 21, [(0, 1, 2), (0, 2, 2), (0, 3, 1), (3, 2, 6), (0, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 6)]),
  ([1, 0, 3, 1, 1, 0, 1], 8, [(0, 1, 2), (0, 3, 1), (3, 1, 1), (3, 2, 1), (5, 2, 2), (5, 4, 1)]),
  ([1, 0, 3, 1, 1, 1, 0], 8, [(0, 1, 2), (0, 3, 1), (3, 1, 1), (3, 2, 1), (5, 2, 2), (5, 4, 1)]),
  ([1, 0, 3, 1, 2, 0, 0], 11, [(0, 1, 4), (3, 2, 3), (5, 2, 1), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([1, 0, 3, 2, 0, 0, 1], 16, [(0, 1, 4), (0, 4, 1), (3, 0, 1), (3, 1, 2), (3, 2, 1), (4, 3, 1), (3, 6, 1), (5, 2, 5)]),
  ([1, 0, 3, 2, 0, 1, 0], 8, [(0, 1, 2), (3, 1, 1), (3, 2, 1), (4, 3, 1), (6, 4, 1), (5, 2, 2)]),
  ([1, 0, 3, 2, 1, 0, 0], 11, [(0, 1, 4), (3, 2, 3), (5, 2, 1), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([1, 0, 3, 3, 0, 0, 0], 20, [(0, 1, 4), (1, 5, 3), (3, 2, 3), (4, 2, 1), (4, 3, 1), (4, 5, 1), (6, 3, 3), (5, 4, 4)]),
  ([1, 0, 4, 0, 0, 0, 2], 3, [(0, 3, 1), (3, 2, 1), (5, 1, 1)]),
  ([1, 0, 4, 0, 0, 1, 1], 3, [(0, 3, 1), (3, 2, 1), (5, 1, 1)]),
  ([1, 0, 4, 0, 0, 2, 0], 3, [(0, 3, 1), (3, 2, 1), (5, 1, 1)]),
  ([1, 0, 4, 0, 1, 0, 1], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 4, 0, 1, 1, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)])
]
theorem chunk_030_checked : chunk_030.all checkCertificate = true := by
  decide

def chunk_031 : List Certificate := [
  ([1, 0, 4, 0, 2, 0, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 4, 1, 0, 0, 1], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 4, 1, 0, 1, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 4, 1, 1, 0, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 4, 2, 0, 0, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 5, 0, 0, 0, 1], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 5, 0, 0, 1, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 5, 0, 1, 0, 0], 3, [(0, 1, 1), (3, 3, 1), (5, 2, 1)]),
  ([1, 0, 5, 1, 0, 0, 0], 3, [(0, 1, 1), (3, 2, 1), (5, 4, 1)]),
  ([1, 0, 6, 0, 0, 0, 0], 3, [(0, 5, 1), (3, 4, 1), (5, 1, 1)]),
  ([1, 1, 0, 0, 0, 0, 5], 3, [(4, 2, 1), (0, 3, 1), (2, 4, 1)]),
  ([1, 1, 0, 0, 0, 1, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([1, 1, 0, 0, 0, 2, 3], 22, [(0, 2, 2), (1, 3, 5), (3, 4, 2), (4, 4, 3), (0, 5, 1), (2, 5, 3), (3, 5, 1), (3, 6, 2), (6, 2, 3)]),
  ([1, 1, 0, 0, 0, 3, 2], 11, [(1, 2, 1), (1, 3, 3), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 2, 3)]),
  ([1, 1, 0, 0, 0, 4, 1], 3, [(3, 2, 1), (1, 4, 1), (6, 3, 1)]),
  ([1, 1, 0, 0, 0, 5, 0], 3, [(3, 2, 1), (1, 3, 1), (6, 5, 1)]),
  ([1, 1, 0, 0, 1, 0, 4], 3, [(0, 3, 1), (4, 4, 1), (2, 5, 1)]),
  ([1, 1, 0, 0, 1, 1, 3], 8, [(0, 3, 1), (1, 4, 1), (4, 4, 2), (0, 5, 1), (2, 5, 1), (3, 5, 1), (2, 6, 1)]),
  ([1, 1, 0, 0, 1, 2, 2], 18, [(2, 2, 2), (0, 3, 3), (1, 4, 3), (2, 4, 2), (0, 5, 1), (3, 5, 3), (4, 5, 1), (4, 6, 1), (6, 3, 2)]),
  ([1, 1, 0, 0, 1, 3, 1], 16, [(3, 0, 1), (2, 2, 1), (1, 3, 4), (3, 3, 2), (1, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 5)]),
  ([1, 1, 0, 0, 1, 4, 0], 3, [(1, 3, 1), (3, 4, 1), (6, 5, 1)]),
  ([1, 1, 0, 0, 2, 0, 3], 8, [(2, 2, 1), (2, 3, 1), (0, 4, 1), (4, 4, 2), (0, 5, 2), (2, 5, 1)]),
  ([1, 1, 0, 0, 2, 1, 2], 28, [(2, 2, 5), (1, 3, 1), (2, 3, 4), (0, 4, 5), (3, 4, 2), (0, 5, 4), (1, 5, 1), (4, 5, 2), (6, 3, 2), (5, 2, 2)]),
  ([1, 1, 0, 0, 2, 2, 1], 18, [(2, 2, 3), (1, 3, 1), (2, 3, 2), (0, 4, 3), (3, 4, 2), (0, 5, 2), (1, 5, 1), (6, 3, 2), (5, 2, 2)]),
  ([1, 1, 0, 0, 2, 3, 0], 16, [(2, 2, 2), (1, 3, 3), (0, 4, 1), (3, 4, 3), (0, 5, 1), (6, 5, 3), (2, 6, 1), (5, 0, 1), (5, 2, 1)]),
  ([1, 1, 0, 0, 3, 0, 2], 16, [(2, 0, 1), (0, 2, 4), (2, 2, 2), (2, 3, 1), (2, 4, 1), (0, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([1, 1, 0, 0, 3, 1, 1], 16, [(2, 0, 1), (0, 2, 4), (2, 2, 2), (2, 3, 1), (0, 4, 1), (2, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([1, 1, 0, 0, 3, 2, 0], 16, [(2, 0, 1), (0, 2, 5), (2, 2, 1), (2, 3, 1), (2, 4, 1), (2, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([1, 1, 0, 0, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([1, 1, 0, 0, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([1, 1, 0, 0, 5, 0, 0], 3, [(2, 2, 1), (0, 3, 1), (5, 5, 1)]),
  ([1, 1, 0, 1, 0, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)])
]
theorem chunk_031_checked : chunk_031.all checkCertificate = true := by
  decide

def chunk_032 : List Certificate := [
  ([1, 1, 0, 1, 0, 1, 3], 8, [(1, 3, 1), (0, 4, 2), (2, 4, 1), (2, 5, 1), (4, 5, 2), (3, 6, 1)]),
  ([1, 1, 0, 1, 0, 2, 2], 18, [(1, 3, 3), (0, 4, 2), (1, 4, 2), (3, 4, 1), (3, 5, 3), (4, 5, 2), (2, 6, 2), (3, 6, 1), (6, 3, 2)]),
  ([1, 1, 0, 1, 0, 3, 1], 8, [(1, 3, 3), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 2)]),
  ([1, 1, 0, 1, 0, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([1, 1, 0, 1, 1, 0, 3], 8, [(2, 0, 1), (0, 4, 1), (4, 4, 2), (0, 5, 1), (2, 5, 2), (4, 6, 1)]),
  ([1, 1, 0, 1, 1, 1, 2], 42, [(2, 0, 3), (1, 3, 7), (0, 4, 4), (2, 4, 3), (4, 5, 7), (2, 6, 3), (3, 6, 4), (6, 1, 2), (6, 2, 5), (5, 0, 4)]),
  ([1, 1, 0, 1, 1, 2, 1], 7, [(1, 3, 1), (0, 4, 1), (2, 4, 1), (3, 5, 1), (2, 6, 1), (6, 3, 1), (5, 0, 1)]),
  ([1, 1, 0, 1, 1, 3, 0], 8, [(3, 4, 2), (1, 5, 3), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([1, 1, 0, 1, 2, 0, 2], 14, [(0, 2, 3), (2, 3, 1), (4, 0, 2), (1, 5, 1), (4, 5, 1), (2, 6, 2), (6, 3, 1), (5, 1, 2), (5, 3, 1)]),
  ([1, 1, 0, 1, 2, 1, 1], 7, [(0, 2, 1), (2, 3, 1), (4, 0, 1), (3, 5, 1), (1, 6, 1), (6, 4, 1), (5, 1, 1)]),
  ([1, 1, 0, 1, 2, 2, 0], 18, [(0, 2, 2), (1, 2, 1), (2, 3, 2), (1, 4, 4), (3, 5, 2), (6, 3, 1), (6, 4, 1), (6, 5, 3), (5, 3, 2)]),
  ([1, 1, 0, 1, 3, 0, 1], 21, [(2, 3, 4), (0, 4, 6), (2, 4, 2), (0, 5, 1), (2, 6, 1), (5, 0, 1), (5, 1, 1), (5, 2, 1), (5, 3, 4)]),
  ([1, 1, 0, 1, 3, 1, 0], 8, [(1, 3, 1), (0, 4, 1), (2, 4, 2), (0, 5, 1), (6, 3, 1), (5, 2, 1), (5, 3, 1)]),
  ([1, 1, 0, 1, 4, 0, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 5, 1)]),
  ([1, 1, 0, 2, 0, 0, 3], 16, [(4, 0, 1), (4, 1, 1), (4, 2, 1), (0, 4, 1), (2, 4, 5), (0, 5, 4), (4, 5, 2), (4, 6, 1)]),
  ([1, 1, 0, 2, 0, 1, 2], 28, [(0, 2, 3), (3, 0, 1), (1, 3, 5), (0, 4, 1), (2, 4, 4), (4, 5, 5), (1, 6, 1), (4, 6, 1), (6, 1, 2), (6, 2, 4), (5, 0, 1)]),
  ([1, 1, 0, 2, 0, 2, 1], 63, [(0, 2, 5), (3, 0, 5), (1, 3, 3), (2, 4, 10), (4, 1, 3), (1, 5, 9), (2, 5, 1), (2, 6, 1), (4, 6, 9), (6, 2, 5), (6, 3, 7), (5, 0, 5)]),
  ([1, 1, 0, 2, 0, 3, 0], 8, [(1, 2, 1), (1, 3, 1), (1, 4, 1), (3, 4, 2), (6, 5, 3)]),
  ([1, 1, 0, 2, 1, 0, 2], 42, [(0, 2, 5), (1, 3, 1), (4, 0, 7), (4, 2, 2), (0, 4, 2), (2, 5, 7), (1, 6, 3), (3, 6, 4), (6, 3, 4), (5, 1, 7)]),
  ([1, 1, 0, 2, 1, 1, 1], 7, [(0, 2, 1), (2, 4, 1), (4, 0, 1), (1, 5, 1), (3, 6, 1), (6, 3, 1), (5, 1, 1)]),
  ([1, 1, 0, 2, 1, 2, 0], 28, [(0, 2, 1), (0, 4, 1), (1, 4, 4), (2, 4, 2), (1, 5, 5), (3, 5, 2), (4, 2, 2), (6, 2, 4), (6, 3, 5), (5, 3, 2)]),
  ([1, 1, 0, 2, 2, 0, 1], 42, [(0, 2, 3), (2, 0, 2), (0, 3, 3), (1, 3, 7), (0, 4, 1), (2, 4, 2), (4, 0, 1), (4, 1, 3), (2, 5, 3), (4, 6, 3), (6, 4, 7), (5, 2, 7)]),
  ([1, 1, 0, 2, 2, 1, 0], 18, [(1, 3, 5), (2, 4, 2), (0, 5, 2), (4, 2, 2), (6, 2, 1), (6, 4, 3), (6, 5, 1), (5, 2, 2)]),
  ([1, 1, 0, 2, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 2), (5, 5, 3)]),
  ([1, 1, 0, 3, 0, 0, 2], 16, [(1, 3, 3), (4, 0, 1), (4, 1, 1), (4, 2, 4), (1, 5, 1), (1, 6, 1), (6, 2, 2), (6, 3, 3)]),
  ([1, 1, 0, 3, 0, 1, 1], 21, [(1, 3, 5), (4, 0, 1), (4, 1, 1), (4, 2, 5), (1, 5, 1), (1, 6, 1), (6, 2, 3), (6, 3, 3), (6, 4, 1)]),
  ([1, 1, 0, 3, 0, 2, 0], 8, [(1, 2, 1), (1, 3, 1), (1, 4, 1), (4, 2, 2), (6, 3, 2), (6, 5, 1)]),
  ([1, 1, 0, 3, 1, 0, 1], 21, [(1, 2, 6), (4, 0, 1), (4, 1, 1), (4, 3, 4), (1, 5, 1), (4, 6, 1), (6, 2, 2), (6, 3, 4), (6, 4, 1)]),
  ([1, 1, 0, 3, 1, 1, 0], 8, [(1, 2, 2), (1, 5, 1), (4, 3, 2), (6, 2, 1), (6, 3, 1), (6, 4, 1)]),
  ([1, 1, 0, 3, 2, 0, 0], 8, [(0, 2, 2), (1, 4, 1), (2, 5, 1), (4, 3, 1), (6, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([1, 1, 0, 4, 0, 0, 1], 3, [(1, 4, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 1, 0, 4, 0, 1, 0], 3, [(1, 2, 1), (4, 3, 1), (6, 4, 1)])
]
theorem chunk_032_checked : chunk_032.all checkCertificate = true := by
  decide

def chunk_033 : List Certificate := [
  ([1, 1, 0, 4, 1, 0, 0], 3, [(1, 3, 1), (4, 2, 1), (6, 4, 1)]),
  ([1, 1, 0, 5, 0, 0, 0], 3, [(1, 5, 1), (4, 4, 1), (6, 3, 1)]),
  ([1, 1, 1, 0, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([1, 1, 1, 0, 0, 1, 3], 8, [(0, 3, 1), (0, 4, 1), (2, 4, 2), (1, 5, 1), (3, 5, 1), (4, 5, 1), (4, 6, 1)]),
  ([1, 1, 1, 0, 0, 2, 2], 18, [(1, 3, 3), (1, 4, 2), (3, 4, 3), (0, 5, 2), (3, 5, 1), (4, 5, 2), (2, 6, 2), (3, 6, 1), (6, 3, 2)]),
  ([1, 1, 1, 0, 0, 3, 1], 16, [(3, 0, 1), (3, 1, 1), (1, 3, 5), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 5)]),
  ([1, 1, 1, 0, 0, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)]),
  ([1, 1, 1, 0, 1, 0, 3], 8, [(2, 0, 1), (0, 4, 2), (2, 4, 1), (4, 5, 3), (2, 6, 1)]),
  ([1, 1, 1, 0, 1, 1, 2], 28, [(3, 1, 5), (1, 3, 1), (0, 4, 4), (1, 4, 1), (0, 5, 1), (3, 5, 2), (4, 5, 2), (2, 6, 5), (6, 3, 2), (5, 0, 5)]),
  ([1, 1, 1, 0, 1, 2, 1], 7, [(3, 1, 1), (0, 4, 1), (1, 4, 1), (3, 5, 1), (2, 6, 1), (6, 3, 1), (5, 0, 1)]),
  ([1, 1, 1, 0, 1, 3, 0], 21, [(3, 0, 1), (3, 1, 1), (1, 3, 1), (1, 4, 4), (3, 4, 4), (1, 5, 2), (6, 2, 1), (6, 5, 6), (3, 6, 1)]),
  ([1, 1, 1, 0, 2, 0, 2], 14, [(0, 3, 1), (3, 0, 3), (0, 4, 1), (0, 5, 1), (2, 5, 2), (2, 6, 1), (4, 6, 2), (5, 1, 3)]),
  ([1, 1, 1, 0, 2, 1, 1], 49, [(0, 2, 1), (0, 3, 4), (2, 3, 2), (3, 0, 8), (0, 4, 5), (2, 5, 8), (1, 6, 3), (3, 6, 2), (4, 6, 3), (6, 4, 3), (5, 1, 8), (5, 3, 2)]),
  ([1, 1, 1, 0, 2, 2, 0], 42, [(1, 3, 2), (3, 0, 3), (0, 4, 1), (1, 4, 2), (2, 4, 7), (0, 5, 6), (3, 5, 4), (6, 3, 7), (1, 6, 3), (5, 1, 3), (5, 2, 3), (5, 3, 1)]),
  ([1, 1, 1, 0, 3, 0, 1], 21, [(2, 0, 1), (0, 3, 6), (2, 3, 2), (2, 4, 3), (0, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1), (5, 4, 5)]),
  ([1, 1, 1, 0, 3, 1, 0], 21, [(2, 0, 1), (0, 3, 7), (2, 4, 4), (2, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 4)]),
  ([1, 1, 1, 0, 4, 0, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 5, 1)]),
  ([1, 1, 1, 1, 0, 0, 3], 8, [(2, 0, 1), (0, 4, 2), (2, 4, 1), (4, 5, 3), (2, 6, 1)]),
  ([1, 1, 1, 1, 0, 1, 2], 42, [(0, 2, 3), (3, 1, 8), (4, 0, 1), (0, 4, 4), (2, 5, 2), (4, 5, 6), (1, 6, 3), (2, 6, 5), (6, 3, 3), (5, 0, 7)]),
  ([1, 1, 1, 1, 0, 2, 1], 7, [(3, 1, 1), (1, 4, 1), (4, 2, 1), (0, 5, 1), (2, 6, 1), (6, 3, 1), (5, 0, 1)]),
  ([1, 1, 1, 1, 0, 3, 0], 21, [(3, 0, 1), (3, 1, 1), (1, 3, 1), (1, 4, 6), (3, 4, 2), (3, 5, 2), (6, 2, 1), (6, 5, 6), (3, 6, 1)]),
  ([1, 1, 1, 1, 1, 0, 2], 70, [(0, 2, 6), (2, 0, 1), (1, 3, 1), (3, 0, 12), (4, 1, 1), (0, 4, 6), (1, 5, 4), (2, 5, 9), (2, 6, 2), (4, 6, 11), (6, 3, 5), (5, 1, 12)]),
  ([1, 1, 1, 1, 1, 1, 1], 7, [(1, 3, 1), (3, 0, 1), (2, 4, 1), (0, 5, 1), (4, 6, 1), (6, 2, 1), (5, 1, 1)]),
  ([1, 1, 1, 1, 1, 2, 0], 56, [(0, 2, 4), (3, 0, 9), (1, 4, 5), (2, 4, 4), (1, 5, 6), (4, 2, 4), (6, 3, 8), (6, 5, 3), (3, 6, 2), (5, 1, 9), (5, 2, 1), (5, 3, 1)]),
  ([1, 1, 1, 1, 2, 0, 1], 14, [(0, 3, 4), (1, 4, 1), (2, 4, 1), (3, 1, 1), (4, 0, 1), (6, 4, 1), (5, 2, 4), (5, 4, 1)]),
  ([1, 1, 1, 1, 2, 1, 0], 14, [(0, 3, 4), (1, 4, 1), (2, 4, 1), (3, 1, 1), (4, 0, 1), (6, 4, 1), (5, 2, 4), (5, 4, 1)]),
  ([1, 1, 1, 1, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 2), (5, 5, 3)]),
  ([1, 1, 1, 2, 0, 0, 2], 42, [(0, 2, 3), (2, 0, 2), (3, 0, 5), (4, 2, 4), (4, 3, 4), (0, 5, 2), (1, 5, 5), (2, 6, 3), (4, 6, 4), (6, 1, 2), (6, 3, 3), (5, 1, 5)]),
  ([1, 1, 1, 2, 0, 1, 1], 35, [(1, 3, 5), (3, 0, 6), (1, 4, 1), (4, 0, 2), (4, 1, 1), (4, 2, 4), (1, 5, 1), (3, 6, 1), (6, 2, 4), (6, 3, 3), (5, 1, 7)]),
  ([1, 1, 1, 2, 0, 2, 0], 14, [(1, 3, 1), (3, 0, 3), (1, 4, 1), (1, 5, 1), (4, 2, 2), (6, 2, 1), (6, 3, 2), (5, 1, 3)]),
  ([1, 1, 1, 2, 1, 0, 1], 35, [(0, 3, 9), (0, 4, 2), (1, 4, 3), (3, 0, 1), (3, 1, 1), (4, 2, 1), (4, 3, 3), (3, 6, 1), (6, 4, 3), (5, 2, 11)]),
  ([1, 1, 1, 2, 1, 1, 0], 28, [(0, 3, 7), (1, 4, 3), (3, 0, 2), (3, 1, 1), (4, 1, 1), (4, 3, 2), (6, 4, 3), (5, 2, 9)])
]
theorem chunk_033_checked : chunk_033.all checkCertificate = true := by
  decide

def chunk_034 : List Certificate := [
  ([1, 1, 1, 2, 2, 0, 0], 18, [(0, 2, 3), (0, 3, 1), (0, 4, 1), (1, 5, 2), (2, 5, 2), (4, 3, 2), (6, 3, 2), (5, 4, 4), (5, 5, 1)]),
  ([1, 1, 1, 3, 0, 0, 1], 16, [(1, 3, 5), (4, 0, 1), (4, 2, 1), (4, 4, 3), (4, 6, 1), (6, 1, 1), (6, 3, 1), (6, 4, 3)]),
  ([1, 1, 1, 3, 0, 1, 0], 8, [(1, 4, 2), (4, 3, 3), (6, 1, 1), (6, 2, 1), (6, 4, 1)]),
  ([1, 1, 1, 3, 1, 0, 0], 8, [(0, 2, 1), (1, 4, 2), (4, 3, 1), (4, 4, 1), (6, 3, 2), (5, 5, 1)]),
  ([1, 1, 1, 4, 0, 0, 0], 3, [(1, 3, 1), (4, 4, 1), (6, 5, 1)]),
  ([1, 1, 2, 0, 0, 0, 3], 8, [(0, 2, 1), (4, 1, 1), (0, 4, 1), (3, 4, 1), (2, 5, 2), (4, 6, 1), (5, 0, 1)]),
  ([1, 1, 2, 0, 0, 1, 2], 5, [(3, 2, 1), (4, 1, 1), (0, 5, 1), (2, 6, 1), (5, 0, 1)]),
  ([1, 1, 2, 0, 0, 2, 1], 42, [(3, 2, 7), (1, 4, 3), (3, 4, 3), (4, 0, 2), (4, 1, 3), (0, 5, 5), (3, 5, 2), (1, 6, 2), (2, 6, 5), (6, 1, 4), (6, 4, 1), (5, 0, 5)]),
  ([1, 1, 2, 0, 0, 3, 0], 8, [(3, 1, 1), (3, 2, 1), (1, 5, 2), (3, 5, 1), (6, 4, 3)]),
  ([1, 1, 2, 0, 1, 0, 2], 5, [(0, 2, 1), (2, 0, 1), (4, 5, 1), (3, 6, 1), (5, 1, 1)]),
  ([1, 1, 2, 0, 1, 1, 1], 14, [(0, 2, 1), (2, 0, 1), (3, 0, 1), (3, 2, 4), (4, 0, 1), (6, 1, 1), (5, 0, 1), (5, 1, 4)]),
  ([1, 1, 2, 0, 1, 2, 0], 21, [(0, 2, 2), (2, 0, 2), (3, 0, 2), (3, 2, 5), (4, 0, 1), (6, 4, 1), (6, 5, 1), (5, 1, 7)]),
  ([1, 1, 2, 0, 2, 0, 1], 14, [(0, 3, 4), (1, 4, 1), (2, 4, 1), (3, 1, 1), (4, 0, 1), (6, 4, 1), (5, 2, 4), (5, 4, 1)]),
  ([1, 1, 2, 0, 2, 1, 0], 14, [(0, 3, 4), (1, 4, 1), (2, 4, 1), (3, 1, 1), (4, 2, 1), (6, 4, 1), (5, 0, 1), (5, 2, 3), (5, 4, 1)]),
  ([1, 1, 2, 0, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 2), (5, 5, 3)]),
  ([1, 1, 2, 1, 0, 0, 2], 5, [(3, 2, 1), (4, 0, 1), (0, 5, 1), (2, 6, 1), (5, 1, 1)]),
  ([1, 1, 2, 1, 0, 1, 1], 14, [(0, 2, 1), (2, 0, 1), (3, 2, 4), (4, 0, 2), (6, 1, 1), (6, 3, 1), (5, 1, 4)]),
  ([1, 1, 2, 1, 0, 2, 0], 35, [(0, 2, 3), (2, 0, 3), (3, 0, 2), (3, 2, 9), (4, 0, 3), (6, 1, 1), (6, 3, 1), (6, 4, 1), (6, 5, 1), (5, 1, 11)]),
  ([1, 1, 2, 1, 1, 0, 1], 42, [(0, 3, 11), (1, 4, 4), (3, 1, 3), (3, 2, 1), (4, 0, 2), (4, 3, 3), (6, 4, 5), (5, 2, 13)]),
  ([1, 1, 2, 1, 1, 1, 0], 21, [(0, 3, 5), (0, 4, 1), (1, 4, 2), (3, 0, 1), (3, 1, 1), (4, 3, 2), (6, 4, 2), (5, 2, 7)]),
  ([1, 1, 2, 1, 2, 0, 0], 28, [(0, 2, 5), (0, 3, 3), (0, 4, 1), (1, 5, 2), (2, 5, 2), (3, 2, 2), (4, 3, 2), (6, 3, 2), (5, 4, 6), (5, 5, 3)]),
  ([1, 1, 2, 2, 0, 0, 1], 18, [(0, 3, 2), (1, 4, 2), (3, 2, 2), (4, 1, 3), (4, 4, 2), (6, 2, 1), (6, 3, 3), (6, 4, 1), (5, 2, 2)]),
  ([1, 1, 2, 2, 0, 1, 0], 18, [(0, 3, 2), (1, 4, 2), (3, 1, 2), (4, 1, 1), (4, 3, 3), (4, 4, 1), (6, 2, 3), (6, 4, 2), (5, 2, 2)]),
  ([1, 1, 2, 2, 1, 0, 0], 18, [(0, 2, 4), (1, 4, 2), (3, 1, 1), (3, 2, 1), (4, 3, 2), (4, 4, 1), (6, 3, 3), (5, 4, 2), (5, 5, 2)]),
  ([1, 1, 2, 3, 0, 0, 0], 22, [(0, 2, 3), (1, 4, 2), (1, 5, 1), (3, 1, 1), (3, 2, 2), (4, 3, 1), (4, 5, 4), (6, 1, 1), (6, 3, 4), (5, 4, 3)]),
  ([1, 1, 3, 0, 0, 0, 2], 8, [(0, 3, 2), (3, 2, 3), (5, 0, 1), (5, 1, 1), (5, 3, 1)]),
  ([1, 1, 3, 0, 0, 1, 1], 8, [(0, 2, 2), (3, 2, 1), (3, 3, 2), (5, 0, 1), (5, 1, 1), (5, 3, 1)]),
  ([1, 1, 3, 0, 0, 2, 0], 8, [(0, 2, 2), (3, 2, 1), (3, 3, 1), (3, 5, 1), (6, 3, 1), (5, 1, 1), (5, 3, 1)]),
  ([1, 1, 3, 0, 1, 0, 1], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([1, 1, 3, 0, 1, 1, 0], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([1, 1, 3, 0, 2, 0, 0], 8, [(0, 2, 3), (3, 3, 2), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([1, 1, 3, 1, 0, 0, 1], 16, [(0, 3, 5), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (4, 4, 1), (3, 6, 1), (5, 2, 5)])
]
theorem chunk_034_checked : chunk_034.all checkCertificate = true := by
  decide

def chunk_035 : List Certificate := [
  ([1, 1, 3, 1, 0, 1, 0], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([1, 1, 3, 1, 1, 0, 0], 8, [(0, 2, 3), (3, 3, 2), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([1, 1, 3, 2, 0, 0, 0], 22, [(0, 2, 5), (1, 5, 1), (3, 1, 1), (3, 3, 4), (4, 3, 3), (6, 1, 1), (6, 5, 2), (5, 2, 2), (5, 4, 3)]),
  ([1, 1, 4, 0, 0, 0, 1], 3, [(0, 3, 1), (3, 4, 1), (5, 2, 1)]),
  ([1, 1, 4, 0, 0, 1, 0], 3, [(0, 3, 1), (3, 4, 1), (5, 2, 1)]),
  ([1, 1, 4, 0, 1, 0, 0], 3, [(0, 2, 1), (3, 4, 1), (5, 3, 1)]),
  ([1, 1, 4, 1, 0, 0, 0], 3, [(0, 2, 1), (3, 3, 1), (5, 4, 1)]),
  ([1, 1, 5, 0, 0, 0, 0], 3, [(0, 2, 1), (3, 4, 1), (5, 3, 1)]),
  ([1, 2, 0, 0, 0, 0, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([1, 2, 0, 0, 0, 1, 3], 11, [(4, 0, 1), (4, 1, 1), (2, 4, 4), (0, 5, 3), (4, 5, 1), (4, 6, 1)]),
  ([1, 2, 0, 0, 0, 2, 2], 21, [(2, 1, 3), (4, 0, 3), (0, 4, 1), (1, 4, 1), (2, 4, 1), (3, 4, 1), (1, 5, 3), (4, 5, 1), (3, 6, 3), (6, 3, 4)]),
  ([1, 2, 0, 0, 0, 3, 1], 16, [(2, 0, 1), (3, 1, 1), (1, 3, 5), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 5)]),
  ([1, 2, 0, 0, 0, 4, 0], 3, [(3, 3, 1), (1, 5, 1), (6, 4, 1)]),
  ([1, 2, 0, 0, 1, 0, 3], 11, [(2, 1, 1), (4, 0, 1), (0, 4, 2), (2, 4, 2), (0, 5, 1), (4, 5, 3), (2, 6, 1)]),
  ([1, 2, 0, 0, 1, 1, 2], 28, [(2, 1, 4), (3, 0, 2), (4, 0, 3), (4, 1, 1), (0, 5, 2), (4, 5, 5), (1, 6, 2), (2, 6, 5), (6, 1, 2), (5, 0, 2)]),
  ([1, 2, 0, 0, 1, 2, 1], 5, [(2, 1, 1), (4, 0, 1), (1, 5, 1), (3, 6, 1), (6, 4, 1)]),
  ([1, 2, 0, 0, 1, 3, 0], 16, [(2, 1, 1), (3, 0, 1), (1, 3, 1), (1, 4, 1), (1, 5, 3), (3, 5, 3), (6, 4, 5), (3, 6, 1)]),
  ([1, 2, 0, 0, 2, 0, 2], 28, [(2, 0, 7), (4, 1, 3), (0, 5, 2), (1, 5, 2), (4, 5, 3), (2, 6, 2), (3, 6, 2), (4, 6, 3), (6, 1, 2), (5, 1, 2)]),
  ([1, 2, 0, 0, 2, 1, 1], 42, [(2, 0, 6), (1, 3, 3), (2, 3, 4), (2, 4, 2), (4, 0, 1), (4, 1, 2), (0, 5, 5), (1, 5, 2), (3, 6, 5), (4, 6, 2), (6, 4, 5), (5, 1, 5)]),
  ([1, 2, 0, 0, 2, 2, 0], 18, [(0, 3, 2), (2, 4, 4), (1, 5, 2), (2, 5, 1), (3, 5, 2), (6, 1, 1), (6, 3, 3), (6, 4, 1), (5, 1, 2)]),
  ([1, 2, 0, 0, 3, 0, 1], 16, [(2, 0, 1), (2, 1, 1), (0, 3, 5), (2, 3, 1), (2, 4, 1), (2, 5, 1), (2, 6, 1), (5, 4, 5)]),
  ([1, 2, 0, 0, 3, 1, 0], 8, [(2, 0, 1), (2, 1, 1), (0, 3, 2), (2, 3, 1), (5, 4, 3)]),
  ([1, 2, 0, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 5, 1)]),
  ([1, 2, 0, 1, 0, 0, 3], 11, [(2, 1, 1), (4, 0, 1), (0, 4, 2), (2, 4, 2), (0, 5, 1), (4, 5, 3), (2, 6, 1)]),
  ([1, 2, 0, 1, 0, 1, 2], 28, [(2, 1, 4), (3, 0, 2), (4, 0, 3), (4, 1, 1), (0, 5, 2), (4, 5, 5), (1, 6, 2), (2, 6, 5), (6, 1, 2), (5, 0, 2)]),
  ([1, 2, 0, 1, 0, 2, 1], 5, [(2, 1, 1), (4, 0, 1), (1, 5, 1), (3, 6, 1), (6, 4, 1)]),
  ([1, 2, 0, 1, 0, 3, 0], 21, [(3, 0, 1), (3, 1, 1), (1, 3, 1), (1, 4, 2), (1, 5, 4), (3, 5, 4), (6, 2, 1), (6, 4, 6), (3, 6, 1)]),
  ([1, 2, 0, 1, 1, 0, 2], 28, [(2, 0, 7), (2, 1, 1), (3, 1, 2), (0, 5, 2), (1, 5, 2), (4, 5, 3), (2, 6, 1), (4, 6, 6), (6, 1, 2), (5, 1, 2)]),
  ([1, 2, 0, 1, 1, 1, 1], 7, [(2, 0, 2), (4, 1, 1), (1, 5, 1), (3, 6, 1), (6, 4, 1), (5, 1, 1)]),
  ([1, 2, 0, 1, 1, 2, 0], 7, [(2, 0, 2), (3, 5, 1), (4, 1, 1), (6, 4, 1), (1, 6, 1), (5, 1, 1)]),
  ([1, 2, 0, 1, 2, 0, 1], 28, [(2, 0, 1), (2, 1, 3), (0, 3, 5), (1, 4, 2), (2, 4, 1), (3, 0, 2), (4, 0, 2), (6, 1, 2), (5, 2, 5), (5, 4, 5)]),
  ([1, 2, 0, 1, 2, 1, 0], 28, [(2, 0, 3), (2, 1, 1), (0, 3, 5), (1, 4, 2), (2, 4, 1), (3, 0, 2), (4, 1, 2), (6, 1, 2), (5, 2, 5), (5, 4, 5)])
]
theorem chunk_035_checked : chunk_035.all checkCertificate = true := by
  decide

def chunk_036 : List Certificate := [
  ([1, 2, 0, 1, 3, 0, 0], 8, [(2, 0, 1), (2, 1, 1), (0, 4, 2), (2, 4, 1), (5, 5, 3)]),
  ([1, 2, 0, 2, 0, 0, 2], 28, [(2, 0, 2), (3, 0, 2), (4, 0, 3), (4, 1, 3), (0, 5, 2), (1, 5, 2), (4, 5, 3), (2, 6, 7), (6, 1, 2), (5, 1, 2)]),
  ([1, 2, 0, 2, 0, 1, 1], 21, [(1, 3, 1), (2, 0, 1), (3, 0, 4), (1, 4, 1), (4, 1, 1), (4, 3, 3), (1, 5, 1), (1, 6, 1), (6, 2, 4), (5, 1, 4)]),
  ([1, 2, 0, 2, 0, 2, 0], 14, [(1, 3, 1), (3, 0, 3), (1, 4, 2), (2, 5, 1), (4, 3, 1), (6, 2, 2), (6, 5, 1), (5, 1, 3)]),
  ([1, 2, 0, 2, 1, 0, 1], 35, [(0, 3, 4), (1, 3, 1), (2, 1, 4), (1, 4, 3), (3, 0, 4), (4, 0, 3), (4, 1, 1), (6, 1, 2), (6, 3, 2), (5, 2, 7), (5, 4, 4)]),
  ([1, 2, 0, 2, 1, 1, 0], 35, [(0, 3, 4), (1, 3, 1), (2, 0, 3), (2, 1, 1), (1, 4, 3), (3, 0, 4), (4, 1, 4), (6, 1, 2), (6, 3, 2), (5, 2, 7), (5, 4, 4)]),
  ([1, 2, 0, 2, 2, 0, 0], 33, [(0, 3, 5), (1, 3, 1), (2, 0, 3), (2, 1, 2), (1, 4, 4), (4, 2, 3), (4, 3, 2), (6, 1, 1), (6, 4, 4), (5, 5, 8)]),
  ([1, 2, 0, 3, 0, 0, 1], 16, [(1, 3, 4), (1, 4, 1), (4, 0, 1), (4, 1, 1), (4, 2, 1), (4, 3, 2), (4, 6, 1), (6, 4, 5)]),
  ([1, 2, 0, 3, 0, 1, 0], 8, [(1, 4, 2), (4, 3, 3), (6, 1, 1), (6, 2, 1), (6, 4, 1)]),
  ([1, 2, 0, 3, 1, 0, 0], 16, [(1, 4, 5), (4, 0, 1), (4, 3, 4), (6, 1, 1), (6, 2, 1), (6, 3, 2), (6, 4, 1), (5, 5, 1)]),
  ([1, 2, 0, 4, 0, 0, 0], 3, [(1, 4, 1), (4, 5, 1), (6, 3, 1)]),
  ([1, 2, 1, 0, 0, 0, 3], 11, [(4, 0, 1), (4, 1, 1), (0, 4, 3), (2, 4, 1), (2, 5, 3), (4, 5, 1), (4, 6, 1)]),
  ([1, 2, 1, 0, 0, 1, 2], 28, [(3, 1, 2), (4, 0, 5), (4, 1, 3), (0, 5, 2), (2, 5, 5), (1, 6, 2), (2, 6, 4), (4, 6, 1), (6, 1, 2), (5, 0, 2)]),
  ([1, 2, 1, 0, 0, 2, 1], 5, [(3, 4, 1), (4, 0, 1), (2, 5, 1), (1, 6, 1), (6, 1, 1)]),
  ([1, 2, 1, 0, 0, 3, 0], 8, [(3, 2, 1), (3, 4, 2), (1, 5, 2), (6, 1, 1), (6, 4, 1), (6, 5, 1)]),
  ([1, 2, 1, 0, 1, 0, 2], 28, [(2, 0, 7), (4, 1, 3), (0, 5, 2), (4, 5, 5), (1, 6, 2), (2, 6, 2), (3, 6, 2), (4, 6, 1), (6, 1, 2), (5, 1, 2)]),
  ([1, 2, 1, 0, 1, 1, 1], 49, [(2, 0, 11), (0, 4, 3), (1, 4, 3), (4, 0, 2), (4, 1, 3), (1, 5, 2), (3, 5, 4), (3, 6, 6), (6, 2, 5), (5, 1, 10)]),
  ([1, 2, 1, 0, 1, 2, 0], 21, [(2, 0, 4), (3, 0, 2), (3, 2, 1), (0, 4, 1), (3, 5, 2), (4, 2, 2), (6, 1, 1), (6, 4, 1), (1, 6, 2), (5, 1, 5)]),
  ([1, 2, 1, 0, 2, 0, 1], 14, [(2, 1, 1), (0, 3, 1), (1, 4, 1), (3, 0, 4), (4, 1, 1), (6, 1, 1), (5, 1, 1), (5, 2, 4)]),
  ([1, 2, 1, 0, 2, 1, 0], 14, [(2, 1, 1), (0, 4, 1), (3, 0, 4), (3, 1, 1), (1, 5, 1), (6, 1, 1), (5, 1, 1), (5, 2, 4)]),
  ([1, 2, 1, 0, 3, 0, 0], 8, [(2, 0, 1), (2, 1, 1), (0, 4, 2), (2, 4, 1), (5, 5, 3)]),
  ([1, 2, 1, 1, 0, 0, 2], 28, [(2, 1, 3), (3, 0, 1), (4, 0, 6), (0, 5, 2), (1, 5, 2), (4, 5, 3), (2, 6, 6), (3, 6, 1), (6, 1, 2), (5, 1, 2)]),
  ([1, 2, 1, 1, 0, 1, 1], 7, [(2, 0, 1), (3, 2, 2), (4, 0, 1), (6, 1, 1), (5, 1, 2)]),
  ([1, 2, 1, 1, 0, 2, 0], 21, [(0, 3, 1), (2, 0, 2), (3, 2, 6), (0, 4, 1), (4, 0, 2), (6, 1, 1), (6, 2, 1), (6, 5, 1), (5, 1, 6)]),
  ([1, 2, 1, 1, 1, 0, 1], 14, [(0, 3, 1), (2, 1, 1), (1, 4, 1), (3, 0, 4), (4, 1, 1), (6, 1, 1), (5, 1, 1), (5, 2, 4)]),
  ([1, 2, 1, 1, 1, 1, 0], 28, [(0, 3, 1), (2, 1, 2), (0, 4, 1), (3, 0, 7), (3, 1, 2), (1, 5, 1), (4, 1, 2), (6, 1, 3), (5, 2, 9)]),
  ([1, 2, 1, 1, 2, 0, 0], 5, [(0, 3, 1), (2, 1, 1), (4, 2, 1), (6, 4, 1), (5, 5, 1)]),
  ([1, 2, 1, 2, 0, 0, 1], 28, [(0, 3, 2), (1, 4, 2), (2, 1, 2), (3, 2, 2), (4, 1, 5), (4, 4, 4), (6, 2, 3), (6, 3, 5), (6, 4, 1), (5, 2, 2)]),
  ([1, 2, 1, 2, 0, 1, 0], 28, [(0, 3, 2), (1, 4, 2), (2, 1, 2), (3, 1, 2), (4, 3, 4), (4, 4, 5), (6, 1, 3), (6, 2, 5), (6, 3, 1), (5, 2, 2)]),
  ([1, 2, 1, 2, 1, 0, 0], 28, [(0, 3, 2), (1, 4, 2), (2, 1, 2), (3, 2, 2), (4, 1, 3), (4, 2, 5), (4, 4, 1), (6, 3, 5), (6, 4, 4), (5, 1, 2)]),
  ([1, 2, 1, 3, 0, 0, 0], 11, [(1, 5, 3), (4, 2, 1), (4, 4, 3), (6, 1, 1), (6, 3, 1), (6, 4, 1), (6, 5, 1)]),
  ([1, 2, 2, 0, 0, 0, 2], 21, [(0, 3, 1), (2, 0, 1), (3, 2, 4), (4, 0, 2), (4, 3, 2), (0, 5, 3), (2, 6, 3), (6, 3, 1), (5, 1, 4)])
]
theorem chunk_036_checked : chunk_036.all checkCertificate = true := by
  decide

def chunk_037 : List Certificate := [
  ([1, 2, 2, 0, 0, 1, 1], 18, [(0, 3, 2), (2, 0, 2), (3, 2, 5), (4, 0, 1), (4, 3, 1), (6, 3, 2), (5, 1, 5)]),
  ([1, 2, 2, 0, 0, 2, 0], 18, [(0, 3, 2), (2, 0, 2), (3, 2, 5), (4, 0, 1), (4, 3, 1), (6, 3, 2), (5, 1, 5)]),
  ([1, 2, 2, 0, 1, 0, 1], 18, [(0, 3, 2), (2, 1, 2), (3, 0, 3), (3, 1, 1), (3, 3, 1), (4, 1, 2), (6, 3, 2), (5, 2, 5)]),
  ([1, 2, 2, 0, 1, 1, 0], 18, [(0, 3, 2), (2, 1, 2), (3, 0, 3), (3, 1, 2), (4, 3, 2), (6, 1, 1), (6, 3, 1), (5, 2, 5)]),
  ([1, 2, 2, 0, 2, 0, 0], 18, [(0, 3, 2), (2, 0, 2), (3, 1, 1), (3, 2, 3), (3, 3, 1), (4, 3, 2), (6, 2, 2), (5, 0, 1), (5, 1, 4)]),
  ([1, 2, 2, 1, 0, 0, 1], 18, [(0, 3, 2), (2, 1, 2), (3, 0, 3), (3, 3, 2), (4, 1, 1), (4, 3, 1), (6, 1, 2), (5, 2, 5)]),
  ([1, 2, 2, 1, 0, 1, 0], 18, [(0, 3, 2), (2, 1, 2), (3, 0, 3), (3, 1, 1), (3, 3, 1), (4, 1, 2), (6, 3, 2), (5, 2, 5)]),
  ([1, 2, 2, 1, 1, 0, 0], 18, [(0, 3, 2), (2, 1, 2), (3, 2, 4), (4, 0, 2), (4, 2, 1), (6, 1, 3), (5, 3, 3), (5, 4, 1)]),
  ([1, 2, 2, 2, 0, 0, 0], 35, [(0, 3, 3), (1, 5, 3), (2, 1, 3), (3, 3, 3), (4, 2, 7), (4, 4, 3), (6, 1, 4), (6, 3, 1), (6, 4, 1), (6, 5, 4), (5, 4, 3)]),
  ([1, 2, 3, 0, 0, 0, 1], 22, [(0, 3, 3), (2, 1, 3), (3, 0, 2), (3, 3, 2), (3, 4, 1), (4, 4, 3), (6, 1, 2), (6, 4, 1), (5, 2, 5)]),
  ([1, 2, 3, 0, 0, 1, 0], 22, [(0, 3, 2), (0, 4, 1), (2, 1, 3), (3, 0, 2), (3, 4, 3), (4, 1, 2), (4, 4, 1), (6, 3, 3), (5, 2, 5)]),
  ([1, 2, 3, 0, 1, 0, 0], 11, [(0, 3, 2), (2, 1, 1), (3, 0, 1), (3, 2, 2), (4, 4, 1), (6, 1, 1), (5, 3, 1), (5, 4, 2)]),
  ([1, 2, 3, 1, 0, 0, 0], 11, [(0, 3, 3), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (5, 4, 4)]),
  ([1, 2, 4, 0, 0, 0, 0], 3, [(0, 4, 1), (3, 5, 1), (5, 3, 1)]),
  ([1, 3, 0, 0, 0, 0, 3], 42, [(2, 0, 3), (2, 2, 1), (3, 1, 4), (4, 2, 5), (1, 4, 1), (4, 4, 6), (0, 5, 4), (1, 5, 3), (2, 6, 7), (6, 1, 3), (6, 2, 1), (5, 0, 4)]),
  ([1, 3, 0, 0, 0, 1, 2], 11, [(2, 0, 1), (2, 1, 2), (4, 1, 2), (4, 2, 1), (2, 5, 1), (4, 6, 1), (6, 2, 3)]),
  ([1, 3, 0, 0, 0, 2, 1], 8, [(2, 0, 1), (2, 1, 1), (3, 1, 1), (4, 2, 1), (1, 5, 1), (4, 6, 1), (6, 2, 1), (6, 4, 1)]),
  ([1, 3, 0, 0, 0, 3, 0], 8, [(3, 1, 2), (1, 4, 1), (2, 4, 1), (4, 2, 1), (6, 2, 1), (6, 5, 2)]),
  ([1, 3, 0, 0, 1, 0, 2], 11, [(2, 0, 1), (2, 1, 1), (4, 1, 3), (4, 2, 1), (2, 5, 1), (2, 6, 1), (6, 2, 3)]),
  ([1, 3, 0, 0, 1, 1, 1], 8, [(2, 0, 1), (2, 1, 2), (4, 1, 1), (4, 2, 1), (4, 6, 1), (6, 2, 2)]),
  ([1, 3, 0, 0, 1, 2, 0], 16, [(2, 0, 1), (2, 1, 3), (2, 4, 1), (4, 2, 5), (6, 1, 3), (6, 2, 1), (6, 5, 1), (2, 6, 1)]),
  ([1, 3, 0, 0, 2, 0, 1], 8, [(2, 0, 1), (2, 2, 2), (4, 1, 2), (6, 1, 1), (6, 4, 1), (5, 2, 1)]),
  ([1, 3, 0, 0, 2, 1, 0], 8, [(2, 0, 1), (2, 2, 2), (4, 1, 2), (6, 1, 1), (6, 4, 1), (5, 2, 1)]),
  ([1, 3, 0, 0, 3, 0, 0], 11, [(2, 0, 1), (2, 1, 1), (2, 2, 1), (0, 4, 3), (2, 4, 1), (5, 5, 4)]),
  ([1, 3, 0, 1, 0, 0, 2], 11, [(2, 0, 1), (2, 1, 1), (4, 1, 3), (4, 2, 1), (2, 5, 1), (2, 6, 1), (6, 2, 3)]),
  ([1, 3, 0, 1, 0, 1, 1], 8, [(2, 0, 1), (2, 1, 1), (4, 1, 2), (4, 2, 1), (2, 6, 1), (6, 2, 2)]),
  ([1, 3, 0, 1, 0, 2, 0], 21, [(2, 0, 1), (2, 1, 4), (2, 5, 1), (4, 2, 6), (4, 3, 1), (6, 1, 4), (6, 2, 2), (6, 4, 1), (2, 6, 1)]),
  ([1, 3, 0, 1, 1, 0, 1], 8, [(2, 0, 1), (2, 2, 1), (4, 1, 1), (4, 2, 2), (2, 6, 1), (6, 1, 2)]),
  ([1, 3, 0, 1, 1, 1, 0], 21, [(2, 0, 1), (2, 2, 4), (2, 5, 1), (4, 1, 3), (4, 2, 4), (6, 1, 5), (6, 3, 1), (6, 4, 1), (2, 6, 1)]),
  ([1, 3, 0, 1, 2, 0, 0], 8, [(2, 0, 1), (2, 1, 1), (2, 2, 1), (4, 2, 2), (6, 1, 2), (5, 5, 1)]),
  ([1, 3, 0, 2, 0, 0, 1], 8, [(2, 1, 1), (2, 2, 1), (4, 2, 2), (4, 3, 1), (6, 1, 2), (6, 4, 1)]),
  ([1, 3, 0, 2, 0, 1, 0], 8, [(2, 2, 2), (4, 1, 2), (4, 4, 1), (6, 1, 1), (6, 2, 1), (6, 3, 1)])
]
theorem chunk_037_checked : chunk_037.all checkCertificate = true := by
  decide

def chunk_038 : List Certificate := [
  ([1, 3, 0, 2, 1, 0, 0], 16, [(2, 2, 5), (4, 0, 1), (4, 1, 1), (4, 2, 1), (4, 3, 1), (4, 4, 1), (6, 1, 5), (5, 5, 1)]),
  ([1, 3, 0, 3, 0, 0, 0], 11, [(1, 4, 2), (2, 2, 1), (4, 1, 2), (4, 2, 1), (4, 4, 1), (6, 3, 1), (6, 5, 3)]),
  ([1, 3, 1, 0, 0, 0, 2], 11, [(2, 0, 1), (2, 1, 1), (4, 1, 3), (4, 2, 1), (2, 5, 1), (2, 6, 1), (6, 2, 3)]),
  ([1, 3, 1, 0, 0, 1, 1], 8, [(2, 0, 1), (2, 1, 1), (3, 3, 1), (4, 1, 1), (4, 2, 1), (6, 2, 2), (5, 1, 1)]),
  ([1, 3, 1, 0, 0, 2, 0], 8, [(2, 0, 1), (2, 1, 1), (3, 3, 1), (4, 1, 1), (4, 2, 1), (6, 2, 2), (5, 1, 1)]),
  ([1, 3, 1, 0, 1, 0, 1], 8, [(2, 0, 1), (2, 1, 1), (3, 3, 1), (4, 1, 2), (6, 2, 2), (5, 2, 1)]),
  ([1, 3, 1, 0, 1, 1, 0], 8, [(2, 0, 1), (2, 2, 1), (3, 3, 1), (4, 1, 1), (4, 2, 1), (6, 1, 2), (5, 2, 1)]),
  ([1, 3, 1, 0, 2, 0, 0], 8, [(2, 0, 1), (2, 1, 1), (2, 2, 1), (4, 2, 2), (6, 1, 2), (5, 5, 1)]),
  ([1, 3, 1, 1, 0, 0, 1], 8, [(2, 1, 1), (2, 2, 1), (3, 0, 1), (4, 1, 2), (6, 2, 1), (6, 3, 1), (5, 2, 1)]),
  ([1, 3, 1, 1, 0, 1, 0], 8, [(2, 1, 1), (2, 2, 1), (3, 0, 1), (4, 1, 2), (6, 2, 1), (6, 3, 1), (5, 2, 1)]),
  ([1, 3, 1, 1, 1, 0, 0], 24, [(2, 1, 2), (2, 2, 5), (3, 2, 1), (4, 0, 2), (4, 2, 3), (4, 3, 2), (6, 1, 7), (5, 4, 1), (5, 5, 1)]),
  ([1, 3, 1, 2, 0, 0, 0], 11, [(2, 1, 1), (2, 2, 2), (4, 2, 2), (4, 3, 1), (4, 4, 1), (6, 1, 3), (6, 5, 1)]),
  ([1, 3, 2, 0, 0, 0, 1], 22, [(0, 4, 3), (2, 1, 3), (3, 0, 2), (3, 3, 2), (3, 4, 1), (4, 3, 3), (6, 1, 2), (6, 4, 1), (5, 2, 5)]),
  ([1, 3, 2, 0, 0, 1, 0], 22, [(0, 4, 3), (2, 1, 3), (3, 0, 2), (3, 3, 3), (4, 1, 2), (4, 4, 1), (6, 3, 2), (6, 4, 1), (5, 2, 5)]),
  ([1, 3, 2, 0, 1, 0, 0], 22, [(0, 4, 3), (2, 2, 3), (3, 0, 1), (3, 3, 4), (4, 0, 1), (4, 1, 2), (6, 1, 3), (5, 2, 2), (5, 3, 1), (5, 4, 2)]),
  ([1, 3, 2, 1, 0, 0, 0], 44, [(0, 4, 3), (0, 5, 3), (2, 1, 2), (2, 2, 4), (3, 0, 1), (3, 2, 6), (4, 1, 8), (4, 3, 1), (6, 3, 9), (5, 4, 7)]),
  ([1, 3, 3, 0, 0, 0, 0], 26, [(0, 4, 4), (2, 0, 1), (2, 1, 3), (3, 2, 5), (4, 4, 1), (4, 5, 3), (6, 1, 2), (6, 5, 2), (5, 3, 5)]),
  ([1, 4, 0, 0, 0, 0, 2], 3, [(2, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 4, 0, 0, 0, 1, 1], 3, [(2, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([1, 4, 0, 0, 0, 2, 0], 3, [(2, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 4, 0, 0, 1, 0, 1], 3, [(2, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 4, 0, 0, 1, 1, 0], 3, [(2, 1, 1), (4, 3, 1), (6, 2, 1)]),
  ([1, 4, 0, 0, 2, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 4, 0, 1, 0, 0, 1], 3, [(2, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([1, 4, 0, 1, 0, 1, 0], 3, [(2, 2, 1), (4, 1, 1), (6, 3, 1)]),
  ([1, 4, 0, 1, 1, 0, 0], 3, [(2, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([1, 4, 0, 2, 0, 0, 0], 3, [(2, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([1, 4, 1, 0, 0, 0, 1], 3, [(2, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([1, 4, 1, 0, 0, 1, 0], 3, [(2, 2, 1), (4, 1, 1), (6, 3, 1)]),
  ([1, 4, 1, 0, 1, 0, 0], 3, [(2, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([1, 4, 1, 1, 0, 0, 0], 3, [(2, 3, 1), (4, 1, 1), (6, 2, 1)]),
  ([1, 4, 2, 0, 0, 0, 0], 3, [(2, 2, 1), (4, 3, 1), (6, 1, 1)])
]
theorem chunk_038_checked : chunk_038.all checkCertificate = true := by
  decide

def chunk_039 : List Certificate := [
  ([1, 5, 0, 0, 0, 0, 1], 3, [(2, 2, 1), (4, 3, 1), (6, 1, 1)]),
  ([1, 5, 0, 0, 0, 1, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 5, 0, 0, 1, 0, 0], 3, [(2, 3, 1), (4, 2, 1), (6, 1, 1)]),
  ([1, 5, 0, 1, 0, 0, 0], 3, [(2, 1, 1), (4, 2, 1), (6, 3, 1)]),
  ([1, 5, 1, 0, 0, 0, 0], 3, [(2, 2, 1), (4, 1, 1), (6, 3, 1)]),
  ([1, 6, 0, 0, 0, 0, 0], 3, [(2, 5, 1), (4, 2, 1), (6, 1, 1)]),
  ([2, 0, 0, 0, 0, 0, 5], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([2, 0, 0, 0, 0, 1, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([2, 0, 0, 0, 0, 2, 3], 28, [(1, 0, 2), (3, 2, 2), (3, 3, 2), (0, 4, 2), (2, 4, 5), (0, 5, 3), (1, 5, 3), (3, 5, 1), (4, 6, 5), (5, 0, 3)]),
  ([2, 0, 0, 0, 0, 3, 2], 14, [(1, 0, 1), (1, 2, 1), (1, 3, 3), (3, 3, 2), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 2, 4)]),
  ([2, 0, 0, 0, 0, 4, 1], 3, [(1, 2, 1), (3, 4, 1), (6, 3, 1)]),
  ([2, 0, 0, 0, 0, 5, 0], 9, [(3, 2, 2), (1, 3, 1), (3, 3, 1), (1, 5, 2), (6, 4, 2), (5, 0, 1)]),
  ([2, 0, 0, 0, 1, 0, 4], 3, [(2, 3, 1), (4, 4, 1), (0, 5, 1)]),
  ([2, 0, 0, 0, 1, 1, 3], 11, [(2, 0, 1), (2, 3, 1), (0, 4, 3), (1, 4, 1), (3, 5, 1), (4, 5, 3), (2, 6, 1)]),
  ([2, 0, 0, 0, 1, 2, 2], 35, [(1, 0, 4), (1, 3, 4), (3, 4, 7), (0, 5, 3), (2, 5, 3), (3, 5, 1), (1, 6, 2), (3, 6, 2), (4, 6, 3), (6, 3, 3), (5, 0, 3)]),
  ([2, 0, 0, 0, 1, 3, 1], 11, [(1, 0, 1), (1, 3, 2), (3, 3, 2), (3, 4, 1), (1, 5, 1), (3, 6, 1), (6, 4, 3)]),
  ([2, 0, 0, 0, 1, 4, 0], 3, [(3, 3, 1), (1, 5, 1), (6, 4, 1)]),
  ([2, 0, 0, 0, 2, 0, 3], 16, [(2, 2, 2), (0, 3, 1), (1, 3, 1), (1, 4, 2), (4, 4, 1), (0, 5, 2), (3, 5, 1), (2, 6, 1), (3, 6, 2), (5, 0, 3)]),
  ([2, 0, 0, 0, 2, 1, 2], 21, [(2, 2, 3), (0, 3, 2), (1, 3, 1), (1, 4, 3), (0, 5, 2), (2, 5, 1), (3, 5, 1), (3, 6, 3), (4, 6, 1), (5, 0, 4)]),
  ([2, 0, 0, 0, 2, 2, 1], 42, [(2, 2, 6), (0, 3, 5), (1, 3, 2), (1, 4, 6), (0, 5, 3), (2, 5, 2), (3, 5, 2), (3, 6, 6), (4, 6, 1), (6, 4, 1), (5, 0, 7), (5, 2, 1)]),
  ([2, 0, 0, 0, 2, 3, 0], 16, [(2, 2, 2), (0, 3, 3), (3, 4, 3), (1, 5, 1), (2, 5, 1), (6, 5, 1), (1, 6, 2), (5, 0, 2), (5, 2, 1)]),
  ([2, 0, 0, 0, 3, 0, 2], 16, [(2, 0, 1), (0, 2, 3), (2, 2, 3), (0, 3, 1), (2, 4, 1), (0, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([2, 0, 0, 0, 3, 1, 1], 16, [(2, 0, 1), (0, 2, 3), (2, 2, 3), (0, 3, 1), (2, 4, 1), (0, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([2, 0, 0, 0, 3, 2, 0], 16, [(2, 0, 1), (0, 2, 3), (2, 2, 3), (0, 3, 1), (2, 4, 1), (0, 5, 1), (2, 6, 1), (5, 3, 5)]),
  ([2, 0, 0, 0, 4, 0, 1], 3, [(2, 3, 1), (0, 4, 1), (5, 2, 1)]),
  ([2, 0, 0, 0, 4, 1, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 2, 1)]),
  ([2, 0, 0, 0, 5, 0, 0], 3, [(0, 2, 1), (2, 3, 1), (5, 5, 1)]),
  ([2, 0, 0, 1, 0, 0, 4], 3, [(2, 3, 1), (0, 4, 1), (4, 5, 1)]),
  ([2, 0, 0, 1, 0, 1, 3], 11, [(1, 0, 1), (3, 3, 1), (0, 4, 3), (4, 4, 1), (2, 5, 3), (4, 5, 1), (4, 6, 1)]),
  ([2, 0, 0, 1, 0, 2, 2], 35, [(1, 0, 4), (3, 3, 4), (1, 4, 6), (3, 4, 1), (0, 5, 3), (3, 5, 4), (2, 6, 3), (3, 6, 1), (4, 6, 3), (6, 3, 3), (5, 0, 3)]),
  ([2, 0, 0, 1, 0, 3, 1], 11, [(1, 0, 1), (1, 3, 2), (3, 3, 2), (1, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 3)]),
  ([2, 0, 0, 1, 0, 4, 0], 3, [(1, 3, 1), (3, 5, 1), (6, 4, 1)])
]
theorem chunk_039_checked : chunk_039.all checkCertificate = true := by
  decide

def chunk_040 : List Certificate := [
  ([2, 0, 0, 1, 1, 0, 3], 32, [(1, 0, 2), (1, 2, 2), (1, 3, 2), (3, 4, 5), (4, 4, 2), (0, 5, 5), (4, 5, 2), (1, 6, 1), (2, 6, 5), (4, 6, 1), (5, 0, 5)]),
  ([2, 0, 0, 1, 1, 1, 2], 18, [(1, 0, 3), (3, 4, 3), (0, 5, 2), (2, 5, 1), (4, 5, 2), (1, 6, 2), (2, 6, 1), (3, 6, 2), (5, 0, 2)]),
  ([2, 0, 0, 1, 1, 2, 1], 28, [(1, 0, 3), (2, 4, 1), (3, 4, 4), (4, 0, 2), (0, 5, 2), (3, 5, 5), (1, 6, 6), (2, 6, 1), (6, 4, 2), (5, 0, 2)]),
  ([2, 0, 0, 1, 1, 3, 0], 8, [(1, 2, 1), (3, 4, 2), (1, 5, 2), (6, 3, 1), (6, 4, 1), (6, 5, 1)]),
  ([2, 0, 0, 1, 2, 0, 2], 33, [(2, 0, 2), (1, 2, 1), (3, 0, 5), (4, 0, 1), (2, 4, 3), (0, 5, 5), (4, 5, 3), (1, 6, 7), (4, 6, 1), (5, 2, 2), (5, 3, 3)]),
  ([2, 0, 0, 1, 2, 1, 1], 5, [(1, 0, 1), (2, 4, 1), (0, 5, 1), (3, 6, 1), (5, 3, 1)]),
  ([2, 0, 0, 1, 2, 2, 0], 18, [(1, 2, 3), (0, 3, 2), (2, 4, 1), (1, 5, 2), (2, 5, 1), (3, 5, 2), (6, 3, 1), (6, 4, 4), (5, 3, 2)]),
  ([2, 0, 0, 1, 3, 0, 1], 8, [(1, 0, 1), (0, 3, 1), (2, 3, 2), (0, 4, 1), (5, 2, 1), (5, 4, 2)]),
  ([2, 0, 0, 1, 3, 1, 0], 8, [(1, 0, 1), (2, 3, 2), (0, 4, 2), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([2, 0, 0, 1, 4, 0, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 5, 1)]),
  ([2, 0, 0, 2, 0, 0, 3], 22, [(1, 0, 2), (1, 2, 2), (0, 4, 1), (1, 4, 1), (3, 4, 3), (0, 5, 2), (4, 5, 3), (2, 6, 3), (4, 6, 2), (5, 0, 3)]),
  ([2, 0, 0, 2, 0, 1, 2], 18, [(1, 0, 3), (1, 2, 1), (2, 4, 2), (0, 5, 2), (4, 5, 3), (1, 6, 1), (3, 6, 4), (5, 0, 2)]),
  ([2, 0, 0, 2, 0, 2, 1], 28, [(1, 0, 3), (3, 4, 5), (4, 0, 2), (0, 5, 2), (1, 5, 1), (3, 5, 4), (1, 6, 5), (2, 6, 2), (6, 4, 2), (5, 0, 2)]),
  ([2, 0, 0, 2, 0, 3, 0], 8, [(1, 2, 1), (3, 4, 2), (1, 5, 2), (6, 3, 1), (6, 4, 1), (6, 5, 1)]),
  ([2, 0, 0, 2, 1, 0, 2], 18, [(1, 0, 1), (2, 0, 2), (4, 2, 3), (0, 5, 2), (1, 5, 1), (3, 5, 2), (1, 6, 3), (4, 6, 2), (5, 0, 2)]),
  ([2, 0, 0, 2, 1, 1, 1], 42, [(1, 0, 2), (2, 0, 5), (0, 3, 5), (1, 4, 3), (4, 2, 3), (1, 5, 7), (3, 6, 5), (4, 6, 2), (6, 2, 1), (6, 4, 4), (5, 2, 3), (5, 3, 2)]),
  ([2, 0, 0, 2, 1, 2, 0], 28, [(0, 3, 2), (1, 3, 2), (1, 4, 7), (2, 5, 2), (3, 5, 2), (4, 2, 2), (6, 2, 5), (6, 3, 1), (6, 5, 3), (5, 3, 2)]),
  ([2, 0, 0, 2, 2, 0, 1], 18, [(1, 0, 1), (0, 3, 2), (1, 3, 3), (1, 4, 1), (2, 4, 2), (4, 0, 2), (6, 2, 2), (5, 2, 3), (5, 4, 2)]),
  ([2, 0, 0, 2, 2, 1, 0], 18, [(1, 0, 1), (1, 3, 1), (1, 4, 3), (2, 4, 2), (0, 5, 2), (4, 2, 2), (6, 3, 4), (5, 2, 3)]),
  ([2, 0, 0, 2, 3, 0, 0], 11, [(1, 0, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 3), (5, 5, 4)]),
  ([2, 0, 0, 3, 0, 0, 2], 11, [(1, 0, 1), (1, 2, 1), (4, 2, 3), (4, 3, 1), (1, 5, 1), (1, 6, 1), (6, 3, 3)]),
  ([2, 0, 0, 3, 0, 1, 1], 8, [(1, 0, 1), (1, 2, 1), (4, 2, 2), (4, 3, 1), (1, 6, 1), (6, 3, 2)]),
  ([2, 0, 0, 3, 0, 2, 0], 16, [(1, 0, 1), (1, 2, 2), (1, 4, 1), (1, 5, 1), (4, 2, 4), (4, 3, 1), (6, 3, 5), (1, 6, 1)]),
  ([2, 0, 0, 3, 1, 0, 1], 8, [(1, 0, 1), (1, 3, 1), (1, 4, 1), (4, 3, 2), (6, 2, 2), (5, 2, 1)]),
  ([2, 0, 0, 3, 1, 1, 0], 8, [(1, 0, 1), (1, 3, 1), (1, 4, 1), (4, 2, 2), (6, 3, 2), (5, 2, 1)]),
  ([2, 0, 0, 3, 2, 0, 0], 11, [(1, 0, 1), (1, 3, 2), (1, 4, 1), (4, 2, 3), (6, 2, 1), (6, 3, 2), (5, 5, 1)]),
  ([2, 0, 0, 4, 0, 0, 1], 3, [(1, 3, 1), (4, 4, 1), (6, 2, 1)]),
  ([2, 0, 0, 4, 0, 1, 0], 3, [(1, 4, 1), (4, 2, 1), (6, 3, 1)]),
  ([2, 0, 0, 4, 1, 0, 0], 3, [(1, 3, 1), (4, 4, 1), (6, 2, 1)]),
  ([2, 0, 0, 5, 0, 0, 0], 9, [(1, 3, 1), (1, 5, 2), (3, 0, 1), (4, 2, 1), (4, 3, 1), (6, 2, 1), (6, 4, 1), (5, 4, 1)]),
  ([2, 0, 1, 0, 0, 0, 4], 3, [(4, 3, 1), (0, 4, 1), (2, 5, 1)]),
  ([2, 0, 1, 0, 0, 1, 3], 22, [(3, 0, 2), (1, 3, 2), (0, 4, 1), (2, 4, 3), (3, 4, 1), (0, 5, 2), (1, 5, 3), (3, 6, 2), (4, 6, 3), (5, 0, 3)])
]
theorem chunk_040_checked : chunk_040.all checkCertificate = true := by
  decide

def chunk_041 : List Certificate := [
  ([2, 0, 1, 0, 0, 2, 2], 35, [(1, 0, 4), (0, 3, 3), (1, 3, 1), (2, 4, 3), (3, 4, 4), (1, 5, 5), (3, 5, 2), (3, 6, 4), (4, 6, 3), (6, 3, 3), (5, 0, 3)]),
  ([2, 0, 1, 0, 0, 3, 1], 11, [(1, 0, 1), (1, 3, 3), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 3)]),
  ([2, 0, 1, 0, 0, 4, 0], 3, [(3, 3, 1), (1, 5, 1), (6, 4, 1)]),
  ([2, 0, 1, 0, 1, 0, 3], 8, [(1, 0, 1), (4, 4, 2), (0, 5, 1), (3, 5, 1), (2, 6, 2), (5, 0, 1)]),
  ([2, 0, 1, 0, 1, 1, 2], 18, [(1, 0, 3), (1, 4, 2), (3, 4, 1), (0, 5, 2), (3, 5, 3), (2, 6, 2), (3, 6, 1), (4, 6, 2), (5, 0, 2)]),
  ([2, 0, 1, 0, 1, 2, 1], 28, [(1, 0, 4), (3, 0, 1), (3, 4, 5), (0, 5, 2), (2, 5, 2), (3, 5, 3), (1, 6, 5), (4, 6, 2), (6, 4, 2), (5, 0, 2)]),
  ([2, 0, 1, 0, 1, 3, 0], 8, [(1, 0, 1), (3, 4, 1), (1, 5, 2), (3, 5, 1), (6, 4, 2), (3, 6, 1)]),
  ([2, 0, 1, 0, 2, 0, 2], 5, [(3, 0, 1), (0, 4, 1), (2, 5, 1), (1, 6, 1), (5, 3, 1)]),
  ([2, 0, 1, 0, 2, 1, 1], 5, [(3, 0, 1), (2, 4, 1), (0, 5, 1), (1, 6, 1), (5, 3, 1)]),
  ([2, 0, 1, 0, 2, 2, 0], 5, [(3, 0, 1), (2, 4, 1), (0, 5, 1), (1, 6, 1), (5, 3, 1)]),
  ([2, 0, 1, 0, 3, 0, 1], 21, [(2, 0, 1), (0, 3, 6), (2, 3, 2), (2, 4, 3), (0, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1), (5, 4, 5)]),
  ([2, 0, 1, 0, 3, 1, 0], 21, [(2, 0, 1), (0, 3, 7), (2, 4, 4), (2, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 4)]),
  ([2, 0, 1, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 5, 1)]),
  ([2, 0, 1, 1, 0, 0, 3], 32, [(1, 0, 2), (3, 1, 2), (4, 2, 2), (2, 4, 5), (3, 4, 1), (4, 4, 1), (0, 5, 5), (3, 5, 2), (1, 6, 3), (4, 6, 4), (5, 0, 5)]),
  ([2, 0, 1, 1, 0, 1, 2], 18, [(1, 0, 3), (1, 4, 2), (3, 4, 1), (0, 5, 2), (3, 5, 3), (2, 6, 2), (3, 6, 1), (4, 6, 2), (5, 0, 2)]),
  ([2, 0, 1, 1, 0, 2, 1], 28, [(1, 0, 5), (1, 4, 1), (3, 4, 4), (0, 5, 2), (3, 5, 5), (1, 6, 3), (2, 6, 2), (4, 6, 2), (6, 4, 2), (5, 0, 2)]),
  ([2, 0, 1, 1, 0, 3, 0], 8, [(1, 0, 1), (1, 4, 1), (3, 4, 2), (1, 5, 1), (6, 5, 2), (3, 6, 1)]),
  ([2, 0, 1, 1, 1, 0, 2], 42, [(0, 3, 2), (3, 0, 7), (4, 2, 3), (2, 4, 3), (0, 5, 5), (1, 5, 1), (4, 5, 4), (1, 6, 6), (2, 6, 4), (5, 0, 3), (5, 1, 3), (5, 3, 1)]),
  ([2, 0, 1, 1, 1, 1, 1], 35, [(0, 2, 2), (1, 3, 1), (3, 0, 9), (2, 4, 2), (4, 2, 2), (1, 5, 4), (1, 6, 4), (6, 4, 2), (5, 0, 2), (5, 1, 4), (5, 3, 3)]),
  ([2, 0, 1, 1, 1, 2, 0], 35, [(1, 3, 3), (3, 0, 9), (2, 4, 2), (0, 5, 2), (1, 5, 2), (4, 2, 2), (6, 4, 2), (1, 6, 4), (5, 0, 2), (5, 1, 4), (5, 2, 2), (5, 3, 1)]),
  ([2, 0, 1, 1, 2, 0, 1], 14, [(0, 3, 4), (1, 4, 1), (2, 4, 1), (3, 1, 1), (4, 0, 1), (6, 4, 1), (5, 2, 4), (5, 4, 1)]),
  ([2, 0, 1, 1, 2, 1, 0], 14, [(0, 3, 4), (1, 4, 1), (2, 4, 1), (3, 1, 1), (4, 0, 1), (6, 4, 1), (5, 2, 4), (5, 4, 1)]),
  ([2, 0, 1, 1, 3, 0, 0], 8, [(1, 0, 1), (0, 3, 1), (0, 4, 1), (2, 4, 2), (5, 5, 3)]),
  ([2, 0, 1, 2, 0, 0, 2], 18, [(0, 3, 1), (3, 0, 2), (4, 0, 3), (0, 5, 1), (1, 5, 2), (4, 5, 2), (1, 6, 3), (2, 6, 2), (5, 3, 2)]),
  ([2, 0, 1, 2, 0, 1, 1], 14, [(1, 0, 1), (1, 3, 1), (3, 0, 4), (4, 2, 1), (1, 5, 1), (1, 6, 1), (6, 4, 1), (5, 1, 2), (5, 2, 1), (5, 3, 1)]),
  ([2, 0, 1, 2, 0, 2, 0], 14, [(1, 0, 1), (1, 3, 1), (3, 0, 4), (1, 5, 1), (4, 2, 1), (6, 4, 1), (1, 6, 1), (5, 1, 2), (5, 2, 1), (5, 3, 1)]),
  ([2, 0, 1, 2, 1, 0, 1], 21, [(0, 3, 6), (1, 4, 2), (3, 1, 1), (4, 0, 1), (4, 2, 1), (4, 3, 1), (3, 6, 1), (6, 4, 2), (5, 2, 6)]),
  ([2, 0, 1, 2, 1, 1, 0], 7, [(0, 3, 2), (1, 4, 1), (4, 3, 1), (6, 4, 1), (5, 2, 2)]),
  ([2, 0, 1, 2, 2, 0, 0], 18, [(1, 0, 3), (0, 3, 1), (0, 4, 1), (1, 4, 2), (2, 5, 2), (4, 3, 2), (6, 3, 2), (5, 4, 2), (5, 5, 3)]),
  ([2, 0, 1, 3, 0, 0, 1], 16, [(1, 0, 1), (1, 3, 1), (1, 4, 2), (4, 1, 1), (4, 3, 5), (1, 6, 1), (6, 2, 1), (6, 4, 4)]),
  ([2, 0, 1, 3, 0, 1, 0], 21, [(1, 0, 1), (1, 4, 5), (4, 1, 1), (4, 3, 6), (6, 2, 1), (6, 3, 2), (6, 4, 3), (6, 5, 1), (1, 6, 1)]),
  ([2, 0, 1, 3, 1, 0, 0], 8, [(1, 0, 1), (1, 4, 2), (4, 3, 1), (4, 4, 1), (6, 3, 2), (5, 5, 1)])
]
theorem chunk_041_checked : chunk_041.all checkCertificate = true := by
  decide

def chunk_042 : List Certificate := [
  ([2, 0, 1, 4, 0, 0, 0], 3, [(1, 5, 1), (4, 4, 1), (6, 3, 1)]),
  ([2, 0, 2, 0, 0, 0, 3], 16, [(0, 2, 1), (3, 1, 2), (3, 2, 1), (4, 4, 3), (0, 5, 2), (1, 5, 1), (2, 6, 3), (5, 0, 3)]),
  ([2, 0, 2, 0, 0, 1, 2], 18, [(1, 0, 1), (3, 0, 2), (1, 4, 3), (0, 5, 2), (3, 5, 3), (1, 6, 1), (2, 6, 2), (4, 6, 2), (5, 0, 2)]),
  ([2, 0, 2, 0, 0, 2, 1], 28, [(1, 0, 3), (0, 4, 1), (3, 4, 4), (4, 0, 2), (0, 5, 1), (1, 5, 6), (2, 6, 2), (3, 6, 5), (6, 4, 2), (5, 0, 2)]),
  ([2, 0, 2, 0, 0, 3, 0], 16, [(3, 0, 1), (3, 1, 1), (3, 2, 1), (1, 4, 4), (3, 4, 2), (1, 5, 1), (6, 5, 5), (3, 6, 1)]),
  ([2, 0, 2, 0, 1, 0, 2], 5, [(0, 2, 1), (3, 0, 1), (2, 5, 1), (4, 6, 1), (5, 1, 1)]),
  ([2, 0, 2, 0, 1, 1, 1], 21, [(0, 2, 2), (3, 0, 6), (3, 2, 1), (1, 4, 1), (4, 2, 1), (2, 5, 1), (2, 6, 1), (6, 2, 1), (5, 1, 6), (5, 2, 1)]),
  ([2, 0, 2, 0, 1, 2, 0], 21, [(0, 2, 2), (3, 0, 6), (3, 2, 1), (1, 4, 1), (2, 5, 1), (4, 2, 1), (6, 2, 1), (2, 6, 1), (5, 1, 6), (5, 2, 1)]),
  ([2, 0, 2, 0, 2, 0, 1], 14, [(0, 3, 3), (0, 4, 1), (1, 4, 1), (3, 1, 1), (4, 0, 1), (2, 5, 1), (3, 6, 1), (6, 4, 1), (5, 2, 4)]),
  ([2, 0, 2, 0, 2, 1, 0], 7, [(0, 3, 2), (1, 4, 1), (3, 0, 1), (5, 2, 2), (5, 4, 1)]),
  ([2, 0, 2, 0, 3, 0, 0], 8, [(0, 2, 1), (0, 3, 1), (0, 4, 1), (2, 4, 2), (5, 5, 3)]),
  ([2, 0, 2, 1, 0, 0, 2], 33, [(0, 2, 2), (1, 0, 2), (0, 3, 3), (3, 0, 5), (2, 5, 5), (4, 5, 3), (1, 6, 3), (4, 6, 5), (5, 0, 1), (5, 1, 3), (5, 2, 1)]),
  ([2, 0, 2, 1, 0, 1, 1], 35, [(0, 2, 2), (1, 0, 2), (3, 0, 9), (3, 2, 4), (4, 2, 2), (2, 5, 1), (2, 6, 1), (6, 2, 2), (5, 1, 11), (5, 2, 1)]),
  ([2, 0, 2, 1, 0, 2, 0], 35, [(0, 2, 2), (1, 0, 2), (3, 0, 9), (3, 2, 4), (2, 5, 1), (4, 2, 2), (6, 2, 2), (2, 6, 1), (5, 1, 11), (5, 2, 1)]),
  ([2, 0, 2, 1, 1, 0, 1], 14, [(0, 3, 3), (1, 4, 1), (3, 0, 1), (3, 1, 2), (4, 0, 1), (6, 4, 1), (5, 2, 5)]),
  ([2, 0, 2, 1, 1, 1, 0], 21, [(0, 3, 6), (1, 4, 2), (3, 0, 1), (3, 1, 1), (4, 2, 1), (4, 3, 1), (6, 4, 2), (5, 2, 6), (5, 4, 1)]),
  ([2, 0, 2, 1, 2, 0, 0], 28, [(0, 2, 5), (0, 3, 3), (0, 4, 1), (1, 5, 2), (2, 5, 2), (3, 2, 2), (4, 3, 2), (6, 3, 2), (5, 4, 6), (5, 5, 3)]),
  ([2, 0, 2, 2, 0, 0, 1], 33, [(0, 3, 5), (1, 4, 5), (3, 1, 2), (3, 2, 3), (4, 0, 3), (4, 1, 1), (4, 4, 1), (4, 6, 3), (6, 3, 3), (6, 4, 2), (5, 2, 5)]),
  ([2, 0, 2, 2, 0, 1, 0], 5, [(1, 0, 1), (3, 1, 1), (4, 4, 1), (6, 3, 1), (5, 2, 1)]),
  ([2, 0, 2, 2, 1, 0, 0], 18, [(0, 2, 3), (0, 3, 1), (0, 4, 1), (1, 4, 2), (3, 2, 2), (4, 3, 2), (6, 3, 2), (5, 4, 2), (5, 5, 3)]),
  ([2, 0, 2, 3, 0, 0, 0], 40, [(0, 2, 7), (1, 5, 6), (3, 0, 2), (3, 1, 2), (3, 2, 2), (4, 3, 3), (4, 5, 3), (6, 3, 6), (5, 4, 9)]),
  ([2, 0, 3, 0, 0, 0, 2], 8, [(0, 3, 1), (3, 0, 1), (3, 3, 1), (4, 2, 1), (0, 5, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1)]),
  ([2, 0, 3, 0, 0, 1, 1], 8, [(0, 2, 2), (3, 0, 1), (3, 3, 2), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([2, 0, 3, 0, 0, 2, 0], 8, [(0, 2, 2), (3, 0, 1), (3, 3, 2), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([2, 0, 3, 0, 1, 0, 1], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([2, 0, 3, 0, 1, 1, 0], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([2, 0, 3, 0, 2, 0, 0], 8, [(0, 2, 3), (3, 3, 2), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([2, 0, 3, 1, 0, 0, 1], 16, [(0, 3, 5), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (4, 4, 1), (3, 6, 1), (5, 2, 5)]),
  ([2, 0, 3, 1, 0, 1, 0], 8, [(0, 3, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 2, 3)]),
  ([2, 0, 3, 1, 1, 0, 0], 8, [(0, 2, 3), (3, 3, 2), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([2, 0, 3, 2, 0, 0, 0], 16, [(0, 2, 5), (1, 5, 1), (3, 3, 3), (4, 3, 2), (4, 5, 1), (6, 5, 1), (5, 4, 3)]),
  ([2, 0, 4, 0, 0, 0, 1], 3, [(0, 3, 1), (3, 4, 1), (5, 2, 1)])
]
theorem chunk_042_checked : chunk_042.all checkCertificate = true := by
  decide

def chunk_043 : List Certificate := [
  ([2, 0, 4, 0, 0, 1, 0], 3, [(0, 3, 1), (3, 4, 1), (5, 2, 1)]),
  ([2, 0, 4, 0, 1, 0, 0], 3, [(0, 2, 1), (3, 4, 1), (5, 3, 1)]),
  ([2, 0, 4, 1, 0, 0, 0], 3, [(0, 2, 1), (3, 3, 1), (5, 4, 1)]),
  ([2, 0, 5, 0, 0, 0, 0], 3, [(0, 2, 1), (3, 4, 1), (5, 3, 1)]),
  ([2, 1, 0, 0, 0, 0, 4], 3, [(0, 3, 1), (2, 4, 1), (4, 5, 1)]),
  ([2, 1, 0, 0, 0, 1, 3], 22, [(2, 0, 3), (3, 0, 1), (0, 4, 3), (3, 4, 2), (1, 5, 3), (2, 5, 2), (4, 6, 5), (5, 0, 1), (5, 1, 2)]),
  ([2, 1, 0, 0, 0, 2, 2], 35, [(1, 0, 4), (1, 3, 4), (2, 4, 3), (3, 4, 4), (0, 5, 3), (1, 5, 2), (3, 5, 2), (3, 6, 4), (4, 6, 3), (6, 3, 3), (5, 0, 3)]),
  ([2, 1, 0, 0, 0, 3, 1], 11, [(1, 0, 1), (1, 3, 3), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 3)]),
  ([2, 1, 0, 0, 0, 4, 0], 3, [(1, 4, 1), (3, 5, 1), (6, 3, 1)]),
  ([2, 1, 0, 0, 1, 0, 3], 22, [(1, 0, 2), (3, 1, 2), (1, 4, 1), (4, 4, 4), (0, 5, 3), (2, 5, 1), (4, 5, 1), (2, 6, 4), (3, 6, 1), (5, 0, 3)]),
  ([2, 1, 0, 0, 1, 1, 2], 18, [(1, 0, 3), (3, 1, 2), (2, 4, 1), (0, 5, 2), (2, 5, 3), (3, 6, 1), (4, 6, 4), (5, 0, 2)]),
  ([2, 1, 0, 0, 1, 2, 1], 28, [(2, 0, 2), (3, 0, 3), (1, 4, 5), (0, 5, 2), (1, 5, 4), (3, 5, 1), (3, 6, 5), (4, 6, 2), (6, 4, 2), (5, 0, 2)]),
  ([2, 1, 0, 0, 1, 3, 0], 16, [(2, 0, 1), (3, 1, 1), (1, 4, 4), (3, 5, 4), (6, 3, 1), (6, 4, 2), (6, 5, 2), (1, 6, 1)]),
  ([2, 1, 0, 0, 2, 0, 2], 18, [(1, 0, 2), (2, 1, 1), (4, 0, 3), (0, 5, 2), (3, 5, 2), (4, 5, 1), (2, 6, 4), (4, 6, 1), (5, 1, 2)]),
  ([2, 1, 0, 0, 2, 1, 1], 5, [(2, 3, 1), (1, 4, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1)]),
  ([2, 1, 0, 0, 2, 2, 0], 33, [(2, 3, 6), (3, 0, 3), (0, 4, 5), (1, 4, 3), (1, 5, 2), (3, 5, 1), (6, 5, 5), (2, 6, 2), (3, 6, 1), (5, 1, 3), (5, 3, 2)]),
  ([2, 1, 0, 0, 3, 0, 1], 8, [(2, 0, 1), (2, 1, 1), (0, 3, 2), (2, 3, 1), (5, 4, 3)]),
  ([2, 1, 0, 0, 3, 1, 0], 8, [(2, 0, 1), (2, 1, 1), (0, 3, 2), (2, 3, 1), (5, 4, 3)]),
  ([2, 1, 0, 0, 4, 0, 0], 3, [(2, 3, 1), (0, 4, 1), (5, 5, 1)]),
  ([2, 1, 0, 1, 0, 0, 3], 22, [(1, 0, 2), (3, 1, 2), (1, 4, 1), (4, 4, 4), (0, 5, 3), (2, 5, 1), (4, 5, 1), (2, 6, 4), (3, 6, 1), (5, 0, 3)]),
  ([2, 1, 0, 1, 0, 1, 2], 18, [(1, 0, 3), (3, 1, 2), (2, 4, 1), (0, 5, 2), (2, 5, 3), (3, 6, 1), (4, 6, 4), (5, 0, 2)]),
  ([2, 1, 0, 1, 0, 2, 1], 28, [(2, 0, 2), (3, 0, 3), (0, 4, 2), (1, 4, 3), (1, 5, 6), (3, 5, 1), (3, 6, 5), (4, 6, 2), (6, 4, 2), (5, 0, 2)]),
  ([2, 1, 0, 1, 0, 3, 0], 8, [(3, 0, 1), (1, 4, 1), (3, 4, 2), (1, 5, 1), (6, 5, 2), (1, 6, 1)]),
  ([2, 1, 0, 1, 1, 0, 2], 18, [(2, 0, 3), (2, 1, 1), (3, 0, 2), (0, 5, 2), (1, 5, 2), (2, 5, 1), (4, 6, 5), (5, 1, 2)]),
  ([2, 1, 0, 1, 1, 1, 1], 21, [(1, 0, 1), (1, 3, 2), (3, 0, 5), (1, 4, 2), (2, 5, 2), (4, 6, 2), (6, 2, 2), (5, 0, 1), (5, 1, 4)]),
  ([2, 1, 0, 1, 1, 2, 0], 28, [(1, 0, 1), (3, 0, 7), (1, 4, 3), (2, 5, 3), (4, 0, 2), (6, 3, 2), (1, 6, 3), (5, 1, 5), (5, 2, 2)]),
  ([2, 1, 0, 1, 2, 0, 1], 7, [(1, 0, 1), (2, 1, 1), (0, 3, 1), (3, 0, 1), (5, 2, 1), (5, 4, 2)]),
  ([2, 1, 0, 1, 2, 1, 0], 7, [(1, 0, 1), (2, 1, 1), (0, 3, 1), (3, 0, 1), (5, 2, 1), (5, 4, 2)]),
  ([2, 1, 0, 1, 3, 0, 0], 8, [(1, 0, 1), (0, 3, 1), (0, 4, 1), (2, 4, 2), (5, 5, 3)]),
  ([2, 1, 0, 2, 0, 0, 2], 18, [(1, 0, 3), (3, 0, 2), (4, 3, 1), (0, 5, 2), (4, 5, 3), (2, 6, 4), (4, 6, 1), (5, 1, 2)]),
  ([2, 1, 0, 2, 0, 1, 1], 14, [(1, 0, 3), (3, 0, 3), (4, 2, 1), (4, 3, 1), (2, 6, 2), (4, 6, 1), (5, 1, 3)]),
  ([2, 1, 0, 2, 0, 2, 0], 14, [(1, 3, 1), (3, 0, 3), (1, 4, 2), (2, 5, 1), (4, 3, 1), (6, 2, 2), (6, 5, 1), (5, 1, 3)])
]
theorem chunk_043_checked : chunk_043.all checkCertificate = true := by
  decide

def chunk_044 : List Certificate := [
  ([2, 1, 0, 2, 1, 0, 1], 7, [(1, 0, 1), (0, 3, 1), (3, 0, 1), (4, 1, 1), (2, 6, 1), (5, 2, 1), (5, 4, 1)]),
  ([2, 1, 0, 2, 1, 1, 0], 14, [(1, 0, 1), (0, 3, 1), (2, 1, 1), (3, 0, 3), (1, 5, 1), (4, 1, 1), (6, 3, 1), (1, 6, 1), (5, 2, 2), (5, 4, 2)]),
  ([2, 1, 0, 2, 2, 0, 0], 18, [(1, 0, 3), (0, 3, 1), (0, 4, 1), (1, 4, 2), (2, 5, 2), (4, 3, 2), (6, 3, 2), (5, 4, 2), (5, 5, 3)]),
  ([2, 1, 0, 3, 0, 0, 1], 8, [(1, 3, 1), (1, 4, 1), (4, 0, 1), (4, 4, 2), (1, 6, 1), (6, 3, 2)]),
  ([2, 1, 0, 3, 0, 1, 0], 21, [(1, 3, 1), (1, 4, 4), (1, 5, 1), (4, 0, 1), (4, 1, 1), (4, 2, 1), (4, 4, 4), (6, 3, 7), (1, 6, 1)]),
  ([2, 1, 0, 3, 1, 0, 0], 8, [(1, 0, 1), (1, 3, 1), (1, 4, 1), (4, 4, 2), (6, 3, 2), (5, 5, 1)]),
  ([2, 1, 0, 4, 0, 0, 0], 3, [(1, 5, 1), (4, 4, 1), (6, 3, 1)]),
  ([2, 1, 1, 0, 0, 0, 3], 22, [(3, 0, 1), (3, 1, 2), (4, 0, 1), (0, 4, 3), (1, 4, 2), (1, 5, 1), (4, 5, 4), (2, 6, 5), (5, 0, 3)]),
  ([2, 1, 1, 0, 0, 1, 2], 36, [(3, 1, 5), (4, 0, 6), (1, 4, 1), (0, 5, 4), (1, 5, 3), (4, 5, 3), (1, 6, 1), (2, 6, 9), (5, 0, 4)]),
  ([2, 1, 1, 0, 0, 2, 1], 28, [(1, 0, 4), (3, 0, 1), (0, 4, 2), (2, 4, 2), (3, 4, 1), (3, 5, 7), (1, 6, 5), (4, 6, 2), (6, 4, 2), (5, 0, 2)]),
  ([2, 1, 1, 0, 0, 3, 0], 16, [(3, 0, 1), (3, 1, 1), (3, 2, 1), (1, 4, 1), (1, 5, 3), (3, 5, 3), (6, 4, 5), (1, 6, 1)]),
  ([2, 1, 1, 0, 1, 0, 2], 18, [(1, 0, 2), (2, 0, 1), (3, 0, 2), (4, 1, 1), (0, 5, 2), (4, 5, 3), (2, 6, 4), (4, 6, 1), (5, 1, 2)]),
  ([2, 1, 1, 0, 1, 1, 1], 14, [(1, 0, 1), (3, 0, 4), (2, 4, 1), (4, 2, 1), (2, 5, 1), (1, 6, 1), (6, 2, 1), (5, 1, 4)]),
  ([2, 1, 1, 0, 1, 2, 0], 14, [(1, 0, 1), (3, 0, 4), (2, 4, 1), (2, 5, 1), (4, 2, 1), (6, 2, 1), (1, 6, 1), (5, 1, 4)]),
  ([2, 1, 1, 0, 2, 0, 1], 28, [(1, 0, 1), (2, 1, 2), (0, 3, 1), (0, 4, 1), (3, 0, 9), (4, 1, 2), (1, 6, 2), (5, 1, 3), (5, 2, 7)]),
  ([2, 1, 1, 0, 2, 1, 0], 7, [(1, 0, 1), (3, 0, 2), (3, 1, 1), (5, 1, 1), (5, 2, 2)]),
  ([2, 1, 1, 0, 3, 0, 0], 16, [(2, 0, 1), (2, 1, 1), (0, 3, 1), (0, 4, 4), (2, 4, 2), (2, 5, 1), (5, 2, 1), (5, 5, 5)]),
  ([2, 1, 1, 1, 0, 0, 2], 18, [(1, 0, 2), (2, 0, 1), (3, 0, 2), (4, 1, 1), (0, 5, 2), (4, 5, 3), (2, 6, 4), (4, 6, 1), (5, 1, 2)]),
  ([2, 1, 1, 1, 0, 1, 1], 28, [(1, 0, 3), (3, 0, 7), (3, 2, 3), (4, 2, 2), (2, 5, 1), (2, 6, 1), (6, 2, 2), (5, 1, 9)]),
  ([2, 1, 1, 1, 0, 2, 0], 14, [(1, 0, 1), (3, 0, 4), (3, 2, 1), (2, 5, 1), (4, 2, 1), (6, 2, 1), (1, 6, 1), (5, 1, 4)]),
  ([2, 1, 1, 1, 1, 0, 1], 21, [(1, 0, 1), (0, 3, 1), (2, 1, 1), (3, 0, 7), (4, 1, 2), (1, 6, 2), (5, 1, 2), (5, 2, 5)]),
  ([2, 1, 1, 1, 1, 1, 0], 7, [(1, 0, 1), (3, 0, 2), (3, 1, 1), (5, 1, 1), (5, 2, 2)]),
  ([2, 1, 1, 1, 2, 0, 0], 42, [(1, 0, 5), (0, 3, 5), (2, 0, 2), (2, 1, 3), (3, 1, 4), (3, 2, 1), (4, 2, 5), (6, 3, 2), (6, 5, 3), (5, 2, 1), (5, 4, 7), (5, 5, 4)]),
  ([2, 1, 1, 2, 0, 0, 1], 5, [(1, 4, 1), (3, 0, 1), (4, 1, 1), (6, 3, 1), (5, 2, 1)]),
  ([2, 1, 1, 2, 0, 1, 0], 5, [(1, 4, 1), (3, 0, 1), (4, 1, 1), (6, 3, 1), (5, 2, 1)]),
  ([2, 1, 1, 2, 1, 0, 0], 5, [(1, 0, 1), (3, 1, 1), (4, 4, 1), (6, 2, 1), (5, 3, 1)]),
  ([2, 1, 1, 3, 0, 0, 0], 8, [(1, 0, 1), (1, 5, 1), (3, 1, 1), (4, 3, 1), (4, 4, 1), (6, 2, 1), (6, 5, 1), (5, 4, 1)]),
  ([2, 1, 2, 0, 0, 0, 2], 21, [(0, 3, 3), (3, 0, 4), (4, 2, 2), (0, 5, 1), (2, 5, 3), (1, 6, 1), (2, 6, 1), (4, 6, 2), (5, 1, 3), (5, 2, 1)]),
  ([2, 1, 2, 0, 0, 1, 1], 28, [(0, 3, 2), (1, 0, 2), (2, 0, 2), (3, 0, 3), (3, 2, 1), (3, 3, 5), (4, 2, 2), (6, 2, 2), (5, 1, 7), (5, 2, 2)]),
  ([2, 1, 2, 0, 0, 2, 0], 28, [(0, 3, 2), (1, 0, 2), (2, 0, 2), (3, 0, 3), (3, 2, 1), (3, 3, 5), (4, 2, 2), (6, 2, 2), (5, 1, 7), (5, 2, 2)]),
  ([2, 1, 2, 0, 1, 0, 1], 28, [(0, 3, 2), (1, 0, 2), (2, 1, 2), (3, 0, 5), (3, 1, 3), (3, 3, 1), (4, 3, 2), (6, 3, 2), (5, 1, 2), (5, 2, 7)]),
  ([2, 1, 2, 0, 1, 1, 0], 28, [(0, 3, 2), (1, 0, 2), (2, 1, 2), (3, 0, 5), (3, 1, 1), (3, 3, 3), (4, 1, 2), (6, 3, 2), (5, 1, 2), (5, 2, 7)])
]
theorem chunk_044_checked : chunk_044.all checkCertificate = true := by
  decide

def chunk_045 : List Certificate := [
  ([2, 1, 2, 0, 2, 0, 0], 28, [(0, 3, 2), (1, 0, 2), (2, 0, 2), (3, 1, 2), (3, 2, 7), (4, 3, 2), (6, 3, 2), (5, 0, 3), (5, 1, 5), (5, 3, 1)]),
  ([2, 1, 2, 1, 0, 0, 1], 28, [(0, 3, 2), (1, 0, 2), (2, 1, 2), (3, 0, 5), (3, 1, 4), (4, 1, 1), (4, 3, 1), (6, 3, 2), (5, 2, 7), (5, 3, 2)]),
  ([2, 1, 2, 1, 0, 1, 0], 28, [(0, 3, 2), (1, 0, 2), (2, 1, 2), (3, 0, 5), (3, 1, 4), (4, 3, 2), (6, 3, 2), (5, 1, 1), (5, 2, 7), (5, 3, 1)]),
  ([2, 1, 2, 1, 1, 0, 0], 28, [(0, 3, 2), (1, 0, 2), (2, 1, 2), (3, 1, 5), (3, 2, 1), (3, 3, 3), (4, 0, 2), (6, 3, 2), (5, 0, 3), (5, 2, 6)]),
  ([2, 1, 2, 2, 0, 0, 0], 21, [(0, 3, 1), (1, 0, 2), (1, 5, 2), (3, 0, 1), (3, 1, 3), (4, 2, 3), (4, 5, 1), (6, 3, 3), (6, 5, 1), (5, 4, 4)]),
  ([2, 1, 3, 0, 0, 0, 1], 11, [(0, 3, 1), (0, 4, 2), (3, 0, 1), (3, 1, 1), (3, 4, 2), (5, 2, 1), (5, 3, 3)]),
  ([2, 1, 3, 0, 0, 1, 0], 11, [(0, 3, 3), (3, 0, 1), (3, 3, 1), (3, 4, 2), (5, 1, 1), (5, 2, 1), (5, 4, 2)]),
  ([2, 1, 3, 0, 1, 0, 0], 11, [(0, 3, 3), (3, 1, 1), (3, 3, 1), (3, 4, 2), (5, 0, 1), (5, 2, 1), (5, 4, 2)]),
  ([2, 1, 3, 1, 0, 0, 0], 11, [(0, 3, 3), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (5, 4, 4)]),
  ([2, 1, 4, 0, 0, 0, 0], 3, [(0, 4, 1), (3, 5, 1), (5, 3, 1)]),
  ([2, 2, 0, 0, 0, 0, 3], 14, [(3, 0, 1), (3, 1, 1), (4, 2, 1), (1, 4, 1), (4, 4, 2), (0, 5, 2), (1, 5, 1), (2, 6, 3), (5, 0, 2)]),
  ([2, 2, 0, 0, 0, 1, 2], 35, [(2, 1, 4), (3, 1, 3), (4, 0, 4), (4, 2, 4), (0, 5, 3), (1, 5, 3), (4, 5, 1), (2, 6, 6), (4, 6, 1), (6, 2, 3), (5, 0, 3)]),
  ([2, 2, 0, 0, 0, 2, 1], 21, [(2, 0, 3), (2, 2, 1), (3, 1, 4), (1, 4, 1), (4, 2, 1), (1, 5, 3), (4, 6, 3), (6, 2, 2), (6, 4, 2), (5, 0, 1)]),
  ([2, 2, 0, 0, 0, 3, 0], 8, [(2, 2, 1), (3, 1, 1), (1, 5, 2), (4, 0, 1), (6, 4, 2), (3, 6, 1)]),
  ([2, 2, 0, 0, 1, 0, 2], 35, [(1, 0, 3), (2, 2, 3), (3, 0, 3), (4, 0, 1), (4, 1, 4), (4, 2, 1), (0, 5, 3), (4, 5, 4), (2, 6, 7), (6, 2, 3), (5, 1, 3)]),
  ([2, 2, 0, 0, 1, 1, 1], 18, [(1, 0, 2), (2, 2, 2), (3, 0, 2), (4, 0, 1), (4, 1, 3), (4, 2, 1), (2, 6, 3), (6, 2, 2), (5, 1, 2)]),
  ([2, 2, 0, 0, 1, 2, 0], 33, [(2, 0, 3), (2, 2, 2), (3, 0, 5), (2, 4, 3), (1, 5, 2), (4, 1, 3), (4, 2, 2), (6, 2, 4), (6, 5, 1), (1, 6, 3), (5, 1, 5)]),
  ([2, 2, 0, 0, 2, 0, 1], 18, [(1, 0, 2), (2, 0, 1), (2, 1, 3), (2, 4, 1), (3, 1, 2), (4, 0, 2), (6, 4, 2), (5, 2, 5)]),
  ([2, 2, 0, 0, 2, 1, 0], 18, [(1, 0, 2), (2, 1, 4), (2, 4, 1), (3, 0, 2), (4, 0, 1), (4, 1, 1), (6, 4, 2), (5, 2, 5)]),
  ([2, 2, 0, 0, 3, 0, 0], 11, [(2, 0, 1), (2, 2, 1), (2, 4, 2), (0, 5, 3), (5, 1, 1), (5, 4, 2), (5, 5, 1)]),
  ([2, 2, 0, 1, 0, 0, 2], 35, [(1, 0, 3), (2, 2, 3), (3, 0, 3), (4, 0, 1), (4, 1, 4), (4, 2, 1), (0, 5, 3), (4, 5, 4), (2, 6, 7), (6, 2, 3), (5, 1, 3)]),
  ([2, 2, 0, 1, 0, 1, 1], 18, [(1, 0, 2), (2, 2, 2), (3, 0, 2), (4, 0, 1), (4, 1, 3), (4, 2, 1), (2, 6, 3), (6, 2, 2), (5, 1, 2)]),
  ([2, 2, 0, 1, 0, 2, 0], 5, [(3, 0, 1), (2, 5, 1), (4, 1, 1), (6, 2, 1), (1, 6, 1)]),
  ([2, 2, 0, 1, 1, 0, 1], 18, [(1, 0, 2), (2, 1, 2), (3, 0, 2), (4, 0, 1), (4, 1, 3), (4, 2, 1), (2, 6, 3), (6, 2, 2), (5, 2, 2)]),
  ([2, 2, 0, 1, 1, 1, 0], 42, [(1, 0, 5), (2, 1, 6), (3, 0, 5), (1, 5, 2), (4, 2, 7), (6, 3, 3), (6, 4, 3), (6, 5, 1), (2, 6, 1), (3, 6, 2), (5, 1, 4), (5, 2, 3)]),
  ([2, 2, 0, 1, 2, 0, 0], 18, [(1, 0, 2), (2, 0, 2), (2, 1, 3), (3, 2, 2), (4, 1, 2), (6, 2, 2), (5, 0, 1), (5, 2, 1), (5, 5, 3)]),
  ([2, 2, 0, 2, 0, 0, 1], 18, [(1, 0, 2), (2, 1, 5), (4, 0, 3), (4, 2, 1), (3, 6, 2), (4, 6, 1), (6, 2, 2), (5, 2, 2)]),
  ([2, 2, 0, 2, 0, 1, 0], 5, [(1, 0, 1), (3, 1, 1), (4, 4, 1), (6, 3, 1), (5, 2, 1)]),
  ([2, 2, 0, 2, 1, 0, 0], 33, [(1, 0, 5), (2, 2, 5), (3, 1, 2), (3, 2, 3), (4, 1, 5), (6, 3, 2), (6, 4, 3), (5, 0, 3), (5, 1, 1), (5, 3, 1), (5, 5, 3)]),
  ([2, 2, 0, 3, 0, 0, 0], 8, [(1, 0, 1), (1, 5, 1), (3, 1, 1), (4, 2, 1), (4, 5, 1), (6, 3, 1), (6, 4, 1), (5, 4, 1)]),
  ([2, 2, 1, 0, 0, 0, 2], 35, [(1, 0, 3), (2, 2, 3), (3, 0, 3), (4, 0, 1), (4, 1, 4), (4, 2, 1), (0, 5, 3), (4, 5, 4), (2, 6, 7), (6, 2, 3), (5, 1, 3)]),
  ([2, 2, 1, 0, 0, 1, 1], 54, [(1, 0, 4), (2, 2, 8), (3, 0, 11), (3, 1, 2), (4, 2, 7), (4, 3, 1), (1, 6, 2), (6, 3, 6), (5, 1, 13)])
]
theorem chunk_045_checked : chunk_045.all checkCertificate = true := by
  decide

def chunk_046 : List Certificate := [
  ([2, 2, 1, 0, 0, 2, 0], 18, [(1, 0, 2), (2, 2, 2), (3, 0, 3), (3, 3, 2), (4, 2, 2), (6, 2, 1), (6, 3, 1), (5, 1, 5)]),
  ([2, 2, 1, 0, 1, 0, 1], 18, [(1, 0, 1), (2, 1, 3), (3, 0, 4), (4, 1, 2), (4, 3, 1), (1, 6, 1), (6, 2, 1), (6, 3, 1), (5, 2, 4)]),
  ([2, 2, 1, 0, 1, 1, 0], 18, [(1, 0, 2), (2, 1, 2), (3, 0, 3), (3, 1, 2), (4, 1, 1), (4, 3, 1), (6, 3, 2), (5, 2, 5)]),
  ([2, 2, 1, 0, 2, 0, 0], 18, [(1, 0, 2), (2, 0, 1), (2, 1, 4), (3, 2, 2), (4, 1, 1), (4, 2, 1), (6, 2, 2), (5, 0, 2), (5, 5, 3)]),
  ([2, 2, 1, 1, 0, 0, 1], 18, [(1, 0, 1), (2, 1, 3), (3, 0, 4), (4, 1, 2), (4, 3, 1), (1, 6, 1), (6, 2, 1), (6, 3, 1), (5, 2, 4)]),
  ([2, 2, 1, 1, 0, 1, 0], 18, [(1, 0, 2), (2, 1, 2), (3, 0, 3), (3, 1, 1), (3, 3, 1), (4, 1, 2), (6, 3, 2), (5, 2, 5)]),
  ([2, 2, 1, 1, 1, 0, 0], 18, [(1, 0, 2), (2, 1, 2), (3, 1, 3), (3, 2, 1), (3, 3, 1), (4, 2, 2), (6, 2, 2), (5, 0, 3), (5, 3, 2)]),
  ([2, 2, 1, 2, 0, 0, 0], 42, [(1, 0, 5), (0, 5, 1), (1, 5, 3), (2, 1, 1), (3, 0, 2), (3, 1, 6), (4, 2, 2), (4, 3, 6), (6, 2, 5), (6, 5, 3), (5, 3, 1), (5, 4, 7)]),
  ([2, 2, 2, 0, 0, 0, 1], 35, [(0, 4, 3), (1, 0, 3), (2, 1, 3), (3, 0, 4), (3, 1, 1), (3, 3, 4), (3, 4, 1), (4, 1, 3), (6, 3, 3), (5, 2, 7), (5, 4, 3)]),
  ([2, 2, 2, 0, 0, 1, 0], 35, [(0, 4, 3), (1, 0, 3), (2, 1, 3), (3, 0, 4), (3, 3, 4), (3, 4, 2), (4, 1, 3), (6, 3, 3), (5, 1, 1), (5, 2, 7), (5, 4, 2)]),
  ([2, 2, 2, 0, 1, 0, 0], 35, [(0, 4, 3), (1, 0, 3), (2, 1, 3), (3, 1, 4), (3, 2, 4), (3, 3, 2), (4, 0, 3), (6, 2, 3), (5, 0, 1), (5, 3, 5), (5, 4, 4)]),
  ([2, 2, 2, 1, 0, 0, 0], 35, [(0, 4, 3), (1, 0, 3), (2, 2, 3), (3, 0, 4), (3, 1, 4), (3, 2, 2), (4, 1, 3), (6, 2, 2), (6, 3, 1), (5, 3, 6), (5, 4, 4)]),
  ([2, 2, 3, 0, 0, 0, 0], 14, [(0, 4, 2), (2, 0, 1), (2, 2, 1), (3, 4, 1), (3, 5, 2), (4, 1, 1), (4, 5, 1), (6, 2, 2), (5, 3, 3)]),
  ([2, 3, 0, 0, 0, 0, 2], 14, [(1, 0, 1), (2, 3, 3), (3, 2, 1), (4, 0, 2), (4, 1, 1), (1, 5, 1), (3, 6, 1), (6, 2, 2), (5, 1, 2)]),
  ([2, 3, 0, 0, 0, 1, 1], 22, [(1, 0, 2), (2, 3, 5), (3, 2, 2), (4, 0, 3), (4, 1, 2), (1, 6, 1), (3, 6, 1), (6, 2, 3), (5, 1, 3)]),
  ([2, 3, 0, 0, 0, 2, 0], 8, [(1, 0, 1), (2, 3, 2), (3, 2, 1), (4, 0, 1), (6, 2, 1), (5, 1, 2)]),
  ([2, 3, 0, 0, 1, 0, 1], 11, [(1, 0, 1), (2, 3, 3), (3, 0, 1), (4, 1, 2), (4, 6, 1), (6, 2, 2), (5, 2, 1)]),
  ([2, 3, 0, 0, 1, 1, 0], 8, [(1, 0, 1), (2, 1, 1), (2, 3, 1), (3, 1, 1), (4, 0, 1), (6, 3, 1), (5, 2, 2)]),
  ([2, 3, 0, 0, 2, 0, 0], 22, [(1, 0, 3), (2, 0, 1), (2, 1, 2), (2, 3, 2), (3, 1, 3), (4, 0, 1), (4, 2, 2), (6, 3, 3), (5, 2, 3), (5, 5, 2)]),
  ([2, 3, 0, 1, 0, 0, 1], 11, [(1, 0, 1), (2, 3, 3), (3, 0, 1), (4, 1, 2), (4, 6, 1), (6, 2, 2), (5, 2, 1)]),
  ([2, 3, 0, 1, 0, 1, 0], 8, [(2, 3, 3), (4, 0, 1), (4, 1, 1), (6, 2, 2), (5, 2, 1)]),
  ([2, 3, 0, 1, 1, 0, 0], 32, [(1, 0, 5), (2, 1, 5), (3, 1, 2), (3, 2, 3), (4, 2, 3), (4, 4, 2), (6, 2, 1), (6, 3, 4), (5, 0, 2), (5, 3, 3), (5, 5, 2)]),
  ([2, 3, 0, 2, 0, 0, 0], 8, [(1, 0, 1), (2, 1, 1), (2, 3, 1), (3, 0, 1), (4, 1, 1), (6, 3, 1), (5, 2, 2)]),
  ([2, 3, 1, 0, 0, 0, 1], 44, [(1, 0, 6), (2, 3, 7), (3, 1, 8), (4, 0, 4), (4, 1, 2), (4, 2, 1), (3, 6, 1), (6, 3, 3), (6, 4, 3), (5, 2, 9)]),
  ([2, 3, 1, 0, 0, 1, 0], 22, [(1, 0, 3), (2, 3, 3), (3, 1, 4), (3, 3, 1), (4, 0, 2), (4, 1, 1), (6, 3, 1), (6, 4, 2), (5, 2, 5)]),
  ([2, 3, 1, 0, 1, 0, 0], 22, [(1, 0, 3), (2, 2, 3), (3, 0, 1), (3, 3, 2), (3, 4, 2), (4, 0, 1), (4, 1, 2), (6, 3, 3), (5, 1, 3), (5, 2, 2)]),
  ([2, 3, 1, 1, 0, 0, 0], 22, [(1, 0, 3), (2, 3, 3), (3, 0, 2), (3, 1, 3), (4, 1, 2), (4, 3, 1), (6, 2, 2), (6, 3, 1), (5, 2, 3), (5, 4, 2)]),
  ([2, 3, 2, 0, 0, 0, 0], 14, [(1, 0, 2), (2, 0, 1), (2, 2, 1), (3, 1, 3), (4, 2, 2), (6, 4, 1), (6, 5, 1), (5, 3, 3)]),
  ([2, 4, 0, 0, 0, 0, 1], 3, [(2, 3, 1), (4, 2, 1), (6, 4, 1)]),
  ([2, 4, 0, 0, 0, 1, 0], 3, [(2, 3, 1), (4, 2, 1), (6, 4, 1)]),
  ([2, 4, 0, 0, 1, 0, 0], 3, [(2, 3, 1), (4, 4, 1), (6, 2, 1)]),
  ([2, 4, 0, 1, 0, 0, 0], 3, [(2, 3, 1), (4, 4, 1), (6, 2, 1)])
]
theorem chunk_046_checked : chunk_046.all checkCertificate = true := by
  decide

def chunk_047 : List Certificate := [
  ([2, 4, 1, 0, 0, 0, 0], 3, [(2, 4, 1), (4, 2, 1), (6, 3, 1)]),
  ([2, 5, 0, 0, 0, 0, 0], 3, [(2, 2, 1), (4, 4, 1), (6, 3, 1)]),
  ([3, 0, 0, 0, 0, 0, 4], 6, [(4, 1, 1), (2, 3, 1), (0, 4, 1), (3, 5, 1), (1, 6, 1), (5, 0, 1)]),
  ([3, 0, 0, 0, 0, 1, 3], 26, [(1, 0, 5), (3, 1, 1), (0, 3, 1), (0, 4, 1), (2, 4, 4), (0, 5, 2), (3, 5, 3), (3, 6, 1), (4, 6, 4), (5, 1, 4)]),
  ([3, 0, 0, 0, 0, 2, 2], 42, [(1, 0, 3), (3, 1, 3), (1, 3, 3), (4, 1, 4), (0, 4, 4), (3, 4, 3), (1, 5, 3), (2, 5, 4), (1, 6, 2), (3, 6, 5), (6, 3, 4), (5, 0, 4)]),
  ([3, 0, 0, 0, 0, 3, 1], 14, [(1, 0, 1), (3, 1, 1), (1, 3, 4), (3, 3, 1), (3, 4, 1), (3, 5, 1), (3, 6, 1), (6, 4, 4)]),
  ([3, 0, 0, 0, 0, 4, 0], 3, [(3, 4, 1), (1, 5, 1), (6, 3, 1)]),
  ([3, 0, 0, 0, 1, 0, 3], 20, [(3, 1, 4), (4, 0, 1), (1, 4, 1), (2, 4, 3), (0, 5, 3), (1, 5, 1), (1, 6, 2), (4, 6, 2), (5, 0, 3)]),
  ([3, 0, 0, 0, 1, 1, 2], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 0, 0, 1, 2, 1], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 0, 0, 1, 3, 0], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 0, 0, 2, 0, 2], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 0, 2, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 0, 2, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 0, 3, 0, 1], 8, [(1, 1, 1), (0, 3, 2), (3, 0, 1), (2, 5, 1), (2, 6, 1), (5, 4, 2)]),
  ([3, 0, 0, 0, 3, 1, 0], 16, [(2, 0, 2), (2, 1, 3), (0, 3, 3), (1, 3, 1), (3, 0, 1), (5, 3, 1), (5, 4, 5)]),
  ([3, 0, 0, 0, 4, 0, 0], 3, [(0, 3, 1), (2, 4, 1), (5, 5, 1)]),
  ([3, 0, 0, 1, 0, 0, 3], 20, [(1, 0, 1), (3, 1, 4), (0, 4, 3), (1, 4, 1), (1, 5, 1), (2, 5, 3), (1, 6, 1), (4, 6, 3), (5, 0, 3)]),
  ([3, 0, 0, 1, 0, 1, 2], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 0, 1, 0, 2, 1], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 0, 1, 0, 3, 0], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 0, 1, 1, 0, 2], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 1, 1, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 1, 1, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 1, 2, 0, 1], 16, [(1, 0, 4), (1, 3, 1), (3, 0, 2), (3, 1, 2), (1, 5, 1), (3, 6, 1), (5, 1, 4), (5, 4, 1)]),
  ([3, 0, 0, 1, 2, 1, 0], 16, [(1, 0, 2), (1, 1, 2), (1, 3, 1), (3, 0, 4), (1, 5, 1), (3, 6, 1), (5, 1, 4), (5, 4, 1)]),
  ([3, 0, 0, 1, 3, 0, 0], 11, [(1, 0, 1), (2, 1, 1), (0, 3, 1), (0, 4, 2), (2, 4, 2), (5, 5, 4)]),
  ([3, 0, 0, 2, 0, 0, 2], 11, [(1, 0, 4), (3, 1, 1), (4, 3, 1), (3, 5, 1), (3, 6, 1), (5, 1, 3)]),
  ([3, 0, 0, 2, 0, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 2, 0, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 0, 2, 1, 0, 1], 16, [(1, 0, 4), (1, 3, 1), (3, 0, 2), (3, 1, 2), (1, 5, 1), (3, 6, 1), (5, 1, 4), (5, 4, 1)]),
  ([3, 0, 0, 2, 1, 1, 0], 8, [(1, 0, 1), (1, 1, 2), (3, 0, 2), (5, 1, 1), (5, 3, 1), (5, 4, 1)])
]
theorem chunk_047_checked : chunk_047.all checkCertificate = true := by
  decide

def chunk_048 : List Certificate := [
  ([3, 0, 0, 2, 2, 0, 0], 11, [(1, 0, 2), (1, 1, 1), (1, 3, 1), (3, 1, 3), (5, 0, 2), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 0, 3, 0, 0, 1], 11, [(1, 0, 1), (1, 1, 1), (1, 3, 1), (3, 0, 2), (4, 1, 2), (1, 6, 1), (6, 3, 1), (5, 4, 2)]),
  ([3, 0, 0, 3, 0, 1, 0], 16, [(1, 0, 2), (1, 1, 2), (1, 3, 2), (3, 0, 3), (4, 1, 3), (6, 3, 1), (5, 4, 3)]),
  ([3, 0, 0, 3, 1, 0, 0], 11, [(1, 0, 4), (3, 1, 3), (5, 1, 1), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 0, 4, 0, 0, 0], 3, [(1, 4, 1), (4, 5, 1), (6, 3, 1)]),
  ([3, 0, 1, 0, 0, 0, 3], 20, [(1, 0, 1), (3, 1, 4), (0, 4, 3), (1, 4, 1), (1, 5, 1), (4, 5, 3), (1, 6, 1), (2, 6, 3), (5, 0, 3)]),
  ([3, 0, 1, 0, 0, 1, 2], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 1, 0, 0, 2, 1], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 1, 0, 0, 3, 0], 11, [(1, 0, 1), (3, 1, 4), (1, 4, 1), (1, 5, 1), (1, 6, 1), (5, 0, 3)]),
  ([3, 0, 1, 0, 1, 0, 2], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 1, 0, 1, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 1, 0, 1, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 1, 0, 2, 0, 1], 21, [(1, 0, 1), (1, 1, 4), (3, 0, 7), (1, 5, 1), (1, 6, 1), (5, 1, 4), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 0, 1, 0, 2, 1, 0], 21, [(1, 1, 4), (1, 4, 1), (3, 0, 7), (1, 5, 1), (1, 6, 1), (5, 0, 1), (5, 1, 4), (5, 2, 1), (5, 3, 1)]),
  ([3, 0, 1, 0, 3, 0, 0], 8, [(1, 0, 3), (3, 1, 2), (5, 1, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 1, 1, 0, 0, 2], 24, [(1, 0, 8), (3, 1, 2), (3, 2, 1), (4, 0, 1), (4, 3, 1), (3, 5, 2), (3, 6, 2), (5, 1, 7)]),
  ([3, 0, 1, 1, 0, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 1, 1, 0, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 0, 1, 1, 1, 0, 1], 21, [(1, 0, 1), (1, 1, 4), (3, 0, 7), (1, 5, 1), (1, 6, 1), (5, 1, 4), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 0, 1, 1, 1, 1, 0], 21, [(1, 0, 1), (1, 1, 4), (3, 0, 7), (1, 5, 1), (1, 6, 1), (5, 1, 4), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 0, 1, 1, 2, 0, 0], 8, [(1, 0, 3), (3, 1, 2), (5, 1, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 1, 2, 0, 0, 1], 16, [(1, 0, 1), (1, 1, 3), (3, 0, 5), (4, 1, 1), (1, 6, 1), (5, 1, 2), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 0, 1, 2, 0, 1, 0], 21, [(1, 0, 1), (1, 1, 4), (3, 0, 7), (1, 5, 1), (1, 6, 1), (5, 1, 4), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 0, 1, 2, 1, 0, 0], 8, [(1, 0, 3), (3, 1, 2), (5, 1, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 1, 3, 0, 0, 0], 8, [(1, 0, 2), (1, 5, 1), (3, 1, 1), (4, 1, 1), (6, 5, 1), (5, 4, 2)]),
  ([3, 0, 2, 0, 0, 0, 2], 16, [(0, 3, 1), (2, 1, 1), (3, 0, 4), (3, 2, 1), (4, 0, 1), (1, 5, 2), (1, 6, 2), (5, 1, 4)]),
  ([3, 0, 2, 0, 0, 1, 1], 8, [(1, 1, 1), (3, 0, 3), (1, 5, 1), (1, 6, 1), (5, 1, 2)]),
  ([3, 0, 2, 0, 0, 2, 0], 8, [(1, 1, 1), (3, 0, 3), (1, 5, 1), (1, 6, 1), (5, 1, 2)]),
  ([3, 0, 2, 0, 1, 0, 1], 8, [(1, 1, 2), (3, 0, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([3, 0, 2, 0, 1, 1, 0], 8, [(1, 1, 2), (3, 0, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([3, 0, 2, 0, 2, 0, 0], 16, [(1, 0, 5), (3, 0, 1), (3, 1, 3), (3, 2, 1), (5, 1, 3), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 2, 1, 0, 0, 1], 8, [(1, 1, 2), (3, 0, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1)])
]
theorem chunk_048_checked : chunk_048.all checkCertificate = true := by
  decide

def chunk_049 : List Certificate := [
  ([3, 0, 2, 1, 0, 1, 0], 8, [(1, 1, 2), (3, 0, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([3, 0, 2, 1, 1, 0, 0], 16, [(1, 1, 5), (3, 0, 2), (3, 1, 1), (3, 2, 1), (3, 3, 1), (5, 0, 4), (5, 4, 1), (5, 5, 1)]),
  ([3, 0, 2, 2, 0, 0, 0], 8, [(1, 0, 1), (1, 5, 1), (3, 0, 1), (3, 1, 1), (4, 2, 1), (6, 3, 1), (5, 1, 1), (5, 4, 1)]),
  ([3, 0, 3, 0, 0, 0, 1], 11, [(1, 1, 3), (3, 0, 4), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 0, 3, 0, 0, 1, 0], 11, [(0, 3, 1), (1, 1, 2), (3, 0, 3), (3, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 2)]),
  ([3, 0, 3, 0, 1, 0, 0], 11, [(0, 3, 3), (3, 1, 1), (3, 3, 1), (3, 4, 2), (5, 0, 1), (5, 2, 1), (5, 4, 2)]),
  ([3, 0, 3, 1, 0, 0, 0], 11, [(0, 3, 3), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (5, 4, 4)]),
  ([3, 0, 4, 0, 0, 0, 0], 3, [(0, 4, 1), (3, 5, 1), (5, 3, 1)]),
  ([3, 1, 0, 0, 0, 0, 3], 26, [(1, 0, 1), (1, 1, 3), (2, 1, 2), (2, 2, 1), (0, 4, 4), (3, 4, 1), (4, 5, 5), (2, 6, 2), (3, 6, 3), (5, 0, 4)]),
  ([3, 1, 0, 0, 0, 1, 2], 11, [(1, 0, 1), (1, 1, 2), (2, 2, 1), (3, 1, 2), (4, 5, 1), (3, 6, 1), (5, 0, 3)]),
  ([3, 1, 0, 0, 0, 2, 1], 11, [(1, 0, 1), (1, 1, 2), (3, 1, 2), (3, 4, 1), (1, 5, 1), (3, 6, 1), (5, 0, 3)]),
  ([3, 1, 0, 0, 0, 3, 0], 11, [(1, 0, 1), (1, 1, 2), (3, 1, 2), (1, 4, 1), (3, 5, 1), (3, 6, 1), (5, 0, 3)]),
  ([3, 1, 0, 0, 1, 0, 2], 11, [(1, 0, 3), (2, 0, 1), (3, 2, 1), (4, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 3)]),
  ([3, 1, 0, 0, 1, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 1, 0, 0, 1, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 1, 0, 0, 2, 0, 1], 8, [(1, 0, 1), (1, 1, 1), (2, 1, 1), (3, 0, 2), (5, 1, 1), (5, 2, 1), (5, 4, 1)]),
  ([3, 1, 0, 0, 2, 1, 0], 8, [(1, 0, 1), (2, 1, 1), (1, 4, 1), (3, 0, 2), (5, 1, 2), (5, 2, 1)]),
  ([3, 1, 0, 0, 3, 0, 0], 11, [(2, 0, 1), (2, 1, 1), (2, 2, 1), (0, 4, 3), (2, 4, 1), (5, 5, 4)]),
  ([3, 1, 0, 1, 0, 0, 2], 11, [(1, 0, 3), (2, 0, 1), (3, 2, 1), (4, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 3)]),
  ([3, 1, 0, 1, 0, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 1, 0, 1, 0, 2, 0], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 1, 0, 1, 1, 0, 1], 8, [(1, 1, 2), (3, 0, 2), (4, 0, 1), (2, 6, 1), (5, 1, 1), (5, 2, 1)]),
  ([3, 1, 0, 1, 1, 1, 0], 21, [(1, 1, 5), (3, 0, 7), (1, 5, 1), (1, 6, 1), (5, 0, 1), (5, 1, 3), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 1, 0, 1, 2, 0, 0], 8, [(1, 0, 3), (3, 1, 2), (5, 1, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 1, 0, 2, 0, 0, 1], 8, [(1, 1, 1), (2, 0, 1), (3, 0, 2), (4, 1, 1), (1, 6, 1), (5, 1, 1), (5, 2, 1)]),
  ([3, 1, 0, 2, 0, 1, 0], 21, [(1, 0, 4), (1, 1, 2), (3, 1, 6), (1, 5, 1), (3, 6, 1), (5, 0, 4), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 1, 0, 2, 1, 0, 0], 8, [(1, 0, 3), (3, 1, 2), (5, 1, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 1, 0, 3, 0, 0, 0], 8, [(1, 0, 2), (1, 5, 1), (3, 1, 1), (4, 1, 1), (6, 5, 1), (5, 4, 2)]),
  ([3, 1, 1, 0, 0, 0, 2], 11, [(1, 0, 3), (3, 0, 1), (3, 2, 1), (4, 1, 1), (2, 5, 1), (3, 6, 1), (5, 1, 3)]),
  ([3, 1, 1, 0, 0, 1, 1], 8, [(1, 0, 3), (3, 1, 1), (3, 5, 1), (3, 6, 1), (5, 1, 2)]),
  ([3, 1, 1, 0, 0, 2, 0], 8, [(1, 0, 2), (3, 0, 1), (3, 2, 1), (3, 3, 1), (5, 1, 3)]),
  ([3, 1, 1, 0, 1, 0, 1], 8, [(1, 1, 2), (3, 0, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1)])
]
theorem chunk_049_checked : chunk_049.all checkCertificate = true := by
  decide

def chunk_050 : List Certificate := [
  ([3, 1, 1, 0, 1, 1, 0], 8, [(1, 1, 2), (3, 0, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1)]),
  ([3, 1, 1, 0, 2, 0, 0], 8, [(1, 0, 2), (2, 0, 1), (3, 1, 1), (3, 2, 1), (5, 1, 2), (5, 5, 1)]),
  ([3, 1, 1, 1, 0, 0, 1], 8, [(1, 0, 2), (2, 1, 1), (3, 1, 1), (4, 0, 1), (3, 6, 1), (5, 1, 1), (5, 2, 1)]),
  ([3, 1, 1, 1, 0, 1, 0], 8, [(1, 0, 2), (3, 0, 1), (3, 1, 1), (3, 3, 1), (5, 1, 2), (5, 2, 1)]),
  ([3, 1, 1, 1, 1, 0, 0], 16, [(1, 0, 5), (3, 0, 1), (3, 1, 3), (3, 2, 1), (5, 1, 3), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 1, 1, 2, 0, 0, 0], 8, [(1, 0, 1), (1, 5, 1), (3, 0, 1), (3, 2, 1), (4, 1, 1), (6, 3, 1), (5, 1, 1), (5, 4, 1)]),
  ([3, 1, 2, 0, 0, 0, 1], 11, [(1, 0, 3), (3, 1, 4), (5, 0, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 1, 2, 0, 0, 1, 0], 11, [(1, 0, 3), (3, 0, 1), (3, 1, 2), (3, 4, 1), (5, 1, 2), (5, 2, 1), (5, 3, 1)]),
  ([3, 1, 2, 0, 1, 0, 0], 11, [(1, 0, 3), (3, 0, 1), (3, 1, 3), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 1, 2, 1, 0, 0, 0], 11, [(1, 0, 3), (3, 0, 1), (3, 1, 2), (3, 2, 1), (5, 1, 2), (5, 3, 1), (5, 4, 1)]),
  ([3, 1, 3, 0, 0, 0, 0], 14, [(1, 1, 4), (3, 0, 5), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 2, 0, 0, 0, 0, 2], 14, [(1, 0, 3), (2, 3, 1), (3, 0, 2), (3, 1, 1), (3, 2, 1), (4, 5, 1), (1, 6, 1), (5, 1, 4)]),
  ([3, 2, 0, 0, 0, 1, 1], 11, [(1, 0, 3), (2, 3, 1), (3, 0, 1), (3, 1, 1), (3, 2, 1), (4, 6, 1), (5, 1, 3)]),
  ([3, 2, 0, 0, 0, 2, 0], 8, [(1, 0, 2), (2, 3, 1), (3, 0, 1), (3, 2, 1), (5, 1, 3)]),
  ([3, 2, 0, 0, 1, 0, 1], 11, [(1, 0, 2), (2, 3, 1), (3, 1, 2), (4, 0, 1), (4, 1, 1), (2, 6, 1), (6, 3, 1), (5, 2, 2)]),
  ([3, 2, 0, 0, 1, 1, 0], 8, [(1, 0, 1), (2, 3, 1), (3, 1, 2), (4, 0, 1), (6, 3, 1), (5, 2, 2)]),
  ([3, 2, 0, 0, 2, 0, 0], 11, [(1, 0, 3), (2, 0, 1), (3, 1, 2), (3, 2, 1), (5, 1, 2), (5, 3, 1), (5, 5, 1)]),
  ([3, 2, 0, 1, 0, 0, 1], 11, [(1, 0, 1), (2, 1, 1), (2, 3, 1), (3, 1, 2), (4, 0, 2), (1, 6, 1), (6, 3, 1), (5, 2, 2)]),
  ([3, 2, 0, 1, 0, 1, 0], 8, [(1, 1, 1), (2, 0, 1), (2, 3, 1), (3, 1, 1), (4, 0, 1), (6, 3, 1), (5, 2, 2)]),
  ([3, 2, 0, 1, 1, 0, 0], 16, [(1, 0, 5), (3, 0, 1), (3, 1, 3), (3, 2, 1), (5, 1, 3), (5, 3, 1), (5, 4, 1), (5, 5, 1)]),
  ([3, 2, 0, 2, 0, 0, 0], 24, [(1, 0, 7), (3, 0, 1), (3, 1, 6), (4, 1, 2), (6, 3, 1), (5, 2, 2), (5, 3, 1), (5, 4, 2), (5, 5, 2)]),
  ([3, 2, 1, 0, 0, 0, 1], 33, [(1, 0, 3), (1, 1, 1), (2, 3, 5), (3, 1, 7), (4, 0, 5), (1, 6, 1), (6, 3, 2), (6, 4, 2), (5, 2, 7)]),
  ([3, 2, 1, 0, 0, 1, 0], 22, [(1, 0, 2), (1, 1, 1), (2, 3, 3), (3, 1, 4), (3, 3, 1), (4, 0, 3), (6, 3, 1), (6, 4, 2), (5, 2, 5)]),
  ([3, 2, 1, 0, 1, 0, 0], 11, [(1, 0, 2), (2, 3, 1), (3, 0, 1), (3, 2, 2), (4, 1, 1), (6, 4, 1), (5, 1, 2), (5, 3, 1)]),
  ([3, 2, 1, 1, 0, 0, 0], 11, [(1, 1, 3), (3, 0, 4), (5, 1, 1), (5, 2, 1), (5, 3, 1), (5, 4, 1)]),
  ([3, 2, 2, 0, 0, 0, 0], 14, [(1, 0, 1), (1, 1, 1), (2, 0, 2), (3, 2, 3), (4, 1, 2), (6, 4, 1), (6, 5, 1), (5, 3, 3)]),
  ([3, 3, 0, 0, 0, 0, 1], 26, [(1, 1, 4), (2, 3, 5), (3, 0, 4), (4, 0, 1), (4, 1, 1), (4, 2, 1), (4, 4, 1), (4, 6, 1), (6, 4, 4), (5, 2, 4)]),
  ([3, 3, 0, 0, 0, 1, 0], 20, [(1, 0, 2), (1, 1, 1), (2, 3, 4), (3, 0, 2), (3, 4, 1), (4, 1, 3), (6, 4, 3), (5, 2, 4)]),
  ([3, 3, 0, 0, 1, 0, 0], 20, [(1, 0, 3), (2, 2, 3), (3, 2, 1), (3, 3, 1), (3, 4, 2), (4, 0, 1), (4, 4, 2), (6, 3, 3), (5, 1, 4)]),
  ([3, 3, 0, 1, 0, 0, 0], 20, [(1, 0, 2), (1, 1, 1), (2, 2, 4), (3, 0, 2), (3, 3, 1), (4, 1, 3), (6, 3, 3), (5, 4, 4)]),
  ([3, 3, 1, 0, 0, 0, 0], 26, [(1, 1, 4), (2, 0, 4), (3, 0, 1), (3, 1, 1), (3, 2, 1), (3, 4, 1), (3, 5, 1), (4, 2, 4), (6, 4, 4), (5, 3, 5)]),
  ([3, 4, 0, 0, 0, 0, 0], 9, [(1, 0, 1), (2, 5, 2), (3, 4, 1), (4, 1, 1), (4, 2, 1), (6, 3, 2), (5, 4, 1)])
]
theorem chunk_050_checked : chunk_050.all checkCertificate = true := by
  decide

def chunk_051 : List Certificate := [
  ([4, 0, 0, 0, 0, 0, 3], 6, [(3, 1, 1), (4, 0, 1), (1, 4, 1), (0, 5, 1), (2, 6, 1), (5, 2, 1)]),
  ([4, 0, 0, 0, 0, 1, 2], 3, [(1, 1, 1), (3, 2, 1), (5, 0, 1)]),
  ([4, 0, 0, 0, 0, 2, 1], 3, [(1, 1, 1), (3, 2, 1), (5, 0, 1)]),
  ([4, 0, 0, 0, 0, 3, 0], 3, [(1, 1, 1), (3, 2, 1), (5, 0, 1)]),
  ([4, 0, 0, 0, 1, 0, 2], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 0, 1, 1, 1], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 0, 1, 2, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 0, 2, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 0, 2, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 0, 3, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 1, 0, 0, 2], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 1, 0, 1, 1], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 1, 0, 2, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 1, 1, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 1, 1, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 1, 2, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 0, 2, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 2, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 2, 1, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 0, 3, 0, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 1, 0, 0, 0, 2], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 1, 0, 0, 1, 1], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 1, 0, 0, 2, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 1, 0, 1, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 1, 0, 1, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 1, 0, 2, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 0, 1, 1, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 1, 1, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 1, 1, 1, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 1, 2, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 2, 0, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 0, 2, 0, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)])
]
theorem chunk_051_checked : chunk_051.all checkCertificate = true := by
  decide

def chunk_052 : List Certificate := [
  ([4, 0, 2, 0, 1, 0, 0], 3, [(1, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([4, 0, 2, 1, 0, 0, 0], 3, [(1, 2, 1), (3, 0, 1), (5, 1, 1)]),
  ([4, 0, 3, 0, 0, 0, 0], 3, [(1, 1, 1), (3, 0, 1), (5, 2, 1)]),
  ([4, 1, 0, 0, 0, 0, 2], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 1, 0, 0, 0, 1, 1], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 1, 0, 0, 0, 2, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 1, 0, 0, 1, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 0, 0, 1, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 0, 0, 2, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([4, 1, 0, 1, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 0, 1, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 0, 1, 1, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 0, 2, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 1, 0, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 1, 0, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 1, 1, 0, 1, 0, 0], 3, [(1, 2, 1), (3, 0, 1), (5, 1, 1)]),
  ([4, 1, 1, 1, 0, 0, 0], 3, [(1, 2, 1), (3, 0, 1), (5, 1, 1)]),
  ([4, 1, 2, 0, 0, 0, 0], 3, [(1, 2, 1), (3, 0, 1), (5, 1, 1)]),
  ([4, 2, 0, 0, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 2, 0, 0, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 2, 0, 0, 1, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 2, 0, 1, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([4, 2, 1, 0, 0, 0, 0], 3, [(1, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([4, 3, 0, 0, 0, 0, 0], 6, [(1, 0, 1), (2, 4, 1), (3, 3, 1), (4, 2, 1), (6, 5, 1), (5, 1, 1)]),
  ([5, 0, 0, 0, 0, 0, 2], 9, [(1, 3, 2), (2, 1, 1), (3, 2, 1), (4, 0, 1), (0, 5, 1), (3, 6, 1), (5, 0, 1), (5, 1, 1)]),
  ([5, 0, 0, 0, 0, 1, 1], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([5, 0, 0, 0, 0, 2, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([5, 0, 0, 0, 1, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 0, 0, 0, 1, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 0, 0, 0, 2, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([5, 0, 0, 1, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 0, 0, 1, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)])
]
theorem chunk_052_checked : chunk_052.all checkCertificate = true := by
  decide

def chunk_053 : List Certificate := [
  ([5, 0, 0, 1, 1, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([5, 0, 0, 2, 0, 0, 0], 3, [(1, 1, 1), (3, 0, 1), (5, 2, 1)]),
  ([5, 0, 1, 0, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 0, 1, 0, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 0, 1, 0, 1, 0, 0], 3, [(1, 2, 1), (3, 0, 1), (5, 1, 1)]),
  ([5, 0, 1, 1, 0, 0, 0], 3, [(1, 2, 1), (3, 0, 1), (5, 1, 1)]),
  ([5, 0, 2, 0, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 3, 1)]),
  ([5, 1, 0, 0, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 1, 0, 0, 0, 1, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([5, 1, 0, 0, 1, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([5, 1, 0, 1, 0, 0, 0], 3, [(1, 1, 1), (3, 0, 1), (5, 2, 1)]),
  ([5, 1, 1, 0, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 3, 1)]),
  ([5, 2, 0, 0, 0, 0, 0], 9, [(1, 1, 1), (1, 3, 1), (2, 3, 1), (3, 2, 2), (4, 1, 1), (6, 5, 1), (5, 0, 2)]),
  ([6, 0, 0, 0, 0, 0, 1], 3, [(1, 0, 1), (3, 1, 1), (5, 2, 1)]),
  ([6, 0, 0, 0, 0, 1, 0], 3, [(1, 0, 1), (3, 3, 1), (5, 2, 1)]),
  ([6, 0, 0, 0, 1, 0, 0], 3, [(1, 0, 1), (3, 2, 1), (5, 1, 1)]),
  ([6, 0, 0, 1, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 4, 1)]),
  ([6, 0, 1, 0, 0, 0, 0], 3, [(1, 0, 1), (3, 1, 1), (5, 3, 1)]),
  ([6, 1, 0, 0, 0, 0, 0], 3, [(1, 2, 1), (3, 1, 1), (5, 0, 1)]),
  ([7, 0, 0, 0, 0, 0, 0], 3, [(1, 4, 1), (3, 0, 1), (5, 3, 1)])
]
theorem chunk_053_checked : chunk_053.all checkCertificate = true := by
  decide

def certificates : List Certificate :=
  chunk_000 ++
  chunk_001 ++
  chunk_002 ++
  chunk_003 ++
  chunk_004 ++
  chunk_005 ++
  chunk_006 ++
  chunk_007 ++
  chunk_008 ++
  chunk_009 ++
  chunk_010 ++
  chunk_011 ++
  chunk_012 ++
  chunk_013 ++
  chunk_014 ++
  chunk_015 ++
  chunk_016 ++
  chunk_017 ++
  chunk_018 ++
  chunk_019 ++
  chunk_020 ++
  chunk_021 ++
  chunk_022 ++
  chunk_023 ++
  chunk_024 ++
  chunk_025 ++
  chunk_026 ++
  chunk_027 ++
  chunk_028 ++
  chunk_029 ++
  chunk_030 ++
  chunk_031 ++
  chunk_032 ++
  chunk_033 ++
  chunk_034 ++
  chunk_035 ++
  chunk_036 ++
  chunk_037 ++
  chunk_038 ++
  chunk_039 ++
  chunk_040 ++
  chunk_041 ++
  chunk_042 ++
  chunk_043 ++
  chunk_044 ++
  chunk_045 ++
  chunk_046 ++
  chunk_047 ++
  chunk_048 ++
  chunk_049 ++
  chunk_050 ++
  chunk_051 ++
  chunk_052 ++
  chunk_053

theorem append_checked (xs ys : List Certificate)
    (hx : xs.all checkCertificate = true) (hy : ys.all checkCertificate = true) :
    (xs ++ ys).all checkCertificate = true :=
  (List.all_append).trans (congrArg₂ Bool.and hx hy)

theorem all_certificates_checked : certificates.all checkCertificate = true := by
  exact (append_checked chunk_000 (chunk_001 ++ chunk_002 ++ chunk_003 ++ chunk_004 ++ chunk_005 ++ chunk_006 ++ chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_000_checked
    (append_checked chunk_001 (chunk_002 ++ chunk_003 ++ chunk_004 ++ chunk_005 ++ chunk_006 ++ chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_001_checked
    (append_checked chunk_002 (chunk_003 ++ chunk_004 ++ chunk_005 ++ chunk_006 ++ chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_002_checked
    (append_checked chunk_003 (chunk_004 ++ chunk_005 ++ chunk_006 ++ chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_003_checked
    (append_checked chunk_004 (chunk_005 ++ chunk_006 ++ chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_004_checked
    (append_checked chunk_005 (chunk_006 ++ chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_005_checked
    (append_checked chunk_006 (chunk_007 ++ chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_006_checked
    (append_checked chunk_007 (chunk_008 ++ chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_007_checked
    (append_checked chunk_008 (chunk_009 ++ chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_008_checked
    (append_checked chunk_009 (chunk_010 ++ chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_009_checked
    (append_checked chunk_010 (chunk_011 ++ chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_010_checked
    (append_checked chunk_011 (chunk_012 ++ chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_011_checked
    (append_checked chunk_012 (chunk_013 ++ chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_012_checked
    (append_checked chunk_013 (chunk_014 ++ chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_013_checked
    (append_checked chunk_014 (chunk_015 ++ chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_014_checked
    (append_checked chunk_015 (chunk_016 ++ chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_015_checked
    (append_checked chunk_016 (chunk_017 ++ chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_016_checked
    (append_checked chunk_017 (chunk_018 ++ chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_017_checked
    (append_checked chunk_018 (chunk_019 ++ chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_018_checked
    (append_checked chunk_019 (chunk_020 ++ chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_019_checked
    (append_checked chunk_020 (chunk_021 ++ chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_020_checked
    (append_checked chunk_021 (chunk_022 ++ chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_021_checked
    (append_checked chunk_022 (chunk_023 ++ chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_022_checked
    (append_checked chunk_023 (chunk_024 ++ chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_023_checked
    (append_checked chunk_024 (chunk_025 ++ chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_024_checked
    (append_checked chunk_025 (chunk_026 ++ chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_025_checked
    (append_checked chunk_026 (chunk_027 ++ chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_026_checked
    (append_checked chunk_027 (chunk_028 ++ chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_027_checked
    (append_checked chunk_028 (chunk_029 ++ chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_028_checked
    (append_checked chunk_029 (chunk_030 ++ chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_029_checked
    (append_checked chunk_030 (chunk_031 ++ chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_030_checked
    (append_checked chunk_031 (chunk_032 ++ chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_031_checked
    (append_checked chunk_032 (chunk_033 ++ chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_032_checked
    (append_checked chunk_033 (chunk_034 ++ chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_033_checked
    (append_checked chunk_034 (chunk_035 ++ chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_034_checked
    (append_checked chunk_035 (chunk_036 ++ chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_035_checked
    (append_checked chunk_036 (chunk_037 ++ chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_036_checked
    (append_checked chunk_037 (chunk_038 ++ chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_037_checked
    (append_checked chunk_038 (chunk_039 ++ chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_038_checked
    (append_checked chunk_039 (chunk_040 ++ chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_039_checked
    (append_checked chunk_040 (chunk_041 ++ chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_040_checked
    (append_checked chunk_041 (chunk_042 ++ chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_041_checked
    (append_checked chunk_042 (chunk_043 ++ chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_042_checked
    (append_checked chunk_043 (chunk_044 ++ chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_043_checked
    (append_checked chunk_044 (chunk_045 ++ chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_044_checked
    (append_checked chunk_045 (chunk_046 ++ chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_045_checked
    (append_checked chunk_046 (chunk_047 ++ chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_046_checked
    (append_checked chunk_047 (chunk_048 ++ chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_047_checked
    (append_checked chunk_048 (chunk_049 ++ chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_048_checked
    (append_checked chunk_049 (chunk_050 ++ chunk_051 ++ chunk_052 ++ chunk_053) chunk_049_checked
    (append_checked chunk_050 (chunk_051 ++ chunk_052 ++ chunk_053) chunk_050_checked
    (append_checked chunk_051 (chunk_052 ++ chunk_053) chunk_051_checked
    (append_checked chunk_052 (chunk_053) chunk_052_checked
    chunk_053_checked)))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem all_compositions_present : certificates.map Prod.fst = compositions 7 7 := by
  rfl

end CakeQuantileSeven


namespace CakeSevenUnconditional
open MeasureTheory

/-- Unconditional four-cut division for the fixed three-agent demands (2,1,4)/7. -/
theorem fixed_three_agent_division (μ : Fin 3 → Measure ℝ)
    (hprob : ∀ i, IsProbabilityMeasure (μ i))
    (hatom : ∀ i, NullSingletonClass (μ i))
    (hcake : ∀ i, μ i (Set.Icc 0 1) = 1) :
    OMA.S_arxiv_1909_07141.DivisionWithCuts μ ![(2/7:ℝ),1/7,4/7] 4 := by
  exact CakeSevenComplete.division_of_checked_table
    CakeQuantileSeven.certificates CakeQuantileSeven.all_certificates_checked
    CakeQuantileSeven.all_compositions_present μ hprob hatom hcake

end CakeSevenUnconditional
