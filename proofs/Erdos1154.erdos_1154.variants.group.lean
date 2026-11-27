import FormalConjectures.ErdosProblems.«1154»
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Probability.ProductMeasure

/-!
# Erdős Problem 1154 (Additive group of given Hausdorff dimension)

Proves `Erdos1154.erdos_1154.variants.group`: for every `a ∈ [0, 1]`, there exists
an `AddSubgroup ℝ` with Hausdorff dimension `a`.
-/

open scoped ENNReal NNReal BigOperators Topology
open Set MeasureTheory Filter Metric

namespace Erdos1154GroupProof

local instance (n : ℕ) : MeasurableSpace (Fin n) := ⊤

private lemma measurableSpace_fin_eq_top (n : ℕ) :
    (inferInstance : MeasurableSpace (Fin n)) = ⊤ := rfl

private def q (j₀ j : ℕ) : ℕ := 2 ^ (j + j₀)

private def Q (j₀ n : ℕ) : ℕ := ∏ j ∈ Finset.range n, q j₀ j

private noncomputable def D (j₀ : ℕ) (α : ℝ) (j : ℕ) : ℕ := Nat.floor ((q j₀ j : ℝ) ^ α)

private noncomputable def P (j₀ : ℕ) (α : ℝ) (n : ℕ) : ℕ := ∏ j ∈ Finset.range n, D j₀ α j

private lemma q_pos (j₀ j : ℕ) : 0 < q j₀ j := by
  unfold q
  positivity

private lemma q_cast (j₀ j : ℕ) : (q j₀ j : ℝ) = (2 : ℝ) ^ ((j + j₀ : ℕ) : ℝ) := by
  unfold q
  simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]

private lemma Q_zero (j₀ : ℕ) : Q j₀ 0 = 1 := by
  simp [Q]

private lemma Q_succ (j₀ n : ℕ) : Q j₀ (n + 1) = Q j₀ n * q j₀ n := by
  simp [Q, Finset.prod_range_succ]

private lemma Q_pos (j₀ n : ℕ) : 0 < Q j₀ n := by
  unfold Q
  exact Finset.prod_pos fun j _ => q_pos j₀ j

private lemma Q_mono (j₀ : ℕ) {m n : ℕ} (h : m ≤ n) : Q j₀ m ≤ Q j₀ n := by
  unfold Q
  exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono h)
    fun j _ _ => q_pos j₀ j

private lemma Q_ge_pow_sum (j₀ n : ℕ) : 2 ^ (n * (n - 1) / 2) ≤ Q j₀ n := by
  unfold Q q
  have h1 : ∏ j ∈ Finset.range n, 2 ^ j ≤ ∏ j ∈ Finset.range n, 2 ^ (j + j₀) := by
    refine Finset.prod_le_prod' fun j _ => ?_
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right j j₀)
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id] at h1
  exact h1

private lemma exists_j₀ {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ j₀ : ℕ, 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)) ∧ 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)) := by
  have h1 : Tendsto (fun n : ℕ => (2 : ℝ) ^ ((1 - α) * (n : ℝ))) atTop atTop := by
    have hb : 1 < (2 : ℝ) ^ (1 - α) := Real.one_lt_rpow (by norm_num) (sub_pos.2 hα1)
    have ht := tendsto_pow_atTop_atTop_of_one_lt hb
    refine ht.congr fun n => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) ^ (α * (n : ℝ))) atTop atTop := by
    have hb : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα0
    have ht := tendsto_pow_atTop_atTop_of_one_lt hb
    refine ht.congr fun n => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (h1.eventually_ge_atTop 8)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (h2.eventually_ge_atTop 2)
  exact ⟨max N₁ N₂, hN₁ _ (le_max_left _ _), hN₂ _ (le_max_right _ _)⟩

private lemma rpow_one_sub_ge_eight {α : ℝ} (hα1 : α < 1) {j₀ : ℕ}
    (hj₀ : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ))) (j : ℕ) :
    8 ≤ (q j₀ j : ℝ) ^ (1 - α) := by
  rw [q_cast, ← Real.rpow_mul (by norm_num), mul_comm ((j + j₀ : ℕ) : ℝ) (1 - α)]
  refine hj₀.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hα1.le)
  exact_mod_cast Nat.le_add_left j₀ j

private lemma rpow_alpha_ge_two {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (j : ℕ) :
    2 ≤ (q j₀ j : ℝ) ^ α := by
  rw [q_cast, ← Real.rpow_mul (by norm_num), mul_comm ((j + j₀ : ℕ) : ℝ) α]
  refine hj₀.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  refine mul_le_mul_of_nonneg_left ?_ hα0.le
  exact_mod_cast Nat.le_add_left j₀ j

private lemma D_ge_two {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (j : ℕ) :
    2 ≤ D j₀ α j := by
  unfold D
  exact Nat.le_floor (rpow_alpha_ge_two hα0 hj₀ j)

private lemma D_pos {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (j : ℕ) :
    0 < D j₀ α j :=
  lt_of_lt_of_le (by norm_num) (D_ge_two hα0 hj₀ j)

private lemma D_le_rpow {j₀ : ℕ} {α : ℝ} (j : ℕ) :
    (D j₀ α j : ℝ) ≤ (q j₀ j : ℝ) ^ α := by
  unfold D
  exact Nat.floor_le (by positivity)

private lemma rpow_div_two_le_D {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (j : ℕ) :
    (q j₀ j : ℝ) ^ α / 2 ≤ (D j₀ α j : ℝ) := by
  have h1 : (q j₀ j : ℝ) ^ α < (D j₀ α j : ℝ) + 1 := by
    unfold D
    exact Nat.lt_floor_add_one _
  have h2 : (1 : ℝ) ≤ (D j₀ α j : ℝ) := by
    exact_mod_cast le_trans (by norm_num) (D_ge_two hα0 hj₀ j)
  linarith

private lemma D_le_q_div_eight {α : ℝ} (hα1 : α < 1) {j₀ : ℕ}
    (hj₀ : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ))) (j : ℕ) :
    (D j₀ α j : ℝ) ≤ (q j₀ j : ℝ) / 8 := by
  have hq : 0 < (q j₀ j : ℝ) := by exact_mod_cast q_pos j₀ j
  have h8 : (8 : ℝ) ≤ (q j₀ j : ℝ) ^ (1 - α) := rpow_one_sub_ge_eight hα1 hj₀ j
  have hmul : (q j₀ j : ℝ) ^ α * (q j₀ j : ℝ) ^ (1 - α) = (q j₀ j : ℝ) := by
    rw [← Real.rpow_add hq, add_sub_cancel, Real.rpow_one]
  have hD : (D j₀ α j : ℝ) ≤ (q j₀ j : ℝ) ^ α := D_le_rpow j
  rw [le_div_iff₀ (by norm_num)]
  calc
    (D j₀ α j : ℝ) * 8 ≤ (q j₀ j : ℝ) ^ α * (q j₀ j : ℝ) ^ (1 - α) :=
      mul_le_mul hD h8 (by norm_num) (by positivity)
    _ = (q j₀ j : ℝ) := hmul

private lemma eight_le_q {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (j : ℕ) :
    8 ≤ q j₀ j := by
  have h1 : (2 : ℝ) ≤ (D j₀ α j : ℝ) := by exact_mod_cast D_ge_two hα0 hj₀2 j
  have h2 : (D j₀ α j : ℝ) ≤ (q j₀ j : ℝ) / 8 := D_le_q_div_eight hα1 hj₀1 j
  have h4 : (8 : ℝ) ≤ (q j₀ j : ℝ) := by linarith
  exact_mod_cast h4

private lemma Q_ge_eight_pow {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (n : ℕ) :
    8 ^ n ≤ Q j₀ n := by
  unfold Q
  calc
    8 ^ n = ∏ _j ∈ Finset.range n, 8 := by simp
    _ ≤ ∏ j ∈ Finset.range n, q j₀ j :=
      Finset.prod_le_prod' fun j _ => eight_le_q hα0 hα1 hj₀1 hj₀2 j

private lemma P_zero (j₀ : ℕ) (α : ℝ) : P j₀ α 0 = 1 := by
  simp [P]

private lemma P_succ (j₀ : ℕ) (α : ℝ) (n : ℕ) : P j₀ α (n + 1) = P j₀ α n * D j₀ α n := by
  simp [P, Finset.prod_range_succ]

private lemma P_pos {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (n : ℕ) :
    0 < P j₀ α n := by
  unfold P
  exact Finset.prod_pos fun j _ => D_pos hα0 hj₀ j

private lemma P_ge_two_pow {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (n : ℕ) :
    2 ^ n ≤ P j₀ α n := by
  unfold P
  calc
    2 ^ n = ∏ _j ∈ Finset.range n, 2 := by simp
    _ ≤ ∏ j ∈ Finset.range n, D j₀ α j :=
      Finset.prod_le_prod' fun j _ => D_ge_two hα0 hj₀ j

private lemma P_ge_Q_rpow {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀ : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (n : ℕ) :
    (Q j₀ n : ℝ) ^ α / (2 : ℝ) ^ n ≤ (P j₀ α n : ℝ) := by
  unfold P Q
  push_cast
  rw [← Real.finsetProd_rpow _ _ fun j _ => by positivity]
  rw [div_eq_mul_one_div, one_div, ← inv_pow]
  have hcard : (2 : ℝ)⁻¹ ^ n = ∏ _j ∈ Finset.range n, (2 : ℝ)⁻¹ := by simp
  rw [hcard, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
  rw [← div_eq_mul_inv]
  exact rpow_div_two_le_D hα0 hj₀ j

private abbrev Ω (j₀ : ℕ) (α : ℝ) : Type := ∀ j : ℕ, Fin (D j₀ α j)

private noncomputable def term (j₀ : ℕ) (α : ℝ) (d : Ω j₀ α) (j : ℕ) : ℝ :=
  ((d j : ℕ) : ℝ) / (Q j₀ (j + 1) : ℝ)

private lemma term_nonneg (j₀ : ℕ) (α : ℝ) (d : Ω j₀ α) (j : ℕ) :
    0 ≤ term j₀ α d j := by
  unfold term
  positivity

private lemma term_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    (d : Ω j₀ α) (j : ℕ) :
    term j₀ α d j ≤ (1 / 8 : ℝ) * (1 / 8 : ℝ) ^ j := by
  unfold term
  have hd : ((d j : ℕ) : ℝ) ≤ (D j₀ α j : ℝ) := by exact_mod_cast (d j).isLt.le
  have hD : (D j₀ α j : ℝ) ≤ (q j₀ j : ℝ) / 8 := D_le_q_div_eight hα1 hj₀1 j
  have hQ : (8 : ℝ) ^ j ≤ (Q j₀ j : ℝ) := by exact_mod_cast Q_ge_eight_pow hα0 hα1 hj₀1 hj₀2 j
  have hQpos : (0 : ℝ) < (Q j₀ j : ℝ) := by exact_mod_cast Q_pos j₀ j
  have hqpos : (0 : ℝ) < (q j₀ j : ℝ) := by exact_mod_cast q_pos j₀ j
  rw [Q_succ, Nat.cast_mul]
  calc
    ((d j : ℕ) : ℝ) / ((Q j₀ j : ℝ) * (q j₀ j : ℝ))
        ≤ ((q j₀ j : ℝ) / 8) / ((Q j₀ j : ℝ) * (q j₀ j : ℝ)) := by
          gcongr
          exact hd.trans hD
    _ = 1 / (8 * (Q j₀ j : ℝ)) := by
          field_simp
    _ ≤ 1 / (8 * (8 : ℝ) ^ j) := by
          gcongr
    _ = (1 / 8 : ℝ) * (1 / 8 : ℝ) ^ j := by
          simp only [one_div, mul_inv, inv_pow]

private lemma summable_term {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    (d : Ω j₀ α) :
    Summable (term j₀ α d) := by
  refine Summable.of_nonneg_of_le (term_nonneg j₀ α d) (term_le hα0 hα1 hj₀1 hj₀2 d) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1)).mul_left (1 / 8)

private noncomputable def π (j₀ : ℕ) (α : ℝ) (d : Ω j₀ α) : ℝ :=
  ∑' j : ℕ, term j₀ α d j

private lemma measurable_π {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) :
    Measurable (π j₀ α) := by
  have h_lim : ∀ d : Ω j₀ α,
      Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, term j₀ α d j) atTop (𝓝 (π j₀ α d)) :=
    fun d => (summable_term hα0 hα1 hj₀1 hj₀2 d).hasSum.tendsto_sum_nat
  refine measurable_of_tendsto_metrizable (f := fun N d => ∑ j ∈ Finset.range N, term j₀ α d j)
    (fun N => ?_) (tendsto_pi_nhds.2 h_lim)
  refine Finset.measurable_sum _ fun j _ => ?_
  have hcoord : Measurable (fun d : Ω j₀ α => d j) := measurable_pi_apply j
  exact Measurable.comp (measurable_from_top (f := fun x : Fin (D j₀ α j) =>
    ((x : ℕ) : ℝ) / (Q j₀ (j + 1) : ℝ))) hcoord

private lemma tail_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    (d : Ω j₀ α) (N : ℕ) :
    0 ≤ ∑' r : ℕ, term j₀ α d (N + r) ∧
      ∑' r : ℕ, term j₀ α d (N + r) ≤ 1 / (7 * (Q j₀ N : ℝ)) := by
  have hs : Summable (fun r : ℕ => term j₀ α d (N + r)) :=
    (summable_term hα0 hα1 hj₀1 hj₀2 d).comp_injective (add_right_injective N)
  refine ⟨tsum_nonneg fun r => term_nonneg j₀ α d (N + r), ?_⟩
  have h_le : ∀ r : ℕ, term j₀ α d (N + r) ≤ (1 / (8 * (Q j₀ N : ℝ))) * (1 / 8 : ℝ) ^ r := by
    intro r
    unfold term
    have hd : ((d (N + r) : ℕ) : ℝ) ≤ (q j₀ (N + r) : ℝ) / 8 :=
      (Nat.cast_le.2 (d (N + r)).isLt.le).trans (D_le_q_div_eight hα1 hj₀1 (N + r))
    have hQ_split : Q j₀ (N + r) = Q j₀ N * ∏ k ∈ Finset.range r, q j₀ (N + k) := by
      unfold Q
      rw [Finset.prod_range_add]
    have h_prod : (8 : ℝ) ^ r ≤ (∏ k ∈ Finset.range r, q j₀ (N + k) : ℕ) := by
      have : 8 ^ r ≤ ∏ k ∈ Finset.range r, q j₀ (N + k) := by
        calc
          8 ^ r = ∏ _k ∈ Finset.range r, 8 := by simp
          _ ≤ ∏ k ∈ Finset.range r, q j₀ (N + k) :=
            Finset.prod_le_prod' fun k _ => eight_le_q hα0 hα1 hj₀1 hj₀2 (N + k)
      exact_mod_cast this
    have hQN : (0 : ℝ) < (Q j₀ N : ℝ) := by exact_mod_cast Q_pos j₀ N
    have hqr : (0 : ℝ) < (q j₀ (N + r) : ℝ) := by exact_mod_cast q_pos j₀ (N + r)
    rw [Q_succ, hQ_split, Nat.cast_mul, Nat.cast_mul]
    calc
      ((d (N + r) : ℕ) : ℝ) / ((Q j₀ N : ℝ) * (∏ k ∈ Finset.range r, q j₀ (N + k) : ℕ) * (q j₀ (N + r) : ℝ))
          ≤ ((q j₀ (N + r) : ℝ) / 8) /
              ((Q j₀ N : ℝ) * (∏ k ∈ Finset.range r, q j₀ (N + k) : ℕ) * (q j₀ (N + r) : ℝ)) := by
            gcongr
      _ = 1 / (8 * (Q j₀ N : ℝ) * (∏ k ∈ Finset.range r, q j₀ (N + k) : ℕ)) := by
            field_simp
      _ ≤ 1 / (8 * (Q j₀ N : ℝ) * (8 : ℝ) ^ r) := by
            gcongr
      _ = (1 / (8 * (Q j₀ N : ℝ))) * (1 / 8 : ℝ) ^ r := by
            simp only [one_div, mul_inv, inv_pow]
  have hs_geom : Summable (fun r : ℕ => (1 / (8 * (Q j₀ N : ℝ))) * (1 / 8 : ℝ) ^ r) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1)).mul_left _
  calc
    ∑' r : ℕ, term j₀ α d (N + r)
        ≤ ∑' r : ℕ, (1 / (8 * (Q j₀ N : ℝ))) * (1 / 8 : ℝ) ^ r :=
          Summable.tsum_le_tsum h_le hs hs_geom
    _ = (1 / (8 * (Q j₀ N : ℝ))) * (1 - (1 / 8 : ℝ))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 1 / (7 * (Q j₀ N : ℝ)) := by
          ring

private lemma π_split {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    (d : Ω j₀ α) (N : ℕ) :
    π j₀ α d = (∑ j ∈ Finset.range N, term j₀ α d j) + ∑' r : ℕ, term j₀ α d (N + r) := by
  unfold π
  simpa [add_comm] using ((summable_term hα0 hα1 hj₀1 hj₀2 d).sum_add_tsum_nat_add N).symm

private lemma π_sep {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    {d d' : Ω j₀ α} {j₁ : ℕ} (h_eq : ∀ j < j₁, d j = d' j) (h_ne : d j₁ ≠ d' j₁) :
    1 / (2 * (Q j₀ (j₁ + 1) : ℝ)) ≤ |π j₀ α d - π j₀ α d'| := by
  rw [π_split hα0 hα1 hj₀1 hj₀2 d (j₁ + 1), π_split hα0 hα1 hj₀1 hj₀2 d' (j₁ + 1)]
  have hsum : ∑ j ∈ Finset.range (j₁ + 1), term j₀ α d j -
      ∑ j ∈ Finset.range (j₁ + 1), term j₀ α d' j =
      term j₀ α d j₁ - term j₀ α d' j₁ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hp : ∑ j ∈ Finset.range j₁, term j₀ α d j = ∑ j ∈ Finset.range j₁, term j₀ α d' j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [term, h_eq j (Finset.mem_range.1 hj)]
    linarith
  have hQpos : (0 : ℝ) < (Q j₀ (j₁ + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (j₁ + 1)
  have h_main : 1 / (Q j₀ (j₁ + 1) : ℝ) ≤ |term j₀ α d j₁ - term j₀ α d' j₁| := by
    unfold term
    rw [← sub_div, abs_div, abs_of_pos hQpos]
    refine div_le_div_of_nonneg_right ?_ hQpos.le
    have hne_nat : (d j₁ : ℕ) ≠ (d' j₁ : ℕ) := fun h => h_ne (Fin.ext h)
    have h_abs : (1 : ℤ) ≤ |(d j₁ : ℤ) - (d' j₁ : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.2 (by exact_mod_cast hne_nat))
    exact_mod_cast h_abs
  have ht1 := tail_bound hα0 hα1 hj₀1 hj₀2 d (j₁ + 1)
  have ht2 := tail_bound hα0 hα1 hj₀1 hj₀2 d' (j₁ + 1)
  have h_tail : |∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r)| ≤
      1 / (7 * (Q j₀ (j₁ + 1) : ℝ)) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have h_tri : |term j₀ α d j₁ - term j₀ α d' j₁| -
      |∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r)| ≤
      |((∑ j ∈ Finset.range (j₁ + 1), term j₀ α d j + ∑' r : ℕ, term j₀ α d (j₁ + 1 + r)) -
        (∑ j ∈ Finset.range (j₁ + 1), term j₀ α d' j + ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r)))| := by
    have heq : (∑ j ∈ Finset.range (j₁ + 1), term j₀ α d j + ∑' r : ℕ, term j₀ α d (j₁ + 1 + r)) -
        (∑ j ∈ Finset.range (j₁ + 1), term j₀ α d' j + ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r)) =
        (term j₀ α d j₁ - term j₀ α d' j₁) +
          (∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r)) := by
      linarith
    rw [heq]
    calc
      |term j₀ α d j₁ - term j₀ α d' j₁| -
          |∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r)|
          = |term j₀ α d j₁ - term j₀ α d' j₁| -
              |-(∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r))| := by
            rw [abs_neg]
      _ ≤ |(term j₀ α d j₁ - term j₀ α d' j₁) -
            -(∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r))| :=
            abs_sub_abs_le_abs_sub _ _
      _ = |(term j₀ α d j₁ - term j₀ α d' j₁) +
            (∑' r : ℕ, term j₀ α d (j₁ + 1 + r) - ∑' r : ℕ, term j₀ α d' (j₁ + 1 + r))| := by
            rw [sub_neg_eq_add]
  have h_num : 1 / (2 * (Q j₀ (j₁ + 1) : ℝ)) ≤
      1 / (Q j₀ (j₁ + 1) : ℝ) - 1 / (7 * (Q j₀ (j₁ + 1) : ℝ)) := by
    rw [show 1 / (Q j₀ (j₁ + 1) : ℝ) - 1 / (7 * (Q j₀ (j₁ + 1) : ℝ)) =
        (6 / 7 : ℝ) / (Q j₀ (j₁ + 1) : ℝ) by ring]
    rw [show 1 / (2 * (Q j₀ (j₁ + 1) : ℝ)) = (1 / 2 : ℝ) / (Q j₀ (j₁ + 1) : ℝ) by ring]
    refine div_le_div_of_nonneg_right (by norm_num) hQpos.le
  linarith

private lemma π_injective {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) :
    Function.Injective (π j₀ α) := by
  classical
  intro d d' h
  by_contra hne
  have hex : ∃ j, d j ≠ d' j := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  let j₁ := Nat.find hex
  have hj₁ : d j₁ ≠ d' j₁ := Nat.find_spec hex
  have hmin : ∀ j < j₁, d j = d' j := fun j hj => by
    by_contra hne'
    exact Nat.lt_le_asymm hj (Nat.find_min' hex hne')
  have hsep := π_sep hα0 hα1 hj₀1 hj₀2 hmin hj₁
  rw [h, sub_self, abs_zero] at hsep
  have hpos : (0 : ℝ) < 1 / (2 * (Q j₀ (j₁ + 1) : ℝ)) := by
    have : (0 : ℝ) < (Q j₀ (j₁ + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (j₁ + 1)
    positivity
  linarith

private lemma π_prefix_sep {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    {d d' : Ω j₀ α} {N : ℕ} (hex : ∃ j < N, d j ≠ d' j) :
    1 / (2 * (Q j₀ N : ℝ)) ≤ |π j₀ α d - π j₀ α d'| := by
  classical
  let j₁ := Nat.find hex
  have hj₁_spec := Nat.find_spec hex
  have hj₁_lt : j₁ < N := hj₁_spec.1
  have hj₁_ne : d j₁ ≠ d' j₁ := hj₁_spec.2
  have hmin : ∀ j < j₁, d j = d' j := fun j hj => by
    by_contra hne'
    exact Nat.lt_le_asymm hj (Nat.find_min' hex ⟨hj.trans hj₁_lt, hne'⟩)
  have hsep := π_sep hα0 hα1 hj₀1 hj₀2 hmin hj₁_ne
  have hQle : (Q j₀ (j₁ + 1) : ℝ) ≤ (Q j₀ N : ℝ) := by
    exact_mod_cast Q_mono j₀ (Nat.succ_le_of_lt hj₁_lt)
  have hQpos : (0 : ℝ) < (Q j₀ (j₁ + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (j₁ + 1)
  have h1 : 1 / (2 * (Q j₀ N : ℝ)) ≤ 1 / (2 * (Q j₀ (j₁ + 1) : ℝ)) := by
    gcongr
  exact h1.trans hsep

private def K (j₀ : ℕ) (α : ℝ) : Set ℝ := Set.range (π j₀ α)

private def G (j₀ : ℕ) (α : ℝ) : AddSubgroup ℝ := AddSubgroup.closure (K j₀ α)

private def Km (j₀ : ℕ) (α : ℝ) (m : ℕ) : Set ℝ :=
  {x : ℝ | ∃ (s : Fin m → Bool) (d : Fin m → Ω j₀ α),
    x = ∑ i : Fin m, (if s i then (1 : ℝ) else -1) * π j₀ α (d i)}

private lemma G_subset_iUnion_Km (j₀ : ℕ) (α : ℝ) :
    (G j₀ α : Set ℝ) ⊆ ⋃ m : ℕ, Km j₀ α m := by
  intro x hx
  unfold G at hx
  refine AddSubgroup.closure_induction (p := fun y _ => y ∈ ⋃ m : ℕ, Km j₀ α m)
    (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun y _ hy => ?_) hx
  · rcases hy with ⟨d, rfl⟩
    refine mem_iUnion.2 ⟨1, fun _ => true, fun _ => d, by simp⟩
  · refine mem_iUnion.2 ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  · rcases mem_iUnion.1 hy with ⟨m, s₁, d₁, rfl⟩
    rcases mem_iUnion.1 hz with ⟨n, s₂, d₂, rfl⟩
    refine mem_iUnion.2 ⟨m + n, Fin.addCases s₁ s₂, Fin.addCases d₁ d₂, ?_⟩
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [Fin.addCases_left]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [Fin.addCases_right]
  · rcases mem_iUnion.1 hy with ⟨m, s, d, rfl⟩
    refine mem_iUnion.2 ⟨m, fun i => !(s i), d, ?_⟩
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : s i <;> simp [h]

private lemma superexp_tendsto_zero {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (j₀ : ℕ) :
    Tendsto (fun N : ℕ => C ^ N * (Q j₀ N : ℝ) ^ (-δ)) atTop (𝓝 0) := by
  have h_gt : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt h_gt).eventually_ge_atTop (C + 1))
  let B : ℝ := ((2 : ℝ) ^ δ) ^ k
  have hB_pos : 0 < B := by positivity
  have hCB : C / B < 1 := by
    rw [div_lt_one hB_pos]
    linarith [hk k le_rfl]
  have h_tend : Tendsto (fun N : ℕ => (C / B) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hCB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tend
    (Eventually.of_forall fun N => by positivity) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * k + 1)] with N hN
  have h_exp : k * N ≤ N * (N - 1) / 2 := by
    refine Nat.le_div_iff_mul_le (by norm_num) |>.2 ?_
    have h1 : 2 * k ≤ N - 1 := by omega
    calc
      k * N * 2 = 2 * k * N := by ring
      _ ≤ (N - 1) * N := Nat.mul_le_mul_right N h1
      _ = N * (N - 1) := by ring
  have hQ : (2 : ℝ) ^ ((k * N : ℕ) : ℝ) ≤ (Q j₀ N : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num) h_exp).trans (Q_ge_pow_sum j₀ N)
  have hB_inv : B⁻¹ = (2 : ℝ) ^ (-(k : ℝ) * δ) := by
    dsimp [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  have hQ_neg : (Q j₀ N : ℝ) ^ (-δ) ≤ (B⁻¹) ^ N := by
    have h1 : (Q j₀ N : ℝ) ^ (-δ) ≤ ((2 : ℝ) ^ ((k * N : ℕ) : ℝ)) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hQ (by linarith)
    refine h1.trans_eq ?_
    rw [← Real.rpow_mul (by norm_num)]
    have hexp : ((k * N : ℕ) : ℝ) * (-δ) = (N : ℝ) * (-(k : ℝ) * δ) := by
      push_cast
      ring
    rw [hexp, mul_comm (N : ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast, ← hB_inv]
  calc
    C ^ N * (Q j₀ N : ℝ) ^ (-δ) ≤ C ^ N * (B⁻¹) ^ N := by gcongr
    _ = (C / B) ^ N := by rw [← mul_pow, div_eq_mul_inv]

private lemma hausdorffMeasure_Km_eq_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    (m : ℕ) (hm : 1 ≤ m) {d : ℝ≥0} (hd : α < (d : ℝ)) :
    μH[(d : ℝ)] (Km j₀ α m) = 0 := by
  let ι : ℕ → Type := fun N => ∀ j : Fin N, Fin (2 * m * D j₀ α j + 1)
  let center : ∀ N, ι N → ℝ := fun N c =>
    ∑ j : Fin N, (((c j : ℕ) : ℤ) - (m * D j₀ α j : ℤ) : ℝ) / (Q j₀ (j + 1) : ℝ)
  let t : ∀ N, ι N → Set ℝ := fun N c =>
    Set.Icc (center N c - (m : ℝ) / (Q j₀ N : ℝ)) (center N c + (m : ℝ) / (Q j₀ N : ℝ))
  let r : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (2 * (m : ℝ) / (Q j₀ N : ℝ))
  have hr : Tendsto r atTop (𝓝 0) := by
    have h_real : Tendsto (fun N : ℕ => 2 * (m : ℝ) / (Q j₀ N : ℝ)) atTop (𝓝 0) := by
      have h8 : Tendsto (fun N : ℕ => 2 * (m : ℝ) * (1 / 8 : ℝ) ^ N) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1)).const_mul (2 * (m : ℝ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h8
        (Eventually.of_forall fun N => by positivity) (Eventually.of_forall fun N => ?_)
      have hQ : (8 : ℝ) ^ N ≤ (Q j₀ N : ℝ) := by exact_mod_cast Q_ge_eight_pow hα0 hα1 hj₀1 hj₀2 N
      rw [div_eq_mul_one_div, one_div_pow]
      gcongr
    have h_comp : Tendsto (ENNReal.ofReal ∘ fun N : ℕ => 2 * (m : ℝ) / (Q j₀ N : ℝ)) atTop (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h_real
    simpa [Function.comp_def, r] using h_comp
  have ht : ∀ N c, ediam (t N c) ≤ r N := by
    intro N c
    refine Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_
    rw [Real.dist_eq]
    have hx' : center N c - (m : ℝ) / (Q j₀ N : ℝ) ≤ x ∧ x ≤ center N c + (m : ℝ) / (Q j₀ N : ℝ) := hx
    have hy' : center N c - (m : ℝ) / (Q j₀ N : ℝ) ≤ y ∧ y ≤ center N c + (m : ℝ) / (Q j₀ N : ℝ) := hy
    have h2 : 2 * (m : ℝ) / (Q j₀ N : ℝ) = (m : ℝ) / (Q j₀ N : ℝ) + (m : ℝ) / (Q j₀ N : ℝ) := by ring
    rw [abs_le, h2]
    constructor <;> linarith
  have hst : ∀ N, Km j₀ α m ⊆ ⋃ c : ι N, t N c := by
    intro N x hx
    rcases hx with ⟨s, f, rfl⟩
    let k : Fin N → ℤ := fun j =>
      ∑ i : Fin m, (if s i then (1 : ℤ) else -1) * ((f i j : ℕ) : ℤ)
    have hk_bound : ∀ j : Fin N, -(m * D j₀ α j : ℤ) ≤ k j ∧ k j ≤ (m * D j₀ α j : ℤ) := by
      intro j
      have h_abs : |k j| ≤ (m * D j₀ α j : ℤ) := by
        calc
          |k j| ≤ ∑ i : Fin m, |(if s i then (1 : ℤ) else -1) * ((f i j : ℕ) : ℤ)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin m, (D j₀ α j : ℤ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            have h1 : |(if s i then (1 : ℤ) else -1)| = 1 := by cases s i <;> norm_num
            rw [h1, one_mul, abs_of_nonneg (Int.natCast_nonneg _)]
            exact_mod_cast (f i j).isLt.le
          _ = (m * D j₀ α j : ℤ) := by simp [Finset.sum_const, nsmul_eq_mul]
      exact abs_le.1 h_abs
    let c : ι N := fun j =>
      ⟨(k j + (m * D j₀ α j : ℤ)).toNat, by
        have hb := hk_bound j
        rw [Int.toNat_lt (by linarith [hb.1])]
        push_cast
        linarith [hb.2]⟩
    refine mem_iUnion.2 ⟨c, ?_⟩
    have hc_val : ∀ j : Fin N, (((c j : ℕ) : ℤ) - (m * D j₀ α j : ℤ) : ℝ) = (k j : ℝ) := by
      intro j
      have hb := hk_bound j
      have hnat : ((c j : ℕ) : ℤ) = k j + (m * D j₀ α j : ℤ) := by
        dsimp [c]
        exact Int.toNat_of_nonneg (by linarith [hb.1])
      exact_mod_cast (show ((c j : ℕ) : ℤ) - (m * D j₀ α j : ℤ) = k j by linarith)
    have hsplit : ∀ i : Fin m,
        π j₀ α (f i) = (∑ j : Fin N, term j₀ α (f i) j) + ∑' r : ℕ, term j₀ α (f i) (N + r) := by
      intro i
      rw [π_split hα0 hα1 hj₀1 hj₀2 (f i) N, Fin.sum_univ_eq_sum_range (f := fun j => term j₀ α (f i) j)]
    have h_center : center N c =
        ∑ i : Fin m, (if s i then (1 : ℝ) else -1) * ∑ j : Fin N, term j₀ α (f i) j := by
      dsimp [center]
      simp_rw [hc_val]
      have hk_real : ∀ j : Fin N, (k j : ℝ) =
          ∑ i : Fin m, (if s i then (1 : ℝ) else -1) * ((f i j : ℕ) : ℝ) := by
        intro j
        dsimp [k]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        cases s i <;> simp
      simp_rw [hk_real, Finset.sum_div]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold term
      ring
    have h_err :
        |(∑ i : Fin m, (if s i then (1 : ℝ) else -1) * π j₀ α (f i)) - center N c| ≤
          (m : ℝ) / (Q j₀ N : ℝ) := by
      rw [h_center]
      have hdiff : (∑ i : Fin m, (if s i then (1 : ℝ) else -1) * π j₀ α (f i)) -
          ∑ i : Fin m, (if s i then (1 : ℝ) else -1) * ∑ j : Fin N, term j₀ α (f i) j =
          ∑ i : Fin m, (if s i then (1 : ℝ) else -1) * ∑' r : ℕ, term j₀ α (f i) (N + r) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsplit i]
        ring
      rw [hdiff]
      calc
        |∑ i : Fin m, (if s i then (1 : ℝ) else -1) * ∑' r : ℕ, term j₀ α (f i) (N + r)|
            ≤ ∑ i : Fin m, |(if s i then (1 : ℝ) else -1) * ∑' r : ℕ, term j₀ α (f i) (N + r)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin m, (1 / (Q j₀ N : ℝ)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              have h1 : |(if s i then (1 : ℝ) else -1)| = 1 := by cases s i <;> norm_num
              have ht := tail_bound hα0 hα1 hj₀1 hj₀2 (f i) N
              rw [h1, one_mul, abs_of_nonneg ht.1]
              have hQpos : (0 : ℝ) < (Q j₀ N : ℝ) := by exact_mod_cast Q_pos j₀ N
              refine ht.2.trans ?_
              gcongr
              linarith
        _ = (m : ℝ) / (Q j₀ N : ℝ) := by
              simp [Finset.sum_const, div_eq_mul_inv]
    exact ⟨by linarith [(abs_sub_le_iff.1 h_err).2], by linarith [(abs_sub_le_iff.1 h_err).1]⟩
  have h_le := Measure.hausdorffMeasure_le_liminf_sum (d : ℝ) (Km j₀ α m) r hr t
    (Eventually.of_forall ht) (Eventually.of_forall hst)
  have h_sum_tend : Tendsto (fun N : ℕ => ∑ c : ι N, ediam (t N c) ^ (d : ℝ)) atTop (𝓝 0) := by
    have h_bound : ∀ N : ℕ, ∑ c : ι N, ediam (t N c) ^ (d : ℝ) ≤
        ENNReal.ofReal ((2 * (m : ℝ)) ^ (d : ℝ) * (2 * (m : ℝ) + 1) ^ N * (Q j₀ N : ℝ) ^ (α - (d : ℝ))) := by
      intro N
      have hd_pos : 0 ≤ (d : ℝ) := d.2
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hQpos : (0 : ℝ) < (Q j₀ N : ℝ) := by exact_mod_cast Q_pos j₀ N
      have hterm_le : ∀ c : ι N, ediam (t N c) ^ (d : ℝ) ≤
          ENNReal.ofReal ((2 * (m : ℝ) / (Q j₀ N : ℝ)) ^ (d : ℝ)) := by
        intro c
        refine le_trans (ENNReal.rpow_le_rpow (ht N c) hd_pos) ?_
        rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hd_pos]
      calc
        ∑ c : ι N, ediam (t N c) ^ (d : ℝ)
            ≤ ∑ _c : ι N, ENNReal.ofReal ((2 * (m : ℝ) / (Q j₀ N : ℝ)) ^ (d : ℝ)) :=
              Finset.sum_le_sum fun c _ => hterm_le c
        _ = (Fintype.card (ι N) : ℝ≥0∞) * ENNReal.ofReal ((2 * (m : ℝ) / (Q j₀ N : ℝ)) ^ (d : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal ((2 * (m : ℝ) + 1) ^ N * (Q j₀ N : ℝ) ^ α) *
              ENNReal.ofReal ((2 * (m : ℝ) / (Q j₀ N : ℝ)) ^ (d : ℝ)) := by
              gcongr
              rw [← ENNReal.ofReal_natCast]
              refine ENNReal.ofReal_le_ofReal ?_
              have hcard : (Fintype.card (ι N) : ℝ) =
                  ∏ j : Fin N, (2 * (m : ℝ) * (D j₀ α j : ℝ) + 1) := by
                dsimp [ι]
                rw [Fintype.card_pi]
                push_cast
                simp
              rw [hcard]
              calc
                ∏ j : Fin N, (2 * (m : ℝ) * (D j₀ α j : ℝ) + 1)
                    ≤ ∏ j : Fin N, ((2 * (m : ℝ) + 1) * (q j₀ j : ℝ) ^ α) := by
                      refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
                      have hD1 : (1 : ℝ) ≤ (D j₀ α j : ℝ) := by
                        exact_mod_cast le_trans (by norm_num) (D_ge_two hα0 hj₀2 j)
                      have hDr : (D j₀ α j : ℝ) ≤ (q j₀ j : ℝ) ^ α := D_le_rpow j
                      nlinarith
                _ = (2 * (m : ℝ) + 1) ^ N * (Q j₀ N : ℝ) ^ α := by
                      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
                      congr 1
                      unfold Q
                      push_cast
                      rw [← Fin.prod_univ_eq_prod_range (f := fun j => (q j₀ j : ℝ)),
                        Real.finsetProd_rpow _ _ fun j _ => by positivity]
        _ = ENNReal.ofReal ((2 * (m : ℝ)) ^ (d : ℝ) * (2 * (m : ℝ) + 1) ^ N *
              (Q j₀ N : ℝ) ^ (α - (d : ℝ))) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [Real.div_rpow (by positivity) hQpos.le, Real.rpow_sub hQpos]
              ring
    have h_real_tend : Tendsto (fun N : ℕ => (2 * (m : ℝ)) ^ (d : ℝ) * (2 * (m : ℝ) + 1) ^ N *
        (Q j₀ N : ℝ) ^ (α - (d : ℝ))) atTop (𝓝 0) := by
      have h1 := (superexp_tendsto_zero (C := 2 * (m : ℝ) + 1) (δ := (d : ℝ) - α)
        (by positivity) (sub_pos.2 hd) j₀).const_mul ((2 * (m : ℝ)) ^ (d : ℝ))
      simpa [mul_assoc, neg_sub] using h1
    have h_enn_tend : Tendsto (fun N : ℕ =>
        ENNReal.ofReal ((2 * (m : ℝ)) ^ (d : ℝ) * (2 * (m : ℝ) + 1) ^ N *
          (Q j₀ N : ℝ) ^ (α - (d : ℝ)))) atTop (𝓝 0) := by
      have h_comp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h_real_tend
      simpa [Function.comp_def] using h_comp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_enn_tend
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall h_bound)
  rw [h_sum_tend.liminf_eq] at h_le
  exact le_antisymm h_le bot_le

private lemma dimH_G_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) :
    dimH (G j₀ α : Set ℝ) ≤ ENNReal.ofReal α := by
  refine (dimH_mono (G_subset_iUnion_Km j₀ α)).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · have hsub : Km j₀ α 0 ⊆ ({0} : Set ℝ) := by
      rintro x ⟨s, d, rfl⟩
      simp
    exact (dimH_mono hsub).trans (by simp)
  · refine dimH_le fun d hd => ?_
    by_contra hlt
    push Not at hlt
    have hαd : α < (d : ℝ) := by
      have hdpos : 0 < (d : ℝ) := by
        have hlt' : (0 : ℝ≥0∞) < (d : ℝ≥0∞) := lt_of_le_of_lt bot_le hlt
        exact_mod_cast hlt'
      rw [← ENNReal.ofReal_coe_nnreal] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff hdpos).1 hlt
    have h0 := hausdorffMeasure_Km_eq_zero hα0 hα1 hj₀1 hj₀2 m (Nat.pos_of_ne_zero hm) hαd
    rw [h0] at hd
    exact ENNReal.zero_ne_top hd

private noncomputable def νj (j₀ : ℕ) (α : ℝ) (j : ℕ) : Measure (Fin (D j₀ α j)) :=
  ((D j₀ α j : ℝ≥0∞)⁻¹) • Measure.count

private lemma isProbabilityMeasure_νj {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (j : ℕ) :
    IsProbabilityMeasure (νj j₀ α j) := by
  constructor
  unfold νj
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin, ENat.toENNReal_coe]
  have hpos : (D j₀ α j : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (D_pos hα0 hj₀2 j).ne'
  exact ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _)

private noncomputable def ν (j₀ : ℕ) (α : ℝ) : Measure (Ω j₀ α) :=
  Measure.infinitePi (νj j₀ α)

private noncomputable def μ (j₀ : ℕ) (α : ℝ) : Measure ℝ :=
  (ν j₀ α).map (π j₀ α)

private lemma ν_cylinder_singleton {α : ℝ} (hα0 : 0 < α) {j₀ : ℕ}
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (N : ℕ)
    (f : ∀ i : Finset.range N, Fin (D j₀ α i)) :
    ν j₀ α (MeasureTheory.cylinder (Finset.range N) {f}) = (P j₀ α N : ℝ≥0∞)⁻¹ := by
  haveI : ∀ j, IsProbabilityMeasure (νj j₀ α j) := isProbabilityMeasure_νj hα0 hj₀2
  unfold ν
  rw [Measure.infinitePi_cylinder (μ := νj j₀ α) (MeasurableSet.singleton f)]
  rw [Measure.pi_singleton]
  simp only [νj, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  rw [Finset.prod_coe_sort (Finset.range N) (fun j => (D j₀ α j : ℝ≥0∞)⁻¹)]
  clear f
  induction N with
  | zero => simp [P]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, P_succ, Nat.cast_mul, ENNReal.mul_inv]
    · left; exact_mod_cast (P_pos hα0 hj₀2 N).ne'
    · left; exact ENNReal.natCast_ne_top _

private lemma μ_singleton_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) (x : ℝ) :
    μ j₀ α {x} = 0 := by
  have : ∀ j, IsProbabilityMeasure (νj j₀ α j) := isProbabilityMeasure_νj hα0 hj₀2
  unfold μ
  rw [Measure.map_apply (measurable_π hα0 hα1 hj₀1 hj₀2) (measurableSet_singleton x)]
  by_cases hne : (π j₀ α ⁻¹' {x}).Nonempty
  · obtain ⟨d, hd⟩ := hne
    have hsub : π j₀ α ⁻¹' {x} ⊆ {d} := by
      intro d' hd'
      exact π_injective hα0 hα1 hj₀1 hj₀2 (hd'.symm ▸ hd.symm ▸ rfl)
    refine le_antisymm ((measure_mono hsub).trans ?_) bot_le
    have h_le_N : ∀ N : ℕ, ν j₀ α {d} ≤ (P j₀ α N : ℝ≥0∞)⁻¹ := by
      intro N
      have hcyl : ({d} : Set (Ω j₀ α)) ⊆
          MeasureTheory.cylinder (Finset.range N) {fun i : Finset.range N => d i.1} := by
        intro d' hd'
        rw [mem_singleton_iff] at hd'
        subst hd'
        simp [MeasureTheory.cylinder]
        rfl
      exact (measure_mono hcyl).trans_eq (ν_cylinder_singleton hα0 hj₀2 N (fun i : Finset.range N => d i.1))
    have h_tend : Tendsto (fun N : ℕ => (P j₀ α N : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      have h2 : ∀ N : ℕ, (P j₀ α N : ℝ≥0∞)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹) ^ N := by
        intro N
        calc
          (P j₀ α N : ℝ≥0∞)⁻¹ ≤ ((2 ^ N : ℕ) : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.2 (by exact_mod_cast P_ge_two_pow hα0 hj₀2 N)
          _ = ((2 : ℝ≥0∞)⁻¹) ^ N := by
            push_cast
            simp [ENNReal.inv_pow]
      have ht : Tendsto (fun N : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ N) atTop (𝓝 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
        (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall h2)
    exact ge_of_tendsto h_tend (Eventually.of_forall h_le_N)
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]

private lemma min_le_rpow_mul_rpow {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    min A B ≤ A ^ (1 - s) * B ^ s := by
  by_cases hAB : A ≤ B
  · rw [min_eq_left hAB]
    calc
      A = A ^ (1 - s) * A ^ s := by
            rcases eq_or_lt_of_le hA with rfl | hApos
            · by_cases hs0' : s = 0
              · subst hs0'; simp
              · simp [Real.zero_rpow hs0']
            · rw [← Real.rpow_add hApos, sub_add_cancel, Real.rpow_one]
      _ ≤ A ^ (1 - s) * B ^ s := by
            gcongr
  · push Not at hAB
    rw [min_eq_right hAB.le]
    calc
      B = B ^ (1 - s) * B ^ s := by
            rcases eq_or_lt_of_le hB with rfl | hBpos
            · by_cases hs0' : s = 0
              · subst hs0'; simp
              · simp [Real.zero_rpow hs0']
            · rw [← Real.rpow_add hBpos, sub_add_cancel, Real.rpow_one]
      _ ≤ A ^ (1 - s) * B ^ s := by
            gcongr

private lemma alg_step {s D P Q q r : ℝ} (hD : 0 < D) (hQ : 0 ≤ Q) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    3 * ((D ^ (1 - s) * (4 * r * (Q * q)) ^ s) / (P * D)) =
      (3 * 4 ^ s * (Q ^ s / P) * (q / D) ^ s) * r ^ s := by
  have hD_pow : D ^ (1 - s) / D = (D ^ s)⁻¹ := by
    rw [Real.rpow_sub hD, Real.rpow_one, div_div, mul_comm (D ^ s) D, ← div_div,
      div_self hD.ne', one_div]
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hr,
    Real.mul_rpow hQ hq, Real.div_rpow hq hD.le]
  calc
    3 * (D ^ (1 - s) * (4 ^ s * r ^ s * (Q ^ s * q ^ s)) / (P * D))
        = 3 * ((D ^ (1 - s) / D) * (4 ^ s * r ^ s * (Q ^ s * q ^ s)) / P) := by ring
    _ = 3 * ((D ^ s)⁻¹ * (4 ^ s * r ^ s * (Q ^ s * q ^ s)) / P) := by rw [hD_pow]
    _ = (3 * 4 ^ s * (Q ^ s / P) * (q ^ s / D ^ s)) * r ^ s := by ring

private lemma μ_ball_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    {s : ℝ≥0} (hs0 : 0 < (s : ℝ)) (hsα : (s : ℝ) < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set ℝ, MeasurableSet U →
      ediam U ≤ ENNReal.ofReal (1 / (2 * (Q j₀ 1 : ℝ))) →
      μ j₀ α U ≤ ENNReal.ofReal C * ediam U ^ (s : ℝ) := by
  have hs1 : (s : ℝ) < 1 := hsα.trans hα1
  let f : ℕ → ℝ := fun N =>
    3 * (4 : ℝ) ^ (s : ℝ) *
      ((Q j₀ (N + 1) : ℝ) ^ (s : ℝ) / (P j₀ α (N + 1) : ℝ)) *
      ((q j₀ (N + 1) : ℝ) / (D j₀ α (N + 1) : ℝ)) ^ (s : ℝ)
  have hf_tend : Tendsto f atTop (𝓝 0) := by
    have h_bound : ∀ N : ℕ, 0 ≤ f N ∧ f N ≤
        (3 * (4 : ℝ) ^ (s : ℝ) * 2 * (2 : ℝ) ^ j₀) *
          ((4 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α)) := by
      intro N
      have hQpos : (0 : ℝ) < (Q j₀ (N + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (N + 1)
      have hPpos : (0 : ℝ) < (P j₀ α (N + 1) : ℝ) := by exact_mod_cast P_pos hα0 hj₀2 (N + 1)
      have hqpos : (0 : ℝ) < (q j₀ (N + 1) : ℝ) := by exact_mod_cast q_pos j₀ (N + 1)
      have hDpos : (0 : ℝ) < (D j₀ α (N + 1) : ℝ) := by exact_mod_cast D_pos hα0 hj₀2 (N + 1)
      refine ⟨by positivity, ?_⟩
      have hP_le : (Q j₀ (N + 1) : ℝ) ^ (s : ℝ) / (P j₀ α (N + 1) : ℝ) ≤
          (2 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α) := by
        have hP := P_ge_Q_rpow hα0 hj₀2 (N + 1)
        calc
          (Q j₀ (N + 1) : ℝ) ^ (s : ℝ) / (P j₀ α (N + 1) : ℝ)
              ≤ (Q j₀ (N + 1) : ℝ) ^ (s : ℝ) / ((Q j₀ (N + 1) : ℝ) ^ α / (2 : ℝ) ^ (N + 1)) := by
                gcongr
          _ = (2 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α) := by
                rw [div_div_eq_mul_div, mul_comm ((Q j₀ (N + 1) : ℝ) ^ (s : ℝ)),
                  mul_div_assoc, ← Real.rpow_sub hQpos]
      have hqD : ((q j₀ (N + 1) : ℝ) / (D j₀ α (N + 1) : ℝ)) ^ (s : ℝ) ≤
          (q j₀ (N + 1) : ℝ) := by
        have h1 : (q j₀ (N + 1) : ℝ) / (D j₀ α (N + 1) : ℝ) ≤ (q j₀ (N + 1) : ℝ) := by
          refine div_le_self hqpos.le ?_
          exact_mod_cast le_trans (by norm_num) (D_ge_two hα0 hj₀2 (N + 1))
        have h2 : ((q j₀ (N + 1) : ℝ) / (D j₀ α (N + 1) : ℝ)) ^ (s : ℝ) ≤
            (q j₀ (N + 1) : ℝ) ^ (s : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 hs0.le
        have h3 : (q j₀ (N + 1) : ℝ) ^ (s : ℝ) ≤ (q j₀ (N + 1) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_trans (by norm_num) (q_pos j₀ (N + 1))) hs1.le
        simpa using h2.trans h3
      have hq_eq : (q j₀ (N + 1) : ℝ) = (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ j₀ := by
        unfold q
        push_cast
        rw [← pow_add]
      calc
        f N ≤ 3 * (4 : ℝ) ^ (s : ℝ) * ((2 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α)) *
              (q j₀ (N + 1) : ℝ) := by
            dsimp [f]
            gcongr
        _ = (3 * (4 : ℝ) ^ (s : ℝ) * 1 * (2 : ℝ) ^ j₀) *
              ((4 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α)) := by
            rw [hq_eq]
            have h4 : (4 : ℝ) ^ (N + 1) = (2 : ℝ) ^ (N + 1) * (2 : ℝ) ^ (N + 1) := by
              rw [← mul_pow]; norm_num
            rw [h4]
            ring
        _ ≤ (3 * (4 : ℝ) ^ (s : ℝ) * 2 * (2 : ℝ) ^ j₀) *
              ((4 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α)) := by
            gcongr
            norm_num
    have h_sup := superexp_tendsto_zero (C := 4) (δ := α - (s : ℝ)) (by norm_num) (sub_pos.2 hsα) j₀
    have h_sup_shift : Tendsto (fun N : ℕ =>
        (3 * (4 : ℝ) ^ (s : ℝ) * 2 * (2 : ℝ) ^ j₀) *
          ((4 : ℝ) ^ (N + 1) * (Q j₀ (N + 1) : ℝ) ^ ((s : ℝ) - α))) atTop (𝓝 0) := by
      have h1 := (h_sup.comp (tendsto_add_atTop_nat 1)).const_mul
        (3 * (4 : ℝ) ^ (s : ℝ) * 2 * (2 : ℝ) ^ j₀)
      simpa [neg_sub] using h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sup_shift
      (Eventually.of_forall fun N => (h_bound N).1)
      (Eventually.of_forall fun N => (h_bound N).2)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hf_tend.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  let C : ℝ := 1 + ∑ N ∈ Finset.range N₀, f N
  have hC_pos : 0 < C := by
    have : 0 ≤ ∑ N ∈ Finset.range N₀, f N := Finset.sum_nonneg fun N _ => by
      dsimp [f]; positivity
    linarith
  have hf_le_C : ∀ N : ℕ, f N ≤ C := by
    intro N
    by_cases hN : N < N₀
    · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.2 hN
      have h1 : f N ≤ ∑ k ∈ Finset.range N₀, f k :=
        Finset.single_le_sum (fun k _ => by dsimp [f]; positivity) hmem
      linarith
    · push Not at hN
      have h1 : f N ≤ 1 := hN₀ N hN
      have h2 : 0 ≤ ∑ k ∈ Finset.range N₀, f k := Finset.sum_nonneg fun k _ => by
        dsimp [f]; positivity
      linarith
  refine ⟨C, hC_pos, fun U hU_meas hU_diam => ?_⟩
  by_cases hdiam0 : ediam U = 0
  · have hsub : U.Subsingleton := Metric.ediam_eq_zero_iff.1 hdiam0
    have hμ0 : μ j₀ α U = 0 := by
      rcases hsub.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
      · simp
      · exact μ_singleton_zero hα0 hα1 hj₀1 hj₀2 x
    rw [hμ0]
    exact bot_le
  · haveI : ∀ j, IsProbabilityMeasure (νj j₀ α j) := isProbabilityMeasure_νj hα0 hj₀2
    have hdiam_pos : 0 < ediam U := pos_iff_ne_zero.2 hdiam0
    have hdiam_lt_top : ediam U < ⊤ :=
      lt_of_le_of_lt hU_diam ENNReal.ofReal_lt_top
    let r : ℝ := (ediam U).toReal
    have hr_pos : 0 < r := ENNReal.toReal_pos hdiam0 hdiam_lt_top.ne
    have hr_le : r ≤ 1 / (2 * (Q j₀ 1 : ℝ)) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU_diam
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hr_lt : r < 1 / (Q j₀ 1 : ℝ) := by
      have hQ1 : (0 : ℝ) < (Q j₀ 1 : ℝ) := by exact_mod_cast Q_pos j₀ 1
      linarith [show 1 / (2 * (Q j₀ 1 : ℝ)) < 1 / (Q j₀ 1 : ℝ) by
        rw [one_div, one_div, inv_lt_inv₀ (by positivity) hQ1]; linarith]
    have hex_N : ∃ N : ℕ, 1 / (Q j₀ (N + 2) : ℝ) ≤ r := by
      have h_tend : Tendsto (fun N : ℕ => 1 / (Q j₀ (N + 2) : ℝ)) atTop (𝓝 0) := by
        have h8 : Tendsto (fun N : ℕ => (1 / 8 : ℝ) ^ (N + 2)) atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 8 : ℝ) < 1)).comp
            (tendsto_add_atTop_nat 2)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h8
          (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall fun N => ?_)
        have hQ : (8 : ℝ) ^ (N + 2) ≤ (Q j₀ (N + 2) : ℝ) := by
          exact_mod_cast Q_ge_eight_pow hα0 hα1 hj₀1 hj₀2 (N + 2)
        rw [one_div_pow, one_div, one_div]
        exact inv_anti₀ (by positivity) hQ
      obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (h_tend.eventually_le_const hr_pos)
      exact ⟨a, ha a le_rfl⟩
    classical
    let N : ℕ := Nat.find hex_N
    have hN_lower : 1 / (Q j₀ (N + 2) : ℝ) ≤ r := Nat.find_spec hex_N
    have hN_upper : r < 1 / (Q j₀ (N + 1) : ℝ) := by
      rcases eq_or_ne N 0 with h0 | hpos
      · simpa [h0] using hr_lt
      · have hlt := Nat.find_min hex_N (Nat.pred_lt hpos)
        push Not at hlt
        rwa [show (Nat.find hex_N).pred + 2 = N + 1 by dsimp [N]; omega] at hlt
    have hdist_le : ∀ {x y : ℝ}, x ∈ U → y ∈ U → |x - y| ≤ r := by
      intro x y hx hy
      rw [← Real.dist_eq, ← ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist x y), ← edist_dist]
      exact ENNReal.toReal_mono hdiam_lt_top.ne (Metric.edist_le_ediam_of_mem hx hy)
    let Pref : Type := ∀ j : Fin (N + 1), Fin (D j₀ α j)
    let S₁ : Finset Pref := Finset.univ.filter fun p =>
      ∃ d ∈ π j₀ α ⁻¹' U, (fun j : Fin (N + 1) => d j) = p
    have hS₁_card : S₁.card ≤ 3 := by
      by_contra h4
      push Not at h4
      have hrep : ∀ p ∈ S₁, ∃ d ∈ π j₀ α ⁻¹' U, (fun j : Fin (N + 1) => d j) = p :=
        fun p hp => (Finset.mem_filter.1 hp).2
      choose rep hrep_mem hrep_eq using hrep
      let T : Finset ℝ := S₁.attach.image fun p => π j₀ α (rep p.1 p.2)
      have hT_inj : Function.Injective (fun p : S₁ => π j₀ α (rep p.1 p.2)) := by
        intro p₁ p₂ hp
        by_contra hne
        have hpne : p₁.1 ≠ p₂.1 := fun h => hne (Subtype.ext h)
        have hexj : ∃ j < N + 1, rep p₁.1 p₁.2 j ≠ rep p₂.1 p₂.2 j := by
          by_contra hall
          push Not at hall
          apply hpne
          funext j
          rw [← hrep_eq p₁.1 p₁.2, ← hrep_eq p₂.1 p₂.2]
          exact hall j j.isLt
        have hsep := π_prefix_sep hα0 hα1 hj₀1 hj₀2 hexj
        dsimp only at hp
        rw [hp, sub_self, abs_zero] at hsep
        have hQpos : (0 : ℝ) < (Q j₀ (N + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (N + 1)
        linarith [show (0 : ℝ) < 1 / (2 * (Q j₀ (N + 1) : ℝ)) by positivity]
      have hT_card : 4 ≤ T.card := by
        rw [Finset.card_image_of_injective _ hT_inj, Finset.card_attach]
        exact h4
      let l : List ℝ := T.sort (· ≤ ·)
      have hl_len : 4 ≤ l.length := by simpa [l, T.length_sort] using hT_card
      have hl_sorted : l.Pairwise (· ≤ ·) := T.pairwise_sort (· ≤ ·)
      have hl_nodup : l.Nodup := T.sort_nodup (· ≤ ·)
      have hl_mem : ∀ i (hi : i < l.length), l[i] ∈ U := by
        intro i hi
        have hmemT : l[i] ∈ T := (T.mem_sort (· ≤ ·)).1 (List.getElem_mem hi)
        rcases Finset.mem_image.1 hmemT with ⟨p, _, hp⟩
        rw [← hp]
        exact hrep_mem p.1 p.2
      have h_adj : ∀ i (hi : i + 1 < l.length),
          1 / (2 * (Q j₀ (N + 1) : ℝ)) ≤ l[i + 1] - l[i] := by
        intro i hi
        have hle : l[i] ≤ l[i + 1] :=
          List.pairwise_iff_getElem.1 hl_sorted i (i + 1) (Nat.lt_of_succ_lt hi) hi (Nat.lt_succ_self i)
        have hne : l[i] ≠ l[i + 1] := fun h => by
          have := (List.nodup_iff_injective_getElem.1 hl_nodup)
            (a₁ := ⟨i, Nat.lt_of_succ_lt hi⟩) (a₂ := ⟨i + 1, hi⟩) h
          simp at this
        have hlt : l[i] < l[i + 1] := lt_of_le_of_ne hle hne
        have hmem1 : l[i] ∈ T := (T.mem_sort (· ≤ ·)).1 (List.getElem_mem (Nat.lt_of_succ_lt hi))
        have hmem2 : l[i + 1] ∈ T := (T.mem_sort (· ≤ ·)).1 (List.getElem_mem hi)
        rcases Finset.mem_image.1 hmem1 with ⟨p₁, _, hp₁⟩
        rcases Finset.mem_image.1 hmem2 with ⟨p₂, _, hp₂⟩
        have hpne : p₁.1 ≠ p₂.1 := by
          intro h
          have : l[i] = l[i + 1] := by rw [← hp₁, ← hp₂, Subtype.ext h]
          linarith
        have hexj : ∃ j < N + 1, rep p₁.1 p₁.2 j ≠ rep p₂.1 p₂.2 j := by
          by_contra hall
          push Not at hall
          apply hpne
          funext j
          rw [← hrep_eq p₁.1 p₁.2, ← hrep_eq p₂.1 p₂.2]
          exact hall j j.isLt
        have hsep := π_prefix_sep hα0 hα1 hj₀1 hj₀2 hexj
        rw [hp₁, hp₂, abs_of_neg (sub_neg.2 hlt), neg_sub] at hsep
        exact hsep
      have h01 := h_adj 0 (by omega)
      have h12 := h_adj 1 (by omega)
      have h23 := h_adj 2 (by omega)
      have h03 : l[3] - l[0] ≤ r := by
        have := hdist_le (hl_mem 3 (by omega)) (hl_mem 0 (by omega))
        exact (le_abs_self _).trans this
      have h_sum : 3 / (2 * (Q j₀ (N + 1) : ℝ)) ≤ r := by
        have h3 : 3 / (2 * (Q j₀ (N + 1) : ℝ)) =
            1 / (2 * (Q j₀ (N + 1) : ℝ)) + 1 / (2 * (Q j₀ (N + 1) : ℝ)) +
            1 / (2 * (Q j₀ (N + 1) : ℝ)) := by ring
        linarith
      have hQpos : (0 : ℝ) < (Q j₀ (N + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (N + 1)
      have h1 : 1 / (Q j₀ (N + 1) : ℝ) ≤ 3 / (2 * (Q j₀ (N + 1) : ℝ)) := by
        rw [show 3 / (2 * (Q j₀ (N + 1) : ℝ)) = (3 / 2 : ℝ) / (Q j₀ (N + 1) : ℝ) by ring]
        gcongr
        norm_num
      linarith
    let S₂ : Pref → Finset (Fin (D j₀ α (N + 1))) := fun p =>
      Finset.univ.filter fun k =>
        ∃ d ∈ π j₀ α ⁻¹' U, (fun j : Fin (N + 1) => d j) = p ∧ d (N + 1) = k
    have hS₂_card : ∀ p : Pref, ((S₂ p).card : ℝ) ≤
        min (D j₀ α (N + 1) : ℝ) (4 * r * (Q j₀ (N + 2) : ℝ)) := by
      intro p
      refine le_min (by exact_mod_cast (S₂ p).card_le_univ.trans_eq (Fintype.card_fin _)) ?_
      by_cases h0 : (S₂ p).card = 0
      · simp [h0]; positivity
      · have hrep : ∀ k ∈ S₂ p, ∃ d ∈ π j₀ α ⁻¹' U, (fun j : Fin (N + 1) => d j) = p ∧ d (N + 1) = k :=
          fun k hk => (Finset.mem_filter.1 hk).2
        choose rep hrep_mem hrep_p hrep_k using hrep
        let T : Finset ℝ := (S₂ p).attach.image fun k => π j₀ α (rep k.1 k.2)
        have hT_inj : Function.Injective (fun k : S₂ p => π j₀ α (rep k.1 k.2)) := by
          intro k₁ k₂ hk
          by_contra hne
          have hkne : k₁.1 ≠ k₂.1 := fun h => hne (Subtype.ext h)
          have hexj : ∃ j < N + 2, rep k₁.1 k₁.2 j ≠ rep k₂.1 k₂.2 j :=
            ⟨N + 1, Nat.lt_succ_self _, by rw [hrep_k k₁.1 k₁.2, hrep_k k₂.1 k₂.2]; exact hkne⟩
          have hsep := π_prefix_sep hα0 hα1 hj₀1 hj₀2 hexj
          dsimp only at hk
          rw [hk, sub_self, abs_zero] at hsep
          have hQpos : (0 : ℝ) < (Q j₀ (N + 2) : ℝ) := by exact_mod_cast Q_pos j₀ (N + 2)
          linarith [show (0 : ℝ) < 1 / (2 * (Q j₀ (N + 2) : ℝ)) by positivity]
        have hT_card : T.card = (S₂ p).card := by
          rw [Finset.card_image_of_injective _ hT_inj, Finset.card_attach]
        let l : List ℝ := T.sort (· ≤ ·)
        have hl_len : l.length = (S₂ p).card := by simpa [l, T.length_sort] using hT_card
        have hl_sorted : l.Pairwise (· ≤ ·) := T.pairwise_sort (· ≤ ·)
        have hl_nodup : l.Nodup := T.sort_nodup (· ≤ ·)
        have hl_mem : ∀ i (hi : i < l.length), l[i] ∈ U := by
          intro i hi
          have hmemT : l[i] ∈ T := (T.mem_sort (· ≤ ·)).1 (List.getElem_mem hi)
          rcases Finset.mem_image.1 hmemT with ⟨k, _, hk⟩
          rw [← hk]
          exact hrep_mem k.1 k.2
        have h_adj : ∀ i (hi : i + 1 < l.length),
            1 / (2 * (Q j₀ (N + 2) : ℝ)) ≤ l[i + 1] - l[i] := by
          intro i hi
          have hle : l[i] ≤ l[i + 1] :=
            List.pairwise_iff_getElem.1 hl_sorted i (i + 1) (Nat.lt_of_succ_lt hi) hi (Nat.lt_succ_self i)
          have hne : l[i] ≠ l[i + 1] := fun h => by
            have := (List.nodup_iff_injective_getElem.1 hl_nodup)
              (a₁ := ⟨i, Nat.lt_of_succ_lt hi⟩) (a₂ := ⟨i + 1, hi⟩) h
            simp at this
          have hlt : l[i] < l[i + 1] := lt_of_le_of_ne hle hne
          have hmem1 : l[i] ∈ T := (T.mem_sort (· ≤ ·)).1 (List.getElem_mem (Nat.lt_of_succ_lt hi))
          have hmem2 : l[i + 1] ∈ T := (T.mem_sort (· ≤ ·)).1 (List.getElem_mem hi)
          rcases Finset.mem_image.1 hmem1 with ⟨k₁, _, hk₁⟩
          rcases Finset.mem_image.1 hmem2 with ⟨k₂, _, hk₂⟩
          have hkne : k₁.1 ≠ k₂.1 := by
            intro h
            have : l[i] = l[i + 1] := by rw [← hk₁, ← hk₂, Subtype.ext h]
            linarith
          have hexj : ∃ j < N + 2, rep k₁.1 k₁.2 j ≠ rep k₂.1 k₂.2 j :=
            ⟨N + 1, Nat.lt_succ_self _, by rw [hrep_k k₁.1 k₁.2, hrep_k k₂.1 k₂.2]; exact hkne⟩
          have hsep := π_prefix_sep hα0 hα1 hj₀1 hj₀2 hexj
          rw [hk₁, hk₂, abs_of_neg (sub_neg.2 hlt), neg_sub] at hsep
          exact hsep
        have h_tele : ((l.length - 1 : ℕ) : ℝ) / (2 * (Q j₀ (N + 2) : ℝ)) ≤
            l[l.length - 1]'(Nat.sub_lt (by omega) Nat.one_pos) - l[0]'(by omega) := by
          have h_ind : ∀ m (hm : m < l.length),
              (m : ℝ) / (2 * (Q j₀ (N + 2) : ℝ)) ≤ l[m]'hm - l[0]'(by omega) := by
            intro m hm
            induction m with
            | zero => simp
            | succ m ih =>
              have hm' : m < l.length := Nat.lt_of_succ_lt hm
              have h1 := ih hm'
              have h2 := h_adj m hm
              push_cast
              linarith [show ((m : ℝ) + 1) / (2 * (Q j₀ (N + 2) : ℝ)) =
                (m : ℝ) / (2 * (Q j₀ (N + 2) : ℝ)) + 1 / (2 * (Q j₀ (N + 2) : ℝ)) by ring]
          exact h_ind (l.length - 1) (Nat.sub_lt (by omega) Nat.one_pos)
        have h_end : l[l.length - 1]'(Nat.sub_lt (by omega) Nat.one_pos) - l[0]'(by omega) ≤ r := by
          have := hdist_le (hl_mem (l.length - 1) (Nat.sub_lt (by omega) Nat.one_pos)) (hl_mem 0 (by omega))
          exact (le_abs_self _).trans this
        have hQpos : (0 : ℝ) < (Q j₀ (N + 2) : ℝ) := by exact_mod_cast Q_pos j₀ (N + 2)
        have h_len1 : (((S₂ p).card : ℝ) - 1) / (2 * (Q j₀ (N + 2) : ℝ)) ≤ r := by
          have hcast : ((l.length - 1 : ℕ) : ℝ) = ((S₂ p).card : ℝ) - 1 := by
            rw [hl_len, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 h0)]
            simp
          rw [← hcast]
          exact h_tele.trans h_end
        have h_len2 : ((S₂ p).card : ℝ) - 1 ≤ 2 * r * (Q j₀ (N + 2) : ℝ) := by
          rw [div_le_iff₀ (by positivity)] at h_len1
          linarith
        have h_one : 1 ≤ r * (Q j₀ (N + 2) : ℝ) := by
          rw [one_div, inv_eq_one_div, div_le_iff₀ hQpos] at hN_lower
          exact hN_lower
        linarith
    let cyl : ∀ (p : Pref) (k : Fin (D j₀ α (N + 1))), Set (Ω j₀ α) := fun p k =>
      MeasureTheory.cylinder (Finset.range (N + 2))
        {g | (∀ j : Fin (N + 1), g ⟨j, Finset.mem_range.2 (Nat.lt_trans j.isLt (Nat.lt_succ_self _))⟩ = p j) ∧
             g ⟨N + 1, Finset.mem_range.2 (Nat.lt_succ_self _)⟩ = k}
    have h_cover : π j₀ α ⁻¹' U ⊆ ⋃ p ∈ S₁, ⋃ k ∈ S₂ p, cyl p k := by
      intro d hd
      let p : Pref := fun j => d j
      let k : Fin (D j₀ α (N + 1)) := d (N + 1)
      have hp : p ∈ S₁ := Finset.mem_filter.2 ⟨Finset.mem_univ _, d, hd, rfl⟩
      have hk : k ∈ S₂ p := Finset.mem_filter.2 ⟨Finset.mem_univ _, d, hd, rfl, rfl⟩
      refine mem_biUnion hp (mem_biUnion hk ?_)
      simp [cyl, MeasureTheory.cylinder, p, k]
    have h_cyl_meas : ∀ p k, ν j₀ α (cyl p k) = (P j₀ α (N + 2) : ℝ≥0∞)⁻¹ := by
      intro p k
      let g₀ : ∀ i : Finset.range (N + 2), Fin (D j₀ α i) := fun i =>
        if h : i.1 < N + 1 then p ⟨i.1, h⟩
        else (have heq : i.1 = N + 1 := by
                have := Finset.mem_range.1 i.2
                omega
              heq ▸ k)
      have hset : {g : ∀ i : Finset.range (N + 2), Fin (D j₀ α i) |
          (∀ j : Fin (N + 1), g ⟨j, Finset.mem_range.2 (Nat.lt_trans j.isLt (Nat.lt_succ_self _))⟩ = p j) ∧
          g ⟨N + 1, Finset.mem_range.2 (Nat.lt_succ_self _)⟩ = k} = {g₀} := by
        ext g
        simp only [mem_ofPred_eq, mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          funext ⟨i, hi⟩
          dsimp [g₀]
          split_ifs with hlt
          · exact h1 ⟨i, hlt⟩
          · have heq : i = N + 1 := by
              have := Finset.mem_range.1 hi
              omega
            subst heq
            exact h2
        · rintro rfl
          refine ⟨fun j => ?_, ?_⟩
          · dsimp [g₀]
            simp [j.isLt]
          · dsimp [g₀]
            simp
      dsimp [cyl]
      rw [hset]
      exact ν_cylinder_singleton hα0 hj₀2 (N + 2) g₀
    have hμU : μ j₀ α U ≤
        (∑ p ∈ S₁, ∑ _k ∈ S₂ p, (P j₀ α (N + 2) : ℝ≥0∞)⁻¹) := by
      unfold μ
      rw [Measure.map_apply (measurable_π hα0 hα1 hj₀1 hj₀2) hU_meas]
      refine (measure_mono h_cover).trans ?_
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine Finset.sum_le_sum fun p _ => ?_
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine Finset.sum_le_sum fun k _ => ?_
      rw [h_cyl_meas p k]
    have hP_pos : (0 : ℝ) < (P j₀ α (N + 2) : ℝ) := by exact_mod_cast P_pos hα0 hj₀2 (N + 2)
    have h_real_bound : (μ j₀ α U).toReal ≤ f N * r ^ (s : ℝ) := by
      have h1 : (μ j₀ α U).toReal ≤
          ((∑ p ∈ S₁, ∑ _k ∈ S₂ p, (P j₀ α (N + 2) : ℝ≥0∞)⁻¹) : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by
          refine ne_of_lt (ENNReal.sum_lt_top.2 fun p _ => ENNReal.sum_lt_top.2 fun k _ => ?_)
          exact ENNReal.inv_lt_top.2 (by exact_mod_cast P_pos hα0 hj₀2 (N + 2))) hμU
      have h2 : ((∑ p ∈ S₁, ∑ _k ∈ S₂ p, (P j₀ α (N + 2) : ℝ≥0∞)⁻¹) : ℝ≥0∞).toReal =
          ∑ p ∈ S₁, ((S₂ p).card : ℝ) / (P j₀ α (N + 2) : ℝ) := by
        rw [ENNReal.toReal_sum (fun p _ => ne_of_lt (ENNReal.sum_lt_top.2 fun _ _ =>
          ENNReal.inv_lt_top.2 (by exact_mod_cast P_pos hα0 hj₀2 (N + 2))))]
        simp [Finset.sum_const, div_eq_mul_inv]
      rw [h2] at h1
      refine h1.trans ?_
      have h3 : ∑ p ∈ S₁, ((S₂ p).card : ℝ) / (P j₀ α (N + 2) : ℝ) ≤
          ∑ _p ∈ S₁, ((D j₀ α (N + 1) : ℝ) ^ (1 - (s : ℝ)) *
            (4 * r * (Q j₀ (N + 2) : ℝ)) ^ (s : ℝ)) / (P j₀ α (N + 2) : ℝ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hmin : ((S₂ p).card : ℝ) ≤ (D j₀ α (N + 1) : ℝ) ^ (1 - (s : ℝ)) *
            (4 * r * (Q j₀ (N + 2) : ℝ)) ^ (s : ℝ) :=
          (hS₂_card p).trans (min_le_rpow_mul_rpow (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hr_pos.le) (Nat.cast_nonneg _)) hs0.le hs1.le)
        exact div_le_div_of_nonneg_right hmin hP_pos.le
      refine h3.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hS₁_r : (S₁.card : ℝ) ≤ 3 := by exact_mod_cast hS₁_card
      have hP_succ : (P j₀ α (N + 2) : ℝ) = (P j₀ α (N + 1) : ℝ) * (D j₀ α (N + 1) : ℝ) := by
        exact_mod_cast P_succ j₀ α (N + 1)
      have hQ_succ : (Q j₀ (N + 2) : ℝ) = (Q j₀ (N + 1) : ℝ) * (q j₀ (N + 1) : ℝ) := by
        exact_mod_cast Q_succ j₀ (N + 1)
      have hDpos : (0 : ℝ) < (D j₀ α (N + 1) : ℝ) := by exact_mod_cast D_pos hα0 hj₀2 (N + 1)
      have hQpos : (0 : ℝ) < (Q j₀ (N + 1) : ℝ) := by exact_mod_cast Q_pos j₀ (N + 1)
      have hqpos : (0 : ℝ) < (q j₀ (N + 1) : ℝ) := by exact_mod_cast q_pos j₀ (N + 1)
      calc
        (S₁.card : ℝ) * (((D j₀ α (N + 1) : ℝ) ^ (1 - (s : ℝ)) *
            (4 * r * (Q j₀ (N + 2) : ℝ)) ^ (s : ℝ)) / (P j₀ α (N + 2) : ℝ))
            ≤ 3 * (((D j₀ α (N + 1) : ℝ) ^ (1 - (s : ℝ)) *
                (4 * r * (Q j₀ (N + 2) : ℝ)) ^ (s : ℝ)) / (P j₀ α (N + 2) : ℝ)) := by
              gcongr
        _ = f N * r ^ (s : ℝ) := by
              dsimp [f]
              rw [hP_succ, hQ_succ]
              exact alg_step hDpos hQpos.le hqpos.le hr_pos.le
    have hμ_lt_top : μ j₀ α U ≠ ⊤ := by
      haveI : IsProbabilityMeasure (ν j₀ α) := by unfold ν; infer_instance
      have h_le_one : μ j₀ α U ≤ 1 := by
        unfold μ
        rw [Measure.map_apply (measurable_π hα0 hα1 hj₀1 hj₀2) hU_meas]
        exact (measure_mono (subset_univ _)).trans_eq measure_univ
      exact ne_top_of_le_ne_top ENNReal.one_ne_top h_le_one
    rw [← ENNReal.ofReal_toReal hμ_lt_top]
    calc
      ENNReal.ofReal (μ j₀ α U).toReal
          ≤ ENNReal.ofReal (f N * r ^ (s : ℝ)) := ENNReal.ofReal_le_ofReal h_real_bound
      _ ≤ ENNReal.ofReal (C * r ^ (s : ℝ)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            gcongr
            exact hf_le_C N
      _ = ENNReal.ofReal C * ENNReal.ofReal (r ^ (s : ℝ)) :=
            ENNReal.ofReal_mul hC_pos.le
      _ = ENNReal.ofReal C * ediam U ^ (s : ℝ) := by
            congr 1
            rw [← ENNReal.ofReal_rpow_of_pos hr_pos, ENNReal.ofReal_toReal hdiam_lt_top.ne]

private lemma hausdorffMeasure_K_ne_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ)))
    {s : ℝ≥0} (hs0 : 0 < (s : ℝ)) (hsα : (s : ℝ) < α) :
    μH[(s : ℝ)] (K j₀ α) ≠ 0 := by
  haveI : ∀ j, IsProbabilityMeasure (νj j₀ α j) := isProbabilityMeasure_νj hα0 hj₀2
  haveI : IsProbabilityMeasure (ν j₀ α) := by unfold ν; infer_instance
  obtain ⟨C, hC_pos, h_ball⟩ := μ_ball_bound hα0 hα1 hj₀1 hj₀2 hs0 hsα
  let r₀ : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * (Q j₀ 1 : ℝ)))
  have hr₀ : 0 < r₀ := by
    refine ENNReal.ofReal_pos.2 ?_
    have : (0 : ℝ) < (Q j₀ 1 : ℝ) := by exact_mod_cast Q_pos j₀ 1
    positivity
  have h_lower : (ENNReal.ofReal C)⁻¹ ≤ μH[(s : ℝ)] (K j₀ α) := by
    rw [Measure.hausdorffMeasure_apply]
    refine le_iSup₂_of_le r₀ hr₀ (le_iInf₂ fun t ht_cov => le_iInf fun ht_diam => ?_)
    have h_one : (1 : ℝ≥0∞) ≤ ∑' n : ℕ, μ j₀ α (closure (t n)) := by
      rw [← measure_univ (μ := ν j₀ α)]
      have hsub : Set.univ ⊆ π j₀ α ⁻¹' (⋃ n, closure (t n)) := by
        intro d _
        have hd : π j₀ α d ∈ K j₀ α := ⟨d, rfl⟩
        rcases mem_iUnion.1 (ht_cov hd) with ⟨n, hn⟩
        exact mem_iUnion.2 ⟨n, subset_closure hn⟩
      refine (measure_mono hsub).trans ?_
      rw [preimage_iUnion]
      refine (measure_iUnion_le _).trans ?_
      refine ENNReal.tsum_le_tsum fun n => ?_
      unfold μ
      rw [Measure.map_apply (measurable_π hα0 hα1 hj₀1 hj₀2) isClosed_closure.measurableSet]
    have h_term : ∀ n : ℕ,
        μ j₀ α (closure (t n)) ≤ ENNReal.ofReal C * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (s : ℝ) := by
      intro n
      by_cases hne : (t n).Nonempty
      · have hd : ediam (closure (t n)) ≤ r₀ := by
          rw [Metric.ediam_closure]
          exact ht_diam n
        have hb := h_ball (closure (t n)) isClosed_closure.measurableSet hd
        rw [Metric.ediam_closure] at hb
        refine hb.trans ?_
        gcongr
        exact le_iSup (fun _ : (t n).Nonempty => ediam (t n) ^ (s : ℝ)) hne
      · have hempty : t n = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
        simp [hempty]
    have h_sum : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C *
        ∑' n : ℕ, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (s : ℝ) := by
      refine h_one.trans ((ENNReal.tsum_le_tsum h_term).trans ?_)
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.inv_le_iff_le_mul (fun _ => (ENNReal.ofReal_pos.2 hC_pos).ne')
      (fun h => absurd h ENNReal.ofReal_ne_top)]
    exact h_sum
  have h_pos : 0 < (ENNReal.ofReal C)⁻¹ := ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
  exact ne_of_gt (lt_of_lt_of_le h_pos h_lower)

private lemma le_dimH_G {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j₀ : ℕ}
    (hj₀1 : 8 ≤ (2 : ℝ) ^ ((1 - α) * (j₀ : ℝ)))
    (hj₀2 : 2 ≤ (2 : ℝ) ^ (α * (j₀ : ℝ))) :
    ENNReal.ofReal α ≤ dimH (G j₀ α : Set ℝ) := by
  refine le_trans ?_ (dimH_mono (AddSubgroup.subset_closure : K j₀ α ⊆ (G j₀ α : Set ℝ)))
  refine le_of_forall_lt fun t ht => ?_
  by_cases ht0 : t = 0
  · subst ht0
    by_contra hle
    have h0 : dimH (K j₀ α) = 0 := le_antisymm (not_lt.1 hle) bot_le
    let s : ℝ≥0 := ⟨α / 2, by linarith⟩
    have hs0 : 0 < (s : ℝ) := by change 0 < α / 2; linarith
    have hsα : (s : ℝ) < α := by change α / 2 < α; linarith
    have hne := hausdorffMeasure_K_ne_zero hα0 hα1 hj₀1 hj₀2 hs0 hsα
    have hle' := le_dimH_of_hausdorffMeasure_ne_zero hne
    rw [h0] at hle'
    have : (s : ℝ≥0∞) = 0 := le_antisymm hle' bot_le
    simp at this
    linarith [show (s : ℝ) = 0 by exact_mod_cast this]
  · have ht_lt_top : t < ⊤ := lt_of_lt_of_le ht le_top
    let s : ℝ≥0 := t.toNNReal
    have hs_eq : (s : ℝ≥0∞) = t := ENNReal.coe_toNNReal ht_lt_top.ne
    have hs0 : 0 < (s : ℝ) := by
      rw [NNReal.coe_pos]
      exact ENNReal.toNNReal_pos ht0 ht_lt_top.ne
    have hsα : (s : ℝ) < α := by
      refine (ENNReal.ofReal_lt_ofReal_iff hα0).1 ?_
      rw [ENNReal.ofReal_coe_nnreal, hs_eq]
      exact ht
    have hne := hausdorffMeasure_K_ne_zero hα0 hα1 hj₀1 hj₀2 hs0 hsα
    have hle' := le_dimH_of_hausdorffMeasure_ne_zero hne
    rw [hs_eq] at hle'
    rcases lt_or_eq_of_le hle' with h | h_eq
    · exact h
    · let s' : ℝ≥0 := ⟨((s : ℝ) + α) / 2, by positivity⟩
      have hs'0 : (s : ℝ) < (s' : ℝ) := by change (s : ℝ) < ((s : ℝ) + α) / 2; linarith
      have hs'α : (s' : ℝ) < α := by change ((s : ℝ) + α) / 2 < α; linarith
      have hne' := hausdorffMeasure_K_ne_zero hα0 hα1 hj₀1 hj₀2 (hs0.trans hs'0) hs'α
      have hle'' := le_dimH_of_hausdorffMeasure_ne_zero hne'
      have hlt'' : t < (s' : ℝ≥0∞) := by
        rw [← hs_eq, ENNReal.coe_lt_coe]
        exact_mod_cast hs'0
      exact lt_of_lt_of_le hlt'' hle''

end Erdos1154GroupProof

theorem OMA.solution : type_of% @Erdos1154.erdos_1154.variants.group := by
  intro a ha
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨⊥, ?_⟩
    rw [AddSubgroup.coe_bot]
    exact (Set.countable_singleton (0 : ℝ)).dimH_zero
  · by_cases ha1 : a = 1
    · subst ha1
      refine ⟨⊤, ?_⟩
      rw [AddSubgroup.coe_top, Real.dimH_univ]
    · have ha_pos : 0 < a := pos_iff_ne_zero.2 ha0
      have ha_lt : a < 1 := lt_of_le_of_ne ha.2 ha1
      have ha_ne_top : a ≠ ⊤ := ne_top_of_lt ha_lt
      let α : ℝ := a.toReal
      have hα0 : 0 < α := ENNReal.toReal_pos ha0 ha_ne_top
      have hα1 : α < 1 := by
        have := ENNReal.toReal_strict_mono ENNReal.one_ne_top ha_lt
        simpa [α] using this
      have hα_eq : ENNReal.ofReal α = a := ENNReal.ofReal_toReal ha_ne_top
      obtain ⟨j₀, hj₀1, hj₀2⟩ := Erdos1154GroupProof.exists_j₀ hα0 hα1
      refine ⟨Erdos1154GroupProof.G j₀ α, ?_⟩
      apply le_antisymm
      · exact (Erdos1154GroupProof.dimH_G_le hα0 hα1 hj₀1 hj₀2).trans_eq hα_eq
      · exact hα_eq.symm.trans_le (Erdos1154GroupProof.le_dimH_G hα0 hα1 hj₀1 hj₀2)
