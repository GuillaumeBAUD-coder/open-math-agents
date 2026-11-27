import OMAStatements.S_oeis_a329813
import Mathlib

namespace A329813

open Filter Topology

noncomputable def sol (s t : ℝ) : ℕ → ℝ
  | 0 => s
  | 1 => t
  | n + 2 => ((n : ℝ) + 2) * sol s t (n + 1) / sol s t n

lemma sol_zero (s t : ℝ) : sol s t 0 = s := by
  rw [sol]

lemma sol_one (s t : ℝ) : sol s t 1 = t := by
  rw [sol]

lemma sol_rec (s t : ℝ) : OMA.S_oeis_a329813.recurrence (sol s t) := by
  intro n
  rw [sol]

lemma ne_zero (b : ℕ → ℝ) (h0 : b 0 ≠ 0) (h1 : b 1 ≠ 0)
    (hr : OMA.S_oeis_a329813.recurrence b) : ∀ n, b n ≠ 0 ∧ b (n + 1) ≠ 0 := by
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [hr k]
    exact div_ne_zero (mul_ne_zero (by positivity) ih.2) ih.1

lemma three (b : ℕ → ℝ) (h0 : b 0 ≠ 0) (h1 : b 1 ≠ 0)
    (hr : OMA.S_oeis_a329813.recurrence b) (n : ℕ) :
    b (n + 3) * b n = ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
  have hn := (ne_zero b h0 h1 hr n).1
  have hn1 := (ne_zero b h0 h1 hr n).2
  have e1 : b (n + 2) = ((n : ℝ) + 2) * b (n + 1) / b n := hr n
  have e2 : b (n + 3) = (((n + 1 : ℕ) : ℝ) + 2) * b (n + 2) / b (n + 1) := hr (n + 1)
  rw [e2, e1]
  push_cast
  field_simp
  ring

lemma six (b : ℕ → ℝ) (h0 : b 0 ≠ 0) (h1 : b 1 ≠ 0)
    (hr : OMA.S_oeis_a329813.recurrence b) (n : ℕ) :
    b (n + 6) * (((n : ℝ) + 2) * ((n : ℝ) + 3)) = ((n : ℝ) + 5) * ((n : ℝ) + 6) * b n := by
  have t1 := three b h0 h1 hr n
  have t2 : b (n + 6) * b (n + 3) = (((n + 3 : ℕ) : ℝ) + 2) * (((n + 3 : ℕ) : ℝ) + 3) :=
    three b h0 h1 hr (n + 3)
  push_cast at t2
  linear_combination b n * t2 - b (n + 6) * t1

lemma lim_aux : Tendsto (fun n : ℕ => 1 + (2 : ℝ) / (6 * (n : ℝ) + 1)) atTop (𝓝 1) := by
  have hlin : Tendsto (fun n : ℕ => 6 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 6))
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) / (6 * (n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlin
  have h3 := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h2
  simpa using h3

lemma prod_one (b c : ℕ → ℝ) (h0 : b 0 ≠ 0) (h1 : b 1 ≠ 0)
    (hr : OMA.S_oeis_a329813.recurrence b) (hc : OMA.S_oeis_a329813.limitCycle b c) :
    c 1 * c 4 = 1 := by
  have t1 := hc.1 1 (by norm_num) (by norm_num)
  have t4 := hc.1 4 (by norm_num) (by norm_num)
  have tp := t1.mul t4
  have key : ∀ n : ℕ, b (6 * n + 1) / ((6 * n + 1 : ℕ) : ℝ) * (b (6 * n + 4) / ((6 * n + 4 : ℕ) : ℝ))
      = 1 + (2 : ℝ) / (6 * (n : ℝ) + 1) := by
    intro n
    have h3 : b (6 * n + 4) * b (6 * n + 1) =
        (((6 * n + 1 : ℕ) : ℝ) + 2) * (((6 * n + 1 : ℕ) : ℝ) + 3) := three b h0 h1 hr (6 * n + 1)
    push_cast at h3
    push_cast
    have hp1 : (6 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hp4 : (6 * (n : ℝ) + 4) ≠ 0 := by positivity
    rw [div_mul_div_comm, mul_comm (b (6 * n + 1)) (b (6 * n + 4)), h3]
    field_simp
    ring
  have tp' : Tendsto (fun n : ℕ => 1 + (2 : ℝ) / (6 * (n : ℝ) + 1)) atTop (𝓝 (c 1 * c 4)) :=
    tp.congr key
  exact tendsto_nhds_unique tp' lim_aux

lemma prop (t : ℝ) (ht : t ≠ 0) : ∀ n : ℕ, sol 1 t (6 * n + 1) = t * sol 1 1 (6 * n + 1) := by
  intro n
  induction n with
  | zero =>
    show sol 1 t 1 = t * sol 1 1 1
    rw [sol_one, sol_one, mul_one]
  | succ k ih =>
    have e : 6 * (k + 1) + 1 = 6 * k + 1 + 6 := by ring
    rw [e]
    have s1 := six (sol 1 t) (by rw [sol_zero]; exact one_ne_zero) (by rw [sol_one]; exact ht)
      (sol_rec 1 t) (6 * k + 1)
    have s2 := six (sol 1 1) (by rw [sol_zero]; exact one_ne_zero) (by rw [sol_one]; exact one_ne_zero)
      (sol_rec 1 1) (6 * k + 1)
    have hK : (((6 * k + 1 : ℕ) : ℝ) + 2) * (((6 * k + 1 : ℕ) : ℝ) + 3) ≠ 0 := by positivity
    apply mul_right_cancel₀ hK
    linear_combination s1 - t * s2 + ((((6 * k + 1 : ℕ) : ℝ) + 5) * (((6 * k + 1 : ℕ) : ℝ) + 6)) * ih

end A329813

open Filter Topology in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a329813.main) := by
  intro H
  have b0 : ∀ t : ℝ, A329813.sol 1 t 0 ≠ 0 := by
    intro t
    rw [A329813.sol_zero]
    exact one_ne_zero
  have b1 : A329813.sol 1 1 1 ≠ 0 := by
    rw [A329813.sol_one]
    exact one_ne_zero
  obtain ⟨c, hc⟩ := H (A329813.sol 1 1) (b0 1) b1 (A329813.sol_rec 1 1)
  have hc14 := A329813.prod_one (A329813.sol 1 1) c (b0 1) b1 (A329813.sol_rec 1 1) hc
  have hc1 : c 1 ≠ 0 := left_ne_zero_of_mul_eq_one hc14
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (c 1)⁻¹ := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by
    rw [ht]
    exact inv_ne_zero hc1
  have b1' : A329813.sol 1 t 1 ≠ 0 := by
    rw [A329813.sol_one]
    exact ht0
  obtain ⟨c', hc'⟩ := H (A329813.sol 1 t) (b0 t) b1' (A329813.sol_rec 1 t)
  have hc'14 := A329813.prod_one (A329813.sol 1 t) c' (b0 t) b1' (A329813.sol_rec 1 t) hc'
  have l1 := hc'.1 1 (by norm_num) (by norm_num)
  have l2 : Tendsto (fun n : ℕ => A329813.sol 1 t (6 * n + 1) / ((6 * n + 1 : ℕ) : ℝ)) atTop
      (𝓝 (t * c 1)) := by
    have h := (hc.1 1 (by norm_num) (by norm_num)).const_mul t
    refine h.congr (fun n => ?_)
    rw [A329813.prop t ht0 n, mul_div_assoc]
  have e1 : c' 1 = t * c 1 := tendsto_nhds_unique l1 l2
  have e1' : c' 1 = 1 := by
    rw [e1, ht]
    exact inv_mul_cancel₀ hc1
  have e4 : c' 4 = 1 := by
    rw [e1', one_mul] at hc'14
    exact hc'14
  exact hc'.2 1 4 (by norm_num) (by norm_num) (by norm_num) (by rw [e1', e4])
