import FormalConjectures.Wikipedia.GaussCircleProblem
import Mathlib
/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ChironTheCentaur/rh-lab-divisor-problem/blob/80d65168002a5c5903c5808f619f23f21a21f632/HardyOmegaFC/CircleHardy.lean  (theorem GaussCircleProblem.error_not_isLittleO)
Original author: Sky (GitHub: ChironTheCentaur)   Licence: Apache-2.0 (LICENSE)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: flattened HardyOmegaFC/{CircleLattice,CircleReduction,DiscFourier,CirclePoisson,DiscAsymp,CircleVoronoi,CircleHardy}.lean
into one file inside namespace OMAPort_Circle, dropping the five declarations the final theorem does not use; dropped the copied FC definitions (Circle.lean) in favour of
formal-conjectures' own N and E (identical text); wrapped each source file in its own section; removed one module-level set_option line; for the
pinned Mathlib, replaced seven `convert _ using 1` steps on HasDerivAt by HasDerivAt.congr_deriv (one of them
also uses hasDerivAt_id' in place of hasDerivAt_id) and added Circle.norm_coe to one simp call.
-/
/-
NOTICE (from the original package):
HardyDivisorOmega (standalone package)
Copyright 2026 Sky (GitHub: ChironTheCentaur)
The original work in this package (HardyOmegaFC/, LeanClassics/, ...) is licensed under the Apache License,
Version 2.0. The definitions N and E of the Gauss circle problem and the statement of error_not_isLittleO are
from google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/GaussCircleProblem.lean),
Copyright 2025 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0.
Licensed under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); distributed on an
AS IS basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND. This file is a modified version of the original.
-/

namespace OMAPort_Circle

-- ===== from HardyOmegaFC.CircleLattice =====
section

open Real Finset

namespace HardyC1

/-- `‖k‖²` for a lattice point, as a natural number. -/
def nn (k : ℤ × ℤ) : ℕ := k.1.natAbs ^ 2 + k.2.natAbs ^ 2

theorem nn_cast (k : ℤ × ℤ) : (nn k : ℝ) = (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2 := by
  unfold nn; push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, sq_abs, sq_abs]

theorem nn_eq_zero {k : ℤ × ℤ} : nn k = 0 ↔ k = 0 := by
  simp [nn, Prod.ext_iff]

/-- The square box `[-s, s]²`. -/
def box (s : ℕ) : Finset (ℤ × ℤ) := Icc (-(s:ℤ)) s ×ˢ Icc (-(s:ℤ)) s

theorem mem_box {s : ℕ} {k : ℤ × ℤ} : k ∈ box s ↔ k.1.natAbs ≤ s ∧ k.2.natAbs ≤ s := by
  simp only [box, mem_product, mem_Icc]; omega

theorem card_box (s : ℕ) : (box s).card = (2 * s + 1) ^ 2 := by
  rw [box, card_product, Int.card_Icc]
  have : ((s:ℤ) + 1 - -(s:ℤ)).toNat = 2 * s + 1 := by omega
  rw [this]; ring

theorem mem_box_sqrt {X : ℕ} {k : ℤ × ℤ} (h : nn k ≤ X) : k ∈ box (Nat.sqrt X) := by
  rw [mem_box]; unfold nn at h
  constructor <;> rw [Nat.le_sqrt'] <;> omega

/-- At most `9X` lattice points with `‖k‖² < X`, `X ≥ 1`. -/
theorem card_filter_lt_le (F : Finset (ℤ × ℤ)) {X : ℕ} (hX : 1 ≤ X) :
    ((F.filter fun k => nn k < X).card : ℝ) ≤ 9 * X := by
  have hsub : F.filter (fun k => nn k < X) ⊆ box (Nat.sqrt X) := by
    intro k hk; rw [mem_filter] at hk; exact mem_box_sqrt hk.2.le
  have h1 := card_le_card hsub
  rw [card_box] at h1
  have hs1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt'.mpr (by simpa using hX)
  have hs2 := Nat.sqrt_le' X
  have : (2 * Nat.sqrt X + 1) ^ 2 ≤ 9 * X := by nlinarith
  exact_mod_cast h1.trans this

/-- The weight `‖k‖^{-3/2} e^{-π δ² ‖k‖²}` (zero at `k = 0`). -/
noncomputable def v (δ : ℝ) (k : ℤ × ℤ) : ℝ :=
  if k = 0 then 0 else (nn k : ℝ) ^ (-(3/4 : ℝ)) * exp (-π * δ ^ 2 * nn k)

theorem v_nonneg (δ : ℝ) (k : ℤ × ℤ) : 0 ≤ v δ k := by
  unfold v; split_ifs
  · exact le_rfl
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le

/-- weight is antitone in `‖k‖²`. -/
theorem v_le_of_le {δ : ℝ} {k : ℤ × ℤ} (hk : k ≠ 0) {y : ℝ} (hy : 0 < y) (hyk : y ≤ nn k) :
    v δ k ≤ y ^ (-(3/4 : ℝ)) * exp (-π * δ ^ 2 * y) := by
  unfold v; simp only [hk, ite_false]
  have hm := mul_le_mul_of_nonneg_left hyk (by positivity : 0 ≤ π * δ ^ 2)
  apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hy hyk (by norm_num))
    (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_pos _).le (Real.rpow_nonneg hy.le _)

theorem geom_aux (j : ℕ) : (4:ℝ) ^ j * exp (-(4 * π) * 2 ^ j) ≤ exp (-(4 * π)) := by
  have hj : (j : ℝ) ≤ 2 ^ j - 1 := by
    have : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have : ((j + 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have h4 : (4:ℝ) ≤ exp (4 * π) := by
    have := Real.add_one_le_exp (4 * π); nlinarith [Real.pi_gt_three]
  have hpow : (4:ℝ) ^ j ≤ exp (4 * π) ^ j := pow_le_pow_left₀ (by norm_num) h4 j
  rw [← Real.exp_nat_mul] at hpow
  have : exp ((j:ℝ) * (4 * π)) ≤ exp ((2 ^ j - 1) * (4 * π)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hj (by positivity))
  calc (4:ℝ) ^ j * exp (-(4 * π) * 2 ^ j) ≤ exp ((2 ^ j - 1) * (4 * π)) * exp (-(4 * π) * 2 ^ j) :=
        mul_le_mul_of_nonneg_right (hpow.trans this) (Real.exp_pos _).le
    _ = exp (-(4 * π)) := by rw [← Real.exp_add]; congr 1; ring

/-- One dyadic shell `M 2^j ≤ ‖k‖² < M 2^{j+1}` contributes at most `18 M^{1/4} e^{-4π} 2^{-j}`. -/
theorem shell_le {δ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hδM : δ ^ 2 * M = 4) (F : Finset (ℤ × ℤ)) (j : ℕ)
    (hF : ∀ k ∈ F, k ≠ 0 ∧ M * 2 ^ j ≤ nn k ∧ nn k < M * 2 ^ (j + 1)) :
    ∑ k ∈ F, v δ k ≤ 18 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) * (1/2) ^ j := by
  set y : ℝ := (M : ℝ) * 2 ^ j with hy
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hy0 : 0 < y := by positivity
  have hcard : (F.card : ℝ) ≤ 9 * (M * 2 ^ (j + 1) : ℕ) := by
    have hF' : F.filter (fun k => nn k < M * 2 ^ (j + 1)) = F := filter_true_of_mem (fun k hk => (hF k hk).2.2)
    have := card_filter_lt_le F (X := M * 2 ^ (j + 1)) (Nat.one_le_iff_ne_zero.mpr (by positivity))
    rwa [hF'] at this
  have hterm : ∀ k ∈ F, v δ k ≤ y ^ (-(3/4 : ℝ)) * exp (-(4 * π) * 2 ^ j) := by
    intro k hk
    obtain ⟨hk0, hlo, -⟩ := hF k hk
    have hlo' : y ≤ nn k := by rw [hy]; exact_mod_cast hlo
    refine (v_le_of_le hk0 hy0 hlo').trans (le_of_eq ?_)
    congr 1; congr 1; rw [hy, ← hδM]; ring
  have hsum := sum_le_card_nsmul F (v δ) _ hterm
  rw [nsmul_eq_mul] at hsum
  have hpos : 0 ≤ y ^ (-(3/4 : ℝ)) * exp (-(4 * π) * 2 ^ j) := by positivity
  have h1 : ∑ k ∈ F, v δ k ≤ 9 * (M * 2 ^ (j + 1) : ℕ) * (y ^ (-(3/4 : ℝ)) * exp (-(4 * π) * 2 ^ j)) :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard hpos)
  -- 9 · M 2^{j+1} · y^{-3/4} = 18 y^{1/4}, and y^{1/4} = M^{1/4} (2^j)^{1/4} ≤ M^{1/4} 2^j
  have hy14 : (M * 2 ^ (j + 1) : ℕ) * y ^ (-(3/4 : ℝ)) = 2 * y ^ (1/4 : ℝ) := by
    have : ((M * 2 ^ (j + 1) : ℕ) : ℝ) = 2 * y := by rw [hy]; push_cast; ring
    rw [this, mul_assoc]
    congr 1
    rw [show y * y ^ (-(3/4:ℝ)) = y ^ (1 + -(3/4:ℝ)) by rw [Real.rpow_add hy0, Real.rpow_one]]
    norm_num
  have h2j : ((2:ℝ) ^ j) ^ (1/4 : ℝ) ≤ 2 ^ j := by
    conv_rhs => rw [← Real.rpow_one ((2:ℝ) ^ j)]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by norm_num)
  have hysplit : y ^ (1/4 : ℝ) = (M:ℝ) ^ (1/4 : ℝ) * ((2:ℝ) ^ j) ^ (1/4 : ℝ) := by
    rw [hy, Real.mul_rpow hM0.le (by positivity)]
  have hg := geom_aux j
  have h4 : (4:ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  have hhalf : (1/2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
  have hM14 : 0 ≤ (M:ℝ) ^ (1/4 : ℝ) := Real.rpow_nonneg hM0.le _
  have he : 0 ≤ exp (-(4 * π) * 2 ^ j) := (Real.exp_pos _).le
  calc ∑ k ∈ F, v δ k ≤ 9 * (M * 2 ^ (j + 1) : ℕ) * (y ^ (-(3/4 : ℝ)) * exp (-(4 * π) * 2 ^ j)) := h1
    _ = 18 * y ^ (1/4 : ℝ) * exp (-(4 * π) * 2 ^ j) := by
        rw [← mul_assoc, mul_assoc 9, hy14]; ring
    _ ≤ 18 * ((M:ℝ) ^ (1/4 : ℝ) * 2 ^ j) * exp (-(4 * π) * 2 ^ j) := by
        rw [hysplit]; gcongr
    _ = 18 * (M:ℝ) ^ (1/4 : ℝ) * (1/2) ^ j * ((4:ℝ) ^ j * exp (-(4 * π) * 2 ^ j)) := by
        rw [h4]
        linear_combination (-(18 * (M:ℝ) ^ (1/4:ℝ) * exp (-(4 * π) * 2 ^ j) * 2 ^ j)) * hhalf
    _ ≤ 18 * (M:ℝ) ^ (1/4 : ℝ) * (1/2) ^ j * exp (-(4 * π)) := by gcongr
    _ = 18 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) * (1/2) ^ j := by ring

/-- **Tail.** With `δ² M = 4`, the lattice points with `‖k‖² > M` carry total weight `≤ 36 M^{1/4} e^{-4π}`. -/
theorem tail_le {δ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hδM : δ ^ 2 * M = 4) (F : Finset (ℤ × ℤ)) :
    ∑ k ∈ F.filter (fun k => M < nn k), v δ k ≤ 36 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) := by
  set G := F.filter (fun k => M < nn k)
  set g : ℤ × ℤ → ℕ := fun k => Nat.log 2 (nn k / M)
  rw [← sum_fiberwise_of_maps_to (g := g) (t := G.image g) (fun k hk => mem_image_of_mem g hk)]
  have hshell : ∀ j ∈ G.image g, ∑ k ∈ G.filter (fun k => g k = j), v δ k ≤
      18 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) * (1/2) ^ j := by
    intro j _
    apply shell_le hM hδM
    intro k hk
    simp only [G, mem_filter] at hk
    obtain ⟨⟨-, hMk⟩, hj⟩ := hk
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hMk; simp [nn] at hMk
    have hq : 1 ≤ nn k / M := (Nat.one_le_div_iff (by omega)).mpr hMk.le
    have hlo : 2 ^ j ≤ nn k / M := by
      rw [← hj]; exact Nat.pow_log_le_self 2 (by omega)
    have hhi : nn k / M < 2 ^ (j + 1) := by
      rw [← hj]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    refine ⟨hk0, ?_, ?_⟩
    · calc M * 2 ^ j ≤ M * (nn k / M) := Nat.mul_le_mul_left _ hlo
        _ ≤ nn k := Nat.mul_div_le (nn k) M
    · have h1 := Nat.lt_div_mul_add (a := nn k) (b := M) (by omega)
      have h2 : nn k / M + 1 ≤ 2 ^ (j + 1) := hhi
      nlinarith
  calc ∑ j ∈ G.image g, ∑ k ∈ G.filter (fun k => g k = j), v δ k
      ≤ ∑ j ∈ G.image g, 18 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) * (1/2) ^ j := sum_le_sum hshell
    _ = 18 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) * ∑ j ∈ G.image g, (1/2 : ℝ) ^ j := by
        rw [mul_sum]
    _ ≤ 18 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) * 2 := by
        gcongr
        set n := (G.image g).sup id + 1
        have hsub : G.image g ⊆ range n := by
          intro j hj; rw [mem_range]
          exact Nat.lt_succ_of_le (le_sup (f := id) hj)
        exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
          (sum_geometric_two_le n)
    _ = 36 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) := by ring

/-- `‖k‖` for a lattice point. -/
noncomputable def lnorm (k : ℤ × ℤ) : ℝ := √((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2)

/-- The `k`-th term of the smoothed Voronoi series (zero at `k = 0`). -/
noncomputable def w (δ R : ℝ) (k : ℤ × ℤ) : ℝ :=
  if k = 0 then 0 else
    lnorm k ^ (-(3/2 : ℝ)) * exp (-π * δ ^ 2 * lnorm k ^ 2) * cos (2 * π * R * lnorm k - 3 * π / 4)

theorem w_eq (δ R : ℝ) (k : ℤ × ℤ) : w δ R k = v δ k * cos (2 * π * R * √(nn k) - 3 * π / 4) := by
  unfold w v
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    have hl : lnorm k = √(nn k) := by rw [lnorm, nn_cast]
    have h0 : (0:ℝ) ≤ nn k := Nat.cast_nonneg _
    rw [hl, Real.sq_sqrt h0, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
    norm_num

theorem abs_w_le (δ R : ℝ) (k : ℤ × ℤ) : |w δ R k| ≤ v δ k := by
  rw [w_eq, abs_mul, abs_of_nonneg (v_nonneg δ k)]
  exact mul_le_of_le_one_right (v_nonneg δ k) (abs_cos_le_one _)

/-- the aligned set: `0 < ‖k‖² ≤ M`. -/
def Aset (M : ℕ) : Finset (ℤ × ℤ) := (box (Nat.sqrt M)).filter (fun k => k ≠ 0 ∧ nn k ≤ M)

theorem not_mem_Aset {M : ℕ} {k : ℤ × ℤ} (h : k ∉ Aset M) : k = 0 ∨ M < nn k := by
  by_contra h'
  push Not at h'
  exact h (mem_filter.mpr ⟨mem_box_sqrt h'.2, h'.1, h'.2⟩)

theorem sum_v_le {δ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hδM : δ ^ 2 * M = 4) (F : Finset (ℤ × ℤ)) :
    ∑ k ∈ F, v δ k ≤ ∑ k ∈ box (Nat.sqrt M), v δ k + 36 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) := by
  rw [← sum_filter_add_sum_filter_not F (fun k => M < nn k)]
  have h1 := tail_le hM hδM F
  have h2 : ∑ k ∈ F.filter (fun k => ¬ M < nn k), v δ k ≤ ∑ k ∈ box (Nat.sqrt M), v δ k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk; rw [mem_filter] at hk; exact mem_box_sqrt (not_lt.mp hk.2)
    · intro k _ _; exact v_nonneg δ k
  linarith

theorem summable_v {δ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hδM : δ ^ 2 * M = 4) : Summable (v δ) :=
  summable_of_sum_le (v_nonneg δ) (sum_v_le hM hδM)

theorem summable_w {δ : ℝ} {M : ℕ} (hM : 1 ≤ M) (hδM : δ ^ 2 * M = 4) (R : ℝ) : Summable (w δ R) :=
  Summable.of_norm_bounded (summable_v hM hδM) (fun k => by rw [Real.norm_eq_abs]; exact abs_w_le δ R k)

/-- **Lower bound** for the aligned weight: `∑_{0<‖k‖²≤M} v ≥ e^{-π} (M/4)^{1/4}`. -/
theorem lower_sum {δ : ℝ} {M : ℕ} (hM : 8 ≤ M) (hδM : δ ^ 2 * M = 4) :
    exp (-π) * ((M:ℝ) / 4) ^ (1/4 : ℝ) ≤ ∑ k ∈ Aset M, v δ k := by
  set s := Nat.sqrt (M / 8) with hs
  have hM0 : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hs1 : 1 ≤ s := Nat.le_sqrt'.mpr (by omega)
  have hs2 : s ^ 2 ≤ M / 8 := Nat.sqrt_le' _
  have hs3 : M / 8 < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
  set Sm := (box s).erase 0
  have hsub : Sm ⊆ Aset M := by
    intro k hk
    rw [mem_erase] at hk
    have hb := mem_box.mp hk.2
    have hnn : nn k ≤ M := by
      unfold nn
      have : k.1.natAbs ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hb.1 2
      have : k.2.natAbs ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hb.2 2
      omega
    exact mem_filter.mpr ⟨mem_box_sqrt hnn, hk.1, hnn⟩
  have hterm : ∀ k ∈ Sm, ((M:ℝ) / 4) ^ (-(3/4 : ℝ)) * exp (-π) ≤ v δ k := by
    intro k hk
    rw [mem_erase] at hk
    have hb := mem_box.mp hk.2
    have hnn4 : 4 * nn k ≤ M := by
      unfold nn
      have : k.1.natAbs ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hb.1 2
      have : k.2.natAbs ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hb.2 2
      omega
    have hnn1 : 1 ≤ nn k := Nat.one_le_iff_ne_zero.mpr (fun h => hk.1 (nn_eq_zero.mp h))
    have hr4 : (nn k : ℝ) ≤ M / 4 := by
      have : ((4 * nn k : ℕ) : ℝ) ≤ M := by exact_mod_cast hnn4
      push_cast at this; linarith
    have hr1 : (1:ℝ) ≤ nn k := by exact_mod_cast hnn1
    unfold v; simp only [hk.1, ite_false]
    apply mul_le_mul (Real.rpow_le_rpow_of_nonpos (by linarith) hr4 (by norm_num))
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
    have : δ ^ 2 * nn k ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hr4 (sq_nonneg δ)
      linarith
    nlinarith [Real.pi_pos]
  have hcard : (M:ℝ) / 4 ≤ Sm.card := by
    have hc : Sm.card = (2 * s + 1) ^ 2 - 1 := by
      rw [card_erase_of_mem (mem_box.mpr ⟨by simp, by simp⟩), card_box]
    have hM8 : M < 8 * (M / 8 + 1) := by omega
    have : M ≤ 4 * ((2 * s + 1) ^ 2 - 1) := by
      have h1 : 2 * (s + 1) ^ 2 ≤ (2 * s + 1) ^ 2 - 1 := by
        have : 2 * (s + 1) ^ 2 + 1 ≤ (2 * s + 1) ^ 2 := by nlinarith
        omega
      nlinarith
    rw [hc]
    have : (M:ℝ) ≤ ((4 * ((2 * s + 1) ^ 2 - 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_mul] at this ⊢
    rw [Nat.cast_sub (by nlinarith)] at this ⊢
    push_cast at this ⊢
    linarith
  have hsum := card_nsmul_le_sum Sm (v δ) _ hterm
  rw [nsmul_eq_mul] at hsum
  have hpos : 0 ≤ ((M:ℝ) / 4) ^ (-(3/4 : ℝ)) * exp (-π) := by positivity
  have hx : ((M:ℝ) / 4) * ((M:ℝ) / 4) ^ (-(3/4 : ℝ)) = ((M:ℝ) / 4) ^ (1/4 : ℝ) := by
    rw [show ((M:ℝ) / 4) * ((M:ℝ) / 4) ^ (-(3/4:ℝ)) = ((M:ℝ) / 4) ^ (1 + -(3/4:ℝ)) by
      rw [Real.rpow_add (by positivity), Real.rpow_one]]
    norm_num
  calc exp (-π) * ((M:ℝ) / 4) ^ (1/4 : ℝ) = ((M:ℝ) / 4) * (((M:ℝ) / 4) ^ (-(3/4 : ℝ)) * exp (-π)) := by
        rw [← mul_assoc, hx, mul_comm]
    _ ≤ Sm.card * (((M:ℝ) / 4) ^ (-(3/4 : ℝ)) * exp (-π)) := mul_le_mul_of_nonneg_right hcard hpos
    _ ≤ ∑ k ∈ Sm, v δ k := hsum
    _ ≤ ∑ k ∈ Aset M, v δ k :=
        sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => v_nonneg δ k)

/-- `cos(2πx - 3π/4) ≤ -1/2` when `x` is within `1/64` of an integer. -/
theorem cos_aligned {x : ℝ} {m : ℤ} (h : |x - m| ≤ 1 / 64) : cos (2 * π * x - 3 * π / 4) ≤ -1 / 2 := by
  have hper : cos (2 * π * x - 3 * π / 4) = cos (2 * π * (x - m) - 3 * π / 4) := by
    rw [show 2 * π * x - 3 * π / 4 = (2 * π * (x - m) - 3 * π / 4) + (m : ℤ) * (2 * π) by ring]
    exact Real.cos_add_int_mul_two_pi _ m
  have h34 : cos (3 * π / 4) = -(√2 / 2) := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  have hlip := Real.abs_cos_sub_cos_le (2 * π * (x - m) - 3 * π / 4) (-(3 * π / 4))
  rw [Real.cos_neg, h34] at hlip
  have hd : |2 * π * (x - m) - 3 * π / 4 - -(3 * π / 4)| ≤ 2 * π / 64 := by
    rw [show 2 * π * (x - m) - 3 * π / 4 - -(3 * π / 4) = 2 * π * (x - m) by ring, abs_mul,
      abs_of_pos (by positivity)]
    calc 2 * π * |x - m| ≤ 2 * π * (1 / 64) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * π / 64 := by ring
  have hs2 : (1.4 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpi := Real.pi_lt_four
  rw [hper]
  have := (abs_le.mp (hlip.trans hd)).2
  linarith

/-- **Main sum.** If `q R₂ √(i+1)` is within `1/64` of an integer for every `i < M`, then at `R = q R₂` the smoothed
Voronoi series is at most `-(1/120) (M/4)^{1/4}`. -/
theorem main_sum_le {M : ℕ} (hM : 8 ≤ M) {δ : ℝ} (hδM : δ ^ 2 * M = 4) {R₂ : ℝ} {q : ℕ}
    (hq : ∀ i < M, ∃ m : ℤ, |(q : ℝ) * (R₂ * √((i : ℝ) + 1)) - m| ≤ 1 / 64) :
    ∑' k, w δ (q * R₂) k ≤ -(1 / 120) * ((M : ℝ) / 4) ^ (1/4 : ℝ) := by
  have hM1 : 1 ≤ M := by omega
  set A := Aset M
  set R := (q : ℝ) * R₂
  -- split the series into the aligned part and the rest
  have hsw := summable_w hM1 hδM R
  set g : ℤ × ℤ → ℝ := fun k => if k ∈ A then 0 else w δ R k
  set f : ℤ × ℤ → ℝ := fun k => if k ∈ A then w δ R k else 0
  have hfg : w δ R = f + g := by
    funext k; simp only [f, g, Pi.add_apply]; split_ifs <;> simp
  have hsf : Summable f := summable_of_ne_finset_zero (s := A) (fun k hk => by simp [f, hk])
  have hsg : Summable g := by
    have : g = w δ R - f := by rw [hfg]; abel
    rw [this]; exact hsw.sub hsf
  have htf : ∑' k, f k = ∑ k ∈ A, w δ R k := by
    rw [tsum_eq_sum (s := A) (fun k hk => by simp [f, hk])]
    exact sum_congr rfl (fun k hk => by simp [f, hk])
  -- aligned terms are ≤ -v/2
  have halign : ∀ k ∈ A, w δ R k ≤ -(1/2) * v δ k := by
    intro k hk
    have hk' := (mem_filter.mp hk).2
    have hn1 : 1 ≤ nn k := Nat.one_le_iff_ne_zero.mpr (fun h => hk'.1 (nn_eq_zero.mp h))
    obtain ⟨m, hm⟩ := hq (nn k - 1) (by omega)
    have hcast : ((nn k - 1 : ℕ) : ℝ) + 1 = nn k := by
      rw [Nat.cast_sub hn1]; push_cast; ring
    rw [hcast] at hm
    have hc := cos_aligned (x := R * √(nn k)) (m := m) (by
      simpa [R, mul_assoc] using hm)
    rw [w_eq, show 2 * π * R * √(nn k) = 2 * π * (R * √(nn k)) by ring]
    have := mul_le_mul_of_nonneg_left hc (v_nonneg δ k)
    linarith
  have hA : ∑ k ∈ A, w δ R k ≤ -(1/2) * ∑ k ∈ A, v δ k := by
    rw [mul_sum]; exact sum_le_sum halign
  -- the rest is bounded by the tail
  have htg : ∑' k, g k ≤ 36 * (M : ℝ) ^ (1/4 : ℝ) * exp (-(4 * π)) := by
    refine hsg.tsum_le_of_sum_le (fun F => ?_)
    refine le_trans ?_ (tail_le hM1 hδM F)
    rw [sum_filter]
    refine sum_le_sum (fun k _ => ?_)
    simp only [g]
    by_cases hkA : k ∈ A
    · simp only [hkA, ite_true]; split_ifs
      · exact v_nonneg δ k
      · exact le_rfl
    · simp only [hkA, ite_false]
      rcases not_mem_Aset hkA with h0 | hlt
      · simp [h0, w]
        split_ifs <;> simp [v_nonneg]
      · simp only [hlt, ite_true]
        exact (le_abs_self _).trans (abs_w_le δ R k)
  have hlow := lower_sum (δ := δ) hM hδM
  -- numerics
  have hM0 : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM14 : (M : ℝ) ^ (1/4 : ℝ) ≤ 2 * ((M : ℝ) / 4) ^ (1/4 : ℝ) := by
    rw [Real.div_rpow hM0.le (by norm_num)]
    have h4 : (4:ℝ) ^ (1/4 : ℝ) ≤ 2 := by
      have h2 : (4:ℝ) ^ (1/2 : ℝ) = 2 := by
        rw [← Real.sqrt_eq_rpow, show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← h2]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h40 : 0 < (4:ℝ) ^ (1/4 : ℝ) := by positivity
    rw [mul_div_assoc', le_div_iff₀ h40]
    have := Real.rpow_nonneg hM0.le (1/4 : ℝ)
    nlinarith
  have he1 : 1 / 55 ≤ exp (-π) := by
    have h1 : exp π ≤ 55 := by
      have := Real.exp_one_lt_d9
      have h4 : exp π ≤ exp 4 := Real.exp_le_exp.mpr Real.pi_lt_four.le
      have h5 : exp (4:ℝ) = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have h6 : exp 1 ^ 4 ≤ (2.7182818286:ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 4
      norm_num at h6
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos π) h1
  have he4 : exp (-(4 * π)) ≤ 1 / 150000 := by
    have h1 : 150000 ≤ exp (4 * π) := by
      have := Real.exp_one_gt_d9
      have h4 : exp 12 ≤ exp (4 * π) := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
      have h5 : exp (12:ℝ) = exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
      have h6 : (2.7182818283:ℝ) ^ 12 ≤ exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) this.le 12
      norm_num at h6
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h1
  have hX : 0 ≤ ((M : ℝ) / 4) ^ (1/4 : ℝ) := by positivity
  rw [hfg]; simp only [Pi.add_apply]; rw [hsf.tsum_add hsg, htf]
  nlinarith [Real.exp_pos (-(4 * π))]

end HardyC1

end

-- ===== from HardyOmegaFC.CircleReduction =====
section

/-!
# Gauss circle problem, rung C1: the Diophantine reduction

`error_not_isLittleO_of_smoothedVoronoi : SmoothedVoronoiC → ¬E =o[atTop] (fun r => √r * √√r.log)`,
where `E` is formal-conjectures' circle error (copied in `HardyOmegaFC/Circle.lean`) and `SmoothedVoronoiC` is the
named analytic input: the Gaussian average of `E` in the radius,
`∫ φ_δ(u) E(R+u) du` with `φ_δ(u) = δ⁻¹ e^{-π u²/δ²}`, equals
`(√R/π) Σ_{k ∈ ℤ², k ≠ 0} ‖k‖^{-3/2} e^{-πδ²‖k‖²} cos(2πR‖k‖ - 3π/4)` up to `O(√R)`,
for `R ≥ R₀` and `(log R)⁻¹ ≤ δ ≤ 1`. Rungs C2-C5 (PLAN_C.md) prove it (2-D Poisson + disc Fourier transform + the
`J₁` asymptotic); this file shows it is all that is missing.

Argument: if `E = o(√r (log r)^{1/4})`, the smoothed average is `≤ ε √(2R) (log 2R)^{1/4} + 425` (`smooth_upper`).
Take `δ = 2/√M`, `R₂ = e^M` and Dirichlet's simultaneous approximation (`dirichlet_simul`, `Q = 64`) to find
`R = q R₂`, `1 ≤ q ≤ 64^M`, with `R √n` within `1/64` of an integer for all `n ≤ M`. Then every term with
`‖k‖² ≤ M` has `cos ≤ -1/2`, the rest is a tail `≤ 36 M^{1/4} e^{-4π}`, so the series is `≤ -(1/120)(M/4)^{1/4}`
(`main_sum_le`), while `log 2R ≤ 6M`. Comparing, `(M/4)^{1/4} ≤ 240π (C + 425)`: false for large `M`.
-/

open GaussCircleProblem Real Filter MeasureTheory Asymptotics
open scoped EuclideanGeometry

namespace HardyC1

theorem norm_vec_sq (m n : ℤ) : ‖!₂[(m:ℝ), (n:ℝ)]‖ ^ 2 = (m:ℝ) ^ 2 + (n:ℝ) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

theorem N_le (r : ℝ) : (N r : ℝ) ≤ (2 * |r| + 3) ^ 2 := by
  set K : ℤ := ⌈|r|⌉
  have hsub : { (m, n) : ℤ × ℤ | !₂[(m:ℝ), (n:ℝ)] ∈ Metric.closedBall (0 : ℝ²) r } ⊆
      ((Finset.Icc (-K) K) ×ˢ (Finset.Icc (-K) K) : Finset (ℤ × ℤ)) := by
    rintro ⟨m, n⟩ h
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] at h
    have h0 : 0 ≤ r := le_trans (norm_nonneg _) h
    have hsq := norm_vec_sq m n
    have h2 : (m:ℝ)^2 + (n:ℝ)^2 ≤ r^2 := by
      rw [← hsq]; exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have hm : |(m:ℝ)| ≤ |r| := by
      apply sq_le_sq.mp; nlinarith [sq_nonneg (n:ℝ)]
    have hn : |(n:ℝ)| ≤ |r| := by
      apply sq_le_sq.mp; nlinarith [sq_nonneg (m:ℝ)]
    have hK : |r| ≤ (K:ℝ) := Int.le_ceil _
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    rw [abs_le] at hm hn
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have : (-(K:ℝ)) ≤ m := by linarith
      exact_mod_cast this
    · have : (m:ℝ) ≤ K := by linarith
      exact_mod_cast this
    · have : (-(K:ℝ)) ≤ n := by linarith
      exact_mod_cast this
    · have : (n:ℝ) ≤ K := by linarith
      exact_mod_cast this
  have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hc
  have hK0 : 0 ≤ K := Int.ceil_nonneg (abs_nonneg r)
  have hcard : ((Finset.Icc (-K) K) ×ˢ (Finset.Icc (-K) K) : Finset (ℤ × ℤ)).card = (2 * K.toNat + 1) ^ 2 := by
    rw [Finset.card_product, Int.card_Icc]
    have : (K + 1 - -K).toNat = 2 * K.toNat + 1 := by omega
    rw [this]; ring
  rw [hcard] at hc
  have hKr : (K:ℝ) ≤ |r| + 1 := (Int.ceil_lt_add_one _).le
  have hKn : ((K.toNat : ℕ) : ℝ) = (K:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hK0
  have : (N r : ℝ) ≤ ((2 * K.toNat + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hc
  push_cast at this; rw [hKn] at this
  have hK0' : (0:ℝ) ≤ K := by exact_mod_cast hK0
  nlinarith

theorem abs_E_le (r : ℝ) : |E r| ≤ 15 * (1 + r ^ 2) := by
  have h1 := N_le r
  have h0 : (0:ℝ) ≤ N r := Nat.cast_nonneg _
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have ha := abs_nonneg r
  have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
  rw [E, abs_le]
  constructor <;> nlinarith [sq_nonneg (|r| - 1)]

/-- The Gaussian kernel of width `δ` in the radius, `∫ φ δ = 1`, `\hat φ δ (ξ) = exp(-π δ² ξ²)`. -/
noncomputable def phi (δ u : ℝ) : ℝ := δ⁻¹ * exp (-π * u ^ 2 / δ ^ 2)

theorem gauss_eq (δ u : ℝ) (c : ℝ) : exp (-(π / (c * δ ^ 2)) * u ^ 2) = exp (-π * u ^ 2 / (c * δ ^ 2)) := by
  congr 1; ring

theorem integral_gauss_scaled {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, exp (-(π / (c * δ ^ 2)) * u ^ 2) = √c * δ := by
  rw [integral_gaussian]
  have : π / (π / (c * δ ^ 2)) = c * δ ^ 2 := by field_simp
  rw [this, Real.sqrt_mul hc.le, Real.sqrt_sq hδ.le]

theorem integrable_gauss_scaled {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => exp (-(π / (c * δ ^ 2)) * u ^ 2)) :=
  integrable_exp_neg_mul_sq (by positivity)

theorem phi_eq (δ u : ℝ) : phi δ u = δ⁻¹ * exp (-(π / (1 * δ ^ 2)) * u ^ 2) := by
  rw [phi, gauss_eq]; simp

theorem integral_phi {δ : ℝ} (hδ : 0 < δ) : ∫ u, phi δ u = 1 := by
  simp_rw [phi_eq]
  rw [integral_const_mul, integral_gauss_scaled hδ one_pos]
  simp [hδ.ne']

theorem integrable_phi {δ : ℝ} (hδ : 0 < δ) : Integrable (phi δ) := by
  have := (integrable_gauss_scaled hδ one_pos).const_mul δ⁻¹
  refine this.congr (Eventually.of_forall fun u => ?_)
  simp only [phi_eq]

theorem phi_nonneg {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 ≤ phi δ u := by
  unfold phi; positivity

/-- far-tail weight: `φ δ u · (180 u² + 120 u⁴) ≤ 300 δ⁻¹ exp(-(π/(2δ²)) u²)` for `δ ≤ 1`. -/
theorem phi_poly_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (u : ℝ) :
    phi δ u * (180 * u ^ 2 + 120 * u ^ 4) ≤ 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2) := by
  set x := π * u ^ 2 / (2 * δ ^ 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have hδ20 : 0 < δ ^ 2 := by positivity
  have hu2 : u ^ 2 = 2 * δ ^ 2 * x / π := by rw [hx]; field_simp
  have hpi3 : 3 < π := Real.pi_gt_three
  have e1 : 1 + x + x ^ 2 / 2 ≤ exp x := Real.quadratic_le_exp_of_nonneg hx0
  have hsplit : exp (-π * u ^ 2 / δ ^ 2) = exp (-(π / (2 * δ ^ 2)) * u ^ 2) * exp (-x) := by
    rw [← Real.exp_add]; congr 1; rw [hx]; field_simp; ring
  have hexx : exp x * exp (-x) = 1 := by rw [← Real.exp_add]; simp
  -- 180 u² + 120 u⁴ ≤ 300 exp x
  have hpoly : 180 * u ^ 2 + 120 * u ^ 4 ≤ 300 * exp x := by
    have h4 : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [h4, hu2]
    have hA : 2 * δ ^ 2 * x / π ≤ x := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith
    have hA0 : 0 ≤ 2 * δ ^ 2 * x / π := by positivity
    have hB : (2 * δ ^ 2 * x / π) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hA0 hA 2
    nlinarith
  unfold phi
  rw [hsplit]
  have hg : 0 ≤ exp (-(π / (2 * δ ^ 2)) * u ^ 2) := (Real.exp_pos _).le
  have hδi : 0 ≤ δ⁻¹ := by positivity
  have hmx : 0 ≤ exp (-x) := (Real.exp_pos _).le
  calc δ⁻¹ * (exp (-(π / (2 * δ ^ 2)) * u ^ 2) * exp (-x)) * (180 * u ^ 2 + 120 * u ^ 4)
      ≤ δ⁻¹ * (exp (-(π / (2 * δ ^ 2)) * u ^ 2) * exp (-x)) * (300 * exp x) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2) * (exp x * exp (-x)) := by ring
    _ = 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2) := by rw [hexx, mul_one]

/-- The FC comparison function. -/
noncomputable def fcf (r : ℝ) : ℝ := √r * √√r.log

theorem fcf_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : fcf a ≤ fcf b := by
  unfold fcf
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hl : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  exact mul_le_mul (Real.sqrt_le_sqrt hab) (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hl))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem fcf_nonneg (a : ℝ) : 0 ≤ fcf a := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **Upper bound.** If `E = o(√r (log r)^{1/4})`, the Gaussian average of `E` near `R` is at most
`ε √(2R) (log 2R)^{1/4} + 425`, uniformly in `0 < δ ≤ 1`. -/
theorem smooth_upper (hE : E =o[atTop] fcf) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₁ : ℝ, 1 ≤ R₁ ∧ ∀ R ≥ R₁, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      |∫ u, phi δ u * E (R + u)| ≤ ε * fcf (2 * R) + 425 := by
  obtain ⟨R', hR'⟩ := eventually_atTop.mp (hE.bound hε)
  refine ⟨max (2 * R') 2, le_max_of_le_right (by norm_num), fun R hR δ hδ hδ1 => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_right _ _) hR
  have hRR' : 2 * R' ≤ R := le_trans (le_max_left _ _) hR
  set B := ε * fcf (2 * R)
  have hB0 : 0 ≤ B := mul_nonneg hε.le (fcf_nonneg _)
  -- pointwise bound
  have hpt : ∀ u, phi δ u * |E (R + u)| ≤
      B * phi δ u + 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2) := by
    intro u
    have hp0 := phi_nonneg hδ u
    have hg0 : 0 ≤ 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2) := by positivity
    by_cases hu : |u| ≤ R / 2
    · have hu' := abs_le.mp hu
      have h1 : R' ≤ R + u := by linarith
      have h2 : 1 ≤ R + u := by linarith
      have hb := hR' (R + u) h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (fcf_nonneg _)] at hb
      have hm : fcf (R + u) ≤ fcf (2 * R) := fcf_mono h2 (by linarith)
      have : |E (R + u)| ≤ B := le_trans hb (mul_le_mul_of_nonneg_left hm hε.le)
      nlinarith
    · push Not at hu
      have hE15 := abs_E_le (R + u)
      have hu2 : R ^ 2 < 4 * u ^ 2 := by
        have : R / 2 < |u| := hu
        have h0 : 0 ≤ R / 2 := by linarith
        have := mul_lt_mul'' this this h0 h0
        rw [← sq, ← sq, sq_abs] at this
        nlinarith
      have hEp : |E (R + u)| ≤ 180 * u ^ 2 + 120 * u ^ 4 := by
        have hR1 : (1:ℝ) ≤ R ^ 2 := by nlinarith
        have : 15 * (1 + (R + u) ^ 2) ≤ 180 * u ^ 2 + 120 * u ^ 4 := by
          nlinarith [sq_nonneg (R - u), sq_nonneg (R + u), sq_nonneg u, sq_nonneg (u ^ 2 - 1)]
        linarith
      have := mul_le_mul_of_nonneg_left hEp hp0
      linarith [phi_poly_le hδ hδ1 u, mul_nonneg hB0 hp0]
  have hint_rhs : Integrable (fun u => B * phi δ u + 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2)) :=
    ((integrable_phi hδ).const_mul B).add
      (by simpa [mul_assoc] using (integrable_gauss_scaled hδ two_pos).const_mul (300 * δ⁻¹))
  have hint_val : ∫ u, (B * phi δ u + 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2)) =
      B + 300 * √2 := by
    rw [integral_add ((integrable_phi hδ).const_mul B)
      (by simpa [mul_assoc] using (integrable_gauss_scaled hδ two_pos).const_mul (300 * δ⁻¹)),
      integral_const_mul, integral_phi hδ, integral_const_mul, integral_gauss_scaled hδ two_pos]
    field_simp
  calc |∫ u, phi δ u * E (R + u)| ≤ ∫ u, |phi δ u * E (R + u)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => phi δ u * E (R + u))
    _ ≤ ∫ u, (B * phi δ u + 300 * δ⁻¹ * exp (-(π / (2 * δ ^ 2)) * u ^ 2)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) hint_rhs
          (Eventually.of_forall fun u => ?_)
        simp only
        rw [abs_mul, abs_of_nonneg (phi_nonneg hδ u)]
        exact hpt u
    _ = B + 300 * √2 := hint_val
    _ ≤ B + 425 := by
        have : √2 < 1.415 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        linarith

/-- **Dirichlet's simultaneous approximation** (pigeonhole): for `Q ≥ 1` and any reals `α 0, …, α (M-1)` there is
`1 ≤ q ≤ Q^M` with every `q α i` within `1/Q` of an integer. -/
theorem dirichlet_simul (M Q : ℕ) (hQ : 0 < Q) (α : ℕ → ℝ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ M ∧ ∀ i < M, ∃ m : ℤ, |(q : ℝ) * α i - m| ≤ 1 / Q := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hlt : ∀ (q : ℕ) (i : ℕ), ⌊(Q:ℝ) * Int.fract ((q:ℝ) * α i)⌋₊ < Q := by
    intro q i
    apply (Nat.floor_lt (by have := Int.fract_nonneg ((q:ℝ) * α i); positivity)).mpr
    have := Int.fract_lt_one ((q:ℝ) * α i)
    nlinarith
  let f : ℕ → (Fin M → Fin Q) := fun q i => ⟨⌊(Q:ℝ) * Int.fract ((q:ℝ) * α i)⌋₊, hlt q i⟩
  have hc : (Finset.univ : Finset (Fin M → Fin Q)).card < (Finset.range (Q ^ M + 1)).card := by
    simp
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc (f := f) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.mem_range] at hx hy
  -- key: equal boxes give close fractional parts
  have key : ∀ a b : ℕ, f a = f b → ∀ i < M,
      |Int.fract ((a:ℝ) * α i) - Int.fract ((b:ℝ) * α i)| < 1 / Q := by
    intro a b hab i hi
    have h := congrArg (fun g => (g ⟨i, hi⟩ : ℕ)) hab
    simp only [f] at h
    set A := (Q:ℝ) * Int.fract ((a:ℝ) * α i)
    set B := (Q:ℝ) * Int.fract ((b:ℝ) * α i)
    have hA0 : 0 ≤ A := mul_nonneg hQr.le (Int.fract_nonneg _)
    have hB0 : 0 ≤ B := mul_nonneg hQr.le (Int.fract_nonneg _)
    have h1 := Nat.floor_le hA0
    have h2 := Nat.lt_floor_add_one A
    have h3 := Nat.floor_le hB0
    have h4 := Nat.lt_floor_add_one B
    rw [h] at h1 h2
    have hAB : |A - B| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [lt_div_iff₀ hQr]
    have : |A - B| = |Int.fract ((a:ℝ) * α i) - Int.fract ((b:ℝ) * α i)| * Q := by
      simp only [A, B]; rw [← mul_sub, abs_mul, abs_of_pos hQr, mul_comm]
    linarith
  have main : ∀ a b : ℕ, a < b → b ≤ Q ^ M → f a = f b →
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ M ∧ ∀ i < M, ∃ m : ℤ, |(q : ℝ) * α i - m| ≤ 1 / Q := by
    intro a b hab hb hf
    refine ⟨b - a, by omega, by omega, fun i hi => ?_⟩
    refine ⟨⌊(b:ℝ) * α i⌋ - ⌊(a:ℝ) * α i⌋, ?_⟩
    have hk := key b a hf.symm i hi
    have hcast : ((b - a : ℕ) : ℝ) = (b:ℝ) - a := by rw [Nat.cast_sub hab.le]
    rw [hcast]
    have e1 := Int.floor_add_fract ((b:ℝ) * α i)
    have e2 := Int.floor_add_fract ((a:ℝ) * α i)
    have : ((b:ℝ) - a) * α i - ((⌊(b:ℝ) * α i⌋ - ⌊(a:ℝ) * α i⌋ : ℤ) : ℝ) =
        Int.fract ((b:ℝ) * α i) - Int.fract ((a:ℝ) * α i) := by
      push_cast; linarith
    rw [this]; exact hk.le
  rcases lt_or_gt_of_ne hxy with h | h
  · exact main x y h (by omega) hfxy
  · exact main y x h (by omega) hfxy.symm

/-- **The analytic input** (rungs C2-C5): the Gaussian average of FC's `E` in the radius is the smoothed Voronoi
series up to `O(√R)`. -/
def SmoothedVoronoiC : Prop :=
  ∃ C R₀ : ℝ, ∀ R ≥ R₀, ∀ δ : ℝ, (Real.log R)⁻¹ ≤ δ → δ ≤ 1 →
    |(∫ u, phi δ u * E (R + u)) - √R / π * ∑' k : ℤ × ℤ, w δ R k| ≤ C * √R

theorem rpow_quarter_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (1/4 : ℝ) = √√x := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

set_option maxHeartbeats 1000000 in
/-- **Rung C1.** The smoothed Voronoi expansion implies Hardy's Ω-theorem in formal-conjectures' wording. -/
theorem error_not_isLittleO_of_smoothedVoronoi (hV : SmoothedVoronoiC) :
    ¬E =o[atTop] (fun r => √r * √√r.log) := by
  intro hE
  have hE' : E =o[atTop] fcf := hE
  obtain ⟨C, R₀, hCV⟩ := hV
  set ε : ℝ := 1 / 4000 with hε
  obtain ⟨R₁, hR₁, hup⟩ := smooth_upper hE' (ε := ε) (by norm_num)
  set K : ℝ := 1200 * (|C| + 425) with hK
  have hK0 : 0 < K := by positivity
  -- choose M
  set M : ℕ := ⌈max (max 8 (4 * K ^ 4)) (Real.log (max (max R₀ R₁) 1))⌉₊ + 1 with hMdef
  have hMc := Nat.le_ceil (max (max 8 (4 * K ^ 4)) (Real.log (max (max R₀ R₁) 1)))
  have hMr : max (max 8 (4 * K ^ 4)) (Real.log (max (max R₀ R₁) 1)) + 1 ≤ (M : ℝ) := by
    rw [hMdef]; push_cast; linarith
  have m1 := le_max_left (8:ℝ) (4 * K ^ 4)
  have m2 := le_max_right (8:ℝ) (4 * K ^ 4)
  have m3 := le_max_left (max 8 (4 * K ^ 4)) (Real.log (max (max R₀ R₁) 1))
  have m4 := le_max_right (max 8 (4 * K ^ 4)) (Real.log (max (max R₀ R₁) 1))
  have hM8r : (8:ℝ) + 1 ≤ M := by linarith
  have hM8 : 8 ≤ M := by
    have : (8:ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hMK : 4 * K ^ 4 < (M : ℝ) := by linarith
  have hMlog : Real.log (max (max R₀ R₁) 1) ≤ (M : ℝ) := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  -- δ and R₂
  set δ : ℝ := 2 / √(M : ℝ) with hδ
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.mpr hM0
  have hδ0 : 0 < δ := by positivity
  have hδM : δ ^ 2 * M = 4 := by
    rw [hδ, div_pow, Real.sq_sqrt hM0.le]; field_simp; norm_num
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hsM, Real.le_sqrt (by norm_num) hM0.le]; linarith
  set R₂ : ℝ := exp M with hR₂
  have hR₂big : max (max R₀ R₁) 1 ≤ R₂ := by
    rw [hR₂, ← Real.log_le_iff_le_exp (by positivity)]; exact hMlog
  -- Dirichlet
  obtain ⟨q, hq1, hqQ, hq⟩ := dirichlet_simul M 64 (by norm_num) (fun i => R₂ * √((i : ℝ) + 1))
  have hq' : ∀ i < M, ∃ m : ℤ, |(q : ℝ) * (R₂ * √((i : ℝ) + 1)) - m| ≤ 1 / 64 := by
    intro i hi; obtain ⟨m, hm⟩ := hq i hi; exact ⟨m, by simpa using hm⟩
  set R : ℝ := (q : ℝ) * R₂ with hR
  have hq1r : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have hR₂1 : 1 ≤ R₂ := le_trans (le_max_right _ _) hR₂big
  have hRR₂ : R₂ ≤ R := by rw [hR]; nlinarith
  have hR1 : 1 ≤ R := le_trans hR₂1 hRR₂
  have hRR₀ : R₀ ≤ R := by linarith [le_max_left R₀ R₁, le_max_left (max R₀ R₁) 1]
  have hRR₁ : R₁ ≤ R := by linarith [le_max_right R₀ R₁, le_max_left (max R₀ R₁) 1]
  have hlogR : (M : ℝ) ≤ Real.log R := by
    have : Real.log R₂ = M := by rw [hR₂, Real.log_exp]
    rw [← this]; exact Real.log_le_log (by linarith) hRR₂
  have hδlog : (Real.log R)⁻¹ ≤ δ := by
    have hl0 : 0 < Real.log R := by linarith
    rw [inv_le_comm₀ hl0 hδ0, hδ, inv_div]
    have : √(M:ℝ) / 2 ≤ M := by
      have := Real.sqrt_le_sqrt (show (M:ℝ) ≤ M ^ 2 by nlinarith)
      rw [Real.sqrt_sq hM0.le] at this; linarith
    linarith
  -- the three estimates
  have hV := hCV R hRR₀ δ hδlog hδ1
  have hU := hup R hRR₁ δ hδ0 hδ1
  have hS := main_sum_le hM8 hδM hq'
  -- log (2R) ≤ 6M
  have hlog2R : Real.log (2 * R) ≤ 6 * M := by
    have hq64 : Real.log q ≤ M * Real.log 64 := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by linarith) (by exact_mod_cast hqQ)
    have hl64 : Real.log 64 < 4.2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h5 : exp (4.2:ℝ) = exp 4 * exp 0.2 := by rw [← Real.exp_add]; norm_num
      have h6 : exp (4:ℝ) = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have h7 : (2.7182818283:ℝ) ^ 4 ≤ exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) this.le 4
      have h8 : (0.2:ℝ) + 1 ≤ exp 0.2 := Real.add_one_le_exp _
      norm_num at h7
      rw [h5]; nlinarith [Real.exp_pos (4:ℝ)]
    have hl2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9; linarith
    have hsplit : Real.log (2 * R) = Real.log 2 + Real.log q + M := by
      rw [Real.log_mul (by norm_num) (by linarith), hR, Real.log_mul (by linarith) (by positivity),
        hR₂, Real.log_exp]; ring
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hl64.le hM0.le
    nlinarith
  set X : ℝ := ((M : ℝ) / 4) ^ (1/4 : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXK : K < X := by
    rw [hX, rpow_quarter_eq _ (by positivity)]
    have h1 : K ^ 4 < (M : ℝ) / 4 := by linarith
    have h2 : K ^ 2 < √((M : ℝ) / 4) := by
      rw [Real.lt_sqrt (by positivity), ← pow_mul]; exact h1
    rw [Real.lt_sqrt hK0.le]; exact h2
  -- fcf (2R) ≤ (3/2)·3·√R·X
  have hfcf : fcf (2 * R) ≤ (3/2 * √R) * (3 * X) := by
    unfold fcf
    have h1 : √(2 * R) ≤ 3/2 * √R := by
      rw [Real.sqrt_mul (by norm_num)]
      have : √(2:ℝ) ≤ 3/2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    have h2 : √√(Real.log (2 * R)) ≤ 3 * X := by
      have hl0 : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
      have : √√(Real.log (2 * R)) ≤ √√(24 * ((M:ℝ) / 4)) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by linarith))
      refine this.trans ?_
      rw [hX, rpow_quarter_eq _ (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity)]
      have h24 : √√(24:ℝ) ≤ 3 := by
        rw [Real.sqrt_le_left (by norm_num), Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_le_mul_of_nonneg_right h24 (Real.sqrt_nonneg _)
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  -- combine
  have hsR : 1 ≤ √R := by rw [Real.one_le_sqrt]; exact hR1
  set I := ∫ u, phi δ u * E (R + u)
  set S := ∑' k : ℤ × ℤ, w δ R k
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hA : √R / π * (X / 120) ≤ -(√R / π * S) := by
    have : -(1 / 120) * X ≥ S := hS
    have h' : √R / π * S ≤ √R / π * (-(1/120) * X) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hB : -(√R / π * S) ≤ C * √R + |I| := by
    have h1 := (abs_le.mp hV).2
    have h2 := neg_le_abs I
    linarith
  have hC : |I| ≤ ε * ((3/2 * √R) * (3 * X)) + 425 :=
    hU.trans (add_le_add_left (mul_le_mul_of_nonneg_left hfcf (by norm_num)) 425)
  -- √R·X/(120π) ≤ |C|√R + (9/8000)√R X + 425 √R
  have e1 : ε * ((3/2 * √R) * (3 * X)) = √R * X * (9 / 8000) := by rw [hε]; ring
  have e2 : √R / π * (X / 120) = √R * X / (120 * π) := by rw [div_mul_div_comm, mul_comm π 120]
  have h2 : C * √R ≤ |C| * √R := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
  have h3 : (425:ℝ) ≤ 425 * √R := by linarith
  have hfin : √R * X / (120 * π) ≤ √R * (|C| + 425) + √R * X * (9 / 8000) := by
    have e3 : √R * (|C| + 425) = |C| * √R + 425 * √R := by ring
    rw [e3, ← e2]; linarith
  have hsR0 : 0 < √R := by linarith
  have hfin' : X / (120 * π) ≤ (|C| + 425) + X * (9 / 8000) := by
    have : √R * (X / (120 * π)) ≤ √R * ((|C| + 425) + X * (9 / 8000)) := by
      have e4 : √R * (X / (120 * π)) = √R * X / (120 * π) := by ring
      have e5 : √R * ((|C| + 425) + X * (9 / 8000)) = √R * (|C| + 425) + √R * X * (9 / 8000) := by ring
      rw [e4, e5]; exact hfin
    exact le_of_mul_le_mul_left this hsR0
  have hpiX : X / 480 ≤ X / (120 * π) := by
    apply div_le_div_of_nonneg_left hX0 (by positivity); linarith
  have hX1100 : X / 1100 ≤ |C| + 425 := by linarith
  linarith

end HardyC1

end

-- ===== from HardyOmegaFC.DiscFourier =====
section

/-!
# Gauss circle problem, rung C3: the Fourier transform of a disc

For `ρ > 0` and `ξ ∈ ℝ²` (`ℝ² = EuclideanSpace ℝ (Fin 2)`, formal-conjectures' notation, as in C1),
with Mathlib's additive character `𝐞 t = exp(2πit)`:

* `disc_ft : ∫ x in closedBall 0 ρ, 𝐞(-⟪x, ξ⟫) = ρ² · I(ρ‖ξ‖)`,
  `I t := 2 ∫_{-1}^{1} √(1-y²) cos(2πty) dy` (real; `I t = J₁(2πt)/t`, checked numerically in
  `controls/disc_ft_check.py`, not used here);
* `fourier_indicator_ball`: the same identity in Mathlib's `𝓕` form;
* `I_zero : I 0 = π`, `abs_I_le : |I t| ≤ π`, `I_neg : I (-t) = I t`, `continuous_I`.

Route: rotate `ξ` onto the first axis (an orthonormal basis with first vector `ξ/‖ξ‖`; `b.repr` is a linear isometry,
so it preserves volume and the disc), pass to `ℝ × ℝ`, Fubini (the vertical section of the disc at `a` has length
`2√(ρ²-a²)`, which is `0` off `[-ρ, ρ]` because `√` of a negative is `0`), scale `a = ρy`, and fold the odd sine part.
-/

open Real MeasureTheory Set intervalIntegral
open scoped EuclideanGeometry FourierTransform

namespace HardyC3

/-- `I t = 2 ∫_{-1}^{1} √(1-y²) cos(2πty) dy`, so that `\hat{1_{B_ρ}}(ξ) = ρ² I(ρ‖ξ‖)`. -/
noncomputable def I (t : ℝ) : ℝ := 2 * ∫ y in (-1:ℝ)..1, √(1 - y ^ 2) * cos (2 * π * t * y)

/-! ## Elementary properties of `I` -/

theorem I_zero : I 0 = π := by
  unfold I
  simp only [mul_zero, zero_mul, cos_zero, mul_one]
  rw [integral_sqrt_one_sub_sq]
  ring

theorem abs_I_le (t : ℝ) : |I t| ≤ π := by
  have hle : |∫ y in (-1:ℝ)..1, √(1 - y ^ 2) * cos (2 * π * t * y)| ≤ π / 2 := by
    rw [← integral_sqrt_one_sub_sq]
    refine (abs_integral_le_integral_abs (by norm_num)).trans ?_
    refine integral_mono_on (by norm_num) ?_ ?_ ?_
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    · intro y _
      rw [abs_mul, abs_of_nonneg (sqrt_nonneg _)]
      exact mul_le_of_le_one_right (sqrt_nonneg _) (abs_cos_le_one _)
  rw [I, abs_mul, abs_two]
  linarith

theorem continuous_I : Continuous I := by
  unfold I
  refine continuous_const.mul ?_
  exact continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _

/-! ## The one-dimensional integral -/

theorem e_add_e_neg (x : ℝ) : (𝐞 x : ℂ) + 𝐞 (-x) = 2 * ((cos (2 * π * x) : ℝ) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Complex.ofReal_cos, Complex.cos]
  have : ((2 * π * (-x) : ℝ) : ℂ) = -((2 * π * x : ℝ) : ℂ) := by push_cast; ring
  rw [this, neg_mul]; ring

/-- The odd sine part drops out: `∫_{-1}^{1} √(1-y²) e(-ty) dy = I t / 2`. -/
theorem integral_sqrt_mul_exp (t : ℝ) :
    ∫ y in (-1:ℝ)..1, ((√(1 - y ^ 2) : ℝ) : ℂ) * (𝐞 (-(t * y)) : ℂ) = ((I t / 2 : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun y => ((√(1 - y ^ 2) : ℝ) : ℂ) * (𝐞 (-(t * y)) : ℂ) with hh
  have hc : Continuous h := by
    simp only [hh, Real.fourierChar_apply]
    fun_prop
  have hneg : ∫ y in (-1:ℝ)..1, h (-y) = ∫ y in (-1:ℝ)..1, h y := by
    rw [integral_comp_neg]; norm_num
  have hpt : ∀ y : ℝ, h y + h (-y) = (((2 * (√(1 - y ^ 2) * cos (2 * π * t * y))) : ℝ) : ℂ) := by
    intro y
    simp only [hh]
    rw [neg_sq, show -(t * -y) = t * y by ring, ← mul_add, add_comm, e_add_e_neg,
      show 2 * π * (t * y) = 2 * π * t * y by ring]
    push_cast; ring
  have hi2 : IntervalIntegrable (fun y => h (-y)) volume (-1) 1 :=
    (hc.comp continuous_neg).intervalIntegrable _ _
  have hsum := integral_add (hc.intervalIntegrable (-1) 1) hi2
  simp_rw [hpt, hneg] at hsum
  rw [integral_ofReal] at hsum
  have : (2 : ℂ) * ∫ y in (-1:ℝ)..1, h y = ((I t : ℝ) : ℂ) := by
    rw [two_mul, ← hsum, I, intervalIntegral.integral_const_mul]
  rw [show ((I t / 2 : ℝ) : ℂ) = ((I t : ℝ) : ℂ) / 2 by push_cast; ring, ← this]
  ring

/-! ## Sections of the disc and Fubini on the plane -/

theorem volume_real_sq_le (c : ℝ) : volume.real {b : ℝ | b ^ 2 ≤ c} = 2 * √c := by
  rcases lt_or_ge c 0 with hc | hc
  · have : {b : ℝ | b ^ 2 ≤ c} = ∅ := by
      ext b; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hc (sq_nonneg b)
    rw [this, sqrt_eq_zero_of_nonpos hc.le]; simp
  · have : {b : ℝ | b ^ 2 ≤ c} = Icc (-√c) √c := by
      ext b
      simp only [mem_ofPred_eq, mem_Icc]
      exact Real.sq_le hc
    rw [this, Real.volume_real_Icc]
    have := sqrt_nonneg c
    rw [max_eq_left (by linarith)]; ring

/-- The disc in `ℝ × ℝ` coordinates. -/
def discP (ρ : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ ρ ^ 2}

theorem measurableSet_discP (ρ : ℝ) : MeasurableSet (discP ρ) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- Fubini: `∫_{disc} F(p.1) = ∫_ℝ F(a) · 2√(ρ²-a²) da` for continuous `F`. -/
theorem integral_discP (ρ : ℝ) {F : ℝ → ℂ} (hF : Continuous F) :
    ∫ p : ℝ × ℝ, (discP ρ).indicator (fun p => F p.1) p =
      ∫ a : ℝ, ((2 * √(ρ ^ 2 - a ^ 2) : ℝ) : ℂ) * F a := by
  have hsub : discP ρ ⊆ Icc (-|ρ|) |ρ| ×ˢ Icc (-|ρ|) |ρ| := by
    rintro ⟨a, b⟩ h
    simp only [discP, mem_ofPred_eq] at h
    simp only [mem_prod, mem_Icc, ← abs_le]
    constructor <;> apply sq_le_sq.mp <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_abs ρ]
  have hint : Integrable ((discP ρ).indicator (fun p : ℝ × ℝ => F p.1)) := by
    refine IntegrableOn.integrable_indicator ?_ (measurableSet_discP ρ)
    exact ((hF.comp continuous_fst).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hsub
  refine (integral_prod _ hint).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only
  have hset : ∀ b : ℝ, (discP ρ).indicator (fun p : ℝ × ℝ => F p.1) (a, b) =
      {b : ℝ | b ^ 2 ≤ ρ ^ 2 - a ^ 2}.indicator (fun _ => F a) b := by
    intro b
    by_cases hb : b ^ 2 ≤ ρ ^ 2 - a ^ 2
    · rw [indicator_of_mem (show (a, b) ∈ discP ρ by simp only [discP, mem_ofPred_eq]; linarith),
        indicator_of_mem (show b ∈ {b : ℝ | b ^ 2 ≤ ρ ^ 2 - a ^ 2} from hb)]
    · rw [indicator_of_notMem (show (a, b) ∉ discP ρ by simp only [discP, mem_ofPred_eq]; linarith),
        indicator_of_notMem (show b ∉ {b : ℝ | b ^ 2 ≤ ρ ^ 2 - a ^ 2} from hb)]
  simp_rw [hset]
  rw [integral_indicator_const _ (measurableSet_le (by fun_prop) (by fun_prop)), volume_real_sq_le,
    Complex.real_smul]

/-! ## The disc along the first axis -/

/-- `x ↦ (x 0, x 1)`, a volume-preserving equivalence `ℝ² ≃ᵐ ℝ × ℝ`. -/
noncomputable def toProd : ℝ² ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem toProd_apply (x : ℝ²) : toProd x = (x 0, x 1) := rfl

theorem toProd_mp : MeasurePreserving toProd :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

theorem mem_closedBall_iff (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℝ²) :
    x ∈ Metric.closedBall (0 : ℝ²) ρ ↔ toProd x ∈ discP ρ := by
  rw [Metric.mem_closedBall, dist_zero_right, toProd_apply, discP, mem_ofPred_eq,
    ← sq_le_sq₀ (norm_nonneg _) hρ, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]

/-- The disc integral of a function of the first coordinate. -/
theorem integral_ball_fst (ρ : ℝ) (hρ : 0 ≤ ρ) {F : ℝ → ℂ} (hF : Continuous F) :
    ∫ x in Metric.closedBall (0 : ℝ²) ρ, F (x 0) = ∫ a : ℝ, ((2 * √(ρ ^ 2 - a ^ 2) : ℝ) : ℂ) * F a := by
  rw [← integral_discP ρ hF, ← MeasureTheory.integral_indicator Metric.isClosed_closedBall.measurableSet,
    ← toProd_mp.integral_comp' ((discP ρ).indicator (fun p => F p.1))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ²) ρ
  · rw [indicator_of_mem hx, indicator_of_mem ((mem_closedBall_iff ρ hρ x).mp hx), toProd_apply]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((mem_closedBall_iff ρ hρ x).mpr h))]

/-- Scaling `a = ρy`: `∫_ℝ 2√(ρ²-a²) e(-sa) da = ρ² I(ρs)`. -/
theorem integral_section_exp (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    ∫ a : ℝ, ((2 * √(ρ ^ 2 - a ^ 2) : ℝ) : ℂ) * (𝐞 (-(s * a)) : ℂ) = ((ρ ^ 2 * I (ρ * s) : ℝ) : ℂ) := by
  set G : ℝ → ℂ := fun a => ((2 * √(ρ ^ 2 - a ^ 2) : ℝ) : ℂ) * (𝐞 (-(s * a)) : ℂ) with hG
  have hzero : ∀ a, a ∉ Ioc (-ρ) ρ → G a = 0 := by
    intro a ha
    have : ρ ^ 2 - a ^ 2 ≤ 0 := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at ha
      rcases ha with h | h <;> nlinarith
    simp [hG, sqrt_eq_zero_of_nonpos this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_of_le (by linarith)]
  have hscale : ∫ y in (-1:ℝ)..1, G (ρ * y) = ρ⁻¹ • ∫ a in -ρ..ρ, G a := by
    rw [integral_comp_mul_left (fun y => G y) hρ.ne']; norm_num
  have hGy : ∀ y : ℝ, G (ρ * y) = ((2 * ρ : ℝ) : ℂ) *
      (((√(1 - y ^ 2) : ℝ) : ℂ) * (𝐞 (-((ρ * s) * y)) : ℂ)) := by
    intro y
    have : √(ρ ^ 2 - (ρ * y) ^ 2) = ρ * √(1 - y ^ 2) := by
      rw [show ρ ^ 2 - (ρ * y) ^ 2 = ρ ^ 2 * (1 - y ^ 2) by ring, sqrt_mul (sq_nonneg ρ),
        sqrt_sq hρ.le]
    simp only [hG, this]
    rw [show -(s * (ρ * y)) = -(ρ * s * y) by ring]
    push_cast; ring
  simp_rw [hGy] at hscale
  rw [intervalIntegral.integral_const_mul, integral_sqrt_mul_exp] at hscale
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have := congrArg (fun z : ℂ => (ρ : ℂ) * z) hscale
  simp only [Complex.real_smul, Complex.ofReal_inv] at this
  rw [mul_inv_cancel_left₀ hρ'] at this
  rw [← this]; push_cast; ring

/-- The disc transform along the first axis. -/
theorem disc_ft_axis (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    ∫ x in Metric.closedBall (0 : ℝ²) ρ, (𝐞 (-(s * x 0)) : ℂ) = ((ρ ^ 2 * I (ρ * s) : ℝ) : ℂ) := by
  rw [integral_ball_fst ρ hρ.le (F := fun a => (𝐞 (-(s * a)) : ℂ)) (by
    simp only [Real.fourierChar_apply]; fun_prop)]
  exact integral_section_exp ρ hρ s

/-! ## Rotation invariance -/

/-- An orthonormal basis of `ℝ²` whose first vector is `u` (for a unit vector `u`). -/
theorem exists_basis_first (u : ℝ²) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ ℝ², b 0 = u := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ : Fin 2 => u)) := by
    refine ⟨fun i => by simpa using hu, fun i j hij => ?_⟩
    exact absurd (Subtype.ext ((i.2.trans j.2.symm))) hij
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp) (s := {0})
  exact ⟨b, hb 0 rfl⟩

/-- **C3.** The Fourier transform of the disc of radius `ρ`: `∫_{‖x‖ ≤ ρ} e(-⟪x, ξ⟫) dx = ρ² I(ρ‖ξ‖)`. -/
theorem disc_ft (ρ : ℝ) (hρ : 0 < ρ) (ξ : ℝ²) :
    ∫ x in Metric.closedBall (0 : ℝ²) ρ, (𝐞 (-inner ℝ x ξ) : ℂ) = ((ρ ^ 2 * I (ρ * ‖ξ‖) : ℝ) : ℂ) := by
  rw [← disc_ft_axis ρ hρ ‖ξ‖]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  obtain ⟨b, hb⟩ := exists_basis_first (‖ξ‖⁻¹ • ξ) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn])
  have hrep : ∀ x : ℝ², inner ℝ x ξ = ‖ξ‖ * b.repr x 0 := by
    intro x
    rw [b.repr_apply_apply, hb, inner_smul_left, real_inner_comm, RCLike.conj_to_real, ← mul_assoc,
      mul_inv_cancel₀ hn, one_mul]
  have hball : ∀ x : ℝ², b.repr x ∈ Metric.closedBall (0 : ℝ²) ρ ↔ x ∈ Metric.closedBall (0 : ℝ²) ρ := by
    intro x; simp only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← MeasureTheory.integral_indicator Metric.isClosed_closedBall.measurableSet,
    ← MeasureTheory.integral_indicator Metric.isClosed_closedBall.measurableSet,
    ← b.measurePreserving_measurableEquiv.integral_comp'
      ((Metric.closedBall (0 : ℝ²) ρ).indicator (fun x => (𝐞 (-(‖ξ‖ * x 0)) : ℂ)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hbx : b.measurableEquiv x = b.repr x := rfl
  simp only [hbx]
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ²) ρ
  · rw [indicator_of_mem hx, indicator_of_mem ((hball x).mpr hx), hrep]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hball x).mp h))]

end HardyC3

end

-- ===== from HardyOmegaFC.CirclePoisson =====
section

/-!
# Gauss circle problem, rung C2: Poisson summation for the radially smoothed count

Part 1 (`poisson_torus`): Poisson summation on `ℤᵈ ⊂ ℝᵈ` for a continuous `f` whose integer translates are locally
uniformly summable and whose Fourier transform is summable on `ℤᵈ`. Mathlib has the `d`-dimensional Fourier series
(`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`) but only the 1-D Poisson formula; this is the `d`-dimensional
version, proved the same way (periodise, descend to the torus, unfold the Fourier coefficients).
-/

open MeasureTheory ContinuousMap Topology Set UnitAddTorus TopologicalSpace Function

noncomputable section

namespace HardyC2

section Torus

variable {d : Type*}

/-- An integer vector as a real vector. -/
def iv (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

theorem iv_add (m n : d → ℤ) : iv (m + n) = iv m + iv n := by
  ext i; simp [iv]

/-- The projection `ℝᵈ → (ℝ/ℤ)ᵈ`. -/
def qt : C(d → ℝ, UnitAddTorus d) :=
  ⟨fun x i => (x i : UnitAddCircle), continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)⟩

theorem qt_apply (x : d → ℝ) : qt x = fun i => (x i : UnitAddCircle) := rfl

theorem isQuotientMap_qt : IsQuotientMap (qt : (d → ℝ) → UnitAddTorus d) :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

theorem qt_add_iv (x : d → ℝ) (n : d → ℤ) : qt (x + iv n) = qt x := by
  ext i
  simp only [qt_apply, Pi.add_apply, iv, AddCircle.coe_add]
  have : ((n i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨n i, by simp⟩
  rw [this, add_zero]

theorem qt_eq_iff (x y : d → ℝ) (h : qt x = qt y) : ∃ m : d → ℤ, x = y + iv m := by
  have hi : ∀ i, ∃ k : ℤ, x i = y i + k := by
    intro i
    have := congrFun h i
    simp only [qt_apply] at this
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp this)
    exact ⟨k, by simp at hk; linarith⟩
  choose m hm using hi
  exact ⟨m, funext fun i => by simp [iv, hm i]⟩

end Torus

section Periodise

variable {d : Type*} [Fintype d]

/-- The translate `x ↦ f (x + n)`. -/
def tr (f : C(d → ℝ, ℂ)) (n : d → ℤ) : C(d → ℝ, ℂ) := f.comp (ContinuousMap.addRight (iv n))

theorem tr_apply (f : C(d → ℝ, ℂ)) (n : d → ℤ) (x : d → ℝ) : tr f n x = f (x + iv n) := rfl

/-- The unit box `∏ (0, 1]` (the fundamental domain `mFourierCoeff_eq_integral` uses with `a = 0`). -/
def B : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0:ℝ) 1}

/-- The tile `B + n`. -/
def S (n : d → ℤ) : Set (d → ℝ) := {x | ∀ i, x i - n i ∈ Ioc (0:ℝ) 1}

/-- The closed unit box, a compact set containing `B`. -/
def Kc : Compacts (d → ℝ) := ⟨Icc 0 1, isCompact_Icc⟩

theorem B_sub_Kc : (B : Set (d → ℝ)) ⊆ ((Kc (d := d)) : Set (d → ℝ)) := fun x hx =>
  ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

theorem measurableSet_S (n : d → ℤ) : MeasurableSet (S n) := by
  have : S n = ⋂ i, (fun x : d → ℝ => x i - n i) ⁻¹' Ioc (0:ℝ) 1 := by ext x; simp [S]
  rw [this]
  exact MeasurableSet.iInter fun i => ((measurable_pi_apply i).sub_const _) measurableSet_Ioc

theorem mem_S_iff (n : d → ℤ) (x : d → ℝ) : x ∈ S n ↔ ∀ i, ⌈x i⌉ = n i + 1 := by
  simp only [S, mem_ofPred_eq, mem_Ioc, Int.ceil_eq_iff]
  refine forall_congr' fun i => ?_
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem pairwise_disjoint_S : Pairwise (Disjoint on (S : (d → ℤ) → Set (d → ℝ))) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun x hm hn => hmn ?_
  rw [mem_S_iff] at hm hn
  funext i
  have := (hm i).symm.trans (hn i)
  omega

theorem iUnion_S : (⋃ n : d → ℤ, S n) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1, ?_⟩
  rw [mem_S_iff]; intro i; ring

theorem S_sub_Icc (n : d → ℤ) : S n ⊆ Icc (iv n) (iv n + 1) := fun x hx =>
  ⟨fun i => by have := (hx i).1; simp [iv]; linarith, fun i => by have := (hx i).2; simp [iv]; linarith⟩

theorem preimage_S (n : d → ℤ) : (fun x => x + iv n) ⁻¹' S n = B := by
  ext x; simp [S, B, iv]

/-- Translating the box to the tile. -/
theorem setIntegral_B_add (n : d → ℤ) (G : (d → ℝ) → ℂ) :
    ∫ x in B, G (x + iv n) = ∫ y in S n, G y := by
  rw [← preimage_S n]
  exact (measurePreserving_add_right volume (iv n)).setIntegral_preimage_emb
    (measurableEmbedding_addRight _) G (S n)

theorem setIntegral_B_add_real (n : d → ℤ) (G : (d → ℝ) → ℝ) :
    ∫ x in B, G (x + iv n) = ∫ y in S n, G y := by
  rw [← preimage_S n]
  exact (measurePreserving_add_right volume (iv n)).setIntegral_preimage_emb
    (measurableEmbedding_addRight _) G (S n)

/-- The Fourier kernel `x ↦ e(-k·x)`, read off the torus. -/
noncomputable def ek (k : d → ℤ) : C(d → ℝ, ℂ) := (mFourier (-k)).comp qt

theorem ek_add (k n : d → ℤ) (x : d → ℝ) : ek k (x + iv n) = ek k x := by
  simp only [ek, ContinuousMap.comp_apply, qt_add_iv]

theorem norm_ek (k : d → ℤ) (x : d → ℝ) : ‖ek k x‖ = 1 := by
  simp only [ek, ContinuousMap.comp_apply, mFourier, ContinuousMap.coe_mk, norm_prod]
  exact Finset.prod_eq_one fun i _ => by simp [fourier_apply, Circle.norm_coe]

variable {f : C(d → ℝ, ℂ)}

theorem norm_setIntegral_B_le (n : d → ℤ) :
    ∫ x in B, ‖f (x + iv n)‖ ≤ ‖(tr f n).restrict (Kc (d := d))‖ * volume.real (B : Set (d → ℝ)) := by
  have hfin : volume (B : Set (d → ℝ)) < ⊤ :=
    (measure_mono B_sub_Kc).trans_lt (Kc (d := d)).isCompact.measure_lt_top
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun x => ‖f (x + iv n)‖) hfin
    (C := ‖(tr f n).restrict (Kc (d := d))‖) (fun x hx => by
      rw [norm_norm]
      exact ((tr f n).restrict _).norm_coe_le_norm (⟨x, B_sub_Kc hx⟩ : ((Kc (d := d)) : Set (d → ℝ))))
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

variable (hf : ∀ K : Compacts (d → ℝ), Summable fun n : d → ℤ => ‖(tr f n).restrict K‖)
include hf

theorem summable_setIntegral_norm :
    Summable fun n : d → ℤ => ∫ x in B, ‖f (x + iv n)‖ :=
  Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
    (fun n => norm_setIntegral_B_le n) ((hf (Kc (d := d))).mul_right _)

theorem integrable_ek_mul (k : d → ℤ) : Integrable (fun x => ek k x * f x) := by
  have hc : Continuous fun x => ek k x * f x := (ek k).continuous.mul f.continuous
  have hU : IntegrableOn (fun x => ek k x * f x) (⋃ n : d → ℤ, S n) := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (fun n => (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set (S_sub_Icc n)) ?_
    refine (summable_setIntegral_norm hf).congr fun n => ?_
    rw [← setIntegral_B_add_real n (fun y => ‖ek k y * f y‖)]
    simp only [norm_mul, norm_ek, one_mul]
  rwa [iUnion_S, integrableOn_univ] at hU

theorem summable_tr : Summable (tr f) := summable_of_locally_summable_norm hf

/-- The periodisation `x ↦ ∑ₙ f (x + n)`. -/
noncomputable def per : C(d → ℝ, ℂ) := ∑' n, tr f n

omit hf in
theorem per_def : per (f := f) = ∑' n, tr f n := rfl

theorem per_apply (x : d → ℝ) : per (f := f) x = ∑' n, f (x + iv n) := by
  rw [per_def, ← ContinuousMap.tsum_apply (summable_tr hf)]; rfl

theorem per_add (x : d → ℝ) (m : d → ℤ) : per (f := f) (x + iv m) = per (f := f) x := by
  rw [per_apply hf, per_apply hf, ← (Equiv.addLeft m).tsum_eq (fun n => f (x + iv n))]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addLeft, iv_add, add_assoc]

theorem factors : Function.FactorsThrough (per (f := f)) (qt : (d → ℝ) → UnitAddTorus d) := by
  intro a b h
  obtain ⟨m, rfl⟩ := qt_eq_iff a b h
  exact per_add hf b m

/-- The periodisation, as a continuous function on the torus. -/
noncomputable def perT : C(UnitAddTorus d, ℂ) := isQuotientMap_qt.lift (per (f := f)) (factors hf)

theorem perT_qt (x : d → ℝ) : perT hf (qt x) = per (f := f) x := by
  exact DFunLike.congr_fun (isQuotientMap_qt.lift_comp (per (f := f)) (factors hf)) x

/-- The Fourier coefficients of the periodisation are the Fourier transform of `f` at `ℤᵈ`. -/
theorem mFourierCoeff_perT (k : d → ℤ) : mFourierCoeff (perT hf) k = ∫ x, ek k x * f x := by
  rw [mFourierCoeff_eq_integral (perT hf) k 0]
  have h1 : ∀ x : d → ℝ, mFourier (-k) (fun i => (x i : UnitAddCircle)) • perT hf (fun i => (x i : UnitAddCircle))
      = ∑' n, ek k x * f (x + iv n) := by
    intro x
    rw [smul_eq_mul, ← qt_apply, perT_qt hf, per_apply hf, ← tsum_mul_left]; rfl
  simp only [Pi.zero_apply, zero_add]
  change ∫ x in B, _ = _
  simp_rw [h1]
  rw [← integral_tsum_of_summable_integral_norm]
  · have hint : IntegrableOn (fun x => ek k x * f x) (⋃ n : d → ℤ, S n) := by
      rw [iUnion_S]; exact (integrable_ek_mul hf k).integrableOn
    have hU := (hasSum_integral_iUnion measurableSet_S pairwise_disjoint_S hint).tsum_eq
    rw [iUnion_S, setIntegral_univ] at hU
    rw [← hU]
    refine tsum_congr fun n => ?_
    rw [← setIntegral_B_add n (fun y => ek k y * f y)]
    simp only [ek_add]
  · intro n
    have hc : Continuous fun x => ek k x * f (x + iv n) := (ek k).continuous.mul (tr f n).continuous
    exact (hc.continuousOn.integrableOn_compact (Kc (d := d)).isCompact).mono_set B_sub_Kc
  · refine (summable_setIntegral_norm hf).congr fun n => ?_
    simp only [norm_mul, norm_ek, one_mul]

/-- **Poisson summation on `ℤᵈ`.** -/
theorem poisson_torus (h_sum : Summable fun k : d → ℤ => ∫ x, ek k x * f x) :
    HasSum (fun k : d → ℤ => ∫ x, ek k x * f x) (∑' n : d → ℤ, f (iv n)) := by
  have hs : Summable (mFourierCoeff (perT hf)) := by
    have e : mFourierCoeff (perT hf) = fun k => ∫ x, ek k x * f x := funext (mFourierCoeff_perT hf)
    rw [e]; exact h_sum
  have := hasSum_mFourier_series_apply_of_summable hs (qt 0)
  have h0 : ∀ k : d → ℤ, mFourier k (qt (0 : d → ℝ)) = 1 := by
    intro k
    simp [mFourier, qt_apply]
  simp only [h0, smul_eq_mul, mul_one, mFourierCoeff_perT hf, perT_qt hf, per_apply hf, zero_add] at this
  exact this

end Periodise

/-! ## Part 2: the radially smoothed disc indicator -/

section Smooth

open HardyC1 Filter
open scoped EuclideanGeometry

/-- The Gaussian upper tail `G_δ(t) = ∫_{u ≥ t} φ_δ(u) du`. -/
def G (δ t : ℝ) : ℝ := ∫ u in Ici t, phi δ u

variable {δ : ℝ}

theorem G_nonneg (hδ : 0 < δ) (t : ℝ) : 0 ≤ G δ t :=
  setIntegral_nonneg measurableSet_Ici fun u _ => phi_nonneg hδ u

theorem G_le_one (hδ : 0 < δ) (t : ℝ) : G δ t ≤ 1 := by
  rw [← integral_phi hδ]
  exact setIntegral_le_integral (integrable_phi hδ) (Eventually.of_forall (phi_nonneg hδ))

theorem G_eq_indicator (t : ℝ) : G δ t = ∫ u, (Ici t).indicator (phi δ) u :=
  (integral_indicator measurableSet_Ici).symm

theorem continuous_G (hδ : 0 < δ) : Continuous (G δ) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  have h := continuousAt_of_dominated (F := fun t u => (Ici t).indicator (phi δ) u) (x₀ := t₀)
    (bound := phi δ)
    (Eventually.of_forall fun t => ((integrable_phi hδ).indicator measurableSet_Ici).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun u _ => phi_nonneg hδ u) u)]
      exact Set.indicator_le_self' (fun u _ => phi_nonneg hδ u) u)
    (integrable_phi hδ)
    (by
      have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ ({t₀}ᶜ : Set ℝ) :=
        compl_mem_ae_iff.mpr (measure_singleton t₀)
      filter_upwards [hne] with u hu
      rcases lt_or_gt_of_ne (Ne.symm (hu : u ≠ t₀)) with h | h
      · refine (continuousAt_const (y := phi δ u)).congr ?_
        filter_upwards [eventually_lt_nhds h] with t ht
        simp [Set.indicator_of_mem (show u ∈ Ici t from le_of_lt ht)]
      · refine (continuousAt_const (y := (0:ℝ))).congr ?_
        filter_upwards [eventually_gt_nhds h] with t ht
        simp [Set.indicator_of_notMem (show u ∉ Ici t from not_le.mpr ht)])
  have e : G δ = fun t => ∫ u, (Ici t).indicator (phi δ) u := funext G_eq_indicator
  rw [e]; exact h

theorem continuous_phi (δ : ℝ) : Continuous (phi δ) := by
  unfold phi; fun_prop

/-- The fourth moment of `φ_δ`. -/
def M4 (δ : ℝ) : ℝ := ∫ u, phi δ u * u ^ 4

theorem integrable_phi_mul_pow4 (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Integrable fun u => phi δ u * u ^ 4 := by
  refine ((integrable_gauss_scaled hδ (c := 2) two_pos).const_mul (300 * δ⁻¹)).mono'
    ((continuous_phi δ).mul (continuous_pow 4)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have h1 := phi_poly_le hδ hδ1 u
  have h2 := phi_nonneg hδ u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg h2 (sq_nonneg u), mul_nonneg h2 (pow_nonneg (sq_nonneg u) 2)]

theorem M4_nonneg (hδ : 0 < δ) : 0 ≤ M4 δ :=
  integral_nonneg fun u => mul_nonneg (phi_nonneg hδ u) (by positivity)

/-- Markov: `G_δ(t) ≤ M₄/t⁴` for `t > 0`. -/
theorem G_le_markov (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : 0 < t) : G δ t ≤ M4 δ / t ^ 4 := by
  have hI := integrable_phi_mul_pow4 hδ hδ1
  have ht4 : 0 < t ^ 4 := by positivity
  calc G δ t ≤ ∫ u in Ici t, phi δ u * u ^ 4 / t ^ 4 := by
        refine setIntegral_mono_on (integrable_phi hδ).integrableOn (hI.div_const _).integrableOn
          measurableSet_Ici fun u hu => ?_
        have hu' : t ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ ht.le hu 4
        rw [le_div_iff₀ ht4]
        exact mul_le_mul_of_nonneg_left hu' (phi_nonneg hδ u)
    _ = (∫ u in Ici t, phi δ u * u ^ 4) / t ^ 4 := integral_div _ _
    _ ≤ M4 δ / t ^ 4 := by
        refine div_le_div_of_nonneg_right ?_ ht4.le
        exact setIntegral_le_integral hI (Eventually.of_forall fun u => mul_nonneg (phi_nonneg hδ u) (by positivity))

/-- The constant in the uniform tail bound. -/
def Atail (δ : ℝ) : ℝ := 16 * (1 + M4 δ)

theorem G_le_tail (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) : G δ t ≤ Atail δ / (1 + max t 0) ^ 4 := by
  have hM := M4_nonneg hδ
  rcases le_or_gt t 1 with h | h
  · have h0 : (1 + max t 0) ^ 4 ≤ 16 := by
      have : 1 + max t 0 ≤ 2 := by have := max_le h zero_le_one; linarith
      calc (1 + max t 0) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 16 := by norm_num
    rw [le_div_iff₀ (by positivity)]
    calc G δ t * (1 + max t 0) ^ 4 ≤ 1 * 16 :=
          mul_le_mul (G_le_one hδ t) h0 (by positivity) zero_le_one
      _ ≤ Atail δ := by unfold Atail; nlinarith
  · have hmax : max t 0 = t := max_eq_left (by linarith)
    rw [hmax]
    have ht : 0 < t := by linarith
    have h1 : (1 + t) ^ 4 ≤ 16 * t ^ 4 := by
      have : 1 + t ≤ 2 * t := by linarith
      calc (1 + t) ^ 4 ≤ (2 * t) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 16 * t ^ 4 := by ring
    calc G δ t ≤ M4 δ / t ^ 4 := G_le_markov hδ hδ1 ht
      _ = 16 * M4 δ / (16 * t ^ 4) := by field_simp
      _ ≤ Atail δ / (1 + t) ^ 4 := by
          apply div_le_div₀ (by unfold Atail; positivity) (by unfold Atail; linarith) (by positivity) h1

theorem summable_inv_one_add_abs_sq : Summable fun a : ℤ => 1 / (1 + |(a : ℝ)|) ^ 2 := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0:ℤ)).compl_mem_cofinite] with a ha
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (ha : a ≠ 0)
  have hpos : 0 < |(a : ℝ)| := abs_pos.mpr ha'
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg hpos.le, Real.rpow_two, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le (by linarith) 2)

/-- The lattice weight `∏ᵢ (1 + |nᵢ|)⁻²` on `ℤ²`. -/
def bw (n : Fin 2 → ℤ) : ℝ := 1 / (1 + |(n 0 : ℝ)|) ^ 2 * (1 / (1 + |(n 1 : ℝ)|) ^ 2)

theorem summable_bw : Summable bw := by
  have h := summable_inv_one_add_abs_sq.mul_of_nonneg summable_inv_one_add_abs_sq
    (fun a => by positivity) (fun a => by positivity)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff]
  refine h.congr fun p => ?_
  simp [bw, finTwoArrowEquiv]

variable {R : ℝ}

/-- `W(x) = G_δ(‖x‖ - R)`, the radially smoothed disc indicator, on `ℝ²` read as `Fin 2 → ℝ`. -/
def Wr (δ R : ℝ) (x : Fin 2 → ℝ) : ℝ := G δ (‖(WithLp.toLp 2 x : ℝ²)‖ - R)

theorem continuous_toLp2 : Continuous fun x : Fin 2 → ℝ => (WithLp.toLp 2 x : ℝ²) :=
  PiLp.continuous_toLp 2 _

theorem continuous_Wr (hδ : 0 < δ) : Continuous (Wr δ R) :=
  (continuous_G hδ).comp (continuous_toLp2.norm.sub continuous_const)

/-- `W` as a continuous complex-valued function. -/
def Wc (hδ : 0 < δ) (R : ℝ) : C(Fin 2 → ℝ, ℂ) :=
  ⟨fun x => (Wr δ R x : ℂ), Complex.continuous_ofReal.comp (continuous_Wr hδ)⟩

theorem Wc_apply (hδ : 0 < δ) (x : Fin 2 → ℝ) : Wc hδ R x = (Wr δ R x : ℂ) := rfl

theorem abs_le_norm_toLp_iv (n : Fin 2 → ℤ) (i : Fin 2) :
    |(n i : ℝ)| ≤ ‖(WithLp.toLp 2 (iv n) : ℝ²)‖ := by
  have := PiLp.norm_apply_le (WithLp.toLp 2 (iv n) : ℝ²) i
  simpa [iv] using this

/-- The integer translates of `W` are locally uniformly summable (`poisson_torus`'s `hf`). -/
theorem hnorm_W (hδ : 0 < δ) (hδ1 : δ ≤ 1) (K : Compacts (Fin 2 → ℝ)) :
    Summable fun n : Fin 2 → ℤ => ‖(tr (Wc hδ R) n).restrict K‖ := by
  obtain ⟨ρ, hρ⟩ := K.isCompact.exists_bound_of_continuousOn continuous_toLp2.continuousOn
  set c := max ρ 0 + |R| with hc
  have hc0 : 0 ≤ c := by positivity
  have hA : 0 ≤ Atail δ := by unfold Atail; linarith [M4_nonneg hδ]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_bw.mul_left (Atail δ * (1 + c) ^ 4))
  refine (ContinuousMap.norm_le _ (by unfold bw; positivity)).mpr fun ⟨x, hx⟩ => ?_
  simp only [ContinuousMap.restrict_apply, tr_apply, Wc_apply, Complex.norm_real, Real.norm_eq_abs, Wr]
  rw [abs_of_nonneg (G_nonneg hδ _)]
  refine (G_le_tail hδ hδ1 _).trans ?_
  set s := ‖(WithLp.toLp 2 (iv n) : ℝ²)‖ with hs
  set t := ‖(WithLp.toLp 2 (x + iv n) : ℝ²)‖ - R with ht
  have hx' : ‖(WithLp.toLp 2 x : ℝ²)‖ ≤ ρ := hρ x hx
  have hts : s - c ≤ t := by
    have e : (WithLp.toLp 2 (x + iv n) : ℝ²) = WithLp.toLp 2 x + WithLp.toLp 2 (iv n) := WithLp.toLp_add _ _ _
    have h3 : s - ‖(WithLp.toLp 2 x : ℝ²)‖ ≤ ‖(WithLp.toLp 2 (x + iv n) : ℝ²)‖ := by
      rw [e]
      have := norm_sub_le (WithLp.toLp 2 x + WithLp.toLp 2 (iv n) : ℝ²) (WithLp.toLp 2 x)
      simp only [add_sub_cancel_left] at this
      linarith
    have : -R ≥ -|R| := by linarith [le_abs_self R]
    have : ρ ≤ max ρ 0 := le_max_left _ _
    linarith
  have hs0 : 0 ≤ s := norm_nonneg _
  set M := max t 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMt : t ≤ M := le_max_left _ _
  have hE : (1 + s) / (1 + c) ≤ 1 + M := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hM0 hc0]
  have hEpos : 0 < (1 + s) / (1 + c) := by positivity
  have hab : (1 + |(n 0 : ℝ)|) ^ 2 * (1 + |(n 1 : ℝ)|) ^ 2 ≤ (1 + s) ^ 4 := by
    have h0 := abs_le_norm_toLp_iv n 0
    have h1 := abs_le_norm_toLp_iv n 1
    have : (1 + s) ^ 4 = (1 + s) ^ 2 * (1 + s) ^ 2 := by ring
    rw [this]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 2)
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity) (by positivity)
  calc Atail δ / (1 + M) ^ 4 ≤ Atail δ / ((1 + s) / (1 + c)) ^ 4 :=
        div_le_div_of_nonneg_left hA (by positivity) (pow_le_pow_left₀ hEpos.le hE 4)
    _ = Atail δ * (1 + c) ^ 4 / (1 + s) ^ 4 := by
        rw [div_pow]; field_simp
    _ ≤ Atail δ * (1 + c) ^ 4 / ((1 + |(n 0 : ℝ)|) ^ 2 * (1 + |(n 1 : ℝ)|) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hab
    _ = Atail δ * (1 + c) ^ 4 * bw n := by
        unfold bw; field_simp

end Smooth

/-! ### The Fourier transform of `W` (C3's disc transform under the Gaussian average) -/

section FT

open HardyC1 HardyC3 Filter
open scoped EuclideanGeometry FourierTransform

variable {δ R : ℝ}

/-- An integer frequency as a vector of `ℝ²`. -/
def kv (k : Fin 2 → ℤ) : ℝ² := WithLp.toLp 2 (iv k)

theorem ek_ofLp (k : Fin 2 → ℤ) (y : ℝ²) : ek k (WithLp.ofLp y) = (𝐞 (-inner ℝ y (kv k)) : ℂ) := by
  simp only [ek, ContinuousMap.comp_apply, mFourier, ContinuousMap.coe_mk, qt_apply, fourier_coe_apply,
    Real.fourierChar_apply, Fin.prod_univ_two, ← Complex.exp_add]
  congr 1
  simp only [kv, iv, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, Pi.neg_apply,
    WithLp.ofLp_toLp]
  push_cast
  ring

/-- The `(u, y)` integrand: `φ_δ(u) 1(‖y‖ ≤ R+u) e(-⟨y, k⟩)`. -/
def Fk (δ R : ℝ) (k : Fin 2 → ℤ) (u : ℝ) (y : ℝ²) : ℂ :=
  (phi δ u : ℂ) * (Metric.closedBall (0:ℝ²) (R + u)).indicator (fun y => (𝐞 (-inner ℝ y (kv k)) : ℂ)) y

theorem integral_Fk_u (hδ : 0 < δ) (k : Fin 2 → ℤ) (y : ℝ²) :
    ∫ u, Fk δ R k u y = (𝐞 (-inner ℝ y (kv k)) : ℂ) * (G δ (‖y‖ - R) : ℂ) := by
  rw [G_eq_indicator, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Fk]
  by_cases h : ‖y‖ - R ≤ u
  · have hy : y ∈ Metric.closedBall (0:ℝ²) (R + u) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    rw [indicator_of_mem hy, indicator_of_mem (show u ∈ Ici (‖y‖ - R) from h)]; ring
  · have hy : y ∉ Metric.closedBall (0:ℝ²) (R + u) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    rw [indicator_of_notMem hy, indicator_of_notMem (show u ∉ Ici (‖y‖ - R) from h)]; simp

/-- `Ŵ(k)` integrand in `u`: `(R+u)² I((R+u)‖k‖)` for `R + u > 0`, else `0`. -/
def hatW (R : ℝ) (k : Fin 2 → ℤ) (u : ℝ) : ℝ :=
  if 0 < R + u then (R + u) ^ 2 * I ((R + u) * ‖kv k‖) else 0

theorem integral_Fk_y (k : Fin 2 → ℤ) (u : ℝ) :
    ∫ y, Fk δ R k u y = ((phi δ u * hatW R k u : ℝ) : ℂ) := by
  simp only [Fk]
  rw [integral_const_mul, integral_indicator Metric.isClosed_closedBall.measurableSet, hatW]
  split_ifs with h
  · rw [disc_ft _ h]; push_cast; ring
  · have h0 : volume (Metric.closedBall (0:ℝ²) (R + u)) = 0 := by
      rw [EuclideanSpace.volume_closedBall_fin_two, ENNReal.ofReal_of_nonpos (not_lt.mp h)]; simp
    rw [setIntegral_measure_zero _ h0]; simp

theorem integrable_phi_mul_sq (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Integrable fun u => phi δ u * u ^ 2 := by
  refine ((integrable_gauss_scaled hδ (c := 2) two_pos).const_mul (300 * δ⁻¹)).mono'
    ((continuous_phi δ).mul (continuous_pow 2)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have h1 := phi_poly_le hδ hδ1 u
  have h2 := phi_nonneg hδ u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg h2 (sq_nonneg u), mul_nonneg h2 (pow_nonneg (sq_nonneg u) 2)]

/-- The set `{(u, y) : ‖y‖ ≤ R + u}`. -/
def SR (R : ℝ) : Set (ℝ × ℝ²) := {p | ‖p.2‖ ≤ R + p.1}

theorem measurableSet_SR (R : ℝ) : MeasurableSet (SR R) :=
  (isClosed_le continuous_snd.norm (continuous_const.add continuous_fst)).measurableSet

theorem continuous_e (k : Fin 2 → ℤ) : Continuous fun y : ℝ² => (𝐞 (-inner ℝ y (kv k)) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)

theorem uncurry_Fk (k : Fin 2 → ℤ) : Function.uncurry (Fk δ R k) =
    (SR R).indicator (fun p : ℝ × ℝ² => (phi δ p.1 : ℂ) * (𝐞 (-inner ℝ p.2 (kv k)) : ℂ)) := by
  funext ⟨u, y⟩
  simp only [Function.uncurry_apply_pair, Fk]
  by_cases h : ‖y‖ ≤ R + u
  · rw [indicator_of_mem (show y ∈ Metric.closedBall (0:ℝ²) (R + u) by simpa using h),
      indicator_of_mem (show ((u, y) : ℝ × ℝ²) ∈ SR R from h)]
  · rw [indicator_of_notMem (show y ∉ Metric.closedBall (0:ℝ²) (R + u) by simpa using h),
      indicator_of_notMem (show ((u, y) : ℝ × ℝ²) ∉ SR R from h)]; simp

theorem integral_norm_Fk (hδ : 0 < δ) (k : Fin 2 → ℤ) (u : ℝ) :
    ∫ y, ‖Fk δ R k u y‖ ≤ phi δ u * ((R + u) ^ 2 * Real.pi) := by
  have e : (fun y => ‖Fk δ R k u y‖) = (Metric.closedBall (0:ℝ²) (R + u)).indicator (fun _ => phi δ u) := by
    funext y
    simp only [Fk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phi_nonneg hδ u)]
    by_cases h : y ∈ Metric.closedBall (0:ℝ²) (R + u)
    · rw [indicator_of_mem h, indicator_of_mem h, Circle.norm_coe, mul_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, norm_zero, mul_zero]
  rw [e, integral_indicator Metric.isClosed_closedBall.measurableSet, setIntegral_const, smul_eq_mul,
    mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (phi_nonneg hδ u)
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal Real.pi_pos.le, ENNReal.toReal_ofReal']
  refine mul_le_mul_of_nonneg_right ?_ Real.pi_pos.le
  rcases le_total (R + u) 0 with h | h
  · rw [max_eq_right h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  · rw [max_eq_left h]

theorem integrable_Fk (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : Fin 2 → ℤ) :
    Integrable (Function.uncurry (Fk δ R k)) (volume.prod volume) := by
  have hcont : Continuous fun p : ℝ × ℝ² => (phi δ p.1 : ℂ) * (𝐞 (-inner ℝ p.2 (kv k)) : ℂ) :=
    (Complex.continuous_ofReal.comp ((continuous_phi δ).comp continuous_fst)).mul
      ((continuous_e k).comp continuous_snd)
  have hm : AEStronglyMeasurable (Function.uncurry (Fk δ R k)) (volume.prod volume) := by
    rw [uncurry_Fk]; exact hcont.aestronglyMeasurable.indicator (measurableSet_SR R)
  refine (integrable_prod_iff hm).mpr ⟨Eventually.of_forall fun u => ?_, ?_⟩
  · simp only [Function.uncurry_apply_pair]
    unfold Fk
    exact ((integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
      ((continuous_e k).continuousOn.integrableOn_compact (isCompact_closedBall _ _))).const_mul _
  · have hb : Integrable fun u => Real.pi * (2 * R ^ 2 * phi δ u + 2 * (phi δ u * u ^ 2)) :=
      (((integrable_phi hδ).const_mul _).add ((integrable_phi_mul_sq hδ hδ1).const_mul 2)).const_mul _
    refine hb.mono' hm.norm.integral_prod_right' (Eventually.of_forall fun u => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    refine (integral_norm_Fk hδ k u).trans ?_
    have h2 := phi_nonneg hδ u
    nlinarith [mul_nonneg h2 (sq_nonneg (R - u)), Real.pi_pos]

/-- **The Fourier transform of `W`**: `∫ e(-k·x) W(x) dx = ∫ φ_δ(u) (R+u)² I((R+u)|k|) du` (`R+u > 0`). -/
theorem integral_ek_Wc (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : Fin 2 → ℤ) :
    ∫ x, ek k x * Wc hδ R x = ((∫ u, phi δ u * hatW R k u : ℝ) : ℂ) := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp']
  have h : ∀ y : ℝ², ek k ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm y) *
      Wc hδ R ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm y) = ∫ u, Fk δ R k u y := by
    intro y
    rw [integral_Fk_u hδ]
    have hy : (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm y = WithLp.ofLp y := rfl
    rw [hy, ek_ofLp, Wc_apply, Wr, WithLp.toLp_ofLp]
  simp_rw [h]
  rw [← integral_integral_swap (integrable_Fk hδ hδ1 k)]
  simp_rw [integral_Fk_y]
  exact integral_complex_ofReal

end FT

/-! ### The lattice side and the assembled statement -/

section Assemble

open HardyC1 HardyC3 GaussCircleProblem Filter
open scoped EuclideanGeometry

variable {δ R : ℝ}

/-- `Fin 2 → ℤ ≃ ℤ × ℤ`. -/
abbrev e2 : (Fin 2 → ℤ) ≃ ℤ × ℤ := finTwoArrowEquiv ℤ

theorem vec_e2 (p : ℤ × ℤ) : (!₂[(p.1 : ℝ), (p.2 : ℝ)] : ℝ²) = WithLp.toLp 2 (iv (e2.symm p)) := by
  congr 1; funext i; fin_cases i <;> rfl

theorem norm_kv_e2 (k : ℤ × ℤ) : ‖kv (e2.symm k)‖ = lnorm k := by
  rw [kv, ← vec_e2, lnorm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, sq_abs]

/-- `Ŵ(k)` on `ℤ × ℤ`: `∫ φ_δ(u) (R+u)² I((R+u)‖k‖) du` over `R + u > 0`. -/
def What (δ R : ℝ) (k : ℤ × ℤ) : ℝ :=
  ∫ u, phi δ u * (if 0 < R + u then (R + u) ^ 2 * I ((R + u) * lnorm k) else 0)

theorem What_e2 (k : Fin 2 → ℤ) : What δ R (e2 k) = ∫ u, phi δ u * hatW R k u := by
  have := norm_kv_e2 (e2 k)
  rw [Equiv.symm_apply_apply] at this
  simp only [What, hatW, this]

/-- The finite set counted by FC's `N r`. -/
theorem finite_N_set (r : ℝ) :
    { p : ℤ × ℤ | !₂[(p.1:ℝ), (p.2:ℝ)] ∈ Metric.closedBall (0 : ℝ²) r }.Finite := by
  set K : ℤ := ⌈|r|⌉
  refine (Finset.finite_toSet ((Finset.Icc (-K) K) ×ˢ (Finset.Icc (-K) K))).subset ?_
  rintro ⟨m, n⟩ h
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] at h
  have hsq := HardyC1.norm_vec_sq m n
  have h2 : (m:ℝ)^2 + (n:ℝ)^2 ≤ r^2 := by
    rw [← hsq]; exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hm : |(m:ℝ)| ≤ |r| := by apply sq_le_sq.mp; nlinarith [sq_nonneg (n:ℝ)]
  have hn : |(n:ℝ)| ≤ |r| := by apply sq_le_sq.mp; nlinarith [sq_nonneg (m:ℝ)]
  have hK : |r| ≤ (K:ℝ) := Int.le_ceil _
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  rw [abs_le] at hm hn
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : (-(K:ℝ)) ≤ m := by linarith
    exact_mod_cast this
  · have : (m:ℝ) ≤ K := by linarith
    exact_mod_cast this
  · have : (-(K:ℝ)) ≤ n := by linarith
    exact_mod_cast this
  · have : (n:ℝ) ≤ K := by linarith
    exact_mod_cast this

/-- FC's count as a lattice sum. -/
theorem N_eq_tsum (r : ℝ) :
    (N r : ℝ) = ∑' p : ℤ × ℤ, if ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ ≤ r then (1:ℝ) else 0 := by
  have hfin := finite_N_set r
  rw [N, Set.ncard_eq_toFinset_card _ hfin]
  rw [tsum_eq_sum (s := hfin.toFinset) (fun p hp => by
    rw [Set.Finite.mem_toFinset] at hp
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] at hp
    simp [hp])]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [Set.Finite.mem_toFinset] at hp
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] at hp
    simp [hp] : ∀ p ∈ hfin.toFinset, (if ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ ≤ r then (1:ℝ) else 0) = 1)]
  simp

theorem summable_Wr (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Summable fun n : Fin 2 → ℤ => Wr δ R (iv n) := by
  refine Summable.of_nonneg_of_le (fun n => G_nonneg hδ _) (fun n => ?_) (hnorm_W (R := R) hδ hδ1 Kc)
  have h0 : (0 : Fin 2 → ℝ) ∈ ((Kc (d := Fin 2)) : Set (Fin 2 → ℝ)) := ⟨le_rfl, zero_le_one⟩
  have := ((tr (Wc hδ R) n).restrict _).norm_coe_le_norm
    (⟨0, h0⟩ : ((Kc (d := Fin 2)) : Set (Fin 2 → ℝ)))
  simp only [ContinuousMap.restrict_apply, tr_apply, zero_add, Wc_apply, Complex.norm_real,
    Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- The left side: `∫ φ_δ(u) N(R+u) du = ∑ₙ W(n)`. -/
theorem integral_phi_N (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ u, phi δ u * (N (R + u) : ℝ) = ∑' n : Fin 2 → ℤ, Wr δ R (iv n) := by
  have hS : Summable fun p : ℤ × ℤ => G δ (‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ - R) := by
    rw [← e2.summable_iff]
    refine (summable_Wr (R := R) hδ hδ1).congr fun n => ?_
    simp only [Function.comp_apply, Wr]
    rw [vec_e2, Equiv.symm_apply_apply]
  have hpt : ∀ p : ℤ × ℤ, ∫ u, phi δ u * (if ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ ≤ R + u then (1:ℝ) else 0)
      = G δ (‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ - R) := by
    intro p
    rw [G_eq_indicator]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases h : ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ - R ≤ u
    · rw [if_pos (by linarith), indicator_of_mem (show u ∈ Ici _ from h), mul_one]
    · rw [if_neg (by linarith), indicator_of_notMem (show u ∉ Ici _ from h), mul_zero]
  have hint : ∀ p : ℤ × ℤ, Integrable fun u =>
      phi δ u * (if ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ ≤ R + u then (1:ℝ) else 0) := by
    intro p
    refine (integrable_phi hδ).mono' ?_ (Eventually.of_forall fun u => ?_)
    · have : (fun u => phi δ u * (if ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ ≤ R + u then (1:ℝ) else 0))
          = (Ici (‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ - R)).indicator (phi δ) := by
        funext u
        by_cases h : ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ - R ≤ u
        · rw [if_pos (by linarith), indicator_of_mem (show u ∈ Ici _ from h), mul_one]
        · rw [if_neg (by linarith), indicator_of_notMem (show u ∉ Ici _ from h), mul_zero]
      rw [this]
      exact ((integrable_phi hδ).indicator measurableSet_Ici).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (phi_nonneg hδ u) (by split_ifs <;> norm_num))]
      split_ifs <;> simp [phi_nonneg hδ u]
  calc ∫ u, phi δ u * (N (R + u) : ℝ)
      = ∫ u, ∑' p : ℤ × ℤ, phi δ u * (if ‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ ≤ R + u then (1:ℝ) else 0) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [N_eq_tsum, tsum_mul_left]
    _ = ∑' p : ℤ × ℤ, G δ (‖(!₂[(p.1:ℝ), (p.2:ℝ)] : ℝ²)‖ - R) := by
        rw [← integral_tsum_of_summable_integral_norm hint]
        · exact tsum_congr hpt
        · refine hS.congr fun p => ?_
          rw [← hpt p]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          dsimp only
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (phi_nonneg hδ u) (by split_ifs <;> norm_num))]
    _ = ∑' n : Fin 2 → ℤ, Wr δ R (iv n) := by
        rw [← e2.symm.tsum_eq]
        refine tsum_congr fun p => ?_
        rw [Wr, ← vec_e2]

/-- **Rung C2.** Poisson summation for the radially smoothed lattice count: if the transforms
`Ŵ(k) = ∫ φ_δ(u) (R+u)² I((R+u)‖k‖) du` are summable over `ℤ²` (rung C5 proves this), then
`∫ φ_δ(u) N(R+u) du = ∑_{k ∈ ℤ²} Ŵ(k)`. Here `N` is formal-conjectures' lattice count, `φ_δ` is C1's `phi`,
`I` is C3's disc transform. -/
theorem smoothed_poisson (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : Summable (What δ R)) :
    ∫ u, phi δ u * (N (R + u) : ℝ) = ∑' k : ℤ × ℤ, What δ R k := by
  have hsum : Summable fun k : Fin 2 → ℤ => ∫ x, ek k x * Wc hδ R x := by
    have h' : Summable fun k : Fin 2 → ℤ => What δ R (e2 k) := e2.summable_iff.mpr h
    refine (Complex.ofRealCLM.summable h').congr fun k => ?_
    rw [integral_ek_Wc hδ hδ1, What_e2]; rfl
  have hP := poisson_torus (hnorm_W (R := R) hδ hδ1) hsum
  simp only [integral_ek_Wc hδ hδ1] at hP
  simp only [Wc_apply, ← What_e2] at hP
  have hP' := hP.tsum_eq
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum, Complex.ofReal_inj] at hP'
  rw [integral_phi_N hδ hδ1, ← hP', e2.tsum_eq (What δ R)]

end Assemble

end HardyC2

end

end

-- ===== from HardyOmegaFC.DiscAsymp =====
section

/-!
# Gauss circle problem, rung C4: the asymptotic of the disc transform `I`

`HardyC3.I t = 2 ∫_{-1}^{1} √(1-y²) cos(2πty) dy` (`= J₁(2πt)/t`, numerically only). Main result:

* `abs_I_sub_main_le : ∀ t ≥ 1, |I t - π⁻¹ t^{-3/2} cos(2πt - 3π/4)| ≤ 40 t^{-5/2}`,
  and `I_asymp`, the `∃ C` form asked for in PLAN_C.md.

Route (contour, Watson): `f(z) = √(1-z) √(1+z) e^{-2πitz}` (principal branches, `csq`) is continuous on the closed
rectangle `[-1,1] × [-1,0]` and holomorphic inside, so Cauchy–Goursat moves `∫_{-1}^{1}` onto the two vertical sides
`±1 - i[0,1]` and the bottom side `[-1,1] - i`. On the right side `√(1-z) = √s e^{iπ/4}` and on the left
`√(1+z) = √s e^{-iπ/4}`; replacing `√(2 ∓ is)` by `√2` costs `|√w - √2| ≤ |w-2|/√2 = s/√2`. The bottom side is
`O(e^{-2πt})`. What is left is `∫_0^1 √s e^{-2πts} ds = Γ(3/2)(2πt)^{-3/2} + O(t^{-5/2})` (Mathlib's
`integral_rpow_mul_exp_neg_mul_Ioi`). No limit in the height is taken (height 1 suffices).
-/

open Real MeasureTheory Set intervalIntegral
open scoped FourierTransform

namespace HardyC4

/-! ## The principal square root -/

/-- Principal square root `z ^ (1/2)`. -/
noncomputable def csq (z : ℂ) : ℂ := z ^ (((1:ℝ) / 2 : ℝ) : ℂ)

theorem csq_sq (z : ℂ) : csq z ^ 2 = z := by
  unfold csq
  have : (((1:ℝ) / 2 : ℝ) : ℂ) = ((2:ℕ) : ℂ)⁻¹ := by push_cast; ring
  rw [this]; exact Complex.cpow_nat_inv_pow z two_ne_zero

theorem norm_csq (z : ℂ) : ‖csq z‖ = √‖z‖ := by
  unfold csq; rw [Complex.norm_cpow_real, Real.sqrt_eq_rpow]

theorem re_csq_nonneg (z : ℂ) : 0 ≤ (csq z).re := by
  unfold csq; rw [Complex.cpow_ofReal_re]
  apply mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [Complex.neg_pi_lt_arg z, Complex.arg_le_pi z, Real.pi_pos]

theorem csq_ofReal {x : ℝ} (hx : 0 ≤ x) : csq x = ((√x : ℝ) : ℂ) := by
  unfold csq; rw [← Complex.ofReal_cpow hx, Real.sqrt_eq_rpow]

/-- `|√w - √2| ≤ |w - 2| / √2` (the real part of a principal root is `≥ 0`). -/
theorem norm_csq_sub_le (w : ℂ) : ‖csq w - ((√2 : ℝ) : ℂ)‖ ≤ ‖w - 2‖ / √2 := by
  have h2 : csq w ^ 2 = w := csq_sq w
  have hs2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hfac : w - 2 = (csq w - ((√2 : ℝ) : ℂ)) * (csq w + ((√2 : ℝ) : ℂ)) := by
    linear_combination -h2 + hs2
  have hlow : √2 ≤ ‖csq w + ((√2 : ℝ) : ℂ)‖ := by
    calc √2 ≤ (csq w + ((√2 : ℝ) : ℂ)).re := by
            simp only [Complex.add_re, Complex.ofReal_re]; linarith [re_csq_nonneg w]
      _ ≤ _ := Complex.re_le_norm _
  rw [le_div_iff₀ (by positivity), hfac, norm_mul]
  exact mul_le_mul_of_nonneg_left hlow (norm_nonneg _)

theorem continuousAt_csq {z : ℂ} (hz : 0 ≤ z.re ∨ z.im ≠ 0) : ContinuousAt csq z :=
  Complex.continuousAt_cpow_const_of_re_pos hz (by simp)

theorem differentiableAt_csq {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ csq z :=
  (differentiableAt_id.cpow (differentiableAt_const _) (Or.inl hz) :)

/-- `√(s i) = √s e^{iπ/4}` for `s ≥ 0`. -/
theorem csq_mul_I {s : ℝ} (hs : 0 ≤ s) :
    csq (s * Complex.I) = ((√s : ℝ) : ℂ) * Complex.exp (π / 4 * Complex.I) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [csq]
  unfold csq
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hs.ne') Complex.I_ne_zero),
    Complex.log_ofReal_mul hs Complex.I_ne_zero, Complex.log_I, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hs, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `√(-s i) = √s e^{-iπ/4}` for `s ≥ 0`. -/
theorem csq_mul_neg_I {s : ℝ} (hs : 0 ≤ s) :
    csq (s * -Complex.I) = ((√s : ℝ) : ℂ) * Complex.exp (-(π / 4) * Complex.I) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [csq]
  unfold csq
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hs.ne') (neg_ne_zero.2 Complex.I_ne_zero)),
    Complex.log_ofReal_mul hs (neg_ne_zero.2 Complex.I_ne_zero), Complex.log_neg_I, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hs, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## The contour shift -/

/-- `f(z) = √(1-z) √(1+z) e^{-2πitz}`. -/
noncomputable def F (t : ℝ) (z : ℂ) : ℂ :=
  csq (1 - z) * csq (1 + z) * Complex.exp (-(2 * π * t * Complex.I) * z)

theorem F_continuousAt (t : ℝ) {z : ℂ} (h1 : 0 ≤ (1 - z).re ∨ (1 - z).im ≠ 0)
    (h2 : 0 ≤ (1 + z).re ∨ (1 + z).im ≠ 0) : ContinuousAt (F t) z := by
  unfold F
  refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (by fun_prop)
  · exact (continuousAt_csq h1).comp (by fun_prop : ContinuousAt (fun z : ℂ => 1 - z) z)
  · exact (continuousAt_csq h2).comp (by fun_prop : ContinuousAt (fun z : ℂ => 1 + z) z)

theorem F_differentiableAt (t : ℝ) {z : ℂ} (h1 : 0 < (1 - z).re) (h2 : 0 < (1 + z).re) :
    DifferentiableAt ℂ (F t) z := by
  unfold F
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) (by fun_prop)
  · exact (differentiableAt_csq h1).comp z (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 - z) z)
  · exact (differentiableAt_csq h2).comp z (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 + z) z)

/-- Cauchy–Goursat on `[-1,1] × [-1,0]`, with the vertical sides written as `±1 - is`, `s ∈ [0,1]`. -/
theorem contour (t : ℝ) :
    ∫ x in (-1:ℝ)..1, F t x = (∫ x in (-1:ℝ)..1, F t (x - Complex.I))
      + Complex.I * (∫ s in (0:ℝ)..1, F t (1 - s * Complex.I))
      - Complex.I * (∫ s in (0:ℝ)..1, F t (-1 - s * Complex.I)) := by
  have H := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (F t)
    (-1 : ℂ) (1 - Complex.I) ?_ ?_
  · simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
      Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im, zero_sub,
      Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul] at H
    have hR : ∫ s in (0:ℝ)..1, F t (1 - s * Complex.I)
        = -∫ y in (0:ℝ)..(-1), F t (((1:ℝ):ℂ) + y * Complex.I) := by
      rw [integral_symm (f := fun y : ℝ => F t (((1:ℝ):ℂ) + y * Complex.I)) (-1:ℝ) 0, neg_neg]
      have := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1)
        (fun y : ℝ => F t (((1:ℝ):ℂ) + y * Complex.I))
      simp only [neg_zero] at this
      rw [← this]
      refine integral_congr fun s _ => ?_
      show F t _ = F t _; congr 1; push_cast; ring
    have hL : ∫ s in (0:ℝ)..1, F t (-1 - s * Complex.I)
        = -∫ y in (0:ℝ)..(-1), F t (((-1:ℝ):ℂ) + y * Complex.I) := by
      rw [integral_symm (f := fun y : ℝ => F t (((-1:ℝ):ℂ) + y * Complex.I)) (-1:ℝ) 0, neg_neg]
      have := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1)
        (fun y : ℝ => F t (((-1:ℝ):ℂ) + y * Complex.I))
      simp only [neg_zero] at this
      rw [← this]
      refine integral_congr fun s _ => ?_
      show F t _ = F t _; congr 1; push_cast; ring
    have hB : ∫ x in (-1:ℝ)..1, F t (x - Complex.I) = ∫ x in (-1:ℝ)..1, F t (x + (-1:ℝ) * Complex.I) := by
      refine integral_congr fun s _ => ?_
      show F t _ = F t _; congr 1; push_cast; ring
    rw [hR, hL, hB]
    push_cast at H ⊢
    linear_combination H
  · intro z hz
    rw [Complex.mem_reProdIm] at hz
    simp only [Complex.neg_re, Complex.one_re, Complex.sub_re, Complex.I_re, sub_zero,
      Complex.neg_im, Complex.one_im, neg_zero, Complex.sub_im, Complex.I_im, zero_sub] at hz
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_ge (by norm_num)] at hz
    refine (F_continuousAt t ?_ ?_).continuousWithinAt
    · left; simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1.2]
    · left; simp only [Complex.add_re, Complex.one_re]; linarith [hz.1.1]
  · intro z hz
    rw [Complex.mem_reProdIm] at hz
    simp only [Complex.neg_re, Complex.one_re, Complex.sub_re, Complex.I_re, sub_zero,
      Complex.neg_im, Complex.one_im, neg_zero, Complex.sub_im, Complex.I_im, zero_sub] at hz
    norm_num at hz
    refine (F_differentiableAt t ?_ ?_).differentiableWithinAt
    · simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1.2]
    · simp only [Complex.add_re, Complex.one_re]; linarith [hz.1.1]

/-- On the real segment, `f` is the integrand of C3's `integral_sqrt_mul_exp`. -/
theorem integral_F_real (t : ℝ) : ∫ x in (-1:ℝ)..1, F t x = ((HardyC3.I t / 2 : ℝ) : ℂ) := by
  rw [← HardyC3.integral_sqrt_mul_exp]
  refine integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by norm_num)] at hx
  simp only [F]
  rw [show (1:ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    show (1:ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring,
    csq_ofReal (by linarith [hx.2]), csq_ofReal (by linarith [hx.1]),
    ← Complex.ofReal_mul, ← Real.sqrt_mul (by linarith [hx.2]), Real.fourierChar_apply]
  congr 2
  · ring_nf
  · push_cast; ring

/-! ## Laplace integrals on `[0,1]` -/

theorem rpow_three_half {s : ℝ} (hs : 0 < s) : s ^ ((5:ℝ) / 2 - 1) = s * √s := by
  rw [show (5:ℝ) / 2 - 1 = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one, Real.sqrt_eq_rpow]

theorem rpow_one_half {s : ℝ} (_hs : 0 < s) : s ^ ((3:ℝ) / 2 - 1) = √s := by
  rw [show (3:ℝ) / 2 - 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]

theorem integrableOn_laplace {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s ^ (b - 1) * rexp (-(a * s))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := b - 1) (p := 1) (b := a) (by linarith) one_pos ha
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

theorem integrableOn_s32 {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s * √s * rexp (-(a * s))) (Ioi 0) :=
  (integrableOn_laplace (b := 5 / 2) (by norm_num) ha).congr_fun
    (fun s hs => by beta_reduce; rw [rpow_three_half hs]) measurableSet_Ioi

theorem integrableOn_s12 {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => √s * rexp (-(a * s))) (Ioi 0) :=
  (integrableOn_laplace (b := 3 / 2) (by norm_num) ha).congr_fun
    (fun s hs => by beta_reduce; rw [rpow_one_half hs]) measurableSet_Ioi

theorem integral_Ioi_s32 {a : ℝ} (ha : 0 < a) :
    ∫ s in Ioi 0, s * √s * rexp (-(a * s)) = (1 / a) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) := by
  rw [← integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) ha]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [rpow_three_half hs]

theorem integral_Ioi_s12 {a : ℝ} (ha : 0 < a) :
    ∫ s in Ioi 0, √s * rexp (-(a * s)) = (1 / a) ^ ((3:ℝ) / 2) * Real.Gamma (3 / 2) := by
  rw [← integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) ha]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [rpow_one_half hs]

/-- `∫_0^1 s^{3/2} e^{-as} ds ≤ Γ(5/2) a^{-5/2}`. -/
theorem laplace32_le {a : ℝ} (ha : 0 < a) :
    ∫ s in (0:ℝ)..1, s * √s * rexp (-(a * s)) ≤ (1 / a) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) := by
  rw [integral_of_le zero_le_one, ← integral_Ioi_s32 ha]
  refine setIntegral_mono_set (integrableOn_s32 ha) ?_ (Ioc_subset_Ioi_self.eventuallyLE)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have : (0:ℝ) < s := hs
  positivity

/-- `|∫_0^1 s^{1/2} e^{-as} ds - Γ(3/2) a^{-3/2}| ≤ Γ(5/2) a^{-5/2}`. -/
theorem laplace12_sub {a : ℝ} (ha : 0 < a) :
    |(∫ s in (0:ℝ)..1, √s * rexp (-(a * s))) - (1 / a) ^ ((3:ℝ) / 2) * Real.Gamma (3 / 2)|
      ≤ (1 / a) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) := by
  have hsplit : ∫ s in Ioi 0, √s * rexp (-(a * s))
      = (∫ s in Ioc 0 1, √s * rexp (-(a * s))) + ∫ s in Ioi 1, √s * rexp (-(a * s)) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((integrableOn_s12 ha).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_s12 ha).mono_set (Ioi_subset_Ioi zero_le_one)), Ioc_union_Ioi_eq_Ioi zero_le_one]
  have htail_nn : 0 ≤ ∫ s in Ioi 1, √s * rexp (-(a * s)) :=
    setIntegral_nonneg measurableSet_Ioi fun s _ => by positivity
  have htail_le : ∫ s in Ioi 1, √s * rexp (-(a * s)) ≤ (1 / a) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) := by
    rw [← integral_Ioi_s32 ha]
    calc ∫ s in Ioi 1, √s * rexp (-(a * s)) ≤ ∫ s in Ioi 1, s * √s * rexp (-(a * s)) := by
          refine setIntegral_mono_on ((integrableOn_s12 ha).mono_set (Ioi_subset_Ioi zero_le_one))
            ((integrableOn_s32 ha).mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi fun s hs => ?_
          have h1 : (1:ℝ) < s := hs
          have := Real.sqrt_nonneg s
          have := Real.exp_pos (-(a * s))
          nlinarith [mul_nonneg this.le (Real.sqrt_nonneg s)]
      _ ≤ ∫ s in Ioi 0, s * √s * rexp (-(a * s)) := by
          refine setIntegral_mono_set (integrableOn_s32 ha) ?_
            ((Ioi_subset_Ioi zero_le_one).eventuallyLE)
          refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
          have : (0:ℝ) < s := hs
          positivity
  rw [integral_of_le zero_le_one, ← integral_Ioi_s12 ha, hsplit, abs_le]
  constructor <;> linarith

/-! ## The three sides -/

/-- `e^{iπ/4}`, `e^{-iπ/4}`, `e^{-2πit}`, `e^{2πit}`. -/
noncomputable def ωp : ℂ := Complex.exp ((π / 4 : ℝ) * Complex.I)
noncomputable def ωm : ℂ := Complex.exp ((-(π / 4) : ℝ) * Complex.I)
noncomputable def cp (t : ℝ) : ℂ := Complex.exp ((-(2 * π * t) : ℝ) * Complex.I)
noncomputable def cm (t : ℝ) : ℂ := Complex.exp ((2 * π * t : ℝ) * Complex.I)

/-- The Laplace integral left after the contour shift. -/
noncomputable def A (t : ℝ) : ℝ := ∫ s in (0:ℝ)..1, √s * rexp (-(2 * π * t * s))

theorem norm_ωp : ‖ωp‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem norm_ωm : ‖ωm‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem norm_cp (t : ℝ) : ‖cp t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem norm_cm (t : ℝ) : ‖cm t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem F_right (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    F t (1 - s * Complex.I)
      = (((√s : ℝ) : ℂ) * ωp * cp t * ((rexp (-(2 * π * t * s)) : ℝ) : ℂ)) * csq (2 - s * Complex.I) := by
  unfold F ωp cp
  rw [show (1:ℂ) - (1 - s * Complex.I) = s * Complex.I by ring, csq_mul_I hs,
    show (1:ℂ) + (1 - s * Complex.I) = 2 - s * Complex.I by ring, Complex.ofReal_exp]
  have : Complex.exp (-(2 * π * t * Complex.I) * (1 - s * Complex.I))
      = Complex.exp ((-(2 * π * t) : ℝ) * Complex.I) * Complex.exp ((-(2 * π * t * s) : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; linear_combination (2 * π * t * s) * Complex.I_sq
  rw [this]; push_cast; ring

theorem F_left (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    F t (-1 - s * Complex.I)
      = (((√s : ℝ) : ℂ) * ωm * cm t * ((rexp (-(2 * π * t * s)) : ℝ) : ℂ)) * csq (2 + s * Complex.I) := by
  unfold F ωm cm
  rw [show (1:ℂ) - (-1 - s * Complex.I) = 2 + s * Complex.I by ring,
    show (1:ℂ) + (-1 - s * Complex.I) = s * -Complex.I by ring, csq_mul_neg_I hs, Complex.ofReal_exp]
  have : Complex.exp (-(2 * π * t * Complex.I) * (-1 - s * Complex.I))
      = Complex.exp ((2 * π * t : ℝ) * Complex.I) * Complex.exp ((-(2 * π * t * s) : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; linear_combination (2 * π * t * s) * Complex.I_sq
  rw [this]; push_cast; ring

theorem side_bound {s : ℝ} (hs : 0 ≤ s) (ω c : ℂ) (hω : ‖ω‖ = 1) (hc : ‖c‖ = 1) (e : ℝ) (he : 0 ≤ e) (w : ℂ)
    (hw : ‖w - 2‖ = s) :
    ‖(((√s : ℝ) : ℂ) * ω * c * (e : ℂ)) * csq w - (((√2 : ℝ) : ℂ) * ω * c) * ((√s * e : ℝ) : ℂ)‖
      ≤ s * √s * e := by
  have : (((√s : ℝ) : ℂ) * ω * c * (e : ℂ)) * csq w - (((√2 : ℝ) : ℂ) * ω * c) * ((√s * e : ℝ) : ℂ)
      = (((√s : ℝ) : ℂ) * ω * c * (e : ℂ)) * (csq w - ((√2 : ℝ) : ℂ)) := by push_cast; ring
  rw [this, norm_mul, norm_mul, norm_mul, norm_mul, hω, hc, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg he]
  have h1 := norm_csq_sub_le w
  rw [hw] at h1
  have h2 : s / √2 ≤ s := div_le_self hs (Real.one_le_sqrt.2 (by norm_num))
  have h3 : 0 ≤ √s * e := mul_nonneg (Real.sqrt_nonneg _) he
  calc √s * 1 * 1 * e * ‖csq w - ((√2 : ℝ) : ℂ)‖ = (√s * e) * ‖csq w - ((√2 : ℝ) : ℂ)‖ := by ring
    _ ≤ (√s * e) * s := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = s * √s * e := by ring

theorem continuous_right (t : ℝ) : Continuous fun s : ℝ => F t (1 - s * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  refine ContinuousAt.comp (g := F t) (F_continuousAt t ?_ ?_) (by fun_prop)
  · left; simp
  · left; simp

theorem continuous_left (t : ℝ) : Continuous fun s : ℝ => F t (-1 - s * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  refine ContinuousAt.comp (g := F t) (F_continuousAt t ?_ ?_) (by fun_prop)
  · left; simp
  · left; simp

/-- One vertical side: `|∫_0^1 f(±1 - is) ds - √2 ω c A(t)| ≤ Γ(5/2)(2πt)^{-5/2}`. -/
theorem vertical_bound {t : ℝ} (ht : 0 < t) (g : ℝ → ℂ) (hg : Continuous g) (ω c : ℂ) (hω : ‖ω‖ = 1)
    (hc : ‖c‖ = 1) (w : ℝ → ℂ) (hw : ∀ s, 0 ≤ s → ‖w s - 2‖ = s)
    (hgs : ∀ s, 0 ≤ s → g s = (((√s : ℝ) : ℂ) * ω * c * ((rexp (-(2 * π * t * s)) : ℝ) : ℂ)) * csq (w s)) :
    ‖(∫ s in (0:ℝ)..1, g s) - (((√2 : ℝ) : ℂ) * ω * c) * (A t : ℂ)‖
      ≤ (1 / (2 * π * t)) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) := by
  have ha : 0 < 2 * π * t := by positivity
  have hA : (((√2 : ℝ) : ℂ) * ω * c) * (A t : ℂ)
      = ∫ s in (0:ℝ)..1, (((√2 : ℝ) : ℂ) * ω * c) * ((√s * rexp (-(2 * π * t * s)) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, A]
  rw [hA, ← intervalIntegral.integral_sub (hg.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_
    (Continuous.intervalIntegrable (by fun_prop) _ _)).trans (laplace32_le ha)
  refine Filter.Eventually.of_forall fun s hs => ?_
  have hs0 : 0 ≤ s := hs.1.le
  rw [hgs s hs0]
  exact side_bound hs0 ω c hω hc _ (Real.exp_pos _).le (w s) (hw s hs0)

theorem right_bound {t : ℝ} (ht : 0 < t) :
    ‖(∫ s in (0:ℝ)..1, F t (1 - s * Complex.I)) - (((√2 : ℝ) : ℂ) * ωp * cp t) * (A t : ℂ)‖
      ≤ (1 / (2 * π * t)) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) :=
  vertical_bound ht _ (continuous_right t) ωp (cp t) norm_ωp (norm_cp t) (fun s => 2 - s * Complex.I)
    (fun s hs => by simp [abs_of_nonneg hs]) (fun s hs => F_right t hs)

theorem left_bound {t : ℝ} (ht : 0 < t) :
    ‖(∫ s in (0:ℝ)..1, F t (-1 - s * Complex.I)) - (((√2 : ℝ) : ℂ) * ωm * cm t) * (A t : ℂ)‖
      ≤ (1 / (2 * π * t)) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2) :=
  vertical_bound ht _ (continuous_left t) ωm (cm t) norm_ωm (norm_cm t) (fun s => 2 + s * Complex.I)
    (fun s hs => by simp [abs_of_nonneg hs]) (fun s hs => F_left t hs)

/-- The bottom side `[-1,1] - i` is `O(e^{-2πt})`. -/
theorem bottom_bound (t : ℝ) :
    ‖∫ x in (-1:ℝ)..1, F t (x - Complex.I)‖ ≤ 8 * rexp (-(2 * π * t)) := by
  have hsq : ∀ w : ℂ, ‖w‖ ≤ 3 → ‖csq w‖ ≤ 2 := by
    intro w hw
    rw [norm_csq, Real.sqrt_le_iff]; constructor <;> norm_num; linarith
  have hpt : ∀ x ∈ Ioc (-1:ℝ) 1, ‖F t (x - Complex.I)‖ ≤ 4 * rexp (-(2 * π * t)) := by
    intro x hx
    have h1 : ‖csq (1 - (x - Complex.I))‖ ≤ 2 := by
      refine hsq _ ?_
      rw [show (1:ℂ) - (x - Complex.I) = ((1 - x : ℝ) : ℂ) + Complex.I by push_cast; ring]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.2])]
      linarith [hx.1]
    have h2 : ‖csq (1 + (x - Complex.I))‖ ≤ 2 := by
      refine hsq _ ?_
      rw [show (1:ℂ) + (x - Complex.I) = ((1 + x : ℝ) : ℂ) - Complex.I by push_cast; ring]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    have h3 : ‖Complex.exp (-(2 * π * t * Complex.I) * (x - Complex.I))‖ = rexp (-(2 * π * t)) := by
      rw [Complex.norm_exp]; congr 1; simp
    unfold F
    rw [norm_mul, norm_mul, h3]
    have := Real.exp_pos (-(2 * π * t))
    calc ‖csq (1 - (↑x - Complex.I))‖ * ‖csq (1 + (↑x - Complex.I))‖ * rexp (-(2 * π * t))
        ≤ 2 * 2 * rexp (-(2 * π * t)) := by gcongr
      _ = 4 * rexp (-(2 * π * t)) := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Filter.Eventually.of_forall hpt) intervalIntegrable_const).trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul]; linarith

/-! ## Assembly -/

/-- `Γ(5/2) (2πt)^{-5/2}`, the unit of the remainder. -/
noncomputable def G5 (t : ℝ) : ℝ := (1 / (2 * π * t)) ^ ((5:ℝ) / 2) * Real.Gamma (5 / 2)

/-- The complex main term is real: `i√2 A (e^{-iθ} - e^{iθ}) = 2√2 A sin θ`, `θ = 2πt - π/4`. -/
theorem main_complex (t : ℝ) :
    Complex.I * ((((√2 : ℝ) : ℂ) * ωp * cp t) * (A t : ℂ))
      - Complex.I * ((((√2 : ℝ) : ℂ) * ωm * cm t) * (A t : ℂ))
      = ((2 * √2 * A t * Real.sin (2 * π * t - π / 4) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * π * t - π / 4 with hθ
  have hp : ωp * cp t = Complex.exp (-(θ : ℂ) * Complex.I) := by
    unfold ωp cp; rw [← Complex.exp_add]; congr 1; rw [hθ]; push_cast; ring
  have hm : ωm * cm t = Complex.exp ((θ : ℂ) * Complex.I) := by
    unfold ωm cm; rw [← Complex.exp_add]; congr 1; rw [hθ]; push_cast; ring
  have key : Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)
      = -2 * Complex.I * Complex.sin θ := by
    rw [Complex.sin]
    linear_combination (Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)) * Complex.I_sq
  have : Complex.I * ((((√2 : ℝ) : ℂ) * ωp * cp t) * (A t : ℂ))
      - Complex.I * ((((√2 : ℝ) : ℂ) * ωm * cm t) * (A t : ℂ))
      = Complex.I * ((√2 : ℝ) : ℂ) * (A t : ℂ) * (ωp * cp t - ωm * cm t) := by ring
  rw [this, hp, hm, key, ← Complex.ofReal_sin]; push_cast
  linear_combination (-2 * ((√2 : ℝ) : ℂ) * (A t : ℂ) * (Complex.sin θ)) * Complex.I_sq

/-- `|I(t)/2 - 2√2 A(t) sin(2πt - π/4)| ≤ 8 e^{-2πt} + 2 Γ(5/2)(2πt)^{-5/2}`. -/
theorem half_bound {t : ℝ} (ht : 0 < t) :
    |HardyC3.I t / 2 - 2 * √2 * A t * Real.sin (2 * π * t - π / 4)| ≤ 8 * rexp (-(2 * π * t)) + 2 * G5 t := by
  have hJ := contour t
  rw [integral_F_real] at hJ
  have hdiff : ((HardyC3.I t / 2 - 2 * √2 * A t * Real.sin (2 * π * t - π / 4) : ℝ) : ℂ)
      = (∫ x in (-1:ℝ)..1, F t (x - Complex.I))
        + Complex.I * ((∫ s in (0:ℝ)..1, F t (1 - s * Complex.I)) - (((√2 : ℝ) : ℂ) * ωp * cp t) * (A t : ℂ))
        - Complex.I * ((∫ s in (0:ℝ)..1, F t (-1 - s * Complex.I)) - (((√2 : ℝ) : ℂ) * ωm * cm t) * (A t : ℂ)) := by
    rw [Complex.ofReal_sub, hJ, ← main_complex]; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff]
  set X := ∫ x in (-1:ℝ)..1, F t (x - Complex.I)
  set Y := (∫ s in (0:ℝ)..1, F t (1 - s * Complex.I)) - (((√2 : ℝ) : ℂ) * ωp * cp t) * (A t : ℂ)
  set Z := (∫ s in (0:ℝ)..1, F t (-1 - s * Complex.I)) - (((√2 : ℝ) : ℂ) * ωm * cm t) * (A t : ℂ)
  have n1 := norm_sub_le (X + Complex.I * Y) (Complex.I * Z)
  have n2 := norm_add_le X (Complex.I * Y)
  rw [norm_mul, Complex.norm_I, one_mul] at n1 n2
  have h1 := bottom_bound t
  have h2 := right_bound ht
  have h3 := left_bound ht
  unfold G5; linarith

theorem Gamma_three_half : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3:ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring

theorem Gamma_five_half_le : Real.Gamma (5 / 2) ≤ 3 / 2 := by
  rw [show (5:ℝ) / 2 = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Gamma_three_half]
  have : √π ≤ 2 := by
    rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt Real.pi_le_four
  linarith

theorem rpow_neg_three_half {t : ℝ} (ht : 0 < t) : t ^ (-(3:ℝ) / 2) = (t * √t)⁻¹ := by
  rw [show -(3:ℝ) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg ht.le, Real.rpow_add ht, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The main term: `4√2 Γ(3/2) (2πt)^{-3/2} sin(2πt - π/4) = π⁻¹ t^{-3/2} cos(2πt - 3π/4)`. -/
theorem main_real {t : ℝ} (ht : 0 < t) :
    4 * √2 * ((1 / (2 * π * t)) ^ ((3:ℝ) / 2) * Real.Gamma (3 / 2)) * Real.sin (2 * π * t - π / 4)
      = π⁻¹ * t ^ (-(3:ℝ) / 2) * Real.cos (2 * π * t - 3 * π / 4) := by
  have ha : 0 < 2 * π * t := by positivity
  rw [show 2 * π * t - 3 * π / 4 = (2 * π * t - π / 4) - π / 2 by ring, Real.cos_sub_pi_div_two,
    rpow_neg_three_half ht, Gamma_three_half,
    show (3:ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow,
    Real.sqrt_div' _ ha.le, Real.sqrt_one, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have h2 : 0 < √2 := by positivity
  have hp : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have htt : 0 < √t := Real.sqrt_pos.2 ht
  field_simp
  ring

theorem exp_le_rpow {t : ℝ} (ht : 1 ≤ t) : rexp (-(2 * π * t)) ≤ t ^ (-(5:ℝ) / 2) := by
  have ht0 : 0 < t := by linarith
  rw [Real.exp_neg, show -(5:ℝ) / 2 = -(5 / 2) by ring, Real.rpow_neg ht0.le]
  refine inv_anti₀ (by positivity) ?_
  have h1 : t ^ ((5:ℝ) / 2) ≤ t ^ (3:ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have h2 : (2 * π * t) ^ 3 / Nat.factorial 3 ≤ rexp (2 * π * t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) 3
  rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast] at h1
  have h3 : t ^ 3 ≤ (2 * π * t) ^ 3 / Nat.factorial 3 := by
    rw [mul_pow, mul_pow]; norm_num [Nat.factorial]
    have : (4:ℝ) ^ 3 ≤ (2 * π) ^ 3 := by
      gcongr; linarith [Real.two_le_pi]
    nlinarith [pow_pos ht0 3]
  linarith

theorem G5_le {t : ℝ} (ht : 1 ≤ t) : G5 t ≤ 3 / 2 * t ^ (-(5:ℝ) / 2) := by
  have ht0 : 0 < t := by linarith
  unfold G5
  have h1 : (1 / (2 * π * t)) ^ ((5:ℝ) / 2) ≤ t ^ (-(5:ℝ) / 2) := by
    rw [show -(5:ℝ) / 2 = -(5 / 2) by ring, Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [one_div]; refine inv_anti₀ ht0 ?_
    nlinarith [Real.two_le_pi]
  have h2 := Gamma_five_half_le
  have h3 : 0 ≤ (1 / (2 * π * t)) ^ ((5:ℝ) / 2) := by positivity
  have h4 : 0 ≤ Real.Gamma (5 / 2) := (Real.Gamma_pos_of_pos (by norm_num)).le
  have h5 : 0 ≤ t ^ (-(5:ℝ) / 2) := by positivity
  nlinarith

/-- **Rung C4.** `|I t - π⁻¹ t^{-3/2} cos(2πt - 3π/4)| ≤ 40 t^{-5/2}` for `t ≥ 1`. -/
theorem abs_I_sub_main_le {t : ℝ} (ht : 1 ≤ t) :
    |HardyC3.I t - π⁻¹ * t ^ (-(3:ℝ) / 2) * Real.cos (2 * π * t - 3 * π / 4)| ≤ 40 * t ^ (-(5:ℝ) / 2) := by
  have ht0 : 0 < t := by linarith
  have hh := half_bound ht0
  have hA := laplace12_sub (a := 2 * π * t) (by positivity)
  rw [← A] at hA
  have hm := main_real ht0
  set S := Real.sin (2 * π * t - π / 4)
  set G3 := (1 / (2 * π * t)) ^ ((3:ℝ) / 2) * Real.Gamma (3 / 2)
  have hS : |S| ≤ 1 := Real.abs_sin_le_one _
  have hdecomp : HardyC3.I t - π⁻¹ * t ^ (-(3:ℝ) / 2) * Real.cos (2 * π * t - 3 * π / 4)
      = 2 * (HardyC3.I t / 2 - 2 * √2 * A t * S) + 4 * √2 * S * (A t - G3) := by
    rw [← hm]; ring
  have hG5 : G5 t ≤ 3 / 2 * t ^ (-(5:ℝ) / 2) := G5_le ht
  have he := exp_le_rpow ht
  have hs2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hAG : |A t - G3| ≤ G5 t := hA
  have hprod : |4 * √2 * S * (A t - G3)| ≤ 4 * √2 * G5 t := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * √2)]
    have : |S| * |A t - G3| ≤ 1 * G5 t :=
      mul_le_mul hS hAG (abs_nonneg _) zero_le_one
    nlinarith [Real.sqrt_nonneg 2]
  rw [hdecomp]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_two]
  have h0 : 0 ≤ G5 t := by unfold G5; positivity
  nlinarith [Real.sqrt_nonneg 2]

end HardyC4

end

-- ===== from HardyOmegaFC.CircleVoronoi =====
section

/-!
# Gauss circle problem, rung C5: the smoothed Voronoi expansion

`smoothedVoronoiC : HardyC1.SmoothedVoronoiC`, no hypothesis. With `f(ρ) = φ_δ(ρ - R)` and `l = ‖k‖`:

* **C5a** `integral_phi_cos`: `∫ φ_δ(u) cos(a u + b) du = e^{-δ²a²/(4π)} cos b` (Mathlib `integral_cexp_quadratic`).
* **C5b** `abs_What_sub_le`: for `k ≠ 0`, `R ≥ 2`, `0 < δ ≤ 1`,
  `|Ŵ(k) - (√R/π) w(k)| ≤ 130 l^{-5/2}`. Write `ρ² I(ρl) = res + π⁻¹ l^{-3/2} √ρ cos(2πlρ - 3π/4)` for `ρ > 0`;
  `|res| ≤ 5 l^{-2}` on `(0, 1/l]` and `≤ 40 l^{-5/2} ρ^{-1/2}` beyond (C4), and `∫ f ρ^{-1/2} ≤ 3`
  (`phi_sqrt_inv`). The rest is `π⁻¹ l^{-3/2} ∫ f (√ρ - √R) cos(…)` plus `π⁻¹ l^{-3/2} √R ∫ f cos(…)`; the second is the
  main term exactly (C5a), the first is `O(1/l)` by one integration by parts (`abs_integral_mul_cos_le`, which allows
  the kink of `√ρ` at `0`), using `|√ρ - √R| ≤ |ρ - R|` and `∫ φ_δ u² = δ²/(2π)`.
* **C5c** `What_zero_sub` (`k = 0`: the area, up to a Gaussian tail `≤ 4`), `summable_q5`
  (`∑ ‖k‖^{-5/2} < ∞` via Mathlib's Eisenstein-series lattice sum), `summable_w_all`, `integrable_phi_N`,
  and the assembly with C2's `smoothed_poisson`. Constant `C = 4 + 130 ∑ ‖k‖^{-5/2}`, `R₀ = 2`.
-/

open MeasureTheory Real Set Filter Topology GaussCircleProblem
open HardyC1

noncomputable section

namespace HardyC5

section Gauss

open Complex

theorem phi_cos_eq (δ a b u : ℝ) :
    phi δ u * Real.cos (a * u + b) =
      ((δ⁻¹ : ℝ) * cexp (((-(π / δ ^ 2) : ℝ) : ℂ) * (u:ℂ) ^ 2 + (a * I) * u + b * I)).re := by
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  have h1 : (((-(π / δ ^ 2) : ℝ) : ℂ) * (u:ℂ) ^ 2 + (a * I) * u + b * I).re = -π * u ^ 2 / δ ^ 2 := by
    simp only [Complex.add_re, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have h2 : (((-(π / δ ^ 2) : ℝ) : ℂ) * (u:ℂ) ^ 2 + (a * I) * u + b * I).im = a * u + b := by
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  rw [h1, h2, phi]; ring

/-- **C5a.** The Gaussian average of a cosine: `∫ φ_δ(u) cos(a u + b) du = e^{-δ²a²/(4π)} cos b`. -/
theorem integral_phi_cos {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    ∫ u, phi δ u * Real.cos (a * u + b) = Real.exp (-(δ ^ 2 * a ^ 2) / (4 * π)) * Real.cos b := by
  have hb : (((-(π / δ ^ 2) : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]; have : 0 < π / δ ^ 2 := by positivity
    linarith
  have hint := (integrable_cexp_quadratic' hb (a * I) (b * I)).const_mul ((δ⁻¹ : ℝ) : ℂ)
  simp_rw [phi_cos_eq]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre, integral_const_mul, integral_cexp_quadratic hb]
  have hδ2 : π / -(((-(π / δ ^ 2) : ℝ) : ℂ)) = ((δ ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  have hsq : ((δ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (δ : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hδ.le]
  have hexp : b * I - (a * I) ^ 2 / (4 * (((-(π / δ ^ 2) : ℝ) : ℂ))) =
      ((-(δ ^ 2 * a ^ 2) / (4 * π) : ℝ) : ℂ) + b * I := by
    push_cast
    have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    have : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
    field_simp
    ring_nf; rw [Complex.I_sq]; ring
  rw [hδ2, hsq, hexp, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hδ.ne', Complex.ofReal_one, one_mul,
    Complex.exp_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simp

end Gauss

/-- One integration by parts against `cos`, allowing one non-differentiable point (`0`). -/
theorem abs_integral_mul_cos_le {F F' : ℝ → ℝ} (hc : Continuous F) (hd : ∀ x ≠ 0, HasDerivAt F (F' x) x)
    (hF : Integrable F) (hF' : Integrable F') {l : ℝ} (hl : 0 < l) (c : ℝ) :
    |∫ x, F x * Real.cos (2 * π * l * x + c)| ≤ (∫ x, |F' x|) / (2 * π * l) := by
  set ω := 2 * π * l with hω
  have hω0 : 0 < ω := by positivity
  set G : ℝ → ℝ := fun x => F x * Real.sin (ω * x + c)
  set G' : ℝ → ℝ := fun x => F' x * Real.sin (ω * x + c) + F x * (Real.cos (ω * x + c) * ω)
  have hG : ∀ x ≠ 0, HasDerivAt G (G' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => ω * x + c) ω x := by
      simpa using ((hasDerivAt_id x).const_mul ω).add_const c
    exact (hd x hx).mul h1.sin
  have hGc : Continuous G := hc.mul (by fun_prop)
  have hmeas_s : Continuous fun x => Real.sin (ω * x + c) := by fun_prop
  have hmeas_c : Continuous fun x => Real.cos (ω * x + c) := by fun_prop
  have iFs : Integrable fun x => F' x * Real.sin (ω * x + c) :=
    hF'.norm.mono' (hF'.aestronglyMeasurable.mul hmeas_s.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_sin_le_one _))
  have iFc : Integrable fun x => F x * Real.cos (ω * x + c) :=
    hF.norm.mono' (hF.aestronglyMeasurable.mul hmeas_c.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_cos_le_one _))
  have iG : Integrable G :=
    hF.norm.mono' (hF.aestronglyMeasurable.mul hmeas_s.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        simp only [G]
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_sin_le_one _))
  have iG' : Integrable G' := by
    have : Integrable fun x => F x * Real.cos (ω * x + c) * ω := iFc.mul_const ω
    refine (iFs.add this).congr (Eventually.of_forall fun x => ?_)
    simp only [G', Pi.add_apply]; ring
  have hIoi : ∫ x in Ioi (0:ℝ), G' x = 0 - G 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto hGc.continuousWithinAt
      (fun x hx => hG x (ne_of_gt hx)) iG'.integrableOn
      (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun x hx => hG x (ne_of_gt hx))
        iG'.integrableOn iG.integrableOn)
  have hIic : ∫ x in Iic (0:ℝ), G' x = G 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto hGc.continuousWithinAt
      (fun x hx => hG x (ne_of_lt hx)) iG'.integrableOn
      (tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := -1)
        (fun x hx => hG x (by have : x ≤ -1 := hx; linarith)) iG'.integrableOn iG.integrableOn)
  have h0 : ∫ x, G' x = 0 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi iG'.integrableOn iG'.integrableOn, hIoi, hIic]; ring
  have hsplit : ∫ x, G' x = (∫ x, F' x * Real.sin (ω * x + c)) + ω * ∫ x, F x * Real.cos (ω * x + c) := by
    rw [← integral_const_mul, ← integral_add iFs (iFc.const_mul ω)]
    congr 1; funext x; simp only [G']; ring
  have hkey : ω * ∫ x, F x * Real.cos (ω * x + c) = -∫ x, F' x * Real.sin (ω * x + c) := by
    linarith
  have hbd : |∫ x, F' x * Real.sin (ω * x + c)| ≤ ∫ x, |F' x| := by
    refine (abs_integral_le_integral_abs).trans (integral_mono iFs.abs hF'.abs fun x => ?_)
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have : (fun x => F x * Real.cos (2 * π * l * x + c)) = fun x => F x * Real.cos (ω * x + c) := rfl
  rw [this, le_div_iff₀ hω0, ← abs_of_pos hω0, ← abs_mul, abs_of_pos hω0, mul_comm, hkey, abs_neg]
  exact hbd

theorem phi_shift_le_one {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 2 ≤ R) {ρ : ℝ} (hρ : ρ ≤ 1) :
    phi δ (ρ - R) ≤ 1 := by
  unfold phi
  have h1 : 1 ≤ (ρ - R) ^ 2 := by nlinarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h2 : -π * (ρ - R) ^ 2 / δ ^ 2 ≤ -(π / δ ^ 2) := by
    rw [div_le_iff₀ hδ2, show -(π / δ ^ 2) * δ ^ 2 = -π by field_simp]
    nlinarith [Real.pi_pos]
  have h3 : π / δ ^ 2 ≤ rexp (π / δ ^ 2) := by
    have := Real.add_one_le_exp (π / δ ^ 2); linarith
  have h4 : δ⁻¹ ≤ π / δ ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hδ hδ2]; nlinarith [Real.pi_gt_three]
  calc δ⁻¹ * rexp (-π * (ρ - R) ^ 2 / δ ^ 2) ≤ δ⁻¹ * rexp (-(π / δ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) (by positivity)
    _ ≤ rexp (π / δ ^ 2) * rexp (-(π / δ ^ 2)) :=
        mul_le_mul_of_nonneg_right (h4.trans h3) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem hasDerivAt_two_sqrt {x : ℝ} (hx : 0 < x) : HasDerivAt (fun x => 2 * √x) ((√x)⁻¹) x := by
  have := (Real.hasDerivAt_sqrt hx.ne').const_mul 2
  refine this.congr_deriv ?_
  have : 0 < √x := Real.sqrt_pos.mpr hx
  field_simp

theorem integral_sqrt_inv : ∫ x in (0:ℝ)..1, (√x)⁻¹ = 2 ∧ IntervalIntegrable (fun x => (√x)⁻¹) volume 0 1 := by
  have hc : ContinuousOn (fun x : ℝ => 2 * √x) (uIcc 0 1) := by fun_prop
  have hd : ∀ x ∈ Ioo (min (0:ℝ) 1) (max 0 1), HasDerivAt (fun x => 2 * √x) ((√x)⁻¹) x := by
    intro x hx; simp at hx; exact hasDerivAt_two_sqrt hx.1
  have hi := intervalIntegral.intervalIntegrable_deriv_of_nonneg hc hd (fun x _ => by positivity)
  refine ⟨?_, hi⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one (by simpa using hc)
    (fun x hx => hasDerivAt_two_sqrt hx.1) hi]
  simp

/-- `∫ φ_δ(ρ-R) ρ^{-1/2} dρ ≤ 3` (the `ρ^{-1/2}` singularity sits where `φ_δ(ρ - R) ≤ 1`). -/
theorem phi_sqrt_inv {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 2 ≤ R) :
    Integrable (fun ρ => phi δ (ρ - R) * (√ρ)⁻¹) ∧ ∫ ρ, phi δ (ρ - R) * (√ρ)⁻¹ ≤ 3 := by
  obtain ⟨hI, hII⟩ := integral_sqrt_inv
  have hIon : IntegrableOn (fun x : ℝ => (√x)⁻¹) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hII
  have hphi : Integrable fun ρ => phi δ (ρ - R) := (integrable_phi hδ).comp_sub_right R
  set M : ℝ → ℝ := fun ρ => (Ioc (0:ℝ) 1).indicator (fun x => (√x)⁻¹) ρ + phi δ (ρ - R)
  have hM : Integrable M := (hIon.integrable_indicator measurableSet_Ioc).add hphi
  have hmeas : AEStronglyMeasurable (fun ρ => phi δ (ρ - R) * (√ρ)⁻¹) volume :=
    ((HardyC2.continuous_phi δ).comp (continuous_sub_right R)).aestronglyMeasurable.mul
      (Real.continuous_sqrt.measurable.inv.aestronglyMeasurable)
  have hpt : ∀ ρ, phi δ (ρ - R) * (√ρ)⁻¹ ≤ M ρ := by
    intro ρ
    have h0 := phi_nonneg hδ (ρ - R)
    simp only [M]
    rcases le_or_gt ρ 0 with h | h
    · rw [Real.sqrt_eq_zero'.mpr h, inv_zero, mul_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ => by positivity) _) h0
    rcases le_or_gt ρ 1 with h1 | h1
    · rw [indicator_of_mem (show ρ ∈ Ioc (0:ℝ) 1 from ⟨h, h1⟩)]
      have := phi_shift_le_one hδ hδ1 hR h1
      have hs : 0 ≤ (√ρ)⁻¹ := by positivity
      nlinarith
    · rw [indicator_of_notMem (show ρ ∉ Ioc (0:ℝ) 1 from fun hh => by linarith [hh.2]), zero_add]
      have : (√ρ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by rw [Real.le_sqrt (by norm_num) h.le]; linarith)
      exact mul_le_of_le_one_right h0 this
  have hint : Integrable (fun ρ => phi δ (ρ - R) * (√ρ)⁻¹) :=
    hM.mono' hmeas (Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (phi_nonneg hδ _) (by positivity))]; exact hpt ρ)
  refine ⟨hint, (integral_mono hint hM hpt).trans ?_⟩
  simp only [M]
  rw [integral_add (hIon.integrable_indicator measurableSet_Ioc) hphi, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, hI, integral_sub_right_eq_self (phi δ) R, integral_phi hδ]
  norm_num

/-- `∫ φ_δ u² = δ²/(2π)` (one integration by parts). -/
theorem integral_phi_mul_sq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ u, phi δ u * u ^ 2 = δ ^ 2 / (2 * π) := by
  have hd : ∀ u, HasDerivAt (phi δ) (phi δ u * (-(2 * π * u / δ ^ 2))) u := by
    intro u
    have h1 : HasDerivAt (fun u => -π * u ^ 2 / δ ^ 2) (-(2 * π * u / δ ^ 2)) u := by
      have := ((hasDerivAt_pow 2 u).const_mul (-π)).div_const (δ ^ 2)
      refine this.congr_deriv ?_; push_cast; ring
    have := (h1.exp).const_mul δ⁻¹
    rw [show phi δ = fun y => δ⁻¹ * rexp (-π * y ^ 2 / δ ^ 2) from rfl]
    refine this.congr_deriv ?_
    ring
  have hG : ∀ u, HasDerivAt (fun u => u * phi δ u) (phi δ u - (2 * π / δ ^ 2) * (phi δ u * u ^ 2)) u := by
    intro u
    refine ((hasDerivAt_id' u).mul (hd u)).congr_deriv ?_
    ring
  have i2 := HardyC2.integrable_phi_mul_sq hδ hδ1
  have i0 := integrable_phi hδ
  have iG : Integrable fun u => u * phi δ u := by
    refine (i0.add i2).mono' ((continuous_id.mul (HardyC2.continuous_phi δ))).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have h0 := phi_nonneg hδ u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, Pi.add_apply]
    nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]
  have h := integral_eq_zero_of_hasDerivAt_of_integrable hG (i0.sub (i2.const_mul _)) iG
  rw [integral_sub i0 (i2.const_mul _), integral_const_mul, integral_phi hδ] at h
  have hδ2 : 0 < δ ^ 2 := by positivity
  field_simp at h ⊢
  linarith

theorem hasDerivAt_phi (δ u : ℝ) : HasDerivAt (phi δ) (phi δ u * (-(2 * π * u / δ ^ 2))) u := by
  have h1 : HasDerivAt (fun u => -π * u ^ 2 / δ ^ 2) (-(2 * π * u / δ ^ 2)) u := by
    have := ((hasDerivAt_pow 2 u).const_mul (-π)).div_const (δ ^ 2)
    refine this.congr_deriv ?_; push_cast; ring
  have := (h1.exp).const_mul δ⁻¹
  rw [show phi δ = fun y => δ⁻¹ * rexp (-π * y ^ 2 / δ ^ 2) from rfl]
  refine this.congr_deriv ?_
  ring

theorem abs_sqrt_sub_le {ρ R : ℝ} (hR : 1 ≤ R) : |√ρ - √R| ≤ |ρ - R| := by
  have hr : 1 ≤ √R := by rw [Real.le_sqrt zero_le_one (by linarith)]; simpa using hR
  have hrR : √R ^ 2 = R := Real.sq_sqrt (by linarith)
  rcases le_or_gt ρ 0 with h | h
  · rw [Real.sqrt_eq_zero'.mpr h, zero_sub, abs_neg, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    nlinarith
  · have hs : 0 ≤ √ρ := Real.sqrt_nonneg _
    have hsρ : √ρ ^ 2 = ρ := Real.sq_sqrt h.le
    have : |ρ - R| = |√ρ - √R| * (√ρ + √R) := by
      rw [show ρ - R = (√ρ - √R) * (√ρ + √R) by linear_combination (-1 : ℝ) * hsρ + hrR, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ √ρ + √R)]
    rw [this]
    have := abs_nonneg (√ρ - √R)
    nlinarith

theorem rpow_neg_five_half {t : ℝ} (ht : 0 < t) : t ^ (-(5:ℝ) / 2) = (t ^ 2 * √t)⁻¹ := by
  rw [show (-(5:ℝ) / 2) = -((2:ℕ) + 1 / 2 : ℝ) by norm_num, Real.rpow_neg ht.le,
    Real.rpow_add ht, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

theorem lnorm_ge_one {k : ℤ × ℤ} (hk : k ≠ 0) : 1 ≤ lnorm k := by
  have h1 : (1:ℝ) ≤ (nn k : ℝ) := by
    have : nn k ≠ 0 := fun h => hk (nn_eq_zero.mp h)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  rw [lnorm, ← nn_cast]
  exact Real.le_sqrt_of_sq_le (by simpa using h1)

/-- The residual of the disc transform after its `J₁` main term, `ρ > 0`. -/
def resF (l ρ : ℝ) : ℝ :=
  ρ ^ 2 * HardyC3.I (ρ * l) - π⁻¹ * (l * √l)⁻¹ * √ρ * Real.cos (2 * π * l * ρ + -(3 * π / 4))

def res (l ρ : ℝ) : ℝ := if 0 < ρ then resF l ρ else 0

theorem continuous_resF (l : ℝ) : Continuous (resF l) := by
  have := HardyC3.continuous_I
  unfold resF; fun_prop

theorem res_eq_indicator (l : ℝ) : res l = (Ioi 0).indicator (resF l) := by
  funext ρ; simp [res, indicator_apply]

theorem abs_res_small {l ρ : ℝ} (hl : 1 ≤ l) (h0 : 0 < ρ) (h1 : ρ ≤ l⁻¹) : |res l ρ| ≤ 5 * (l ^ 2)⁻¹ := by
  rw [res, if_pos h0, resF]
  have hl0 : 0 < l := by linarith
  have hsl : 0 < √l := Real.sqrt_pos.mpr hl0
  have hI := HardyC3.abs_I_le (ρ * l)
  have hρ2 : ρ ^ 2 ≤ (l ^ 2)⁻¹ := by rw [← inv_pow]; exact pow_le_pow_left₀ h0.le h1 2
  have hsρ : √ρ ≤ (√l)⁻¹ := by rw [← Real.sqrt_inv]; exact Real.sqrt_le_sqrt h1
  have hB : (l * √l)⁻¹ * √ρ ≤ (l ^ 2)⁻¹ := by
    calc (l * √l)⁻¹ * √ρ ≤ (l * √l)⁻¹ * (√l)⁻¹ := mul_le_mul_of_nonneg_left hsρ (by positivity)
      _ = (l ^ 2)⁻¹ := by
        rw [← mul_inv, mul_assoc, Real.mul_self_sqrt hl0.le, sq]
  have hcos := Real.abs_cos_le_one (2 * π * l * ρ + -(3 * π / 4))
  have hpi : π⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hpi0 : 0 < π⁻¹ := by positivity
  have hq : 0 ≤ (l ^ 2)⁻¹ := by positivity
  have hBn : 0 ≤ (l * √l)⁻¹ * √ρ := by positivity
  have e1 : |ρ ^ 2 * HardyC3.I (ρ * l)| ≤ (l ^ 2)⁻¹ * π := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ρ ^ 2)]
    exact mul_le_mul hρ2 hI (abs_nonneg _) hq
  have e2 : |π⁻¹ * (l * √l)⁻¹ * √ρ * Real.cos (2 * π * l * ρ + -(3 * π / 4))| ≤ (l ^ 2)⁻¹ := by
    rw [abs_mul, show π⁻¹ * (l * √l)⁻¹ * √ρ = π⁻¹ * ((l * √l)⁻¹ * √ρ) by ring,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹ * ((l * √l)⁻¹ * √ρ))]
    calc π⁻¹ * ((l * √l)⁻¹ * √ρ) * |Real.cos (2 * π * l * ρ + -(3 * π / 4))| ≤ 1 * (l ^ 2)⁻¹ * 1 :=
          mul_le_mul (mul_le_mul hpi hB hBn zero_le_one) hcos (abs_nonneg _) (by positivity)
      _ = (l ^ 2)⁻¹ := by ring
  have := abs_sub (ρ ^ 2 * HardyC3.I (ρ * l)) (π⁻¹ * (l * √l)⁻¹ * √ρ * Real.cos (2 * π * l * ρ + -(3 * π / 4)))
  nlinarith [Real.pi_lt_four]

theorem abs_res_large {l ρ : ℝ} (hl : 1 ≤ l) (h1 : l⁻¹ ≤ ρ) :
    |res l ρ| ≤ 40 * (l ^ 2 * √l)⁻¹ * (√ρ)⁻¹ := by
  have hl0 : 0 < l := by linarith
  have h0 : 0 < ρ := lt_of_lt_of_le (inv_pos.mpr hl0) h1
  have ht : 1 ≤ ρ * l := by
    have := mul_le_mul_of_nonneg_right h1 hl0.le
    rwa [inv_mul_cancel₀ hl0.ne'] at this
  have ht0 : 0 < ρ * l := by positivity
  have hC := HardyC4.abs_I_sub_main_le ht
  rw [HardyC4.rpow_neg_three_half ht0, rpow_neg_five_half ht0] at hC
  have hsρ : 0 < √ρ := Real.sqrt_pos.mpr h0
  have hsl : 0 < √l := Real.sqrt_pos.mpr hl0
  have hst : √(ρ * l) = √ρ * √l := Real.sqrt_mul h0.le l
  have hρ : √ρ * √ρ = ρ := Real.mul_self_sqrt h0.le
  have hl' : √l * √l = l := Real.mul_self_sqrt hl0.le
  have heq : res l ρ = ρ ^ 2 *
      (HardyC3.I (ρ * l) - π⁻¹ * (ρ * l * √(ρ * l))⁻¹ * Real.cos (2 * π * (ρ * l) - 3 * π / 4)) := by
    rw [res, if_pos h0, resF, hst]
    have hc : Real.cos (2 * π * l * ρ + -(3 * π / 4)) = Real.cos (2 * π * (ρ * l) - 3 * π / 4) := by
      congr 1; ring
    rw [hc]
    have key : ∀ s : ℝ, 0 < s →
        π⁻¹ * (l * √l)⁻¹ * s = (s * s) ^ 2 * (π⁻¹ * ((s * s) * l * (s * √l))⁻¹) := by
      intro s hs; field_simp
    have k2 := key (√ρ) hsρ
    rw [hρ] at k2
    rw [k2]; ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ρ ^ 2)]
  calc ρ ^ 2 * |_| ≤ ρ ^ 2 * (40 * ((ρ * l) ^ 2 * √(ρ * l))⁻¹) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = 40 * (l ^ 2 * √l)⁻¹ * (√ρ)⁻¹ := by
        rw [hst]; field_simp

theorem What_shift (δ R : ℝ) (k : ℤ × ℤ) : HardyC2.What δ R k =
    ∫ ρ, phi δ (ρ - R) * (if 0 < ρ then ρ ^ 2 * HardyC3.I (ρ * lnorm k) else 0) := by
  unfold HardyC2.What
  have := integral_add_left_eq_self (μ := volume)
    (fun ρ => phi δ (ρ - R) * (if 0 < ρ then ρ ^ 2 * HardyC3.I (ρ * lnorm k) else 0)) R
  simp only [add_sub_cancel_left] at this
  exact this

/-- **C5b, per-term bound.** For `k ≠ 0`, `R ≥ 2`, `0 < δ ≤ 1`:
`|Ŵ(k) - (√R/π) w(k)| ≤ 130 ‖k‖^{-5/2}`. -/
theorem abs_What_sub_le {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 2 ≤ R) {k : ℤ × ℤ} (hk : k ≠ 0) :
    |HardyC2.What δ R k - √R / π * w δ R k| ≤ 130 * (lnorm k ^ 2 * √(lnorm k))⁻¹ := by
  have hl : 1 ≤ lnorm k := lnorm_ge_one hk
  have hw : w δ R k = lnorm k ^ (-(3/2 : ℝ)) * rexp (-π * δ ^ 2 * lnorm k ^ 2) *
      Real.cos (2 * π * R * lnorm k - 3 * π / 4) := by
    rw [w, if_neg hk]
  rw [What_shift, hw]
  generalize lnorm k = l at hl ⊢
  have hl0 : 0 < l := by linarith
  have hsl : 0 < √l := Real.sqrt_pos.mpr hl0
  rw [show (-(3/2 : ℝ)) = -(3:ℝ) / 2 by norm_num, HardyC4.rpow_neg_three_half hl0]
  set A := π⁻¹ * (l * √l)⁻¹ with hA
  set q := (l ^ 2 * √l)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  set cs : ℝ → ℝ := fun ρ => Real.cos (2 * π * l * ρ + -(3 * π / 4)) with hcs
  set F : ℝ → ℝ := fun ρ => phi δ (ρ - R) * (√ρ - √R) with hF
  set F' : ℝ → ℝ := fun ρ => phi δ (ρ - R) * (-(2 * π * (ρ - R) / δ ^ 2)) * (√ρ - √R) +
    phi δ (ρ - R) * (1 / (2 * √ρ)) with hF'
  have hcont_f : Continuous fun ρ => phi δ (ρ - R) := (HardyC2.continuous_phi δ).comp (continuous_sub_right R)
  have hint_f : Integrable fun ρ => phi δ (ρ - R) := (integrable_phi hδ).comp_sub_right R
  have hint_f2 : Integrable fun ρ => phi δ (ρ - R) * (ρ - R) ^ 2 :=
    (HardyC2.integrable_phi_mul_sq hδ hδ1).comp_sub_right R
  obtain ⟨hint_s, hval_s⟩ := phi_sqrt_inv hδ hδ1 hR
  have hR1 : (1:ℝ) ≤ R := by linarith
  -- the pointwise decomposition
  have hpt : (fun ρ => phi δ (ρ - R) * (if 0 < ρ then ρ ^ 2 * HardyC3.I (ρ * l) else 0)) =
      fun ρ => (phi δ (ρ - R) * res l ρ + A * (F ρ * cs ρ)) + A * √R * (phi δ (ρ - R) * cs ρ) := by
    funext ρ
    simp only [res, resF, F, cs, hA]
    split_ifs with h
    · ring
    · rw [Real.sqrt_eq_zero'.mpr (not_lt.mp h)]; ring
  have hcs_cont : Continuous cs := by simp only [hcs]; fun_prop
  have hcs_le : ∀ ρ, |cs ρ| ≤ 1 := fun ρ => Real.abs_cos_le_one _
  -- integrability
  have iC : Integrable fun ρ => phi δ (ρ - R) * cs ρ :=
    hint_f.mono' (hcont_f.mul hcs_cont).aestronglyMeasurable (Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_nonneg hδ _)]
      exact mul_le_of_le_one_right (phi_nonneg hδ _) (hcs_le ρ))
  have hFle : ∀ ρ, |F ρ| ≤ phi δ (ρ - R) + phi δ (ρ - R) * (ρ - R) ^ 2 := by
    intro ρ
    simp only [F]
    rw [abs_mul, abs_of_nonneg (phi_nonneg hδ _)]
    have h1 := abs_sqrt_sub_le (ρ := ρ) hR1
    have h2 : |ρ - R| ≤ 1 + (ρ - R) ^ 2 := by nlinarith [abs_nonneg (ρ - R), sq_abs (ρ - R)]
    have h0 := phi_nonneg hδ (ρ - R)
    nlinarith
  have hcont_F : Continuous F := hcont_f.mul (Real.continuous_sqrt.sub continuous_const)
  have iF : Integrable F :=
    (hint_f.add hint_f2).mono' hcont_F.aestronglyMeasurable (Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs]; exact hFle ρ)
  have iFc : Integrable fun ρ => F ρ * cs ρ :=
    iF.norm.mono' (hcont_F.mul hcs_cont).aestronglyMeasurable (Eventually.of_forall fun ρ => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using hcs_le ρ))
  -- the residual
  set Mr : ℝ → ℝ := fun ρ => 5 * (l ^ 2)⁻¹ * (Ioc 0 l⁻¹).indicator (fun _ => (1:ℝ)) ρ +
    40 * q * (phi δ (ρ - R) * (√ρ)⁻¹) with hMr
  have iInd : Integrable ((Ioc (0:ℝ) l⁻¹).indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const measure_Ioc_lt_top.ne)
  have iMr : Integrable Mr := (iInd.const_mul _).add (hint_s.const_mul _)
  have hlinv : l⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl
  have hMr_pt : ∀ ρ, |phi δ (ρ - R) * res l ρ| ≤ Mr ρ := by
    intro ρ
    have h0 := phi_nonneg hδ (ρ - R)
    have hn1 : 0 ≤ 5 * (l ^ 2)⁻¹ * (Ioc 0 l⁻¹).indicator (fun _ => (1:ℝ)) ρ :=
      mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
    have hn2 : 0 ≤ 40 * q * (phi δ (ρ - R) * (√ρ)⁻¹) := by positivity
    rw [abs_mul, abs_of_nonneg h0]
    simp only [Mr]
    rcases le_or_gt ρ 0 with h | h
    · rw [show res l ρ = 0 by simp [res, not_lt.mpr h], abs_zero, mul_zero]; linarith
    rcases le_or_gt ρ l⁻¹ with h1 | h1
    · rw [indicator_of_mem (show ρ ∈ Ioc 0 l⁻¹ from ⟨h, h1⟩), mul_one]
      have hp1 := phi_shift_le_one hδ hδ1 hR (h1.trans hlinv)
      have := abs_res_small hl h h1
      have : phi δ (ρ - R) * |res l ρ| ≤ 1 * (5 * (l ^ 2)⁻¹) :=
        mul_le_mul hp1 this (abs_nonneg _) zero_le_one
      linarith
    · have := abs_res_large hl h1.le
      have : phi δ (ρ - R) * |res l ρ| ≤ phi δ (ρ - R) * (40 * q * (√ρ)⁻¹) :=
        mul_le_mul_of_nonneg_left this h0
      nlinarith
  have hres_meas : AEStronglyMeasurable (res l) volume := by
    rw [res_eq_indicator]; exact (continuous_resF l).aestronglyMeasurable.indicator measurableSet_Ioi
  have iR : Integrable fun ρ => phi δ (ρ - R) * res l ρ :=
    iMr.mono' (hcont_f.aestronglyMeasurable.mul hres_meas) (Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs]; exact hMr_pt ρ)
  have hsl_le : √l ≤ l := by
    calc √l ≤ √(l ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = l := Real.sqrt_sq hl0.le
  have hMr_val : ∫ ρ, Mr ρ ≤ 125 * q := by
    simp only [Mr]
    rw [integral_add (iInd.const_mul _) (hint_s.const_mul _), integral_const_mul, integral_const_mul,
      integral_indicator_const _ measurableSet_Ioc, volume_real_Ioc_of_le (by positivity), smul_eq_mul,
      mul_one, sub_zero]
    have h3 : (l ^ 2)⁻¹ * l⁻¹ ≤ q := by
      rw [hq, ← mul_inv]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by simpa using hsl_le) (by positivity))
    have : 40 * q * ∫ ρ, phi δ (ρ - R) * (√ρ)⁻¹ ≤ 40 * q * 3 := mul_le_mul_of_nonneg_left hval_s (by positivity)
    nlinarith
  have hres_bd : |∫ ρ, phi δ (ρ - R) * res l ρ| ≤ 125 * q :=
    (abs_integral_le_integral_abs).trans ((integral_mono iR.abs iMr hMr_pt).trans hMr_val)
  -- the oscillatory term
  have hd : ∀ x ≠ 0, HasDerivAt F (F' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun ρ => phi δ (ρ - R)) (phi δ (x - R) * (-(2 * π * (x - R) / δ ^ 2))) x := by
      have h := (hasDerivAt_phi δ (x - R)).comp x ((hasDerivAt_id x).sub_const R)
      refine h.congr_deriv ?_
      ring
    have h2 : HasDerivAt (fun ρ => √ρ - √R) (1 / (2 * √x)) x := (Real.hasDerivAt_sqrt hx).sub_const _
    exact h1.mul h2
  have hF'le : ∀ ρ, |F' ρ| ≤ (2 * π / δ ^ 2) * (phi δ (ρ - R) * (ρ - R) ^ 2) +
      1 / 2 * (phi δ (ρ - R) * (√ρ)⁻¹) := by
    intro ρ
    simp only [F']
    have h0 := phi_nonneg hδ (ρ - R)
    have h1 := abs_sqrt_sub_le (ρ := ρ) hR1
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_neg, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π),
        abs_of_pos (by positivity : (0:ℝ) < δ ^ 2)]
      have hd2 : 0 < δ ^ 2 := by positivity
      calc phi δ (ρ - R) * (2 * π * |ρ - R| / δ ^ 2) * |√ρ - √R|
          ≤ phi δ (ρ - R) * (2 * π * |ρ - R| / δ ^ 2) * |ρ - R| :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * π / δ ^ 2 * (phi δ (ρ - R) * (ρ - R) ^ 2) := by
            rw [← sq_abs (ρ - R)]; ring
    · rw [abs_mul, abs_of_nonneg h0, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * √ρ))]
      rw [one_div, mul_inv]; ring_nf; rfl
  have hmeas_F' : AEStronglyMeasurable F' volume := by
    have m1 : Measurable fun ρ : ℝ => 1 / (2 * √ρ) :=
      measurable_const.div (measurable_const.mul Real.continuous_sqrt.measurable)
    exact ((hcont_f.mul (by fun_prop : Continuous fun ρ : ℝ => -(2 * π * (ρ - R) / δ ^ 2))).mul
      (Real.continuous_sqrt.sub continuous_const)).aestronglyMeasurable.add
      (hcont_f.aestronglyMeasurable.mul m1.aestronglyMeasurable)
  have iMF : Integrable fun ρ => (2 * π / δ ^ 2) * (phi δ (ρ - R) * (ρ - R) ^ 2) +
      1 / 2 * (phi δ (ρ - R) * (√ρ)⁻¹) := (hint_f2.const_mul _).add (hint_s.const_mul _)
  have iF' : Integrable F' := iMF.mono' hmeas_F' (Eventually.of_forall fun ρ => by
    rw [Real.norm_eq_abs]; exact hF'le ρ)
  have hF'val : ∫ ρ, |F' ρ| ≤ 5 / 2 := by
    refine (integral_mono iF'.abs iMF hF'le).trans ?_
    rw [integral_add (hint_f2.const_mul _) (hint_s.const_mul _), integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self (fun u => phi δ u * u ^ 2) R, integral_phi_mul_sq hδ hδ1]
    have hd2 : 0 < δ ^ 2 := by positivity
    have : 2 * π / δ ^ 2 * (δ ^ 2 / (2 * π)) = 1 := by field_simp
    nlinarith
  have hJ := abs_integral_mul_cos_le hcont_F hd iF iF' hl0 (-(3 * π / 4))
  have hJ' : |∫ ρ, F ρ * cs ρ| ≤ (5 / 2) / (2 * π * l) :=
    hJ.trans (div_le_div_of_nonneg_right hF'val (by positivity))
  -- the Gaussian main term
  have hG : ∫ ρ, phi δ (ρ - R) * cs ρ = rexp (-π * δ ^ 2 * l ^ 2) * Real.cos (2 * π * R * l - 3 * π / 4) := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun u => phi δ u * Real.cos ((2 * π * l) * u + (2 * π * l * R + -(3 * π / 4)))) R
    have e : (fun ρ => phi δ (ρ - R) * cs ρ) =
        fun ρ => phi δ (ρ - R) * Real.cos ((2 * π * l) * (ρ - R) + (2 * π * l * R + -(3 * π / 4))) := by
      funext ρ; simp only [cs]; congr 2; ring
    rw [e, h, integral_phi_cos hδ]
    congr 1
    · congr 1; field_simp; ring
    · congr 1; ring
  -- assemble
  have s1 := integral_add (iR.add (iFc.const_mul A)) (iC.const_mul (A * √R))
  have s2 := integral_add iR (iFc.const_mul A)
  simp only [Pi.add_apply] at s1
  rw [hpt, s1, s2, integral_const_mul, integral_const_mul, hG]
  have hAJ : A * ((5 / 2) / (2 * π * l)) ≤ q := by
    rw [hA, hq]
    have e : π⁻¹ * (l * √l)⁻¹ * (5 / 2 / (2 * π * l)) = (5 / (4 * π ^ 2)) * (l ^ 2 * √l)⁻¹ := by
      field_simp; ring
    rw [e]
    have : 5 / (4 * π ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    exact mul_le_of_le_one_left (by positivity) this
  have hA0 : 0 ≤ A := by positivity
  have hAJ2 : |A * ∫ ρ, F ρ * cs ρ| ≤ q := by
    rw [abs_mul, abs_of_nonneg hA0]
    exact (mul_le_mul_of_nonneg_left hJ' hA0).trans hAJ
  have e2 : √R / π * ((l * √l)⁻¹ * rexp (-π * δ ^ 2 * l ^ 2) * Real.cos (2 * π * R * l - 3 * π / 4)) =
      A * √R * (rexp (-π * δ ^ 2 * l ^ 2) * Real.cos (2 * π * R * l - 3 * π / 4)) := by
    rw [hA]; ring
  rw [e2, add_sub_cancel_right]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- `‖k‖^{-5/2}` on `ℤ²` (zero at `k = 0`). -/
def q5 (k : ℤ × ℤ) : ℝ := (lnorm k ^ 2 * √(lnorm k))⁻¹

theorem q5_nonneg (k : ℤ × ℤ) : 0 ≤ q5 k := by
  unfold q5 lnorm; positivity

theorem summable_q5 : Summable q5 := by
  have hs := EisensteinSeries.summable_one_div_norm_rpow (k := 5 / 2) (by norm_num)
  rw [← HardyC2.e2.summable_iff]
  refine Summable.of_nonneg_of_le (fun x => q5_nonneg _) (fun x => ?_) hs
  simp only [Function.comp_apply]
  rcases eq_or_ne x 0 with h | h
  · subst h
    have : lnorm (HardyC2.e2 0) = 0 := by simp [lnorm, HardyC2.e2]
    rw [q5, this]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.sqrt_zero,
      mul_zero, inv_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
    have hle : ‖x‖ ≤ lnorm (HardyC2.e2 x) := by
      refine (pi_norm_le_iff_of_nonneg (by unfold lnorm; positivity)).mpr fun i => ?_
      rw [Int.norm_eq_abs, show HardyC2.e2 x = (x 0, x 1) from rfl, lnorm]
      dsimp only
      fin_cases i
      · exact Real.abs_le_sqrt (by simp; nlinarith [sq_nonneg ((x 1 : ℤ) : ℝ)])
      · exact Real.abs_le_sqrt (by simp; nlinarith [sq_nonneg ((x 0 : ℤ) : ℝ)])
    have hl0 : 0 < lnorm (HardyC2.e2 x) := lt_of_lt_of_le hx hle
    rw [q5, ← rpow_neg_five_half hl0, show (-(5:ℝ) / 2) = -(5 / 2) by norm_num]
    exact Real.rpow_le_rpow_of_nonpos hx hle (by norm_num)

theorem abs_w_le_q5 {δ : ℝ} (hδ : 0 < δ) (R : ℝ) (k : ℤ × ℤ) : |w δ R k| ≤ (π * δ ^ 2)⁻¹ * q5 k := by
  rcases eq_or_ne k 0 with h | h
  · subst h; simp [w]; exact mul_nonneg (by positivity) (q5_nonneg 0)
  have hl := lnorm_ge_one h
  rw [w, if_neg h, q5]
  generalize lnorm k = l at hl ⊢
  have hl0 : 0 < l := by linarith
  rw [show (-(3/2 : ℝ)) = -(3:ℝ) / 2 by norm_num, HardyC4.rpow_neg_three_half hl0]
  set x := π * δ ^ 2 * l ^ 2
  have hx : 0 < x := by positivity
  have he : rexp (-π * δ ^ 2 * l ^ 2) ≤ x⁻¹ := by
    rw [show -π * δ ^ 2 * l ^ 2 = -x by ring, Real.exp_neg]
    exact inv_anti₀ hx (by linarith [Real.add_one_le_exp x])
  have hxl : x⁻¹ ≤ (π * δ ^ 2 * l)⁻¹ := inv_anti₀ (by positivity) (by
    simp only [x]; have : l ≤ l ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity))
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (l * √l)⁻¹), abs_of_pos (Real.exp_pos _)]
  calc (l * √l)⁻¹ * rexp (-π * δ ^ 2 * l ^ 2) * |Real.cos (2 * π * R * l - 3 * π / 4)|
      ≤ (l * √l)⁻¹ * (π * δ ^ 2 * l)⁻¹ * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (he.trans hxl) (by positivity)) (Real.abs_cos_le_one _)
          (abs_nonneg _) (by positivity)
    _ = (π * δ ^ 2)⁻¹ * (l ^ 2 * √l)⁻¹ := by
        have : 0 < √l := Real.sqrt_pos.mpr hl0
        field_simp

theorem summable_w_all {δ : ℝ} (hδ : 0 < δ) (R : ℝ) : Summable (w δ R) :=
  Summable.of_norm_bounded (summable_q5.mul_left _) (fun k => by
    rw [Real.norm_eq_abs]; exact abs_w_le_q5 hδ R k)

/-- the fourth moment is at most `4`. -/
theorem M4_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : HardyC2.M4 δ ≤ 4 := by
  have i4 := HardyC2.integrable_phi_mul_pow4 hδ hδ1
  have ig : Integrable fun u => 300 * δ⁻¹ * rexp (-(π / (2 * δ ^ 2)) * u ^ 2) := by
    simpa [mul_assoc] using (integrable_gauss_scaled hδ two_pos).const_mul (300 * δ⁻¹)
  have h := integral_mono (i4.const_mul 120) ig fun u => by
    have h1 := phi_poly_le hδ hδ1 u
    have h2 := phi_nonneg hδ u
    simp only
    nlinarith [mul_nonneg h2 (sq_nonneg u)]
  rw [integral_const_mul, integral_const_mul, integral_gauss_scaled hδ two_pos] at h
  unfold HardyC2.M4
  have hs : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have : 300 * δ⁻¹ * (√2 * δ) = 300 * √2 := by field_simp
  nlinarith

theorem lnorm_zero : lnorm 0 = 0 := by simp [lnorm]

theorem integrable_phi_shift_sq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : ℝ) :
    Integrable fun u => phi δ u * (R + u) ^ 2 := by
  refine (((integrable_phi hδ).const_mul (2 * R ^ 2)).add ((HardyC2.integrable_phi_mul_sq hδ hδ1).const_mul 2)).mono'
    ((HardyC2.continuous_phi δ).mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have h0 := phi_nonneg hδ u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (R - u), mul_nonneg h0 (sq_nonneg (R - u))]

/-- **C5c, `k = 0`.** `Ŵ(0)` is the smoothed area up to a Gaussian tail: `|Ŵ(0) - π ∫ φ_δ(u)(R+u)²| ≤ 4`. -/
theorem What_zero_sub {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 2 ≤ R) :
    |HardyC2.What δ R 0 - π * ∫ u, phi δ u * (R + u) ^ 2| ≤ 4 := by
  have ip := integrable_phi_shift_sq hδ hδ1 R
  set h : ℝ → ℝ := (Iic (-R)).indicator (fun u => π * (phi δ u * (R + u) ^ 2)) with hh
  have ih : Integrable h := (ip.const_mul π).indicator measurableSet_Iic
  have hW : HardyC2.What δ R 0 = ∫ u, (π * (phi δ u * (R + u) ^ 2) - h u) := by
    unfold HardyC2.What
    congr 1; funext u
    rw [lnorm_zero, mul_zero, HardyC3.I_zero]
    by_cases hu : 0 < R + u
    · rw [if_pos hu, hh, indicator_of_notMem (show u ∉ Iic (-R) from fun h' => by simp at h'; linarith)]
      ring
    · rw [if_neg hu, hh, indicator_of_mem (show u ∈ Iic (-R) from by simp; linarith)]
      ring
  rw [hW, integral_sub (ip.const_mul π) ih, integral_const_mul, sub_sub_cancel_left, abs_neg]
  have i4 := HardyC2.integrable_phi_mul_pow4 hδ hδ1
  have hR0 : 0 < R := by linarith
  have hpt : ∀ u, h u ≤ π / R ^ 2 * (phi δ u * u ^ 4) := by
    intro u
    have h0 := phi_nonneg hδ u
    simp only [hh, indicator_apply, mem_Iic]
    split_ifs with hu
    · have hu2 : (R + u) ^ 2 * R ^ 2 ≤ u ^ 4 := by
        have a1 : (R + u) ^ 2 ≤ u ^ 2 := by nlinarith
        have a2 : R ^ 2 ≤ u ^ 2 := by nlinarith
        nlinarith [sq_nonneg (R + u)]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hu2 (mul_nonneg Real.pi_pos.le h0)
      nlinarith
    · positivity
  have hnn : 0 ≤ ∫ u, h u := integral_nonneg fun u => by
    simp only [hh, indicator_apply]; split_ifs
    · exact mul_nonneg Real.pi_pos.le (mul_nonneg (phi_nonneg hδ u) (sq_nonneg _))
    · exact le_rfl
  rw [abs_of_nonneg hnn]
  refine (integral_mono ih (i4.const_mul _) hpt).trans ?_
  rw [integral_const_mul]
  have hM := M4_le hδ hδ1
  have hM0 := HardyC2.M4_nonneg hδ
  unfold HardyC2.M4 at hM hM0
  have hR2 : 4 ≤ R ^ 2 := by nlinarith
  calc π / R ^ 2 * ∫ u, phi δ u * u ^ 4 ≤ π / 4 * 4 := by
        apply mul_le_mul (div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hR2) hM hM0 (by positivity)
    _ ≤ 4 := by nlinarith [Real.pi_lt_four]

theorem N_mono : Monotone fun r : ℝ => (N r : ℝ) := by
  intro a b hab
  simp only [Nat.cast_le]
  refine Set.ncard_le_ncard (fun p hp => ?_) (HardyC2.finite_N_set b)
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] at hp ⊢
  linarith

theorem integrable_phi_N {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : ℝ) :
    Integrable fun u => phi δ u * (N (R + u) : ℝ) := by
  set B := 2 * (2 * |R| + 3) ^ 2
  refine (((integrable_phi hδ).const_mul B).add ((HardyC2.integrable_phi_mul_sq hδ hδ1).const_mul 8)).mono'
    (((HardyC2.continuous_phi δ).measurable.mul (N_mono.measurable.comp (measurable_const_add R))).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  have h0 := phi_nonneg hδ u
  have hN := HardyC1.N_le (R + u)
  have hN0 : (0:ℝ) ≤ N (R + u) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hN0)]
  simp only [Pi.add_apply]
  have h1 : |R + u| ≤ |R| + |u| := abs_add_le R u
  have h2 : (2 * |R + u| + 3) ^ 2 ≤ B + 8 * u ^ 2 := by
    have : 0 ≤ 2 * |R + u| + 3 := by positivity
    have h3 : 2 * |R + u| + 3 ≤ (2 * |R| + 3) + 2 * |u| := by linarith
    have h4 : (2 * |R + u| + 3) ^ 2 ≤ ((2 * |R| + 3) + 2 * |u|) ^ 2 := pow_le_pow_left₀ this h3 2
    nlinarith [sq_nonneg ((2 * |R| + 3) - 2 * |u|), sq_abs u]
  have := mul_le_mul_of_nonneg_left (hN.trans h2) h0
  nlinarith

theorem integral_phi_E {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : ℝ) :
    ∫ u, phi δ u * E (R + u) = (∫ u, phi δ u * (N (R + u) : ℝ)) - π * ∫ u, phi δ u * (R + u) ^ 2 := by
  have : (fun u => phi δ u * E (R + u)) = fun u => phi δ u * (N (R + u) : ℝ) - π * (phi δ u * (R + u) ^ 2) := by
    funext u; simp only [E]; ring
  rw [this, integral_sub (integrable_phi_N hδ hδ1 R) ((integrable_phi_shift_sq hδ hδ1 R).const_mul π),
    integral_const_mul]

/-- **Rung C5.** The smoothed Voronoi expansion `HardyC1.SmoothedVoronoiC` holds (with `R₀ = 2`,
`C = 4 + 130 ∑ ‖k‖^{-5/2}`). -/
theorem smoothedVoronoiC : SmoothedVoronoiC := by
  refine ⟨4 + 130 * ∑' k, q5 k, 2, fun R hR δ hδl hδ1 => ?_⟩
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hδ : 0 < δ := lt_of_lt_of_le (inv_pos.mpr hlog) hδl
  set D : ℤ × ℤ → ℝ := fun k => HardyC2.What δ R k - √R / π * w δ R k with hD
  have hDb : ∀ k, |D k| ≤ 130 * q5 k + (if k = 0 then |D 0| else 0) := by
    intro k; rcases eq_or_ne k 0 with h | h
    · subst h; simp only [if_true]
      have := q5_nonneg 0; linarith
    · rw [if_neg h, add_zero]; exact abs_What_sub_le hδ hδ1 hR h
  have hDs : Summable D := Summable.of_norm_bounded
    ((summable_q5.mul_left 130).add (hasSum_ite_eq (0 : ℤ × ℤ) |D 0|).summable)
    (fun k => by rw [Real.norm_eq_abs]; exact hDb k)
  have hws := summable_w_all hδ R
  have hWs : Summable (HardyC2.What δ R) :=
    (hDs.add (hws.mul_left (√R / π))).congr fun k => by simp [D]
  have hP := HardyC2.smoothed_poisson hδ hδ1 hWs
  rw [integral_phi_E hδ hδ1, hP]
  have hsplit : ∑' k, HardyC2.What δ R k = ∑' k, D k + √R / π * ∑' k, w δ R k := by
    rw [← tsum_mul_left, ← hDs.tsum_add (hws.mul_left _)]; congr 1; funext k; simp [D]
  rw [hsplit, hDs.tsum_eq_add_tsum_ite 0]
  have hw0 : w δ R 0 = 0 := by simp [w]
  have h0 := What_zero_sub hδ hδ1 hR
  have hrest : |∑' k, (if k = 0 then 0 else D k)| ≤ 130 * ∑' k, q5 k := by
    have := tsum_of_norm_bounded (summable_q5.mul_left 130).hasSum
      (f := fun k => if k = 0 then 0 else D k) (fun k => by
        rcases eq_or_ne k 0 with h | h
        · subst h; simp only [if_true, norm_zero]; exact mul_nonneg (by norm_num) (q5_nonneg 0)
        · rw [if_neg h, Real.norm_eq_abs]; exact abs_What_sub_le hδ hδ1 hR h)
    rw [Real.norm_eq_abs] at this
    rwa [tsum_mul_left] at this
  have hD0 : D 0 = HardyC2.What δ R 0 := by simp [D, hw0]
  have hsqrt : 1 ≤ √R := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hS0 : 0 ≤ ∑' k, q5 k := tsum_nonneg q5_nonneg
  rw [hD0]
  have e : HardyC2.What δ R 0 + ∑' k, (if k = 0 then 0 else D k) + √R / π * ∑' k, w δ R k -
      π * (∫ u, phi δ u * (R + u) ^ 2) - √R / π * ∑' k, w δ R k =
      (HardyC2.What δ R 0 - π * ∫ u, phi δ u * (R + u) ^ 2) + ∑' k, (if k = 0 then 0 else D k) := by ring
  rw [e]
  calc _ ≤ |HardyC2.What δ R 0 - π * ∫ u, phi δ u * (R + u) ^ 2| + |∑' k, (if k = 0 then 0 else D k)| :=
        abs_add_le _ _
    _ ≤ 4 + 130 * ∑' k, q5 k := add_le_add h0 hrest
    _ ≤ (4 + 130 * ∑' k, q5 k) * √R := le_mul_of_one_le_right (by positivity) hsqrt

end HardyC5

end

end

end OMAPort_Circle

open Filter
open scoped EuclideanGeometry Real Topology

/-- Hardy-Landau: `¬E =o[atTop] (fun r => √r * √√r.log)` (original proof: C1 applied to C5). -/
theorem OMA.solution : type_of% @GaussCircleProblem.error_not_isLittleO :=
  OMAPort_Circle.HardyC1.error_not_isLittleO_of_smoothedVoronoi OMAPort_Circle.HardyC5.smoothedVoronoiC
