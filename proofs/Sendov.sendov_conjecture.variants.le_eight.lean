import FormalConjectures.Wikipedia.Sendov
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-
Sendov conjecture, degrees 2 to 8. Ported from the Lean formalisation of Sendov conjecture
by Terence Tao, repo teorth/sendov, commit 1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d,
licence Apache-2.0 (Copyright 2026 Terence Tao). Merged files: Defs, Common, Analytic,
Counterexample, Reduction, FiniteRange degrees 5 to 8, Interior, Boundary, Conjecture;
the all-degree numerical claim is replaced by the degree 5 to 8 cases plus a hypothesis n <= 8.
-/

section
namespace Sendov
noncomputable def M (n : ℕ) : ℝ := (n : ℝ) - 1
noncomputable def A (n : ℕ) (α : ℝ) : ℝ := 1 - 2 * α / M n
noncomputable def c (n : ℕ) (α : ℝ) : ℝ := 1 - α / M n - α / (2 * (3 + α))
noncomputable def Q (n : ℕ) (α : ℝ) (t : ℝ) : ℝ := 1 - 2 * c n α * t + A n α * t ^ 2
noncomputable def R (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
    A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) *
      ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)
end Sendov
end

section
namespace Sendov
variable {n : ℕ} {α t : ℝ}
lemma M_pos (hn : 2 ≤ n) : 0 < M n := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [M]
  linarith
lemma three_add_pos (hα : 0 ≤ α) : (0 : ℝ) < 3 + α := by linarith
lemma Q_eq (n : ℕ) (α t : ℝ) :
    Q n α t = (1 - c n α * t) ^ 2 + (A n α - c n α ^ 2) * t ^ 2 := by
  simp only [Q]
  ring
lemma A_nonneg (hfeas : c n α ^ 2 ≤ A n α) : 0 ≤ A n α :=
  le_trans (sq_nonneg _) hfeas
lemma alpha_le_half_M (hn : 2 ≤ n) (hfeas : c n α ^ 2 ≤ A n α) : α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  have hA : 0 ≤ A n α := A_nonneg hfeas
  rw [A] at hA
  have h : 2 * α / M n ≤ 1 := by linarith
  rw [div_le_one hM] at h
  linarith
lemma Q_nonneg (hfeas : c n α ^ 2 ≤ A n α) (t : ℝ) : 0 ≤ Q n α t := by
  rw [Q_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
lemma Q_one (hn : 2 ≤ n) (hα : 0 ≤ α) : Q n α 1 = α / (3 + α) := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  simp only [Q, c, A]
  field_simp
  ring
lemma Q_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) (hc : 0 ≤ c n α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ 1 := by
  have hB : Q n α 1 ≤ 1 := by
    rw [Q_one hn hα, div_le_one (three_add_pos hα)]
    linarith
  have hAc : A n α - 2 * c n α ≤ 0 := by
    simp only [Q] at hB
    linarith
  have h5 : A n α * t - 2 * c n α ≤ 0 := by
    rcases le_total 0 (A n α) with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [Q]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]
lemma c_pos_of_le_half_M (hn : 2 ≤ n) (hα : 0 ≤ α) (hhalf : α ≤ M n / 2) : 0 < c n α := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have h1 : α / M n ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hM (by norm_num)]
    linarith
  have h2 : α / (2 * (3 + α)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  simp only [c]
  linarith
lemma R_le_of_integral_le (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
      A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcoef : 0 ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
      (M_pos hn).le) hn2) (by linarith)
  rw [R]
  have := mul_le_mul_of_nonneg_left hJ hcoef
  linarith
end Sendov
end

section
namespace Sendov
open MeasureTheory Finset
lemma intervalIntegrable_const_mul_pow (a : ℝ) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => a * t ^ m) volume 0 1 :=
  (by fun_prop : Continuous fun t : ℝ => a * t ^ m).intervalIntegrable _ _
lemma quad_pow (b d t : ℝ) (k : ℕ) :
    (1 + b * t + d * t ^ 2) ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by
  rw [show (1 + b * t + d * t ^ 2) = (b * t + d * t ^ 2) + 1 by ring, add_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, add_pow, sum_mul]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have hexp : l + 2 * (i - l) = 2 * i - l := by omega
  rw [mul_pow, mul_pow, ← pow_mul]
  calc b ^ l * t ^ l * (d ^ (i - l) * t ^ (2 * (i - l))) * (i.choose l : ℝ) * (k.choose i : ℝ)
      = ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * (t ^ l * t ^ (2 * (i - l))) := by
        ring
    _ = ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by
        rw [← pow_add, hexp]
lemma t3_mul_Q_pow (n : ℕ) (α t : ℝ) (k : ℕ) :
    t ^ 3 * Q n α t ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) := by
  have hQ : Q n α t = 1 + (-2 * c n α) * t + A n α * t ^ 2 := by simp only [Q]; ring
  rw [hQ, quad_pow, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have hexp : 3 + (2 * i - l) = 2 * i - l + 3 := by omega
  calc t ^ 3 * (((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
        * t ^ (2 * i - l))
      = ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
          * (t ^ 3 * t ^ (2 * i - l)) := by ring
    _ = _ := by rw [← pow_add, hexp]
noncomputable def mom (n : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
    ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
      / ((2 * i - l + 4 : ℕ) : ℝ)
theorem integral_moment (n : ℕ) (α : ℝ) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = mom n α k := by
  rw [mom]
  have hfun : (fun t : ℝ => t ^ 3 * Q n α t ^ k)
      = fun t : ℝ => ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) :=
    funext fun t => t3_mul_Q_pow n α t k
  rw [hfun, intervalIntegral.integral_finsetSum]
  · refine sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun l _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      rw [one_pow]
      norm_num
      ring
    · exact fun l _ => intervalIntegrable_const_mul_pow _ _
  · intro i _
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_finsetSum _ fun l _ => by fun_prop
lemma integral_poly7 (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    (∫ t in (0 : ℝ)..1, (a₀ * t ^ 3 + a₁ * t ^ 4 + a₂ * t ^ 5 + a₃ * t ^ 6 + a₄ * t ^ 7))
      = a₀ / 4 + a₁ / 5 + a₂ / 6 + a₃ / 7 + a₄ / 8 := by
  have h₀ := intervalIntegrable_const_mul_pow a₀ 3
  have h₁ := intervalIntegrable_const_mul_pow a₁ 4
  have h₂ := intervalIntegrable_const_mul_pow a₂ 5
  have h₃ := intervalIntegrable_const_mul_pow a₃ 6
  have h₄ := intervalIntegrable_const_mul_pow a₄ 7
  rw [intervalIntegral.integral_add (((h₀.add h₁).add h₂).add h₃) h₄,
    intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂,
    intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow, integral_pow]
  norm_num
  ring
end Sendov
end

section
namespace Sendov
open MeasureTheory
lemma integral_rpow_zero_one {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring
lemma rpow_add_nat_pos {x : ℝ} (hx : 0 < x) (s : ℝ) (m : ℕ) :
    x ^ (s + (m : ℝ)) = x ^ s * x ^ m := by
  rw [Real.rpow_add hx, Real.rpow_natCast]
lemma continuous_rpow_const {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x e (Or.inr he)
lemma continuous_integrand (n : ℕ) (α : ℝ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ 3 * Q n α t ^ e := by
  have hQ : Continuous fun t : ℝ => Q n α t := by
    simp only [Q]; fun_prop
  have h3 : Continuous fun t : ℝ => t ^ 3 := by fun_prop
  exact h3.mul ((continuous_rpow_const he).comp hQ)
lemma rpow_le_rpow_of_le_one {x s t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hts : t ≤ s) :
    x ^ s ≤ x ^ t :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hts
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}
lemma sqrt_le_tangent (hq : 0 ≤ q) (hw : 0 < w) : Real.sqrt q ≤ q / (2 * w) + w / 2 := by
  have hrw : q / (2 * w) + w / 2 = (q + w ^ 2) / (2 * w) := by field_simp
  rw [hrw, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt q - w), Real.sq_sqrt hq]
lemma rpow_add_half_le (hq : 0 ≤ q) (k : ℕ) (hw : 0 < w) :
    q ^ ((k : ℝ) + 1 / 2) ≤ q ^ k * (q / (2 * w) + w / 2) := by
  rcases hq.lt_or_eq with h | h
  · have he : q ^ ((k : ℝ) + 1 / 2) = q ^ k * Real.sqrt q := by
      rw [Real.rpow_add h, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [he]
    exact mul_le_mul_of_nonneg_left (sqrt_le_tangent hq hw) (pow_nonneg hq k)
  · rw [← h, Real.zero_rpow (by positivity)]
    refine mul_nonneg (pow_nonneg le_rfl k) ?_
    rw [zero_div]
    linarith
lemma integral_rpow_le (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by rw [hk]; positivity
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_integrand n α he).intervalIntegrable _ _)
    ((by simp only [Q]; fun_prop : Continuous fun t : ℝ =>
      t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2))).intervalIntegrable _ _) ?_
  intro t ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht.1 3)
  rw [hk]
  exact rpow_add_half_le (Q_nonneg hfeas t) k hw
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {α : ℝ}
lemma M_five : M 5 = 4 := by norm_num [M]
lemma A_five (α : ℝ) : A 5 α = 1 - α / 2 := by
  rw [A, M]
  push_cast
  ring
lemma c_five (α : ℝ) : c 5 α = 1 - α / 4 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
lemma c_five' (hα : 0 ≤ α) : c 5 α = (12 - α - α ^ 2) / (4 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_five]
  field_simp
  ring
lemma integral_five (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 5 α t ^ ((((5 : ℕ) : ℝ) - 4) / 2))
      ≤ 3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24 := by
  have hk : ((((5 : ℕ) : ℝ) - 4) / 2) = ((0 : ℕ) : ℝ) + 1 / 2 := by norm_num
  refine (integral_rpow_le hfeas 0 hk (by norm_num : (0:ℝ) < 1/3)).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ =>
      t ^ 3 * (Q 5 α t ^ 0 * (Q 5 α t / (2 * (1/3)) + (1/3) / 2)))
      = fun t : ℝ => (3 / 2 * 1 + 1 / 6) * t ^ 3 + (3 / 2 * (-2 * c 5 α)) * t ^ 4
          + (3 / 2 * A 5 α) * t ^ 5 + 0 * t ^ 6 + 0 * t ^ 7 := by
    funext t
    simp only [Q]
    ring
  rw [hfun, integral_poly7]
  ring
lemma R_five_le (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    R 5 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24) := by
  have h := R_le_of_integral_le (n := 5) (by norm_num) hα (integral_five hfeas)
  rw [M_five] at h
  push_cast at h
  exact h.trans (le_of_eq (by ring))
theorem finite_range_five (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) : R 5 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 2 := by
    have h := alpha_le_half_M (n := 5) (by norm_num) hfeas
    rw [M_five] at h
    linarith
  have hR := R_five_le hα hfeas
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24)
      = 1 - (-9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234) / (96 * (3 + α) ^ 2) := by
    rw [A_five, c_five' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234 := by
    nlinarith [mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 2) (sub_nonneg.2 hle), sq_nonneg α, hα]
  have : 0 < (-9 * α ^ 4 - 123 * α ^ 3 + 596 * α ^ 2 + 30 * α + 234) / (96 * (3 + α) ^ 2) :=
    div_pos hP (by positivity)
  linarith
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {α : ℝ}
lemma M_six : M 6 = 5 := by norm_num [M]
lemma A_six (α : ℝ) : A 6 α = 1 - 2 * α / 5 := by norm_num [A, M]
lemma c_six (α : ℝ) : c 6 α = 1 - α / 5 - α / (2 * (3 + α)) := by norm_num [c, M]
lemma c_six' (hα : 0 ≤ α) : c 6 α = (30 - α - 2 * α ^ 2) / (10 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_six]
  field_simp
  ring
lemma integral_six (α : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = 1 / 4 - 2 * c 6 α / 5 + A 6 α / 6 := by
  have hfun : (fun t : ℝ => t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = fun t : ℝ => 1 * t ^ 3 + (-2 * c 6 α) * t ^ 4 + A 6 α * t ^ 5 + 0 * t ^ 6
          + 0 * t ^ 7 := by
    funext t
    rw [show ((((6 : ℕ) : ℝ) - 4) / 2) = 1 by norm_num, Real.rpow_one, Q]
    ring
  rw [hfun, integral_poly7]
  ring
lemma one_sub_R_six (hα : 0 ≤ α) :
    1 - R 6 α
      = (-24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575) / (375 * (3 + α) ^ 2) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [R, integral_six, A_six, c_six, M_six]
  push_cast
  field_simp
  ring
theorem finite_range_six (hα : 0 ≤ α) (hfeas : c 6 α ^ 2 ≤ A 6 α) : R 6 α < 1 := by
  have hle : α ≤ 3 := by
    have h := alpha_le_half_M (n := 6) (by norm_num) hfeas
    rw [M_six] at h
    linarith
  have hP : 0 < -24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575 := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hα hα) hα) (sub_nonneg.2 hle),
      mul_nonneg (mul_nonneg hα hα) (sub_nonneg.2 hle), sq_nonneg (1103 * α - 450)]
  have hpos : 0 < 1 - R 6 α := by
    rw [one_sub_R_six hα]
    exact div_pos hP (by positivity)
  linarith
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {α : ℝ}
lemma M_seven : M 7 = 6 := by norm_num [M]
lemma A_seven (α : ℝ) : A 7 α = 1 - α / 3 := by
  rw [A, M]
  push_cast
  ring
lemma c_seven (α : ℝ) : c 7 α = 1 - α / 6 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
lemma c_seven' (hα : 0 ≤ α) : c 7 α = (18 - α ^ 2) / (6 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_seven]
  field_simp
  ring
lemma integral_seven (hfeas : c 7 α ^ 2 ≤ A 7 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 7 α t ^ ((((7 : ℕ) : ℝ) - 4) / 2))
      ≤ 1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
        - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16 := by
  have hk : ((((7 : ℕ) : ℝ) - 4) / 2) = ((1 : ℕ) : ℝ) + 1 / 2 := by norm_num
  refine (integral_rpow_le hfeas 1 hk one_pos).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ => t ^ 3 * (Q 7 α t ^ 1 * (Q 7 α t / (2 * 1) + 1 / 2)))
      = fun t : ℝ => 1 * t ^ 3 + (-3 * c 7 α) * t ^ 4
          + ((4 * c 7 α ^ 2 + 3 * A 7 α) / 2) * t ^ 5 + (-2 * c 7 α * A 7 α) * t ^ 6
          + (A 7 α ^ 2 / 2) * t ^ 7 := by
    funext t
    simp only [Q]
    ring
  rw [hfun, integral_poly7]
  ring
lemma R_seven_le (hα : 0 ≤ α) (hfeas : c 7 α ^ 2 ≤ A 7 α) :
    R 7 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 12 + 1 / (24 * (3 + α))
      + 210 * A 7 α ^ 2 / (4 * (3 + α))
        * (1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
          - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16) := by
  have h := R_le_of_integral_le (n := 7) (by norm_num) hα (integral_seven hfeas)
  rw [M_seven] at h
  push_cast at h
  exact h.trans (le_of_eq (by ring))
theorem finite_range_seven (hα : 0 ≤ α) (hfeas : c 7 α ^ 2 ≤ A 7 α) : R 7 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 3 := by
    have h := alpha_le_half_M (n := 7) (by norm_num) hfeas
    rw [M_seven] at h
    linarith
  have hR := R_seven_le hα hfeas
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 12 + 1 / (24 * (3 + α))
      + 210 * A 7 α ^ 2 / (4 * (3 + α))
        * (1 / 4 - 3 * c 7 α / 5 + (4 * c 7 α ^ 2 + 3 * A 7 α) / 12
          - 2 * c 7 α * A 7 α / 7 + A 7 α ^ 2 / 16)
      = 1 - (-5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
          - 5022 * α + 33291) / (2592 * (3 + α) ^ 3) := by
    rw [A_seven, c_seven' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
      - 5022 * α + 33291 := by
    nlinarith [mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 4) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 5) (sub_nonneg.2 hle),
      sq_nonneg (19413 * α - 2511)]
  have : 0 < (-5 * α ^ 6 - 222 * α ^ 5 - 2619 * α ^ 4 + 17388 * α ^ 3 + 19413 * α ^ 2
      - 5022 * α + 33291) / (2592 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith
end Sendov
end

section
namespace Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
lemma integral_eq_mom (k : ℕ) (hk : ((n : ℝ) - 4) / 2 = (k : ℕ)) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) = mom n α k := by
  rw [hk]
  simp only [Real.rpow_natCast]
  exact integral_moment n α k
lemma integral_le_mom (hfeas : c n α ^ 2 ≤ A n α) (k : ℕ)
    (hk : ((n : ℝ) - 4) / 2 = (k : ℝ) + 1 / 2) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ mom n α (k + 1) / (2 * w) + w / 2 * mom n α k := by
  refine (integral_rpow_le hfeas k hk hw).trans (le_of_eq ?_)
  have hfun : (fun t : ℝ => t ^ 3 * (Q n α t ^ k * (Q n α t / (2 * w) + w / 2)))
      = fun t : ℝ => 1 / (2 * w) * (t ^ 3 * Q n α t ^ (k + 1))
          + w / 2 * (t ^ 3 * Q n α t ^ k) := by
    funext t
    rw [pow_succ]
    ring
  have hi : ∀ j : ℕ, ∀ a : ℝ,
      IntervalIntegrable (fun t : ℝ => a * (t ^ 3 * Q n α t ^ j)) volume 0 1 := by
    intro j a
    exact (by simp only [Q]; fun_prop :
      Continuous fun t : ℝ => a * (t ^ 3 * Q n α t ^ j)).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_add (hi (k + 1) _) (hi k _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_moment, integral_moment]
  ring
theorem finite_range_of_bound (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J)
    (h : 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J < 1) :
    R n α < 1 :=
  lt_of_le_of_lt (R_le_of_integral_le hn hα hJ) h
lemma mom_one (n : ℕ) (α : ℝ) : mom n α 1 = 1 / 4 - 2 * c n α / 5 + A n α / 6 := by
  simp [mom, Finset.sum_range_succ]
  ring
lemma mom_two (n : ℕ) (α : ℝ) :
    mom n α 2 = 1 / 4 - 4 * c n α / 5 + (2 * c n α ^ 2 / 3 + A n α / 3)
      - 4 * c n α * A n α / 7 + A n α ^ 2 / 8 := by
  simp [mom, Finset.sum_range_succ]
  ring
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {α : ℝ}
lemma M_eight : M 8 = 7 := by norm_num [M]
lemma A_eight (α : ℝ) : A 8 α = 1 - 2 * α / 7 := by
  rw [A, M]
  push_cast
  ring
lemma c_eight (α : ℝ) : c 8 α = 1 - α / 7 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring
lemma c_eight' (hα : 0 ≤ α) : c 8 α = (42 + α - 2 * α ^ 2) / (14 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_eight]
  field_simp
  ring
lemma R_eight_le (hα : 0 ≤ α) :
    R 8 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2 := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  have hk : ((((8 : ℕ) : ℝ) - 4) / 2) = ((2 : ℕ) : ℝ) := by norm_num
  have h := R_le_of_integral_le (n := 8) (by norm_num) hα (le_of_eq (integral_eq_mom 2 hk))
  rw [M_eight] at h
  push_cast at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring
theorem finite_range_eight (hα : 0 ≤ α) (hfeas : c 8 α ^ 2 ≤ A 8 α) : R 8 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 7 / 2 := by
    have h := alpha_le_half_M (n := 8) (by norm_num) hfeas
    rw [M_eight] at h
    linarith
  have hR := R_eight_le hα
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2
      = 1 - (-240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
          + 882882 * α + 1102059) / (72030 * (3 + α) ^ 3) := by
    rw [mom_two, A_eight, c_eight' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
      + 882882 * α + 1102059 := by
    nlinarith [mul_nonneg (pow_nonneg hα 5) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 4) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg hα (sq_nonneg (867020 * α - 700161)), hα, sq_nonneg α]
  have : 0 < (-240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
      + 882882 * α + 1102059) / (72030 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith
end Sendov
end

section
namespace Sendov
open _root_.Polynomial
theorem exists_root_multiset {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ z : Multiset ℂ, z.card = n - 1 ∧ (∀ w ∈ z, ‖w‖ ≤ 1) ∧
      p = C p.leadingCoeff * ((X - C a) * (z.map (fun w => X - C w)).prod) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = n := by
    rw [← hdeg]
    exact hsplit.natDegree_eq_card_roots.symm
  have hmem : a ∈ p.roots := by
    rw [mem_roots hp0]
    exact hpa
  obtain ⟨z, hz⟩ : ∃ z : Multiset ℂ, p.roots = a ::ₘ z :=
    ⟨p.roots.erase a, (Multiset.cons_erase hmem).symm⟩
  have hfac := hsplit.eq_prod_roots
  rw [hz] at hfac hcard
  refine ⟨z, ?_, ?_, ?_⟩
  · simp only [Multiset.card_cons] at hcard
    omega
  · intro w hw
    exact hroots w (by rw [hz]; exact Multiset.mem_cons_of_mem hw)
  · rwa [Multiset.map_cons, Multiset.prod_cons] at hfac
theorem exists_crit_multiset {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n) {a : ℂ}
    (hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - a‖) :
    ∃ q : Multiset ℂ, q.card = n - 1 ∧ (∀ v ∈ q, ‖v‖ ≤ 1) ∧ (∀ v ∈ q, v ≠ 0) ∧
      derivative p = C ((n : ℂ) * p.leadingCoeff)
        * (q.map (fun v => X - C (a - v⁻¹))).prod := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hdd : (derivative p).natDegree = n - 1 := by
    rw [natDegree_derivative p, hdeg]
  have hd0 : derivative p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdd
    omega
  have hlc : (derivative p).leadingCoeff = (n : ℂ) * p.leadingCoeff := by
    rw [leadingCoeff_derivative, hdeg, mul_comm]
  have hsplit : (derivative p).Splits := IsAlgClosed.splits _
  have hcard : (derivative p).roots.card = n - 1 := by
    rw [← hdd]
    exact hsplit.natDegree_eq_card_roots.symm
  have hfac := hsplit.eq_prod_roots
  obtain ⟨W, hW⟩ : ∃ W : Multiset ℂ, (derivative p).roots = W := ⟨_, rfl⟩
  rw [hW] at hfac hcard
  have hcrit' : ∀ w ∈ W, 1 ≤ ‖w - a‖ := by
    intro w hw
    exact hcrit w (isRoot_of_mem_roots (by rw [hW]; exact hw))
  have hne : ∀ w ∈ W, a - w ≠ 0 := by
    intro w hw h
    have h1 := hcrit' w hw
    rw [sub_eq_zero] at h
    rw [← h, sub_self, norm_zero] at h1
    linarith
  obtain ⟨q, hq⟩ : ∃ q : Multiset ℂ, q = W.map (fun w => (a - w)⁻¹) := ⟨_, rfl⟩
  have hback : q.map (fun v => a - v⁻¹) = W := by
    rw [hq, Multiset.map_map]
    have hid : ∀ w ∈ W, ((fun v => a - v⁻¹) ∘ (fun w => (a - w)⁻¹)) w = w := by
      intro w hw
      simp only [Function.comp_apply, inv_inv]
      ring
    rw [Multiset.map_congr rfl hid, Multiset.map_id']
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [hq, Multiset.card_map, hcard]
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    rw [norm_inv, inv_le_one_iff₀]
    right
    rw [norm_sub_rev]
    exact hcrit' w hw
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    exact inv_ne_zero (hne w hw)
  · rw [← hback, hlc] at hfac
    rwa [Multiset.map_map] at hfac
end Sendov
end

section
namespace Sendov
open _root_.Polynomial _root_.Multiset
open scoped Classical in
noncomputable def sumEraseProd (s : Multiset ℂ) : ℂ :=
  (s.map (fun j => (s.erase j).prod)).sum
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
lemma prod_cons_eq (a : ℂ) (z : Multiset ℂ) :
    (X - C a) * (z.map (fun w => X - C w)).prod
      = ((a ::ₘ z).map (fun w => X - C w)).prod := by
  rw [Multiset.map_cons, Multiset.prod_cons]
theorem centroid_identity (hn : 2 ≤ n) {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    ((n : ℂ) - 1) * (a + z.sum) = (n : ℂ) * (q.map (fun v => a - v⁻¹)).sum := by
  have hcard1 : (a ::ₘ z).card = n := by
    simp only [Multiset.card_cons, hzcard]
    omega
  have hcard2 : (q.map (fun v => a - v⁻¹)).card = n - 1 := by
    rw [Multiset.card_map, hqcard]
  have hp1 : p.coeff (n - 1) = c * (-(a + z.sum)) := by
    rw [hpz, prod_cons_eq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (a ::ₘ z) (by rw [hcard1]; omega)
    rw [hcard1] at this
    rw [this, Multiset.sum_cons]
  have hp2 : (derivative p).coeff (n - 2)
      = (n : ℂ) * c * (-((q.map (fun v => a - v⁻¹)).sum)) := by
    rw [hpq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (q.map (fun v => a - v⁻¹))
      (by rw [hcard2]; omega)
    rw [hcard2] at this
    have hn2 : n - 1 - 1 = n - 2 := by omega
    rwa [hn2] at this
  have hlink : (derivative p).coeff (n - 2) = p.coeff (n - 1) * ((n : ℂ) - 1) := by
    have hsucc : n - 2 + 1 = n - 1 := by omega
    have h1 : ((n - 2 : ℕ) : ℂ) + 1 = (n : ℂ) - 1 := by
      have h2 : (2 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2]
      ring
    rw [coeff_derivative, hsucc, h1]
  rw [hp1, hp2] at hlink
  refine mul_left_cancel₀ hc0 ?_
  linear_combination hlink
@[simp] lemma sumEraseProd_zero : sumEraseProd 0 = 0 := by simp [sumEraseProd]
open scoped Classical in
lemma sumEraseProd_cons (v : ℂ) (t : Multiset ℂ) :
    sumEraseProd (v ::ₘ t) = t.prod + v * sumEraseProd t := by
  simp only [sumEraseProd, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.prod_cons]
lemma prod_map_neg (s : Multiset ℂ) :
    (s.map (fun w => -w)).prod = (-1) ^ (Multiset.card s) * s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring
lemma eval_prod_zero (z : Multiset ℂ) :
    ((z.map (fun w => X - C w)).prod).eval 0 = (-1) ^ (Multiset.card z) * z.prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  rw [show (z.map ((fun r : ℂ[X] => r.eval 0) ∘ (fun w => X - C w))).prod
      = (z.map (fun w => -w)).prod from
    congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)]
  exact prod_map_neg z
lemma eval_deriv_prod_zero : ∀ (z : Multiset ℂ),
    (derivative (z.map (fun w => X - C w)).prod).eval 0
      = -((-1) ^ (Multiset.card z) * sumEraseProd z) := by
  intro z
  induction z using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, zero_sub, Multiset.card_cons]
    rw [ih, eval_prod_zero, sumEraseProd_cons]
    ring
lemma prod_inv_sub_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹ - a)).prod * q.prod = (q.map (fun v => 1 - a * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp
open scoped Classical in
theorem second_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by
  have hev1 : (derivative p).eval 0 = (n : ℂ) * c * (q.map (fun v => v⁻¹ - a)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp
  have hev2 : (derivative p).eval 0
      = c * ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, zero_sub, one_mul]
    rw [eval_deriv_prod_zero, eval_prod_zero, hzcard]
    ring
  have hcancel : (n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod
      = (-1) ^ (n - 1) * (z.prod + a * sumEraseProd z) := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev1.symm.trans hev2
  calc (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (n : ℂ) * ((q.map (fun v => v⁻¹ - a)).prod * q.prod) := by
        rw [prod_inv_sub_mul q hq0]
    _ = ((n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod) * q.prod := by ring
    _ = ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by ring
open MeasureTheory in
lemma continuous_deriv_seg (p : ℂ[X]) (a w : ℂ) :
    Continuous fun t : ℝ => (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  fun_prop
open MeasureTheory in
lemma eval_eq_integral {p : ℂ[X]} {a : ℂ} (hpa : p.eval a = 0) (w : ℂ) :
    p.eval w = (w - a) * ∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p.eval (a + (s : ℂ) * (w - a)))
      ((w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a + (s : ℂ) * (w - a)) (w - a) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using (h0.mul_const (w - a)).const_add a
    have h2 : HasDerivAt (fun u : ℂ => p.eval u)
        ((derivative p).eval (a + (t : ℂ) * (w - a))) (a + (t : ℂ) * (w - a)) :=
      p.hasDerivAt _
    have h3 := h2.scomp t h1
    simp only [Function.comp_def] at h3
    exact h3
  have hint : IntervalIntegrable
      (fun t : ℝ => (w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) volume 0 1 :=
    ((continuous_deriv_seg p a w).const_smul (w - a)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, one_mul] at hFTC
  rw [show a + (w - a) = w from by ring, hpa, sub_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_const_mul]
open MeasureTheory in
theorem first_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0) (ha0 : a ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0) (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * z.prod := by
  have hint : p.eval 0
      = -a * ∫ t in (0 : ℝ)..1,
          (n : ℂ) * c * (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod := by
    rw [eval_eq_integral hpa 0]
    congr 1
    · ring
    refine intervalIntegral.integral_congr ?_
    intro t _
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  have hev : p.eval 0 = c * (-a) * ((-1) ^ (n - 1) * z.prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, zero_sub]
    rw [eval_prod_zero, hzcard]
    ring
  rw [intervalIntegral.integral_const_mul] at hint
  have hcancel : (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod
      = (-1) ^ (n - 1) * z.prod := by
    have hne : -a * c ≠ 0 := by simp [ha0, hc0]
    refine mul_left_cancel₀ hne ?_
    linear_combination hint.symm.trans hev
  calc (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod * q.prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [prod_inv_sub_mul q hq0]
        refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
        intro v _
        ring
    _ = ((n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod) * q.prod := by
        rw [intervalIntegral.integral_mul_const]
        ring
    _ = ((-1) ^ (n - 1) * z.prod) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * z.prod := by ring
lemma prod_map_mul_const (b : ℂ) (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map (fun v => b * f v)).prod = b ^ (Multiset.card s) * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring
lemma prod_inv_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹)).prod * q.prod = 1 := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp
theorem prod_sub_mul_prod (hc0 : c ≠ 0) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => a - w)).prod = (n : ℂ) := by
  have hev1 : (derivative p).eval a = (n : ℂ) * c * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  have hev2 : (derivative p).eval a = c * (z.map (fun w => a - w)).prod := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, sub_self, zero_mul,
      add_zero, one_mul, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  have hcancel : (z.map (fun w => a - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev2.symm.trans hev1
  calc q.prod * (z.map (fun w => a - w)).prod
      = q.prod * ((n : ℂ) * (q.map (fun v => v⁻¹)).prod) := by rw [hcancel]
    _ = (n : ℂ) * ((q.map (fun v => v⁻¹)).prod * q.prod) := by ring
    _ = (n : ℂ) := by rw [prod_inv_mul q hq0]; ring
open MeasureTheory in
theorem polar_identity (hc0 : c ≠ 0) (ha0 : a ≠ 0) (ha2 : a ^ 2 ≠ 1)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => 1 - a * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
  have hinv : a⁻¹ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply ha2
    field_simp at h
    linear_combination -h
  have hint : p.eval a⁻¹
      = (a⁻¹ - a) * ((n : ℂ) * c * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
    rw [eval_eq_integral hpa a⁻¹]
    congr 1
    have hcong : (∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (a⁻¹ - a)))
        = ∫ t in (0 : ℝ)..1,
            (n : ℂ) * c * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      simp only []
      rw [hpq]
      simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      congr 1
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v _
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      ring
    rw [hcong, intervalIntegral.integral_const_mul]
  have hev : p.eval a⁻¹ = c * ((a⁻¹ - a) * (z.map (fun w => a⁻¹ - w)).prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  have hcancel : (z.map (fun w => a⁻¹ - w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    have hne : c * (a⁻¹ - a) ≠ 0 := mul_ne_zero hc0 hinv
    refine mul_left_cancel₀ hne ?_
    linear_combination hev.symm.trans hint
  have hLHS : (z.map (fun w => 1 - a * w)).prod
      = a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod := by
    rw [← hzcard, ← prod_map_mul_const a z (fun w => a⁻¹ - w)]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    field_simp
  have hRHS : ∀ t : ℝ, (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
      = a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    intro t
    have h1 : (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
        = (q.map (fun v => a * (v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)))).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v hv
      have hv0 : v ≠ 0 := hq0 v hv
      field_simp
      ring
    rw [h1, prod_map_mul_const a q (fun v => v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)),
      Multiset.prod_map_mul, hqcard]
    have : (q.map (fun v => v)).prod = q.prod := by rw [Multiset.map_id']
    rw [this]
    ring
  rw [hLHS]
  calc q.prod * (a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod)
      = a ^ (n - 1) * q.prod
          * ((n : ℂ) * ∫ t in (0 : ℝ)..1,
              (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
        rw [hcancel]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
        rw [intervalIntegral.integral_const_mul]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [hRHS t]
end Sendov
end

section
namespace Sendov
open _root_.Multiset
variable {a : ℝ} {t : Multiset ℝ}
lemma amgm_step (N : ℕ) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    a * u ^ N ≤ ((a + N * u) / (N + 1)) ^ (N + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + ((N : ℝ) + 1) * (w - 1) ≤ w ^ (N + 1) := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) (N + 1)
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  have hkey : a / u ≤ w ^ (N + 1) := by linarith [hber]
  rw [hbase, mul_pow]
  have : a ≤ w ^ (N + 1) * u := by
    rw [div_le_iff₀ hu] at hkey; linarith
  calc a * u ^ N ≤ (w ^ (N + 1) * u) * u ^ N := by
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = w ^ (N + 1) * u ^ (N + 1) := by ring
lemma maclaurin_step (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    u ^ N + N * a * u ^ (N - 1) ≤ ((N : ℝ) + 1) * ((a + N * u) / (N + 1)) ^ N := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + (N : ℝ) * (w - 1) ≤ w ^ N := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) N
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hpow : u ^ (m + 1) = u ^ m * u := by ring
  rw [hbase, mul_pow]
  simp only [Nat.add_sub_cancel]
  push_cast
  have hkey : 1 + ((m : ℝ) + 1) * (a / u) ≤ ((m : ℝ) + 1 + 1) * w ^ (m + 1) := by
    push_cast at hber hau ⊢
    nlinarith [hber, hau]
  have humpos : (0 : ℝ) < u ^ m := by positivity
  have := mul_le_mul_of_nonneg_right hkey humpos.le
  calc u ^ (m + 1) + ((m : ℝ) + 1) * a * u ^ m
      = (1 + ((m : ℝ) + 1) * (a / u)) * u ^ m * u := by field_simp; ring
    _ ≤ (((m : ℝ) + 1 + 1) * w ^ (m + 1)) * u ^ m * u := by
        exact mul_le_mul_of_nonneg_right this hu.le
    _ = ((m : ℝ) + 1 + 1) * (w ^ (m + 1) * u ^ (m + 1)) := by ring
theorem Multiset.prod_le_mean_pow : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) →
    s.prod ≤ (s.sum / s.card) ^ s.card := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
    intro hs
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have hIH := ih ht
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.prod_cons, Nat.cast_add,
      Nat.cast_one]
    rcases Nat.eq_zero_or_pos t.card with hc | hc
    · 
      have ht0 : t = 0 := Multiset.card_eq_zero.1 hc
      subst ht0
      simp
    · have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · 
        have hzero : t.prod = 0 := by
          have : t.prod ≤ u ^ t.card := hIH
          rw [← hz] at this
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [h0] at this
          linarith
        rw [hzero, mul_zero]
        positivity
      · have hstep := amgm_step (a := a) t.card hupos ha
        calc a * t.prod ≤ a * u ^ t.card := mul_le_mul_of_nonneg_left hIH ha
          _ ≤ ((a + t.card * u) / (t.card + 1)) ^ (t.card + 1) := hstep
          _ = ((a + t.sum) / (t.card + 1)) ^ (t.card + 1) := by rw [hsum]
lemma esymm_card_cons (a : ℝ) (t : Multiset ℝ) (ht : t ≠ 0) :
    (a ::ₘ t).esymm t.card = t.prod + a * t.esymm (t.card - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 := ⟨t.card - 1, by
    have : 0 < t.card := Multiset.card_pos.2 ht
    omega⟩
  rw [hm]
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Nat.add_sub_cancel]
  congr 1
  · rw [← hm, Multiset.powersetCard_self]
    simp
  · rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro u _
    simp
theorem Multiset.esymm_card_pred_le : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) → s ≠ 0 →
    s.esymm (s.card - 1) ≤ s.card * (s.sum / s.card) ^ (s.card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons a t ih =>
    intro hs _
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    have hamgm := Multiset.prod_le_mean_pow t ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [Multiset.esymm]
    · have hc : 0 < t.card := Multiset.card_pos.2 ht0
      have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      have hIH := ih ht ht0
      rw [esymm_card_cons a t ht0]
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · 
        have hzero : t.prod = 0 := by
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [← hz, h0] at hamgm
          linarith
        have hsum0 : t.sum = 0 := by rw [hsum, ← hz, mul_zero]
        rw [hzero, hsum0, zero_add, add_zero]
        rcases Nat.lt_or_ge t.card 2 with h1 | h2
        · 
          have hc1 : t.card = 1 := by omega
          have he0 : t.esymm (t.card - 1) = 1 := by
            rw [hc1]
            simp [Multiset.esymm]
          rw [he0, hc1]
          norm_num
          linarith
        · 
          have hz0 : (0 : ℝ) ^ (t.card - 1) = 0 := zero_pow (by omega)
          rw [← hz, hz0, mul_zero] at hIH
          have : a * t.esymm (t.card - 1) ≤ 0 := by nlinarith [hIH, ha]
          have hrhs : (0 : ℝ) ≤ ((t.card : ℝ) + 1) * (a / ((t.card : ℝ) + 1)) ^ t.card := by
            positivity
          linarith
      · have hstep := maclaurin_step (a := a) t.card hc hupos ha
        calc t.prod + a * t.esymm (t.card - 1)
            ≤ u ^ t.card + a * ((t.card : ℝ) * u ^ (t.card - 1)) := by
              have h2 : a * t.esymm (t.card - 1) ≤ a * ((t.card : ℝ) * u ^ (t.card - 1)) :=
                mul_le_mul_of_nonneg_left hIH ha
              linarith [hamgm]
          _ = u ^ t.card + (t.card : ℝ) * a * u ^ (t.card - 1) := by ring
          _ ≤ ((t.card : ℝ) + 1) * ((a + t.card * u) / (t.card + 1)) ^ t.card := hstep
          _ = ((t.card : ℝ) + 1) * ((a + t.sum) / ((t.card : ℝ) + 1)) ^ t.card := by rw [hsum]
end Sendov
end

section
namespace Sendov
open _root_.Multiset
lemma prod_norm_nonneg (s : Multiset ℂ) : 0 ≤ (s.map (fun z => ‖z‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg z
lemma prod_norm_le_one : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    simp only [Multiset.map_cons, Multiset.prod_cons]
    nlinarith [norm_nonneg w]
lemma norm_mul_norm_inv_sub_conj_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ ≤ 1 - ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · have hkey : w * (w⁻¹ - (starRingEnd ℂ) w) = 1 - ((‖w‖ : ℝ) : ℂ) ^ 2 := by
      rw [mul_sub, mul_inv_cancel₀ hne, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ = ‖(1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2‖ := by
      rw [← norm_mul, hkey]
    rw [h1]
    have h2 : ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [norm_nonneg w])]
theorem defect : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod * (s.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum
      ≤ 1 - ((s.map (fun z => ‖z‖)).prod) ^ 2 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    have hP1 : (t.map (fun z => ‖z‖)).prod ≤ 1 := prod_norm_le_one t ht
    have hT0 : 0 ≤ (t.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum := by
      refine Multiset.sum_nonneg ?_
      intro y hy
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
      exact norm_nonneg _
    have hr0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hpt := norm_mul_norm_inv_sub_conj_le hw
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have hstep1 := mul_le_mul_of_nonneg_left hpt hP0
    have hstep2 := mul_le_mul_of_nonneg_left hIH hr0
    have hfac : 0 ≤ (1 - ‖w‖) * (1 - (t.map (fun z => ‖z‖)).prod)
        * (1 - ‖w‖ * (t.map (fun z => ‖z‖)).prod) := by
      have h3 : ‖w‖ * (t.map (fun z => ‖z‖)).prod ≤ 1 := by nlinarith
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [hstep1, hstep2, hfac]
end Sendov
end

section
namespace Sendov
noncomputable def QQ (c A t : ℝ) : ℝ := 1 - 2 * c * t + A * t ^ 2
lemma Q_eq_QQ (n : ℕ) (α t : ℝ) : Q n α t = QQ (c n α) (A n α) t := rfl
variable {c A t : ℝ}
lemma QQ_eq (c A t : ℝ) : QQ c A t = (1 - c * t) ^ 2 + (A - c ^ 2) * t ^ 2 := by
  simp only [QQ]; ring
lemma QQ_zero (c A : ℝ) : QQ c A 0 = 1 := by simp [QQ]
lemma QQ_one (c A : ℝ) : QQ c A 1 = 1 - 2 * c + A := by simp [QQ]
lemma QQ_nonneg (hfeas : c ^ 2 ≤ A) (t : ℝ) : 0 ≤ QQ c A t := by
  rw [QQ_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
lemma QQ_le_one (hc : 0 ≤ c) (hB : QQ c A 1 ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ c A t ≤ 1 := by
  have hAc : A - 2 * c ≤ 0 := by rw [QQ_one] at hB; linarith
  have h5 : A * t - 2 * c ≤ 0 := by
    rcases le_total 0 A with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]
lemma QQ_le_chord (ht0 : 0 ≤ t) (ht : A * t ≤ c) : QQ c A t ≤ 1 - c * t := by
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht)]
lemma QQ_le_at_one (hA : 0 ≤ A) (ht : c ≤ A * t) (ht1 : t ≤ 1) : QQ c A t ≤ QQ c A 1 := by
  have hkey : 0 ≤ A * (1 + t) - 2 * c := by nlinarith [ht, hA, ht1]
  simp only [QQ]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hkey]
lemma continuous_pow_mul_QQ (c A : ℝ) (k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ k * QQ c A t ^ e := by
  have hQ : Continuous fun t : ℝ => QQ c A t := by simp only [QQ]; fun_prop
  have hk : Continuous fun t : ℝ => t ^ k := by fun_prop
  exact hk.mul ((continuous_rpow_const he).comp hQ)
end Sendov
end

section
namespace Sendov
open MeasureTheory
lemma integral_lin_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s) = 1 / ((s + 1) * (s + 2)) := by
  have hrefl : (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) * x ^ s = x ^ s - x ^ (s + (1 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h, Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (s + (1 : ℕ))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_rpow'
    push_cast
    linarith
  rw [intervalIntegral.integral_sub hi' hi, integral_rpow_zero_one (by linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring
lemma integral_cube_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = 6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) := by
  have h1 : (0 : ℝ) < s + 1 := by linarith
  have hrefl : (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) ^ 3 * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) ^ 3 * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) ^ 3 * x ^ s
        = x ^ s - 3 * x ^ (s + (1 : ℕ)) + 3 * x ^ (s + (2 : ℕ)) - x ^ (s + (3 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]
      rw [Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith),
        Real.zero_rpow (by push_cast; linarith), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h, rpow_add_nat_pos h, rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => x ^ (s + (m : ℕ))) volume 0 1 := by
    intro m
    apply intervalIntegral.intervalIntegrable_rpow'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hc : ∀ (a : ℝ) (m : ℕ),
      IntervalIntegrable (fun x : ℝ => a * x ^ (s + (m : ℕ))) volume 0 1 :=
    fun a m => (hi m).const_mul a
  rw [intervalIntegral.integral_sub ((hi'.sub (hc 3 1)).add (hc 3 2)) (hi 3),
    intervalIntegral.integral_add (hi'.sub (hc 3 1)) (hc 3 2),
    intervalIntegral.integral_sub hi' (hc 3 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow_zero_one (by linarith), integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring
lemma beta_le_six_div_pow {s : ℝ} (hs : 0 < s) :
    6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) ≤ 6 / s ^ 4 := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hs.le, sq_nonneg s, sq_nonneg (s + 1)]
lemma integral_chord_lin {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t * (1 - c * t) ^ s) = 1 / (c ^ 2 * ((s + 1) * (s + 2))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) * (1 - y) ^ s) hc'
  have hfun : (fun t : ℝ => ((c * t) / c) * (1 - c * t) ^ s)
      = fun t : ℝ => t * (1 - c * t) ^ s := by
    funext t
    rw [mul_div_cancel_left₀ t hc']
  simp only [hfun] at h
  rw [show c * (1 / c) = 1 by field_simp, mul_zero] at h
  have hg : (fun y : ℝ => (y / c) * (1 - y) ^ s)
      = fun y : ℝ => (1 / c) * (y * (1 - y) ^ s) := by
    funext y
    field_simp
  rw [hg, intervalIntegral.integral_const_mul, integral_lin_mul_rpow hs] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp
lemma integral_chord_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 3 * (1 - c * t) ^ s)
      = 6 / (c ^ 4 * ((s + 1) * (s + 2) * (s + 3) * (s + 4))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s) hc'
  have hfun : (fun t : ℝ => ((c * t) / c) ^ 3 * (1 - c * t) ^ s)
      = fun t : ℝ => t ^ 3 * (1 - c * t) ^ s := by
    funext t
    rw [mul_div_cancel_left₀ t hc']
  simp only [hfun] at h
  rw [show c * (1 / c) = 1 by field_simp, mul_zero] at h
  have hg : (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s)
      = fun y : ℝ => (1 / c ^ 3) * (y ^ 3 * (1 - y) ^ s) := by
    funext y
    field_simp
  rw [hg, intervalIntegral.integral_const_mul, integral_cube_mul_rpow hs] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp
theorem integral_le_tail_gen {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c A t ^ r)
      ≤ (∫ t in (0 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ r) + QQ c A 1 ^ r / (k + 1) := by
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hfeas
  set t₀ : ℝ := c / A with ht₀def
  have ht₀pos : 0 < t₀ := by positivity
  set s : ℝ := min t₀ 1 with hsdef
  have hs0 : 0 < s := lt_min ht₀pos one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hcont : Continuous fun u : ℝ => u ^ k * QQ c A u ^ r := continuous_pow_mul_QQ c A k hr.le
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => u ^ k * QQ c A u ^ r) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hchordcont : Continuous fun u : ℝ => u ^ k * (1 - c * u) ^ r :=
    (by fun_prop : Continuous fun u : ℝ => u ^ k).mul
      ((continuous_rpow_const hr.le).comp (by fun_prop))
  have hsc : s ≤ 1 / c := by
    rcases min_cases t₀ 1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hsdef, h, ht₀def, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_one hA]
      nlinarith [hfeas]
    · rw [hsdef, h, le_div_iff₀ hc]
      linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s 1)]
  have hfirst : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
      ≤ ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r := by
    have hle : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_mono_on hs0.le (hint 0 s)
        (hchordcont.intervalIntegrable _ _) ?_
      intro u hu
      obtain ⟨hu0, hus⟩ := hu
      have huv : A * u ≤ c := by
        have hut : u ≤ t₀ := le_trans hus (min_le_left _ _)
        rw [ht₀def, le_div_iff₀ hA] at hut
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (QQ_nonneg hfeas u) (QQ_le_chord hu0 huv) hr.le) (pow_nonneg hu0 k)
    refine hle.trans ?_
    have hrest : 0 ≤ ∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_nonneg hsc ?_
      intro u hu
      have : 0 ≤ 1 - c * u := by
        have := hu.2
        rw [le_div_iff₀ hc] at this
        linarith
      exact mul_nonneg (pow_nonneg (le_trans hs0.le hu.1) k) (Real.rpow_nonneg this _)
    have hadd : (∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r)
        + (∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r)
        = ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r :=
      intervalIntegral.integral_add_adjacent_intervals
        (hchordcont.intervalIntegrable 0 s) (hchordcont.intervalIntegrable s (1 / c))
    linarith
  have hsecond : (∫ u in s..1, u ^ k * QQ c A u ^ r) ≤ QQ c A 1 ^ r / (k + 1) := by
    have hBnn : (0 : ℝ) ≤ QQ c A 1 ^ r := Real.rpow_nonneg (QQ_nonneg hfeas 1) _
    have hQB : ∀ u ∈ Set.Icc s 1, QQ c A u ≤ QQ c A 1 := by
      intro u hu
      rcases le_or_gt t₀ u with h | h
      · rw [ht₀def, div_le_iff₀ hA] at h
        exact QQ_le_at_one hA.le (by linarith) hu.2
      · have hu1 : u = 1 := by
          rcases min_cases t₀ 1 with ⟨he, _⟩ | ⟨he, _⟩
          · rw [hsdef, he] at hu; linarith [hu.1]
          · rw [hsdef, he] at hu; linarith [hu.1, hu.2]
        rw [hu1]
    have hle : (∫ u in s..1, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in s..1, QQ c A 1 ^ r * u ^ k := by
      refine intervalIntegral.integral_mono_on hs1 (hint s 1)
        ((by fun_prop : Continuous fun u : ℝ => QQ c A 1 ^ r * u ^ k).intervalIntegrable _ _) ?_
      intro u hu
      have := Real.rpow_le_rpow (QQ_nonneg hfeas u) (hQB u hu) hr.le
      nlinarith [pow_nonneg (le_trans hs0.le hu.1) k, this, hBnn]
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hsk : (0 : ℝ) ≤ s ^ (k + 1) := pow_nonneg hs0.le _
    rw [one_pow, ← mul_div_assoc]
    gcongr
    nlinarith [mul_nonneg hBnn hsk]
  linarith
lemma integral_QQ_anti {c₁ c₂ A : ℝ} (hle : c₁ ≤ c₂) (hfeas : c₂ ^ 2 ≤ A) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c₂ A t ^ r)
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * QQ c₁ A t ^ r := by
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_pow_mul_QQ c₂ A k hr).intervalIntegrable _ _)
    ((continuous_pow_mul_QQ c₁ A k hr).intervalIntegrable _ _) ?_
  intro u hu
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu.1 k)
  refine Real.rpow_le_rpow (QQ_nonneg hfeas u) ?_ hr
  simp only [QQ]
  nlinarith [hu.1, hle]
theorem integral_le_tail_lin {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t * QQ c A t ^ r)
      ≤ 1 / (c ^ 2 * ((r + 1) * (r + 2))) + QQ c A 1 ^ r / 2 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 1
  simp only [pow_one] at h
  rw [integral_chord_lin hr hc, show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at h
  exact h
theorem integral_le_tail_cube {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * QQ c A t ^ r)
      ≤ 6 / (c ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4))) + QQ c A 1 ^ r / 4 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 3
  rw [integral_chord_pow hr hc, show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num] at h
  exact h
end Sendov
end

section
namespace Sendov
noncomputable def Ppolar (a x t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * t * x * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2
variable {n : ℕ} {a x t α : ℝ}
lemma Ppolar_eq (a x t : ℝ) :
    Ppolar a x t = (a + t * (1 - a ^ 2) * x) ^ 2 + t ^ 2 * (1 - a ^ 2) ^ 2 * (1 - x ^ 2) := by
  simp only [Ppolar]; ring
lemma Ppolar_nonneg (hx : x ^ 2 ≤ 1) (a t : ℝ) : 0 ≤ Ppolar a x t := by
  rw [Ppolar_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by linarith))
lemma continuous_Ppolar (a x : ℝ) : Continuous fun t : ℝ => Ppolar a x t := by
  simp only [Ppolar]; fun_prop
lemma A_eq_sq (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) : A n α = a ^ 2 := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [A, hα]
  field_simp
  ring
lemma alpha_pos (hn : 2 ≤ n) (ha1 : a < 1) (_ha0 : 0 ≤ a)
    (hα : α = M n * (1 - a ^ 2) / 2) : 0 < α := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  have : 0 < 1 - a ^ 2 := by nlinarith
  positivity
lemma alpha_le_half (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  nlinarith [sq_nonneg a]
end Sendov
end

section
namespace Sendov
open _root_.Polynomial MeasureTheory
lemma norm_sub_le_norm_one_sub_mul {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by
  have hkey : Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z)
      = (1 - a ^ 2) * (1 - Complex.normSq z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.1 ha
    nlinarith [this.1, this.2]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hdiff : 0 ≤ Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z) := by
    rw [hkey]
    have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 - Complex.normSq z := by linarith
    positivity
  have hsq : ‖(a : ℂ) - z‖ ^ 2 ≤ ‖1 - (a : ℂ) * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  nlinarith [norm_nonneg ((a : ℂ) - z), norm_nonneg (1 - (a : ℂ) * z), hsq]
lemma norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih => simp [ih]
lemma prod_map_le_of_le {s : Multiset ℂ} {f g : ℂ → ℂ} (h : ∀ w ∈ s, ‖f w‖ ≤ ‖g w‖) :
    (s.map (fun w => ‖f w‖)).prod ≤ (s.map (fun w => ‖g w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih =>
    have hw := h w (Multiset.mem_cons_self w t)
    have ht : ∀ u ∈ t, ‖f u‖ ≤ ‖g u‖ := fun u hu => h u (Multiset.mem_cons_of_mem hu)
    have hnn : (0 : ℝ) ≤ (t.map (fun u => ‖f u‖)).prod :=
      Multiset.prod_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact norm_nonneg _)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul hw (ih ht) hnn (norm_nonneg _)
lemma norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun w => ‖f w‖)).prod := by
  rw [norm_multiset_prod, Multiset.map_map]
  rfl
lemma prod_map_norm_nonneg (s : Multiset ℂ) (f : ℂ → ℂ) :
    0 ≤ (s.map (fun w => ‖f w‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg _
theorem one_le_integral_prod_norm {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hmob : (z.map (fun w => ‖(a : ℂ) - w‖)).prod
      ≤ (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod :=
    prod_map_le_of_le (fun w hw => norm_sub_le_norm_one_sub_mul ha (hz w hw))
  have h1 : (n : ℝ) = ‖q.prod‖ * (z.map (fun w => ‖(a : ℂ) - w‖)).prod := by
    have := congrArg (fun w : ℂ => ‖w‖) hdenom
    simpa [norm_mul, norm_prod_map] using this.symm
  have h2 : ‖q.prod‖ * (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod
      = (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) hpolar
    simpa [norm_mul, norm_prod_map] using this
  have h3 : (1 : ℝ) ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have hstep : (n : ℝ) ≤ (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hmob (norm_nonneg _)
    nlinarith [hstep, hnpos]
  refine h3.trans ?_
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
  refine intervalIntegral.integral_congr ?_
  intro t _
  simp only []
  exact norm_prod_map q _
lemma norm_sq_add_real_mul (a s : ℝ) (v : ℂ) :
    ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 = a ^ 2 + 2 * a * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
lemma prod_map_sq (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map (fun v => f v ^ 2)).prod = ((s.map f).prod) ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    ring
lemma sum_norm_sq_split (a s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) * a ^ 2 + 2 * a * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_add_real_mul]
    push_cast
    ring
lemma sum_norm_sq_le_card (q : Multiset ℂ) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) :
    (q.map (fun v => ‖v‖ ^ 2)).sum ≤ (q.card : ℝ) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    have hv := hq1 v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq1 u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    nlinarith [ih ht, norm_nonneg v]
lemma continuous_prod_norm (a : ℝ) (q : Multiset ℂ) :
    Continuous fun t : ℝ =>
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ =>
      ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖).mul ih
lemma prod_norm_le_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
      ≤ Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hNpos : (0 : ℝ) < (q.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set s : ℝ := t * (1 - a ^ 2) with hs
  have hcast : ∀ v : ℂ, (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v = (a : ℂ) + (s : ℂ) * v := by
    intro v
    rw [hs]
    push_cast
    ring
  simp only [hcast]
  set P : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖)).prod with hP
  have hP0 : 0 ≤ P := prod_map_norm_nonneg q _
  have hM0 : ∀ v ∈ q, (0 : ℝ) ≤ ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 := fun v _ => sq_nonneg _
  have hamgm := Multiset.prod_le_mean_pow (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2))
    (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  rw [Multiset.card_map, prod_map_sq] at hamgm
  set M : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum / (q.card : ℝ) with hM
  have hMle : M ≤ Ppolar a x t := by
    rw [hM, div_le_iff₀ hNpos]
    have hsplit := sum_norm_sq_split a s q
    have hcard2 := sum_norm_sq_le_card q hq1
    rw [hsplit, hx, hNcast]
    have hPp : Ppolar a x t = a ^ 2 + 2 * a * s * x + s ^ 2 := by
      rw [Ppolar, hs]; ring
    rw [hPp]
    nlinarith [hcard2, hNcast, sq_nonneg s, hNpos]
  have hM0' : 0 ≤ M := by
    rw [hM]
    apply div_nonneg _ (le_of_lt hNpos)
    exact Multiset.sum_nonneg (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  have hexp : ((q.card : ℕ) : ℝ) / 2 = ((n : ℝ) - 1) / 2 := by rw [hNcast]
  have hb : (0 : ℝ) ≤ Ppolar a x t := le_trans hM0' hMle
  have hsq : (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) ^ 2 = Ppolar a x t ^ (q.card : ℕ) := by
    rw [← Real.rpow_natCast (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) 2, ← Real.rpow_mul hb,
      ← Real.rpow_natCast (Ppolar a x t) q.card, hNcast]
    congr 1
    push_cast
    ring
  have hchain : P ^ 2 ≤ Ppolar a x t ^ (q.card : ℕ) := by
    refine hamgm.trans ?_
    exact pow_le_pow_left₀ hM0' hMle _
  rw [← hsq] at hchain
  nlinarith [hchain, hP0, Real.rpow_nonneg (le_trans hM0' hMle) (((n : ℝ) - 1) / 2)]
theorem one_le_integral_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine hstar.trans (intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    (((continuous_rpow_const he).comp (continuous_Ppolar a x)).intervalIntegrable _ _) ?_)
  intro u _
  exact prod_norm_le_Ppolar hn hqcard hq1 hx
end Sendov
end

section
namespace Sendov
open scoped Classical in
noncomputable def sumEraseProdMap {α : Type*} (s : Multiset α) (f : α → ℝ) : ℝ :=
  (s.map (fun j => ((s.erase j).map f).prod)).sum
open scoped Classical in
lemma sumEraseProdMap_cons {α : Type*} (v : α) (t : Multiset α) (f : α → ℝ) :
    sumEraseProdMap (v ::ₘ t) f = (t.map f).prod + f v * sumEraseProdMap t f := by
  simp only [sumEraseProdMap, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
theorem sumEraseProdMap_eq_esymm {α : Type*} : ∀ (s : Multiset α) (f : α → ℝ), s ≠ 0 →
    sumEraseProdMap s f = (s.map f).esymm ((s.map f).card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons v t ih =>
    intro f _
    rcases eq_or_ne t 0 with rfl | ht
    · simp [sumEraseProdMap, Multiset.esymm]
    · rw [sumEraseProdMap_cons, ih f ht, Multiset.map_cons, Multiset.card_cons]
      rw [show (t.map f).card + 1 - 1 = (t.map f).card from by omega]
      rw [esymm_card_cons (f v) (t.map f) (by simpa using ht)]
lemma norm_sq_one_add_real_mul (s : ℝ) (v : ℂ) :
    ‖1 + (s : ℂ) * v‖ ^ 2 = 1 + 2 * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring
lemma sum_norm_sq_one_sub_split (s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖1 + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) + 2 * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_one_add_real_mul]
    push_cast
    ring
theorem sum_norm_sq_one_sub_le {n : ℕ} {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hn : 1 ≤ n)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ ^ 2)).sum
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub hn]
    ring
  have hcast : ∀ v : ℂ, 1 - (a : ℂ) * (t : ℂ) * v = 1 + ((-(a * t) : ℝ) : ℂ) * v := by
    intro v
    push_cast
    ring
  simp only [hcast]
  rw [sum_norm_sq_one_sub_split, hx, hNcast]
  have hsum2 := sum_norm_sq_le_card q hq1
  rw [hNcast] at hsum2
  simp only [QQ]
  nlinarith [hsum2, sq_nonneg (a * t)]
lemma sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    (s.sum) ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have hb := hs b (Multiset.mem_cons_self b t)
    have ht : ∀ u ∈ t, 0 ≤ u := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · have hIH := ih ht
      have hcard : (0 : ℝ) < (t.card : ℕ) := by
        have := Multiset.card_pos.2 ht0
        exact_mod_cast this
      have hsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
      have hQ : (0 : ℝ) ≤ (t.map (fun b => b ^ 2)).sum :=
        Multiset.sum_nonneg (by
          intro y hy
          obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
          exact sq_nonneg u)
      simp only [Multiset.sum_cons, Multiset.card_cons, Multiset.map_cons]
      push_cast
      nlinarith [hIH, sq_nonneg (t.sum - (t.card : ℝ) * b), hcard, hsum, hb, hQ]
theorem sumEraseProdMap_norm_le {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖)
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set f : ℂ → ℝ := fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ with hf
  set bs : Multiset ℝ := q.map f with hbs
  have hbcard : bs.card = n - 1 := by rw [hbs, Multiset.card_map, hqcard]
  have hNcast : ((bs.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hbcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have hNpos : (0 : ℝ) < (bs.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbs0 : bs ≠ 0 := by
    rw [hbs]
    simpa using hq0
  have hbnn : ∀ b ∈ bs, 0 ≤ b := by
    intro b hb
    rw [hbs] at hb
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hb
    exact norm_nonneg _
  have hsumnn : 0 ≤ bs.sum := Multiset.sum_nonneg hbnn
  have hsq : (bs.map (fun b => b ^ 2)).sum ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
    rw [hbs, Multiset.map_map]
    exact sum_norm_sq_one_sub_le hqcard hq1 (by omega) hx
  have hβ0 : 0 ≤ QQ (a * x) (a ^ 2) t := by
    have hnn : (0 : ℝ) ≤ (bs.map (fun b => b ^ 2)).sum :=
      Multiset.sum_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact sq_nonneg u)
    nlinarith [hsq, hnn, hNcast, hNpos]
  have hcs : (bs.sum) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 * QQ (a * x) (a ^ 2) t := by
    have h := sq_sum_le_card_mul_sum_sq bs hbnn
    rw [hNcast] at h
    nlinarith [h, hsq, hNcast, hNpos]
  have hmean : bs.sum / (bs.card : ℕ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) := by
    rw [div_le_iff₀ hNpos, hNcast]
    have hsqrt : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ 2 = QQ (a * x) (a ^ 2) t :=
      Real.sq_sqrt hβ0
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by rw [← hNcast]; exact hNpos
    have hprodnn : (0 : ℝ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) * ((n : ℝ) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hn1)
    nlinarith [hcs, hsqrt, hsumnn, hprodnn, hn1]
  have hmac := Multiset.esymm_card_pred_le bs hbnn hbs0
  rw [sumEraseProdMap_eq_esymm q f hq0, ← hbs]
  refine hmac.trans ?_
  have hpow : (bs.sum / (bs.card : ℕ)) ^ (bs.card - 1)
      ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
    refine pow_le_pow_left₀ (by positivity) hmean _
  have hfin : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1)
      = QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (QQ (a * x) (a ^ 2) t ^ ((1 : ℝ) / 2))
      (bs.card - 1), ← Real.rpow_mul hβ0]
    congr 1
    have hcast2 : ((bs.card - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [hbcard]
      have h2 : n - 1 - 1 = n - 2 := by omega
      rw [h2]
      push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ n)]
      ring
    rw [hcast2]
    ring
  rw [hNcast] at *
  calc ((n : ℝ) - 1) * (bs.sum / ((n : ℝ) - 1)) ^ (bs.card - 1)
      ≤ ((n : ℝ) - 1) * Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← hNcast] at hpow ⊢
        exact hpow
    _ = ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by rw [hfin]
open scoped Classical in
noncomputable def sumEraseProdC (s : Multiset ℂ) (g f : ℂ → ℂ) : ℂ :=
  (s.map (fun j => g j * ((s.erase j).map f).prod)).sum
open scoped Classical in
@[simp] lemma sumEraseProdC_zero (g f : ℂ → ℂ) : sumEraseProdC 0 g f = 0 := by
  simp [sumEraseProdC]
open scoped Classical in
lemma sumEraseProdC_cons (v : ℂ) (t : Multiset ℂ) (g f : ℂ → ℂ) :
    sumEraseProdC (v ::ₘ t) g f = g v * (t.map f).prod + f v * sumEraseProdC t g f := by
  simp only [sumEraseProdC, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
  ring
lemma norm_sumEraseProdC_le (g f : ℂ → ℂ) : ∀ (s : Multiset ℂ), (∀ v ∈ s, ‖g v‖ ≤ 1) →
    ‖sumEraseProdC s g f‖ ≤ sumEraseProdMap s (fun v => ‖f v‖) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp [sumEraseProdMap]
  | cons v t ih =>
    intro hg
    have hv := hg v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖g u‖ ≤ 1 := fun u hu => hg u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProdC_cons, sumEraseProdMap_cons]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_prod_map]
    have h2 : (0 : ℝ) ≤ (t.map (fun v => ‖f v‖)).prod := prod_map_norm_nonneg t f
    nlinarith [ih ht, norm_nonneg (f v), norm_nonneg (sumEraseProdC t g f), h2, hv]
noncomputable def Fprod (a : ℝ) (q : Multiset ℂ) (t : ℝ) : ℂ :=
  (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod
@[simp] lemma Fprod_zero (a : ℝ) (q : Multiset ℂ) : Fprod a q 0 = 1 := by
  simp [Fprod]
lemma sumEraseProdC_id_eq (a t : ℝ) : ∀ (q : Multiset ℂ),
    sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
      = q.sum * Fprod a q t
        + (a : ℂ) * (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
            (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp [Fprod]
  | cons v r ih =>
    rw [sumEraseProdC_cons, sumEraseProdC_cons, ih, Multiset.sum_cons]
    simp only [Fprod, Multiset.map_cons, Multiset.prod_cons, id]
    ring
lemma hasDerivAt_Fprod (a t : ℝ) : ∀ (q : Multiset ℂ),
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    have he : Fprod a 0 = fun _ : ℝ => (1 : ℂ) := by funext s; simp [Fprod]
    have hz : -(a : ℂ) * sumEraseProdC 0 id (fun v => 1 - (a : ℂ) * (t : ℂ) * v) = 0 := by simp
    rw [he, hz]
    exact hasDerivAt_const t 1
  | cons v r ih =>
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 1 - (a : ℂ) * (s : ℂ) * v) (-((a : ℂ) * v)) t := by
      simpa using ((h0.const_mul (a : ℂ)).mul_const v).const_sub 1
    have h2 := h1.mul ih
    have hfun : Fprod a (v ::ₘ r)
        = fun s : ℝ => (1 - (a : ℂ) * (s : ℂ) * v) * Fprod a r s := by
      funext s
      simp only [Fprod, Multiset.map_cons, Multiset.prod_cons]
    have hderiv : -(a : ℂ) * ((v : ℂ) * (r.map (fun w => 1 - (a : ℂ) * (t : ℂ) * w)).prod
          + (1 - (a : ℂ) * (t : ℂ) * v) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w))
        = -((a : ℂ) * v) * Fprod a r t
          + (1 - (a : ℂ) * (t : ℂ) * v)
              * (-(a : ℂ) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w)) := by
      simp only [Fprod]
      ring
    rw [hfun, sumEraseProdC_cons, id_eq, hderiv]
    exact h2
theorem norm_deriv_add_le {n : ℕ} (hn : 2 ≤ n) {a x y t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (ha0 : 0 ≤ a) (ht0 : 0 ≤ t)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = (((n : ℝ) - 1) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
        + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
      ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set S : ℂ := sumEraseProdC q (fun v => v ^ 2) (fun v => 1 - (a : ℂ) * (t : ℂ) * v) with hS
  have hmain : (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
      + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t
      = -((a : ℂ) ^ 2 * (t : ℂ)) * S := by
    rw [sumEraseProdC_id_eq, hsum, ← hS]
    ring
  rw [hmain, norm_mul]
  have hnorm : ‖-((a : ℂ) ^ 2 * (t : ℂ))‖ = a ^ 2 * t := by
    simp [abs_of_nonneg ha0, abs_of_nonneg ht0]
  rw [hnorm]
  have hSle : ‖S‖ ≤ sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖) := by
    rw [hS]
    refine norm_sumEraseProdC_le _ _ q ?_
    intro v hv
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg v) (hq1 v hv)
  have hbd := sumEraseProdMap_norm_le (a := a) (x := x) (t := t) hn hqcard hq0 hq1 hx
  have hfac : (0 : ℝ) ≤ a ^ 2 * t := mul_nonneg (pow_nonneg ha0 2) ht0
  calc a ^ 2 * t * ‖S‖
      ≤ a ^ 2 * t * (((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
        mul_le_mul_of_nonneg_left (hSle.trans hbd) hfac
    _ = a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by ring
lemma continuous_prodC (a : ℝ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih
lemma continuous_Fprod (a : ℝ) (q : Multiset ℂ) : Continuous (Fprod a q) :=
  continuous_prodC a q
lemma continuous_sumEraseProdC (a : ℝ) (g : ℂ → ℂ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => sumEraseProdC q g (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    simp only [sumEraseProdC_zero]
    exact continuous_const
  | cons v r ih =>
    simp only [sumEraseProdC_cons]
    exact (continuous_const.mul (continuous_prodC a r)).add
      ((by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih)
theorem one_le_tri {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (ha0 : 0 ≤ a)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    1 ≤ ‖Fprod a q 1 + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)
            * ∫ t in (0 : ℝ)..1, Fprod a q t‖
        + a ^ 2 * ((n : ℝ) - 1)
            * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set c : ℂ := ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) with hc
  set D : ℝ → ℂ := fun t => -(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
    with hDdef
  have hDcont : Continuous D := by
    rw [hDdef]
    exact continuous_const.mul (continuous_sumEraseProdC a id q)
  have hFcont : Continuous (Fprod a q) := continuous_Fprod a q
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 1 := hDcont.intervalIntegrable _ _
  have hFint : IntervalIntegrable (Fprod a q) MeasureTheory.volume 0 1 :=
    hFcont.intervalIntegrable _ _
  have hFTC : ∫ t in (0 : ℝ)..1, D t = Fprod a q 1 - Fprod a q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_Fprod a t q) hDint
  have hG : ∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)
      = (Fprod a q 1 - 1) + c * ∫ t in (0 : ℝ)..1, Fprod a q t := by
    rw [intervalIntegral.integral_add hDint (hFint.const_mul c), hFTC, Fprod_zero,
      intervalIntegral.integral_const_mul]
  have hkey : (1 : ℂ) = (Fprod a q 1 + c * ∫ t in (0 : ℝ)..1, Fprod a q t)
      - ∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t) := by
    rw [hG]; ring
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hRcont : Continuous fun t : ℝ =>
      a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
    continuous_const.mul (continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hexp)
  have hGnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t + c * Fprod a q t‖
      ≤ a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    intro t ht
    have h := norm_deriv_add_le hn hqcard hq0 hq1 ha0 ht.1 hx hsum (t := t) (y := y)
    rw [hDdef, hc]
    calc ‖-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
            + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
        ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := h
      _ = a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by ring
  have hint : ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖
      ≤ a ^ 2 * ((n : ℝ) - 1)
          * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    have hni : IntervalIntegrable (fun t : ℝ => ‖D t + c * Fprod a q t‖)
        MeasureTheory.volume 0 1 :=
      (hDcont.add (continuous_const.mul hFcont)).norm.intervalIntegrable _ _
    have hri : IntervalIntegrable (fun t : ℝ =>
        a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)))
        MeasureTheory.volume 0 1 := hRcont.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hni hri hGnorm
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    simp
  have hnorm1 : ‖(1 : ℂ)‖ ≤ ‖Fprod a q 1 + c * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      + ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖ := by
    conv_lhs => rw [hkey]
    exact norm_sub_le _ _
  rw [norm_one] at hnorm1
  linarith [hnorm1, hint]
end Sendov
end

section
namespace Sendov
lemma sum_map_sub (s : Multiset ℂ) (f g : ℂ → ℂ) :
    (s.map (fun v => f v - g v)).sum = (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring
lemma sum_map_const_sub (s : Multiset ℂ) (c : ℂ) (g : ℂ → ℂ) :
    (s.map (fun v => c - g v)).sum = (s.card : ℂ) * c - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring
lemma sum_map_re (s : Multiset ℂ) : (s.map (fun v => v.re)).sum = s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih => simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, ih]
lemma norm_sum_map_le (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).sum‖ ≤ (s.map (fun w => ‖f w‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    linarith [norm_add_le (f v) ((t.map f).sum), ih]
lemma norm_prod_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, norm_mul]
    nlinarith [ih ht, norm_nonneg v, norm_nonneg t.prod]
lemma prod_mul_sum_inv : ∀ (s : Multiset ℂ), (∀ w ∈ s, w ≠ 0) →
    s.prod * (s.map (fun w => w⁻¹)).sum = sumEraseProd s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp [sumEraseProd]
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, u ≠ 0 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, sumEraseProd_cons, ← ih ht]
    field_simp
lemma sumEraseProd_norm_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → s.prod = 0 →
    ‖sumEraseProd s‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; simp at h
  | cons v t ih =>
    intro hs hp
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProd_cons]
    rcases eq_or_ne t.prod 0 with ht0 | ht0
    · rw [ht0, zero_add, norm_mul]
      nlinarith [ih ht ht0, norm_nonneg v, norm_nonneg (sumEraseProd t), hv]
    · have hv0 : v = 0 := by
        rw [Multiset.prod_cons] at hp
        rcases mul_eq_zero.1 hp with h | h
        · exact h
        · exact absurd h ht0
      rw [hv0, zero_mul, add_zero]
      exact norm_prod_le_one t ht
theorem Jsum_estimate {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {z q : Multiset ℂ}
    (hqcard : q.card = n - 1)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod)‖
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hratio : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hn1]; linarith
  have hqpnorm : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  rcases eq_or_ne z.prod 0 with hz0 | hz0
  · 
    rw [hz0, mul_zero, mul_zero, sub_zero, norm_zero, mul_zero, norm_mul]
    have h2 : ‖sumEraseProd z‖ ≤ 1 := sumEraseProd_norm_le_one z hz1 hz0
    nlinarith [norm_nonneg q.prod, norm_nonneg (sumEraseProd z)]
  · 
    have hzne : ∀ w ∈ z, w ≠ 0 := by
      intro w hw hw0
      exact hz0 (Multiset.prod_eq_zero (hw0 ▸ hw))
    set qc : Multiset ℂ := q.map (fun v => (starRingEnd ℂ) v) with hqc
    have hqcnorm : ∀ w ∈ qc, ‖w‖ ≤ 1 := by
      intro w hw
      rw [hqc] at hw
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hw
      simpa using hq1 v hv
    have hqsum : q.sum = (qc.map (fun w => (starRingEnd ℂ) w)).sum := by
      rw [hqc, Multiset.map_map]
      simp
    have hconj : ((n : ℂ) - 1) * ((a : ℂ) + (z.map (fun w => (starRingEnd ℂ) w)).sum)
        = (n : ℂ) * (((n : ℂ) - 1) * (a : ℂ) - (qc.map (fun w => w⁻¹)).sum) := by
      have h := congrArg (starRingEnd ℂ) hcent
      simp only [map_mul, map_sub, map_add, map_one, map_inv₀, map_natCast,
        Complex.conj_ofReal, map_multiset_sum, Multiset.map_map, Function.comp_def] at h
      rw [sum_map_const_sub, hqcard] at h
      have hcard : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
        ring
      rw [hcard] at h
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def]
      exact h
    have hSz : q.prod * sumEraseProd z = (q.prod * z.prod) * (z.map (fun w => w⁻¹)).sum := by
      rw [← prod_mul_sum_inv z hzne]; ring
    obtain ⟨E, hEdef⟩ : ∃ w : ℂ, w = q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod) := ⟨_, rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ w : ℂ, w = ((n : ℂ) - 1)
          * ((z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum)
        + (n : ℂ) * (q.sum - (qc.map (fun w => w⁻¹)).sum) := ⟨_, rfl⟩
    rw [← hEdef]
    have hE : ((n : ℂ) - 1) * E = (q.prod * z.prod) * X := by
      rw [hEdef, hXdef, hSz, hxy]
      linear_combination (q.prod * z.prod) * hconj
    have hdefect := defect (z + qc) (by
      intro w hw
      rcases Multiset.mem_add.1 hw with h | h
      · exact hz1 w h
      · exact hqcnorm w h)
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.sum_add] at hdefect
    have hzp : (z.map (fun w => ‖w‖)).prod = ‖z.prod‖ := (norm_multiset_prod z).symm
    have hqp : (qc.map (fun w => ‖w‖)).prod = ‖q.prod‖ := by
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def, RCLike.norm_conj]
      exact (norm_multiset_prod q).symm
    rw [hzp, hqp] at hdefect
    obtain ⟨Dz, hDz⟩ : ∃ r : ℝ, r = (z.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ r : ℝ, r = (qc.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    rw [← hDz, ← hDq] at hdefect
    have hDz0 : 0 ≤ Dz := by
      rw [hDz]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    have hDq0 : 0 ≤ Dq := by
      rw [hDq]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    have hbz : ‖(z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum‖ ≤ Dz := by
      rw [← sum_map_sub, hDz]
      exact norm_sum_map_le z _
    have hbq : ‖q.sum - (qc.map (fun w => w⁻¹)).sum‖ ≤ Dq := by
      have hneg : q.sum - (qc.map (fun w => w⁻¹)).sum
          = -((qc.map (fun w => w⁻¹ - (starRingEnd ℂ) w)).sum) := by
        rw [hqsum, sum_map_sub]
        ring
      rw [hneg, norm_neg, hDq]
      exact norm_sum_map_le qc _
    have hnorm : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
      have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
    have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    have hXle : ‖X‖ ≤ ((n : ℝ) - 1) * Dz + (n : ℝ) * Dq := by
      rw [hXdef]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hnorm, hnn]
      exact add_le_add (mul_le_mul_of_nonneg_left hbz (by linarith))
        (mul_le_mul_of_nonneg_left hbq (by positivity))
    have hkey : ((n : ℝ) - 1) * ‖E‖ = ‖q.prod‖ * ‖z.prod‖ * ‖X‖ := by
      have h := congrArg norm hE
      rw [norm_mul, norm_mul, norm_mul, hnorm] at h
      exact h
    have hP0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
    have hstep : ((n : ℝ) - 1) * ‖E‖ ≤ (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
      rw [hkey]
      calc ‖q.prod‖ * ‖z.prod‖ * ‖X‖
          ≤ ‖q.prod‖ * ‖z.prod‖ * (((n : ℝ) - 1) * Dz + (n : ℝ) * Dq) :=
            mul_le_mul_of_nonneg_left hXle hP0
        _ ≤ ‖q.prod‖ * ‖z.prod‖ * ((n : ℝ) * (Dz + Dq)) := by nlinarith [hDz0, hP0]
        _ = (n : ℝ) * (‖z.prod‖ * ‖q.prod‖ * (Dz + Dq)) := by ring
        _ ≤ (n : ℝ) * (1 - (‖z.prod‖ * ‖q.prod‖) ^ 2) := by
            have hnpos : (0 : ℝ) ≤ (n : ℝ) := by linarith
            exact mul_le_mul_of_nonneg_left hdefect hnpos
        _ = (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hn1]
    linarith [hstep]
end Sendov
end

section
namespace Sendov
open Complex (I)
lemma sum_norm_le_card : ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
    (q.map (fun v => ‖v‖)).sum ≤ (q.card : ℝ) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]
lemma norm_mul_two_re_le {w : ℂ} (_hs : 0 < w.re) :
    ‖w‖ * (2 * w.re) ≤ 2 * w.re ^ 2 + w.im ^ 2 := by
  have h1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg w, h1, sq_nonneg (w.im ^ 2), sq_nonneg (w.re * w.im)]
noncomputable def Worigin (n : ℕ) (a x y : ℝ) : ℂ :=
  (a : ℂ) ^ 2 * ((n : ℂ) - 1) + 1 - (a : ℂ) * ((x : ℂ) + (y : ℂ) * I)
lemma Worigin_eq (n : ℕ) (a x y : ℝ) :
    Worigin n a x y = ((a ^ 2 * ((n : ℝ) - 1) + 1 - a * x : ℝ) : ℂ)
      + ((-(a * y) : ℝ) : ℂ) * I := by
  simp only [Worigin]
  push_cast
  ring
lemma Worigin_re (n : ℕ) (a x y : ℝ) :
    (Worigin n a x y).re = a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by
  rw [Worigin_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
lemma Worigin_im (n : ℕ) (a x y : ℝ) : (Worigin n a x y).im = -(a * y) := by
  rw [Worigin_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
theorem grow {n : ℕ} (hn : 5 ≤ n) {a x y : ℝ} (ha0 : 0 < a) (hx : x ≤ 1) :
    2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ ‖Worigin n a x y‖ := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hu : (0 : ℝ) ≤ (n : ℝ) - 5 := by linarith
  have hdisc : 0 < 4 * ((n : ℝ) - 1) ^ 3 - (3 * (n : ℝ) - 1) ^ 2 := by
    nlinarith [hu, sq_nonneg ((n : ℝ) - 5), mul_nonneg (mul_nonneg hu hu) hu]
  have hquad : 0 < ((n : ℝ) - 1) ^ 2 * a ^ 2 - (3 * (n : ℝ) - 1) * a + ((n : ℝ) - 1) := by
    nlinarith [sq_nonneg (2 * ((n : ℝ) - 1) ^ 2 * a - (3 * (n : ℝ) - 1)), hdisc,
      mul_pos hn1 hn1]
  have hre : 2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ (Worigin n a x y).re := by
    rw [Worigin_re, div_le_iff₀ hn1]
    nlinarith [hquad, mul_nonneg (mul_nonneg (le_of_lt ha0) (sub_nonneg.2 hx)) (le_of_lt hn1)]
  exact hre.trans (Complex.re_le_norm _)
lemma collapse_J {K c P : ℝ} (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hcK : 2 * c ≤ K) :
    P * K + c * (1 - P ^ 2) ≤ K := by
  have hfac : 0 ≤ (1 - P) * (K - c * (1 + P)) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [hc0, hP1, hcK]
  nlinarith [hfac]
lemma norm_Worigin_le {n : ℕ} {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hn1 : (0 : ℝ) < (n : ℝ) - 1) (hxle : x ≤ 1) (hy2 : y ^ 2 ≤ 1 - x ^ 2) :
    ‖Worigin n a x y‖
      ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x + (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
  have hax : a * x ≤ a := mul_le_of_le_one_right (le_of_lt ha0) hxle
  have ha2 : (0 : ℝ) < a ^ 2 * ((n : ℝ) - 1) := by positivity
  have hslow : a ^ 2 * ((n : ℝ) - 1) ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by linarith
  have hpos : 0 < (Worigin n a x y).re := by rw [Worigin_re]; linarith
  have hs : (0 : ℝ) < 2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x) := by linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have h := norm_mul_two_re_le hpos
  rw [Worigin_re, Worigin_im] at h
  have hmain : ‖Worigin n a x y‖
      ≤ (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)
        + a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hs]
    nlinarith [h]
  have htail : a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x))
      ≤ (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hs hden]
    nlinarith [hy2, hslow, ha2, sq_nonneg y, hn1]
  linarith [hmain, htail]
lemma xy_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)) :
    (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x ∧ x ^ 2 + y ^ 2 ≤ 1 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnc : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
    have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
  have hqcardR : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  refine ⟨?_, ?_⟩
  · have hc : ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)
        = ((((n : ℝ) - 1) * x : ℝ) : ℂ) + ((((n : ℝ) - 1) * y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [sum_map_re, hxy, hc]
    simp
  · have hxynorm : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    have h2 : ‖q.sum‖ ≤ (q.map (fun v => ‖v‖)).sum := by
      have h := norm_sum_map_le q (fun v => v)
      simpa using h
    have h3 := sum_norm_le_card q hq1
    rw [hqcardR] at h3
    have h1 : ‖q.sum‖ ≤ (n : ℝ) - 1 := h2.trans h3
    rw [hxy, norm_mul, hnc] at h1
    have h4 : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [h1, hn1]
    nlinarith [hxynorm, h4, norm_nonneg ((x : ℂ) + (y : ℂ) * I)]
theorem origin_exact {n : ℕ} (hn : 5 ≤ n) {a x y α : ℝ} {z q : Multiset ℂ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I))
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hfirst : (n : ℂ) * ∫ t in (0 : ℝ)..1, Fprod a q t = (-1) ^ (n - 1) * q.prod * z.prod)
    (hsecond : (n : ℂ) * (q.map (fun v => 1 - (a : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z))
    (hα : α = M n * (1 - a ^ 2) / 2) :
    2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hxre, hx2⟩ := xy_bounds hn2 hqcard hq1 hxy
  have hxle : x ≤ 1 := by nlinarith [hx2, sq_nonneg y]
  have htri := one_le_tri hn2 hqcard hq0 hq1 (le_of_lt ha0) hxre hxy
  have hJ := Jsum_estimate (n := n) hn2 (a := a) (x := x) (y := y) hqcard hz1 hq1 hcent hxy
  have hF1 : Fprod a q 1 = (q.map (fun v => 1 - (a : ℂ) * v)).prod := by
    simp only [Fprod, Complex.ofReal_one, mul_one]
  have hsecond' : (n : ℂ) * Fprod a q 1
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z) := by
    rw [hF1]; exact hsecond
  have hf1aq : (n : ℂ) * (Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t)
      = (-1) ^ (n - 1) * ((q.prod * z.prod) * Worigin n a x y
        + (a : ℂ) * (q.prod * sumEraseProd z
            - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * I))
              * (q.prod * z.prod))) := by
    simp only [Worigin]
    linear_combination hsecond' + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * hfirst
  have hsign : ‖((-1 : ℂ)) ^ (n - 1)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  have hana : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0)]
  have hPJ0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
  have hPJ1 : ‖q.prod‖ * ‖z.prod‖ ≤ 1 := by
    have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
    have h2 : ‖z.prod‖ ≤ 1 := norm_prod_le_one z hz1
    nlinarith [norm_nonneg q.prod, norm_nonneg z.prod]
  have hstep1 : (n : ℝ) * ‖Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      ≤ ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
        + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
    have h := congrArg norm hf1aq
    rw [norm_mul, hnn, norm_mul, hsign, one_mul] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, hana]
    have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt ha0)
    linarith [hmul]
  have hgrow := grow (n := n) hn (a := a) (x := x) (y := y) ha0 hxle
  have hcoll : ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
      + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2)
      ≤ ‖Worigin n a x y‖ := by
    have hc : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) ≤ ‖Worigin n a x y‖ := by
      have he : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) = 2 * a * (n : ℝ) / ((n : ℝ) - 1) := by ring
      rw [he]; exact hgrow
    have hcnn : (0 : ℝ) ≤ a * ((n : ℝ) / ((n : ℝ) - 1)) := by positivity
    exact collapse_J hPJ1 hcnn hc
  have htri3 : (n : ℝ) ≤ ‖Worigin n a x y‖
      + (n : ℝ) * (a ^ 2 * ((n : ℝ) - 1)
        * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    have h := mul_le_mul_of_nonneg_left htri (le_of_lt hnpos)
    linarith [h, hstep1, hcoll]
  have hWle := norm_Worigin_le (n := n) (y := y) ha0 ha1 hn1 hxle (by linarith [hx2])
  simp only [M] at hα ⊢
  linarith [htri3, hWle, hα]
end Sendov
end

section
namespace Sendov
noncomputable def lowX (a t : ℝ) : ℝ := a + (1 - a ^ 2) * t
noncomputable def lowJ (m : ℕ) (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, lowX a t ^ m
lemma lowX_nonneg {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) : 0 ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  simp only [lowX]
  positivity
lemma continuous_lowX_pow (a : ℝ) (m : ℕ) : Continuous fun t : ℝ => lowX a t ^ m := by
  simp only [lowX]
  fun_prop
lemma norm_le_lowX {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) {v : ℂ}
    (hv : ‖v‖ ≤ 1) : ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖ ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hcast : (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v
      = ((a : ℝ) : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * v := by push_cast; ring
  rw [hcast]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg ht0 hb)]
  simp only [lowX]
  nlinarith [hv, norm_nonneg v, mul_nonneg ht0 hb]
lemma prod_norm_le_lowX_pow {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) :
    ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t ^ q.card := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v s ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v s)
    have hs : ∀ u ∈ s, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    have hX0 : 0 ≤ lowX a t := lowX_nonneg ha0 ha1 ht0
    have h3 : 0 ≤ (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod :=
      prod_map_norm_nonneg s _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖
          * (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t * lowX a t ^ s.card :=
          mul_le_mul (norm_le_lowX ha0 ha1 ht0 hv) (ih hs) h3 hX0
      _ = lowX a t ^ s.card * lowX a t := by ring
theorem one_le_lowJ {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ lowJ (n - 1) a := by
  refine hstar.trans ?_
  rw [lowJ]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    ((continuous_lowX_pow a (n - 1)).intervalIntegrable _ _) ?_
  intro u hu
  have h := prod_norm_le_lowX_pow ha0 ha1 hu.1 q hq1
  rwa [hqcard] at h
lemma lowJ_four (a : ℝ) :
    lowJ 4 a = a ^ 4 + 2 * a ^ 3 * (1 - a ^ 2) + 2 * a ^ 2 * (1 - a ^ 2) ^ 2
      + a * (1 - a ^ 2) ^ 3 + (1 - a ^ 2) ^ 4 / 5 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ =>
      a ^ 4 * s + 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2 + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3
        + a * (1 - a ^ 2) ^ 3 * s ^ 4 + (1 - a ^ 2) ^ 4 / 5 * s ^ 5) (lowX a t ^ 4) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a ^ 4 * s) (a ^ 4 * 1) t :=
      (hasDerivAt_id' (x := t)).const_mul _
    have h2 : HasDerivAt (fun s : ℝ => 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2)
        (2 * a ^ 3 * (1 - a ^ 2) * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (2 * a ^ 3 * (1 - a ^ 2))
    have h3 : HasDerivAt (fun s : ℝ => 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3)
        (2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2)) t := by
      simpa using (hasDerivAt_pow 3 t).const_mul (2 * a ^ 2 * (1 - a ^ 2) ^ 2)
    have h4 : HasDerivAt (fun s : ℝ => a * (1 - a ^ 2) ^ 3 * s ^ 4)
        (a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)) t := by
      simpa using (hasDerivAt_pow 4 t).const_mul (a * (1 - a ^ 2) ^ 3)
    have h5 : HasDerivAt (fun s : ℝ => (1 - a ^ 2) ^ 4 / 5 * s ^ 5)
        ((1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4)) t := by
      simpa using (hasDerivAt_pow 5 t).const_mul ((1 - a ^ 2) ^ 4 / 5)
    have hval : lowX a t ^ 4 = a ^ 4 * 1 + 2 * a ^ 3 * (1 - a ^ 2) * (2 * t)
        + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2) + a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)
        + (1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4) := by
      simp only [lowX]
      ring
    rw [hval]
    exact ((((h1.add h2).add h3).add h4).add h5)
  rw [lowJ, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((continuous_lowX_pow a 4).intervalIntegrable _ _)]
  norm_num
lemma lowJ_four_identity (a : ℝ) :
    1 - lowJ 4 a = ((1 - a) ^ 3 * (1 + a) / 5) * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  rw [lowJ_four]
  ring
lemma quartic_aux_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
  have hfactor : a ^ 4 - 3 * a ^ 3 + 3 * a + 4
      = 2 + 3 * a + (1 - a) * (2 + 2 * a + a ^ 2 * (2 - a)) := by ring
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 2 - a := by linarith
  rw [hfactor]
  positivity
lemma lowJ_four_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : lowJ 4 a < 1 := by
  have haux := quartic_aux_pos ha0 ha1
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 1 + a := by linarith
  rw [← sub_pos, lowJ_four_identity]
  positivity
lemma pow_le_quartic_average {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    x ^ m ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * x ^ 4 := by
  interval_cases m
  · 
    have hpos : (0 : ℝ) ≤ x ^ 2 + 2 * x + 3 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · 
    norm_num
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  · 
    have hpos : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x + 1 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · 
    norm_num
theorem lowJ_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    lowJ m a < 1 := by
  have hcont4 := continuous_lowX_pow a 4
  have hcontm := continuous_lowX_pow a m
  have hmaj : Continuous fun t : ℝ => 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4 :=
    continuous_const.add (hcont4.const_mul _)
  have hint : (∫ t in (0 : ℝ)..1, (1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4))
      = 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      ((hcont4.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul, lowJ]
    simp
  have hle : lowJ m a ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [lowJ, ← hint]
    refine intervalIntegral.integral_mono_on (by norm_num) (hcontm.intervalIntegrable _ _)
      (hmaj.intervalIntegrable _ _) ?_
    intro u hu
    exact pow_le_quartic_average (lowX_nonneg (le_of_lt ha0) (le_of_lt ha1) hu.1) hm0 hm4
  have h4 := lowJ_four_lt_one ha0 ha1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  nlinarith [hle, h4, hmpos]
theorem low_degree_contradiction {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    False := by
  have h1 := one_le_lowJ (n := n) (le_of_lt ha0) (le_of_lt ha1) hqcard hq1 hstar
  have h2 := lowJ_lt_one ha0 ha1 (m := n - 1) (by omega) (by omega)
  linarith
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
lemma Ppolar_le_lin (a x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) := by
  have hid : 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) - Ppolar a x t
      = (1 - a ^ 2) ^ 2 * (t - t ^ 2) := by
    simp only [Ppolar, QQ]; ring
  nlinarith [mul_nonneg (sq_nonneg (1 - a ^ 2)) (mul_nonneg ht0 (sub_nonneg.2 ht1))]
lemma Ppolar_rpow_le (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ^ (((n : ℝ) - 1) / 2)
      ≤ Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  set y : ℝ := (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) with hy
  have h1 : Ppolar a x t ≤ Real.exp y := by
    refine le_trans (Ppolar_le_lin a x ht0 ht1) ?_
    have := Real.add_one_le_exp y
    linarith
  have h2 : Ppolar a x t ^ (((n : ℝ) - 1) / 2) ≤ Real.exp y ^ (((n : ℝ) - 1) / 2) :=
    Real.rpow_le_rpow (Ppolar_nonneg hx a t) h1 he
  refine h2.trans_eq ?_
  rw [← Real.exp_mul]
  congr 1
  simp only [M] at hα
  rw [hy, hα]
  ring
theorem polar_exp (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  have hc1 : Continuous fun t : ℝ => Ppolar a x t ^ (((n : ℝ) - 1) / 2) :=
    (continuous_rpow_const he).comp (continuous_Ppolar a x)
  have hc2 : Continuous fun t : ℝ =>
      Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by fun_prop
  refine hpolar.trans (intervalIntegral.integral_mono_on (by norm_num)
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _) ?_)
  intro u hu
  exact Ppolar_rpow_le hn hx hα hu.1 hu.2
end Sendov
end

section
namespace Sendov
open Real Set Filter
private lemma nonneg_of_deriv {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  simpa [h0] using hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
private lemma quad_le_exp {y : ℝ} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ exp y := by
  suffices 0 ≤ exp y - 1 - y - y ^ 2 / 2 by linarith
  refine nonneg_of_deriv (f := fun t => exp t - 1 - t - t ^ 2 / 2)
    (g := fun t => exp t - 1 - t) (fun t => ?_) (by norm_num) (fun t ht => ?_) hy
  · exact ((((hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id' t)).sub
      ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv (by norm_num)
  · linarith [add_one_le_exp t]
private noncomputable def Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) : ℝ :=
  exp (2 * y) * (u₃ * y ^ 3 + u₂ * y ^ 2 + u₁ * y + u₀)
    - exp y * (v₄ * y ^ 4 + v₃ * y ^ 3 + v₂ * y ^ 2 + v₁ * y + v₀)
    - (w₃ * y ^ 3 + w₂ * y ^ 2 + w₁ * y + w₀)
private lemma hasDerivAt_Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) :
    HasDerivAt (fun t : ℝ => Sf u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ t)
      (Sf (2 * u₃) (2 * u₂ + 3 * u₃) (2 * u₁ + 2 * u₂) (2 * u₀ + u₁)
          v₄ (v₃ + 4 * v₄) (v₂ + 3 * v₃) (v₁ + 2 * v₂) (v₀ + v₁)
          0 (3 * w₃) (2 * w₂) w₁ y) y := by
  simp only [Sf]
  have he2 : HasDerivAt (fun t : ℝ => exp (2 * t)) (exp (2 * y) * 2) y :=
    ((hasDerivAt_id' y).const_mul (2 : ℝ)).exp.congr_deriv (by ring)
  have he1 : HasDerivAt (fun t : ℝ => exp t) (exp y) y := hasDerivAt_exp y
  have hu : HasDerivAt (fun t : ℝ => u₃ * t ^ 3 + u₂ * t ^ 2 + u₁ * t + u₀)
      (3 * u₃ * y ^ 2 + 2 * u₂ * y + u₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul u₃).add
      ((hasDerivAt_pow 2 y).const_mul u₂)).add ((hasDerivAt_id' y).const_mul u₁)).add_const u₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hv : HasDerivAt (fun t : ℝ => v₄ * t ^ 4 + v₃ * t ^ 3 + v₂ * t ^ 2 + v₁ * t + v₀)
      (4 * v₄ * y ^ 3 + 3 * v₃ * y ^ 2 + 2 * v₂ * y + v₁) y := by
    have h := (((((hasDerivAt_pow 4 y).const_mul v₄).add
      ((hasDerivAt_pow 3 y).const_mul v₃)).add
      ((hasDerivAt_pow 2 y).const_mul v₂)).add ((hasDerivAt_id' y).const_mul v₁)).add_const v₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hw : HasDerivAt (fun t : ℝ => w₃ * t ^ 3 + w₂ * t ^ 2 + w₁ * t + w₀)
      (3 * w₃ * y ^ 2 + 2 * w₂ * y + w₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul w₃).add
      ((hasDerivAt_pow 2 y).const_mul w₂)).add ((hasDerivAt_id' y).const_mul w₁)).add_const w₀
    refine h.congr_deriv ?_
    norm_num
    ring
  exact (((he2.mul hu).sub (he1.mul hv)).sub hw).congr_deriv (by ring)
private lemma step8 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0 y := by
  have : (1 + y + y ^ 2 / 2) * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560) := by
    grw [quad_le_exp hy]
    nlinarith [sq_nonneg (y - 1), pow_nonneg hy 3, sq_nonneg y]
  have : (0 : ℝ) ≤ 56 + 448 * y + 928 * y ^ 2 + 480 * y ^ 3 + 511 * y ^ 4 + 128 * y ^ 5 := by
    nlinarith [pow_nonneg hy 5, pow_nonneg hy 4, pow_nonneg hy 3, sq_nonneg y, hy]
  have h3 : (0 : ℝ) ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      - (2504 + 1600 * y + 352 * y ^ 2 + 32 * y ^ 3 + 1 * y ^ 4) := by nlinarith
  calc
    _ ≤ _ := mul_nonneg (exp_pos y).le h3
    _ = _ := by
        simp only [Sf, two_mul, exp_add]
        ring
private lemma step7 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0)
    (fun z => ?_) ?_ step8 hy
  · exact (hasDerivAt_Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 z).congr_deriv
      (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step6 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0)
    (fun z => ?_) ?_ step7 hy
  · exact (hasDerivAt_Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step5 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0)
    (fun z => ?_) ?_ step6 hy
  · exact (hasDerivAt_Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step4 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0)
    (fun z => ?_) ?_ step5 hy
  · exact (hasDerivAt_Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step3 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 y := by
  refine nonneg_of_deriv (g := Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0)
    (fun z => ?_) ?_ step4 hy
  · exact (hasDerivAt_Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step2 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 y := by
  refine nonneg_of_deriv (g := Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6)
    (fun z => ?_) ?_ step3 hy
  · exact (hasDerivAt_Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step1 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 y := by
  refine nonneg_of_deriv (g := Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20)
    (fun z => ?_) ?_ step2 hy
  · exact (hasDerivAt_Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step0 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 y := by
  refine nonneg_of_deriv (g := Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36)
    (fun z => ?_) ?_ step1 hy
  · exact (hasDerivAt_Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma Sf_eq (h : ℝ) :
    Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 (2 * h)
    = 16 * exp h ^ 2 * (h ^ 4 * sinh h ^ 2 - (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2) := by
  have : exp h ≠ 0 := (exp_pos h).ne'
  have e4 : exp (2 * (2 * h)) = exp h ^ 4 := by simp [←exp_nat_mul]; ring
  have e2 : exp (2 * h) = exp h ^ 2 := by simp [←exp_nat_mul]
  simp only [Sf, sinh_eq, cosh_eq, e4, e2, exp_neg]
  field_simp
  ring
theorem sinh_sq_le {h : ℝ} (hh : 0 ≤ h) :
    (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2 ≤ h ^ 4 * sinh h ^ 2 := by
  have h0 := step0 (2 * h) (by linarith)
  rw [Sf_eq] at h0
  have : (0 : ℝ) < 16 * exp h ^ 2 := by positivity
  nlinarith
private lemma sinh_le_mul_cosh {h : ℝ} (hh : 0 ≤ h) : sinh h ≤ h * cosh h := by
  have : 0 ≤ h * cosh h - sinh h := by
    refine nonneg_of_deriv (f := fun t => t * cosh t - sinh t) (g := fun t => t * sinh t)
      (fun t => ?_) (by simp) (fun t ht => mul_nonneg ht (sinh_nonneg_iff.2 ht)) hh
    exact (((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)).congr_deriv
      (by ring)
  linarith
theorem sqrt_mul_sub_le {h : ℝ} (hh : 0 ≤ h) :
    sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) ≤ h ^ 2 * sinh h := by
  have : (0 : ℝ) ≤ h ^ 2 * sinh h := mul_nonneg (sq_nonneg h) (sinh_nonneg_iff.2 hh)
  have : (0 : ℝ) ≤ sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) :=
    mul_nonneg (sqrt_nonneg _) (by linarith [sinh_le_mul_cosh hh])
  have : (sqrt (h ^ 2 + 9) * (h * cosh h - sinh h)) ^ 2 ≤ (h ^ 2 * sinh h) ^ 2 := by
    convert sinh_sq_le hh
    · rw [mul_pow, sq_sqrt (by positivity)]
    ·  ring
  nlinarith
theorem log_sinh_div_le {h : ℝ} (hh : 0 < h) :
    log (sinh h / h) ≤ sqrt (h ^ 2 + 9) - 3 := by
  set ψ : ℝ → ℝ := fun z => sqrt (z ^ 2 + 9) - 3 - (log (sinh z) - log z) with hψdef
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt ψ (z / sqrt (z ^ 2 + 9) - (cosh z / sinh z - 1 / z)) z := by
    intro z hz
    have hsinh : sinh z ≠ 0 := ne_of_gt (sinh_pos_iff.2 hz)
    apply HasDerivAt.sub
    · have h := (((hasDerivAt_pow 2 z).add_const 9).sqrt (ne_of_gt (by positivity))).sub_const 3
      refine h.congr_deriv ?_
      field_simp
      ring
    · exact (((hasDerivAt_sinh z).log hsinh).sub
        ((hasDerivAt_id' z).log (ne_of_gt hz))).congr_deriv (by field_simp)
  have hmono : MonotoneOn ψ (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun z hz => (hderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (by rwa [interior_Ioi] at hz)).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_)
    rw [interior_Ioi, mem_Ioi] at hz
    rw [(hderiv z hz).deriv, sub_nonneg, div_sub_div _ _ (ne_of_gt (sinh_pos_iff.2 hz))
      (ne_of_gt hz), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sqrt_mul_sub_le (le_of_lt hz)]
  have hslope : Tendsto (fun z => sinh z / z) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    simpa [slope_fun_def, div_eq_inv_mul, hasDerivAt_iff_tendsto_slope] using hasDerivAt_sinh 0
  have hlog : Tendsto ψ (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsub : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun z hz => ne_of_gt hz)
    have h1 : Tendsto (fun z => log (sinh z / z)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp
        (hslope.mono_left hsub)
    have h2 : Tendsto (fun z : ℝ => sqrt (z ^ 2 + 9) - 3)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h9 : sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
      have hc : ContinuousAt (fun z => sqrt (z ^ 2 + 9) - 3) 0 := by fun_prop
      simpa [ContinuousWithinAt, h9] using hc.continuousWithinAt (s := Ioi (0 : ℝ))
    have heq : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0),
        ψ z = (sqrt (z ^ 2 + 9) - 3) - log (sinh z / z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hψdef, log_div (ne_of_gt (sinh_pos_iff.2 hz)) (ne_of_gt hz)]
    simpa [tendsto_congr' heq] using h2.sub h1
  have hev : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0), ψ z ≤ ψ h := by
    have hmem : Ioo (0 : ℝ) h ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
      mem_nhdsGT_iff_exists_Ioo_subset.2 (Exists.intro h (And.intro (mem_Ioi.2 hh) subset_rfl))
    filter_upwards [hmem] with z hz
    exact hmono (mem_Ioi.2 hz.1) (mem_Ioi.2 hh) (le_of_lt hz.2)
  have h0 : (0 : ℝ) ≤ ψ h := le_of_tendsto hlog hev
  have : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hh) hh
  rw [hψdef] at h0
  rw [log_div (ne_of_gt (sinh_pos_iff.2 hh)) (ne_of_gt hh)]
  linarith
theorem sinh_le_mul_exp {h : ℝ} (hh : 0 ≤ h) :
    sinh h ≤ h * exp (sqrt (h ^ 2 + 9) - 3) := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · simp
  · have hd : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hpos) hpos
    grw [← (log_le_iff_le_exp hd).1 (log_sinh_div_le hpos)]
    field_simp
    simp
end Sendov
end

section
namespace Sendov
open MeasureTheory Real
variable {α B c : ℝ}
lemma integral_exp_mul (hc : c ≠ 0) (a b : ℝ) :
    (∫ t in a..b, exp (c * t)) = (exp (c * b) - exp (c * a)) / c := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b) (fun y : ℝ => exp y) hc
  rw [h, integral_exp]
  simp only [smul_eq_mul]
  field_simp
lemma integral_exp_eq (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = exp (-(α * B / 2)) * (sinh (α * (2 - B) / 2) / (α * (2 - B) / 2)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hEF : exp (-(α * B / 2)) = exp (-α) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : exp (α * (2 - B) * 1) = exp (α * (2 - B) / 2) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hneg : exp (-(α * (2 - B) / 2)) = (exp (α * (2 - B) / 2))⁻¹ := Real.exp_neg _
  have hF : exp (α * (2 - B) / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.sinh_eq, hEF, hsq, hneg]
  field_simp
lemma integral_exp_eq' (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = (exp (α * (1 - B)) - exp (-α)) / (α * (2 - B)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hsum : exp (-α) * exp (α * (2 - B) * 1) = exp (α * (1 - B)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hsum]
  field_simp
lemma beta_lt_two (hα : 0 < α)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B < 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono : (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      ≤ ∫ _t in (0 : ℝ)..1, exp (-α) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous fun t : ℝ =>
        exp (α * (-1 + (2 - B) * t))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun _ : ℝ => exp (-α)).intervalIntegrable _ _) ?_
    intro u hu
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg (mul_nonneg hα.le hu.1) (sub_nonneg.2 hcon)]
  have hval : (∫ _t in (0 : ℝ)..1, exp (-α)) = exp (-α) := by simp
  have hone : exp (-α) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  rw [hval] at hmono
  linarith
theorem beta_le (hα : 0 < α) (hB0 : 0 ≤ B)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B ≤ α / (3 + α) := by
  have hB2 : B < 2 := beta_lt_two hα hlt
  rw [integral_exp_eq hα hB2] at hlt
  set u : ℝ := α * B / 2 with hudef
  set h : ℝ := α * (2 - B) / 2 with hhdef
  have hhpos : 0 < h := by
    rw [hhdef]
    have : 0 < 2 - B := by linarith
    positivity
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have h1 : exp u ≤ sinh h / h := by
    rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos u)] at hlt
    linarith
  have h2 : u ≤ Real.log (sinh h / h) := by
    rw [← Real.log_exp u]
    exact Real.log_le_log (Real.exp_pos u) h1
  have h3 : u ≤ Real.sqrt (h ^ 2 + 9) - 3 := h2.trans (log_sinh_div_le hhpos)
  have hhu : h = α - u := by rw [hhdef, hudef]; ring
  have hsq : Real.sqrt (h ^ 2 + 9) ^ 2 = h ^ 2 + 9 := Real.sq_sqrt (by positivity)
  have h4 : (u + 3) ^ 2 ≤ h ^ 2 + 9 := by
    have hnn : (0 : ℝ) ≤ u + 3 := by linarith
    nlinarith [h3, hsq, Real.sqrt_nonneg (h ^ 2 + 9)]
  have h5 : u * (6 + 2 * α) ≤ α ^ 2 := by rw [hhu] at h4; nlinarith [h4]
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 + α)]
  rw [hudef] at h5
  nlinarith [h5, hα]
theorem log_le_alpha_mul (hα : 0 < α) (hB1 : B ≤ 1)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) :
    Real.log α ≤ α * (1 - B) := by
  have hB2 : B < 2 := by linarith
  rw [integral_exp_eq' hα hB2] at hlt
  have hden : (0 : ℝ) < α * (2 - B) := by
    have : (0 : ℝ) < 2 - B := by linarith
    positivity
  rw [le_div_iff₀ hden, one_mul] at hlt
  have hge : α ≤ α * (2 - B) := by nlinarith
  have hlt' : α < exp (α * (1 - B)) := by
    have := Real.exp_pos (-α)
    linarith
  exact (Real.log_le_iff_le_exp hα).2 hlt'.le
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}
lemma mul_eq_c (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    a * x = 1 - QQ (a * x) (a ^ 2) 1 / 2 - α / M n := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [QQ, hα]
  field_simp
  ring
lemma c_le_mul (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ≤ a * x := by
  rw [mul_eq_c hn hα]
  simp only [c]
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have : α / (2 * (3 + α)) = (α / (3 + α)) / 2 := by field_simp
  rw [this]
  linarith
lemma feasible_of_beta (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ^ 2 ≤ A n α := by
  have hcpos : 0 < c n α := c_pos_of_le_half_M hn hα0.le (alpha_le_half hn hα)
  have hcle : c n α ≤ a * x := c_le_mul hn hα hα0 hbeta
  rw [A_eq_sq hn hα]
  nlinarith [hcpos, hcle, sq_nonneg a, sq_nonneg x]
theorem stat_of_one_le (hn : 5 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (h1le : 1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :
    1 ≤ R n α := by
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hA : A n α = a ^ 2 := A_eq_sq hn2 hα
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have hkey : B1 * (3 + α) ≤ α := by
    rw [← le_div_iff₀ h3]; exact hbeta
  have hB1lt : B1 < 1 := by nlinarith [hα0, hB0]
  have t1 : B1 / (2 * α * (1 - B1)) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [hkey, hB0, hα0]
  have t2 : B1 / (4 * α) ≤ 1 / (4 * (3 + α)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hkey]
  have t4 : B1 / (4 * α * M n) ≤ 1 / (4 * M n * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hM]
  have hcle : c n α ≤ a * x := c_le_mul hn2 hα hα0 hbeta
  have hr : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hI : (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (c n α) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) :=
    integral_QQ_anti hcle hfeas hr 3
  have hInn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfeas u) _)
  have hpre : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    positivity
  have t5 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2) := by
    have hcoef : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hkey, hpre]
    have hstep1 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
      mul_le_mul_of_nonneg_right hcoef hInn
    refine hstep1.trans ?_
    have hcnn : (0 : ℝ) ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA]; positivity
    refine mul_le_mul_of_nonneg_left ?_ hcnn
    simpa only [Q_eq_QQ, hA] using hI
  rw [R]
  linarith
end Sendov
end

section
namespace Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
lemma rpow_add_le_of_one_le {P Q p : ℝ} (hP : 0 ≤ P) (hPQ : 0 < P + Q) (hp : 1 ≤ p) :
    (P + Q) ^ p ≤ P ^ p + p * Q * (P + Q) ^ (p - 1) := by
  have hθ : (0 : ℝ) ≤ P / (P + Q) := div_nonneg hP hPQ.le
  have hb := one_add_mul_self_le_rpow_one_add (s := P / (P + Q) - 1) (by linarith) hp
  rw [show (1 : ℝ) + (P / (P + Q) - 1) = P / (P + Q) by ring] at hb
  have hpow : (0 : ℝ) < (P + Q) ^ p := Real.rpow_pos_of_pos hPQ p
  have hfrac : (P / (P + Q)) ^ p * (P + Q) ^ p = P ^ p := by
    rw [← Real.mul_rpow hθ hPQ.le]
    congr 1
    field_simp
  have hsub : (P + Q) ^ (p - 1) = (P + Q) ^ p / (P + Q) := by
    rw [Real.rpow_sub hPQ, Real.rpow_one]
  have key : (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q)) ≤ P ^ p := by
    calc (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q))
        = (1 + p * (P / (P + Q) - 1)) * (P + Q) ^ p := by
          field_simp
          ring
      _ ≤ (P / (P + Q)) ^ p * (P + Q) ^ p := mul_le_mul_of_nonneg_right hb hpow.le
      _ = P ^ p := hfrac
  rw [hsub]
  linarith
lemma one_sub_mul_pos (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < 1 - a * x * t := by
  rcases le_or_gt x 0 with h | h
  · nlinarith [mul_nonneg ht0 (mul_nonneg ha.le (neg_nonneg.2 h))]
  · have hx1 : x ≤ 1 := by nlinarith
    have h1 : a * x * t ≤ a * x * 1 :=
      mul_le_mul_of_nonneg_left ht1 (mul_pos ha h).le
    nlinarith [h1]
lemma beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)
      ≤ (1 - a * x * t) ^ ((n : ℝ) - 2)
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * t ^ 2 * (1 - x ^ 2))
          * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) < 1 - a * x * t := one_sub_mul_pos ha ha1 hx ht0 ht1
  have hP : (0 : ℝ) ≤ (1 - a * x * t) ^ 2 := sq_nonneg _
  have hQ : (0 : ℝ) ≤ a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    have : (0 : ℝ) ≤ 1 - x ^ 2 := by linarith
    positivity
  have hsum : QQ (a * x) (a ^ 2) t
      = (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    rw [QQ_eq]; ring
  have hPQ : (0 : ℝ) < (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by positivity
  have hp : (1 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hb := rpow_add_le_of_one_le hP hPQ hp
  rw [← hsum] at hb
  have hchord : ((1 - a * x * t) ^ 2 : ℝ) ^ (((n : ℝ) - 2) / 2)
      = (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast (1 - a * x * t) 2, ← Real.rpow_mul hy.le]
    congr 1
    push_cast
    ring
  have hexp : ((n : ℝ) - 2) / 2 - 1 = ((n : ℝ) - 4) / 2 := by ring
  rw [hchord, hexp] at hb
  exact hb
lemma integral_beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hax : 0 < a * x) :
    (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
          * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hr2 : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hr4 : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by linarith
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  have hc1 : Continuous fun t : ℝ => t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    simpa using continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hr2
  have hc2 : Continuous fun t : ℝ => t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
    (by fun_prop : Continuous fun t : ℝ => t).mul
      ((continuous_rpow_const hs.le).comp (by fun_prop))
  have hc3 : Continuous fun t : ℝ =>
      ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
        * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
    (continuous_pow_mul_QQ (a * x) (a ^ 2) 3 hr4).const_mul _
  have hstep : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + ∫ t in (0 : ℝ)..1, ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
            * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) := by
    rw [← intervalIntegral.integral_add (hc2.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable _ _)
      ((hc2.add hc3).intervalIntegrable _ _) ?_
    intro u hu
    have h := beta_split hn ha ha1 hx hu.1 hu.2
    have hu0 : (0 : ℝ) ≤ u := hu.1
    nlinarith [h, hu0, Real.rpow_nonneg (QQ_nonneg (by nlinarith [sq_nonneg a] :
      (a * x) ^ 2 ≤ a ^ 2) u) (((n : ℝ) - 4) / 2)]
  refine hstep.trans ?_
  rw [intervalIntegral.integral_const_mul]
  gcongr
  have hrest : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
      ≤ ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    have hone : (1 : ℝ) ≤ 1 / (a * x) := by rw [le_div_iff₀ hax]; linarith
    have hadd : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + (∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        = ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hc2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
    have hnn : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
      refine intervalIntegral.integral_nonneg hone ?_
      intro u hu
      have : (0 : ℝ) ≤ 1 - a * x * u := by
        have := hu.2
        rw [le_div_iff₀ hax] at this
        linarith
      exact mul_nonneg (by linarith [hu.1]) (Real.rpow_nonneg this _)
    linarith
  refine hrest.trans_eq ?_
  rw [integral_chord_lin hs hax]
  congr 1
  ring
theorem one_le_of_origin (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hB1lt : QQ (a * x) (a ^ 2) 1 < 1)
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hMn : M n = (n : ℝ) - 1 := rfl
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set I3 : ℝ := ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) with hI3def
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  have hxsq : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
  have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
  have hinv : 1 / x ^ 2 ≤ 1 / (1 - B1) := by
    apply one_div_le_one_div_of_le (by linarith) hxsq
  have hone_sub : 1 - x ^ 2 ≤ B1 := by linarith
  have hsplit := integral_beta_split hn ha ha1 hx hax
  have hI3nn : (0 : ℝ) ≤ I3 := by
    rw [hI3def]
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    have hfe : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfe u) _)
  have hcoef : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hbeta_simp : a ^ 2 * (n : ℝ) * M n
      * (1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))) = 1 / x ^ 2 := by
    have hane : (a : ℝ) ≠ 0 := ha.ne'
    have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
    have hn1 : ((n : ℝ) - 1) ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    rw [hMn]
    field_simp
  have hkey : a ^ 2 * n * M n
        * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / x ^ 2 + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3 := by
    refine (mul_le_mul_of_nonneg_left hsplit hcoef).trans_eq ?_
    rw [mul_add, hbeta_simp]
    congr 1
    ring
  have hax_eq : a * x = 1 - B1 / 2 - α / M n := mul_eq_c hn2 hα
  have hmain : 2 * α ≤ B1 / (1 - B1) + B1 / 2 + α / M n + B1 / (2 * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    have hlast : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3
        ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
      have hc : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) / 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
        positivity
      nlinarith [mul_nonneg (mul_nonneg hc (sub_nonneg.2 hone_sub)) hI3nn]
    have hfirst : (1 - x ^ 2) / (2 * M n) ≤ B1 / (2 * M n) := by
      apply div_le_div_of_nonneg_right hone_sub (by positivity)
    have hne1 : (1 : ℝ) - B1 ≠ 0 := by linarith
    have hrec : 1 / (1 - B1) = 1 + B1 / (1 - B1) := by
      field_simp
      ring
    have hinv' : 1 / x ^ 2 ≤ 1 + B1 / (1 - B1) := by rw [← hrec]; exact hinv
    linarith [horigin, hkey, hinv', hfirst, hlast, hax_eq]
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hne : (1 : ℝ) - B1 ≠ 0 := by linarith
  have h1 : 2 * α * (B1 / (2 * α * (1 - B1))) = B1 / (1 - B1) := by
    field_simp
  have h2 : 2 * α * (B1 / (4 * α)) = B1 / 2 := by
    field_simp
    ring
  have h3 : 2 * α * (1 / (2 * M n)) = α / M n := by
    field_simp
  have h4 : 2 * α * (B1 / (4 * α * M n)) = B1 / (2 * M n) := by
    field_simp
    ring
  have h5 : 2 * α * ((a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / (4 * α) * I3)
      = (a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ h2α
  rw [mul_one, mul_add, mul_add, mul_add, mul_add, h1, h2, h3, h4, h5]
  exact hmain
end Sendov
end

section
namespace Sendov
open MeasureTheory Real
lemma quartic_le_exp {z : ℝ} (hz : 0 ≤ z) : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 ≤ exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith
lemma log_le_div_exp_one {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := t / exp 1) (by positivity)
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith
lemma exp_le_one_div_one_sub {z : ℝ} (hz : z < 1) : exp z ≤ 1 / (1 - z) := by
  have hpos := Real.exp_pos z
  have h1 : (0 : ℝ) < 1 - z := by linarith
  have h := Real.add_one_le_exp (-z)
  rw [Real.exp_neg] at h
  have h2 : (1 - z) * exp z ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  rw [le_div_iff₀ h1]
  linarith
lemma log_seventeen_ge : (2.83 : ℝ) ≤ Real.log 17 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hfrac : (1 : ℝ) - 16 / 17 ≤ Real.log (17 / 16) := by
    have h := Real.log_le_sub_one_of_pos (x := (16 : ℝ) / 17) (by norm_num)
    rw [show (16 : ℝ) / 17 = ((17 : ℝ) / 16)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hsplit : Real.log 17 = Real.log 16 + Real.log (17 / 16) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit, h16]
  linarith
lemma tail_poly_bound {v : ℝ} (hv : 0 ≤ v) :
    v * (2 * (v + 1) + 1 / 17) * exp (-(2.83 * v)) ≤ 0.4118 := by
  have hz : (0 : ℝ) ≤ 2.83 * v := by linarith
  have hexp := quartic_le_exp hz
  have hpos : (0 : ℝ) < exp (2.83 * v) := Real.exp_pos _
  have hneg : exp (-(2.83 * v)) = (exp (2.83 * v))⁻¹ := Real.exp_neg _
  rw [hneg, mul_inv_le_iff₀ hpos]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 0.4118))
  nlinarith [hv, sq_nonneg v, sq_nonneg (v - 1 / 2), pow_nonneg hv 3]
set_option maxHeartbeats 1000000 in
theorem alpha_le_seventeen {n : ℕ} {a x α : ℝ} (hn : 5 ≤ n)
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    α ≤ 17 := by
  by_contra hcon
  rw [not_le] at hcon
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hα0 : (0 : ℝ) < α := by linarith
  have hMge : 2 * α ≤ M n := by linarith [alpha_le_half hn2 hα]
  have hM34 : (34 : ℝ) < M n := by linarith
  have hMn : M n = (n : ℝ) - 1 := rfl
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set r : ℝ := ((n : ℝ) - 2) / 2 with hrdef
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hB1lt : B1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  have hr : (0 : ℝ) < r := by rw [hrdef]; rw [hMn] at hM34; linarith
  have hlog17 : (2.83 : ℝ) ≤ Real.log α :=
    le_trans log_seventeen_ge (Real.log_le_log (by norm_num) hcon.le)
  have hlogpos : (0 : ℝ) < Real.log α := by linarith
  have hxsq : Real.log α / α ≤ x ^ 2 := by
    have h1 : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
    rw [div_le_iff₀ hα0]
    nlinarith [hlogb, h1]
  have hI1 := integral_le_tail_lin hfeas hax haxle hr
  set I1 : ℝ := ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ r with hI1def
  have hprod : (r + 1) * (r + 2) = (n : ℝ) * ((n : ℝ) + 2) / 4 := by rw [hrdef]; ring
  have hane : (a : ℝ) ≠ 0 := ha.ne'
  have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hMn] at hM34; linarith
  have hbeta_term : a ^ 2 * n * M n * (1 / ((a * x) ^ 2 * ((r + 1) * (r + 2))))
      = 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) := by
    rw [hprod]
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := by linarith
    field_simp
  have hcoefnn : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hstep : a ^ 2 * n * M n * I1
      ≤ 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) + a ^ 2 * n * M n * (B1 ^ r / 2) := by
    calc a ^ 2 * n * M n * I1
        ≤ a ^ 2 * n * M n * (1 / ((a * x) ^ 2 * ((r + 1) * (r + 2))) + B1 ^ r / 2) :=
          mul_le_mul_of_nonneg_left hI1 hcoefnn
      _ = 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) + a ^ 2 * n * M n * (B1 ^ r / 2) := by
          rw [mul_add, hbeta_term]
  have hfourx : 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) ≤ 4 * α / Real.log α := by
    have h1 : 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) ≤ 4 / x ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : M n ≤ (n : ℝ) + 2 := by rw [hMn]; linarith
      nlinarith [sq_nonneg x, hxpos]
    have h2 : (4 : ℝ) / x ^ 2 ≤ 4 * α / Real.log α := by
      rw [div_le_div_iff₀ (by positivity) hlogpos]
      have := hxsq
      rw [div_le_iff₀ hα0] at this
      nlinarith [this]
    linarith
  have hfirst : (1 - x ^ 2) / (2 * M n) ≤ 1 / (2 * M n) := by
    have hD : (0 : ℝ) < 2 * M n := by linarith
    rw [div_le_div_iff₀ hD hD]
    nlinarith [sq_nonneg x, hD]
  have hmain : 2 * α ≤ 1 / (2 * M n) + 4 * α / Real.log α + a ^ 2 * n * M n * (B1 ^ r / 2) := by
    linarith [horigin, hstep, hfourx, hfirst, hax]
  obtain ⟨v, hvdef⟩ : ∃ w : ℝ, w = M n / (2 * α) - 1 := ⟨_, rfl⟩
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hv0 : 0 ≤ v := by
    rw [hvdef, sub_nonneg, le_div_iff₀ h2α]
    linarith
  have hMv : M n = 2 * α * (v + 1) := by
    rw [hvdef]
    field_simp
    ring
  have ha2 : a ^ 2 = 1 - 2 * α / M n := by
    rw [hα]
    field_simp
    ring
  have hav : a ^ 2 * M n / (2 * α) = v := by
    rw [ha2, hvdef]
    field_simp
  have hB1exp : B1 ≤ exp (-(Real.log α / α)) := by
    have h1 : B1 ≤ exp (B1 - 1) := by linarith [Real.add_one_le_exp (B1 - 1)]
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have : Real.log α / α ≤ 1 - B1 := by rw [div_le_iff₀ hα0]; linarith
    linarith
  have hrM : r = (M n - 1) / 2 := by rw [hrdef, hMn]; ring
  have hB1r : B1 ^ r ≤ exp (-(v * Real.log α)) / α * exp (Real.log α / (2 * α)) := by
    have h1 : B1 ^ r ≤ exp (-(Real.log α / α) * r) := by
      calc B1 ^ r ≤ exp (-(Real.log α / α)) ^ r := Real.rpow_le_rpow hB0 hB1exp hr.le
        _ = exp (-(Real.log α / α) * r) := by rw [← Real.exp_mul]
    refine h1.trans_eq ?_
    have hexpo : -(Real.log α / α) * r
        = (-(v * Real.log α) + -Real.log α) + Real.log α / (2 * α) := by
      rw [hrM, hMv]
      field_simp
      ring
    have hinv : exp (-Real.log α) = 1 / α := by
      rw [Real.exp_neg, Real.exp_log hα0]
      ring
    rw [hexpo, Real.exp_add, Real.exp_add, hinv]
    ring
  have hvexp : exp (-(v * Real.log α)) ≤ exp (-(2.83 * v)) :=
    Real.exp_le_exp.2 (by nlinarith [hv0, hlog17])
  have he1 : (2.7 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsecexp : exp (Real.log α / (2 * α)) ≤ 1 / (1 - 0.1852) := by
    refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_one_div_one_sub (by norm_num))
    have h := log_le_div_exp_one hα0
    have h27 : α / exp 1 ≤ α / 2.7 :=
      div_le_div_of_nonneg_left hα0.le (by norm_num) he1.le
    rw [div_le_iff₀ h2α]
    have hlast : α / 2.7 ≤ 0.1852 * (2 * α) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2.7)]
      nlinarith [hα0]
    linarith [h, h27, hlast]
  have hnv : (n : ℝ) = 2 * α * (v + 1) + 1 := by
    rw [← hMv, hMn]
    ring
  have hthird : a ^ 2 * n * M n * (B1 ^ r / 2) ≤ 0.50543 * α := by
    have hexpnn : (0 : ℝ) ≤ exp (-(2.83 * v)) := (Real.exp_pos _).le
    have hkey : a ^ 2 * n * M n * (B1 ^ r / 2) = (n : ℝ) * α * v * B1 ^ r := by
      rw [← hav]
      field_simp
    rw [hkey]
    have hstep1 : (n : ℝ) * α * v * B1 ^ r
        ≤ (n : ℝ) * α * v * (exp (-(2.83 * v)) / α * (1 / (1 - 0.1852))) := by
      refine mul_le_mul_of_nonneg_left (hB1r.trans ?_) (by positivity)
      refine mul_le_mul ?_ hsecexp (Real.exp_pos _).le (by positivity)
      gcongr
    refine hstep1.trans ?_
    have hfinal : (n : ℝ) * α * v * (exp (-(2.83 * v)) / α * (1 / (1 - 0.1852)))
        = α * (v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v))) * (1 / (1 - 0.1852)) := by
      rw [hnv]
      field_simp
    rw [hfinal]
    have hbound : v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v)) ≤ 0.4118 := by
      refine le_trans ?_ (tail_poly_bound hv0)
      have hinv : (1 : ℝ) / α ≤ 1 / 17 := by
        rw [div_le_div_iff₀ hα0 (by norm_num)]; linarith
      have hprod : (0 : ℝ) ≤ v * exp (-(2.83 * v)) := mul_nonneg hv0 hexpnn
      nlinarith [mul_le_mul_of_nonneg_left hinv hprod]
    have hscale : α * (v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v))) ≤ α * 0.4118 :=
      mul_le_mul_of_nonneg_left hbound hα0.le
    linarith [hscale]
  have hlogterm : 4 * α / Real.log α ≤ 1.41343 * α := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [hlog17, hα0]
  have hMterm : 1 / (2 * M n) ≤ 1 / 68 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith [hmain, hlogterm, hMterm, hthird, hcon]
end Sendov
end

section
namespace Sendov
variable {α : ℝ}
theorem stat_lt_one {n : ℕ} (hn : 5 ≤ n) (h8 : n ≤ 8) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  interval_cases n
  · exact finite_range_five hα hfeas
  · exact finite_range_six hα hfeas
  · exact finite_range_seven hα hfeas
  · exact finite_range_eight hα hfeas
end Sendov
end
section
namespace Sendov
open MeasureTheory
theorem polar_origin_incompatible {n : ℕ} (hn : 5 ≤ n) (h8 : n ≤ 8) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    False := by
  have hn2 : 2 ≤ n := by omega
  have hα0 : 0 < α := alpha_pos hn2 ha1 ha.le hα
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ QQ (a * x) (a ^ 2) 1 := QQ_nonneg hfeas 1
  have hlt := polar_exp hn2 hx hα hpolar
  have hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α) := beta_le hα0 hB0 hlt
  have hB1lt : QQ (a * x) (a ^ 2) 1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1) :=
    log_le_alpha_mul hα0 hB1lt.le hlt
  have h17 : α ≤ 17 := alpha_le_seventeen hn ha ha1 hx hα hbeta hlogb horigin
  have h1le := one_le_of_origin hn ha ha1 hx hα hα0 hB1lt horigin
  have hstat : 1 ≤ R n α := stat_of_one_le hn hx hα hα0 hbeta h1le
  exact absurd hstat
    (not_le.2 (stat_lt_one hn h8 hα0.le h17 (feasible_of_beta hn2 hx hα hα0 hbeta)))
end Sendov
end

section
namespace Sendov
open _root_.Polynomial
open Complex (I)
theorem sendov_interior {n : ℕ} (hn : 2 ≤ n) (h8 : n ≤ 8) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (a : ℂ)‖ := by
    intro w hw
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hpa
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  have hne : ((n : ℂ) - 1) ≠ 0 := by
    intro h
    have h1 : (n : ℂ) = 1 := by linear_combination h
    have h2 : n = 1 := by exact_mod_cast h1
    omega
  have hqne : q ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hqcard
    omega
  have haC0 : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha0
  have haC2 : ((a : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro h
    have : (a : ℂ) ^ 2 = ((a ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this] at h
    have h1 : a ^ 2 = 1 := by exact_mod_cast h
    nlinarith [h1, ha0, ha1]
  have hstar := one_le_integral_prod_norm hn (a := a)
    (by rw [abs_of_nonneg (le_of_lt ha0)]; linarith) hz1
    (polar_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q) (p := p)
      hc0 haC0 haC2 hzcard hqcard hq0 hpa hpz hpq')
    (prod_sub_mul_prod (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q)
      (p := p) hc0 hq0 hpz hpq')
  rcases (by omega : n < 5 ∨ 5 ≤ n) with hn5 | hn5
  · exact low_degree_contradiction hn (by omega) ha0 ha1 hqcard hq1 hstar
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I) := by
    refine ⟨(q.sum / ((n : ℂ) - 1)).re, (q.sum / ((n : ℂ) - 1)).im, ?_⟩
    rw [Complex.re_add_im, mul_div_cancel₀ _ hne]
  obtain ⟨hxre, hx2⟩ := xy_bounds hn hqcard hq1 hxy
  have hpolar := one_le_integral_Ppolar hn (a := a) (x := x) hqcard hq1 hxre hstar
  have hcent := centroid_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hn hc0 hzcard hqcard hpz hpq'
  have hfirst := first_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 haC0 hzcard hq0 hpa hpz hpq'
  have hsecond := second_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 hzcard hq0 hpz hpq'
  have horigin := origin_exact (n := n) (α := M n * (1 - a ^ 2) / 2) hn5 ha0 ha1 hqcard hqne
    hz1 hq1 hxy hcent hfirst hsecond rfl
  exact polar_origin_incompatible hn5 (by omega) ha0 ha1 (by nlinarith [hx2, sq_nonneg y]) rfl hpolar
    horigin
theorem sendov_center {n : ℕ} (hn : 2 ≤ n) (h8 : n ≤ 8) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp0 : p.eval 0 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (0 : ℂ)‖ := by
    intro w hw
    rw [sub_zero]
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp0
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (0 : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  have hkey := prod_sub_mul_prod (c := p.leadingCoeff) (a := (0 : ℂ)) (n := n) (z := z) (q := q)
    (p := p) hc0 hq0 hpz hpq'
  have hnorm := congrArg norm hkey
  rw [norm_mul] at hnorm
  have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  have h2 : ‖(z.map (fun w => (0 : ℂ) - w)).prod‖ ≤ 1 := by
    refine norm_prod_le_one _ ?_
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu
    simpa using hz1 w hw
  have h3 : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [h3] at hnorm
  have h4 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hnorm, h1, h2, norm_nonneg q.prod, norm_nonneg (z.map (fun w => (0 : ℂ) - w)).prod]
theorem sendov_interior_real {n : ℕ} (hn : 2 ≤ n) (h8 : n ≤ 8) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  rcases eq_or_lt_of_le ha0 with hz | hz
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn h8 hdeg hroots (by rw [← hz] at hpa; simpa using hpa)
    exact ⟨ζ, hζ, by rw [← hz]; simpa using hlt⟩
  · exact sendov_interior hn h8 hdeg hroots hz ha1 hpa
end Sendov
end

section
namespace Sendov
open _root_.Polynomial
lemma eval_prod_at (u : ℂ) (s : Multiset ℂ) :
    ((s.map (fun w => X - C w)).prod).eval u = (s.map (fun w => u - w)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)
lemma eval_deriv_prod_at (u : ℂ) : ∀ (s : Multiset ℂ),
    (derivative (s.map (fun w => X - C w)).prod).eval u
      = sumEraseProd (s.map (fun w => u - w)) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C]
    rw [ih, eval_prod_at, sumEraseProd_cons]
lemma half_le_re_inv_one_sub {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 : ℝ) / 2 ≤ (((1 : ℂ) - z)⁻¹).re := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hd : 0 < Complex.normSq ((1 : ℂ) - z) := Complex.normSq_pos.2 hne
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    nlinarith [hz, norm_nonneg z, h]
  rw [Complex.inv_re, le_div_iff₀ hd, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [hsq]
lemma eq_one_of_re_eq_one_of_norm_le_one {v : ℂ} (hre : v.re = 1) (hv : ‖v‖ ≤ 1) : v = 1 := by
  have hsq : v.re ^ 2 + v.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq v
    rw [Complex.normSq_apply] at h
    nlinarith [hv, norm_nonneg v, h]
  have him : v.im = 0 := by nlinarith [hsq, hre, sq_nonneg v.im]
  apply Complex.ext <;> simp [hre, him]
lemma eq_zero_of_sum_eq_zero {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (h : s.sum = 0) :
    ∀ x ∈ s, x = 0 := by
  intro x hx
  have hsplit : s.sum = x + (s.erase x).sum := by
    conv_lhs => rw [← Multiset.cons_erase hx]
    rw [Multiset.sum_cons]
  have hrest : 0 ≤ (s.erase x).sum :=
    Multiset.sum_nonneg fun y hy => hs y (Multiset.mem_of_mem_erase hy)
  rw [hsplit] at h
  have := hs x hx
  linarith
lemma sum_le_card_mul (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, x ≤ c) →
    s.sum ≤ (s.card : ℝ) * c := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]
lemma card_mul_le_sum (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, c ≤ x) →
    (s.card : ℝ) * c ≤ s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, c ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]
lemma sum_map_one_sub_re (s : Multiset ℂ) :
    (s.map (fun v => 1 - v.re)).sum = (s.card : ℝ) - (s.map (fun v => v.re)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring
theorem boundary_reciprocal {n : ℕ} {Zs Qi : Multiset ℂ} (hn0 : (n : ℂ) ≠ 0)
    (hZ : ∀ u ∈ Zs, u ≠ 0) (hQ : ∀ u ∈ Qi, u ≠ 0)
    (hI : Zs.prod = (n : ℂ) * Qi.prod)
    (hII : 2 * sumEraseProd Zs = (n : ℂ) * sumEraseProd Qi) :
    (Qi.map (fun u => u⁻¹)).sum = 2 * (Zs.map (fun u => u⁻¹)).sum := by
  have hQ0 : Qi.prod ≠ 0 := Multiset.prod_ne_zero fun h => hQ 0 h rfl
  have h1 := prod_mul_sum_inv Zs hZ
  have h2 := prod_mul_sum_inv Qi hQ
  have h : (n : ℂ) * Qi.prod * (2 * (Zs.map (fun u => u⁻¹)).sum)
      = (n : ℂ) * Qi.prod * (Qi.map (fun u => u⁻¹)).sum := by
    linear_combination (-2 * (Zs.map (fun u => u⁻¹)).sum) * hI + 2 * h1 + hII - (n : ℂ) * h2
  exact (mul_left_cancel₀ (mul_ne_zero hn0 hQ0) h).symm
theorem all_q_eq_one {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hq1 : ∀ v ∈ qs, ‖v‖ ≤ 1) (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1) (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 := by
  have hupper : (qs.map (fun v => v.re)).sum ≤ (N : ℝ) := by
    have h := sum_le_card_mul 1 (qs.map (fun v => v.re)) (by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hr
      exact (Complex.re_le_norm v).trans (hq1 v hv))
    rwa [Multiset.card_map, hqcard, mul_one] at h
  have hlower : (N : ℝ) ≤ (qs.map (fun v => v.re)).sum := by
    have h := card_mul_le_sum (1 / 2) (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)) (by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hr
      exact half_le_re_inv_one_sub (hz1 w hw) (hzne w hw))
    rw [Multiset.card_map, hzcard] at h
    have hmapre : (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum
        = (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum.re := by
      rw [← sum_map_re, Multiset.map_map]
      rfl
    have hre : (qs.map (fun v => v.re)).sum
        = 2 * (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum := by
      rw [sum_map_re, hBR, hmapre, Complex.mul_re]
      simp
    rw [hre]
    linarith
  have heq : (qs.map (fun v => 1 - v.re)).sum = 0 := by
    rw [sum_map_one_sub_re, hqcard]
    linarith
  intro v hv
  refine eq_one_of_re_eq_one_of_norm_le_one ?_ (hq1 v hv)
  have hzero := eq_zero_of_sum_eq_zero (s := qs.map (fun v => 1 - v.re)) (by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hr
    have := (Complex.re_le_norm u).trans (hq1 u hu)
    linarith) heq (1 - v.re) (Multiset.mem_map_of_mem _ hv)
  linarith
theorem rubinstein_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1)
      ∨ p = C p.leadingCoeff * (X ^ n - 1) := by
  by_cases hex : ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1
  · exact Or.inl hex
  refine Or.inr ?_
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - 1‖ := by
    intro w hw
    by_contra hlt
    exact hex ⟨w, hw, not_le.1 hlt⟩
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hn0 : (n : ℂ) ≠ 0 := by
    intro h
    have h1 : n = 0 := by exact_mod_cast h
    omega
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp1
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => X - C u)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  have hp'1 : (derivative p).eval 1 ≠ 0 := fun h => hex ⟨1, h, by simp⟩
  have hd1 : derivative p = C p.leadingCoeff
      * ((z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (z.map (fun w => X - C w)).prod) := by
    conv_lhs => rw [hpz]
    rw [derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul]
  have hd2 : derivative (derivative p) = C p.leadingCoeff
      * (2 * derivative (z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (derivative (z.map (fun w => X - C w)).prod)) := by
    rw [hd1, derivative_C_mul, derivative_add, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul]
    ring
  have hA : (derivative p).eval 1 = p.leadingCoeff * (z.map (fun w => (1 : ℂ) - w)).prod := by
    rw [hd1]
    simp [eval_prod_at]
  have hB : (derivative (derivative p)).eval 1
      = p.leadingCoeff * (2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))) := by
    rw [hd2]
    simp [eval_deriv_prod_at]
  have hmapq : (q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => (1 : ℂ) - u)
      = q.map (fun v => v⁻¹) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun v _ => by simp
  have hC : (derivative p).eval 1
      = (n : ℂ) * p.leadingCoeff * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq', eval_mul, eval_C, eval_prod_at, hmapq]
  have hD : (derivative (derivative p)).eval 1
      = (n : ℂ) * p.leadingCoeff * sumEraseProd (q.map (fun v => v⁻¹)) := by
    rw [hpq', derivative_C_mul, eval_mul, eval_C, eval_deriv_prod_at, hmapq]
  have hI : (z.map (fun w => (1 : ℂ) - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hA.symm.trans hC
    linear_combination h
  have hII : 2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))
      = (n : ℂ) * sumEraseProd (q.map (fun v => v⁻¹)) := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hB.symm.trans hD
    linear_combination h
  have hZ0 : (z.map (fun w => (1 : ℂ) - w)).prod ≠ 0 := by
    intro h
    exact hp'1 (by rw [hA, h, mul_zero])
  have hZne : ∀ u ∈ z.map (fun w => (1 : ℂ) - w), u ≠ 0 := by
    intro u hu hu0
    exact hZ0 (Multiset.prod_eq_zero (hu0 ▸ hu))
  have hzne : ∀ w ∈ z, w ≠ 1 := by
    intro w hw hw1
    exact hZne ((1 : ℂ) - w) (Multiset.mem_map_of_mem _ hw) (by rw [hw1]; ring)
  have hQne : ∀ u ∈ q.map (fun v => v⁻¹), u ≠ 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hu
    exact inv_ne_zero (hq0 v hv)
  have hBRraw := boundary_reciprocal (n := n) hn0 hZne hQne hI hII
  have hQiinv : ((q.map (fun v => v⁻¹)).map (fun u => u⁻¹)).sum = q.sum := by
    rw [Multiset.map_map]
    simp
  have hZsinv : (z.map (fun w => (1 : ℂ) - w)).map (fun u => u⁻¹)
      = z.map (fun w => ((1 : ℂ) - w)⁻¹) := by
    rw [Multiset.map_map]
    rfl
  rw [hQiinv, hZsinv] at hBRraw
  have hqone := all_q_eq_one hqcard hzcard hq1 hz1 hzne hBRraw
  have hderivX : derivative p = C ((n : ℂ) * p.leadingCoeff) * X ^ (n - 1) := by
    rw [hpq]
    congr 1
    have hmap : q.map (fun v => X - C ((1 : ℂ) - v⁻¹))
        = Multiset.replicate q.card (X : ℂ[X]) := by
      rw [← Multiset.map_const']
      exact Multiset.map_congr rfl fun v hv => by rw [hqone v hv]; simp
    rw [hmap, Multiset.prod_replicate, hqcard]
  have hdz : derivative (p - C p.leadingCoeff * X ^ n) = 0 := by
    rw [derivative_sub, hderivX, derivative_C_mul, derivative_X_pow, map_mul]
    ring
  have hdeg0 : (p - C p.leadingCoeff * X ^ n).natDegree = 0 := derivative_eq_zero.1 hdz
  obtain ⟨d, hd⟩ := natDegree_eq_zero.1 hdeg0
  have hdval : d = -p.leadingCoeff := by
    have h := congrArg (Polynomial.eval (1 : ℂ)) hd
    simpa [hp1] using h
  have hCd : (C d : ℂ[X]) = -C p.leadingCoeff := by rw [hdval, map_neg]
  linear_combination -hd + hCd
theorem sendov_boundary_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ ≤ 1 := by
  rcases rubinstein_one hn hdeg hroots hp1 with ⟨ζ, hζ, hlt⟩ | hext
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  refine ⟨0, ?_, by norm_num⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_one]
  simp [zero_pow (by omega : n - 1 ≠ 0)]
end Sendov
end

section
namespace Sendov
open _root_.Polynomial
noncomputable def rotate (ω : ℂ) (p : ℂ[X]) : ℂ[X] := p.comp (C ω * X)
@[simp] lemma eval_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (rotate ω p).eval x = p.eval (ω * x) := by
  simp [rotate, eval_comp]
lemma natDegree_rotate {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    (rotate ω p).natDegree = p.natDegree := by
  rw [rotate, natDegree_comp, natDegree_C_mul hω, natDegree_X, mul_one]
lemma derivative_rotate (ω : ℂ) (p : ℂ[X]) :
    derivative (rotate ω p) = C ω * rotate ω (derivative p) := by
  simp only [rotate, derivative_comp, derivative_mul, derivative_C, derivative_X, zero_mul,
    mul_one, zero_add]
lemma eval_derivative_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (derivative (rotate ω p)).eval x = ω * (derivative p).eval (ω * x) := by
  rw [derivative_rotate, eval_mul, eval_C, eval_rotate]
lemma rotate_rotate_inv {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) : rotate ω⁻¹ (rotate ω p) = p := by
  have h : (C ω * X : ℂ[X]).comp (C ω⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hω, C_1, one_mul]
  rw [rotate, rotate, comp_assoc, h, comp_X]
lemma roots_rotate {ω : ℂ} (hω : ‖ω‖ = 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) : ∀ w ∈ (rotate ω p).roots, ‖w‖ ≤ 1 := by
  intro w hw
  have hev : p.eval (ω * w) = 0 := by
    have := (mem_roots'.1 hw).2
    rwa [IsRoot, eval_rotate] at this
  have hmem : ω * w ∈ p.roots := mem_roots'.2 ⟨hp, hev⟩
  have := hroots _ hmem
  rwa [norm_mul, hω, one_mul] at this
theorem phelps_rodriguez {n : ℕ} (hn : 2 ≤ n) (h8 : n ≤ 8) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧ p = C c * (X ^ n - C (a ^ n))) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn h8 hdeg hroots hpa
    exact Or.inl ⟨ζ, hζ, by simpa using hlt⟩
  have hr0 : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hr1 : ‖a‖ ≤ 1 := hroots a (mem_roots'.2 ⟨hp0, hpa⟩)
  have hrC : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hr0
  obtain ⟨ω, hωdef⟩ : ∃ w : ℂ, w = a / ((‖a‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hωne : ω ≠ 0 := by
    rw [hωdef]
    exact div_ne_zero ha0 hrC
  have hωnorm : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr0),
      div_self (ne_of_gt hr0)]
  have hωr : ω * ((‖a‖ : ℝ) : ℂ) = a := by
    rw [hωdef, div_mul_cancel₀ _ hrC]
  have hdeg' : (rotate ω p).natDegree = n := by rw [natDegree_rotate hωne, hdeg]
  have hroots' := roots_rotate hωnorm hp0 hroots
  have hpr : (rotate ω p).eval ((‖a‖ : ℝ) : ℂ) = 0 := by rw [eval_rotate, hωr, hpa]
  have htransport : ∀ ζ : ℂ, (derivative (rotate ω p)).eval ζ = 0 →
      ‖ζ - ((‖a‖ : ℝ) : ℂ)‖ < 1 → ∃ ξ : ℂ, (derivative p).eval ξ = 0 ∧ ‖ξ - a‖ < 1 := by
    intro ζ hζ hlt
    refine ⟨ω * ζ, ?_, ?_⟩
    · rw [eval_derivative_rotate] at hζ
      exact (mul_eq_zero.1 hζ).resolve_left hωne
    · have : ω * ζ - a = ω * (ζ - ((‖a‖ : ℝ) : ℂ)) := by rw [mul_sub, hωr]
      rw [this, norm_mul, hωnorm, one_mul]
      exact hlt
  rcases lt_or_eq_of_le hr1 with hlt1 | heq1
  · 
    obtain ⟨ζ, hζ, hd⟩ :=
      sendov_interior_real hn h8 hdeg' hroots' (le_of_lt hr0) hlt1 hpr
    exact Or.inl (htransport ζ hζ hd)
  · 
    have hone : ((‖a‖ : ℝ) : ℂ) = 1 := by rw [heq1]; norm_num
    have haω : a = ω := by rw [← hωr, hone, mul_one]
    have hpr1 : (rotate ω p).eval 1 = 0 := by rwa [hone] at hpr
    rcases rubinstein_one hn hdeg' hroots' hpr1 with ⟨ζ, hζ, hd⟩ | hext
    · exact Or.inl (htransport ζ hζ (by rw [hone]; exact hd))
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (rotate ω p).leadingCoeff := ⟨_, rfl⟩
    have hcne : c ≠ 0 := by
      rw [hcdef]
      refine leadingCoeff_ne_zero.2 ?_
      intro h
      rw [h, natDegree_zero] at hdeg'
      omega
    refine Or.inr ⟨heq1, c * ω⁻¹ ^ n,
      mul_ne_zero hcne (pow_ne_zero _ (inv_ne_zero hωne)), ?_⟩
    have hext' : rotate ω p = C c * (X ^ n - 1) := by rw [hcdef]; exact hext
    have hcomp : rotate ω⁻¹ (C c * (X ^ n - 1)) = C c * (C (ω⁻¹ ^ n) * X ^ n - 1) := by
      simp only [rotate, mul_comp, sub_comp, pow_comp, C_comp, X_comp, one_comp, mul_pow,
        ← C_pow]
    have h1 : (C (ω⁻¹ ^ n) * C (ω ^ n) : ℂ[X]) = 1 := by
      rw [← C_mul, ← mul_pow, inv_mul_cancel₀ hωne, one_pow, C_1]
    have hgoal : rotate ω⁻¹ (rotate ω p) = C (c * ω⁻¹ ^ n) * (X ^ n - C (a ^ n)) := by
      rw [hext', hcomp, haω, C_mul]
      linear_combination (C c) * h1
    exact (rotate_rotate_inv hωne p).symm.trans hgoal
theorem sendov {n : ℕ} (hn : 2 ≤ n) (h8 : n ≤ 8) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 := by
  rcases phelps_rodriguez hn h8 hdeg hroots hpa with ⟨ζ, hζ, hlt⟩ | ⟨hnorm, c, hc, hext⟩
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  refine ⟨0, ?_, by simpa using le_of_eq hnorm⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_C]
  simp [zero_pow (by omega : n - 1 ≠ 0)]
end Sendov
end

open _root_.Polynomial in
theorem OMA.solution : type_of% @Sendov.sendov_conjecture.variants.le_eight := by
  intro n hn f hf hdeg z hz
  have hn2 : 2 ≤ n := hn.1
  have h8 : n ≤ 8 := hn.2
  have hf0 : f ≠ 0 := by
    intro h
    have := hf.1
    rw [h, natDegree_zero] at this
    omega
  have hroots : ∀ w ∈ f.roots, ‖w‖ ≤ 1 := by
    intro w hw
    have : w ∈ f.rootSet ℂ := by
      rw [mem_rootSet]; exact ⟨hf0, (mem_roots hf0).1 hw⟩
    simpa using hf.2 this
  have hzr : f.eval z = 0 := ((mem_rootSet.1 hz).2)
  obtain ⟨ζ, hζ, hd⟩ := Sendov.sendov hn2 h8 hdeg hroots hzr
  have hmem : ζ ∈ (derivative f).rootSet ℂ := by
    rw [mem_rootSet]
    refine ⟨?_, hζ⟩
    intro h
    have hdeg' : f.natDegree = 1 ∨ f.natDegree = 0 := by
      by_contra hc
      have := natDegree_eq_zero_of_derivative_eq_zero h
      omega
    omega
  calc Metric.infDist z ((derivative f).rootSet ℂ) ≤ dist z ζ := Metric.infDist_le_dist_of_mem hmem
    _ ≤ 1 := by rw [dist_eq_norm]; rw [← norm_neg, neg_sub]; exact hd
