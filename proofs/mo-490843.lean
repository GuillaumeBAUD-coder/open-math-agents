import OMAStatements.S_mo_490843
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

namespace CodexTwo.Mo490843

noncomputable section

open Finset
open scoped BigOperators Polynomial
open PowerSeries OMA.S_mo_490843

private abbrev P := ℤ[X]
private abbrev Series := PowerSeries P

private abbrev z : P := Polynomial.X
private abbrev Z : Series := C z

private def tailCoeff : ℕ → ℕ → P
  | 0, _ => 1
  | n + 1, h => Polynomial.C (h + 1 : ℤ) * tailCoeff n h +
      z * ∑ i ∈ (range (n + 1)).attach, tailCoeff i.val h * tailCoeff (n - i.val) (h + 1)
termination_by n _h => n
decreasing_by
  · omega
  · exact mem_range.mp i.property
  · omega

private def tail (h : ℕ) : Series := PowerSeries.mk (fun n ↦ tailCoeff n h)

private theorem tail_eq (h : ℕ) :
    tail h = 1 + X * (C (Polynomial.C (h + 1 : ℤ)) * tail h + Z * (tail h * tail (h + 1))) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [tail, tailCoeff.eq_1]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, map_add, coeff_C_mul, coeff_C_mul, coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_one, Nat.succ_ne_zero, if_false, zero_add, tail, coeff_mk]
    rw [tailCoeff.eq_2, Finset.sum_attach (range (n + 1))
      (fun i ↦ tailCoeff i h * tailCoeff (n - i) (h + 1))]

private def d (S : Series) : Series := PowerSeries.mk (fun n ↦ Polynomial.derivative (coeff n S))

private theorem coeff_d (S : Series) (n : ℕ) :
    coeff n (d S) = Polynomial.derivative (coeff n S) := coeff_mk _ _

private theorem d_add (S T : Series) : d (S + T) = d S + d T := by
  apply PowerSeries.ext
  intro n
  simp [coeff_d]

private theorem d_sub (S T : Series) : d (S - T) = d S - d T := by
  apply PowerSeries.ext
  intro n
  simp [coeff_d]

private theorem d_C (p : P) : d (C p) = C (Polynomial.derivative p) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0 <;> simp [coeff_d, coeff_C, hn]

private theorem d_X : d X = 0 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 1 <;> simp [coeff_d, coeff_X, hn]

private theorem d_mul (S T : Series) : d (S * T) = d S * T + S * d T := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_d, coeff_mul, map_add, Polynomial.derivative_sum,
    Polynomial.derivative_mul, sum_add_distrib]

private theorem d_one : d 1 = 0 := by
  rw [← map_one C, d_C, Polynomial.derivative_one, map_zero]

private theorem d_tail (h : ℕ) :
    d (tail h) = X * (tail h)^2 * (tail (h + 1) + Z * d (tail (h + 1))) := by
  let K : Series := 1 - X * (C (Polynomial.C (h + 1 : ℤ)) + Z * tail (h + 1))
  have hc : K * tail h = 1 := by
    have he := tail_eq h
    dsimp [K]
    linear_combination he
  have hd : d K = -(X * (tail (h + 1) + Z * d (tail (h + 1)))) := by
    dsimp [K]
    simp only [d_sub, d_one, d_mul, d_X, zero_mul, zero_add, d_add, d_C,
      Polynomial.derivative_C, Polynomial.derivative_X, map_zero, map_one, one_mul, zero_sub]
  have hp : d (K * tail h) = 0 := hc ▸ d_one
  rw [d_mul, hd] at hp
  linear_combination tail h * hp - d (tail h) * hc

private theorem tail_sub (h : ℕ) :
    tail (h + 1) - tail h =
      X * tail h * tail (h + 1) * (1 + Z * (tail (h + 2) - tail (h + 1))) := by
  have h₀ := tail_eq h
  have h₁ := tail_eq (h + 1)
  rw [Nat.cast_add, Nat.cast_one, map_add, map_one, map_add, map_one] at h₁
  linear_combination tail h * h₁ - tail (h + 1) * h₀

private def err (h : ℕ) : Series :=
  d (tail h) - tail h * (tail (h + 1) - tail h)

private theorem err_eq (h : ℕ) :
    err h = X * (Z * (tail h)^2 * err (h + 1)) := by
  unfold err
  rw [d_tail, tail_sub h]
  ring

private theorem err_zero (h : ℕ) : err h = 0 := by
  have hz : ∀ n h, coeff n (err h) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h
      cases n with
      | zero => rw [err_eq]; simp
      | succ n =>
        rw [err_eq, coeff_succ_X_mul, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply sum_eq_zero
        intro i hi
        rw [ih (n - i) (by omega) (h + 1), mul_zero]
  apply PowerSeries.ext
  intro n
  simp [hz]

private def S : Series := Z * tail 0

private theorem S_eq : S = Z + X * (Z * d S + S * S) := by
  have h := tail_eq 0
  have he := err_zero 0
  dsimp [err] at he
  simp only [Nat.cast_zero, zero_add, map_one, zero_add] at h he
  rw [S, d_mul, d_C, Polynomial.derivative_X, map_one, one_mul]
  linear_combination Z * h - X * Z^2 * he

private def moment (k : ℕ) : P →ₗ[ℤ] ℤ :=
  Polynomial.lsum (fun j ↦ (j : ℤ)^k • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private theorem moment_monomial (k j : ℕ) (a : ℤ) :
    moment k (Polynomial.monomial j a) = (j : ℤ)^k * a := by
  change (Polynomial.monomial j a).sum _ = _
  rw [Polynomial.sum_monomial_index]
  · rfl
  · simp

private theorem moment_z (k : ℕ) : moment k z = 1 := by
  rw [show z = Polynomial.monomial 1 1 from Polynomial.monomial_one_one_eq_X.symm]
  simp [moment_monomial]

private theorem moment_mul (k : ℕ) (p q : P) :
    moment k (p * q) = ∑ j ∈ range (k + 1),
      (k.choose j : ℤ) * moment j p * moment (k - j) q := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    rw [add_mul, map_add, hp, hp', ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [map_add]
    ring
  | monomial a x =>
    induction q using Polynomial.induction_on' with
    | add q q' hq hq' =>
      rw [mul_add, map_add, hq, hq', ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      rw [map_add]
      ring
    | monomial b y =>
      simp only [Polynomial.monomial_mul_monomial, moment_monomial, Nat.cast_add]
      rw [add_pow, sum_mul]
      apply sum_congr rfl
      intro j _
      ring

private theorem moment_euler (k : ℕ) (p : P) :
    moment k (z * Polynomial.derivative p) = moment (k + 1) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, hp, hq]
  | monomial j a =>
    cases j with
    | zero =>
      rw [Polynomial.derivative_monomial, moment_monomial]
      simp
    | succ j =>
      rw [Polynomial.derivative_monomial_succ]
      rw [show z = Polynomial.monomial 1 1 from Polynomial.monomial_one_one_eq_X.symm]
      rw [Polynomial.monomial_mul_monomial, one_mul, Nat.add_comm 1 j]
      simp only [moment_monomial, Nat.cast_succ, pow_succ]
      ring

private theorem moment_zero (p : P) : moment 0 p = Polynomial.eval 1 p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial j a => simp [moment_monomial]

private theorem r_moment (n k : ℕ) : (R n k : ℤ) = moment k (coeff n S) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    cases n with
    | zero =>
      have he := congrArg (coeff 0) S_eq
      simp at he
      change constantCoeff S = z at he
      rw [coeff_zero_eq_constantCoeff, he, moment_z, R.eq_1, Nat.cast_one]
    | succ n =>
      have he := congrArg (coeff (n + 1)) S_eq
      rw [map_add, coeff_succ_X_mul, map_add, coeff_C_mul, coeff_d, coeff_mul,
        Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
      simp only [coeff_C, Nat.succ_ne_zero, if_false, zero_add] at he
      rw [he, map_add, moment_euler, map_sum, ← ih n (by omega), R.eq_2]
      push_cast
      congr 1
      rw [Finset.sum_attach (range (n + 1)) (fun i ↦ ∑ j ∈ range (k + 1),
        (k.choose j : ℤ) * (R (n - i) j : ℤ) * (R i (k - j) : ℤ))]
      apply sum_congr rfl
      intro i hi
      rw [mul_comm (coeff i S) (coeff (n - i) S), moment_mul]
      apply sum_congr rfl
      intro j _
      rw [← ih i (mem_range.mp hi), ← ih (n - i) (by omega)]

private theorem specialization (F : ℕ → PowerSeries ℤ)
    (hF : ∀ h : ℕ, F h = 1 + X * (C ((h + 1 : ℕ) : ℤ) * F h + F (h + 1) * F h))
    (n h : ℕ) : Polynomial.eval 1 (coeff n (tail h)) = coeff n (F h) := by
  induction n using Nat.strong_induction_on generalizing h with
  | h n ih =>
    cases n with
    | zero =>
      have he := congrArg (coeff 0) (hF h)
      simp only [coeff_zero_eq_constantCoeff, map_add, map_one, map_mul,
        constantCoeff_X, zero_mul, add_zero] at he
      simp [tail, tailCoeff.eq_1, coeff_zero_eq_constantCoeff, he]
    | succ n =>
      have he := congrArg (coeff (n + 1)) (hF h)
      have ht := congrArg (coeff (n + 1)) (tail_eq h)
      rw [mul_comm (F (h + 1)) (F h)] at he
      rw [map_add, coeff_succ_X_mul, map_add, coeff_C_mul, coeff_mul,
        Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
      rw [map_add, coeff_succ_X_mul, map_add, coeff_C_mul, coeff_C_mul, coeff_mul,
        Nat.sum_antidiagonal_eq_sum_range_succ_mk] at ht
      simp only [coeff_one, Nat.succ_ne_zero, if_false, zero_add] at he ht
      rw [ht, he]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, one_mul, Polynomial.eval_finsetSum, ih n (by omega)]
      push_cast
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [ih i (mem_range.mp hi), ih (n - i) (by omega)]

end

end CodexTwo.Mo490843

theorem OMA.solution : type_of% @OMA.S_mo_490843.main := by
  intro F hF n
  open CodexTwo.Mo490843 in
  rw [r_moment, moment_zero, S, PowerSeries.coeff_C_mul, Polynomial.eval_mul,
    Polynomial.eval_X, one_mul, specialization F hF]
