import OMAStatements.S_mo_479301
import Mathlib

open Polynomial
open Finset Polynomial
open OMA.S_mo_479301

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_479301.main) := by
  intro h
  have hh := h 5 (by decide) 7 (by decide) 2
  have h₈ : Nat.choose 8 2 = 28 := by decide
  have h₉ : Nat.choose 9 2 = 36 := by decide
  have h₁₀ : Nat.choose 10 2 = 45 := by decide
  simp only [S, C_mul_X_pow_eq_monomial] at hh
  norm_num [coeff_sub, pow_two, coeff_mul, finsetSum_coeff,
    Finset.Nat.antidiagonal_succ, Finset.sum_range_succ, coeff_monomial,
    coeff_one, h₈, h₉, h₁₀] at hh
