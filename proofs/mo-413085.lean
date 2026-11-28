import OMAStatements.S_mo_413085
import Mathlib

-- Problem: Can finitely many real polynomials generate all rational numbers?
-- Upstream: formal-conjectures statements/mo-413085.lean:0 (declaration OMA.S_mo_413085.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_413085.main) := by
  rintro ⟨F, p, hpF, hq⟩
  classical
  have hJ : IsJacobsonRing ℤ := by
    rw [isJacobsonRing_iff_prime_eq]
    intro P hP
    by_cases h0 : P = ⊥
    · subst h0
      refine le_antisymm ?_ Ideal.le_jacobson
      intro x hx
      rw [Ideal.mem_jacobson_bot] at hx
      have h := hx x
      rw [Int.isUnit_iff] at h
      rw [Ideal.mem_bot]
      rcases h with h | h
      · have h3 : x * x = 0 := by linarith
        exact mul_self_eq_zero.mp h3
      · nlinarith [mul_self_nonneg x]
    · have hmax := hP.isMaximal h0
      exact Ideal.jacobson_eq_self_of_isMaximal
  let s : Finset ℝ := F.biUnion (fun f => f.coeffs)
  let A : Subalgebra ℤ ℝ := Algebra.adjoin ℤ (s : Set ℝ)
  have hcoeff : ∀ n i, (p n).coeff i ∈ A := by
    intro n i
    by_cases h : (p n).coeff i = 0
    · rw [h]; exact A.zero_mem
    · apply Algebra.subset_adjoin
      have : (p n).coeff i ∈ s :=
        Finset.mem_biUnion.mpr ⟨p n, hpF n, Polynomial.coeff_mem_coeffs h⟩
      exact this
  have horb : ∀ n, OMA.S_mo_413085.orbit p n ∈ A := by
    intro n
    induction n with
    | zero => exact A.zero_mem
    | succ n ih =>
      show (p n).eval (OMA.S_mo_413085.orbit p n) ∈ A
      rw [Polynomial.eval_eq_sum_range]
      exact A.sum_mem (fun i _ => A.mul_mem (hcoeff n i) (A.pow_mem ih i))
  have hQ : ∀ q : ℚ, (q : ℝ) ∈ A := fun q => by
    obtain ⟨n, hn⟩ := hq q
    rw [← hn]
    exact horb n
  have : Algebra.FiniteType ℤ A :=
    (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset s)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType ℤ (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ m) (Ideal.Quotient.mkₐ_surjective ℤ m)
  have : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  have : Algebra.IsIntegral ℤ (A ⧸ m) := Algebra.IsIntegral.of_finite ℤ (A ⧸ m)
  have hinj : Function.Injective (algebraMap ℤ (A ⧸ m)) := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hk0
    have h1 : ((1 / (k : ℚ) : ℚ) : ℝ) ∈ A := hQ _
    have hr : (⟨_, h1⟩ : A) * (algebraMap ℤ A k) = 1 := by
      apply Subtype.ext
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
      simp
      field_simp
    have h2 := congrArg (Ideal.Quotient.mk m) hr
    rw [map_mul, map_one] at h2
    have e : Ideal.Quotient.mk m (algebraMap ℤ A k) = algebraMap ℤ (A ⧸ m) k := by
      simp
    rw [e, hk, mul_zero] at h2
    exact zero_ne_one h2
  have hfld := isField_of_isIntegral_of_isField hinj (Field.toIsField (A ⧸ m))
  exact Int.not_isField hfld
