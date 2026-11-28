import OMAStatements.S_oeis_a192240
import Mathlib

/-! Proof for OEIS A192240: write X + 3 = (X - 1) + 4 and expand by the binomial theorem.
By induction, (X - 1)^i is congruent modulo X^2 - X - 1 to (-1)^i (F(i+1) - F(i) X), since
X(X - 1) is congruent to 1. Hence (X + 3)^n minus the polynomial R = sum of
C(n,i) 4^(n-i) (-1)^i (F(i+1) - F(i) X) is divisible by the monic X^2 - X - 1; R has degree
at most 1, so it is the remainder, and its constant coefficient is the claimed sum.
Credit: Sudharsan Rajendiran -/

namespace OMA.P192240
open OMA.S_oeis_a192240 Polynomial

noncomputable def e (i : ℕ) : ℤ[X] :=
  (-1) ^ i * ((Nat.fib (i + 1) : ℤ[X]) - (Nat.fib i : ℤ[X]) * X)

lemma e_eq (i : ℕ) : e i = C ((-1) ^ i * (Nat.fib (i + 1) : ℤ)) +
    C (-((-1) ^ i * (Nat.fib i : ℤ))) * X := by
  simp only [e, map_mul, map_neg, map_pow, map_one, map_natCast]
  ring

lemma dvd_e (i : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣ (X - 1) ^ i - e i := by
  induction i with
  | zero => simp [e]
  | succ i ih =>
    obtain ⟨q, hq⟩ := ih
    have hf : (Nat.fib (i + 2) : ℤ[X]) = Nat.fib (i + 1) + Nat.fib i := by
      rw [Nat.fib_add_two]; push_cast; ring
    refine ⟨(X - 1) * q - (-1) ^ i * (Nat.fib i : ℤ[X]), ?_⟩
    simp only [e] at hq ⊢
    rw [pow_succ]
    linear_combination (X - 1) * hq + (-1) ^ i * hf

lemma monic_m : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  exact monic_X_pow_sub (by compute_degree!)

lemma degree_m : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  compute_degree!

theorem main' : ∀ n : ℕ,
    a n = ∑ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i) := by
  intro n
  set R : ℤ[X] := ∑ i ∈ Finset.range (n + 1), e i * 4 ^ (n - i) * (n.choose i : ℤ[X]) with hR
  have hsum : (X + 3 : ℤ[X]) ^ n =
      ∑ i ∈ Finset.range (n + 1), (X - 1) ^ i * 4 ^ (n - i) * (n.choose i : ℤ[X]) := by
    rw [← add_pow]; congr 1; norm_num; ring
  have hdvd : (X ^ 2 - X - 1 : ℤ[X]) ∣ (X + 3) ^ n - R := by
    rw [hsum, hR, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← sub_mul, ← sub_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_e i) _) _
  have hdeg : R.natDegree ≤ 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    rw [e_eq]
    have h4 : (4 : ℤ[X]) ^ (n - i) * (n.choose i : ℤ[X]) = C ((4 : ℤ) ^ (n - i) * n.choose i) := by
      simp
    rw [mul_assoc, h4]
    compute_degree!
  have hRmod : R %ₘ (X ^ 2 - X - 1) = R := by
    rw [modByMonic_eq_self_iff monic_m, degree_m]
    calc R.degree ≤ R.natDegree := degree_le_natDegree
      _ ≤ 1 := by exact_mod_cast hdeg
      _ < 2 := by norm_num
  unfold a
  rw [modByMonic_eq_of_dvd_sub monic_m hdvd, hRmod, hR, finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e_eq]
  have h4 : (4 : ℤ[X]) ^ (n - i) * (n.choose i : ℤ[X]) = C ((4 : ℤ) ^ (n - i) * n.choose i) := by
    simp
  rw [mul_assoc, h4, add_mul, mul_comm (C _ * X), ← mul_assoc, ← map_mul, coeff_add,
    coeff_mul_X_zero, coeff_C_zero]
  ring

end OMA.P192240

theorem OMA.solution : type_of% @OMA.S_oeis_a192240.main := OMA.P192240.main'
