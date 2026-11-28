import OMAStatements.S_oeis_a076552

-- Problem: oeis-a076552. Credit: @arcstone09.
-- Agent: codex. Model: gpt-6-astra (verified from current session metadata).
-- Classical identities formalized here; no claim of a new mathematical result.
-- Sources: https://oeis.org/A076552 and https://oeis.org/A060082
-- Bernoulli translation: https://dlmf.nist.gov/24.4.E12
-- Euler-Bernoulli relation: https://dlmf.nist.gov/24.4.E23
-- Bernoulli shift: https://dlmf.nist.gov/24.4.E1
-- The original definitions and the all-natural-number target are unchanged.
-- OEIS starts at n = 1. The Lean extension has a 0 = -1/3 and E_0 = 1.
-- Mathlib bernoulli uses B_1 = -1/2; only even Bernoulli indices enter a.


open Finset
open OMA.S_oeis_a076552

namespace A076552

lemma sum_pairs (f : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range (2 * n), f i) = ∑ k ∈ range n, (f (2*k) + f (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2*n+1+1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

lemma bernoulli_odd_difference (n : ℕ) (x : ℚ) :
    (Polynomial.bernoulli (2*n+1)).eval x -
      (Polynomial.bernoulli (2*n+1)).eval (-x) =
    2 * ∑ k ∈ range (n+1),
      bernoulli (2*k) * ((2*n+1).choose (2*k) : ℚ) * x^(2*n+1-2*k) := by
  simp only [Polynomial.bernoulli, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [← sum_sub_distrib, show 2*n+1+1 = 2*(n+1) by omega, sum_pairs, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  have he : 2*n+1-2*k = 2*(n-k)+1 := by omega
  have ho : 2*n+1-(2*k+1) = 2*(n-k) := by omega
  simp only [he, ho, pow_add, pow_mul, pow_one, neg_sq]
  ring

lemma scaled_power (n k : ℕ) (hk : k ≤ n) :
    (4 : ℚ)^(2*n+1) * (1/4 : ℚ)^(2*n+1-2*k) = 16^k := by
  have h : 2*n+1 = (2*n+1-2*k) + 2*k := by omega
  calc
    _ = (4 : ℚ)^((2*n+1-2*k)+2*k) * (1/4 : ℚ)^(2*n+1-2*k) := by rw [← h]
    _ = (4 * (1/4) : ℚ)^(2*n+1-2*k) * 4^(2*k) := by rw [pow_add, mul_pow]; ring
    _ = 16^k := by norm_num [pow_mul]

lemma bernoulli_sum_difference (n : ℕ) :
    (∑ k ∈ range (n+1), (16 : ℚ)^k * bernoulli (2*k) *
      ((2*n+1).choose (2*k) : ℚ)) =
    (4 : ℚ)^(2*n+1) / 2 * ((Polynomial.bernoulli (2*n+1)).eval (1/4) -
      (Polynomial.bernoulli (2*n+1)).eval (-(1/4))) := by
  rw [bernoulli_odd_difference]
  rw [show (4 : ℚ)^(2*n+1) / 2 * (2 * ∑ k ∈ range (n+1),
      bernoulli (2*k) * ((2*n+1).choose (2*k) : ℚ) * (1/4 : ℚ)^(2*n+1-2*k)) =
      (4 : ℚ)^(2*n+1) * ∑ k ∈ range (n+1),
      bernoulli (2*k) * ((2*n+1).choose (2*k) : ℚ) * (1/4 : ℚ)^(2*n+1-2*k) by ring]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hp := scaled_power n k (Nat.le_of_lt_succ (mem_range.mp hk))
  calc
    _ = ((4 : ℚ)^(2*n+1) * (1/4 : ℚ)^(2*n+1-2*k)) *
        bernoulli (2*k) * ((2*n+1).choose (2*k) : ℚ) := by rw [hp]
    _ = _ := by ring

lemma target_from_euler_bernoulli
    (h : ∀ n : ℕ, (eulerPoly (2*n)).eval (-(1/2 : ℚ)) =
      (2 : ℚ)^(2*n+1) / (2*n+1) *
        ((Polynomial.bernoulli (2*n+1)).eval (1/4) -
         (Polynomial.bernoulli (2*n+1)).eval (-(1/4)))) :
    type_of% @OMA.S_oeis_a076552.main := by
  intro n
  rw [a, bernoulli_sum_difference, h n]
  have hn : (2*n+1 : ℚ) ≠ 0 := by positivity
  have hp : (-4 : ℚ)^n = (-1 : ℚ)^n * 4^n := by rw [← mul_pow]; norm_num
  rw [hp]
  have hp2 : (4 : ℚ)^(2*n+1) = 2 * 4^n * 2^(2*n+1) := by
    rw [pow_add, pow_add, pow_one, pow_one, pow_mul, pow_mul]
    norm_num
    have hx : (16 : ℚ)^n = 4^n * 4^n := by rw [← mul_pow]; norm_num
    rw [hx]
    ring
  rw [hp2, pow_succ]
  field_simp

lemma initial_value : a 0 = -(1/3 : ℚ) := by norm_num [a]
lemma euler_initial : eulerPoly 0 = 1 := by rw [eulerPoly]; simp

end A076552


open Polynomial Finset
namespace A076552

lemma hasse_bernoulli (n k : ℕ) (hk : k ≤ n) :
    Polynomial.hasseDeriv k (Polynomial.bernoulli n) =
      (n.choose k : ℚ) • Polynomial.bernoulli (n-k) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_bernoulli, Polynomial.coeff_bernoulli]
  by_cases hi : i+k ≤ n
  · rw [if_pos hi, if_pos (by omega : i ≤ n-k)]
    have hc := Nat.choose_mul (n := n) (k := i+k) (s := k) (by omega)
    simp only [Nat.add_sub_cancel] at hc
    have hcq : (n.choose (i+k) : ℚ) * ((i+k).choose k : ℚ) =
        (n.choose k : ℚ) * ((n-k).choose i : ℚ) := by exact_mod_cast hc
    rw [show n-(i+k) = n-k-i by omega]
    change _ = (n.choose k : ℚ) * _
    calc
      _ = _root_.bernoulli (n-k-i) * ((n.choose (i+k) : ℚ) * ((i+k).choose k : ℚ)) := by ring
      _ = _ := by rw [hcq]; ring
  · rw [if_neg hi, if_neg (by omega : ¬ i ≤ n-k)]
    simp

lemma bernoulli_translate (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x+y) =
    ∑ k ∈ range (n+1), (n.choose k : ℚ) *
      (Polynomial.bernoulli (n-k)).eval x * y^k := by
  have ht : Polynomial.taylor x (Polynomial.bernoulli n) =
      ∑ k ∈ range (n+1), Polynomial.monomial k
        ((n.choose k : ℚ) * (Polynomial.bernoulli (n-k)).eval x) := by
    ext i
    rw [Polynomial.taylor_coeff]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hi : i ≤ n
    · rw [hasse_bernoulli n i hi]
      simp [Polynomial.eval_smul, show i < n+1 by omega]
    · have hz : Polynomial.hasseDeriv i (Polynomial.bernoulli n) = 0 := by
        ext j
        rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_bernoulli,
          if_neg (by omega : ¬ j+i ≤ n)]
        simp
      rw [hz]
      simp [show ¬ i < n+1 by omega]
  have he := congrArg (Polynomial.eval y) ht
  simpa [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_assoc, add_comm] using he

lemma bernoulli_translate_rev (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x+y) =
    ∑ k ∈ range (n+1), (n.choose k : ℚ) *
      (Polynomial.bernoulli k).eval x * y^(n-k) := by
  rw [bernoulli_translate, ← sum_range_reflect]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkn, Nat.choose_symm hkn]

lemma scaled_translate (n : ℕ) (x : ℚ) :
    (2 : ℚ)^n * (Polynomial.bernoulli n).eval (x+1/2) =
    ∑ k ∈ range (n+1), (n.choose k : ℚ) * 2^k *
      (Polynomial.bernoulli k).eval x := by
  rw [bernoulli_translate_rev, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  have hp : (2 : ℚ)^n * (1/2 : ℚ)^(n-k) = 2^k := by
    calc
      _ = (2 : ℚ)^((n-k)+k) * (1/2 : ℚ)^(n-k) := by rw [Nat.sub_add_cancel hkn]
      _ = (2*(1/2) : ℚ)^(n-k) * 2^k := by rw [pow_add, mul_pow]; ring
      _ = _ := by norm_num
  calc
    _ = ((2 : ℚ)^n * (1/2 : ℚ)^(n-k)) * (n.choose k : ℚ) *
        (Polynomial.bernoulli k).eval x := by ring
    _ = _ := by rw [hp]; ring

noncomputable def eulerBernoulliValue (n : ℕ) (t : ℚ) : ℚ :=
  (2 : ℚ)^(n+1) / (n+1) *
    ((Polynomial.bernoulli (n+1)).eval (t+1/2) - (Polynomial.bernoulli (n+1)).eval t)

lemma eulerBernoulli_recurrence (n : ℕ) (t : ℚ) :
    (∑ k ∈ range (n+1), (n.choose k : ℚ) * eulerBernoulliValue k t) +
      eulerBernoulliValue n t = 2 * (2*t)^n := by
  have hn : (n+1 : ℚ) ≠ 0 := by positivity
  have hs : (∑ k ∈ range (n+1), (n.choose k : ℚ) * eulerBernoulliValue k t) =
      1 / (n+1 : ℚ) * ∑ j ∈ range (n+2), ((n+1).choose j : ℚ) * 2^j *
        ((Polynomial.bernoulli j).eval (t+1/2) - (Polynomial.bernoulli j).eval t) := by
    conv_rhs => rw [show n+2 = (n+1)+1 by omega, sum_range_succ']
    simp only [Polynomial.bernoulli_zero, Polynomial.eval_one, sub_self, mul_zero, add_zero,
      mul_sum]
    apply sum_congr rfl
    intro k hk
    have hk0 : (k+1 : ℚ) ≠ 0 := by positivity
    have hc : (n+1 : ℚ) * (n.choose k : ℚ) = ((n+1).choose (k+1) : ℚ) * (k+1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    have hcdiv : (n.choose k : ℚ) / (k+1) =
        ((n+1).choose (k+1) : ℚ) / (n+1) := by
      apply (div_eq_div_iff hk0 hn).2
      nlinarith [hc]
    dsimp [eulerBernoulliValue]
    push_cast
    calc
      _ = ((n.choose k : ℚ) / (k+1)) * 2^(k+1) *
          ((Polynomial.bernoulli (k+1)).eval (t+1/2) -
            (Polynomial.bernoulli (k+1)).eval t) := by ring
      _ = _ := by rw [hcdiv]; ring
  rw [hs]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← scaled_translate, ← scaled_translate]
  rw [show t+1/2+1/2 = 1+t by ring, Polynomial.bernoulli_eval_one_add]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  dsimp [eulerBernoulliValue]
  rw [pow_succ, mul_pow]
  field_simp
  <;> ring

lemma euler_eq_bernoulli (n : ℕ) (x : ℚ) :
    (OMA.S_oeis_a076552.eulerPoly n).eval x = eulerBernoulliValue n (x/2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [OMA.S_oeis_a076552.eulerPoly]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_smul, Polynomial.eval_finsetSum, smul_eq_mul]
    have hh := eulerBernoulli_recurrence n (x/2)
    rw [sum_range_succ] at hh
    simp only [Nat.choose_self, Nat.cast_one, one_mul] at hh
    have he : (∑ k : Fin n, (n.choose k.val : ℚ) *
        (OMA.S_oeis_a076552.eulerPoly k.val).eval x) =
        ∑ k ∈ range n, (n.choose k : ℚ) * eulerBernoulliValue k (x/2) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro k hk
      rw [ih k.val k.isLt]
    rw [he]
    have hx : 2 * (x/2) = x := by ring
    rw [hx] at hh
    linarith

end A076552

-- The standard identity at degree 2n and argument -1/2 closes the exact target.
theorem OMA.solution : type_of% @OMA.S_oeis_a076552.main := by
  apply A076552.target_from_euler_bernoulli
  intro n
  have he := A076552.euler_eq_bernoulli (2*n) (-(1/2 : ℚ))
  norm_num [A076552.eulerBernoulliValue] at he
  exact he
