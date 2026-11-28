import OMAStatements.S_oeis_a001700

namespace OMA.A1700
open Finset

noncomputable def rise (a : ℚ) (k : ℕ) := (ascPochhammer ℚ k).eval a

lemma rise_step (a : ℚ) (k : ℕ) : rise a (k+1) = rise a k * (a+k) := by
  exact ascPochhammer_succ_eval _ _

noncomputable def weight (k m : ℕ) : ℚ :=
  (-1)^k * rise (1/2) k * rise (3/2) m / ((k+m+1).factorial : ℚ)

lemma step (k m : ℕ) : weight k m + weight (k+1) m = weight k (m+1) := by
  unfold weight
  rw [rise_step, rise_step, pow_succ]
  rw [show k+1+m+1 = (k+m+1)+1 by omega,
      show k+(m+1)+1 = (k+m+1)+1 by omega, Nat.factorial_succ (k+m+1)]
  push_cast
  field_simp
  ring

lemma collapse (n m : ℕ) :
    (∑ k ∈ range (n+1), (n.choose k : ℚ) * weight k m) = weight 0 (m+n) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_choose_succ_mul (fun k _ => weight k m) n,
      ← Finset.sum_add_distrib]
    simp_rw [← mul_add, step]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (m+1)

lemma hyp_weight (n : ℕ) : OMA.S_oeis_a001700.hyp n = weight 0 n := by
  rw [show weight 0 n = weight 0 (0+n) by simp, ← collapse]
  unfold OMA.S_oeis_a001700.hyp
  apply Finset.sum_congr rfl
  intro k hk
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have two : (ascPochhammer ℚ k).eval 2 = ((k+1).factorial : ℚ) := by
    have h := factorial_mul_ascPochhammer ℚ 1 k
    norm_num [Nat.add_comm] at h ⊢
    exact h
  rw [two]
  simp [weight, rise]
  field_simp

lemma odd_product (n : ℕ) :
    (4:ℚ)^n * rise (3/2) n * (n.factorial : ℚ) = ((2*n+1).factorial : ℚ) := by
  induction n with
  | zero => simp [rise]
  | succ n ih =>
    rw [show 2*(n+1)+1 = ((2*n+1)+1)+1 by omega,
      Nat.factorial_succ ((2*n+1)+1), Nat.factorial_succ (2*n+1),
      Nat.factorial_succ n, pow_succ, rise_step]
    push_cast
    rw [← ih]
    ring

end OMA.A1700

open OMA.A1700
theorem OMA.solution : type_of% @OMA.S_oeis_a001700.main := by
  intro n
  rw [hyp_weight]
  have hc := Nat.choose_mul_factorial_mul_factorial
    (show n+1 ≤ 2*n+1 by omega)
  rw [show 2*n+1-(n+1) = n by omega] at hc
  have h : (((2*n+1).choose (n+1) : ℕ) : ℚ) * ((n+1).factorial : ℚ) *
      (n.factorial : ℚ) = ((2*n+1).factorial : ℚ) := by exact_mod_cast hc
  simp only [weight, pow_zero, zero_add, rise, ascPochhammer_zero, Polynomial.eval_one,
    one_mul]
  change _ = 4^n * (rise (3/2) n / _)
  have h' := odd_product n
  field_simp
  nlinarith [h, h', (show (0:ℚ) < n.factorial by positivity)]
