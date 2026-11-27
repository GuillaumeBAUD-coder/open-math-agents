import OMAReductions.R_OeisA109074_conjecture_R1_H2_R1
import Mathlib

-- Step OeisA109074.conjecture.R1.H2.R1.H2: hypothesis H2 of reduction OeisA109074.conjecture.R1.H2.R1
-- Credit: @ivillar
-- Proof: a(2t) = 3t+1 and a(2t+1) = 3t+2. Pairing the indices 2t, 2t+1 and reflecting t to n-1-t,
-- row(2n) = (3n+1) 3^(2n) (2n)! prod_(s<2n) (3s+2) and
-- row(2n+1) = (3n+2)(6n+3) 3^(2n) (2n)! prod_(s<2n) (3s+4).
-- Splitting (3k)! by residues mod 3 then gives the identity.

open Finset

namespace OMA.L5A109074

/-- The row product of `H2`, with `a j = j + 1 + j / 2`. -/
def rowF (j : ℕ) : ℕ :=
  (j+1+j/2) * ∏ i ∈ range j, ((j+1+j/2) - (i+1+i/2)) * ((j+1+j/2) + (i+1+i/2))

lemma prod_range_two_mul (f : ℕ → ℕ) (n : ℕ) :
    ∏ i ∈ range (2 * n), f i = ∏ t ∈ range n, (f (2 * t) * f (2 * t + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ]
    ring

lemma prod_two_sided (g : ℕ → ℕ) (n : ℕ) :
    ∏ t ∈ range n, (g (n - 1 - t) * g (n + t)) = ∏ s ∈ range (2 * n), g s := by
  rw [prod_mul_distrib, prod_range_reflect g n, two_mul, prod_range_add]

lemma prod_three (k : ℕ) : ∏ s ∈ range k, (3 * s + 3) = 3 ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, pow_succ, Nat.factorial_succ]
    ring

lemma fact_three (k : ℕ) : (3 * k).factorial =
    3 ^ k * k.factorial * ((∏ s ∈ range k, (3 * s + 1)) * ∏ s ∈ range k, (3 * s + 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (3 * (k + 1)).factorial = (3 * k + 3) * (3 * k + 2) * (3 * k + 1) * (3 * k).factorial := by
      rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, Nat.factorial_succ,
        show 3 * k + 2 = 3 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [e, ih, prod_range_succ, prod_range_succ, Nat.factorial_succ, pow_succ]
    ring

lemma rowF_even (n : ℕ) :
    rowF (2 * n) = (3 * n + 1) * (3 ^ (2 * n) * (2 * n).factorial * ∏ s ∈ range (2 * n), (3 * s + 2)) := by
  have hP : ∏ t ∈ range n, ((3*n+1 - (2*t+1+2*t/2)) * (3*n+1 + (2*t+1+2*t/2)) *
      ((3*n+1 - (2*t+1+1+(2*t+1)/2)) * (3*n+1 + (2*t+1+1+(2*t+1)/2)))) =
      3 ^ (2 * n) * (2 * n).factorial * ∏ s ∈ range (2 * n), (3 * s + 2) := by
    rw [← prod_three, ← prod_two_sided, ← prod_two_sided, ← prod_mul_distrib]
    apply prod_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    rw [show 3*n+1 - (2*t+1+2*t/2) = 3*(n-1-t)+3 by omega,
      show 3*n+1 + (2*t+1+2*t/2) = 3*(n+t)+2 by omega,
      show 3*n+1 - (2*t+1+1+(2*t+1)/2) = 3*(n-1-t)+2 by omega,
      show 3*n+1 + (2*t+1+1+(2*t+1)/2) = 3*(n+t)+3 by omega]
    ring
  unfold rowF
  rw [show 2*n+1+2*n/2 = 3*n+1 by omega, prod_range_two_mul, hP]

lemma rowF_odd (n : ℕ) :
    rowF (2 * n + 1) = (3 * n + 2) * (6 * n + 3) *
      (3 ^ (2 * n) * (2 * n).factorial * ∏ s ∈ range (2 * n), (3 * s + 4)) := by
  have hP : ∏ t ∈ range n, ((3*n+2 - (2*t+1+2*t/2)) * (3*n+2 + (2*t+1+2*t/2)) *
      ((3*n+2 - (2*t+1+1+(2*t+1)/2)) * (3*n+2 + (2*t+1+1+(2*t+1)/2)))) =
      3 ^ (2 * n) * (2 * n).factorial * ∏ s ∈ range (2 * n), (3 * s + 4) := by
    rw [← prod_three, ← prod_two_sided, ← prod_two_sided, ← prod_mul_distrib]
    apply prod_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    rw [show 3*n+2 - (2*t+1+2*t/2) = 3*(n-1-t)+4 by omega,
      show 3*n+2 + (2*t+1+2*t/2) = 3*(n+t)+3 by omega,
      show 3*n+2 - (2*t+1+1+(2*t+1)/2) = 3*(n-1-t)+3 by omega,
      show 3*n+2 + (2*t+1+1+(2*t+1)/2) = 3*(n+t)+4 by omega]
    ring
  unfold rowF
  rw [show 2*n+1+1+(2*n+1)/2 = 3*n+2 by omega, prod_range_succ, prod_range_two_mul, hP,
    show 3*n+2 - (2*n+1+2*n/2) = 1 by omega, show 3*n+2 + (2*n+1+2*n/2) = 6*n+3 by omega]
  ring

lemma key (n : ℕ) : 2*(4*n+2) * (rowF (2*n) * rowF (2*n+1)) =
    3^(2*n) * (6*n+4).factorial * (2*n+1).factorial := by
  rw [rowF_even, rowF_odd]
  have h1 : (6*n+4).factorial = (6*n+4) * (3*(2*n+1)).factorial := by
    rw [show 6*n+4 = 3*(2*n+1)+1 by ring, Nat.factorial_succ]
  have hG1 : ∏ s ∈ range (2*n+1), (3*s+1) = ∏ s ∈ range (2*n), (3*s+4) := by
    rw [prod_range_succ']
    simp only [mul_zero, zero_add, mul_one]
    exact prod_congr rfl (fun s _ => by ring)
  have hG2 : ∏ s ∈ range (2*n+1), (3*s+2) = (∏ s ∈ range (2*n), (3*s+2)) * (3*(2*n)+2) :=
    prod_range_succ _ _
  rw [h1, fact_three, hG1, hG2, Nat.factorial_succ (2*n)]
  ring

end OMA.L5A109074

theorem OMA.solution : OMA.R_OeisA109074_conjecture_R1_H2_R1.H2 := by
  intro n a row
  exact OMA.L5A109074.key n
