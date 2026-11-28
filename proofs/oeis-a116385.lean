import OMAStatements.S_oeis_a116385
import Mathlib

/-!
Proof of Mathar's A116385 recurrence (OEIS, June 13, 2014).
Source: https://oeis.org/A116385
Statement: vivanpoddar, merged PR #36543.
Adapted from our earlier checked proof against statement PR #17472.

The even terms a(2m+4) equal (2m+5)!/((m+1)!(m+4)!), and the next
odd term is twice this. The factorial ratio's first-order recurrence gives
the required second-order relation by a polynomial linear combination.
Both parity cases of the original recurrence reduce to that relation.
These parity formulas agree with the binomial expression already in OEIS.
The linked Eremin paper concerns a different identity for this sequence;
no proof of this exact five-term recurrence was found in the source review.
-/

open OMA.S_oeis_a116385

namespace A116385Proof

def b (m : ℕ) : ℚ := (2*m+5).factorial / ((m+1).factorial * (m+4).factorial : ℚ)

lemma even_formula (m : ℕ) : (a (2*m+4) : ℚ) = b m := by
  simp only [a, besselCoeff]
  simp (disch := omega) only [if_pos, if_neg]
  rw [show (2*m+4-2)/2=m+1 by omega,
    show (2*m+4-4)/2=m by omega]
  push_cast
  rw [Nat.cast_choose ℚ (show m+1 ≤ 2*m+4 by omega),
    Nat.cast_choose ℚ (show m ≤ 2*m+4 by omega)]
  rw [show 2*m+4-(m+1)=m+3 by omega, show 2*m+4-m=m+4 by omega]
  unfold b
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma odd_formula (m : ℕ) : (a (2*m+5) : ℚ) = 2*b m := by
  simp only [a, besselCoeff]
  simp (disch := omega) only [if_pos, if_neg]
  rw [show (2*m+5-3)/2=m+1 by omega]
  push_cast
  rw [Nat.cast_choose ℚ (show m+1 ≤ 2*m+5 by omega)]
  rw [show 2*m+5-(m+1)=m+4 by omega]
  unfold b
  ring

lemma b_step (m : ℕ) :
    ((m : ℚ)+2)*((m : ℚ)+5)*b (m+1) = (2*(m : ℚ)+7)*(2*(m : ℚ)+6)*b m := by
  unfold b
  rw [show 2*(m+1)+5=(2*m+5)+1+1 by omega,
    show m+1+4=(m+4)+1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma b_second (m : ℕ) :
    (2*(m : ℚ)+12)*b (m+2) - (14*(m : ℚ)+68)*b (m+1)
      + (24*(m : ℚ)+84)*b m = 0 := by
  have h1 := b_step m
  have h2 := b_step (m+1)
  push_cast at h2
  have hm : (m : ℚ)+3 ≠ 0 := by positivity
  apply (mul_eq_zero.mp (show ((m : ℚ)+3) *
    ((2*(m : ℚ)+12)*b (m+2) - (14*(m : ℚ)+68)*b (m+1)
      + (24*(m : ℚ)+84)*b m) = 0 from ?_)).resolve_left hm
  linear_combination 2*h2 - 6*h1

end A116385Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a116385.main := by
  intro n hn
  apply (Int.cast_injective (α := ℚ))
  push_cast
  by_cases hs : n < 8
  · interval_cases n <;>
      norm_num [a, besselCoeff, Nat.choose] at *
  have hex : ∃ m, n = 2*m+8 ∨ n = 2*m+9 := ⟨(n-8)/2, by omega⟩
  rcases hex with ⟨m, rfl | rfl⟩
  · rw [show 2*m+8-1=2*(m+1)+5 by omega,
      show 2*m+8-2=2*(m+1)+4 by omega,
      show 2*m+8-3=2*m+5 by omega,
      show 2*m+8-4=2*m+4 by omega]
    rw [show 2*m+8=2*(m+2)+4 by omega]
    simp only [A116385Proof.even_formula, A116385Proof.odd_formula,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [A116385Proof.b_second m]
  · rw [show 2*m+9-1=2*(m+2)+4 by omega,
      show 2*m+9-2=2*(m+1)+5 by omega,
      show 2*m+9-3=2*(m+1)+4 by omega,
      show 2*m+9-4=2*m+5 by omega]
    rw [show 2*m+9=2*(m+2)+5 by omega]
    simp only [A116385Proof.even_formula, A116385Proof.odd_formula,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [A116385Proof.b_second m]
