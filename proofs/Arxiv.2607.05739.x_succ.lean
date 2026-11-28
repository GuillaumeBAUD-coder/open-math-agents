import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

-- Problem: Integer values of $\tan(\arctan 1 + \arctan 2 + \cdots + \arctan n)$ — x succ
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean:74 (declaration Arxiv.«2607.05739».x_succ)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Proof idea. Write Z_n = A_n + i B_n for the Gaussian product. Multiplying by 1 + i (n + 1) gives

  A_{n+1} = A_n - (n + 1) B_n,      B_{n+1} = B_n + (n + 1) A_n,

so the recurrence for x_n = B_n / A_n is plain algebra, provided A_n is not zero. That
proviso is needed: if A_n were 0 then x_n would be 0 in Lean, the right-hand side would be
n + 1, and the left-hand side would be -1 / (n + 1).

The upstream file only records A_n ≠ 0 numerically (for n ≤ 3000). Here it is proved for
every n by reducing modulo 3, where the pair (A_n, B_n) follows a pattern of period 3:

  n ≡ 0 or 2 (mod 3):  3 ∤ A_n  and  3 ∣ B_n,
  n ≡ 1      (mod 3):  3 ∤ A_n  and  A_n ≡ B_n.

In particular A_n is never divisible by 3, hence never zero.
-/

open Arxiv.«2607.05739»

namespace OMAAux

lemma gaussProd_succ (n : ℕ) :
    gaussProd (n + 1) = gaussProd n * (⟨1, ((n + 1 : ℕ) : ℤ)⟩ : GaussianInt) := by
  unfold gaussProd
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma A_succ (n : ℕ) : A (n + 1) = A n - ((n : ℤ) + 1) * B n := by
  simp only [A, B, gaussProd_succ, Zsqrtd.re_mul]
  push_cast
  ring

lemma B_succ (n : ℕ) : B (n + 1) = B n + ((n : ℤ) + 1) * A n := by
  simp only [A, B, gaussProd_succ, Zsqrtd.im_mul]
  push_cast
  ring

/-- One step of the recurrence preserves the invariant modulo 3 (a finite check). -/
lemma step_mod_three : ∀ a b c : ZMod 3,
    (a ≠ 0 ∧ ((c = 1 ∧ a = b) ∨ (c ≠ 1 ∧ b = 0))) →
      (a - (c + 1) * b ≠ 0 ∧
        ((c + 1 = 1 ∧ a - (c + 1) * b = b + (c + 1) * a) ∨
          (c + 1 ≠ 1 ∧ b + (c + 1) * a = 0))) := by
  decide

/-- The invariant: modulo 3, `A n` is nonzero, and `B n` is `A n` or `0` according to `n`. -/
lemma inv_mod_three (n : ℕ) :
    ((A n : ℤ) : ZMod 3) ≠ 0 ∧
      (((n : ZMod 3) = 1 ∧ ((A n : ℤ) : ZMod 3) = ((B n : ℤ) : ZMod 3)) ∨
        ((n : ZMod 3) ≠ 1 ∧ ((B n : ℤ) : ZMod 3) = 0)) := by
  induction n with
  | zero =>
    have hA : A 0 = 1 := by simp [A, gaussProd]
    have hB : B 0 = 0 := by simp [B, gaussProd]
    rw [hA, hB]
    simp only [Int.cast_one, Int.cast_zero, Nat.cast_zero]
    decide
  | succ n ih =>
    have h := step_mod_three _ _ _ ih
    rw [A_succ, B_succ]
    push_cast
    exact h

/-- The real part of the Gaussian product never vanishes. -/
lemma A_ne_zero (n : ℕ) : A n ≠ 0 := by
  intro h
  have h3 := (inv_mod_three n).1
  rw [h] at h3
  exact h3 Int.cast_zero

end OMAAux

theorem OMA.solution : type_of% @Arxiv.«2607.05739».x_succ := by
  intro n _
  have hA : (A n : ℚ) ≠ 0 := by exact_mod_cast OMAAux.A_ne_zero n
  unfold x
  rw [OMAAux.A_succ, OMAAux.B_succ]
  push_cast
  -- Rewrite over the common denominator A n before cancelling it.
  rw [← mul_div_assoc, one_sub_div hA, div_add' _ _ _ hA, div_div_div_cancel_right₀ hA]
