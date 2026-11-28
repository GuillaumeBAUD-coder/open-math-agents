import OMAReductions.R_mse_5097283_R1

/-!
# Proof of `mse-5097283.R1.H1`

Verifies by iterative arbitrary-precision integer arithmetic in the Lean kernel (`decide +kernel`)
that for every `1 ≤ n ≤ 5000`, `4 ^ n < 3 ^ (n + 1) % 2 ^ n * 2 ^ n + 3 ^ n` holds if and only if
`n ∈ {1, 2, 5, 10}`.

The recurrence advances `(n, 2^n, 3^n) ↦ (n + 1, 2 * 2^n, 3 * 3^n)` in `5000` steps, avoiding
repeated exponentiation.
-/

namespace Mse5097283R1H1Proof

private def isHit (n : ℕ) : Bool :=
  n == 1 || n == 2 || n == 5 || n == 10

private def checkOne (n p2 p3 : ℕ) : Bool :=
  decide (p2 * p2 < (3 * p3) % p2 * p2 + p3) == isHit n

private def checkLoop (n p2 p3 : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkOne n p2 p3 && checkLoop (n + 1) (2 * p2) (3 * p3) k

private lemma isHit_iff (n : ℕ) :
    isHit n = true ↔ n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10 := by
  simp [isHit, or_assoc]

private lemma checkOne_sound (n : ℕ) (h : checkOne n (2 ^ n) (3 ^ n) = true) :
    4 ^ n < 3 ^ (n + 1) % 2 ^ n * 2 ^ n + 3 ^ n ↔ n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10 := by
  have heq : decide (2 ^ n * 2 ^ n < (3 * 3 ^ n) % 2 ^ n * 2 ^ n + 3 ^ n) = isHit n :=
    beq_iff_eq.mp h
  have h4 : 2 ^ n * 2 ^ n = 4 ^ n := by
    rw [← mul_pow]
    norm_num
  have h3 : 3 * 3 ^ n = 3 ^ (n + 1) := by
    rw [pow_succ']
  rw [h4, h3] at heq
  rw [← isHit_iff, ← heq, decide_eq_true_iff]

private lemma checkLoop_sound : ∀ k n : ℕ,
    checkLoop n (2 ^ n) (3 ^ n) k = true →
    ∀ m : ℕ, n ≤ m → m < n + k →
      (4 ^ m < 3 ^ (m + 1) % 2 ^ m * 2 ^ m + 3 ^ m ↔ m = 1 ∨ m = 2 ∨ m = 5 ∨ m = 10) := by
  intro k
  induction k with
  | zero =>
    intro n _ m hm1 hm2
    omega
  | succ k ih =>
    intro n hok m hm1 hm2
    unfold checkLoop at hok
    rw [Bool.and_eq_true] at hok
    rcases eq_or_lt_of_le hm1 with rfl | hlt
    · exact checkOne_sound n hok.1
    · have h2 : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ']
      have h3 : 3 * 3 ^ n = 3 ^ (n + 1) := by rw [pow_succ']
      rw [h2, h3] at hok
      exact ih (n + 1) hok.2 m (by omega) (by omega)

private lemma checkLoop_5000 : checkLoop 1 (2 ^ 1) (3 ^ 1) 5000 = true := by decide +kernel

end Mse5097283R1H1Proof

theorem OMA.solution : OMA.R_mse_5097283_R1.H1 := by
  intro n h1 h2
  exact Mse5097283R1H1Proof.checkLoop_sound 5000 1 Mse5097283R1H1Proof.checkLoop_5000 n h1 (by omega)
