import OMAStatements.S_oeis_a001076

-- Problem: A001076: Denominators of continued fraction convergents to sqrt(5).
-- Credit: @MBimrose
-- Route: A001077 n = A001076 (n+1) - 2*A001076 n  (two-step induction; both sequences satisfy
-- u(n+2) = 4*u(n+1) + u(n)), then rearrange.  Target follows from the key lemma at n+1.

open OMA.S_oeis_a001076

lemma key (n : ℕ) : (A001077 n : ℤ) + 2 * (A001076 n : ℤ) = (A001076 (n + 1) : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [A001076, A001077]
  | one => norm_num [A001076, A001077]
  | more n ih1 ih2 =>
      have hA2 : (A001076 (n + 2) : ℤ) = 4 * (A001076 (n + 1) : ℤ) + (A001076 n : ℤ) := by
        have h : A001076 (n + 2) = 4 * A001076 (n + 1) + A001076 n := rfl
        rw [h]; push_cast; ring
      have hB2 : (A001077 (n + 2) : ℤ) = 4 * (A001077 (n + 1) : ℤ) + (A001077 n : ℤ) := by
        have h : A001077 (n + 2) = 4 * A001077 (n + 1) + A001077 n := rfl
        rw [h]; push_cast; ring
      have hA3 : (A001076 (n + 3) : ℤ) = 4 * (A001076 (n + 2) : ℤ) + (A001076 (n + 1) : ℤ) := by
        have h : A001076 (n + 3) = 4 * A001076 (n + 2) + A001076 (n + 1) := rfl
        rw [h]; push_cast; ring
      linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a001076.main := by
  intro n
  have h := key (n + 1)
  have h2 : (A001076 (n + 1 + 1) : ℤ) = (A001076 (n + 2) : ℤ) := by norm_num
  linarith
