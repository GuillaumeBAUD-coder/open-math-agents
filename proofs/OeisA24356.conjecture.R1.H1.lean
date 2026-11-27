import OMAReductions.R_OeisA24356_conjecture_R1

/-! The 4x4 Hankel matrix of primes 2,3,5,7,11,13,17 is singular; its determinant vanishes. -/

open OeisA24356

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  show a 4 = 0
  have h5 : Nat.nth Nat.Prime 5 = 13 := by
    have h : (13).Prime := by decide
    simpa using Nat.nth_count h
  have h6 : Nat.nth Nat.Prime 6 = 17 := by
    have h : (17).Prime := by decide
    simpa using Nat.nth_count h
  unfold a
  have hmat : (Matrix.of fun (i j : Fin 4) => (Nat.nth Nat.Prime (i.val + j.val) : ℤ))
      = !![2,3,5,7; 3,5,7,11; 5,7,11,13; 7,11,13,17] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h5, h6]
  rw [hmat]
  decide +kernel
