import OMAStatements.S_mo_128018

open Polynomial OMA.S_mo_128018

-- Barry Cipra's counterexample in the source discussion uses the monic gcd of 2X with itself.
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_128018.main) := by
  intro claim
  let P : ℤ[X] := C 2 * X
  have himg : integerImage P = C (2 : ℚ) * X := by simp [integerImage, P, Polynomial.C_ofNat]
  have hg : monicGCD (integerImage P) (integerImage P) X := by
    rw [himg]
    refine ⟨monic_X, ⟨C 2, by ring⟩, ⟨C 2, by ring⟩, ?_⟩
    intro H hH _
    have hunit : C (1 / 2 : ℚ) * (C 2 * X) = X := by
      rw [← mul_assoc, ← C_mul]
      norm_num
    rw [← hunit]
    exact dvd_mul_of_dvd_right hH _
  have hleast : leastIntegralMultiple X X := by
    refine ⟨1, by decide, ?_, fun m hm _ => hm⟩
    simp [integerImage]
  have hval : complexValue P (1 / 2) = (1 : ℤ) := by
    norm_num [complexValue, P]
  obtain ⟨_, _, d, _, _, hd, _, _⟩ :=
    claim P P X X hg hleast (1 / 2) ⟨1, hval⟩ ⟨1, hval⟩
  have hd' : (1 / 2 : ℂ) = (d : ℂ) := by simpa [complexValue] using hd
  have hc : ((2 * d : ℤ) : ℂ) = 1 := by push_cast; rw [← hd']; norm_num
  have hi : 2 * d = 1 := by exact_mod_cast hc
  omega
