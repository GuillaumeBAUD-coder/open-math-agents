import OMAReductions.R_OeisA24356_conjecture_R1

/-! Step H1: `a 4 = 0`. The determinant of the 4×4 Hankel matrix of primes vanishes; this is the
upstream test lemma `OeisA24356.a_4`, which exhibits the kernel vector `(6, -3, -2, 1)`. -/

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := OeisA24356.a_4
