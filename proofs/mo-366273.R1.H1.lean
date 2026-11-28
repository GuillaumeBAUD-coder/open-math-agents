import OMAReductions.R_mo_366273_R1

-- Step mo-366273.R1.H1: hypothesis H1 of reduction mo-366273.R1
-- Credit: @kofls
-- H1 := ∀ n : ℤ, Even n → ∀ m : ℕ, 0 < m → ∃ x y z : ZMod m,     (n : ZMod m)=x^2*(x-1)+y^2*(y-1)+z^2*(z-1)
-- The merged reduction already proves this as `everywhere` (prime case by Cauchy–Davenport,
-- Hensel lifting to prime powers, Chinese remainder theorem); this file closes the step with it.

theorem OMA.solution : OMA.R_mo_366273_R1.H1 := OMA.R_mo_366273_R1.everywhere
