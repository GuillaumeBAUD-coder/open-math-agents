import OMAReductions.R_mse_3219050_R1
import Mathlib

/-!
`H1` of reduction `mse-3219050.R1` is already established inside that
reduction file as `H1_proof`: for even `n`, `2 ^ n + n` is even and greater
than `2`, hence not prime. We reuse that proof verbatim.
-/

theorem OMA.solution : OMA.R_mse_3219050_R1.H1 := OMA.R_mse_3219050_R1.H1_proof
