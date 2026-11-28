import OMAReductions.R_mse_3219050_R1
import Mathlib

/-!
`H2` of reduction `mse-3219050.R1` is already proved inside that reduction
file (`H2_proof`): for odd `n`, one of `2 ^ n - n` and `2 ^ n + n` is
divisible by `3`, so primality forces it to be `3`, which is impossible;
hence `3 ∣ n`.
-/

theorem OMA.solution : OMA.R_mse_3219050_R1.H2 := OMA.R_mse_3219050_R1.H2_proof
