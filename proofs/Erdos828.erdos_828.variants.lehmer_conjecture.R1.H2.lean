import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1
import Mathlib

-- Step Erdos828.erdos_828.variants.lehmer_conjecture.R1.H2: hypothesis H2 of reduction Erdos828.erdos_828.variants.lehmer_conjecture.R1
-- Credit: @ivillar

/-!
For a prime `n` the totient is `n - 1`, which divides `n - 1`.
-/
namespace F2E828

theorem prime_case : ∀ n : ℕ, 1 < n → Prime n → Nat.totient n ∣ n - 1 := by
  intro n _ hn
  rw [Nat.totient_prime (Nat.prime_iff.mpr hn)]

end F2E828

theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H2 :=
  F2E828.prime_case
