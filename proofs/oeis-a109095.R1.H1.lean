import OMAReductions.R_oeis_a109095_R1
import Mathlib.NumberTheory.Bertrand

/-!
# Proof of `oeis-a109095.R1.H1`

Proves that if `2 ≤ a ≤ b < N` and `N! = a! * b!`, then `N < 2 * b` and (`N = b + 1 → N = a!`).

For `N < 2 * b`: if `2 * b ≤ N`, Bertrand's postulate yields a prime `p` with `b < p ≤ 2 * b ≤ N`.
Then `p ∣ N! = a! * b!`, so `p ∣ a!` or `p ∣ b!`, implying `p ≤ a ≤ b` or `p ≤ b`, contradiction.
For `N = b + 1`: `(b + 1) * b! = a! * b!`, and cancelling `b! > 0` yields `b + 1 = a!`.
-/

theorem OMA.solution : OMA.R_oeis_a109095_R1.H1 := by
  intro N a b ha haN hb hbN heq hab
  constructor
  · by_contra hge
    have h2b : 2 * b ≤ N := by omega
    obtain ⟨p, hp, hbp, hp2b⟩ := Nat.exists_prime_lt_and_le_two_mul b (by omega)
    have hpN : p ≤ N := le_trans hp2b h2b
    have hpdvd : p ∣ Nat.factorial N := hp.dvd_factorial.mpr hpN
    rw [heq] at hpdvd
    rcases hp.dvd_mul.mp hpdvd with hda | hdb
    · have := hp.dvd_factorial.mp hda
      omega
    · have := hp.dvd_factorial.mp hdb
      omega
  · intro hN
    subst hN
    rw [Nat.factorial_succ] at heq
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos b) heq
