import OMAReductions.R_mse_1595838_R1

/-!
# Proof of `mse-1595838.R1.H1`

For `8 < n < m` with `n ∣ m`, we have `m ≥ 2n ≥ n + 3`, so `F_n ∣ F_m` with quotient
`d = F_m / F_n ≥ 3`. Since `φ(d) ≥ 2` for `d ≥ 3` (as `φ(d)` is positive and even) and
`φ(F_n) * φ(d) ≤ φ(F_n * d) = φ(F_m)`, we obtain `φ(F_n) < φ(F_m)`.
-/

theorem OMA.solution : OMA.R_mse_1595838_R1.H1 := by
  intro n m hn hlt hdvd
  obtain ⟨k, rfl⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> omega
  have hm3 : n + 3 ≤ n * k := by nlinarith
  have hfib_dvd : Nat.fib n ∣ Nat.fib (n * k) := Nat.fib_dvd n (n * k) (dvd_mul_right n k)
  obtain ⟨d, hd⟩ := hfib_dvd
  have hfn_pos : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  have hfib3 : 3 * Nat.fib n ≤ Nat.fib (n + 3) := by
    have h1 : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
      rw [Nat.fib_add_two, add_comm]
    have h2 : Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
      rw [show n + 3 = (n + 1) + 2 by omega, Nat.fib_add_two, add_comm]
    have hle : Nat.fib n ≤ Nat.fib (n + 1) := Nat.fib_mono (by omega)
    omega
  have hfib_le : Nat.fib (n + 3) ≤ Nat.fib (n * k) := Nat.fib_mono hm3
  have hd3 : 3 ≤ d := by nlinarith
  have hd_even : Even d.totient := Nat.totient_even (by omega)
  have hd_pos : 0 < d.totient := Nat.totient_pos.mpr (by omega)
  have hd_ge2 : 2 ≤ d.totient := by
    obtain ⟨t, ht⟩ := hd_even
    omega
  have hfn_tot_pos : 0 < (Nat.fib n).totient := Nat.totient_pos.mpr hfn_pos
  have hmul : (Nat.fib n).totient * d.totient ≤ (Nat.fib n * d).totient :=
    Nat.totient_super_multiplicative (Nat.fib n) d
  rw [← hd] at hmul
  have hlt_tot : (Nat.fib n).totient < (Nat.fib (n * k)).totient := by nlinarith
  exact ne_of_lt hlt_tot
