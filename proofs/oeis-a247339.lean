import OMAStatements.S_oeis_a247339
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a247339.main := by
  intro n hn
  have hne1 : n ^ 2 + 1 ≠ 1 := by
    have : 0 < n ^ 2 := by positivity
    omega
  have hp : (Nat.minFac (n ^ 2 + 1)).Prime := Nat.minFac_prime hne1
  set p := Nat.minFac (n ^ 2 + 1) with hpdef
  have hpd : p ∣ n ^ 2 + 1 := Nat.minFac_dvd _
  have hp2 := hp.two_le
  have hmlt : n % p < p := Nat.mod_lt _ (by omega)
  have hdvd : p ∣ (n % p) ^ 2 + 1 := by
    have h : (n % p) ^ 2 + 1 ≡ n ^ 2 + 1 [MOD p] := ((Nat.mod_modEq n p).pow 2).add_right 1
    exact (Nat.ModEq.dvd_iff h (dvd_refl p)).mpr hpd
  have hm1 : 1 ≤ n % p := by
    by_contra h
    have h0 : n % p = 0 := by omega
    rw [h0] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  refine ⟨n % p, hm1, Nat.mod_le _ _, ?_⟩
  have hlt : (n % p) ^ 2 + 1 < p * p := by
    have h1 : n % p + 1 ≤ p := hmlt
    nlinarith
  have hne0 : (n % p) ^ 2 + 1 ≠ 0 := by omega
  unfold OMA.S_oeis_a247339.gpf
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ (n % p) ^ 2 + 1 := Nat.dvd_of_mem_primeFactors hq
    show q ≤ p
    by_contra hcon
    have hne : p ≠ q := by omega
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr hne
    have hmul : p * q ∣ (n % p) ^ 2 + 1 := hcop.mul_dvd_of_dvd_of_dvd hdvd hqd
    have hle := Nat.le_of_dvd (by omega) hmul
    have : p * p < p * q := by
      apply Nat.mul_lt_mul_of_pos_left <;> omega
    omega
  · have hmem : p ∈ ((n % p) ^ 2 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdvd, hne0⟩
    exact Finset.le_sup (f := id) hmem
