import OMAReductions.R_Erdos430_erdos_430_R1

/-!
# Proof of `Erdos430.erdos_430.R1.H2`

Proves that whenever `p ≤ q` are primes with `p * q < n < p * q + p`, the semiprime `p * q`
belongs to `Erdos430.terms n`.

Indeed `1 < p * q < n` since `2 ≤ p ≤ q`, and every prime factor `r` of `p * q` equals either
`p` or `q`, hence satisfies `n - p * q < p ≤ r`.
-/

theorem OMA.solution : OMA.R_Erdos430_erdos_430_R1.H2 := by
  intro n p q hp hq hpq hlt1 hlt2
  unfold Erdos430.terms
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨?_, hlt1⟩, ?_⟩
  · have hp2 : 2 ≤ p := hp.two_le
    have hq2 : 2 ≤ q := hq.two_le
    nlinarith
  · intro r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_dvd : r ∣ p * q := Nat.dvd_of_mem_primeFactors hr
    rcases hr_prime.dvd_mul.mp hr_dvd with hrp | hrq
    · have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr_prime hp).mp hrp
      omega
    · have heq : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime hq).mp hrq
      omega
