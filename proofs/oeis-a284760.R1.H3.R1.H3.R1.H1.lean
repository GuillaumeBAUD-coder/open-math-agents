import OMAReductions.R_oeis_a284760_R1_H3_R1_H3_R1

/-! A finite computation, decided by the kernel. Among the primes 5 ≤ p < 59 and the even
r < p(p - 1) with p ∣ r + 3 (181 pairs), the only one with p² ∣ ∑_{i=1}^{p-1} i^r is
(p, r) = (37, 1292), and 1292 ≡ 32 (mod 36). -/

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_oeis_a284760_R1_H3_R1_H3_R1.H1 := by
  unfold OMA.R_oeis_a284760_R1_H3_R1_H3_R1.H1
  decide +kernel
