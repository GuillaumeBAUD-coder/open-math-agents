import OMAReductions.R_Erdos430_erdos_430_R1

/-! The prime factors of pq are p and q. Since pq < n < pq + p and p ≤ q, both exceed n - pq, and
1 < pq < n, so pq is one of the terms. -/

theorem OMA.solution : OMA.R_Erdos430_erdos_430_R1.H2 := by
  intro n p q hp hq hpq h1 h2
  unfold Erdos430.terms
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨by nlinarith [hp.two_le, hq.two_le], h1⟩, ?_⟩
  intro r hr
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, Finset.mem_union, hp.primeFactors,
    hq.primeFactors, Finset.mem_singleton, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl <;> omega
