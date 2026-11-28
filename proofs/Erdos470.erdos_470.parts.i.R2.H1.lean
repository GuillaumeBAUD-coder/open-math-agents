import OMAReductions.R_Erdos470_erdos_470_parts_i_R2

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_i_R2.H1 := by
  intro m t E hm ht hmt hE hs hp hgap
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hmt
  simp only [ArithmeticFunction.sigma_one_apply] at h
  rw [hs, Nat.mul_assoc, Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
  refine ⟨⟨?_, ?_⟩, hm.mul ht⟩
  · show m * t < ∑ d ∈ (m * t).properDivisors, d
    omega
  · rintro ⟨_, s, hsub, hss⟩
    have := Finset.sum_sdiff (f := fun d : ℕ => d) hsub
    have hc : ∑ d ∈ (m * t).properDivisors \ s, d = E := by omega
    apply hgap _ _ hc
    intro d hd
    have hdvd := (Nat.mem_properDivisors.1 (Finset.mem_sdiff.1 hd).1).1
    refine Nat.mem_divisors.2 ⟨?_, hm.pos.ne'⟩
    suffices co : Nat.Coprime d t from co.dvd_of_dvd_mul_right hdvd
    apply Nat.coprime_of_dvd
    intro p hpp hpd hpt
    have := hp p (Nat.mem_primeFactors.2 ⟨hpp, hpt, ht.pos.ne'⟩)
    have := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hdvd (Nat.mul_pos hm.pos ht.pos)) hpd
    have := Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _) hd
    omega
