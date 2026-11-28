import OMAReductions.R_Erdos677_erdos_677_R1

/-! For k = 1 the lcm of the interval (t, t+1] is t + 1. For k = 2 it is lcm(t+1, t+2) =
(t+1)(t+2), since consecutive integers are coprime. Both are strictly increasing in t, so
m ≥ n + k gives different values. -/

theorem OMA.solution : OMA.R_Erdos677_erdos_677_R1.H1 := by
  intro m n k hk hk2 hmn
  interval_cases k
  · have e : ∀ t : ℕ, Finset.lcmInterval t 1 = t + 1 := by
      intro t
      have hI : Finset.Ioc t (t + 1) = {t + 1} := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      rw [Finset.lcmInterval, hI, Finset.lcm_singleton]
      simp
    rw [e, e]
    omega
  · have e : ∀ t : ℕ, Finset.lcmInterval t 2 = (t + 1) * (t + 2) := by
      intro t
      have hI : Finset.Ioc t (t + 2) = {t + 1, t + 2} := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hc : Nat.Coprime (t + 1) (t + 2) := by
        show Nat.Coprime (t + 1) (t + 1 + 1)
        exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
      rw [Finset.lcmInterval, hI, Finset.lcm_insert, Finset.lcm_singleton]
      simp only [id_eq, normalize_eq]
      exact hc.lcm_eq_mul
    rw [e, e]
    intro h
    have : (n + 1) * (n + 2) < (m + 1) * (m + 2) := by nlinarith
    omega
