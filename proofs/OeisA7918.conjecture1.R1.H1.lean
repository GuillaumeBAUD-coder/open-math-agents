import OMAReductions.R_OeisA7918_conjecture1_R1

-- Step OeisA7918.conjecture1.R1.H1: hypothesis H1 of reduction OeisA7918.conjecture1.R1
-- Credit: @JamesSlash. If p0 < n then the term p0 + p0 * d = p0 * (1 + d) of the progression is
-- composite, so p0 is a prime with n <= p0 and a n = sInf {p prime, n <= p} <= p0.

theorem OMA.solution : OMA.R_OeisA7918_conjecture1_R1.H1 := by
  intro n p0 d hn hap
  obtain ⟨hd, hp⟩ := hap
  have h0 : p0.Prime := by simpa using hp 0 hn
  have hge : n ≤ p0 := by
    by_contra h
    rw [not_le] at h
    have hk := hp p0 h
    have hfac : p0 + p0 * d = p0 * (1 + d) := by ring
    rw [hfac] at hk
    have h2 := h0.two_le
    rcases Nat.prime_mul_iff.mp hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  exact Nat.sInf_le ⟨h0, hge⟩
