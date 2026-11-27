import OMAReductions.R_Erdos398_erdos_398_R1

-- Step Erdos398.erdos_398.R1.H1: hypothesis H1 of reduction Erdos398.erdos_398.R1
-- Credit: @NoahPuckett-IO
-- For n ≥ 4 write n! = 4q. If n! + 1 = m^2 then m = 2t + 1 is odd and q = t (t + 1);
-- conversely q = x (x + 1) gives n! + 1 = (2x + 1)^2.

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 := by
  intro n hn
  obtain ⟨q, hq⟩ : 4 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have hdiv : n.factorial / 4 = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q (by norm_num)
  rw [hdiv]
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.even_or_odd' m with ⟨t, rfl | rfl⟩
    · exfalso
      have e : (2 * t) ^ 2 = 4 * (t * t) := by ring
      omega
    · refine ⟨t, ?_⟩
      have e : (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
      omega
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have e : (2 * x + 1) ^ 2 = 4 * (x * (x + 1)) + 1 := by ring
    omega
