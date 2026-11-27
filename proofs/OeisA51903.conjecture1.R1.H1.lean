import OMAReductions.R_OeisA51903_conjecture1_R1

/-! A totient dividing n−1 excludes every repeated prime factor. Credit: @Deldor14. -/

open OMA.R_OeisA51903_conjecture1_R1

theorem OMA.solution : OMA.R_OeisA51903_conjecture1_R1.H1 := by
  intro n hn hφ
  obtain ⟨p,k,hp,he,hpk⟩ := attains hn
  have h1 := Nat.dvd_one.mp (strip (by omega : 1 ≤ n) hp hpk hφ)
  cases k with
  | zero => exact he
  | succ k =>
    have hle := Nat.pow_le_pow_right (n := p) hp.pos (show 1 ≤ k+1 by omega)
    simp only [pow_one, h1] at hle
    exact False.elim (hp.one_lt.not_ge hle)
