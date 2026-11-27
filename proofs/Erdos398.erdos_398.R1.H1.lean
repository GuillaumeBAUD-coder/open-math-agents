import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib

-- Step Erdos398.erdos_398.R1.H1: hypothesis H1 of reduction Erdos398.erdos_398.R1
-- Credit: @ivillar (original proof).
-- Strategy. Write n! = 4c (n >= 4). If 4c + 1 = m^2 then m is odd, m = 2r + 1 and c = r(r + 1);
-- conversely c = x(x + 1) gives 4c + 1 = (2x + 1)^2.

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 := by
  intro n hn
  have h4 : 4 ∣ n.factorial := by
    have : (4 : ℕ).factorial ∣ n.factorial := Nat.factorial_dvd_factorial hn
    exact dvd_trans (by decide) this
  obtain ⟨c, hc⟩ := h4
  rw [hc, Nat.mul_div_cancel_left c (by norm_num)]
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      subst hr
      have h2 : (4 * c + 1) % 2 = ((r + r) ^ 2) % 2 := by rw [hm]
      rw [show (r + r) ^ 2 = 2 * (2 * r * r) by ring] at h2
      omega
    · subst hr
      refine ⟨r, ?_⟩
      have h3 : 4 * c = 4 * (r * (r + 1)) := by
        have : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
        omega
      omega
  · rintro ⟨x, hx⟩
    exact ⟨2 * x + 1, by rw [← hx]; ring⟩
