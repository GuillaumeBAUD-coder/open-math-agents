import OMAReductions.R_Erdos386_erdos_386_variants_two_R1
import Mathlib

/-! If 8P + 1 = m^2 then m = 2t + 1 is odd, 2P = t (t + 1), so P = C(t + 1, 2), and P >= 6 forces t >= 3. -/

theorem OMA.solution : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := by
  intro P hP hsq
  obtain ⟨m, hm⟩ := hsq
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' m
  · exfalso
    have he : Even (2 * t * (2 * t)) := ⟨2 * t * t, by ring⟩
    rw [← hm] at he
    obtain ⟨r, hr⟩ := he
    omega
  · have h2 : 2 * P = t * (t + 1) := by nlinarith
    refine ⟨t + 1, ?_, ?_, ?_⟩
    · by_contra h
      have ht : t ≤ 2 := by omega
      interval_cases t <;> omega
    · rw [Nat.choose_two_right, Nat.add_sub_cancel]
      exact Nat.div_eq_of_eq_mul_left (by norm_num) (by nlinarith [h2])
    · nlinarith [h2]
