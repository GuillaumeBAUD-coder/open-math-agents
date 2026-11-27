import OMAReductions.R_SteinerSystems_infinitely_many_steiner_t5_R1

/-! The divisibility conditions for S(5, 6, n) hold for every n = 720 N + 6: the falling
factorials of 720 N + 6, 720 N + 5, 720 N + 4 and 720 N + 3 factor explicitly, giving
C(n, 5) = 6 (120N+1)(144N+1)(180N+1)(240N+1)(360N+1),
C(n-1, 4) = 5 (144N+1)(180N+1)(240N+1)(360N+1), C(n-2, 3) = 4 (180N+1)(240N+1)(360N+1),
C(n-3, 2) = 3 (240N+1)(360N+1) and n - 4 = 2 (360N+1). -/

namespace OMASteiner5

lemma dvd5 (N : ℕ) : 6 ∣ Nat.choose (720 * N + 6) 5 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 6) 5
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 720 * N + 6 - 1 = 720 * N + 5 := by omega
  have e2 : 720 * N + 6 - 2 = 720 * N + 4 := by omega
  have e3 : 720 * N + 6 - 3 = 720 * N + 3 := by omega
  have e4 : 720 * N + 6 - 4 = 720 * N + 2 := by omega
  rw [e1, e2, e3, e4, Nat.sub_zero, show Nat.factorial 5 = 120 from rfl] at h
  refine ⟨(120 * N + 1) * (144 * N + 1) * (180 * N + 1) * (240 * N + 1) * (360 * N + 1),
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 120) ?_⟩
  rw [← h]
  ring

lemma dvd4 (N : ℕ) : 5 ∣ Nat.choose (720 * N + 5) 4 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 5) 4
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 720 * N + 5 - 1 = 720 * N + 4 := by omega
  have e2 : 720 * N + 5 - 2 = 720 * N + 3 := by omega
  have e3 : 720 * N + 5 - 3 = 720 * N + 2 := by omega
  rw [e1, e2, e3, Nat.sub_zero, show Nat.factorial 4 = 24 from rfl] at h
  refine ⟨(144 * N + 1) * (180 * N + 1) * (240 * N + 1) * (360 * N + 1),
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 24) ?_⟩
  rw [← h]
  ring

lemma dvd3 (N : ℕ) : 4 ∣ Nat.choose (720 * N + 4) 3 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 4) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 720 * N + 4 - 1 = 720 * N + 3 := by omega
  have e2 : 720 * N + 4 - 2 = 720 * N + 2 := by omega
  rw [e1, e2, Nat.sub_zero, show Nat.factorial 3 = 6 from rfl] at h
  refine ⟨(180 * N + 1) * (240 * N + 1) * (360 * N + 1),
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 6) ?_⟩
  rw [← h]
  ring

lemma dvd2 (N : ℕ) : 3 ∣ Nat.choose (720 * N + 3) 2 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 3) 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 720 * N + 3 - 1 = 720 * N + 2 := by omega
  rw [e1, Nat.sub_zero, show Nat.factorial 2 = 2 from rfl] at h
  refine ⟨(240 * N + 1) * (360 * N + 1), Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_⟩
  rw [← h]
  ring

end OMASteiner5

theorem OMA.solution : OMA.R_SteinerSystems_infinitely_many_steiner_t5_R1.H2 := by
  intro N
  refine ⟨720 * N + 6, by omega, ?_⟩
  intro i hi
  interval_cases i
  · show Nat.choose 6 5 ∣ Nat.choose (720 * N + 6) 5
    rw [show Nat.choose 6 5 = 6 from by decide]
    exact OMASteiner5.dvd5 N
  · show Nat.choose 5 4 ∣ Nat.choose (720 * N + 5) 4
    rw [show Nat.choose 5 4 = 5 from by decide]
    exact OMASteiner5.dvd4 N
  · show Nat.choose 4 3 ∣ Nat.choose (720 * N + 4) 3
    rw [show Nat.choose 4 3 = 4 from by decide]
    exact OMASteiner5.dvd3 N
  · show Nat.choose 3 2 ∣ Nat.choose (720 * N + 3) 2
    rw [show Nat.choose 3 2 = 3 from by decide]
    exact OMASteiner5.dvd2 N
  · show Nat.choose 2 1 ∣ Nat.choose (720 * N + 2) 1
    rw [show Nat.choose 2 1 = 2 from by decide, Nat.choose_one_right]
    exact ⟨360 * N + 1, by ring⟩
