import OMAReductions.R_oeis_a400795_R1
import Mathlib

-- Step oeis-a400795.R1.H3: hypothesis H3 of reduction oeis-a400795.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_oeis_a400795_R1.H3 := by
  intro n q hq hq2 hqn hdvd hcop
  obtain ⟨m, hm⟩ := hdvd
  have hqpos : 0 < q := by omega
  have hmq : (n + 1) / q = m := by rw [hm]; exact Nat.mul_div_cancel_left m hqpos
  rw [hmq]
  have hm2 : 2 ≤ m := by
    by_contra h
    interval_cases m <;> simp_all
  refine ⟨by omega, by omega, ?_⟩
  unfold OMA.S_oeis_a400795.triangleCount
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcop ⊢
  have hj : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [hj]
  have hn : 2 * n + 1 = i * (2 * j + 1) + i + (2 * j + 1) := by
    have : n + 1 = (i + 1) * (j + 1) := hm
    nlinarith
  have hg : Nat.gcd i (2 * j + 1) = 1 := by
    have h1 : Nat.gcd i (2 * j + 1) ∣ 2 * n + 1 := by
      rw [hn]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _)
        (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)
    have h2 := Nat.dvd_gcd (Nat.gcd_dvd_left i (2 * j + 1)) h1
    rw [hcop] at h2
    exact Nat.dvd_one.mp h2
  rw [hg, ← hn]
  omega
