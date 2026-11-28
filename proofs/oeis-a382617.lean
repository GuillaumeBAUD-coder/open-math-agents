import OMAStatements.S_oeis_a382617
import Mathlib

open OMA.S_oeis_a382617

private theorem prime_dvd_solution {p k : ℕ} (hp : p.Prime)
    (hk : isSolution p k) : p ∣ k := by
  by_contra h
  have hp2 : p ∣ p^2 := dvd_pow_self p (by decide)
  have hnot : ¬ p ∣ p^2+k^2 := fun hsum =>
    h (hp.dvd_of_dvd_pow ((Nat.dvd_add_iff_right hp2).mpr hsum))
  have hco : (p^2+k^2).Coprime (p^2) := (hp.coprime_iff_not_dvd.mpr hnot).symm.pow_right _
  have hdiv : p^2+k^2 ∣ k^2 := hco.dvd_of_dvd_mul_left hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero (fun he => h (he ▸ dvd_zero p))
  have hle := Nat.le_of_dvd (pow_pos hkpos 2) hdiv
  have hpos : 0 < p^2 := pow_pos hp.pos 2
  omega

private theorem solution_multiple {p t : ℕ} (hp : 0 < p) :
    isSolution p (p*t) ↔ 1+t^2 ∣ p^2 := by
  unfold isSolution
  rw [show p^2+(p*t)^2 = p^2*(1+t^2) by ring,
    show p^2*(p*t)^2 = p^2*(p^2*t^2) by ring,
    Nat.mul_dvd_mul_iff_left (pow_pos hp 2)]
  constructor
  · intro hd
    have htotal : 1+t^2 ∣ p^2+p^2*t^2 := by
      rw [show p^2+p^2*t^2 = p^2*(1+t^2) by ring]
      exact dvd_mul_left _ _
    exact (Nat.dvd_add_iff_left hd).mpr htotal
  · intro hd
    exact dvd_mul_of_dvd_left hd _

theorem OMA.solution : type_of% @OMA.S_oeis_a382617.main := by
  intro m p hpm hp
  have hm : 0 < m := by
    by_contra! h
    have hm0 : m = 0 := by omega
    have hp1 : p = 1 := by simp [hpm, hm0]
    exact Nat.not_prime_one (hp1 ▸ hp)
  refine ⟨Nat.mul_pos hm hp.pos, fun k => ?_⟩
  constructor
  · intro hk
    obtain ⟨t,rfl⟩ := prime_dvd_solution hp hk
    have ht := (solution_multiple hp.pos).mp hk
    obtain ⟨e,he,hev⟩ := (Nat.dvd_prime_pow hp).mp ht
    interval_cases e
    · left
      simp only [pow_zero] at hev
      have h0 : t = 0 := by
        have hsq : t^2 = 0 := by omega
        exact (Nat.pow_left_injective (by decide : 2 ≠ 0)) (by simpa using hsq)
      simp [h0]
    · right
      rw [pow_one, hpm] at hev
      have hsq : t^2 = m^2 := by omega
      have ht' : t = m := (Nat.pow_left_injective (by decide : 2 ≠ 0)) hsq
      simp [ht',mul_comm]
    · have hlt : t < p := by
        by_contra! hn
        have h := Nat.pow_le_pow_left hn 2
        omega
      have hle : (t+1)^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
      have ht0 : t ≠ 0 := by
        intro h
        have hp2 := hp.two_le
        simp [h] at hev
        nlinarith
      exfalso
      nlinarith
  · rintro (rfl | rfl)
    · simp [isSolution]
    · rw [mul_comm m p, solution_multiple hp.pos]
      rw [add_comm, ← hpm]
      exact dvd_pow_self _ (by decide)