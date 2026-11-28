import OMAStatements.S_oeis_a026741
import Mathlib

open OMA.S_oeis_a026741 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026741.main := by
  intro p n hp hn
  unfold a
  by_cases h : n % p = 0
  · rw [if_pos h]
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    have hp0 : 0 < p := hp.pos
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_div_cancel_left m hp0]
      exact Nat.lcm_eq_left (Dvd.intro m rfl) |>.trans rfl
    · rw [Nat.mul_div_cancel_left m hp0, Nat.mul_div_cancel _ hm]
      exact Nat.gcd_eq_right (Dvd.intro m rfl)
  · rw [if_neg h]
    have hnd : ¬ p ∣ n := fun hd => h (Nat.mod_eq_zero_of_dvd hd)
    have hc : Nat.Coprime n p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    refine ⟨?_, ?_⟩
    · rw [hc.lcm_eq_mul, Nat.mul_comm]
    · rw [hc.gcd_eq_one, Nat.div_self hn]
