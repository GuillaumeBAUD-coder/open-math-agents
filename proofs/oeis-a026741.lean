import OMAStatements.S_oeis_a026741
import Mathlib

open OMA.S_oeis_a026741 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026741.main := by
  intro p n hp hn
  unfold a
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    simp [hp.pos, (Nat.pos_of_mul_pos_left hn).ne']
  · have hc : n.Coprime p := (hp.coprime_iff_not_dvd.2 (h ∘ Nat.mod_eq_zero_of_dvd)).symm
    simp [hc.lcm_eq_mul, hc.gcd_eq_one, Nat.div_self hn, mul_comm]
