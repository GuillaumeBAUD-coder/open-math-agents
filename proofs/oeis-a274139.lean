import OMAStatements.S_oeis_a274139
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a274139.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  have hb : OMA.S_oeis_a274139.b 2 = 2 := by decide +kernel
  have ha : OMA.S_oeis_a274139.a 2 = 2 := by
    simp [OMA.S_oeis_a274139.a, OMA.S_oeis_a274139.oddPart, Nat.factorization_def _ Nat.prime_two]
  rw [hb, ha] at h2
  norm_num at h2
