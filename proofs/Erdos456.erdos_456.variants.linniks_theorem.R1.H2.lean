import OMAReductions.R_Erdos456_erdos_456_variants_linniks_theorem_R1
import Mathlib

-- Step Erdos456.erdos_456.variants.linniks_theorem.R1.H2: hypothesis H2 of reduction Erdos456.erdos_456.variants.linniks_theorem.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics

/-! For n ≥ 1 the given prime is congruent to 1 modulo n, so it bounds the least such prime p n. -/

theorem OMA.solution : OMA.R_Erdos456_erdos_456_variants_linniks_theorem_R1.H2 := by
  intro C L h
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨ℓ, hℓ, hdvd, hle⟩ := h n hn
  have hmod : ℓ ≡ 1 [MOD n] := ((Nat.modEq_iff_dvd' hℓ.one_lt.le).mpr hdvd).symm
  have hp : Erdos456.p n ≤ ℓ := Nat.sInf_le ⟨hℓ, hmod⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity), Real.rpow_natCast]
  exact (Nat.cast_le.mpr hp).trans hle
