import OMAStatements.S_oeis_a109874

-- Problem: A109874: Largest exponent e such that n^e that divides A001142(n).
-- Upstream: formal-conjectures statements/oeis-a109874.lean:0 (declaration OMA.S_oeis_a109874.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 15 is odd and composite, so conjecture (3) would give a(15) = 13 and hence
-- 15^13 would divide A001142(15) = 8950867799438312225700843177441650390625. It does not:
-- 5 divides binomial(15, k) exactly once for the 12 values 0 < k < 15 with k not divisible
-- by 5 and not at all otherwise, so the 5-adic valuation of the product is 12 and a(15) = 12.
-- (The listed data also refute (1) at n = 14 and (2) at n = 16.)

open OMA.S_oeis_a109874 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a109874.main) := by
  intro H
  have hgen : ∀ n : ℕ, n ^ a n ∣ P n := fun n =>
    Nat.findGreatest_spec (P := fun e => n ^ e ∣ P n) (Nat.zero_le _) (by simp)
  have h15 : P 15 = 8950867799438312225700843177441650390625 := by decide
  have ha : ((a 15 : ℕ) : ℤ) = ((15 : ℕ) : ℤ) - 2 :=
    H.2.2 15 (by norm_num) ⟨7, by norm_num⟩ (by norm_num)
  have ha13 : ((a 15 : ℕ) : ℤ) = ((13 : ℕ) : ℤ) := ha.trans (by norm_num)
  have ha' : a 15 = 13 := Nat.cast_injective ha13
  have hspec := hgen 15
  rw [ha', h15, Nat.dvd_iff_mod_eq_zero] at hspec
  norm_num at hspec
