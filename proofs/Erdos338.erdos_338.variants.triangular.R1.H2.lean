import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1
import Mathlib

-- Step Erdos338.erdos_338.variants.triangular.R1.H2: hypothesis H2 of reduction Erdos338.erdos_338.variants.triangular.R1
-- Credit: @ivillar
--
-- If m = T_a + T_b with T_a = a(a+1)/2, then 8m + 2 = (2a+1)^2 + (2b+1)^2. Squares modulo 9 lie in
-- {0, 1, 4, 7}, so a sum of two of them is never 6 modulo 9. Hence no m = 9N + 5 is a sum of at
-- most two triangular numbers (T_0 = 0 covers fewer summands).

namespace OMA.Erdos338TriH2

lemma two_mul_tri (a : ℕ) : 2 * (a * (a + 1) / 2) = a * (a + 1) := by
  have : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
  omega

lemma no_two (N a b : ℕ) : a * (a + 1) / 2 + b * (b + 1) / 2 ≠ 9 * N + 5 := by
  intro h
  have ha := two_mul_tri a
  have hb := two_mul_tri b
  have key : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 = 72 * N + 42 := by
    have : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 = 4 * (a * (a + 1)) + 4 * (b * (b + 1)) + 2 := by
      ring
    omega
  have hz : ((2 * a + 1 : ℕ) : ZMod 9) ^ 2 + ((2 * b + 1 : ℕ) : ZMod 9) ^ 2 = 6 := by
    have := congrArg (fun x : ℕ => (x : ZMod 9)) key
    push_cast at this ⊢
    rw [this]
    have h72 : (72 : ZMod 9) = 0 := by decide
    rw [h72, zero_mul, zero_add]
    decide
  push_cast at hz
  generalize (a : ZMod 9) = u at hz
  generalize (b : ZMod 9) = v at hz
  revert u v
  decide

end OMA.Erdos338TriH2

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 := by
  unfold OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 Erdos338.HasOrder
  rw [Filter.eventually_atTop]
  rintro ⟨M, hM⟩
  obtain ⟨S, hS, hcard, hsum⟩ := hM (9 * M + 5) (by omega)
  have mem : ∀ x ∈ S, ∃ a, x = a * (a + 1) / 2 := by
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨a, ha.symm⟩
  rcases Nat.lt_or_ge (Multiset.card S) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Multiset.card S) 1 with h0 | h1
    · rw [Multiset.card_eq_zero.mp (show Multiset.card S = 0 by omega)] at hsum
      simp at hsum
    · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp (show Multiset.card S = 1 by omega)
      obtain ⟨a, rfl⟩ := mem x (by simp)
      apply OMA.Erdos338TriH2.no_two M a 0
      simpa using hsum
  · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp (show Multiset.card S = 2 by omega)
    obtain ⟨a, rfl⟩ := mem x (by simp)
    obtain ⟨b, rfl⟩ := mem y (by simp)
    apply OMA.Erdos338TriH2.no_two M a b
    simpa using hsum
