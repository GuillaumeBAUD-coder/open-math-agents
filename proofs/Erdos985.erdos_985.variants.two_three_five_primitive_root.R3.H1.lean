import OMAReductions.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R3

/-!
Proof of `OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R3.H1`:
the primes `2`, `3`, `5` each have `2`, `3` or `5` as a primitive root.

* modulo `2`: `3 = 1`, of order `1 = 2 - 1`;
* modulo `3`: `2 ≠ 1` and `2 ^ 2 = 1`, so `2` has order `2 = 3 - 1`;
* modulo `5`: `2 ^ 2 ≠ 1` and `2 ^ 4 = 1`, so `2` has order `4 = 5 - 1`.
-/

theorem OMA.solution :
    OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R3.H1 := by
  refine ⟨Nat.prime_two, Or.inr (Or.inl ?_), Nat.prime_three, Or.inl ?_, Nat.prime_five,
    Or.inl ?_⟩
  · have h : (3 : ZMod 2) = 1 := by decide
    rw [h, orderOf_one]
  · show orderOf (2 : ZMod 3) = 2
    have h1 : (2 : ZMod 3) ^ 2 = 1 := by decide
    have h2 : (2 : ZMod 3) ≠ 1 := by decide
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime h1 h2
  · show orderOf (2 : ZMod 5) = 2 ^ (1 + 1)
    have h1 : ¬ (2 : ZMod 5) ^ 2 ^ 1 = 1 := by decide
    have h2 : (2 : ZMod 5) ^ 2 ^ (1 + 1) = 1 := by decide
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow h1 h2
