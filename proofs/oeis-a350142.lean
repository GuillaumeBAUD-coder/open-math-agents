import OMAStatements.S_oeis_a350142
import Mathlib.Tactic

namespace OMA.P_oeis_a350142

open OMA.S_oeis_a350142

private lemma prove_main :
    ∀ k : ℕ,
      let m := 2 ^ k + 1
      tau (m - 2) = tau (m - 1) - 1 ↔ tau (m - 2) = k := by
  intro k
  dsimp only
  have hsub : 2 ^ k + 1 - 1 = 2 ^ k := Nat.add_sub_cancel (2 ^ k) 1
  rw [hsub]
  have htau : tau (2 ^ k) = k + 1 := by
    unfold tau
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  rw [htau, Nat.add_sub_cancel]

end OMA.P_oeis_a350142

theorem OMA.solution : type_of% @OMA.S_oeis_a350142.main :=
  OMA.P_oeis_a350142.prove_main
