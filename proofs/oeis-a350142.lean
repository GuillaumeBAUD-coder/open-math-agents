import OMAStatements.S_oeis_a350142
import Mathlib

/-
A350142: with m = 2^k + 1, tau(m - 2) = tau(m - 1) - 1 holds exactly when tau(m - 2) = k.

m - 1 = 2^k has k + 1 divisors, so tau(m - 1) - 1 = k and the two conditions are the same.
-/

namespace OMA.P350142

lemma main' (tau : ℕ → ℕ) (ht : ∀ n, tau n = n.divisors.card) :
    ∀ k : ℕ,
      let m := 2 ^ k + 1
      tau (m - 2) = tau (m - 1) - 1 ↔ tau (m - 2) = k := by
  intro k
  show tau (2 ^ k + 1 - 2) = tau (2 ^ k + 1 - 1) - 1 ↔ tau (2 ^ k + 1 - 2) = k
  have h : tau (2 ^ k + 1 - 1) = k + 1 := by
    rw [ht, Nat.add_sub_cancel, Nat.divisors_prime_pow Nat.prime_two]
    simp
  rw [h, Nat.add_sub_cancel]

end OMA.P350142

theorem OMA.solution : type_of% @OMA.S_oeis_a350142.main := OMA.P350142.main' OMA.S_oeis_a350142.tau (fun _ => rfl)
