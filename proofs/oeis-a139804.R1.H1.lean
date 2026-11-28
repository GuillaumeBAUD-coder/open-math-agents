import OMAReductions.R_oeis_a139804_R1
import Mathlib

/-! Prime factors of Fortunate-type offsets for `(3^n)!`.

If `N! + m` is prime, `m ≥ 1` and a prime `q ≤ N` divides `m`, then `q` divides `N!` and hence
`N! + m`, so `q = N! + m`; but `q ≤ m < N! + m`. So every prime factor of `m` exceeds `N`. When
`m > 1` is not prime, its least prime factor `q` satisfies `q^2 ≤ m` and `q ≥ N + 1`.
-/

namespace OMA.P_oeis_a139804_R1_H1

open OMA.S_oeis_a139804

theorem prime_factor_gt (N m q : ℕ) (hp : (N.factorial + m).Prime) (hq : q.Prime) (hqm : q ∣ m)
    (hm : 1 ≤ m) : N < q := by
  by_contra hle
  push Not at hle
  have h1 : q ∣ N.factorial := Nat.dvd_factorial hq.pos hle
  have h2 : q ∣ N.factorial + m := dvd_add h1 hqm
  rcases hp.eq_one_or_self_of_dvd q h2 with h | h
  · exact hq.one_lt.ne' h
  · have := Nat.le_of_dvd (by omega) hqm
    have := Nat.factorial_pos N
    omega

theorem valid_structure (n m : ℕ) (hv : IsValid n m) (h1 : m ≠ 1) :
    (∀ q : ℕ, q.Prime → q ∣ m → 3 ^ n < q) ∧ (m.Prime ∨ (3 ^ n + 1) ^ 2 ≤ m) := by
  obtain ⟨hm, hp⟩ := hv
  refine ⟨fun q hq hqm => prime_factor_gt (3 ^ n) m q hp hq hqm hm, ?_⟩
  by_cases h2 : m.Prime
  · exact Or.inl h2
  right
  have hq := Nat.minFac_prime h1
  have hlt := prime_factor_gt (3 ^ n) m _ hp hq (Nat.minFac_dvd m) hm
  have hsq := Nat.minFac_sq_le_self (by omega) h2
  calc (3 ^ n + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hlt 2
    _ ≤ m := hsq

end OMA.P_oeis_a139804_R1_H1

theorem OMA.solution : OMA.R_oeis_a139804_R1.H1 :=
  fun n m hv h1 => OMA.P_oeis_a139804_R1_H1.valid_structure n m hv h1
