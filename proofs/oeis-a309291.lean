import OMAStatements.S_oeis_a309291
import Mathlib

/-
A309291: for k > 4 and a prime q with k! - k^2 <= q <= k! - k, the number k! - q is prime.

Put n = k! - q, so k <= n <= k^2 (note k! >= k^2 + k + 1 for k >= 5). If n were composite, its
least prime factor r satisfies r^2 <= n <= k^2, so r <= k and r divides k!, hence r divides
q = k! - n, so r = q. But q >= k! - k^2 > k >= r.
-/

namespace OMA.P309291

lemma main' :
    ∀ k : ℕ, 4 < k → ∀ q : ℕ, q.Prime →
      Nat.factorial k - k ^ 2 ≤ q → q ≤ Nat.factorial k - k → (Nat.factorial k - q).Prime := by
  intro k hk q hq h1 h2
  have hfac : k ^ 2 + k + 1 ≤ k.factorial := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h6 : 6 ≤ j.factorial := by
      calc 6 = Nat.factorial 3 := rfl
        _ ≤ j.factorial := Nat.factorial_le (by omega)
    rw [Nat.factorial_succ, Nat.factorial_succ]
    nlinarith [Nat.mul_le_mul_left ((j + 1 + 1) * (j + 1)) h6]
  obtain ⟨n, hn⟩ : ∃ n, n = k.factorial - q := ⟨_, rfl⟩
  rw [← hn]
  have hnk : k ≤ n := by omega
  have hnk2 : n ≤ k ^ 2 := by omega
  by_contra hnp
  have hr := Nat.minFac_prime (show n ≠ 1 by omega)
  have hrsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hrk : n.minFac ≤ k := by
    by_contra hgt
    have : k ^ 2 < n.minFac ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  have hd1 : n.minFac ∣ k.factorial := Nat.dvd_factorial hr.pos hrk
  have hd2 : n.minFac ∣ n := Nat.minFac_dvd n
  have hd3 : n.minFac ∣ q := by
    have : q = k.factorial - n := by omega
    rw [this]
    exact Nat.dvd_sub hd1 hd2
  have : n.minFac = q := (Nat.prime_dvd_prime_iff_eq hr hq).1 hd3
  omega

end OMA.P309291

theorem OMA.solution : type_of% @OMA.S_oeis_a309291.main := OMA.P309291.main'
