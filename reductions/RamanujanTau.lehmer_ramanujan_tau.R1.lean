import FormalConjectures.Wikipedia.RamanujanTau

-- Reduction RamanujanTau.lehmer_ramanujan_tau.R1 of Lehmer's conjecture on the Ramanujan τ-function
-- Credit: @MBimrose (agent: hub-swarm-pi)

/-!
# Lehmer's conjecture: the prime-power and multiplicativity inputs

Lehmer's conjecture (`τ n ≠ 0` for every `n > 0`, where `Δ = X ∏ (1 - X ^ n) ^ 24 = ∑ τ n X ^ n`)
is open.  What is *not* open about it is the passage from primes to all naturals: `τ` is the
eigenform-normalised coefficient function of the modular form `Δ`, hence

* `τ (m * n) = τ m * τ n` for coprime `m, n` (multiplicativity of the coefficients of a
  normalised eigenform; equivalently, `Δ` is an eigenform for all Hecke operators `T_m` with
  eigenvalue `τ m`, and Hecke operators attached to coprime indices commute), and
* `τ (p ^ (k + 1)) = τ p * τ (p ^ k) - p ^ 11 * τ (p ^ (k - 1))`, the Hecke recursion at the
  prime `p` (from `T_{p ^ (k+1)} = T_p T_{p ^ k} - p ^ 11 T_{p ^ (k-1)}`).

Given multiplicativity alone, `τ n = ∏_{p ^ k ‖ n} τ (p ^ k)`, so `τ` is nowhere zero as soon as it
is nowhere zero on prime powers.  This is exactly what `main` below carries out: it is the standard
reduction of Lehmer's conjecture to two independent, still-open statements, and it is *not* a proof of
the conjecture.

* `H1` (open): `τ` does not vanish at any prime power `p ^ k`, `k ≥ 1`.  This is the genuine
  arithmetic content: via the Hecke recursion `τ (p ^ k) = (α ^ (k+1) - β ^ (k+1)) / (α - β)` with
  `α + β = τ p`, `α β = p ^ 11`, the non-vanishing of all `τ (p ^ k)` follows from Deligne's bound
  `|τ p| ≤ 2 p ^ (11/2)` (so that `α, β` are complex conjugates of modulus `p ^ (11/2)` and the
  quotient `α / β` is not a root of unity) together with integrality of `τ`.  In particular `H1`
  contains Lehmer's original condition `τ p ≠ 0` for every prime `p`.
* `H2` (the classical multiplicativity of `τ` on coprime arguments).

`main` performs the induction: for `n ≥ 2`, split off the full power of a prime divisor `p` of `n`,
that is `n = p ^ k * m` with `p ∤ m` (`Nat.factorization`, `Nat.ordProj` / `Nat.ordCompl`), so that
`m < n` and `p ^ k` is coprime to `m`.  Multiplicativity (`H2`) gives `τ n = τ (p ^ k) * τ m`, both
factors are non-zero — `H1` and the induction hypothesis — hence `τ n ≠ 0`.
-/

namespace OMA.R_RamanujanTau_lehmer_ramanujan_tau_R1

open RamanujanTau (τ)

/-- `τ` is nowhere zero on prime powers: `τ (p ^ k) ≠ 0` for every prime `p` and every `k ≥ 1`.
Still open (`k = 1` is Lehmer's condition `τ p ≠ 0`; the case `k ≥ 2` follows from the Hecke
recursion plus Deligne's bound `|τ p| ≤ 2 p ^ (11/2)`). -/
def H1 : Prop := ∀ p k : ℕ, p.Prime → 1 ≤ k → τ (p ^ k) ≠ 0

/-- `τ` is multiplicative on coprime arguments: `τ (m * n) = τ m * τ n` when `m` and `n` are
coprime. This is the classical Hecke-eigenform multiplicativity of the coefficients of `Δ`. -/
def H2 : Prop := ∀ m n : ℕ, m.Coprime n → τ (m * n) = τ m * τ n

theorem main : H1 → H2 → type_of% @RamanujanTau.lehmer_ramanujan_tau := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro hn
  rcases n with _ | _ | k
  · omega
  · rw [RamanujanTau.τ_one]
    exact one_ne_zero
  · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : k + 2 ≠ 1)
    have hn0 : k + 2 ≠ 0 := by omega
    set e : ℕ := (k + 2).factorization p with he
    set m : ℕ := (k + 2) / p ^ e with hmm
    have hsplit : p ^ e * m = k + 2 := by
      rw [hmm, he]
      exact Nat.ordProj_mul_ordCompl_eq_self (k + 2) p
    have he1 : 1 ≤ e := by
      rw [he]
      exact (hp.dvd_iff_one_le_factorization hn0).mp hpdvd
    have hcop : Nat.Coprime (p ^ e) m := by
      rw [hmm]
      exact ((Nat.coprime_pow_left_iff (show 0 < e by omega) p m).mpr (Nat.coprime_ordCompl hp hn0))
    have hmpos : 0 < m := by
      rw [hmm]
      exact Nat.ordCompl_pos p hn0
    have hple : p ≤ p ^ e := by
      simpa using Nat.pow_le_pow_right hp.pos he1
    have hp2 : 2 ≤ p := hp.two_le
    have hmlt : m < k + 2 := by
      have h2 : 2 * m ≤ k + 2 := by
        rw [← hsplit]
        exact Nat.mul_le_mul_right _ (le_trans hp2 hple)
      omega
    have hpow : τ (p ^ e) ≠ 0 := h1 p e hp he1
    have hm : τ m ≠ 0 := ih m hmlt hmpos
    have heq : τ (k + 2) = τ (p ^ e) * τ m := by
      rw [← hsplit]
      exact h2 _ _ hcop
    rw [heq]
    exact mul_ne_zero hpow hm

end OMA.R_RamanujanTau_lehmer_ramanujan_tau_R1
