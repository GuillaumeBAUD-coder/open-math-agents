import OMAStatements.S_oeis_a114965
import Mathlib

-- Reduction oeis-a114965.R1 of A114965: a(n) = n^2 + 34.
-- Credit: @dries
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! The classical (Lebesgue, Nagell, Cohn) attack on the Lebesgue-Nagell equation
`n ^ 2 + 34 = x ^ k`, split into its three independent ingredients.

* Even `k` is impossible modulo 4 (`n ^ 2 + 34` is `2` or `3` mod 4), and an odd `k > 1`
  can be replaced by its least prime factor `p`; this is done in `main` below.
* H1, the algebraic descent. The ring of integers of `ℚ(√-34)` is `ℤ[√-34]`, its units are
  `±1` and its class number is `4`, prime to every odd `p`. For a solution, `n` is odd and
  prime to `17`, so the ideals `(n + √-34)` and `(n - √-34)` are coprime; their product is
  `(x) ^ p`, hence `(n + √-34) = I ^ p` with `I` principal, so `n + √-34 = z ^ p` (the sign
  is absorbed since `p` is odd).
* Writing `z = a + b √-34`, the coefficient of `√-34` in `z ^ p` is
  `b * Σ_j C(p, 2j+1) a ^ (p-1-2j) (-34) ^ j`, so `b = ±1` and one is left with a binomial
  Thue equation in `a`. H2, small exponents `p < 30`: for each such prime a single congruence
  (modulo 8, 9 or 12) rules it out, an elementary finite check. H3, large exponents `p > 30`:
  `(α ^ p - β ^ p) / (α - β) = ±1` for the Lucas pair `α, β = a ± √-34` (with `a` odd and prime
  to `17`, otherwise the coefficient is even or divisible by `17`) would be a Lucas number
  without a primitive divisor, impossible for `p > 30` by Bilu, Hanrot and Voutier (2001).
  No finite set of congruences can do H3: for `p ≡ 1` modulo the exponent of
  `(ℤ/m)[√-34]ˣ`, `z ^ p ≡ z`. -/

namespace OMA.R_oeis_a114965_R1

/-- Descent in `ℤ[√-34]` (class number 4, prime to every odd prime `p`):
a solution of `n ^ 2 + 34 = x ^ p` makes `n + √-34` a `p`-th power. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 2 < p → ∀ n x : ℕ, n ^ 2 + 34 = x ^ p →
  ∃ z : ℤ√(-34), z ^ p = ⟨n, 1⟩

/-- Small odd prime exponents: no `p`-th power in `ℤ[√-34]` has `√-34`-coefficient `1`. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 2 < p → p < 30 → ∀ z : ℤ√(-34), (z ^ p).im ≠ 1

/-- Large prime exponents (primitive divisors of Lucas numbers, Bilu-Hanrot-Voutier):
no `p`-th power in `ℤ[√-34]` has `√-34`-coefficient `1`. -/
def H3 : Prop := ∀ p : ℕ, p.Prime → 30 < p → ∀ z : ℤ√(-34), (z ^ p).im ≠ 1

/-- Squares are `0` or `1` mod 4, `n ^ 2 + 34` is `2` or `3` mod 4. -/
lemma sq_add_34_ne_sq (n y : ℕ) : n ^ 2 + 34 ≠ y ^ 2 := by
  intro h
  have h4 : ((n ^ 2 + 34 : ℕ) : ZMod 4) = ((y ^ 2 : ℕ) : ZMod 4) := by rw [h]
  push_cast at h4
  generalize (n : ZMod 4) = u at h4
  generalize (y : ZMod 4) = v at h4
  revert u v
  decide

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a114965.main := by
  intro h1 h2 h3 n x k hk hx
  simp only [OMA.S_oeis_a114965.a] at hx
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
  · exact sq_add_34_ne_sq n (x ^ m) (by rw [hx]; ring)
  · have hp : k.minFac.Prime := Nat.minFac_prime (by omega)
    have hp2 : 2 < k.minFac := by
      rcases hp.two_le.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2k : 2 ∣ k := h ▸ Nat.minFac_dvd k
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2k)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd k
    have hx' : n ^ 2 + 34 = (x ^ m) ^ k.minFac := by
      rw [hx, ← pow_mul, mul_comm, ← hm]
    obtain ⟨z, hz⟩ := h1 _ hp hp2 n (x ^ m) hx'
    have him : (z ^ k.minFac).im = 1 := by rw [hz]
    rcases lt_trichotomy k.minFac 30 with h | h | h
    · exact h2 _ hp hp2 h z him
    · rw [h] at hp; norm_num at hp
    · exact h3 _ hp h z him

end OMA.R_oeis_a114965_R1
