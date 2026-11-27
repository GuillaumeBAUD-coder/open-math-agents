import FormalConjectures.OEIS.«189286»

-- Reduction OeisA189286.conjecture_3.R1 of Normalized convolution of $\binom{6k}{3k}\binom{3k}{k}$ — conjecture 3
-- Upstream: formal-conjectures FormalConjectures/OEIS/189286.lean (declaration OeisA189286.conjecture_3)
-- Credit: @ihateSAS
--
-- Target: for `n > 0` there is `m : ℤ` with `a n = 8 * m`, and that `m` is odd exactly when `n`
-- is a power of two.
--
-- The two halves of the conjecture are different arguments about the same convolution, so they are
-- split off separately, and the `↔` is split into its two directions:
--   H1  the 8-adic divisibility of `a n` (an arithmetic statement about the binomial convolution),
--   H2  `n = 2 ^ k` forces every witness of divisibility by 8 to be odd,
--   H3  an odd witness of divisibility by 8 forces `n = 2 ^ k`.
-- H2 and H3 are stated for an arbitrary witness `m` rather than through a quotient `a n / 8`, so
-- neither of them presupposes the existence of `m` proved by H1.

namespace OMA.R_OeisA189286_conjecture_3_R1

open OeisA189286

/-- The divisibility half: `a n` is divisible by `8` in `ℤ` for every positive `n`. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → ∃ m : ℤ, a n = 8 * m

/-- The power-of-two direction: if `n = 2 ^ k`, every witness of divisibility by `8` is odd. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ m : ℤ, a n = 8 * m → (∃ k : ℕ, n = 2 ^ k) → Odd m

/-- The converse direction: an odd witness of divisibility by `8` forces `n` to be a power of two. -/
def H3 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ m : ℤ, a n = 8 * m → Odd m → ∃ k : ℕ, n = 2 ^ k

theorem main : H1 → H2 → H3 → type_of% @OeisA189286.conjecture_3 := by
  intro h1 h2 h3 n hn
  obtain ⟨m, hm⟩ := h1 n hn
  refine ⟨m, hm, ?_⟩
  exact ⟨h3 n hn m hm, h2 n hn m hm⟩

end OMA.R_OeisA189286_conjecture_3_R1
