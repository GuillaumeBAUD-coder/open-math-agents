import FormalConjectures.ErdosProblems.«677»

-- Reduction Erdos677.erdos_677.R1 of Erdős Problem 677
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 677: split by the length `k` of the interval

`M(n, k) = lcm(n+1, …, n+k)`; the claim is `M(m, k) ≠ M(n, k)` whenever `m ≥ n + k`.

* `H1` (`k ≤ 2`): elementary. `M(n, 1) = n + 1` and `M(n, 2) = (n + 1)(n + 2)`
  (consecutive integers are coprime), both strictly increasing in `n`.
* `H2` (`k = 3`): `M(n, 3) = P(n+1)/g` with `P(x) = x(x+1)(x+2)` and `g ∈ {1, 2}`, so a
  collision is an integer point on `X³ − X = 2(Y³ − Y)` (`X = m+2`, `Y = n+2`). This cubic is
  birational to an elliptic curve of rank 1 (Cremona 216a1), and the integer points reduce to
  finitely many Thue equations, solved unconditionally with PARI/GP (`thueinit(·, 1)`); only
  trivial solutions appear (sketch by @sntntHb, computer search, not yet in Lean). A finite,
  Diophantine statement, strictly easier than the whole problem.
* `H3` (`k = 4`): `M(n, 4) = P(a)/g` with `P(a) = a(a+1)(a+2)(a+3) = (a²+3a+1)² − 1` and
  `g ∈ {2, 6}`, so a collision forces `P(b) = 3P(a)`, i.e. `u² − 3v² = −2` with
  `u = b²+3b+1`, `v = a²+3a+1`; together with the square conditions this is again a finite
  problem (Pell orbits in `ℤ[√3]`), which a computer search by @sntntHb finds has no
  solutions with `m ≥ n + 4`.
* `H4` (`k ≥ 5`): the open part. For each fixed `k` there are finitely many solutions
  (Thue–Siegel), but no uniform argument is known.
-/

namespace OMA.R_Erdos677_erdos_677_R1

/-- Intervals of length 1 or 2 (elementary). -/
def H1 : Prop :=
  ∀ m n k : ℕ, 0 < k → k ≤ 2 → m ≥ n + k → Finset.lcmInterval m k ≠ Finset.lcmInterval n k

/-- Intervals of length 3 (a cubic Diophantine equation / Thue equations). -/
def H2 : Prop :=
  ∀ m n : ℕ, m ≥ n + 3 → Finset.lcmInterval m 3 ≠ Finset.lcmInterval n 3

/-- Intervals of length 4 (a Pell-type equation with square conditions). -/
def H3 : Prop :=
  ∀ m n : ℕ, m ≥ n + 4 → Finset.lcmInterval m 4 ≠ Finset.lcmInterval n 4

/-- Intervals of length at least 5 (the open part). -/
def H4 : Prop :=
  ∀ m n k : ℕ, 5 ≤ k → m ≥ n + k → Finset.lcmInterval m k ≠ Finset.lcmInterval n k

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos677.erdos_677 := by
  intro h1 h2 h3 h4 m n k hk hm
  by_cases hk2 : k ≤ 2
  · exact h1 m n k hk hk2 hm
  by_cases hk3 : k = 3
  · subst hk3
    exact h2 m n hm
  by_cases hk4 : k = 4
  · subst hk4
    exact h3 m n hm
  exact h4 m n k (by omega) hm

end OMA.R_Erdos677_erdos_677_R1
