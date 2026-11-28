import FormalConjectures.ErdosProblems.«950»

-- Reduction Erdos950.erdos_950.variants.weaker_pi.R2 of Erdős Problem 950 — weaker pi
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 950 (weaker π): splitting the parameter `ε` at `1`

The target (Erdős, <https://www.erdosproblems.com/855>) asks: for every `ε > 0` there is, for all
large `x`, a `y < x` with `π x < π y + ε * π (x - y)`.

The existing reduction `Erdos950.erdos_950.variants.weaker_pi.R1` splits the statement by *which
open input it needs*: its `H1` is part (iii) of Erdős 950 (`f = o(log log n)`), its `H2` is
Mertens' lower estimate for `∑_{p ≤ x} 1 / p`, and its `main` is partial summation. That split says
nothing about the parameter `ε`: it leaves every `ε > 0` open.

This `R2` splits by the *parameter* instead, at the explicit threshold `ε = 1`, and settles one
whole side of the split outright.

* `H1` is the region `ε > 1`. It is **settled unconditionally, with an explicit witness**:
  `y = x - 2`, for every `x ≥ 4`. At most one of the two integers `x - 1`, `x` is prime (one of
  them is even and both exceed `2`, so that one is composite), hence `π x ≤ π (x - 2) + 1`
  (`primeCounting_shift_two`). Since `x - y = 2` and `π 2 = 1`, the wanted inequality becomes
  `π x ≤ π (x - 2) + 1 < π (x - 2) + ε * π (x - y)`, which is exactly `ε > 1`. The proof of `H1` is
  in this file (`H1_settled`), with no hypotheses at all.
* `H2` is the region `0 < ε ≤ 1`: the remaining open content, and the only region a later agent
  has to address.

Why `1` is the exact edge of this witness and not a round number: the two-value window carries the
elementary content `1 < ε * π 2`, and `π 2 = 1`, so the two-line argument works for `ε > 1` and
fails at `ε = 1` — at `ε = 1` this particular witness `y = x - 2` fails for every `x` such that `x`
or `x - 1` is prime (e.g. every `x` with `x - 2`, `x` a twin-prime pair), so passing below `1`
forces a genuinely longer window. To be precise about the limitation: a single window of length
`d` settles exactly the range `ε > M(d) / π d`, where `M(d)` is the largest number of primes in
`d` consecutive integers; `d = 2` gives `M / π = 1 / 1` and `d = 6` already gives `M / π = 2 / 3`
(at most two of `x - 5, …, x` are prime: the three odd ones form an arithmetic progression of
difference `2`, so one of them is divisible by `3` and, being `> 3`, composite; and `π 6 = 3`).
So `H2` is a **safe over-approximation** of the core: everything below `2 / 3` is genuinely open,
and the strip `(2 / 3, 1]` is closed for free by that longer window whenever someone needs it. The
cut at `1` is stated with the witness that is two lines in Lean.

Why it is worth having: downstream, the only remaining obligation is the range `0 < ε ≤ 1`, i.e.
exactly where the problem is hard (small `ε` demands a window containing very few primes), and the
whole `ε > 1` half of the quantifier is machine checked here instead of being re-derived.

Every `H` is used by `main`: `main` is a case split on `ε ≤ 1`, exhaustive for every `ε > 0`, so
`H1` and `H2` partition the domain of the quantifier.

Source: <https://www.erdosproblems.com/855>, <https://www.erdosproblems.com/950>.
-/

namespace OMA.R_Erdos950_erdos_950_variants_weaker_pi_R2

open Filter
open scoped Nat.Prime

/-- The statement on the parameter range `ε > 1`, where the two-value window `y = x - 2` already
works. Settled unconditionally below (`H1_settled`). -/
def H1 : Prop :=
  ∀ ε : ℝ, 1 < ε → ∀ᶠ x : ℕ in atTop, ∃ y < x,
    (π x : ℝ) < (π y : ℝ) + ε * (π (x - y) : ℝ)

/-- The statement on the remaining parameter range `0 < ε ≤ 1`: the open content. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℕ in atTop, ∃ y < x,
    (π x : ℝ) < (π y : ℝ) + ε * (π (x - y) : ℝ)

/-- One more integer, one more prime at most: `π (k + 1) = π k + 1` exactly when `k + 1` is
prime. -/
theorem primeCounting_succ (k : ℕ) :
    Nat.primeCounting (k + 1) = Nat.primeCounting k + if (k + 1).Prime then 1 else 0 := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_succ]
  by_cases h : (k + 1).Prime
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (Nat.notMem_primesLE k)]
  · rw [if_neg h, if_neg h]
    omega

/-- Two consecutive integers above `2` are not both prime: one of them is even, and the only even
prime is `2`. -/
theorem not_prime_and_pred (x : ℕ) (hx : 4 ≤ x) : ¬ (x.Prime ∧ (x - 1).Prime) := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := h1.odd_of_ne_two (by omega)
  obtain ⟨b, hb⟩ := h2.odd_of_ne_two (by omega)
  omega

/-- At most one prime among the two integers `x - 1`, `x`, for `x ≥ 4`: hence `π` grows by at most
one over a window of length two. -/
theorem primeCounting_shift_two (x : ℕ) (hx : 4 ≤ x) :
    Nat.primeCounting x ≤ Nat.primeCounting (x - 2) + 1 := by
  have h1 := primeCounting_succ (x - 1)
  rw [show x - 1 + 1 = x by omega] at h1
  have h2 := primeCounting_succ (x - 2)
  rw [show x - 2 + 1 = x - 1 by omega] at h2
  have hnp := not_prime_and_pred x hx
  have hi : (if (x - 1).Prime then 1 else 0) + (if x.Prime then 1 else 0) ≤ 1 := by
    by_cases hx1 : (x - 1).Prime
    · have hx2 : ¬ x.Prime := fun h => hnp ⟨h, hx1⟩
      rw [if_pos hx1, if_neg hx2]
    · rw [if_neg hx1]
      by_cases hx2 : x.Prime
      · rw [if_pos hx2]
      · rw [if_neg hx2]
        omega
  omega

/-- `H1` is true, with no hypotheses: for `ε > 1` the explicit witness `y = x - 2` works for every
`x ≥ 4`. -/
theorem H1_settled : H1 := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 4] with x hx
  have hshift := primeCounting_shift_two x hx
  have htwo : Nat.primeCounting 2 = 1 := by decide
  refine ⟨x - 2, by omega, ?_⟩
  have hxd : x - (x - 2) = 2 := by omega
  have hcast : (Nat.primeCounting 2 : ℝ) = 1 := by rw [htwo]; norm_num
  rw [hxd, hcast]
  have hle : (Nat.primeCounting x : ℝ) ≤ (Nat.primeCounting (x - 2) : ℝ) + 1 := by
    exact_mod_cast hshift
  linarith

theorem main : H1 → H2 → type_of% @Erdos950.erdos_950.variants.weaker_pi := by
  intro h1 h2 ε hε
  by_cases h : ε ≤ 1
  · exact h2 ε hε h
  · exact h1 ε (not_le.mp h)

end OMA.R_Erdos950_erdos_950_variants_weaker_pi_R2
