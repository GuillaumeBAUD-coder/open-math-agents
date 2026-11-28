import FormalConjectures.ErdosProblems.«236»

-- Reduction Erdos236.erdos_236.R1 of Erdős Problem 236
-- Credit: @MBimrose (agent: hub-swarm-pi)

/-!
# Erdős Problem 236 (`f n = o(log n)`): the quantitative core, and the calculus that turns it into
little-oh

`f n` counts the `k < Nat.log2 n + 1` for which `n - 2 ^ k` is prime, i.e. the representations of `n`
as `p + 2 ^ k`. The trivial bound `f n ≤ Nat.log2 n + 1` (proved below) gives `f = O(log n)` for
free, so the whole content of the problem is the little-oh: those representations must be sparse
pointwise, not merely on average.

Pointwise control is what the literature does not have. Erdős (1950) and Chen (2023) prove moment
bounds `∑_{n ≤ X} r(n)^k ≪_k X`, which control almost every `n` and say nothing about the tail of a
single fixed `n`; a sieve for `n - 2 ^ k` over `k ≤ log2 n` would need the joint modulus `lcm` of
the orders `ord_q(2)` of the small primes `q`, and that is already astronomically larger than
`log n` for a handful of primes, so the CRT error swamps the main term (see the DEAD END note of
2026-11-28T03:53 on this problem).

So this file separates the two things that `f = o(log n)` bundles:

* `H1` (quantitative core; no proof known, and strictly stronger than the target):
  `f n ≤ log n / log log n` for all sufficiently large `n`. This is a concrete, checkable,
  paper-style bound -- the kind of statement one would actually prove about `f`.
* `H2` (elementary): `log n / log log n = o(log n)`. Pure calculus, and it is *proved* in this
  file as `log_div_loglog_isLittleO`, so `main` uses a verified step rather than an assumed one.

`main` composes the two through `Asymptotics.IsBigO.trans_isLittleO`.

The trivial half of the problem is also proved here, not assumed: `f n ≤ Nat.log2 n + 1`.
-/

namespace OMA.R_Erdos236_erdos_236_R1

open Filter Asymptotics
open scoped Topology

/-- Quantitative core (no proof known): the number of representations of `n` as `p + 2 ^ k` is at
most `log n / log log n` for every sufficiently large `n`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (Erdos236.f n : ℝ) ≤ Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))

/-- Calculus step: `log n / log log n = o(log n)`. Proved below as `log_div_loglog_isLittleO`. -/
def H2 : Prop :=
  (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) =o[atTop]
    (fun n : ℕ => Real.log (n : ℝ))

/-- The trivial counting bound: `f n` is the length of a filtered list of length `Nat.log2 n + 1`. -/
lemma f_le_log2 (n : ℕ) : Erdos236.f n ≤ Nat.log2 n + 1 := by
  have h := List.length_filter_le (fun k : ℕ => Nat.Prime (n - 2 ^ k)) (List.range (Nat.log2 n + 1))
  simpa [Erdos236.f] using h

/-- `log` of the index tends to infinity, hence is eventually positive and eventually exceeds one. -/
lemma tendsto_log_atTop_nat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma eventually_log_pos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
  tendsto_log_atTop_nat.eventually (eventually_gt_atTop 0)

lemma eventually_one_lt_log : ∀ᶠ n : ℕ in atTop, 1 < Real.log (n : ℝ) :=
  tendsto_log_atTop_nat.eventually (eventually_gt_atTop 1)

lemma eventually_log_pos_log : ∀ᶠ n : ℕ in atTop, 0 < Real.log (Real.log (n : ℝ)) := by
  filter_upwards [eventually_one_lt_log] with n hn
  exact Real.log_pos hn

/-- `log n / log log n = o(log n)`: the ratio of the two sides is `1 / log log n`, which tends to
zero because `log n` tends to infinity and `log` of it therefore does too. -/
lemma log_div_loglog_isLittleO :
    (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_atTop_nat
  refine (Asymptotics.isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr ?_
  refine hloglog.inv_tendsto_atTop.congr' ?_
  filter_upwards [eventually_log_pos, eventually_log_pos_log] with n hn hll
  change (Real.log (Real.log (n : ℝ)))⁻¹ =
    Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)
  have hne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hn
  have hllne : Real.log (Real.log (n : ℝ)) ≠ 0 := ne_of_gt hll
  field_simp

/-- `H1` and `H2` together are the problem: a uniform bound by `log n / log log n` is a `O` of that
function, and that function is a little-oh of `log n`. -/
theorem main : H1 → H2 → type_of% @Erdos236.erdos_236 := by
  intro h1 h2
  have hO : (fun n : ℕ => (Erdos236.f n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [h1, eventually_log_pos, eventually_log_pos_log] with n hn hl hll
    have hg : 0 < Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := div_pos hl hll
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (Erdos236.f n : ℝ) by positivity),
      abs_of_nonneg (le_of_lt hg), one_mul]
    exact hn
  exact hO.trans_isLittleO h2

end OMA.R_Erdos236_erdos_236_R1
