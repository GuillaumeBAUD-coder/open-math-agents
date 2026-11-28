import Mathlib

/-!
# Map folding – exact asymptotic scaling conjecture for stamp foldings and semimeanders

Source: https://en.wikipedia.org/wiki/Map_folding
Primary references cited by the source:
- J. E. Koehler (1968), "Folding a strip of stamps", J. Combin. Theory 5(2): 135–152.
- S. Legendre (2014), "Foldings and meanders", Australas. J. Combin. 58: 275–291, arXiv:1302.2025.
- P. Di Francesco (2000), "Exact asymptotics of meander numbers", FPSAC 2000, pp. 3–14;
  P. Di Francesco, O. Golinelli, E. Guitter (2000), "Meanders: Exact Asymptotics",
  Nucl. Phys. B 570: 699–712, arXiv:cond-mat/9910453 (v3).

## Scope and ambiguity note

The Wikipedia article *Map folding* is a catalog covering several open problems:
1. Labeled stamp foldings (`t(n) = A000136(n)`) and semimeanders (`M̄(n) = t(n)/n = A000682(n)`):
   whether a closed-form formula or polynomial-time algorithm exists, and the physics-predicted
   asymptotic behavior (citing Di Francesco 2000 [10]).
2. Counting foldings of an `n × n` rectangular map (`A001418`, known only for `n ≤ 7`), for which
   the source gives no conjectured formula or asymptotic exponent.
3. Computational complexity of deciding flat-foldability of a 2D map with a given mountain-valley
   assignment (which depends on a computational model).

This file formalizes the precise, model-independent open conjecture from reference [10]
(Di Francesco 2000 / Di Francesco–Golinelli–Guitter `cond-mat/9910453v3`, Sections 1 & 4) for the
labeled stamp-folding count `t(n) = A000136(n)` and equivalently semimeanders
`M̄(n) = t(n) / n = A000682(n)`:

  `M̄(n) ~ C * R^n * n^(-ᾱ)`  as `n → ∞`,  with  `ᾱ = 1 + √11 * (√29 + √5) / 24`,

equivalently (since `t(n) = n * M̄(n)` for all `n ≥ 1`, Legendre Prop. 2.2),

  `t(n) ~ C * R^n * n^(-β)`  as `n → ∞`,  with  `β = ᾱ - 1 = √11 * (√29 + √5) / 24`,

for positive real constants `R > 0` and `C > 0`. Note that Wikipedia's prose informally refers to
predicting "the rate of exponential growth", whereas Di Francesco–Golinelli–Guitter
(`cond-mat/9910453v3`, Section 6) explicitly state that `R` is non-universal and unpredicted by
the conformal field theory / KPZ derivation, which instead predicts the universal exponent `ᾱ`.
Hence `R` and `C` are existentially quantified as positive reals.

## Amplitude, parity, and strength distinctions

- **Global amplitude vs. parity-split amplitudes**: In `cond-mat/9910453v3` (Section 4), the
  scaling `M̄(n) ~ R^n / n^ᾱ` (where `~` denotes asymptotic proportionality up to a positive
  constant, cf. Section 6 where Catalan numbers are written `c_n ~ 4^n / n^(3/2)`) is derived
  from a single dominant singularity `(x_c - x)^(2Δ_1 - γ_str)` of the generating function, giving
  a single leading amplitude `C > 0`. Likewise, Legendre (`1302.2025v1`, Section 7, eq. (7.2))
  states the single-constant form `x(n) ~ K * n^α * λ^n` for `t(n)` and `r(n) = M̄(n)`, while
  explicitly reserving distinct even/odd leading constants `K_1, K_2` for open meanders `m(n)`
  (`A005316`). Numerical extrapolations (Jensen & Guttmann `cond-mat/0004321`; Di Francesco–
  Guitter–Jacobsen `cond-mat/0003008`) separate even and odd `n` because of strong finite-`n`
  parity oscillations, but report a single leading semimeander amplitude `C ≈ 0.688(1)` with
  alternating terms entering at subleading order.
- **Full scaling conjecture vs. weaker consequences**: The full asymptotic scaling stated in
  `main` (`t(n) / (R^n * n^(-β)) → C > 0`, equivalently `t(n) ~ C * R^n * n^(-β)`) implies:
  1. parity-split power-law scaling (`t(2k) / (R^(2k) * (2k)^(-β)) → C_even > 0` and
     `t(2k+1) / (R^(2k+1) * (2k+1)^(-β)) → C_odd > 0`), which in turn implies
  2. the logarithmic subexponential limit
     `(log (t n) - n * log R) / log n → -β` as `n → ∞`.
  Neither converse holds in general: the logarithmic limit is strictly weaker, allowing arbitrary
  `n^{o(1)}` multiplicative factors such as `(log n)^k` or `exp(√(log n))` that contradict the
  pure power-law scaling conjectured by Di Francesco–Golinelli–Guitter.

## Combinatorial encoding

Following Koehler (1968) and Legendre (`1302.2025v1`, Lemma 2.1, cited on the source page), a
valid flat folding of a labeled strip of `n` stamps `0, 1, ..., n - 1` is encoded by the
permutation `p : Equiv.Perm (Fin n)` assigning to each stamp `i` its vertical position `p i` in
the folded stack (so `p⁻¹` lists the stamp labels from top to bottom). Creases `(i, i + 1)` and
`(j, j + 1)` lie on the same side of the stack iff `i % 2 = j % 2`, and the folding is physically
realizable iff no two same-parity creases interleave in the linear stack order (equivalently, no
two same-parity indices `i, j` have `p i, p j, p (i + 1), p (j + 1)` in cyclic order).
-/

namespace OMA.S_wp_map_folding_various_problems_in_map_folding_and_stamp_folding

/-- Two creases connecting stack positions `{a, b}` and `{c, d}` cross iff their closed intervals
strictly interleave in the linear stack order on `Fin n`. -/
def CreasesCross {n : ℕ} (a b c d : Fin n) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
  (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

instance {n : ℕ} (a b c d : Fin n) : Decidable (CreasesCross a b c d) := by
  unfold CreasesCross
  infer_instance

/-- A permutation `p : Equiv.Perm (Fin n)` (mapping stamp `i` to its stack position `p i`) is a
valid labeled stamp folding iff no two creases of the same parity cross. -/
def IsStampFolding {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin (n - 1), i.val % 2 = j.val % 2 →
    ¬ CreasesCross
      (p ⟨i.val, by omega⟩) (p ⟨i.val + 1, by omega⟩)
      (p ⟨j.val, by omega⟩) (p ⟨j.val + 1, by omega⟩)

instance {n : ℕ} (p : Equiv.Perm (Fin n)) : Decidable (IsStampFolding p) := by
  unfold IsStampFolding
  infer_instance

/-- The number of distinct foldings of a strip of `n` labeled stamps (OEIS A000136 for `n ≥ 1`:
`1, 2, 6, 16, 50, 144, 462, 1392, ...`). -/
def stampFoldingCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (IsStampFolding (n := n))).card

/-- Di Francesco–Golinelli–Guitter exact asymptotic scaling conjecture
(`cond-mat/9910453v3`, Sections 1 & 4; Di Francesco, FPSAC 2000, cited as ref. [10] on
`https://en.wikipedia.org/wiki/Map_folding`) for the labeled stamp-folding sequence
`t(n) = A000136(n)` (equivalently semimeanders `M̄(n) = t(n) / n = A000682(n)`):
there exist `R > 0` and `C > 0` such that
`t(n) ~ C * R^n * n^(-(√11 * (√29 + √5) / 24))` as `n → ∞`,
equivalently `M̄(n) ~ C * R^n * n^(-(1 + √11 * (√29 + √5) / 24))`. -/
theorem main :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      Filter.Tendsto
        (fun n : ℕ =>
          (stampFoldingCount n : ℝ) /
            (R ^ n * (n : ℝ) ^ (-(Real.sqrt 11 * (Real.sqrt 29 + Real.sqrt 5) / 24))))
        Filter.atTop
        (nhds C) := by
  sorry

end OMA.S_wp_map_folding_various_problems_in_map_folding_and_stamp_folding
