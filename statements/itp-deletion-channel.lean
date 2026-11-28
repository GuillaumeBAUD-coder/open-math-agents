import Mathlib

/-!
# Capacity of the binary deletion channel

Source: https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/deletion-channel.md
Credit: @eltociear

The source page asks to *determine* the capacity `C(d)` of the binary deletion channel
for `d ∈ (0,1)` (a closed form, a single-letter characterization, or matching bounds).
That request is not itself a proposition. The source repository ships its own Lean
statement of the problem (`lean/InfoTheory/Problems/DeletionChannel.lean`,
`InfoTheory.Problems.DeletionChannel.Statement`), and we follow that reading here:
the central open structural conjecture on `C(d)`, that `d ↦ C(d)` is **convex on `(0,1)`**
(Mitzenmacher, *A survey of results for deletion channels and related synchronization
channels*, Probability Surveys 2009, Open Problem 1).

The definitions below are ported verbatim, with the source's names and conventions, from
`lean/InfoTheory/Core/Entropy.lean` and `lean/InfoTheory/Core/Channels.lean` of the source
repository (which cannot be imported here):

* `deletionProb d x y = Pr[Del_d(x) = y] = #(embeddings of y in x as a subsequence) ·
  (1-d)^|y| · d^(|x|-|y|)`, which is the i.i.d. deletion channel: every bit is deleted
  independently with probability `d` and the survivors are output in order, with no
  indication of which positions were deleted.
* `deletionChannelMI d n P = H(Y) - H(Y | X)` in bits, for an input distribution `P` on
  `{0,1}^n`; the output `Y` ranges over all binary strings of length `≤ n`.
* `binaryDeletionMaxMI d n = C_n(d) = sup_P I(X^n; Y)`.
* `binaryDeletionCapacity d = inf_{n ≥ 1} C_n(d) / n`. Because `C_n` is subadditive in `n`
  (a block-concatenated output carries at most the information of the separate outputs),
  by Fekete's lemma this infimum equals `lim_n C_n(d)/n`, Dobrushin's capacity.
-/

namespace OMA.S_itp_deletion_channel

open scoped BigOperators

/-- Base-2 logarithm on `ℝ`. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The elementary entropy summand `-p log₂ p`, defined as `0` for `p ≤ 0`. -/
noncomputable def negPLogP (p : ℝ) : ℝ :=
  if p ≤ 0 then 0 else -p * log2 p

/-- A finite probability distribution over a finite type `α`. -/
structure ProbDist (α : Type*) [Fintype α] where
  pmf : α → ℝ
  nonneg : ∀ a, 0 ≤ pmf a
  sum_one : ∑ a : α, pmf a = 1

/-- Exact number of ways `y` appears as a subsequence of `x`
(number of position sets of `x` whose surviving letters spell `y`). -/
def subseqCount {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | _, [] => 1
  | [], _ :: _ => 0
  | a :: xs, b :: ys =>
      subseqCount xs (b :: ys) + (if a = b then subseqCount xs ys else 0)

/-- Transition probability `Pr[Del_d(x) = y]` for the i.i.d. binary deletion channel with
deletion probability `d`. -/
noncomputable def deletionProb (d : ℝ) (x y : List Bool) : ℝ :=
  if y.length ≤ x.length then
    (subseqCount x y : ℝ) * (1 - d) ^ y.length * d ^ (x.length - y.length)
  else 0

/-- Mutual information `I(X^n; Y) = H(Y) - H(Y | X^n)` (in bits) between an input `X^n`
with law `P` on `{0,1}^n` and the output `Y = Del_d(X^n)`, an element of
`Σ k : Fin (n+1), Fin k → Bool` (a binary string of length `k ≤ n`). -/
noncomputable def deletionChannelMI (d : ℝ) (n : ℕ) (P : ProbDist (Fin n → Bool)) : ℝ :=
  let toList : (Fin n → Bool) → List Bool := fun x => List.ofFn x
  let outType := Σ k : Fin (n + 1), Fin k.1 → Bool
  let py : outType → ℝ := fun y =>
    ∑ x : Fin n → Bool, P.pmf x * deletionProb d (toList x) (List.ofFn y.2)
  let hY : ℝ := ∑ y : outType, negPLogP (py y)
  let hYgivenX : ℝ := ∑ x : Fin n → Bool, P.pmf x *
    ∑ y : outType, negPLogP (deletionProb d (toList x) (List.ofFn y.2))
  hY - hYgivenX

/-- `C_n(d) = sup_{P(x^n)} I(X^n; Y)` at block length `n`. -/
noncomputable def binaryDeletionMaxMI (d : ℝ) (n : ℕ) : ℝ :=
  sSup { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = deletionChannelMI d n P }

/-- Capacity `C(d) = lim_n C_n(d)/n = inf_{n ≥ 1} C_n(d)/n` of the binary deletion channel
(Dobrushin 1967; Fekete's lemma, `C_n` being subadditive). -/
noncomputable def binaryDeletionCapacity (d : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = binaryDeletionMaxMI d n / (n : ℝ) }

/-- Convexity of the binary deletion channel capacity on `(0,1)`
(Mitzenmacher 2009, Open Problem 1; the source repository's own Lean statement). -/
theorem main :
    ∀ (d₁ d₂ t : ℝ),
      0 < d₁ → d₁ < 1 → 0 < d₂ → d₂ < 1 → 0 ≤ t → t ≤ 1 →
      binaryDeletionCapacity (t * d₁ + (1 - t) * d₂) ≤
        t * binaryDeletionCapacity d₁ + (1 - t) * binaryDeletionCapacity d₂ := by
  sorry

end OMA.S_itp_deletion_channel
