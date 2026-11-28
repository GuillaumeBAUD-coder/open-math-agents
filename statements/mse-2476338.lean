import Mathlib

namespace OMA.S_mse_2476338

/-- Partial numerator `a_n = -a q^n` (for `n ≥ 1`) of the Generalized Rogers-Ramanujan
continued fraction `F(a, q) = 1 - aq / (1 - aq^2 / (1 - aq^3 / ...))`. -/
def fNum (a q : ℂ) (n : ℕ) : ℂ := -a * q ^ n

/-- Partial numerator `a_n` (for `n ≥ 1`) of the conjectured continued fraction
`H(a, q) = 1 / (1 + aq / (1 - aq / (1 - q / (1 + q / (1 + aq^2 / ...)))))`. -/
def hNum (a q : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let j := n / 4 + 1
    match n % 4 with
    | 0 => a * q ^ j
    | 1 => -(a * q ^ j)
    | 2 => -(q ^ j)
    | _ => q ^ j

/-- Standard continued fraction convergent recurrence `((p_n, q_n), (p_{n-1}, q_{n-1}))`
for `b_0 + K_{k=1}^∞ (a_k / 1)` where `p_{-1} = 1, q_{-1} = 0, p_0 = b_0, q_0 = 1`. -/
def cfPair (b0 : ℂ) (aSeq : ℕ → ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((b0, 1), (1, 0))
  | n + 1 =>
    let ((pn, qn), (p1, q1)) := cfPair b0 aSeq n
    ((pn + aSeq (n + 1) * p1, qn + aSeq (n + 1) * q1), (pn, qn))

/-- The `n`-th convergent `p_n / q_n` of `b_0 + K_{k=1}^∞ (a_k / 1)`. -/
noncomputable def cfConv (b0 : ℂ) (aSeq : ℕ → ℂ) (n : ℕ) : ℂ :=
  (cfPair b0 aSeq n).1.1 / (cfPair b0 aSeq n).1.2

/-- The `q`-Pochhammer symbol `(q)_n = ∏_{k=1}^n (1 - q^k)`. -/
def qPoch (q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - q ^ (k + 1))

theorem main :
    ∀ a q : ℂ, ‖q‖ < 1 →
      (∑' n : ℕ, (-a) ^ n * q ^ (n * (n + 1)) / qPoch q n) ≠ 0 →
      Filter.Tendsto (cfConv 1 (fNum a q)) Filter.atTop
        (nhds ((∑' n : ℕ, (-a) ^ n * q ^ (n ^ 2) / qPoch q n) /
          (∑' n : ℕ, (-a) ^ n * q ^ (n * (n + 1)) / qPoch q n))) ∧
      Filter.Tendsto (cfConv 0 (hNum a q)) Filter.atTop
        (nhds ((∑' n : ℕ, (-a) ^ n * q ^ (n ^ 2) / qPoch q n) /
          (∑' n : ℕ, (-a) ^ n * q ^ (n * (n + 1)) / qPoch q n))) := by
  sorry

end OMA.S_mse_2476338
