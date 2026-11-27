import Mathlib

/-!
# A congruence conjecture for the Lucas sequence

Source: https://math.stackexchange.com/questions/453864/a-conjecture-about-lucas-series
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $L_n$ be the Lucas sequence: $L_0 = 2$, $L_1 = 1$, $L_n = L_{n-1} + L_{n-2}$ for $n > 1$.
Let $p$ be a prime with $p \equiv 3, 7 \pmod{20}$, so that $2p = x^2 + 5y^2$ for some
$x, y \in \mathbb{Z}$. Is it true that
$$L_{(p+1)/4} \equiv \begin{cases}
  (-2)^{(p+1)/4} \pmod p & \text{if } y \equiv \pm \frac{p-1}{2} \pmod 8, \\
  -(-2)^{(p+1)/4} \pmod p & \text{otherwise}?
\end{cases}$$
-/

namespace OMA.S_mse_453864

/-- The Lucas sequence $L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n$. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

theorem main :
    ∀ (p : ℕ), p.Prime → (p % 20 = 3 ∨ p % 20 = 7) →
      ∀ (x y : ℤ), 2 * (p : ℤ) = x ^ 2 + 5 * y ^ 2 →
        let k := (p + 1) / 4
        if (y ≡ ((p : ℤ) - 1) / 2 [ZMOD 8] ∨ y ≡ -(((p : ℤ) - 1) / 2) [ZMOD 8]) then
          lucas k ≡ (-2 : ℤ) ^ k [ZMOD (p : ℤ)]
        else
          lucas k ≡ -((-2 : ℤ) ^ k) [ZMOD (p : ℤ)] := by
  sorry

end OMA.S_mse_453864
