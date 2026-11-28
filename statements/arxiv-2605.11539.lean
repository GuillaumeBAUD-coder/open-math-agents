import Mathlib

/-!
# The value of the noisy min-max game on the binary tree converges in distribution

Source: O. Angel, G. Ray, Y. Spinka, A noisy min-max game on trees,
https://arxiv.org/abs/2605.11539 (v1, 12 May 2026), Section 6, Problem 6.1:
Show that V_n converges in distribution when d = 2.
Credit: @tatashbar

The source, in words (Section 1 and Section 1.2). Let T_d be the infinite d-ary tree, with an
independent cookie X_e, uniform on {-1, +1}, on every edge e. Starting at the root, two players
alternate turns choosing a child to move to, until level 2n is reached (after n rounds). The payoff
to player 1 from player 2 is the sum of the 2n cookies along the chosen path; player 1 maximizes and
player 2 minimizes, both with full information. V_n is the value of this game. Formally (their
equation (1.1)): V_n(v) = 0 for v at height 2n, and for v at height less than 2n,
  V_n(v) = max over the children u of v of (X_uv + V_n(u))   if the height of v is even,
  V_n(v) = min over the children u of v of (X_uv + V_n(u))   if the height of v is odd,
and V_n = V_n(root). The paper proves that (V_n) is tight for d = 2 and converges in distribution for
d >= 3, and states the convergence for d = 2 as open (abstract, introduction, Problem 6.1).

Formalization choices, and where a reader could object.
1. The probability space is finite. V_n depends only on the cookies of the first 2n levels, so the
   law of V_n is the image of the uniform measure on the cookie configurations of the binary tree of
   depth 2n. A configuration is an element of `CTree (2 * n)`: a tree of depth r + 1 is a pair, one
   entry for each of the two children of the root, of (cookie on the edge to that child, labelled
   subtree of depth r below that child); a tree of depth 0 is a single leaf. Every edge of the binary
   tree of depth r carries exactly one Boolean, so `CTree r` is in bijection with the assignments of
   +1 or -1 to the edges, and the uniform (counting) measure on it is the law of independent uniform
   cookies.
2. Cookies: `true` is +1 and `false` is -1.
3. Who moves. `val r t` is the value of the game on a tree of depth r, with leaf value 0. A vertex
   whose subtree has depth r + 1 lies at height 2n - (r + 1) in a tree of depth 2n, so its height is
   even exactly when r + 1 is even: there the maximizer moves, otherwise the minimizer. In
   particular the root of a tree of depth 2n is a max vertex (player 1 moves first) and the last move
   is made by the minimizer, as in the source.
4. Probability as a ratio of cardinalities: P(V_n <= k) is the number of configurations t with
   `val (2 * n) t <= k` divided by the number of all configurations (`Nat.card`; both types are
   finite and the second is nonempty).
5. Convergence in distribution. V_n is integer valued, so the statement asks for a function F on
   the integers that is the distribution function of a probability measure on the integers
   (nondecreasing, limit 0 at minus infinity, limit 1 at plus infinity) with P(V_n <= k) -> F(k)
   for every integer k. For integer-valued random variables this is equivalent to convergence in
   distribution: if V_n -> V in distribution then V is integer valued and
   P(V_n <= k) = P(V_n <= k + 1/2) -> P(V <= k + 1/2) = P(V <= k), since k + 1/2 is a continuity
   point; conversely the displayed convergence gives convergence of the distribution functions at
   every non-integer point, and these are the continuity points of the limit that matter. No
   centring or scaling is applied: it is V_n itself that converges, as in Theorem 1.2 of the source
   for d >= 3.
6. Only d = 2 is formalized, as asked in Problem 6.1.
-/

namespace OMA.S_arxiv_2605_11539

/-- Cookie configurations of the complete binary tree of depth `r`: for each of the two children of
the root, the cookie on the edge to that child and the configuration of the subtree below it. -/
def CTree : ℕ → Type
  | 0 => Unit
  | r + 1 => (Bool × CTree r) × (Bool × CTree r)

/-- A cookie is `+1` (`true`) or `-1` (`false`). -/
def cookie (b : Bool) : ℤ := if b then 1 else -1

/-- The value of the game on a tree of depth `r`: leaves have value `0`; at a vertex whose subtree
has depth `r + 1` the mover takes the better of the two children, each child being worth the cookie on
its edge plus the value below it; the mover maximizes when `r + 1` is even and minimizes when it is
odd. On a tree of depth `2 * n` the maximizer moves first and each player moves `n` times. -/
def val : (r : ℕ) → CTree r → ℤ
  | 0, _ => 0
  | r + 1, ((c₁, t₁), (c₂, t₂)) =>
      if Even (r + 1) then max (cookie c₁ + val r t₁) (cookie c₂ + val r t₂)
      else min (cookie c₁ + val r t₁) (cookie c₂ + val r t₂)

/-- Problem 6.1 of the source: for `d = 2` the value `V_n` converges in distribution. -/
theorem main : ∃ F : ℤ → ℝ, Monotone F ∧
    Filter.Tendsto F Filter.atBot (nhds 0) ∧ Filter.Tendsto F Filter.atTop (nhds 1) ∧
    ∀ k : ℤ, Filter.Tendsto
      (fun n : ℕ => (Nat.card {t : CTree (2 * n) // val (2 * n) t ≤ k} : ℝ) / (Nat.card (CTree (2 * n)) : ℝ))
      Filter.atTop (nhds (F k)) := by
  sorry

end OMA.S_arxiv_2605_11539
