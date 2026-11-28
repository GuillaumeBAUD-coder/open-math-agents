import Mathlib

/-!
# A341334 — positions of zero-free binary words

The one-based word list is defined in https://oeis.org/A341334. The set of
unary input lengths accepted by adaptive automaton 4258072 is A134342,
defined independently in https://oeis.org/A134342.
-/

namespace OMA.S_oeis_a341334

inductive EdgeLabel
  | plain
  | f
  | g
  deriving DecidableEq

/-- Vertices in cyclic order, starting at the cursor. The Boolean marks the
    unique accepting vertex, and the second component labels the outgoing edge. -/
abbrev Ring := List (Bool × EdgeLabel)

/-- Replace the outgoing label of the next state after following G. -/
def setNextF : Ring → Ring
  | [] => []
  | (v, _) :: rest => (v, .f) :: rest

/-- Perform the pre-transition action and consume one unary input symbol. -/
def step : Ring → Ring
  | [] => []
  | (v, .plain) :: rest => rest ++ [(v, .plain)]
  | (v, .g) :: rest => setNextF (rest ++ [(v, .plain)])
  | [(v, .f)] => [(false, .g), (v, .plain)]
  | (v, .f) :: (w, _) :: rest =>
    (w, .plain) :: (false, .g) :: (rest ++ [(v, .f)])

/-- The cursor initially points to the accepting vertex with an F-labelled loop. -/
def run : ℕ → Ring
  | 0 => [(true, .f)]
  | n + 1 => step (run n)

/-- Whether automaton 4258072 accepts the unary input of length `n`. -/
def visit (n : ℕ) : Bool :=
  match run n with
  | [] => false
  | (v, _) :: _ => v

/-- One-based position in the word list. The empty tail has auxiliary index 0.
For a tail at index `p`, prefixing zero selects entry `p+1` of
`1,4,7,…`, and prefixing one selects entry `p+1` of its positive
complement `2,3,5,6,…`. These are the two branch sequences in A341334. -/
def wordPosition : List Bool → Nat
  | [] => 0
  | false :: w => 3 * wordPosition w + 1
  | true :: w => 3 * wordPosition w / 2 + 2

/-- A134342 includes 0, the length of the empty input. The OEIS list W
starts at position 1, so its zero-free positions correspond to the positive
terms of A134342. The two unadjusted lists differ at 0. -/
theorem main :
    ∀ n : Nat, 0 < n →
      ((∃ w : List Bool, false ∉ w ∧ wordPosition w = n) ↔ visit n = true) := by
  sorry

end OMA.S_oeis_a341334
