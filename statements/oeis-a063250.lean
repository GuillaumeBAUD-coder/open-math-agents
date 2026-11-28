import Mathlib.Init

/-!
# A063250: Number of binary right-rotations (iterations of A038572) to reach fixed point.

Source: https://oeis.org/A063250
Credit: @LDJAI

The source gives the recurrence: a(n)=0 if n+1 is a power of 2,
and a(n)=1+a(floor(n/2)) otherwise.

The generating function is read with the summand bracketed as
(1/(1-x)) * sum_{j>=0} [x^(2^j) -
  (1-x^(2^j)) * sum_{k>=1} x^(2^j*(2^k-1))],
as required by the scope of j. We state equality coefficientwise over the integers.
The coefficient of x^n in x^m/(1-x) is 1 when m<=n and 0 otherwise.
Both sums truncate at index n+1 without changing the coefficient, since their
smallest exponents eventually exceed n. The inner index k is shifted by one
to start at zero. There is no restriction on n.
-/

namespace OMA.S_oeis_a063250

def mersenne (n : Nat) : Prop :=
  n + 1 = 2 ^ (Nat.log2 (n + 1))

instance (n : Nat) : Decidable (mersenne n) := inferInstanceAs
  (Decidable (n + 1 = 2 ^ (Nat.log2 (n + 1))))

def a (n : Nat) : Nat :=
  if h : mersenne n then 0 else 1 + a (n / 2)
termination_by n
decreasing_by
  have hn : n ≠ 0 := by
    intro h0
    subst n
    exact h (by decide)
  omega

def coeffGeom (n m : Nat) : Int := if m ≤ n then 1 else 0

/-- The finite sum over indices 0 through B-1. -/
def sumRange (f : Nat → Int) (B : Nat) : Int :=
  ((List.range B).map f).sum

theorem main : ∀ n : Nat,
    (a n : Int) =
      sumRange (fun j => coeffGeom n (2 ^ j) -
        sumRange (fun k => coeffGeom n (2 ^ j * (2 ^ (k + 1) - 1)) -
            coeffGeom n (2 ^ j * 2 ^ (k + 1))) (n + 1)) (n + 1) := by
  sorry

end OMA.S_oeis_a063250
