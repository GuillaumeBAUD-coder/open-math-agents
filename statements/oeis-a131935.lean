import Mathlib.Init

/-!
# OEIS A131935

Samieinia's endpoint recurrences count Khalimsky-continuous functions
from the integer interval [0,n-1] to [0,3]. The four components count
functions ending at 0, 1, 2 and 3, respectively. We use those recurrences
to define the sequence independently of Barker's two conjectures.

Source: https://oeis.org/A131935
Endpoint counts: Shiva Samieinia, Digital straight line segments and curves,
Paper B, Theorem 4.1, equations (4.2)-(4.4).
https://www2.math.su.se/reports/2007/6/2007-6.pdf
Conjectures: Colin Barker, 13 January 2018.
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a131935

structure Endpoints where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

def Endpoints.total (s : Endpoints) : Nat := s.a + s.b + s.c + s.d

def oddToEven (s : Endpoints) : Endpoints :=
  ⟨s.a, s.a + s.b + s.c, s.c, s.c + s.d⟩

def evenToOdd (s : Endpoints) : Endpoints :=
  ⟨s.a + s.b, s.b, s.b + s.c + s.d, s.d⟩

/-- The flag is true when the current interval has odd cardinality. -/
def advance : Bool × Endpoints → Bool × Endpoints
  | (true, s) => (false, oddToEven s)
  | (false, s) => (true, evenToOdd s)

/-- The state for an interval of length k+1. A one-point domain has one
function ending at each of the four possible values. -/
def state : Nat → Bool × Endpoints
  | 0 => (true, ⟨1, 1, 1, 1⟩)
  | k + 1 => advance (state k)

/-- The OEIS sequence begins at one. The constant coefficient of its
ordinary generating function is zero. -/
def a : Nat → Nat
  | 0 => 0
  | k + 1 => (state k).2.total

/-- Coefficient of degree n of a polynomial times a formal series.
The list gives the polynomial coefficients in ascending degree. -/
def productCoeff (s : Nat → Int) : List Int → Nat → Int
  | [], _ => 0
  | c :: _, 0 => c * s 0
  | c :: cs, n + 1 => c * s (n + 1) + productCoeff s cs n

/-- Coefficients of 4X + 3X² - 4X³ - X⁴. -/
def numeratorCoeff : Nat → Int
  | 1 => 4
  | 2 => 3
  | 3 => -4
  | 4 => -1
  | _ => 0

/-- Barker's order-four recurrence, with index n+4 greater than 4,
and his ordinary generating function, expressed coefficientwise after
multiplication by its denominator 1 - X - 3X² + X³ + X⁴. -/
theorem main :
    (∀ n : Nat, 1 ≤ n →
      a (n + 4) + a (n + 1) + a n = a (n + 3) + 3 * a (n + 2)) ∧
    (∀ n : Nat,
      productCoeff (fun k => (a k : Int)) [1, -1, -3, 1, 1] n = numeratorCoeff n) := by
  sorry

end OMA.S_oeis_a131935
