import Mathlib

/-!
# Multiple coverage in Andrew Smith's square Genealodron (OEIS A333637)

A path at depth `4*q+r`, with `r < 4`, takes `2*q+(r+1)/2` horizontal
steps and `2*q+r/2` vertical steps. The axes alternate, starting horizontally.
A path is specified by the subsets of the horizontal and vertical steps
which have positive sign. At a cell indexed by integers `(u,v)`, these
subsets have sizes `u+q` and `v+q`. The physical center of that cell is
`(2*u-(r+1)/2, 2*v-r/2)`. The four residues give the four distinct parity
pairs of centers, so their overlap counts add. The root has depth zero
and the n-th generation includes exactly the depths strictly less than n.

Václav Kotesovec conjectured the quadratic formula. Colin Barker conjectured
the generating function and recurrence. Source: https://oeis.org/A333637
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

noncomputable section

namespace OMA.S_oeis_a333637

abbrev Cell := ℤ × ℤ

def horiz (r : ℕ) := (r+1)/2
def vert (r : ℕ) := r/2

def axis (q s : ℕ) : Finset ℤ := Finset.Icc (-(q:ℤ)) ((q:ℤ)+s)

def rect (r q : ℕ) : Finset Cell := axis q (horiz r) ×ˢ axis q (vert r)

/-- Choose exactly those steps going right (or up) from all steps on the axis. -/
def signChoices (q s : ℕ) (z : ℤ) : ℕ :=
  if z ∈ axis q s then ((Finset.range (2*q+s)).powersetCard (z+q).toNat).card else 0

def multiplicity (r t : ℕ) (p : Cell) := ∑ q ∈ Finset.range t,
  signChoices q (horiz r) p.1 * signChoices q (vert r) p.2

def overlaps (r t : ℕ) : Finset Cell :=
  ((Finset.range t).biUnion (rect r)).filter fun p => 2 ≤ multiplicity r t p

def center (r : ℕ) (p : Cell) : Cell := (2*p.1-horiz r, 2*p.2-vert r)

/-- The physical cells covered more than once, across all four classes. -/
def a (n : ℕ) := ((Finset.range 4).biUnion fun r =>
  (overlaps r ((n+3-r)/4)).image (center r)).card

open PowerSeries in
theorem main : (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = (n:ℤ)^2 - n - 15) ∧
    ((PowerSeries.mk fun n => (a n : ℤ)) * (1-X)^3 =
      X^4*(1+X^2)*(2+X-2*X^2)) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3*(a (n-1):ℤ) - 3*(a (n-2):ℤ) + a (n-3)) := by
  sorry

end OMA.S_oeis_a333637
