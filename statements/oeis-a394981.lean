import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Range

/-! Gary Yane's conjecture in A394981, offset 1. Each piece has a distinct
length. A layout lists its pieces' cell sets in decreasing order of length,
so a unit square has one orientation. The source gives the short side
floor((n+1)/2); the long side follows from the area. We identify all four
symmetries of a nonsquare rectangle. The sole square at n=1 has one cell.
Source: https://oeis.org/A394981 -/

namespace OMA.S_oeis_a394981

abbrev Tile := Finset ℕ
abbrev Layout := List Tile

def placements (h w len : ℕ) : Finset Tile :=
  (Finset.range (h*w)).biUnion fun i =>
    (if i%w + len ≤ w then { (Finset.range len).image (fun j => i+j) } else ∅) ∪
    (if i/w + len ≤ h then { (Finset.range len).image (fun j => i+w*j) } else ∅)

def layouts (h w : ℕ) : ℕ → Finset Layout
  | 0 => {[]}
  | k+1 => (layouts h w k).biUnion fun old =>
      ((placements h w (k+1)).filter fun tile =>
        old.all (fun used => decide (Disjoint tile used))).image (fun tile => tile::old)

def reflect (h w : ℕ) (flipY flipX : Bool) (i : ℕ) : ℕ :=
  (if flipY then h-1-i/w else i/w)*w + (if flipX then w-1-i%w else i%w)

def orbit (h w : ℕ) (xs : Layout) : Finset Layout :=
  {xs, xs.map (fun t => t.image (reflect h w true false)),
       xs.map (fun t => t.image (reflect h w false true)),
       xs.map (fun t => t.image (reflect h w true true))}

def count (n : ℕ) : ℕ :=
  let h := (n+1)/2
  let w := if n%2 = 1 then n else n+1
  ((layouts h w n).image (orbit h w)).card

theorem main : ∀ n : ℕ, 1 ≤ n → n%2 = 1 → count (n+1) = 4 * count n := by
  sorry

end OMA.S_oeis_a394981
