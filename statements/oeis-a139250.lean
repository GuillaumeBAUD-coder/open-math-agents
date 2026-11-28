import Mathlib

/-!
# Rectangular faces and hidden crosses in the toothpick sequence

Source: https://oeis.org/A139250 (OEIS Foundation, CC BY-SA 4.0).
The OEIS entry uses toothpicks of length two and starts vertically at stage one.
The central cross, hidden crosses, and four arms follow Omar E. Pol's diagrams:
http://www.polprimos.com/imagenespub/poltp684.jpg (separated pieces) and
http://www.polprimos.com/imagenespub/poltp685.jpg (growth directions).
Box coordinates refer to the lower left and upper right corners on the integer grid.
Credit: @connoranderson
-/

namespace OMA.S_oeis_a139250

open Finset

abbrev Pt := ℤ × ℤ
/-- Toothpicks are represented by center and orientation; true means horizontal. -/
abbrev Stick := Pt × Bool

def ends (u : Stick) : Finset Pt :=
  let (x,y) := u.1
  if u.2 then {(x-1,y),(x+1,y)} else {(x,y-1),(x,y+1)}

def occupied (u : Stick) : Finset Pt := insert u.1 (ends u)

/-- Add perpendicular toothpicks at all exposed ends simultaneously. -/
def next (s : Finset Stick) : Finset Stick :=
  s ∪ s.biUnion fun u =>
    ((ends u).filter fun p => ∀ v ∈ s.erase u, p ∉ occupied v).image fun p => (p,!u.2)

def stage : ℕ → Finset Stick
  | 0 => ∅
  | n+1 => if n=0 then {((0,0),false)} else next (stage n)

/-- A unit wall is encoded by its left or lower endpoint and its orientation. -/
def walls (s : Finset Stick) : Finset Stick :=
  s.biUnion fun u =>
    let (x,y) := u.1
    if u.2 then {((x-1,y),true),((x,y),true)}
    else {((x,y-1),false),((x,y),false)}

structure Box where
  x₀ : ℤ
  y₀ : ℤ
  x₁ : ℤ
  y₁ : ℤ
  deriving DecidableEq

def width (b : Box) : ℕ := (b.x₁-b.x₀).toNat
def height (b : Box) : ℕ := (b.y₁-b.y₀).toNat

def rim (b : Box) : Finset Stick :=
  ((range (width b)).biUnion fun i =>
    {((b.x₀+i,b.y₀),true),((b.x₀+i,b.y₁),true)}) ∪
  ((range (height b)).biUnion fun j =>
    {((b.x₀,b.y₀+j),false),((b.x₁,b.y₀+j),false)})

def interiorWalls (b : Box) : Finset Stick :=
  (((range (width b)) ×ˢ range (height b - 1)).image fun ij =>
    ((b.x₀+ij.1,b.y₀+ij.2+1),true)) ∪
  (((range (width b - 1)) ×ˢ range (height b)).image fun ij =>
    ((b.x₀+ij.1+1,b.y₀+ij.2),false))

/-- A rectangular face has every unit edge of its rim and no edge in its interior. -/
def face (n : ℕ) (b : Box) : Prop :=
  b.x₀ < b.x₁ ∧ b.y₀ < b.y₁ ∧ rim b ⊆ walls (stage n) ∧ Disjoint (interiorWalls b) (walls (stage n))

/-- The four arms of the central cross. Their successive rectangles have length
1,2,4,... in the growth direction and transverse width two. -/
def centralLayer (i : ℕ) : Finset Box :=
  let t : ℤ := 2^i
  {⟨-1,t,1,2*t⟩, ⟨-1,-2*t,1,-t⟩, ⟨t-1,-1,2*t-1,1⟩, ⟨1-2*t,-1,1-t,1⟩}

/-- One orientation of Pol's off-center cross. Its two narrow arms have width
one and its two broad arms have width two. At i=0 the four boxes form its nucleus. -/
def hiddenLayer (i : ℕ) : Finset Box :=
  let t : ℤ := 2^i
  {⟨2-2*t,0,2-t,1⟩, ⟨0,t,1,2*t⟩, ⟨0,1-2*t,2,1-t⟩, ⟨t,0,2*t,2⟩}

def central (s : ℕ) : Finset Box := (range s).biUnion centralLayer

/-- The eight symmetries of the square, followed by an integer translation. -/
def place (swap flipX flipY : Bool) (p : Pt) (b : Box) : Box :=
  let c : Box := if swap then ⟨b.y₀,b.x₀,b.y₁,b.x₁⟩ else b
  ⟨p.1 + (if flipX then -c.x₁ else c.x₀), p.2 + (if flipY then -c.y₁ else c.y₀),
   p.1 + (if flipX then -c.x₀ else c.x₁), p.2 + (if flipY then -c.y₀ else c.y₁)⟩

def IsHidden (s : ℕ) (g : Finset Box) : Prop :=
  ∃ u v w : Bool, ∃ p : Pt, g = ((range s).biUnion hiddenLayer).image (place u v w p)

/-- A decomposition groups each rectangular face exactly once, as in the
author's diagram separating the pieces. This distinguishes the nuclei of actual
crosses from four adjacent boxes that happen to have the shape of a nucleus. -/
def CrossDecomposition (k : ℕ) (groups : Finset (Finset Box)) : Prop :=
  central (k-1) ∈ groups ∧
  (∀ b, face (2^k) b ↔ ∃ g ∈ groups, b ∈ g) ∧
  (∀ g ∈ groups, ∀ h ∈ groups, g ≠ h → Disjoint g h) ∧
  (∀ g ∈ groups, ∃ s : ℕ, 0 < s ∧ g.card = 4*s ∧
    ((g = central (k-1) ∧ s = k-1) ∨ IsHidden s g))

theorem main :
    (∀ n b, face n b → (∃ u : ℕ, width b = 2^u) ∧ (∃ v : ℕ, height b = 2^v) ∧
      (∃ w : ℕ, width b * height b = 2^w) ∧ (width b ≤ 2 ∨ height b ≤ 2)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ groups : Finset (Finset Box), CrossDecomposition k groups ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ k-1 →
        (groups.filter fun g => g.card = 4*(k-m)).card = 4^(m-1)) ∧
      groups.card = (4^(k-1)-1)/3) := by
  sorry

end OMA.S_oeis_a139250
