import Mathlib

/-!
# A positive closed sum for the extended Stirling array

Source: Mikhail Kurkov, https://mathoverflow.net/questions/435104
Credit: @connoranderson.

The original recurrence uses division, so we define it over the rationals.
The proposed answer is a finite sum of nonnegative integer products.
A mask designates the one-bit positions at which the state is raised,
reading the word from the most significant end. Nat.bits stores the least
significant bit first, so positions larger than i are read before i.
-/
namespace OMA.S_mo_435104

def evenRow (v : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | k+2 => (k+2 : ℚ)*v (k+2) + v (k+1) -
      (evenRow v (k+1) + v (k+1))/(k+1 : ℚ)

def entries : ℕ → ℕ → ℚ :=
  Nat.binaryRec (motive := fun _ => ℕ → ℚ)
    (fun k => if k=1 ∨ k=2 then 1 else 0)
    (fun b _ v => if b then fun k => (k:ℚ)*v k + v (k-1) else evenRow v)

def marks {t : ℕ} (u : Fin t → Bool) : ℕ := ∑ i, (u i).toNat

def pathWeight {t : ℕ} (bits u : Fin t → Bool) : ℕ :=
  ∏ i : Fin t, if u i then (bits i).toNat else
    1 + ∑ j : Fin t, if i < j then (u j).toNat else 0

def wordSum (w : List Bool) (k : ℕ) : ℕ :=
  ∑ u : Fin w.length → Bool,
    if marks u+1=k then pathWeight w.get u else 0

def H (n k : ℕ) : ℕ := wordSum n.bits k

theorem main :
    (∀ (n k : ℕ), 0 < k →
      entries n k = ((k*H n k + H n (k-1) : ℕ) : ℚ)) ∧
    (∀ (r k : ℕ), 0 < k →
      entries (2^r-1) k = Nat.stirlingSecond (r+2) k) := by
  sorry
end OMA.S_mo_435104
