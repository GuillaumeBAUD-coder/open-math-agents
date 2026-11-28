import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The leading coefficient of Guo's subword complexity polynomial
Source: https://oeis.org/A341761
Credit: @NOELOO6

A window selects its last and first positions. Its word contains every
letter from first to last. The conjecture concerns the unique polynomial
whose value on an alphabet of size q is the sum of the numbers of distinct
nonempty contiguous subwords over all words of the given length.
-/

namespace OMA.S_oeis_a341761
open Finset Polynomial
variable {n : ℕ} {α : Type*}
noncomputable section

abbrev Window (n : ℕ) := (last : Fin n) × Fin (last.val+1)

def subword (w : Fin n → α) (p : Window n) : List α :=
  w ⟨p.2.val,by have := p.1.isLt; have := p.2.isLt; omega⟩ ::
    List.ofFn (fun j : Fin (p.1.val-p.2.val) =>
      w ⟨p.2.val+j.val+1,by have := p.1.isLt; have := p.2.isLt; have := j.isLt; omega⟩)

noncomputable def complexity (w : Fin n → α) : ℕ := by
  classical
  exact (univ.image (subword w)).card

def total (n q : ℕ) : ℕ := ∑ w : Fin n → Fin q, complexity w

theorem main : ∀ n : ℕ,
    (∃ p : ℤ[X], ∀ q : ℕ, p.eval (q:ℤ) = total n q) ∧
    ∀ p : ℤ[X], (∀ q : ℕ, p.eval (q:ℤ) = total n q) →
      p.coeff n = (n*(n+1)/2 : ℕ) := by
  sorry

end
end OMA.S_oeis_a341761
