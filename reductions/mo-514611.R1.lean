import OMAStatements.S_mo_514611
import Mathlib

/-!
# Reduction of MathOverflow 514611: the Galois group of `x(x-1)⋯(x-p+1) + 1`

Classical slice, not progress on the question. `H1` is the irreducibility of
`f_p = x(x-1)⋯(x-p+1) + 1` over `ℚ` for every prime `p`, i.e. the transitivity of its Galois
group: modulo `p` the product is `x^p - x`, and the Artin-Schreier polynomial `x^p - x + 1` is
irreducible over `𝔽_p` (a root `α` satisfies `α^(p^k) = α - k`, so it lies in `𝔽_(p^d)` only
when `p ∣ d`); a monic integer polynomial irreducible modulo `p` is irreducible over `ℤ`, and by
Gauss's lemma over `ℚ`.

`H2` is the open core: for the irreducible `f_p`, the Galois group is all of `S_p`.
-/

namespace OMA.R_mo_514611_R1

open Polynomial

def H1 : Prop := ∀ p : ℕ, p.Prime → Irreducible (OMA.S_mo_514611.f p)

def H2 : Prop := ∀ p : ℕ, p.Prime → Irreducible (OMA.S_mo_514611.f p) →
  Nonempty ((OMA.S_mo_514611.f p).Gal ≃* Equiv.Perm (Fin p))

theorem main : H1 → H2 → type_of% @OMA.S_mo_514611.main :=
  fun h1 h2 p hp => h2 p hp (h1 p hp)

end OMA.R_mo_514611_R1
