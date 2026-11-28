import Mathlib

/-!
# The additive basis conjecture

Source: https://www.openproblemgarden.org/op/the_additive_basis_conjecture
Credit: @joshuadc11

Jaeger–Linial–Payan–Tarsi Additive Basis Conjecture: for every prime `p`, there exists a constant
`c` (depending only on `p`) such that for every `n`, the multiset union of any `c` bases of the
vector space `(ZMod p)^n` is an additive basis (every vector in `(ZMod p)^n` is the sum of some
sub-multiset of the union).

## Encoding

* For a prime `p` (with `[Fact p.Prime]`), `(ℤ_p)^n` is `Fin n → ZMod p` over `ZMod p`.
* `c` bases of `(ZMod p)^n` are given as `B : Fin c → Module.Basis (Fin n) (ZMod p) (Fin n → ZMod p)`.
* A sub-multiset of the multiset union of these `c` bases corresponds to a subset
  `S : Finset (Fin c × Fin n)`, with sum `∑ x ∈ S, B x.1 x.2`.
* Saying the multiset union contains an additive basis is equivalent to saying it is an additive
  basis: every `v : Fin n → ZMod p` equals `∑ x ∈ S, B x.1 x.2` for some `S : Finset (Fin c × Fin n)`.
-/

namespace OMA.S_opg_the_additive_basis_conjecture

/-- For every prime `p`, there exists `c : ℕ` such that for every `n : ℕ` and any `c` bases of
`(ZMod p)^n`, every vector in `(ZMod p)^n` is a subset sum of their multiset union. -/
theorem main : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℕ, ∀ (n : ℕ)
    (B : Fin c → Module.Basis (Fin n) (ZMod p) (Fin n → ZMod p)),
    ∀ v : Fin n → ZMod p, ∃ S : Finset (Fin c × Fin n), (∑ x ∈ S, B x.1 x.2) = v := by
  sorry

end OMA.S_opg_the_additive_basis_conjecture
