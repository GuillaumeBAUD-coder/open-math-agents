import Mathlib

/-!
# Caccetta-Häggkvist Conjecture

Source: https://www.openproblemgarden.org/op/caccetta_haggkvist_conjecture
Credit: @John-A-McMahon

Source statement (Open Problem Garden, Caccetta and Häggkvist): every simple digraph of order
`n` with minimum outdegree at least `r` has a cycle with length at most `⌈n / r⌉`.

Conventions. A simple digraph on `n` vertices is an irreflexive arc relation `Adj` on `Fin n`
(no loops; a relation has no parallel arcs; two opposite arcs, i.e. a directed 2-cycle, are
allowed, as is standard for this conjecture). `r ≥ 1`, since for `r = 0` the bound `⌈n / 0⌉ = 0`
is meaningless. The outdegree of `v` is the number of `w` with `Adj v w`. A (directed) cycle of
length `ℓ ≥ 2` is an injective `c : Fin ℓ → Fin n` with an arc from `c i` to `c (i + 1 mod ℓ)`
for every `i`. `⌈n / r⌉` is written `(n + r - 1) / r` in `ℕ`.
-/

namespace OMA.S_opg_caccetta_haggkvist_conjecture

/-- `Adj` has a directed cycle of length `ℓ`. -/
def HasDirectedCycleOfLength {n : ℕ} (Adj : Fin n → Fin n → Prop) (ℓ : ℕ) : Prop :=
  ∃ _ : 2 ≤ ℓ, ∃ c : Fin ℓ → Fin n, Function.Injective c ∧
    ∀ i : Fin ℓ, Adj (c i) (c ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩)

theorem main :
    ∀ (n r : ℕ) (Adj : Fin n → Fin n → Prop) [DecidableRel Adj], 1 ≤ r →
      (∀ v, ¬ Adj v v) →
      (∀ v, r ≤ (Finset.univ.filter (fun w => Adj v w)).card) →
      ∃ ℓ, ℓ ≤ (n + r - 1) / r ∧ HasDirectedCycleOfLength Adj ℓ := by
  sorry

end OMA.S_opg_caccetta_haggkvist_conjecture
