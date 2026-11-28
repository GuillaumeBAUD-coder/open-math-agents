import Mathlib

namespace OMA.S_wpc_jones_unknot

open scoped BigOperators

/-- A braid on n + 1 strands. A true sign denotes a positive crossing. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

abbrev Braid := Σ n : ℕ, Word n

/-- Generating relations for isotopy of oriented braid closures. -/
inductive MarkovMove : Braid → Braid → Prop
  | cancel (n : ℕ) (p q : Word n) (i : Fin n) (s : Bool) :
      MarkovMove ⟨n, p ++ [(i, s), (i, !s)] ++ q⟩ ⟨n, p ++ q⟩
  | commute (n : ℕ) (p q : Word n) (i j : Fin n) (s t : Bool)
      (far : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
      MarkovMove ⟨n, p ++ [(i, s), (j, t)] ++ q⟩
        ⟨n, p ++ [(j, t), (i, s)] ++ q⟩
  | braidRelation (n : ℕ) (p q : Word n) (i j : Fin n) (adjacent : i.val + 1 = j.val) :
      MarkovMove ⟨n, p ++ [(i, true), (j, true), (i, true)] ++ q⟩
        ⟨n, p ++ [(j, true), (i, true), (j, true)] ++ q⟩
  | rotate (n : ℕ) (w : Word n) (c : Fin n × Bool) :
      MarkovMove ⟨n, c :: w⟩ ⟨n, w ++ [c]⟩
  | stabilize (n : ℕ) (w : Word n) (s : Bool) :
      MarkovMove ⟨n, w⟩
        ⟨n + 1, w.map (fun c => (c.1.castSucc, c.2)) ++ [(Fin.last n, s)]⟩

/-- The closure is a knot exactly when the strand permutation has one orbit. -/
def closesToKnot {n : ℕ} (w : Word n) : Prop :=
  let σ := (w.map (fun c => Equiv.swap c.1.castSucc c.1.succ)).prod
  ∀ i j : Fin (n + 1), ∃ k : ℤ, (σ ^ k) i = j

abbrev StateVertex {n : ℕ} (w : Word n) := Fin (w.length + 1) × Fin (n + 1)

/-- At a crossing the strands either go straight through or form a cup and cap.
At the outer boundary the braid is closed by joining matching strand positions. -/
def stateArc {n : ℕ} (w : Word n) (cupCap : Fin w.length → Bool)
    (a b : StateVertex w) : Prop :=
  (a.1.val = 0 ∧ b.1.val = w.length ∧ a.2 = b.2) ∨
  ∃ k : Fin w.length,
    let i := (w.get k).1.val
    let straight := a.1.val = k.val ∧ b.1.val = k.val + 1 ∧ a.2 = b.2
    if cupCap k then
      (straight ∧ a.2.val ≠ i ∧ a.2.val ≠ i + 1) ∨
      (a.1.val = k.val ∧ b.1.val = k.val ∧ a.2.val = i ∧ b.2.val = i + 1) ∨
      (a.1.val = k.val + 1 ∧ b.1.val = k.val + 1 ∧ a.2.val = i ∧ b.2.val = i + 1)
    else straight

/-- Each connected component of the state graph is one bracket circle. -/
def stateGraph {n : ℕ} (w : Word n) (cupCap : Fin w.length → Bool) :
    SimpleGraph (StateVertex w) where
  Adj a b := a ≠ b ∧ (stateArc w cupCap a b ∨ stateArc w cupCap b a)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

/-- The Kauffman bracket of a closed braid, with the one-circle value equal to one. -/
noncomputable def bracket {n : ℕ} (w : Word n) : LaurentPolynomial ℤ :=
  ∑ s : Fin w.length → Bool,
    LaurentPolynomial.T (∑ k : Fin w.length, if s k = (w.get k).2 then -1 else 1) *
      (-LaurentPolynomial.T 2 - LaurentPolynomial.T (-2)) ^
        (Nat.card (stateGraph w s).ConnectedComponent - 1)

/-- The Jones polynomial after the standard substitution t = A to the power minus four. -/
noncomputable def jones {n : ℕ} (w : Word n) : LaurentPolynomial ℤ :=
  let writhe : ℤ := ∑ k : Fin w.length, if (w.get k).2 then 1 else -1
  let scale : ℤ := if Even writhe then 1 else -1
  LaurentPolynomial.C scale * LaurentPolynomial.T (-3 * writhe) * bracket w

/-- Does the Jones polynomial detect the unknot? -/
theorem main :
    ∀ (n : ℕ) (w : Word n), closesToKnot w → jones w = 1 →
      Relation.EqvGen MarkovMove ⟨n, w⟩ ⟨0, []⟩ := by
  sorry

end OMA.S_wpc_jones_unknot
