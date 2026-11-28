import Mathlib

namespace OMA.S_wp_unknotting_problem

open Turing

/-- A signed Artin word on n + 1 strands. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

abbrev Braid := Σ n : ℕ, Word n

/-- The braid relations and the moves generating isotopy of oriented closures. -/
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

/-- A self-delimiting unary encoding of a natural number. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- The strand count minus one comes first, followed by the crossing indices and signs. -/
def encode {n : ℕ} (w : Word n) : List Bool :=
  encodeNat n ++ w.flatMap (fun c => encodeNat c.1.val ++ [c.2])

abbrev Alphabet (s : ℕ) : Fin (s + 1) → Type := fun _ => Bool

abbrev Program (s l q : ℕ) :=
  Fin (l + 1) → TM2.Stmt (Alphabet s) (Fin (l + 1)) (Fin (q + 1))

/-- Execute t transitions, leaving a halted configuration unchanged. -/
def run {s l q : ℕ} (machine : Program s l q) (input : List Bool) (t : ℕ) :
    TM2.Cfg (Alphabet s) (Fin (l + 1)) (Fin (q + 1)) :=
  Nat.iterate (fun c => (TM2.step machine c).getD c) t (TM2.init 0 input)

/-- Can unknot recognition be performed in deterministic polynomial time? -/
theorem main :
    ∃ (s l q C d : ℕ) (machine : Program s l q), 0 < C ∧
      ∀ (n : ℕ) (w : Word n), ∃ (t : ℕ) (answer : Bool),
        t ≤ C * ((encode w).length + 1) ^ d ∧
        let result := run machine (encode w) t
        result.l = none ∧ result.stk 0 = [answer] ∧
          (answer = true ↔ Relation.EqvGen MarkovMove ⟨n, w⟩ ⟨0, []⟩) := by
  sorry

end OMA.S_wp_unknotting_problem
