import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1

-- Reduction BusyBeaver.BB_4.R2.H1.R1.H4.R1 of step BusyBeaver.BB_4.R2.H1.R1.H4
-- Credit: @anthoctz

/-! Split of step H4 of `R_BusyBeaver_BB_4_R2_H1_R1` (A0 = 0RB, B0 = (q, 1, L)) into four
verified enumerations: B0 back to state 0, then by the instruction read at step 2 when B0 moves
to state 2 (or, symmetrically, 3). -/

namespace OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1
open Turing Turing.BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  M 1 0 = some (some 0, Stmt.write 1 Dir.left) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (M 1 0 = some (some 2, Stmt.write 1 Dir.left) ∧ (M 2 0 = some (some 3, Stmt.write 1 Dir.right) ∨ M 2 0 = some (some 3, Stmt.write 1 Dir.left)) ∨
    M 1 0 = some (some 3, Stmt.write 1 Dir.left) ∧ (M 3 0 = some (some 2, Stmt.write 1 Dir.right) ∨ M 3 0 = some (some 2, Stmt.write 1 Dir.left))) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H3 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (M 1 0 = some (some 2, Stmt.write 1 Dir.left) ∧ (M 2 0 = some (some 0, Stmt.write 1 Dir.right) ∨ M 2 0 = some (some 0, Stmt.write 1 Dir.left) ∨ M 2 0 = some (some 1, Stmt.write 1 Dir.right)) ∨
    M 1 0 = some (some 3, Stmt.write 1 Dir.left) ∧ (M 3 0 = some (some 0, Stmt.write 1 Dir.right) ∨ M 3 0 = some (some 0, Stmt.write 1 Dir.left) ∨ M 3 0 = some (some 1, Stmt.write 1 Dir.right))) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H4 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q : Fin 4, M 1 0 = some (some q, Stmt.write 1 Dir.left)) ∧
    ¬ M 1 0 = some (some 0, Stmt.write 1 Dir.left) ∧
    ¬ (M 1 0 = some (some 2, Stmt.write 1 Dir.left) ∧ (M 2 0 = some (some 3, Stmt.write 1 Dir.right) ∨ M 2 0 = some (some 3, Stmt.write 1 Dir.left)) ∨
    M 1 0 = some (some 3, Stmt.write 1 Dir.left) ∧ (M 3 0 = some (some 2, Stmt.write 1 Dir.right) ∨ M 3 0 = some (some 2, Stmt.write 1 Dir.left))) ∧
    ¬ (M 1 0 = some (some 2, Stmt.write 1 Dir.left) ∧ (M 2 0 = some (some 0, Stmt.write 1 Dir.right) ∨ M 2 0 = some (some 0, Stmt.write 1 Dir.left) ∨ M 2 0 = some (some 1, Stmt.write 1 Dir.right)) ∨
    M 1 0 = some (some 3, Stmt.write 1 Dir.left) ∧ (M 3 0 = some (some 0, Stmt.write 1 Dir.right) ∨ M 3 0 = some (some 0, Stmt.write 1 Dir.left) ∨ M 3 0 = some (some 1, Stmt.write 1 Dir.right))) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

theorem main : H1 → H2 → H3 → H4 → OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := by
  intro h1 h2 h3 h4 M hA0 hB0
  by_cases c1 : M 1 0 = some (some 0, Stmt.write 1 Dir.left)
  · exact h1 M hA0 c1
  by_cases c2 : (M 1 0 = some (some 2, Stmt.write 1 Dir.left) ∧ (M 2 0 = some (some 3, Stmt.write 1 Dir.right) ∨ M 2 0 = some (some 3, Stmt.write 1 Dir.left)) ∨
    M 1 0 = some (some 3, Stmt.write 1 Dir.left) ∧ (M 3 0 = some (some 2, Stmt.write 1 Dir.right) ∨ M 3 0 = some (some 2, Stmt.write 1 Dir.left)))
  · exact h2 M hA0 c2
  by_cases c3 : (M 1 0 = some (some 2, Stmt.write 1 Dir.left) ∧ (M 2 0 = some (some 0, Stmt.write 1 Dir.right) ∨ M 2 0 = some (some 0, Stmt.write 1 Dir.left) ∨ M 2 0 = some (some 1, Stmt.write 1 Dir.right)) ∨
    M 1 0 = some (some 3, Stmt.write 1 Dir.left) ∧ (M 3 0 = some (some 0, Stmt.write 1 Dir.right) ∨ M 3 0 = some (some 0, Stmt.write 1 Dir.left) ∨ M 3 0 = some (some 1, Stmt.write 1 Dir.right)))
  · exact h3 M hA0 c3
  exact h4 M hA0 ⟨hB0, c1, c2, c3⟩

end OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1
