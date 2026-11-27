import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1

/-!
Split write-0 residual H1 (`M 1 0` targets state 0 or 1) by the blank write/dir
out of state 1 — the same four branches as @ubuwaits `BusyBeaver.BB_4.R2.H1.R1`,
restricted to target states `{0,1}`.

Donors: @hyprspacecoyote R2.H1 / R2.H2.R1.H1, @ubuwaits R2.H1.R1.H1–H4.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H1_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q' : Fin 4, (q' = 0 ∨ q' = 1) ∧ M 1 0 = some (some q', Stmt.write 0 Dir.right)) →
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
  (∃ q' : Fin 4, (q' = 0 ∨ q' = 1) ∧ M 1 0 = some (some q', Stmt.write 0 Dir.left)) →
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
  (∃ q' : Fin 4, (q' = 0 ∨ q' = 1) ∧ M 1 0 = some (some q', Stmt.write 1 Dir.right)) →
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
  (∃ q' : Fin 4, (q' = 0 ∨ q' = 1) ∧ M 1 0 = some (some q', Stmt.write 1 Dir.left)) →
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

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1.H1 := by
  intro h0r h0l h1r h1l M hFirst hM10 hRun hUsed hForm hMissing hLoop hHalts
  obtain ⟨q', hq01, ⟨w, d⟩, hSecond⟩ := hM10
  fin_cases w
  · cases d with
    | right => exact h0r M hFirst ⟨q', hq01, hSecond⟩ hRun hUsed hForm hMissing hLoop hHalts
    | left => exact h0l M hFirst ⟨q', hq01, hSecond⟩ hRun hUsed hForm hMissing hLoop hHalts
  · cases d with
    | right => exact h1r M hFirst ⟨q', hq01, hSecond⟩ hRun hUsed hForm hMissing hLoop hHalts
    | left => exact h1l M hFirst ⟨q', hq01, hSecond⟩ hRun hUsed hForm hMissing hLoop hHalts

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H1_R1
