import OMAReductions.R_BusyBeaver_BB_4_R1

/-! Reduce the four-state upper bound to two canonical first transitions. -/
-- Credit: @Halldon

namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

-- Relabel the first noninitial state as 1 and reflect a leftward first move.
theorem orient_first (M : Machine (Fin 2) (Fin 4)) (q : Fin 4) (a : Fin 2) (d : Dir)
    (hq : q ≠ 0) (first : M 0 0 = some (some q, Stmt.write a d)) :
    ∃ N : Machine (Fin 2) (Fin 4), N 0 0 = some (some 1, Stmt.write a Dir.right) ∧
      ∀ n, N.HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  let e := Equiv.swap q (1 : Fin 4)
  have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hq) (by decide)
  have heInv : e.symm 0 = 0 := e.symm_apply_eq.mpr he0.symm
  have heq : e q = 1 := Equiv.swap_apply_left _ _
  let mirror := match d with
    | .left => true
    | .right => false
  let turn (direction : Dir) := if mirror then
    match direction with
    | .left => Dir.right
    | .right => Dir.left
    else direction
  let N : Machine (Fin 2) (Fin 4) := fun s b => (M (e.symm s) b).map fun (s', action) =>
    (s'.map e, Stmt.write action.symbol (turn action.dir))
  let image (c : Cfg (Fin 2) (Fin 4)) : Cfg (Fin 2) (Fin 4) :=
    ⟨c.q.map e, if mirror then ⟨c.tape.head, c.tape.right, c.tape.left⟩ else c.tape⟩
  have step (c : Cfg (Fin 2) (Fin 4)) : N.step (image c) = (M.step c).map image := by
    obtain ⟨s, ⟨b, l, r⟩⟩ := c
    cases s with
    | none => rfl
    | some s =>
      cases d <;>
        simp only [Machine.step, image, mirror, Option.map_some, N, Equiv.symm_apply_apply,
          Bool.false_eq_true, if_false, if_true]
      all_goals
        cases ht : M s b with
        | none => rfl
        | some entry =>
          obtain ⟨t, z, direction⟩ := entry
          cases direction <;> rfl
  have start : image (Machine.init []) = Machine.init [] := by
    cases d <;> simpa [image, Machine.init, Tape.mk₁, Tape.mk₂, Tape.mk'] using he0
  have trace (n : ℕ) : N.multiStep (image (Machine.init [])) n =
      (M.multiStep (Machine.init []) n).map image := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases he : M.multiStep (Machine.init []) n with
      | none => rfl
      | some c => exact step c
  refine ⟨N, ?_, fun n => ?_⟩
  · cases d <;> simp [N, turn, mirror, heInv, first, heq]
  · unfold Machine.HaltsAfter
    conv_lhs => rw [← start, trace]
    exact Option.map_eq_none_iff

-- A self-transition from the blank start state keeps seeing fresh blank cells.
theorem self_never_halts (M : Machine (Fin 2) (Fin 4)) (a : Fin 2) (d : Dir)
    (first : M 0 0 = some (some 0, Stmt.write a d)) : ¬ M.IsHalting := by
  let blank := ListBlank.mk ([] : List (Fin 2))
  have trace (n : ℕ) : ∃ t : Tape (Fin 2),
      M.multiStep (Machine.init []) n = some ⟨some 0, t⟩ ∧ t.head = 0 ∧
        (match d with | .left => t.left | .right => t.right) = blank := by
    induction n with
    | zero =>
      refine ⟨Tape.mk₁ [], rfl, rfl, ?_⟩
      cases d <;> rfl
    | succ n ih =>
      obtain ⟨t, ht, ha, hs⟩ := ih
      refine ⟨(t.write a).move d, ?_, ?_, ?_⟩
      · simp [Machine.multiStep_succ, ht, Machine.step, ha, first]
      · cases d <;> simp [Tape.write, Tape.move, hs, blank]
      · cases d <;> simp [Tape.write, Tape.move, hs, blank]
  intro halts
  obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨t, ht, _⟩ := trace (n + 1)
  rw [Machine.HaltsAfter, ht] at hn
  contradiction

theorem stops_immediately (M : Machine (Fin 2) (Fin 4))
    (h : M 0 0 = none ∨ ∃ action, M 0 0 = some (none, action)) :
    M.HaltsAfter (Machine.init []) 107 := by
  have h2 : M.multiStep (Machine.init []) 2 = none := by
    change M.multiStep (Machine.init []) (1 + 1) = none
    rw [Machine.multiStep_succ, Machine.multiStep_one]
    have hi : M.step (Machine.init []) = (M 0 0).map
        (fun (q, a) => (⟨q, ((Tape.mk₁ []).write a.symbol).move a.dir⟩ : Cfg (Fin 2) (Fin 4))) := by
      change (M 0 0).map _ = _
      cases M 0 0 <;> rfl
    rcases h with h | ⟨action, h⟩ <;> rw [hi, h] <;> rfl
  exact Machine.multiStep_eq_none_mono h2 (by decide)

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1.H2 := by
  intro h1 h2 M halts k hk
  have bound : M.HaltsAfter (Machine.init []) 107 := by
    cases h : M 0 0 with
    | none => exact stops_immediately M (Or.inl h)
    | some cmd =>
      obtain ⟨q, a, d⟩ := cmd
      cases q with
      | none => exact stops_immediately M (Or.inr ⟨_, h⟩)
      | some q =>
        by_cases hq : q = 0
        · subst q
          exact (self_never_halts M a d h halts).elim
        · obtain ⟨N, hN, timing⟩ := orient_first M q a d hq h
          obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
          have haltsN := (Machine.isHalting_iff_exists_haltsAt N).mpr ⟨n, (timing n).mpr hn⟩
          apply (timing 107).mp
          fin_cases a
          · exact h1 N hN haltsN
          · exact h2 N hN haltsN
  have hle : M.haltingNumber ≤ (107 : ℕ) := sInf_le ⟨107, bound, rfl⟩
  rw [hk] at hle
  exact_mod_cast hle

end OMA.R_BusyBeaver_BB_4_R1_H2_R1
