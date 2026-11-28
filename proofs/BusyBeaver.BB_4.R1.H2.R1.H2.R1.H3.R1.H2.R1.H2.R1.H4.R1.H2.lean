import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1_H4_R1

/-! The transition checker and automaton certificates come from @hyprspacecoyote’s
proof (#4739), as merged and optimized by @ubuwaits (#5662). The freezing argument is adapted
from @henry10101001’s merged BusyBeaver.BB_4.R2 reduction. This proof certifies
the shorter 50 cutoff and handles both forms of a halt instruction. -/

namespace OMA.BB4Bound106

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Key := State × Symbol
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move
  deriving DecidableEq

def Table.empty : Table := ⟨none, none, none, none, none, none, none, none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _, _ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq, Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1), ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position) (m : Move) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0, _ => []
  | k + 1, [] => 0 :: takePad k []
  | k + 1, x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad, List.foldr_cons, List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad, List.foldr_cons, List.drop_succ_cons]
      rw [ih xs, ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0, q, a, near, rs => some (q, a, near, rs)
  | k + 1, q, a, near, rs =>
    match tb.get q a with
    | none => none
    | some m =>
      if m.left then
        match near with
        | [] => none
        | a' :: near' => runGuardedLeft tb k m.state a' near' (push m.write rs)
      else
        runGuardedLeft tb k m.state (symHead rs) (m.write :: near) rs.tail

def checkGuardedLeft (tb : Table) (p : ℕ) (q : State) (a : Symbol)
    (near rs : List Symbol) : Bool :=
  match runGuardedLeft tb p q a near rs with
  | none => false
  | some (q', a', near', rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q', a', near', rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q', ⟨a', near'.foldr ListBlank.cons tail, ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | true =>
        simp only [hd, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, (x :: xs).foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
              some ⟨some m.state, ⟨x, xs.foldr ListBlank.cons tail, ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
            some ⟨some m.state, ⟨symHead rs, (m.write :: near).foldr ListBlank.cons tail, ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q', a', near', ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q', ⟨a', ListBlank.mk ls', near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht, Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip, hd, Bool.not_false, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, (x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state, ⟨x, ListBlank.mk (push m.write ls), xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state, ⟨symHead ls, ListBlank.mk ls.tail, (m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q, ⟨a, near.foldr ListBlank.cons tail', ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', rs'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hrs⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', ls'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hls⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedRight_sound hm p q' a' near ls' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

structure HistItem where
  step : ℕ
  pos : ℕ
  c : Position

def findRepAux (tb : Table) (cur : HistItem) (minp maxp : ℕ) : List HistItem → Bool
  | [] => false
  | hi :: rest =>
    let minp' := if Nat.ble minp hi.pos then minp else hi.pos
    let maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    let ok :=
      if Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val then
        let p := cur.step - hi.step
        let leftOk :=
          if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
            let dL := hi.pos - minp'
            let near := takePad dL hi.c.ls
            if listEq (takePad dL cur.c.ls) near then
              checkGuardedLeft tb p hi.c.state hi.c.head near hi.c.rs
            else false
          else false
        if leftOk then true
        else if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
          let dR := maxp' - hi.pos
          let near := takePad dR hi.c.rs
          if listEq (takePad dR cur.c.rs) near then
            checkGuardedLeft tb.flip p hi.c.state hi.c.head near hi.c.ls
          else false
        else false
      else false
    if ok then true else findRepAux tb cur minp' maxp' rest

def findRep (tb : Table) (cur : HistItem) (prev : List HistItem) : Bool :=
  findRepAux tb cur 1000 0 prev

def HistValid (M : Machine4) (hist : List HistItem) : Prop :=
  ∀ h ∈ hist, h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg Symbol State)
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')

theorem findRepAux_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem}
    (hcur : cur.step ≤ 107) (hvalid : HistValid M prev)
    {minp maxp : ℕ} (h : findRepAux tb cur minp maxp prev = true) : False := by
  induction prev generalizing minp maxp with
  | nil => simp [findRepAux] at h
  | cons hi rest ih =>
    unfold findRepAux at h
    dsimp only at h
    set minp' := if Nat.ble minp hi.pos then minp else hi.pos
    set maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    by_cases hcond : (Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val) = true
    · simp only [hcond, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
      have ⟨hstep_hi, hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
      have hp_pos : 0 < cur.step - hi.step := by omega
      have hp_le : hi.step + (cur.step - hi.step) ≤ 107 := by omega
      by_cases hleft : (if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
          if listEq (takePad (hi.pos - minp') cur.c.ls) (takePad (hi.pos - minp') hi.c.ls) then
            checkGuardedLeft tb (cur.step - hi.step) hi.c.state hi.c.head (takePad (hi.pos - minp') hi.c.ls) hi.c.rs
          else false else false) = true
      · split at hleft
        · split at hleft
          · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head true
              (takePad (hi.pos - minp') hi.c.ls) (ListBlank.mk hi.c.rs)
              hp_pos hp_le
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')), by
                simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)), by
                  simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright, Bool.false_eq_true, ↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h

-- ============================================================
-- FAR (Finite Automata Reduction) certificate verifier
-- ============================================================

inductive CanStop (tb : Table) : Position → Prop
  | missing {c} : tb.get c.state c.head = none → CanStop tb c
  | move {c m} : tb.get c.state c.head = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Table} {c : Position} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip, h]
    · rwa [← flip_move]

theorem cannot_stop_run {M : Machine4} {tb : Table}
    (hm : Matches M tb) (c : Position) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get c.state c.head with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move hm c m h, Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  fin_cases a
  · cases xs with
    | nil => exact D.blank.symm
    | cons x xs => rfl
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges >>> ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) &&&
      ((1 <<< (4 * cert.dfa.size + 1)) - 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := (val >>> 1) &&& 31
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := (val >>> 6) / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val.testBit 0, ⟨extra, (val >>> 6) % dfaBase⟩, payload >>> width, payload &&& (initialBase - 1)⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

-- A single inclusion check verifies every target in an automaton edge row.
theorem included_bit {x y : ℕ} (h : Nat.beq (x &&& y) x = true) (k : ℕ)
    (bit : x.testBit k = true) : y.testBit k = true := by
  have e := congrArg (fun n : ℕ => n.testBit k) (Nat.eq_of_beq_eq_true h)
  simpa [Nat.testBit_and, bit] using e

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        Nat.beq (row &&& cert.blankReach) row
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              Nat.beq (swRow &&& pRow) swRow
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, by simp [edge_none], .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      exact ih rfl (included_bit ht (nodeId cert q) he)
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    exact Reads.push (show cert.edge (some (c.state, cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd, Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, symHead_eq_headI, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push, symHead_eq_headI] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq, if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state, cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he', if_true] at h''
      exact Reads.push (included_bit h'' (nodeId cert t) hf) ht

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, startPos, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

-- ============================================================
-- Symmetry: swapping states 2 and 3
-- ============================================================

def swap23 : Equiv.Perm State := Equiv.swap (2 : State) (3 : State)

theorem swap23_0 : swap23 0 = 0 := by decide
theorem swap23_1 : swap23 1 = 1 := by decide
theorem swap23_2 : swap23 2 = 3 := by decide
theorem swap23_3 : swap23 3 = 2 := by decide
theorem swap23_inv (q : State) : swap23.symm q = swap23 q := by fin_cases q <;> decide

def reindex23 (M : Machine4) : Machine4 :=
  fun q a => (M (swap23 q) a).map fun (s, b) => (s.map swap23, b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23, c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step, mapCfg23, Option.map_some, reindex23]
    have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
    rw [hinv]
    cases M q t.head with
    | none => rfl
    | some entry => rfl

theorem reindex23_multi (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    (reindex23 M).multiStep (mapCfg23 c) k = (M.multiStep c k).map mapCfg23 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23, Machine.init, swap23_0]


def sp0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩,
   some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩⟩

def sp1Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, some ⟨1, 1, false⟩,
   none, some ⟨3, 0, true⟩, some ⟨0, 1, false⟩, some ⟨3, 1, true⟩⟩

def m0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, some ⟨3, 1, false⟩,
   some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, some ⟨0, 1, false⟩, none⟩

def tblOfList (entries : List ℕ) : Machine4 := fun q a =>
  let v := entries[2*q.val+a.val]?.getD 16
  if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
    Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))

theorem eq_sp0_of_matches {M : Machine4} (hm : Matches M sp0Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,3,3,8,15,10,16,1] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 3 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 0 = none at hMmiss; rw [hm 2 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hm 2 0 _ rfl
  · exact hm 2 1 _ rfl
  · exact hMmiss
  · exact hm 3 1 _ rfl

theorem eq_sp1_of_matches {M : Machine4} (hm : Matches M sp1Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,4,11,6,16,13,2,15] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 2 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 0 = none at hMmiss; rw [hm 3 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hMmiss
  · exact hm 2 1 _ rfl
  · exact hm 3 0 _ rfl
  · exact hm 3 1 _ rfl

def runPos (tb : Table) : ℕ → Position → Option Position
  | 0, c => some c
  | k + 1, c =>
    match tb.get c.state c.head with
    | none => none
    | some m => runPos tb k (c.move m)

theorem runPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (k : ℕ) (c : Position) {c' : Position} (h : runPos tb k c = some c') :
    M.multiStep c.view k = some c'.view := by
  induction k generalizing c with
  | zero =>
    simp only [runPos, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    simp only [runPos] at h
    cases ht : tb.get c.state c.head with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      rw [multi_succ_front, step_move hm c m ht, Option.bind_some]
      exact ih (c.move m) h

theorem run_add (M : Machine4) (x : Cfg Symbol State) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem m0_not_halting {M : Machine4} (hm : Matches M m0Table) (hHalts : M.IsHalting) : False := by
  have h85 : ∃ c85, runPos m0Table 85 startPos = some c85 ∧
      checkGuardedLeft m0Table.flip 29 c85.state c85.head [] c85.ls = true := by
    refine ⟨(runPos m0Table 85 startPos).getD startPos, ?_, ?_⟩ <;> decide +kernel
  obtain ⟨c85, hrun, hcyc⟩ := h85
  have hM85 : M.multiStep (Machine.init []) 85 = some c85.view := runPos_sound hm 85 startPos hrun
  let cfg (tail : ListBlank Symbol) : Cfg Symbol State :=
    ⟨some c85.state, ⟨c85.head, ListBlank.mk c85.ls, tail⟩⟩
  have hEnter : ∃ tail, M.multiStep (Machine.init []) 85 = some (cfg tail) :=
    ⟨ListBlank.mk c85.rs, hM85⟩
  have hStep : ∀ tail, ∃ tail', M.multiStep (cfg tail) 29 = some (cfg tail') := by
    intro tail
    simpa [cfg] using checkGuardedRight_sound hm hcyc tail
  have hRec (m : ℕ) : ∃ tail, M.multiStep (Machine.init []) (85 + 29 * m) = some (cfg tail) := by
    induction m with
    | zero => simpa using hEnter
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := hStep t
      refine ⟨t', ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (85 + 29 * m) 29, ht]
      exact ht'
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
  obtain ⟨t, ht⟩ := hRec (k + 1)
  have hnone := Machine.multiStep_eq_none_mono hk (by omega : k + 1 ≤ 85 + 29 * (k + 1))
  rw [ht] at hnone
  contradiction

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 50 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting ∧
  (M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1]) ∧
  (M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15])

theorem reindex23_invol (M : Machine4) : reindex23 (reindex23 M) = M := by
  funext q a
  have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
  simp only [reindex23, hinv]
  cases M q a with
  | none => rfl
  | some p =>
    rcases p with ⟨s, b⟩
    cases s with
    | none => rfl
    | some s =>
      have hs : swap23 (swap23 s) = s := by fin_cases s <;> decide
      simp [hs]

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts, ⟨hsp0, hsp0'⟩, ⟨hsp1, hsp1'⟩⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨hsp0', by rwa [reindex23_invol]⟩, ⟨hsp1', by rwa [reindex23_invol]⟩⟩
  · refine ⟨swap23 q0, t0, ?_⟩
    rw [← mapCfg23_init, reindex23_multi, hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q', z, h⟩
    · left; simp [reindex23, h]
    · right; exact ⟨swap23 q', z, by simp [reindex23, h]⟩
  · exact ⟨swap23 qm, am, by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23, this, hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
    have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23, cfgM, cfg, this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail, ht⟩ := hEnter
      rw [← mapCfg23_init, reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi, Option.map_some, Option.some.injEq] at ht
        refine ⟨tail, ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht
        rcases ht with ⟨hq', ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht']
    · intro tail
      obtain ⟨tail', ht'⟩ := hCycle tail
      rw [← hmap tail, reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp, Option.map_some, Option.some.injEq] at ht'
        refine ⟨tail', ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq', ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht'']
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m, tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get, h01.1, h01.2.1] at hget
    · fin_cases a <;> simp [Table.get, h01.2.2.1, h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23, hsq, hm q a m hget, Move.command, Option.map_some, hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist, h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle, hrun⟩ := hv h hh
  refine ⟨hle, ?_⟩
  rw [← mapCfg23_init, reindex23_multi, hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23, Position.view, hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q, a) := by
  ext ⟨q', a'⟩
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e, e]

def moves12 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q, a, d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed, moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed, moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem usesOnly01_set {tb : Table} (h01 : UsesOnly01 tb) {q : State} {a : Symbol} {m : Move}
    (hq : q = 0 ∨ q = 1) (hm : m.state = 0 ∨ m.state = 1) :
    UsesOnly01 (tb.set q a m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q', a') = (q, a)
    · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

def limitedStep (stop : ℕ) (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if Nat.beq nstep stop &&
          findRep tb ncur nprev then
        .rep
      else
        limitedStep stop tb rem ncur nprev

theorem limitedStep_sound (stop : ℕ) {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match limitedStep stop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [limitedStep]
  | succ rem ih =>
    unfold limitedStep
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : (Nat.beq (cur.step + 1) stop && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01


def stopAt (tag : ℕ) : ℕ :=
  match tag with
  | 1 => 6 | 2 => 12 | 3 => 24 | 4 => 48 | 5 => 107 | _ => 0

def advisedStep (tag : ℕ) (tb : Table) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : StepResult :=
  if Nat.beq tag 6 then .done else limitedStep (stopAt tag) tb rem cur prev

theorem advisedStep_sound (tag : ℕ) {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match advisedStep tag tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  by_cases h : Nat.beq tag 6 = true
  · simp [advisedStep, h]
  · simpa only [advisedStep, if_neg h] using limitedStep_sound (stopAt tag) hm hG hsum hv h01

def guidedTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [] => none
  | holesLeft + 1, used2, tb, rem, cur, prev, code :: certs =>
    match advisedStep (code % 8) tb rem cur prev with
    | .rep => some ((code >>> 3) :: certs)
    | .done =>
      match certs with
      | [] => none
      | v :: rest =>
        if Nat.beq v 0 then
          if tb == sp0Table || tb == sp1Table || tb == m0Table then some ((code >>> 3) :: rest) else none
        else if checkCertificate tb v then some ((code >>> 3) :: rest) else none
    | .missing q a rem' cur' prev' =>
      if rem' ≤ 57 then none
      else if Nat.beq holesLeft 0 then some ((code >>> 3) :: certs)
      else
        checkMoves (fun m rest =>
          guidedTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) ((code >>> 3) :: certs)

theorem guidedTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : guidedTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [guidedTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    cases a with
    | nil => simp [guidedTree] at hCheck
    | cons code a =>
      unfold guidedTree at hCheck
      have hstep := advisedStep_sound (code % 8) hm hG hsum hv hu
      cases hsl : advisedStep (code % 8) tb rem cur prev with
      | rep => rw [hsl] at hstep; exact hstep
      | done =>
        simp only [hsl] at hCheck
        cases a with
        | nil => simp at hCheck
        | cons v rest =>
          simp only at hCheck
          by_cases hv0 : Nat.beq v 0 = true
          · simp only [hv0, ↓reduceIte] at hCheck
            split at hCheck
            · rename_i hsp
              simp only [Bool.or_eq_true, beq_iff_eq] at hsp
              rcases hsp with (rfl | rfl) | rfl
              · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
              · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
              · exact m0_not_halting hm hG.2.2.2.2.1
            · simp at hCheck
          · simp only [hv0, Bool.false_eq_true, ↓reduceIte] at hCheck
            split at hCheck
            · rename_i hcert
              have hns := certificate_sound hcert
              obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
              exact cannot_stop_run hm startPos hns (k + 1) hk
            · simp at hCheck
      | missing q a rem' cur' prev' =>
        simp only [hsl] at hCheck hstep
        by_cases hlast : rem' ≤ 57
        · simp [hlast] at hCheck
        simp only [hlast, if_false] at hCheck
        obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
        have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
        -- This branch is reached strictly before step 50.
        have hM_def : ∃ q' z, M q a = some (some q', z) := by
          rcases hG.2.1 q a with hMnone | hMsome
          · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
              rw [Machine.multiStep_succ, hcur'_run]
              simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
            have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 50)
            obtain ⟨q0, t0, hrun107⟩ := hG.1
            rw [h107] at hrun107
            contradiction
          · exact hMsome
        obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
        split at hCheck
        · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
          rename_i h0
          have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
          have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
          have hcard1 : (holes tb).card = 1 :=
            le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
          obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
          have hqm_mem : (qm, am) ∈ holes tb := by
            simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
            cases hget : tb.get qm am with
            | none => rfl
            | some m =>
              have := hm qm am m hget
              rw [hMmiss] at this
              simp [Move.command] at this
          have heq_key : (qm, am) = (q, a) := by
            have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
            have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
            rw [← hEq, Finset.mem_singleton] at hqm_mem
            exact hqm_mem
          rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
          rw [hMmiss] at hMqa
          contradiction
        · -- Branch on movesAllowed used2
          let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
          have hm_cmd : M q a = m.command := by
            cases d <;> simpa [m, Move.command] using hMqa
          have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
          have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          by_cases hswap : used2 = false ∧ q' = 3
          · rcases hswap with ⟨hu2, rfl⟩
            have ⟨h01, hprev01⟩ := hu' hu2
            let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
            have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
            obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
            have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
            have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
            have hM2qa : (reindex23 M) q a = m2.command := by
              cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
            have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
              rw [holes_set, Finset.card_erase_of_mem hmem_hole]
              omega
            exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
              (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
              (histValid_reindex23 hv' hprev01) (by simp [m2])
          · have hmem_m : m ∈ movesAllowed used2 :=
              mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
            obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
            refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
            intro hnext_u2
            simp only [Bool.or_eq_false_iff] at hnext_u2
            have ⟨h01, hprev01⟩ := hu' hnext_u2.1
            have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
            have hm01 : m.state = 0 ∨ m.state = 1 := by
              have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
              have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
              fin_cases q' <;> simp_all [m]
            exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4, GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
    False

private theorem mk_good_ne_sp1 (M : Machine4) (h : M 1 0 ≠ some (some 2, Stmt.write 1 Dir.left))
    (h2 : M 1 0 ≠ some (some 3, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h2 ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,4,11,6,16,13,2,15] 1 0 = some (some 2, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs3 : s = 3 := by revert hs; fin_cases s <;> decide
      subst hs3; subst hz; rfl

private theorem mk_good_ne_sp0 (M : Machine4) (h : M 1 0 ≠ some (some 0, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,3,3,8,15,10,16,1] 1 0 = some (some 0, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs0 : s = 0 := by revert hs; fin_cases s <;> decide
      subst hs0; subst hz; rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24e488209302441241249a0804d049269a08249209449249260201249a69248248048000040000049208209a49209049a4020d241249a68249a4826a0000cda4982de8e38f360301029349049248201441249a6820828824d249249049021200001000040a4d26904934902a26006036f340b20a41249208049049a49208269a01401001040201249a692482482ca249a00049e0920024924db49808241249a69a0904824d26d241248009249a4800036f3cdb6c02da09a6d86036c04d679b00059b0a495c90411c8c268369a0004b20924d341049241a89b6820906024934d24904900800000820000924104134124020800006020824904d04904900c069a00048009d11b718004cc20904924820124104d04d841849049a092680002ac22800924936d260a4120934934902208c36f38f300a20a41208049240049a0024920820d060060309241249868249248200209a4924d808261a48269a09048249269241248009249248208209a4da5984930c30da4d25982d68006936a26124800924924802904820124906104d00184da49048008249249361a0800026820824120924924902820826936a660a2ca20ac220804d241079b00059b4960904824030b2616cd860452410200209a4da59000061c40049009048249b6b2610c000d24f4cc30c30da4e2590cda498288, 2923059026737561881309746369607612760256872985410, 1132583016536257, 1128184898717761, 1128184898717761, 1128665935054913, 1128185100044353, 
    1128185100044353, 1027663288900614986408985390262045554256270899010, 566266213962688, 73671716770240, 73687152268224, 144058043995072, 
    566266213962688, 566266213962688, 1130383991247041, 1128665935122625, 1132582949492929, 1130383991247041, 
    1136981268769601, 1136981268769601, 283958550204864, 283958550204864, 354123283435968, 283958550204864, 
    847200561402816, 1136981268769601, 1136981268769601, 72852317671872, 283958550204864, 73671649661376, 
    283816816153024, 283816816153024, 144040460947904]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x269a0804924104db0004db48309248240209a6134d04064da0c208209a4920100004104030000924824b28826104000d64c00c208209a4e2010cc30006c3cc609a4c30000e349209049200019b4d30935020836d040249041049a4d00800804000b209201041009240200001200040248040248049008000009348209241041349241a68000041248261040049349029209a68201248041a5000006134c24920904820806f30000db6c30820826924804064c00000104824920924a20a04820828938804000000100800026184134db60309b7000c00f36c2c124800064d34c24930820105120924104136924104800004d04824804104024104120000104160000100900124000000100004024904104924904d20001934d30984100124d24134800024924826904104da49049049049009209a41041369240209a0804920104000004030030924824020826104d04034d808208209a4925900004134004a80924824828a26104000d04f288208209a4e2790000c236f3ce809a0004137244900907104026d008008008000009201009241009440200200300040200000048049000049079b4c001009040009340001241b6d00000025934da00000069a49341001048249349040201869a4d248201001b4934902180904000954030020c0003cc36004120c04900826820124804100000100000024920900820804134100106060820828924a340301051000340249209209a8984100034136de08208289389b4000000137b38c26206234db7030831104987134024044100184020000104964d34c04024904024100804124d35120000000100124000124104d04804024100024000004904134100000924d36924104120924924900004127934d30004836d24d24000104924924824000d34d36924000020926da4980004130004130000824a389ac000000000000000026826da48000048200000300009a08389200001b6db6db6c20004d24db49a0000826db69a6000136db6d26c000269a6da4980006c34db49b00012679b99e61849241009248209340049249241249048041248249209049249041041249249a0000824904124124904924d248249001249249041041349b4b30922936c00924d24820a268201249841e6c00166db6c249209008209851361819370408208269249d4000186100c0002492092ca2098410003593d340c30c36db8de6308000dbcde70269a4164d04024920824d00124924904924120904100924c34134924104104d24900800030d241049049241259341309a4004934924104104d26d34c2492493003493692082c9a08049241059b0005934960924824020b261249040249b08208209a4925900004144004900924824926b26104000d24f3c8208209a4da590c9a49849561568001c682000410080112018000000012435612080014b4060000000049000077379b7a50800904954dc68200241369b71200009a6db69a61b410, 1128184898717761, 1128184898717761, 1128185100044353, 1461551814199050063162363173862378288981691597635, 2923192831719176615430003279112310561573561185090, 1128184970025153, 
    1128184898717761, 1128184898717761, 1128185100044353, 1128185100044353, 23014456880272322966934778201244376397464482626, 91279338312640, 
    163849253295040, 581659376751552, 581659376751552, 1128666136855105, 581659376358336, 1128253685371073, 
    1128253685371073, 1128666002231489, 1128184970088641, 1128185037199553, 1128185037199553, 1128253618262209, 
    1128253819588801, 163849253295040, 163849253295040, 581659376751552, 1128184970088641, 1128184902981825, 
    1128184902981825, 1128184970088641, 1128185112705985, 1128665935122625, 1128253618194497, 1128665935054913, 
    1128185175747393, 2923059026716252532891576003668296306131812296515, 1128665935258433, 1501503365767945621989761726681307534140041129036580497413667840410145483033766639513220421855818461523524395536512446956438524562423287501135917765839484504657167208983096030445300165355422273819046893991067039745440641454143792312762995591897752862447379456746988553, 11462626758536582302583909586791404600526373699, 2923371238321452602275315853772966510340150932290, 
    531501997402235371604538329849018963974333629708809442753374553223559320445409024892059013950907502661, 1128185175747393, 1128253953946561, 531501997402235371604538329849018963974333629708809442753374553223559301192965533925820837409181552709, 1128184978619329, 1128185175747393, 
    1128185108638529, 182866459800280701675939303819557821249100985154, 15015033664604734385304966506489959399580110773953330295600086866903864083866133108599072806387146212049676744485611025026121041177544918919333576183636804355915796642970539752525234420828523977933341196619934081471551228217639135762042987961378366151467009249877513, 146239484596672, 3957316619184925684297189135165343748734485785569124676029570219791433971881285648085489929242555540140270568007551389034031562785650291705819342222639351911062452182223642182, 73671649661376, 
    132877511029752925051748174825186803139028445692011376668635412537999079269691137052392711834656039172, 581659376751552, 365421404790046575088861852680708487679710593859, 146239484596672, 75870740025792, 146239484203456, 
    146239484203456, 1128665935528513, 1128666136855105, 163849253295040]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249251249a49200049269a49208209249249269241249a69249248259bcda4d31802924120804d241049208249249201200000001201249a68249248029249349249248001249a69a68208249249249249029b4db69269b40a29048201349040a49209049249020a49249249208049249269a0821926d3c9441261249a692492482c9249a49e00009229a69a6db6d86020824924da49008241269a4920126c3c945926124800924924804d379b59c0000926a369a49a0000924d349241041a69b6926820824934d24924906db69a49b00009b71e71e7000020800000000820924104124124024800000024824904d04924900924924924820124924924da49049a49269a6c000228a28209249369240a49209249249020a59259349c00019669249b6d0602d9b6e3db300009a49a00041349c59219061249b6d668028a41208049241049200249249201200000001201249868249248200209a49a51008261a4924820924824926924124800924924831830da4d25982d24902904820124904124920904da49048008249249341a48000248208249209249249029b40069269b40a28a208, 1132582949492929, 1133063985830081, 1130452710723777, 1130383992164545, 1130452710723777, 286156768940480, 
    145419280585152, 286156768940480, 567648925520832, 286156768940480, 567915481928640, 1130865028501697, 
    286449363588032, 567915481928640, 426761113309632, 286156768940480, 426761113309632, 286156768940480, 
    1128185100044353, 1128185100044353, 145419280585152, 286156768940480, 286156768940480, 286156768940480, 
    162814179168961, 286156768940480, 286156768940480]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24db4d64920000938d34da4d0c02cdb6e3cde00009a4db4d349240009269a0924d20000004064120121a480079ec000100104d84c0c804925934926300924d24d251c4c64d449a59b4904924924920000924924926104124934d24c34c24934d249a4902936db6db6db0c00830000824820920104920d240200000001b4c24804004824900924db6db6db6180b64db6f3890002696cdc6f64c36826924824938a26030000900030c20980006c34d30124964d24d0c024934934939130924926926924124934d34980024924924d84104924d359361809a4924926924134924924d84026d349a49a4905124d34d363009a49269269241b6c30db6db6c24804124024904924934934920100100100124024db4d34d30000938d34db490602cdb6e36e600009a4920004204d06d3030905da69a48108104db4930c04924924920100934924934104124924934804024934d249049059349349640001239b69249640001b6da6db6c04036de6da5130c000068060049a0104824904d24024d87920804024900124904900937164964c30024a34d37938130b36db6d34c00026924840108944e34c34b0413793d530124d24924904104924924924924164d24d24d800049249041209249249049248249249240259359349300009269249b490402d9b49adb300009249a00041349c59219061249b4964804946d45964800025a34d36d46300b46db8e4900002692480010d9649e4c44204136d47730136db6db6d86184db6db6db6db6166db6db7180004d249861b0db6db6d86db6c36db6db60208209a4d20100c00004d04d209208269b88240300000301308208209a4d275000061b4d34c208208269349b4104104d36d368208209a4d25984c30c36db6dd6126820006a28dc6100800000820800100004920924020000000324820000004824904104124926a20004824126904124104d24f248249001249a4902924920906d06980800824d24d24920120c36db6c34020306d26900000030db6db0d00804938c00924db6824184c349a6da6020100a369b680c1c0f66db6d84d24124926d20104104d24d0c804000124824904904134936920000000100924104104d048208001209049a41041041359600208248249269241041049249b4824104134d36f2092492003493492080, 1130383991247041, 3957316733435741279695094842938213246030297183398556868321880162344348709122765445991438030010671167740061116195955953666299513519953436211247240708567523686864530757270720070, 3957317617958184597672899128210835318733529284583726970371325177309938065765155744860584514291484461426826578489517421186915115795680661265044183667405405949615101025208716870, 1130383991640257, 1130383926237377, 1130383926302913, 
    2923371238321452602275315851411786646617933755202, 1461685619180664797282003557181428715679348163395, 1130384203197377, 4169565881362078942603269316840097260200449565506583527042533717540875511726429561578240290051919497943838912486411626048174488163270001776130453693895462706485232312776651334, 1130383926237377, 435694511067584, 
    1130452710658241, 1130452710723777, 1130452710723777, 1130452710723777, 1130452710854849, 290554815451584, 
    74921548976321, 581109621461952, 172104583484352, 308439596143552, 1130452710723777, 1130383992164545, 
    1130452710723777, 290554815451584, 149817327096256, 290554815451584, 572046972031936, 290554815451584, 
    308439596143552, 581109621461952, 290554815451584, 2923192831699196581207897358526031384789878125379, 1131002601567169, 1131002601173953, 
    290554815451584, 172104583484352, 172104583484352, 308439596143552, 2923371238321452602275354537185584326676494431042, 426761113309632, 
    426761113309632, 426761113309632, 290554815451584, 290554815451584, 1130384135891905, 1130384135961537, 
    1130384135961537, 1130384136289217, 2923192831676765773212650191598267659641990501187, 149817327096256, 290554815451584, 145221573677249, 
    435566064702400, 567434038743233, 290555083887040, 145281841631680, 145281841631680, 435557340549568, 
    593904731689920, 290554815451584, 589639694947264, 290554815451584, 581109621461952, 581109621461952, 
    567434458186433, 290555083887040, 3957316619645614456670703133741263909701702003214454025535025642061467173125526469753343276291302619358266188478510362446948737417543988739765949797373487029826035532330651206, 708171946545857, 145221993124545, 145221993124545, 
    567434458186433, 531566878008451469248290970559449168515760066662976755054472260129319668484030187147086003014590493572, 149817327096256, 290554815451584, 290554815451584, 11596431761252815292394006238909503455738532675, 
    308439596143552]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24922924d34d24d808049249269a08209349a4d261241249a6924824804000000004904924920820920d36d36d360201249a69248248069a49269b69a6a20000924924d341042289b6f26820824934d249049008069a00009a092492410413432a9c6c20804024934d24904900924d32d24db49360200a4da69349049021000000001240a4da69349049021269ac924924934904106924d24924124000d249a6800024924904104904924d2492412402c9249acb24a2ca200009249259341041a69e6b36c20824964d249049008048200009a09249241041242249b8830c04024964d249049008a4924924920804924924920820926d369349241269a69249a4822924920024924d24900004124924920d06c36934924100000924924802924926d248203269a6924800024934db4da49049a89a69a61009a49a69a6800022ca2800926d349240a00209349249020a4924800804104920820824920926d300300201269a6824824800024b26c36c021808249b0f340001869a6924800036da4da49800041249a492090482492cd241000009a4924800024b2cda49849029249240201343269ac800124824934da4c049049a89a6180920da4b2480002c822800d359379340a002092493490200192db369240a208, 2923728051605758559929314933870742417626711995202, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957406596879099790595470146, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957404383269810945449276226, 
    290555619971520, 290555619971520, 290555620233664, 290555620233664, 2923728051604429326853024096770637962380425835330, 2923728051605758559929334276757643509464395952962, 
    2923728051603764710314869006777135611050905844546, 2923371258736026921429193020158236526728280876867, 2923728070659203411399535038590333965637616486211, 290555083887040, 79449387438528, 149817327096256, 
    290554815451584, 290554815451584, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 
    290555620757952, 290839088600000, 290839088075712, 853797363520448]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2494292493492492018092492492c104124924934c24826e249b4b049049049241009a0924924100124124934934c040249a49a48049009249349a4924924b041049a4924924124104104d258000249249040049069249249241240269b49a6a24a2c9d000092692593c1041a6db6db6c208249b4da4984900804820000a20926924100134224db8c30c040249b4da4984900914924924924180926924926104124934924924826e24924b049029249641049249249a0100824920924124904924924824800024b249009249a69249841049249a4924124136db4d36db0c049a4904104d2492a8040209248249069248249249240209a0924920004100004030000924824826826104d04db4c00020004806004d2080033adb6f38c20006db6dbce30986d87b66f00020824924926d00004934db4d209248249a69a61040209a49b6804924924100a20926924100924124934824804026e24924804902830104926124824104924924a301008249209241249049a49a4820000024b24900004b45984930920db6dbd0301c6338db6dbcd86d871c6db01813311c7b3ac0004d03cc30dbd9b8dec1b8db0dbcdb6d86000decf38dba0001b6f399b6c30006f36dc6db01249a49040249049249249241241249040209248249049a482492492400012492592482480, 3957286475397161215507271467758464678282920511704727498450596225747433248283068596185371699013391854873011680474393894354066091711414048032258511877057077388486965974225180230, 1134782178199617, 531566814648506648577238044788322869782431627444936453682351466636153651288060060779961551739649315140, 1134782048246721, 1134781976873025, 1134782245308481, 
    1134782178199617, 1134782115355585, 2923371239680027450535923395121142647858904961603, 1134781981137857, 1134782048246721, 1134782383799233, 
    2923728051603224709694219430450706072007199769411, 290555619971520, 290555619971520, 590189718410176, 290555620233664, 2923719732379918226590664828984032122686451073859, 
    2923728051603224709694219279334986466289359520579, 290555619971520, 1134781976873025, 1134782178199617, 531566814648491542382975396215709529811340286128523574468508095834682218610479466127616345303077146948, 535719680387928928508263142553344117905758614438823067324213593147744725932992870710078442010956702788, 
    4217746345661154897263197952045289589276152563663330699591193316812080037710027886911626353305625668, 537796239962114842500772471133007928991003666964535805698589647601600549965970226302406424082178548804, 33284258116097804024988001097606118023719077030435534339193063922667440404733838537696065762399265860, 1134781976873025, 1134782245308481, 1134782245514049, 
    1134713457082433, 531566814648491542382975399221116431783425397472412753114851174322809799513357274961440313220991603012, 162887181013952, 154219534356928, 149817327096256, 290554815451584, 
    535719680387928928508262249518143837791014998772725706683028673939927403060909686024192205328790758468, 145689729307072, 145689729307072, 145689729307072]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x228a29a49249a4924d808069a49249a08209349a4d261241249e69248248008040000041069a4920820921146f3c9040201249e69248248049269a69a69a69a00009a69a69a68208269a08000009209a6a268208248209249a29269249360200a49269349049020201000001040a49269249049020a49b8da4d21802d36f369369a61249b69249248249a69a49200069a69a49a0820944a249269241249b69249248249ac9a4da1804924820804d241008200249249201000000009241248008249248029349269a49248001a49269249249029a69a69368600a29268201349040a49269049249020a4980006f269029a6184030b341a68008269248248269a08051008269a08248209048249260201248009248248009800040040049200209a4920934824020d2412480082492482498000cda49849029249269263341249249a48201341b6db6d8603cc249249249049020240001001000a49209049349021200003369240a208, 185542907881716514983538333309578664332188726082, 299351712993728, 981449509505353238871313570943092176245494822015250209404988843581513618466218028789892439123878579809184623934098679028081147322955664436856728207906921311678116421308458661666498766573933700848086566929369723974833493282212757000291371566481768977052729864249837512, 159433623736768, 89084140327872, 159433623736768, 
    145221573677249, 145221573677249, 299350908473792, 299351445344704, 162814179168961, 369516446224832, 
    299351712993728, 299351712993728, 439955252842944]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1452292496492492492010092492492c1041249249248248279a7b64b049049249001008209249241001241249249248040249a49a4804900924924924924924b041049a49a4924124124d04925800024924904004904924924924124024934d34d301809a6a36a2cdd00009249a4d24d60000924d349b48060249a09a6f000040040000001219d60079bc000104924984004802936d379259248249249249240009249249261041249249249248249a4b24b249049359349343009649241009248209241049269241249248041248249a4804b24900934924924924984104924924924924134934924d04024934d040249208249041249a49049449649309209249241249240249b0000d34d20b3ac001b6f38c209209a49200000041040000009249249268261049059258000209209a4da0006db0006c3cc30b24920804926104930004db4d209249240209a61249040249b0802934830827924824924924100a209249241009241249249248040249a4b2480490492410092080092410412c9241249248041a48261a0004b24904b400019e49309209369369a580682492b9bb9b4c0a02c98090490580082413416c960120000000c300001a693c83000684cf4cf06180c04d34d64900120124924924904024904924924924124124934904004824904104b249049a49a412492412480002592482493496490092080, 79449387438528, 75870740025792, 75870740025792, 362919376458176, 290555619971520, 290555619971520, 
    290555620233664, 290555620233664, 4153081087726013885702245672149462584160435651081710015101107350678394278549906459400339478532138779635872324045196186797966625519267032865624376304983622028480718923288770118, 88528420603969, 88528017955521, 88528420603969, 
    137871296185277590929123653149795973942921910054426473123275364300250292407580530529559731306050501, 14272531393547573756878262903182275079827620675, 290555619971520, 290555620233664, 308439863661504, 75870740025792, 
    75870740025792, 23014456880272322966934778201244376397464482626, 75870740025792, 75870740025792, 79449387438528, 23014456539989956041034883063490866391518559042, 
    535719680387928928508263128814341137462336024532963996468164481709518578945588176144112556277596595268, 146239484203456, 88528420603969, 88528420603969, 581659376751552, 581659376751552, 
    46028913678132195818436124369258700730615739202, 148440587833792, 146239485120960, 158415729988289, 149817327096256, 154082229621184, 
    149817327096256, 154082363838912, 149817327096256, 158416266875585, 158415729988289, 158416132657857, 
    158416266875585, 145277412446656, 290554815451584, 580628593525313, 286014900801984, 286014900801984, 
    286014900801984, 294819717976512, 294819852194240, 294819852194240, 286014900801984, 290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

theorem no_repeat {M : Machine (Fin 2) (Fin 4)} (halts : M.IsHalting)
    {i p : ℕ} (hp : 0 < p) {α : Type} (cfg : α → Cfg (Fin 2) (Fin 4))
    (entered : ∃ v, M.multiStep (Machine.init []) i = some (cfg v))
    (cycle : ∀ v, ∃ w, M.multiStep (cfg v) p = some (cfg w)) : False := by
  have recur (m : ℕ) : ∃ v, M.multiStep (Machine.init []) (i + p * m) = some (cfg v) := by
    induction m with
    | zero => simpa using entered
    | succ m ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := cycle v
      refine ⟨w, ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (i + p*m) p, hv]
      exact hw
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨v, hv⟩ := recur (k + 1)
  have hle : k + 1 ≤ i + p * (k + 1) := by
    have := Nat.mul_le_mul_right (k+1) hp
    omega
  have hnone := Machine.multiStep_eq_none_mono hk hle
  rw [hv] at hnone
  contradiction

set_option maxRecDepth 10000 in
private theorem freeze {M : Machine4} (halts : M.IsHalting)
    (late : ¬ M.HaltsAfter (Machine.init []) 50) :
    ∃ P : Machine4, P.IsHalting ∧
      (∃ q t, P.multiStep (Machine.init []) 50 = some ⟨some q,t⟩) ∧
      (∀ q a, P q a = none ∨ ∃ r z, P q a = some (some r,z)) ∧
      (∃ q a, P q a = none) ∧
      (∀ i ≤ 50, P.multiStep (Machine.init []) i = M.multiStep (Machine.init []) i) ∧
      (∀ i < 50, ∀ q t, M.multiStep (Machine.init []) i = some ⟨some q,t⟩ →
        P q t.head = M q t.head) := by
  classical
  let start : Cfg Symbol State := Machine.init []
  have alive (i : ℕ) (hi : i ≤ 51) : M.multiStep start i ≠ none :=
    fun h => late (Machine.multiStep_eq_none_mono h hi)
  let seen (q : State) (a : Symbol) : Prop := ∃ i < 50, ∃ t : Tape Symbol,
    M.multiStep start i = some ⟨some q,t⟩ ∧ t.head = a
  let P : Machine4 := fun q a => if seen q a then M q a else none
  have used {q a} (h : seen q a) : ∃ r z, M q a = some (some r,z) := by
    obtain ⟨i, hi, t, ht, rfl⟩ := h
    have ha := alive (i+1+1) (by omega)
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ht] at ha
    cases hc : M q t.head with
    | none => simp [Machine.step, hc] at ha
    | some entry =>
      obtain ⟨s,z⟩ := entry
      cases s with
      | none => simp [Machine.step, hc] at ha
      | some s => exact ⟨s,z,rfl⟩
  have same (i : ℕ) (hi : i < 50) (q : State) (t : Tape Symbol)
      (ht : M.multiStep start i = some ⟨some q,t⟩) : P q t.head = M q t.head := by
    exact if_pos ⟨i, hi, t, ht, rfl⟩
  have agree (i : ℕ) (hi : i ≤ 50) : P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih (by omega)]
      cases h : M.multiStep start i with
      | none => rfl
      | some c =>
        obtain ⟨q,t⟩ := c
        cases q with
        | none => rfl
        | some q => simp [Machine.step, same i (by omega) q t h]
  have restrictRun (i : ℕ) : P.multiStep start i = none ∨
      P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => exact Or.inr rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ]
      rcases ih with hi | hi
      · simp [hi]
      · rw [hi]
        cases hc : M.multiStep start i with
        | none => exact Or.inl rfl
        | some c =>
          obtain ⟨q,t⟩ := c
          cases q with
          | none => exact Or.inl rfl
          | some q => by_cases h : seen q t.head <;> simp [Machine.step,P,h]
  obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  have haltP : P.IsHalting := by
    apply (Machine.isHalting_iff_exists_haltsAt P).mpr
    refine ⟨k,?_⟩
    rcases restrictRun (k+1) with h | h
    · exact h
    · exact h.trans hk
  obtain ⟨q,t,ht⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) 50 late
  refine ⟨P, haltP, ⟨q,t,(agree 50 (by decide)).trans ht⟩, ?_, ?_, agree, same⟩
  · intro q a
    by_cases h : seen q a
    · exact Or.inr (by simpa [P,h] using used h)
    · exact Or.inl (by simp [P,h])
  · by_contra! all
    apply Machine.not_isHalting_of_forall_isSome P _ haltP
    intro q a
    by_cases h : seen q a
    · simpa [P,h] using used h
    · exact (all q a (by simp [P,h])).elim

private theorem prefixMatches {M : Machine4} {r : State} {w : Symbol} {left : Bool}
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 3, Stmt.write 1 .left))
    (h3 : M 3 0 = some (some r, Stmt.write w (if left then .left else .right))) :
    Matches M ⟨some ⟨1,1,false⟩, none, some ⟨2,0,false⟩, none,
      some ⟨3,1,true⟩, none, some ⟨r,w,left⟩, none⟩ := by
  intro q a m h
  fin_cases q <;> fin_cases a <;> simp [Table.get] at h
  all_goals subst m; first | exact h0 | exact h1 | exact h2 | (cases left <;> exact h3)

private theorem run_prefix {M : Machine4} {r : State} {w : Symbol} {left : Bool}
    (hm : Matches M ⟨some ⟨1,1,false⟩, none, some ⟨2,0,false⟩, none,
      some ⟨3,1,true⟩, none, some ⟨r,w,left⟩, none⟩) :
    HistValid M [⟨3,129,⟨3,[1],0,[1]⟩⟩, ⟨2,130,⟨2,[0,1],0,[]⟩⟩,
      ⟨1,129,⟨1,[1],0,[]⟩⟩, ⟨0,128,⟨0,[],0,[]⟩⟩] := by
  have h0 : M.multiStep (Machine.init []) 0 = some startPos.view := rfl
  have h1 : M.multiStep (Machine.init []) 1 = some (Position.view ⟨1,[1],0,[]⟩) := by
    rw [Machine.multiStep_one]
    exact step_move hm startPos ⟨1,1,false⟩ rfl
  have h2 : M.multiStep (Machine.init []) 2 = some (Position.view ⟨2,[0,1],0,[]⟩) := by
    change M.multiStep (Machine.init []) (1+1) = _
    rw [Machine.multiStep_succ, h1]
    exact step_move hm ⟨1,[1],0,[]⟩ ⟨2,0,false⟩ rfl
  have h3 : M.multiStep (Machine.init []) 3 = some (Position.view ⟨3,[1],0,[1]⟩) := by
    change M.multiStep (Machine.init []) (2+1) = _
    rw [Machine.multiStep_succ,h2]
    exact step_move hm ⟨2,[0,1],0,[]⟩ ⟨3,1,true⟩ rfl
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact ⟨by decide,h3⟩
  · exact ⟨by decide,h2⟩
  · exact ⟨by decide,h1⟩
  · exact ⟨by decide,h0⟩

private theorem branch_bound (M : Machine4) (r : State) (left : Bool)
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 3, Stmt.write 1 .left))
    (h3 : M 3 0 = some (some r, Stmt.write 1 (if left then .left else .right)))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 50 := by
  by_contra late
  obtain ⟨P, haltP, alive, form, missing, _, same⟩ := freeze halts late
  have hv := run_prefix (prefixMatches h0 h1 h2 h3)
  have s0 := (hv ⟨0,128,⟨0,[],0,[]⟩⟩ (by simp)).2
  have s1 := (hv ⟨1,129,⟨1,[1],0,[]⟩⟩ (by simp)).2
  have s2 := (hv ⟨2,130,⟨2,[0,1],0,[]⟩⟩ (by simp)).2
  have s3 := (hv ⟨3,129,⟨3,[1],0,[1]⟩⟩ (by simp)).2
  have claim0 : P 0 0 = _ := (same 0 (by decide) 0 _ s0).trans h0
  have claim1 : P 1 0 = _ := (same 1 (by decide) 1 _ s1).trans h1
  have claim2 : P 2 0 = _ := (same 2 (by decide) 2 _ s2).trans h2
  have claim3 : P 3 0 = _ := (same 3 (by decide) 3 _ s3).trans h3
  have hm := prefixMatches claim0 claim1 claim2 claim3
  have noLoop : NoRepeatHyp P := by
    intro i p q a side near fixed hp _ cfg entry cycle
    exact no_repeat haltP hp cfg entry cycle
  have good : GoodMachine P := ⟨alive,form,missing,noLoop,haltP,
    mk_good_ne_sp0 P (by simp [claim1]), mk_good_ne_sp1 P (by simp [claim1]) (by simp [claim1])⟩
  have af := run_prefix hm
  fin_cases r <;> cases left <;>
    first
    | exact tv_b8_15_2 P good hm rfl af (by simp)
    | exact tv_b8_15_3 P good hm rfl af (by simp)
    | exact tv_b8_15_6 P good hm rfl af (by simp)
    | exact tv_b8_15_7 P good hm rfl af (by simp)
    | exact tv_b8_15_10 P good hm rfl af (by simp)
    | exact tv_b8_15_11 P good hm rfl af (by simp)
    | exact tv_b8_15_14 P good hm rfl af (by simp)
    | exact tv_b8_15_15 P good hm rfl af (by simp)

end OMA.BB4Bound106

open Turing Turing.BusyBeaver in
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1_H4_R1.H2 := by
  intro M r left h0 h1 h2 h3 halts
  exact Machine.multiStep_eq_none_mono
    (OMA.BB4Bound106.branch_bound M r left h0 h1 h2 h3 halts) (by decide)
