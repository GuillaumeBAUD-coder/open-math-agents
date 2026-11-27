import OMAReductions.R_BusyBeaver_BB_4_R2_H2_R1

namespace OMA.BB4H2

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
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq_true_eq] at hcond
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
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

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
  let extra := val / 2 % 32
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 64 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 64 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
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
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
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
      have hn := allNodes ht q
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      simp [he0] at hn
      exact ih rfl hn
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
      have h''' := allNodes h'' t
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      simp [hf'] at h'''
      exact Reads.push h''' ht

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
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
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

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
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
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | holesLeft + 1, used2, tb, rem, cur, prev, certs =>
    match stepLoop tb rem cur prev with
    | .rep => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest =>
        if Nat.beq v 0 then
          if tb == sp0Table || tb == sp1Table || tb == m0Table then some rest else none
        else if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some certs
      else
        checkMoves (fun m rest =>
          checkTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) certs

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

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
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
      by_cases hrep : ((Nat.beq (cur.step + 1) 6 || Nat.beq (cur.step + 1) 12 || Nat.beq (cur.step + 1) 24 ||
          Nat.beq (cur.step + 1) 48 || Nat.beq (cur.step + 1) 107) && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01

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

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm hG hsum hv hu
    cases hsl : stepLoop tb rem cur prev with
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
      obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z, M q a = some (some q', z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ, hcur'_run]
            simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
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

theorem branch_one {tb : Table} {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    {q : State} {a : Symbol} {rem' : ℕ} {cur' : HistItem} {prev' : List HistItem}
    (hsl : stepLoop tb rem cur prev = .missing q a rem' cur' prev')
    (hChildren : ∀ m ∈ movesAllowed used2,
      TreeValid (tb.set q a m) (used2 || Nat.beq m.state.val 2) rem' cur' prev') :
    TreeValid tb used2 rem cur prev := by
  intro M hG hm hsum hv hu
  have hstep := stepLoop_sound hm hG hsum hv hu
  simp only [hsl] at hstep
  obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z, M q a = some (some q', z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ, hcur'_run]
        simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0, t0, hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m, Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2, rfl⟩
    have ⟨h01, hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01, hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩



def baseTable : Table := Table.empty.set 0 0 ⟨1, 1, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 1, false⟩⟩

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

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 1 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1, h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 1, false⟩ rfl
  refine ⟨hm0, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide, hrun1⟩
  · exact ⟨by decide, rfl⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1133048953444545, 2923371238321452602275315851411786646617933755202, 2923371260099524085215377513067761522251099288386]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 1161368023863744, 2928712984119627669801440515032256664395222889282, 1133048953444545, 106105095590336, 317217971900864, 
    317217971900864]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155221459392, 324403033980877405537562920820621316828870797855852538913597458270697488587353581220035361868144324, 1161155285356737, 1161155221459392, 1161164080026048, 371085815678611994235083854345649049513899341634, 
    1161370171150784, 1161368023863744, 1161368023863744, 1161368023732672, 1161368023863744, 2928712984114310737555736974291338717328503239490, 
    316943093993920, 316943093993920, 316943093993920, 583925464646046210032418948265169619527655341046170694675523275017317690177621596081293357927638532, 8369598326593329836429484193452297382501830087944009089720128567922461699263514684307006723843958276, 105839008944576, 
    176209900605888, 316943093993920, 316943093993920, 4217239466888111472080243969461200383654574453816508273986178501851004512023759369613101997419931140, 33283751484824633568462844139029446496669927355979208908471420316520490663848708748493503179927856644, 17127037657320480964811417562565105392572970818, 
    28545062755111125892160670739186208216717473602, 1461551814188457737005823497529518369191583889218, 145275260768449, 145275260768449, 1130849996116161, 2923728051645552963199333300356476754602122819394, 
    17127037667954345495909952439432220128023951170, 15121341268958217710875072373595407989066104045286341663380342275931580135751596557203035207858949121428643059895024514450649403163779305426711671458405530078426125824800343569627158820853426040850494511284886257573637303597827265071969004039538210767368249877512, 28545062765744990423259205616053322952168453954, 28545062765744990423259205616053322952168453954, 28545062765744990423259205616053322952168453954, 16609466995054676039264686756895757063880650068832622971274094502085954536302567317406283616532815556, 
    16610449074603487350192158912779425439564230646405489915487364804369025545991802916291647880297701060, 1461551814199091601536922032406385483927034869570, 145275260768449, 145275260768449, 145275260768449, 1130849995133121, 
    1130849995198657, 1130849995198657, 1130849995198657, 75318833451201, 145687577628865]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2923371258738394617511777935173078628837196051266]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161234880008640, 1161368023863744, 28545062745818983358373638187091580235313869634, 188397414118873100197553673337628427696516133698, 513258889805605223322046716863513927553819518280132834263281228172320860999911596055912701620997604789162605682976289732430875467064312609936858817387901635221197424638022, 3957316615499469982613701026949970134706107164370788607669008626706598596188174160956720691207835445835676495735436173408833829800461849296379635389416383700263823886555196999, 
    17127037652013426268709507324442742335620543298, 97053213336547940768836784797262728837371818818, 1161234880008640, 1161368023863744, 28545062745818983358373638187091580235313869634, 188397414118873100197553673337628427696516133698, 
    513258889805605223322046716863513927553819518280132834263281228172320860999911596055912701620997604789162605682976289732430875467064312609936858817387901635221197424638022, 469678024262996135954626474396049201884783220875215041054024621605583225016001527993514795343872487456337410769246176010095495290068320916796611552389373285131418640684049581264097599128241716526687154708043139109938991244113303636377729362677976272995976245997512, 17127037652013426268709507324442742335620543298, 97053213336547940768836784797262728837371818818, 457547438363072, 316943093993920, 
    1247177207726153154038098006463783627512013935540556657255957341792308789515530887164147822323305077106444814543144337664534432445601373800292744158009052914568042473597228498332232016099205100591132002347970619635020768845287971045613598277091314578401715288978575512370808464068486039296824623733615911617759429979852429486579668204240116108636468556611913406049787909100141194856168082024173730554763263307787636383861869959621288495660086336258626231393854654835659388212755817542960512741996828805180838604]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 1161368023863744, 2928723417169099951829284426158403243005788042050, 2923059026610039557868417108394340061549095551811, 2929080229092276441799548997650765616789883728706, 2923192831676724883718908784880608966556541798211, 
    2923371260099524085215377515428944763685921895234, 1161368023863744, 1161368023732672, 316943093993920, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164444803317065078691857111352826925133177765848226189623022983500158293775044885648381048902, 581094329041473, 
    581094329041473]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [736462597071981342345179509825147940046232400706, 5711778406529883243337093467006430218266129218, 736462597071981342345179509825147940046232400706, 736460511821621273943699801782668006681644938050, 572863283729344, 1135263481074624, 
    736462602516499213080194925239141658954523784002, 736462602516499213080194925239141658954523784002, 736462602516499213080194925239141658954523784002, 736462602516499213080194925239141658954523784002, 736462602516499213080194925239143910762927403842, 261549947706041557390176538361675074190761867923720792719370073773866664630419112222312143098359429, 
    1040117280306995750137338785863443481636722505730908627853379824183438394816862088810446707168495237, 581659376751552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105624522262593, 7729078731994588773169520666295190370093120183095540765374834179524720111209079132734956845828998767437522522968701847930303834604344418333858866518157924867386161229723719, 285984802024043109485611792222636670138114388802, 297402827121999908547499817888410059126394073922, 145825436029633, 163417622074049, 
    163417622074049, 150223490929601, 163417622074049, 736462602516499213080194927600327152197750010690, 567900462138049, 73673864188352, 
    565220398350913, 73673864188352, 567419421606593, 580613561139777, 183402028136003777047981896505496524284749689666]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [84682268545984, 150655113761728, 572863283729344, 163849253295040, 581659376751552, 163849253295040, 
    581659376751552, 145687443406913, 567419421606593, 581334286981683693713488187727256180800793599194341058564502924039835935637918586019986842972206354501, 16610449198353422912511803907944161699844673149109530320237866828533505728608717347251478182110375557, 80284222034880, 
    150655113761728, 572863283729344, 2923728051608344394892238318514072679255399035714, 2923728051608344334045009507559061407413645177666, 1135263481074624, 2923371258738394617670543744030837028375597495106, 
    149673307279553, 149673307279553, 149673307279553, 2923728073386415816985071169215036283046810710850, 581334286981653481327101393010222584013122101823161845146208742016191432707815032123854714693662756933, 16611462957795337051808645890665641476946317295896982266441921389089590297320328872317895957838507653]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [95677451867072, 105624522262593, 105624522262593, 6767645792041897653518787153367553147015770872372382878943165879631626595205726881331280043943432208849424484184025696442329691198012861479732255489068979078365622318092514278935259345579783682345789849900214021225027960657163111514706470609891749467102685084726368406007196333842635405799940711577909411289488901798352816626978723707331013796336829690409094042376626137800770634, 105624522262593, 105899408763201, 
    105899408763201, 105899408763201, 194641827349460318704797760236000879110040476903690560058967534044104936307085814270279922551796421, 105624522262593, 105624522197057, 708156914160321, 
    45694401221598507776227517383879725817021926211, 143007937483457, 3957829878074701413907686587827558920396154515476837234848369427345372996214466429093741388207507762206778840774106734955451788720619767685003242760517082224079341682853671494, 143007937483457, 145206960739009, 162799146783425, 
    163280183120577, 145206960739009, 162799146783425, 149605007250369, 149605007250369, 162799146783425, 
    35255775985729, 708775389450945, 708775389450945, 105624522262593, 316730763192641, 316730763454785, 
    182710353988394096945727813344201171691599049538, 563021375095361, 1461507213920909015201252374224352795098672608066, 581659376751552, 581659376358336, 16610449198353422912511803907944161699844673150382369653175782224809510879283186691525473357923298949, 
    1462220839128391462825535371062575972393936843586, 16611462957795337051808646749353314959229089455844027623461870969448430711160026637415104874884836997, 16611462957795337051808645890665641476946317297169821599379836785365595447994798216591891133651431045, 73669502112192, 565220398350913, 73669502112192, 
    567419421606593, 580613561139777]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b8_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 103) (cur' := ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩) (prev' := [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_3_0
  · exact tv_b8_3_1
  · exact tv_b8_3_2
  · exact tv_b8_3_3
  · exact tv_b8_3_4
  · exact tv_b8_3_5
  · exact tv_b8_3_6
  · exact tv_b8_3_7
  · exact tv_b8_3_8
  · exact tv_b8_3_9
  · exact tv_b8_3_10
  · exact tv_b8_3_11
  · exact tv_b8_3_12
  · exact tv_b8_3_13
  · exact tv_b8_3_14
  · exact tv_b8_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [3957920449257079469080845689865187924151315275616082471199775114488424426119832772153024810198787987097091909662669079247976904835567370733544522429250291433554938222629347910, 581109621461952, 1161367822537152, 1130439822020801, 176063729111233, 1161368023863744, 
    1161368023863744, 316943093993920, 1161368024650176, 1161368024650176, 316943362953664, 290555083887040, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 572029792162240, 
    290554815451584, 299351445344704, 371089997073248001570191377446652703691430196034, 290555083887040, 290555083887040, 290555083887040, 
    290555083887040, 290555083887040, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 286156768940480, 286156768940480, 149817327096256, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584, 299350908473792, 299350908473792, 3957920449257051350869629794887795358285639961157105646737809262289535250311748876691063690664586009528830137948770434459539464824286377350413609929531049863695805937350603334, 567915481928640, 
    581109621461952, 581109621461952, 572313528439744, 581109621461952, 283816003375297, 572313528439744, 
    1135263213425600, 290838283293632, 290838283293632, 853797363520448, 572313796875200, 572313796875200, 
    290838283293632, 290838283293632, 535719680387928928508262249411646441580330649951083551532746788100983712849239947652506897387098225220, 145706909176768, 308430469338048, 1128653050153025, 
    1128653050153025, 1128653050153025, 1128653050220737, 1128653050220737, 1128653050626625, 88515535702081, 
    145423441334720, 3957316619184925684297189135165343748734463072032449210831422820855888213761873049045068183013169601313331595898196396784592148744153662830160795947834798519981373451856207430, 299634376315840, 308439596143552, 581109621461952, 308439596143552, 
    581109621461952, 308439596143552, 581109621461952, 299634376315840, 308439596143552, 1135263212901312, 
    1135263212901312, 2923371239690557509060862098716539164780434371138, 853797363520448, 853797363520448, 290847410099136, 572313528439744, 
    853797363520448, 572313796875200, 308439596143552, 308439596143552, 308439596143552, 308439596143552, 
    1128653050153025, 1128653050153025, 1128653050153025, 1128653050153025, 1128653117329601, 1128653050153025, 
    1128653050626625, 581109621461952, 572313528439744, 88515535702081, 145277412446656]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161165959205312, 736459918326967617761221917034528982686693864258, 3957920449257079469080845689865187924151312875865046798225662926908875983757671340594824493370926789276042752215032645197139226040711466983107102833308149788955144438184665670, 123695392443150858820591777138244336291394395440714787205159704201763050601339851629069209094461428404674401000154992733047238007702126188065678048127864424256712487880090182, 1161230450561472, 176068032467392, 
    1129145300357568, 1129145300357568, 105630973102145, 1130861139726784, 72714878521792, 72714878521792, 
    2923059026705582403273461691369447352415294097219, 1128657622029249, 1128657353982529, 4089193962158339516515071346465170652150032928531769189723606633645627869991822488917762999952826154346271425790918405154719943833034353681826258450776718619856368769362286150, 265751028401102427289067248950908305789144733842075096001308275958421885846822083711059483610047148101, 1135254488355264, 
    1130860736811456, 3957316619184925684297189135165343748734463071869861173193011719549700737721214921254185555839939557909052319763977186599168686537411926603100512561354959370226015551421898310, 308439596143552, 581109621461952, 308439596143552, 581110158332864, 
    72650454012352, 3957287485226948974103744061753945314353862245461522523274866709018383083513226931727335379675683658574435213199391852306695061568797308891377646522680459389903268938471946310, 3957287367290623198430576803805780844030012398690889939847578035126115638576355549661947710495616287923144332728583030407153477089393724349722670032861095030946969343860586566, 33338494248124709924710172511000926192004885740562247571412966604817919374261643270895065480047793861, 72650454012352, 2923059048494287750744621887311993532425221769027, 
    2923059026716216267804560225656018656792056235843, 1128657353982529, 33218933990109348390486863965668843610206729737035290861388417537392854076580101938017597147063455813, 265751028401102427289067248950901754522153426979699358746261707112147361099140469125691584914453164101, 426692192506304, 145281707413952, 
    427173698605504]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161157436117440, 996326080267117150069539610926479629085644235203682507087665625454694564551298210164613094470797211258086398709214024634705375682658086289793468924027786654242637316675142, 1161157436117440, 51381112940244825504347310871443639153522129730, 1125908774125633, 2923059026695112096712381925630729796131540187970, 
    1130719137509825, 51381112940265594691781450181960012947242629954, 567434981938112, 571833028449216, 531567574968099413811186360965354996902178173148492645221429664407691605843714986949838851227552752708, 1125908774125633, 
    1161509891805632, 105630973102145, 2928713332559469371677272818607758208630368776770, 387105950083393, 2928713332559469371677272818607758208630368776770, 316737205905729, 
    1161509623370176, 1161509891805632, 2141060067972986641489983245086216561761654305052551839625955993797949030643018055440989186062078276, 387105949821249, 4167933910274413237245272489742857075257029778043729253603258568650971004515687507990434955024782807430269429343394198434573434716762439875127798874828720019277292754046022214, 316737205643585, 
    1161367889514944, 1161368023863744, 1161368023863744, 105630973102145, 105630973102145, 51381112942721560628132222377356575957917381442, 
    105630973102145, 97053213331397020659796016847637924631234221891, 7759266745884737787867324976944749980532741920554690601082224481221757494454849463974938166481354484065363615996632407204735934235223147936744552146706388694244984216351302, 387105949821249, 1161367889646016, 1134980013232576, 
    2928723417169022067376522458704195217439525450562, 1130581966852544, 1134980013232576, 1161367822537152, 1161368023863744, 1161368023863744, 
    1161368023863744, 316943362167232, 316943362167232, 188402292404221478345290564329279322293436166978, 316943362167232, 316943362167232, 
    316943362167232, 1161368829170112, 1161368829170112, 2923026272390554537988115669023515424749711799106, 917365294896064, 2928723416146182422699051016717009949421530528578, 
    2928723417169022067376406401382792044126027133762, 2928723417169022067376406401382792044126027133762, 1130723298251200, 1130723566686656, 1130723432468928, 1130723566686656, 
    2928723417169022067376986687989816354975032292162, 1130723566686656, 1134980550365632, 2924431224707956147530185292011445697189328728898, 862868602360768, 149818131878336, 
    862868602360768, 290555620233664, 3957920449257051350869629794887795358285641428609152284851801827183634099114761788754536029376551979929867989046204625157455101418220277231743762659643258421713506383448502854, 7759266745884737787867324976944749980533451723996385529686276555252898123882929452606839361515917891368976565329855248476193662653752842279314836769978955928191582389400134, 283958550335936, 283958550335936, 
    286157573460416, 572030596682176, 833693890331902870340313078954012348387065893699, 572030596682176, 183045235268561950217819267195888480153763853122, 1130723298251200, 
    1130723566686656, 1130723566686656, 1134979745059264, 1134979745059264, 1134979745059264, 1134980013494720, 
    1130723298251200, 1130723566686656, 1134979745059264, 1139519391273408, 1134979745059264, 1134979745059264, 
    1134980550365632, 2924431224707956147530185292011447948997732348738, 862868602360768, 290555620233664, 290555620233664, 290555620233664, 
    290555620233664, 79449387438528, 290555619971520, 299351712993728, 3966977959076728493407069132047389504248000812626318421807933950031306258814136838459081076906932684677732169926361810724927128792477930413800872626509811725597425125512180294, 7759266745884737787877145148768247869732949545514152165202631488330373717290523336887000994051046685369872177239443931333151165653160884755603345950179478423099531195314758, 
    7759266745884737787877145148768247869732949545514152165202631488330373717290523336887000994051046683609926858807850165537288420772519394380570558046730906856655854126494278, 7759266745884737787867324976944749980533451723996385529686276555252898123882928947421917201157735849060283300103708148030651350988333041303302301037356387888524202937938502, 7759266745884737787867324976944749980533451723996385529686276555252898123882929468903127172191806579777301993214060196965447082256317923873844261268722492882374825667981894, 123695392443150858820748899887420302518588659820412146180609987400199469246676930144168262627160486889433972128009307786023226470106702675168375871029787152488861566303728198, 290555619971520, 1161157436117440, 
    1161157436117440, 1161168509407680, 3225580504192166417836761545841063272198386497346, 105630973102145, 188397414113883790944883745947744104877559658306, 1161157436117440, 
    2923036725865007830418698853551010946560645151554, 1161157436117440, 1161168173863360, 51381112940410979637645725469671315784408775490, 51381112940410979637645725469671315784408775490, 51381112940410979637645725469671315784408775490, 
    2141060067972986641489956183007052683065088594824095171203612775271352712463195535062745330317578564, 567434981938112, 736462602474296063222861846574931243388519887682, 571833028449216, 580629121471424, 17127037647020871812872020370332351676010216258, 
    35193239371841, 3957920449257051350869629794887795358285594409659868359683118389921524965577106052655561157644413600042373184682157620347167973094132456214706819939431324339143042975515275846, 176343044600257, 51381112940431748825079864780187689578129275714, 51381025828145817064833218156288187045467142978, 567434981938112, 
    571833028449216, 583925460778860723712888219525864395468814475061014398120264503191941525646800522047019333708738629, 35193239371841, 989143293765245393976718131553508388763519527498344923943944473277145124123097435146742168914475360247004159232789782096028760780225773969987304005057043817195229737572927830442869366128337627008365389322852075485340273773509918802639558497716812610967437313246956553, 531566814649450785657876682453298301676521680971546044596409420600945706501360254130836312353876911172, 1161226155594176, 
    976769454382615135350586901657136576064305691034313659323156455086169285251163600088220770061581100593464583926644902819689318865075084429955017773474504395754676985331685389832113485621129393935197787354593647750867930255422654557102350047035303598114210312245997512, 15015491880075510186898946866980240133138633850871926095099288192389851994449201877649744225173010095748661848615924222253106358379004727278239349074585512555989448155036864613347347003760192815302734418907459927754276315680904893088682104077378449875927560245997512, 15015491880075510186898946478850717057961400063627056487701903850262718137229767377201858678490527568698155467293377528787116602074766020759779707580895906265718986459175409758539696654752052324795414035211558400365261253537309108032794607425451499045519361249356553, 176063737500096, 52402270903687832003459046407038011732079721442405875854673365904038467304407418606020294890420466254265969092892307978971229242760664537051494463844616110615148762111925205950594372565629598276254097394349124474961248803724041637758922584594812245611489757207178970228772039149725210400647588315099755907175917560899165175551934193103418447904450960211213916033562019802622923, 961754420725220818364191558845582782040999896248880979041833363901559953222349352541973983353274905382951906843801977850719338162759992833555970314810843774438102246189696668525848963685816347571544563227793544427890741355726547513858136061519974465949139464245997512, 
    1161368023863744, 1161368023863744, 316943093993920, 316943093993920, 5784197299287483405454868079360132401368576549115071685582968012492842342059076906000770205466505842293403811261188302802503782738688226918386777461711733991070754799572754042507689734775535297068161887752486061581012383255480926454329665366449327889869986700283921820453357666897964281765686936849293669370384799413566963125889261480988672766991112084865363051733336392812477810799576271855428323871085555249067171790474317767651141747075384638838638648554315524636917338484291559164372894055906226639178118400265289210115902974204872727299679206690448910291846713820557707606247123059342114923827733314810791617076953708865881472487563293608209037648373724238, 123695392443150858820591777138244336291396694676127880012348308470959859752155427914204236940043264620579573075714916022463214538981245759271343917953645874091684923434857030, 
    316943093993920, 316943093993920, 4158272566466870091383534110015526725823507602172611964368012567025801406072639159820661693913391619540947265344009786154778590961934249926081701457506221329963200667210216006, 989143293765243688632026922530777792841446026963649081106416406050239333336712610034378346344631689209793821883085572329629512672046169742176004247802535167204998903681737043459931891794273465489049661539110458492570131702576101957658684932381998383118680065246956553, 4152865708507573132457227681927858014687311080567740603537893371855269783361387067413492509978240068, 4266660209495474733312466059838050347583873651257638296144116332773531361072192919584455431986455620, 
    4156413866686451810832326196060372877436855084232437382805955175078775291917310401518936410690004036, 4221294472902549454359975158907930339014490239242131417826339713726369959595191814914500760060666948, 4250186618073418690953369688818056170020323984299326123047771839513984505325754825108082050070848580, 265751471920874772371720477642306534438301956038827328422050907019478904717026909581021913713225344068, 265864506102254802529986501678086551913671797550287714252388335183017412147301808937363528169209308228, 265755020079053651050095576156439049301051500042492025201318968822702410225582832915127357613937108036, 
    265815845647351030204276783781755361031961649759598955067185468150713146711403793204285226343657219140, 265848285950700778119048314482005326877301533262821068420416549835808012166259162198186791300861633604, 465064695206726218478724981095366355711890050145677011634251007576576037917499556398121780514698312260, 105630973102145, 105630973102145, 387105950017857, 
    1128932231897921, 567503165068224, 585095351112640, 571901211579328, 2923103629376994606508239527889940007942243760962, 1161228235968960, 
    1128657353982529, 1128657353982529, 1128657353982529, 1128657353982529, 1161226156511680, 2141060067972986641489959188413954655150199938713273817546691263398928877434847813312017917561327940, 
    989728515036096, 567503165068224, 580697304601536, 571901211579328, 580697304601536, 567503165068224, 
    576294828904896, 567503165068224, 571901211579328, 106109457273280, 106109457273280, 106109457273280, 
    106109390164416, 2928712461445908185002432439366369227910974290754, 176476054884800, 182710528180985336458924098297377327399980513858, 182710528266055928189158714163220979257922566722, 265783407324362814692514333977381485969820436219451306309220949869568685688740570863550041873157023236, 
    537795859818752109918893605057614489715581452022222894160747114316220870257584847473373096984006796356, 145689729307072, 1135254622716737, 2928723415815873190407680633916649592034840052547, 424836833743296, 283815877546432, 
    283815877546432, 283815877546432, 424836833743296, 143379439555520, 72709645013440, 4080951628232876772103526134556496487211884578405472854500835915091350203685798936860833433391894517810946657876987289089512764174869998482330808486091681925941146805765925446, 
    72709645013440, 172497874826160916349374052754890674445100240146253624283008677511187487057180548827984668552108177090104038725564842684561086220838323431766585100947228412751333704308857258922400509722509993352677104317357986441126903521921365029141177598712746854043110800407853552446636589970699055944573925332081479411194798870086588157676925855980405196264232322925052058089718989135303764410815178914986818900438954990467642711700685757326322518433821623702403035000671958873909724248872892070336609937456899236140927583126747012124197463882459179801642783344556401644816323246760546075248113122967903525303583150371971143980890701977497367893119026044451186388559, 143361857032640, 143361857032640, 424836833743296, 283815877546432, 
    424836833743296, 283815877546432, 284099479605696, 1128657622688577, 1128657622029249, 1128657353982529, 
    513317857966737387904301874424141937318015012636919573060243240994170094627232533620633204468386808825699707650318627423153498072518257556550430966860996788068673751340614, 265750998701118393905084722680686169349901786447086705643697080014675192465671738246124622795615166021, 1978673462481190782656049655726538460145055812677274566479324212850068932752436812788669926156118293508272331000515451604218169827074560787036764980571330352648230325958202950, 75192404545984, 286157573329344, 286157573460416, 
    75192136110528, 75192404545984, 4158242433965077256442002245306975966697131435609321918454730928296053174801285614975458634365205846937897431057637918943243794182951615716963834785323680186064720867543216710, 286156634722752, 286156768940480, 286156768940480, 
    286157037375936, 286156768940480, 286157574246848, 286157574246848, 567773613789632, 567773345354176, 
    567773613789632, 145419146367424, 286156768940480, 286156768940480, 24263297898931498902744564851690167847859815235, 159184516551616, 
    159184516551616, 1003746885637056, 106109457273280, 106109390164416, 106109457273280, 79735003026368, 
    97053561801634534149586123715437357475297246018, 97053561801634534149586123715437392659803552578, 33218902561492904735556846207601157986802786660681478854088017599573142546110727285950771895572126340, 290847678010304, 106109457273280, 106109457273280, 
    28545062765744990430701354142192811976108815170, 106109457273280, 28545062765744990425739920254204479834328939330, 176476053967296, 176476053967296, 176476053967296, 
    176476054360512, 176476054360512, 176476054884800, 145707311829952, 163299497874368, 163299497874368, 
    150105358341056, 150105358341056, 163299497874368, 158883868840384, 853797363520448, 176476054884800, 
    308439596143552, 990140429243328, 990140831896512, 990140429243328, 567916018799552, 736462602495231484018462085951625254305448112962, 
    585507265319872, 581109621461952, 581109621461952, 572314065310656, 581110158332864, 581109621461952, 
    73120752931264, 73120752931264, 22880651877387912666330838747468919551335348034, 265751028401102427289069007543257046162199885812139376981243710031840842287399647952427409949806817349, 265751028401102427289069007543257046162199885811585350959531095427585587026657425252395646694360084549, 145689729307072, 
    145689729307072, 145689729307072, 990141234549696, 4158242378682424545877174067376945974239547267698697873326787519808434219117271852378230984684694805248724064964951223756716735222699614876508191190749530547597824987792142918, 283958550204864, 620836638035296940978642054847794999380553518048013198747585751226279636110327378989643700503594678268771397552726055391547320708401952599987801909921321524012468218421024145316991048129478768752860690562434337322372143124990786164340443179675938878469124293590239469629224262420360546671614999504640200823731069188949766771348791608416769128123423514777540690050136107376771935979660756601638323965854003755105368825607040107243161696295725729151288489344831700971701356738874480711147348579877660459971398413, 
    283958550204864, 60383859598390094747867247699644404364181302628185540619072920869882325368978588480753566178575452074978404215883638370926341142928659582143334714929316548462999841558086, 72639716594112, 531501997402235371604536482063022968267842695623939605455300626026834323663529161405359765695133557828, 1126458529956417, 1126458529956417, 
    531501949882260587742184532681616481834152658249993574006296330440557833688825337994125483863769892869, 3957287485226948974103744061753945314353862245461522523274866709018383083513226931727335379675683658574435213199391852306695061568797308891377646522680459389903268938471946310, 3957287367290623198430576803805780844030012398690889939847578035126115638576355549661947710495616287923144332728583030407153477089393724349722670032861095030946969343860586566, 72639716594112, 72639716594112, 2923059048494292943061287462768476377696088688451, 
    531566909688434973216618815775582182581406202551230366326597174477014622771159714319274303681260154949, 531501997402235843673080803229557732773481215950084082353306802115131791852314626378355749407695217732, 283958550204864, 283958550204864, 2923059026716221460121225801112501502062923155267, 1128657622688577, 
    1128657353982529, 531567321529194402003021360818622978727958829399911710536193024411891792196006923315195789075376415812, 33218933990109348390486863965668843510242328626201386547243596379522067495145443701425615476041601093, 265751028401102427289067248950901754422189025868683620244406724336805344865485139577384502017804988485, 7774362595245726724594926067066136785475014222102819087314190605825081420594613677621604623221877607431375849865281641798329817420368239172602887953170065046403609331228230, 182777604888390466720997638170411646385955812162, 
    730842809590337560534670766474807141481364634434, 182777604888390466720997638170411646385955812162, 145277412446656, 568056813196224, 145277412446656, 567915481928640, 
    531502440922011507987687986801948015492080352536889840451155839060349930300756034296296476719949456452, 145277412446656, 286156768940480, 286156768940480, 567768668225519906783121689580456505943387169180555699859553756926539504832913868936959790494773317, 149675458957760, 
    299351712993728, 299351712993728, 535686733205322738969914417874735183905193936409054659384936919714325449949038613253422798417936163908, 158471551979968, 158471551979968, 158471551979968]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [291388038583232, 1134988334732224, 1136981266666432, 2928723418532825578142970300950325520779909854018, 16690536445057661165191683008790748473017419616310996966940628220266094376395934651526429639945380676, 163844958327744, 
    581659376751552, 16680407017832143021476894212483785717218805055230324939541377458892788670694896814148244508755256132, 581659376751552, 581659376358336, 581109621461952, 581109621461952, 
    581109353026496, 581109621461952, 581109621461952, 581109621461952, 308431006208960, 581109621461952, 
    79306706391233, 871656105448384, 580629121471424, 580697304601536, 581110158332864, 581110158332864, 
    871656105186240, 290564210168768, 537796105275778724399705667485149936879420477719816759711258088036232295289058162997409423248856556612, 145290297349056, 3958006977665095717692379947811380348004870243827256929399279026976485368581477086369117068984571274005200642565987185581755663836646016578422532699611733699329175149938205254, 168242601661376, 
    11774838384775837982664019748807941481197253186, 75883624928192, 75883624928192, 79457977373632, 871656105710528, 290564210168768, 
    943467958637504, 564786192405865450604643984021517682087009952491083134461009005536047634036238306109657902168254293060, 564786572565669386325938591192582769515773313020731984302508404521864708589214901668488033490824084036, 564790247443784169093990425359048927817677437929304108461026521568842124894822877744320922113233232964, 137871296185277590929123679983784973673306662083472355347340275999265855883041803027702238362547141, 564789740564044329282822216364877668663197681671195088099973548057866371582263865030427771488670426180, 
    290564210168768, 871656105710528, 290564210168768, 75883624928192, 75883624928192, 23014456880290496075264292297925528528967742274, 
    75883624928192, 75883624928192, 81450842198976, 79457977373632, 79457977373632, 23014456540008129154316157317313539622618315586, 
    78082581074880, 6740821879975988026521245911734531044613713152076273354585977065720416950637795508775963741998921209310499249565269567127029317550707705635146231944479863168224143113875313178697021437391925721569569675543098646888947832902392959916761714590352953218828581772369738397425053172617395687841223158811185634144509770316840436210988052398617161386680695914317377452372064994630347362502754515783023063659803101989981039031175809789388115285139339043819674148537805345856332049346423881768576760250607317181773735153396582613609025019905176585883221839150387627734556367978159985696697313760646857416146321469016846543161661330263120791912268680260333888379577892352488579802251080234325973572485409659578855299236678680442686685012288799666289289479522556410086250747000444641408186864196936922838399844806706448383023289827448656851103124896408664773821011139567150721048857367646868254469410797002650120191811893048827800572627238510452312354124387829210988039641734416328410331142722744788701649327689607026460103686207349591061478045310785122385024541524616194822631794721433692445488853791139475054328587560353002992736012265990729527306997401284327050311611510010540013264831409217177426272619795018559824709586307811267743404509594607341885982841708043615865478064964100666155821029817490585295523270499686792078004476829168077451800850583047802681141213663348276410643147614348460378111968673808690588010564803678978744461924528742249391298844452394166594830449970265846470326360571642903355705088628848903729975786059502519845443122763033833194458236036610547222268328118681528758757756505258956683722908019926564399026347166768014765123794508746287547339716235882308157772147059956431779838997258968, 535719680387928928508263128705328054701998740094722918614775471478134019314956006633243009712668386372, 146252369105856, 146252369105856, 564790247443784169093990425359048927817677437929304108461026521568842124894822877744320922113233232964, 
    564789740564044329282822216364877668663197681665740062384672941471641928238297891468518449913900934212, 581659376751552, 46028913678147772768432850737842545414761395010, 149825917031360, 146252370023360, 158420024955585, 
    149825917031360, 154086524588992, 149825917031360, 149825917031360, 171679381722048, 171816820675520, 
    158420024955585, 158420561842881, 145290297349056, 290563405386688, 580628593525313, 286027785704384, 
    286027785704384, 286027785704384, 294824012944320, 312416870077376, 286027785704384, 290564210693056]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [2923371238361329594247099300027507375211110478658, 2923371238361329594247108971470957921129952457538, 1128184970025153, 1128185100044353, 1128185100044353, 572854693794240, 
    150642228859328, 150642228859328, 572854693794240, 572854693794240, 80268786536896, 84675826094528, 
    150642228859328, 150642228859328, 572854693794240, 572854693794240, 1461507213920867476667927770574795875940950881090, 1128253685371073, 
    3957286427485527111778661891709499483189072249239034106659464513565086842785957174549272351145102433321328824145000197370456749242460252136184388282231779062309113555922699847, 290547030036928, 265750998701117656297987067882619201884752896315138283728167663002607021335899336179126138237000839365, 265750998701117656297987067882619201884752896315138283728167663002607021335899336179126138237000839365, 572305474589120, 290547030036928, 
    7729078731600933628437679963602718320107268343769672063058034901047075776712909962211997906679499670124561334693542827355526936696442077018182677612846312680443715998697031, 1978643215484742977146512441229227506897933497775709479222125768714718651725354259878976391944148046632322414905211419051732884829148063524715795031670908784249484761207129671, 531501965722251631616338442218049409810977256899298335935140467231180271693021930836419023112548610245, 531501965722251631616338442218049409810977256899298335935140467231180271693021930836419023112548610245, 531501965722251543103487040183268616042994127252718152040478862918073334657319012107592528450236412101, 531501965722251543103487040183268616042994127252718152040478862918073334657319012107592528450236412101, 
    572030597206464, 531501965722251631616338442218049409810977256899298335935140467231180271693021930836419023112548610245, 1128184898717761, 1128184898717761, 1128184898717761, 2923036725960399449600350732219156686957437027907, 
    1461551814199029293895700872037599829402830766915, 2923192831719176615439906799426593603772754178882, 1128184970025153, 1128184898717761, 1128184898717761, 1128184898717761, 
    1128185100044353, 3957287669502457950539484277213028230953335791663006307413244280538695218689143406849385456874773795973008670212946788459388727336620170861814593323102110446862555034442265158, 1128185100044353, 23014456880272322976838298515527418596657476418, 163857843229632, 581659376751552, 
    581659376751552, 581659376358336, 2923036725907292758956353292997458250970995635010, 1128253685371073, 80268920754624, 1128184970088641, 
    1128184902981825, 1128184970088641, 1128253618262209, 1128665935122625, 3957286427485527111805477507569384677388244432552460802929910892738581610295799659392147100012252587307884841247336294588617620932283950096630848778158173690590703555155294791, 1128665935054913, 
    1128185175747393, 531501997402235843673082028467828721302319981674545662624807775116897818018486351300632948416005644549, 3957286424721394476599031345126779234910548776319919847528248588369111148862390617583182402440625761290423802552966331415946039093288530486429036556204573919559899340701361735, 1128185175747393, 2923036725950097893335815177058518097142871008835, 3958041221582916183306709044732106390945557888734870057655767152005854081573793393005170549248339425444227842172914808065532931110556307740378649337560953492185452165044600390, 
    1128185175747393, 1128185175747393, 123665204423862013091590996083691866570813393571676937481763223356029308536766292539942174095644755554184668085651853310255209900726746569045312751713607100521005069786641991, 146243779563968, 3957316619184925684297189135165343748734485785569124676029570219791433971881285648085489929242555540140270568007551389034031562785650291705819342222639351911062452182223642182, 73671649661376, 
    284777882194368, 80268920754624, 731108332973989501280306833880117991409197298498, 581659376751552, 365421404790025805822199550855930028100849763139, 146243779563968, 
    75879329960384, 146243779170752, 146243779170752, 1128665935528513, 1128665935528513, 531501965722252339719151417920491634045928517979389793547524302420702802677503249413493619632695070917, 
    1128666136855105, 1130452710723777, 83850924396992, 531502440922011507987688872858590831898367316546058926431842159963971489140745710554143137811784385413, 3957286482768179819956743135535386095930346763735873292166478601369796790101300072893659518088668294203269792455656948398523568201146461039653250299469513779227541883091648071, 531502440922011507987689092682635243365879351388973446728986241502240607062889814055478228366189773701, 
    1130383991640257, 2923371238321452602255508810783220562219547767618, 1130521365190849, 3957316619184925684109479824141464766515475154415460408195524067574680411373838615097071421540446546556419967924395455375767303830098161133076735927996442305496657009588514374, 1461685619180644028015341255356650256100487332675, 1130384203197377, 
    3957921577023166580744291592952589360221301937869783870707864548507636940187743053420706668520819636249049469940980054381321318803450229045338191976116352328084308990296584774, 1130383926237377, 435690216100288, 2923594244580123466427191645298702887567025517378, 1130452711641281, 83851058614720, 
    149817327096256, 290545957081536, 1130452710723777, 1130383992164545, 1130452710723777, 79444287951296, 
    149817327096256, 572029792162240, 290546225516992, 581109621461952, 290546225516992, 531502440922011507987689092682658172800521288335407949524201226904195707996731690160918893586232963973, 
    83851058614720, 290545957081536, 290546225516992, 960962621521537293379978066036846006136302196138644212446272102213445698559557918723149746590774080304015590202577841806444910174522418996274607531318137521328568277444690775027369329616726359310423866470854413212749056931611157894831156996330473260828328456246191112, 1131002600911809, 3957316619184925684297189135162222000183942661781737445987016028809626878194468017940148121053556827036465052928649905879006777733221190910374632680133100823280561416835159622, 
    290546225516992, 725845724369856, 567434038743233, 290546493952448, 437687644328384, 437687644328384, 
    11596431782481520859574259147544646405630997314, 531567321528223829083112490188317425117992137813409569224668151583544074859035013571475722929299485572, 149817327096256, 290545957081536, 581109621461952, 567434458186433, 
    290546493952448, 3957318108591727374544439760292094690229662872781875419598534552520245461287320038283648558723622977079539291041913331808525126252171890820723540204155880299594483913071742534, 531566814648484225306161819782817088462783182624643094665866621105900425296436751915818071467744259268, 708171946545857, 145221993124545, 567434458186433, 
    145281573196224, 290546225516992, 308439596143552, 1134782245514049, 1134781976873025, 291370724102592, 
    291370724102592, 290409590952384, 290409590952384, 290821908206016, 290821908206016, 150641825681856, 
    80268719428032, 80268719428032, 80268719428032, 501459318739392, 149679888142784, 183402028175797540171831498863172627440336909122, 
    501459318739392, 149679888142784, 572304670069184, 123696335928358367652635124616695946051363998779537850013747640598074343773263737992291472565102115233315432418798233979760929815691837075503460758257730071818748899155212359, 79238933844416, 290547029905856, 
    290547030299072, 79238933844416, 360713910751680, 642197477659072, 23549676764528270582390966675477641309078958914, 290546493952448, 
    149679753925056, 431154864853440, 431154864853440, 431154864853440, 712630109999552, 149679753925056, 
    290547030823360, 290547030823360, 1134782048246721, 531566814648544414059518183662259215919050899495550234557650921552115942616320921278155726433611211012, 1134781976873025, 572030596682176, 
    2923728051603203940427556977510208006710498689859, 1134781976873025, 1134782178199617, 4081435634987222247512024594046900125474848936706162436628526082504868503941088806975060679041366288760420834503123726627074120688095910526160057316002217190043466023265335367, 123666144228958051663211418310059195504788281291097087845382036321316702784936525560539310870672647462666530061747363219741616483499365996085420223186286705324282921072162887, 1134781976873025, 
    1134782245514049, 1134782245514049, 1134782245308481, 2923371239680027491021495209926182999269499470403, 3957921577023192969013089327086391147594136752317493560909618299334505113702458222869322866132006092390609035715368302261186493940395482871502400173058083749945314094480351814, 150641825681856, 
    75879329960384, 290547030299072, 4104170048216583831055539633580301494153034954633525928953554275633829302337163544843342957248315201511027636875904436266354811011160947260863713661487618624906007727092743750, 943482991023040, 4168901663976203132419678884029226468673294134181894738520170234419460060397279125816501467368985965407734898482922711258062836013301167506063553080603290889667535073374581318, 88528420603969, 
    88528017955521, 88528420603969, 14272531393526804490215961078403815500966789955, 290547030299072, 75879329960384, 75879329960384, 
    23014456880272322976838298515527418596657476418, 75879329960384, 78078286107072, 535719680387928928508263128826081008085695625160495874868197782614452078087738557032028989593403696196, 146243779170752, 146243779170752, 
    88528420603969, 88528420603969, 581659376751552, 146243780088256, 158415729988289, 149817327096256, 
    158415729988289, 158416266875585, 145281707413952, 580628593525313, 286019195769280, 286019195769280]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [2925868921802255685771937679857906968103890268994, 1152580520776640, 1152443081954240, 1152580520776640, 2925868921786304959963762179048734015284989473602, 84680121062336, 
    150650818794432, 572863283729344, 1461507213920909015201252374224352795098672608066, 1152580520776640, 1152580520776640, 3957344566408624784345365678984872470827010303658589706157957064515098036170948400959664994411983136573324529982682738664357480481258422747004465417815801665220590805419274822, 
    589906251092928, 308706152289216, 871656105710528, 590181128999872, 572314064786368, 871656105710528, 
    572314064786368, 3957287367290624894035598852919657905840989602995591593556738405612699739242969877639360287834749370953444352674865565682576917635079948419872013644484824319903506769320130630, 308706152289216, 871656105710528, 871656105710528, 3957317558990021763896597074513483777321156805176720882992698890273639867762698338601815187996751444526582138906454889672419560626776655943359523499653547335948458782808301126, 
    308156395951040, 3957317558990021763896597074513483777321179430161425238078812544392135882582407446978645841895571704072929181978747396174676347508258625721257188210344456221644473855293480518, 1461551814199216217138443208193747167968544162627, 1947836356962666798087585008708321753582925263927133504901248269258065708390309345729541270410230877118744912568497244740574643110826078906561090458325378314676283433731654, 242005340496953503816289947997725603120450446414892547764321895260739028962725682607624613143177243272387085781302026755707210944201541590228037788016161297843887185249862, 2923371238340020255980085679411370351615220462402, 
    1134988334732224, 1134988334732224, 1134988334732224, 2923728051608375487825928603948058202307488215874, 581659376751552, 581659376751552, 
    581659376358336, 291388038583232, 291388038583232, 183045944456907182473841231752050358003379024450, 581659376751552, 581659376751552, 
    1134988334601152, 1134988334732224, 2923371270988497529402960013223026568313658487362, 1134988334732224, 2923036725907251063541363390790229854397059380034, 1130383995442112, 
    1464361729701995150169355557621560483777385411394, 1130383995442112, 1130452715180992, 1130452715180992, 1130452715180992, 183045235268598296434478295389250784401737986882, 
    1130865031779264, 1464356851413983042583976959464031448051080049474, 1464361729701995221157789170402403589880159482690, 368588132237269726995017466629531656489097311042, 1647406955442624936084612697918115873424897290818, 1464718541627830096131189960859731034631995208514, 
    1464361729701995221157789170402406967592764912450, 265751028401102427289068128361143511427579329910789064411693961554287700711724053535319004760845316165, 3957316619184925684297189135165343748734485785395155898837489954396887043002399210077174747422302319922886088184848641372505347747117663314049435674663293668504723005105987142, 73684534563776, 293586860643264, 531566814648487765820298809195371598988215372228345423683554479747612176819634522130820462786109664452, 
    82480829436864, 291388038583232, 1464361710667450402646890684193348870041497580354, 291388038583232, 1464361710667450402646890684193348870041497580354, 915223285333079095203488025763885827198239748930, 
    581659376751552, 146252369499072, 75883624928192, 146252369105856, 146252369105856, 531501997402235371604541297741964151506216033423071027041039861554875986669997478608041426112092565573, 
    3957317558990023521284798067949570812687761370013384503968135726959824672745343890117166425608325245385290567939513423486656320471684837140223329817614814080689947262719057478, 93475744388032, 300184131605440, 300184131605440, 581659376751552, 2925868931330161959558214656832395976193400189762, 
    1143784427754432, 581659376751552, 1143784428540864, 581109621461952, 299359498408896, 581109621461952, 
    581109621461952, 299634376315840, 581109621461952, 14450937376403547803626801717637761630552011586, 11596441990991628041781030195345049886107185986, 11596441990991628041473961856580039065552892738, 
    93476281127872, 93475743798208, 33316191415957783945943730355043089267597827436787229185868035704206606439317792411871186872577717124, 93475743798208, 529357198247630652435972179683705368137487671965939716500371154162029508307158807682837256473127990018716711635022387167579181650223098617840740346397658339718089156802630, 33316191415957776569872780185478023120265899966238880527979568678114380788376610020017998392600195972, 
    870968776987584, 303551453598656, 308018286695360, 581659377275840, 2923728051608375487825853648195290107200036500290, 1134988334994368, 
    14450959835018995398094983067680271868666917442, 1464361729723262950219676752785136610560119485250, 2923371238340020255980085679411370351615220462402, 1134988334732224, 1464356851435250771645864541846761091018434622274, 871106081723328, 
    183045932206741973320056547070572934726204600898, 290563942257600, 581109621461952, 183050266170738958495526025907317649314286744130, 1464361729723262950219676752785141114176926724930, 1136981266666432, 
    308705884115904, 581109621461952, 1134988335518656, 581109621461952, 308431006208960, 581109621461952, 
    290563942257600, 589631105012672, 290563942257600, 581109353026496, 581109353026496, 299634376315840, 
    11797899736279318406999543906883905466488530902591787552497645389860340643701064497195603150573065280899614033252336619886047884646746865438775976682593057259189344604818689145129681857270771148168508473696519726437308990745274456868129863800742126683853286689186173175746039826515492559378220699981129154782282447665784700984941872732859285194444751261118748492248838197176014410, 581109621461952, 581109621461952, 1978643270868171356894984430438010847598071112725106017540665695019489111898869082169883015626927444335469981305372501209951903650234729459161778191849001242204306317332444743, 290563673822144, 708176241513153, 
    708176241513153, 10325882931583270338949127202615331791917288094683748077605096329660877454863205258284248939848279924302804204677533389841603302578666326241426198113977916323027822016972569079380029185213723783881346513601234228562062730341669224002929188436566387488251492748581206347555291376598973668795747222325009410798775211659222404426117832037252847506689682887914077253435760450258381898, 11596431782520463224662554754721215916802126658, 531567321528223829083112490067564469435114015244131300595969046254064609364476617587120772653334819716, 290563673822144, 589631105012672, 
    290563673822144, 589631105012672, 290563673822144, 290563673822144, 581109621461952, 567434458186433, 
    290563673822144, 531566814648484225306161819675481127678065916616732616079050542127603407040065284823729478318768417988, 708176241513153, 145221993124545, 567434458186433, 308705884115904, 
    149825917031360, 290563405386688, 290563405386688, 308431006208960, 862860012164032, 563517166982080, 
    563517972288448, 563517972288448, 580629121471424, 2923192852774438676444060724819748139344018355010, 580697304601536, 308705884115904, 
    308705884115904, 290838283293632, 290838283293632, 581109621461952, 581109621461952, 581109621461952, 
    871656105186240, 90796691297216, 581109353026496, 163432641860544, 581110158332864, 72722462806976, 
    82068512969664, 290839087682496, 72722462806976, 871655166448576, 1016928140268480, 290839088600000, 
    11440325949369034878106482813348436116993291074, 73135785776064, 145703016862656, 531566814648725572209675331654007383076271472313779253986979452823677698909761837643554197386809468420, 299359498408896, 862860012688320, 
    862860012426176, 290564210168768, 871381227803584, 7636324022167556784850685072268030410994111666068086994547516692885697546693455377114055238980715541875548143170422442172544507755306525234954977030503264656315962451531117126, 531566814648498979306709625293015196780908247145655144260271058517068808662899308698057115007281686020, 581659376751552, 
    581659376751552, 580834475119552, 149825917031360, 290563942257600, 290563405386688, 290563405386688, 
    145221577872320, 581385035453376, 581385035453376, 145221577872320, 4850287357029081907113194342608390875253802244502402169044582776359321290648215649155281463286073656860678814575199403924116861470989809551752014687179887422379301813807785629237883988801578879886887275475209916928176762027762898184757009248843031552258155152158563244456153199341682819936790169887138727933387568259037508620987398057058928844448428708707438349334562826829279550260138995591953864009853636824284527800644780315486602008215473371501110037775189563224688979855206736235612614130206918836651341, 426765274059712, 
    308706152289216, 308430469338048, 290563942257600, 871656105710528, 290564210168768]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130383991181505, 1128185100044353, 365399103964897076967743171740240873249883321154, 4153049406159124849731669713328262698878112008606895405297787329162115395083023393932825672345943586230696892378070418147771901580291190239938555485070105537807488157761893958, 2076195733907563424423218752919705972513283005990311738559370344476956089397873526294484106327678660, 354123283435968, 
    283958550204864, 283958550204864, 638763511499107679325966391126393200634711396606467059220997789302805842380876417924522708548251717, 91366501655131037985663318136427239530093886274, 283958550204864, 3114332582089866865587314485581906852615126420036066980425154611558337586783094927486385258698720580, 
    2076195733907563424423218752919705977980083346507057434696909808961440783292019391603307764179328708]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128322409042113, 1128184970088641, 1128253685371073, 1128253618194497, 1128665935054913, 1128665935054913, 
    1128322408978625, 1128184898717761, 1128184898717761, 1128253618194497, 1128665935054913, 2923371238340061865343368227926343987563549766466, 
    1128665935054913, 1128184970025153, 1128185100044353, 133816258058848940926468124843190183060244707070977878120964413137345923864021859638157100446900484, 66441797783171491808080836178675739982439706226983392600694744699229628488636714238991870945684147396, 132879538548455479010670491505896146271138793778095168540268361923357752780640185758681932700500156676, 
    290555619840448, 290555619840448, 1128322476153025, 1128322409042113, 1128253685371073, 99891607233880560330628571490009752224789020271927948280532930767981830340586766790500337700535959700591620706731587415023122358876763790690549557391399923275061893196638955757850472610175927460922363362505436879898884141684461796698699331509206647701950518322226516002996202853265896253475926798801263512030416017404252734902822973784651862329790044249304449174201940398409297759137400934247959494502991622088102398165157462931378767927872732510290814351976338910658671719622921325085850307231805571392829998973771898161340013011052424548340506161340947804136833797584415997097072529070816738017902693145072242914697799902668653894188883221804152618649181809569817156685324319020611505049568063719825440158923109198390984633226971367854323487534578607100189715335162108334932054996527413961140200134573670325492896268298686867312748584210466257588137918018805886424325434982614645604707021991706860099860807166487056153703998259729256643436674809299984688054209379686336449396797452720484085861807093898223827893075591290047923256046235208496528180170526639981746649352615224740741023254721522732343108592715139929890269115325661181230403475468834474406296360258598043352804656624596599882059221928116026762921657264440775042132, 
    1128185037199553, 1128184970088641, 3957317558990021763896597074513483777321156805350689660184779155668186796641584776610130369817004664743966618729157637333945775665309284335129430047629605578506187959930150470, 3957317558990021763896597074513483777321179430508008949843914401840611926891679826522145216615943444482926970830029219585733195874021530996831939694250207091012304685431217734, 290555619840448, 290555619840448, 
    1461529513368780940808987017555877737785634853699, 2923371238321452602275896138018807016802232578882, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 
    79449387438528, 589639962596288, 290555619971520, 589906250568640, 960962621259340297057677422063182476857708814791000968182031025767761290532114054662934279788436017963666500033200301788866773997472270197641447516704438617612315754716475510308692333129850293380266692545289165189736825254535594466821305412451460978583798281246991112, 1128185175747393, 
    1128185175747393, 3957340674509873768378188911914518212778801862219515202564758153999156833648264956248390091894313399019976387632674268808101369649183063890375506523245286460653860320207435334, 33222925915530249330393399661577410146221186406382724844132034808863213295614335035917564742207594756, 589639963120576, 589906251092928, 871389817738176, 
    589906251092928, 290555619971520, 3957287367290624894035598853668097132687774399588490607998728059317599850749494701903335639326607307409515041786847820486116239838392326199466720711843195112146987716955387974, 871389817213888, 362919376458176, 290555619971520, 
    362919376458176, 290555619971520, 362919376458176, 290555619971520, 589906250568640, 1128185175747393, 
    1128185175747393, 572314064786368, 11908007530436053810993964339550845021140997921401489821610122258966937756248230340407420845976550139534016306241194440686255282454902209499860554368512687680045642404686985887704831273274834615507099618147273670620964786414560262975582402050980507387419745571238920956232656817771926423556035064731113940124869762048360666906187822026842386038939962384230422701451460528357877451171588891843796123898478744228834471175296691452019882893694959339391779325088097168372482537624046143794535302669631373892573514744325406142226457082666863188835471466619981883580558960059056382014969911656343765695794231181420200500130664191471055499789044762554427190203702110082941182445747351059828373322568226456531725393211783153960840529795259415815418734824402354712457959514614696929377722723462178179443171913686244764879179915903000867826075583146563753425750182988320148220780878866151006211397163154764089822491314078137416299831631086034248673415500002509000926608624477641285858209226393575546250422765373621355237414972021443996227306219892155296063748934345782823445103778006691905572252636977851466397038878241731192297099822525760687511178742602531940851860469462347595611119863601959067989310549928508648233414606718972757, 572314064786368, 290555620233664, 290555620233664, 
    531566814648517978207501577992281223225957562689410909010909477636145889558758213277082330530778934468, 290555619971520, 3957317558990021763896597074513483777321156805350689660184779155668186796641584776610130369817004664743966618729157637333945775665309284335129430047629605578506187959930150470, 3957317558990021763896597074513483777321179430508008949843914401840611926891679826522145216615943444482926970830029219585733195874021530996831939694250207091012304685431217734]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2923059026737561881309746369607612760256872985410, 1132583016536257, 1128184898717761, 1128184898717761, 1128665935054913, 1128185100044353, 
    1128185100044353, 1027663288900614986408985390262045554256270899010, 566266213962688, 73671716770240, 73687152268224, 144058043995072, 
    566266213962688, 566266213962688, 1130383991247041, 1128665935122625, 1132582949492929, 1130383991247041, 
    1136981268769601, 1136981268769601, 283958550204864, 283958550204864, 354123283435968, 283958550204864, 
    847200561402816, 1136981268769601, 1136981268769601, 72852317671872, 283958550204864, 73671649661376, 
    283816816153024, 283816816153024, 144040460947904]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128184898717761, 1128184898717761, 1128185100044353, 1461551814199050063162363173862378288981691597635, 2923192831719176615430003279112310561573561185090, 1128184970025153, 
    1128184898717761, 1128184898717761, 1128185100044353, 1128185100044353, 23014456880272322966934778201244376397464482626, 91279338312640, 
    163849253295040, 581659376751552, 581659376751552, 1128666136855105, 581659376358336, 1128253685371073, 
    1128253685371073, 1128666002231489, 1128184970088641, 1128185037199553, 1128185037199553, 1128253618262209, 
    1128253819588801, 163849253295040, 163849253295040, 581659376751552, 1128184970088641, 1128184902981825, 
    1128184902981825, 1128184970088641, 1128185112705985, 1128665935122625, 1128253618194497, 1128665935054913, 
    1128185175747393, 2923059026716252532891576003668296306131812296515, 1128665935258433, 1501503365767945621989761726681307534140041129036580497413667840410145483033766639513220421855818461523524395536512446956438524562423287501135917765839484504657167208983096030445300165355422273819046893991067039745440641454143792312762995591897752862447379456746988553, 11462626758536582302583909586791404600526373699, 2923371238321452602275315853772966510340150932290, 
    531501997402235371604538329849018963974333629708809442753374553223559320445409024892059013950907502661, 1128185175747393, 1128253953946561, 531501997402235371604538329849018963974333629708809442753374553223559301192965533925820837409181552709, 1128184978619329, 1128185175747393, 
    1128185108638529, 182866459800280701675939303819557821249100985154, 15015033664604734385304966506489959399580110773953330295600086866903864083866133108599072806387146212049676744485611025026121041177544918919333576183636804355915796642970539752525234420828523977933341196619934081471551228217639135762042987961378366151467009249877513, 146239484596672, 3957316619184925684297189135165343748734485785569124676029570219791433971881285648085489929242555540140270568007551389034031562785650291705819342222639351911062452182223642182, 73671649661376, 
    132877511029752925051748174825186803139028445692011376668635412537999079269691137052392711834656039172, 581659376751552, 365421404790046575088861852680708487679710593859, 146239484596672, 75870740025792, 146239484203456, 
    146239484203456, 1128665935528513, 1128666136855105, 163849253295040]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1132582949492929, 286156768940480, 145419280585152, 286156768940480, 286156768940480, 286156768940480, 
    426761113309632, 286156768940480, 88528152185409, 88528152185409, 286156768940480]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130521365121089, 1130383926167617, 1130383992164545, 1130452577419329, 290554681233856, 290554681233856, 
    735045141664704, 308438925054912, 589905311830976, 1130452710723777, 1130452710723777, 149817327096256, 
    290554815451584, 580834475119552, 11507228419573289408614916196888154110077174595, 290554815451584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1132582949492929, 1133063985830081, 1130452710723777, 1130383992164545, 1130452710723777, 286156768940480, 
    145419280585152, 286156768940480, 567648925520832, 286156768940480, 567915481928640, 1130865028501697, 
    286449363588032, 567915481928640, 426761113309632, 286156768940480, 426761113309632, 286156768940480, 
    1128185100044353, 1128185100044353, 145419280585152, 286156768940480, 286156768940480, 286156768940480, 
    162814179168961, 286156768940480, 286156768940480]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130383991247041, 3957316733435741279695094842938213246030297183398556868321880162344348709122765445991438030010671167740061116195955953666299513519953436211247240708567523686864530757270720070, 3957317617958184597672899128210835318733529284583726970371325177309938065765155744860584514291484461426826578489517421186915115795680661265044183667405405949615101025208716870, 1130383991640257, 1130383926237377, 1130383926302913, 
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
    308439596143552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [79449387438528, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 290555620757952, 290555620757952, 88253542697025, 149675458957760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1134850761429953, 1134782245514049, 818783921166709118066698725725881366947667094225228184714991456056091619568544099113791838402169530250058676024429793666892672165044120315040601205611771367809459306701456472100661027706902479237825725479564257465949941172216575374659335122883992556783555987955941050119922358925163278037033526047553410345842124307225280203244218861715068807574175702551345065348871105518155, 480481084203240450432080877190139154811989515053442435874789679711051441878947742999308991867259810455178929306174411043647158238990012390174971447523251346845261735809792534494360571389852383644920529181788705463993908147776879898660215625348204456461729793246959113, 1134781976873025, 149817327096256, 
    290554815451584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2923728051605758559929314933870742417626711995202, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957406596879099790595470146, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957404383269810945449276226, 
    290555619971520, 290555619971520, 290555620233664, 290555620233664, 2923728051604429326853024096770637962380425835330, 2923728051605758559929334276757643509464395952962, 
    2923728051603764710314869006777135611050905844546, 2923371258736026921429193020158236526728280876867, 2923728070659203411399535038590333965637616486211, 290555083887040, 79449387438528, 149817327096256, 
    290554815451584, 290554815451584, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 
    290555620757952, 290839088600000, 290839088075712, 853797363520448]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [3957286475397161215507271467758464678282920511704727498450596225747433248283068596185371699013391854873011680474393894354066091711414048032258511877057077388486965974225180230, 1134782178199617, 531566814648506648577238044788322869782431627444936453682351466636153651288060060779961551739649315140, 1134782048246721, 1134781976873025, 1134782245308481, 
    1134782178199617, 1134782115355585, 2923371239680027450535923395121142647858904961603, 1134781981137857, 1134782048246721, 1134782383799233, 
    2923728051603224709694219430450706072007199769411, 290555619971520, 290555619971520, 590189718410176, 290555620233664, 2923719732379918226590664828984032122686451073859, 
    2923728051603224709694219279334986466289359520579, 290555619971520, 1134781976873025, 1134782178199617, 531566814648491542382975396215709529811340286128523574468508095834682218610479466127616345303077146948, 535719680387928928508263142553344117905758614438823067324213593147744725932992870710078442010956702788, 
    4217746345661154897263197952045289589276152563663330699591193316812080037710027886911626353305625668, 537796239962114842500772471133007928991003666964535805698589647601600549965970226302406424082178548804, 33284258116097804024988001097606118023719077030435534339193063922667440404733838537696065762399265860, 1134781976873025, 1134782245308481, 1134782245514049, 
    1134713457082433, 531566814648491542382975399221116431783425397472412753114851174322809799513357274961440313220991603012, 162887181013952, 154219534356928, 149817327096256, 290554815451584, 
    535719680387928928508262249518143837791014998772725706683028673939927403060909686024192205328790758468, 145689729307072, 145689729307072, 145689729307072]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [74852829499585, 299350908473792, 299350908473792, 299350908473792, 299350908473792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [23014457560917385301969830696113236373271491394, 4169565881362077212660851155996506481707611342567675281637298081387612534227428990428032550565521795185925276334619633973587839830351751452761531630999914558983472905455661638, 1038343154854761125642749648409976747267357263027445512656581079382127357147827602280673836171055428, 91701014069372659985672593267478796450272392002, 149817327096256, 154073505468864, 
    290554815451584, 294810993824192, 294810993824192, 294819717976512, 294819852194240, 294819717976512, 
    312429352326080, 294819852194240, 312429352326080, 290555620757952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [185542907881716514983538333309578664332188726082, 299351712993728, 981449509505353238871313570943092176245494822015250209404988843581513618466218028789892439123878579809184623934098679028081147322955664436856728207906921311678116421308458661666498766573933700848086566929369723974833493282212757000291371566481768977052729864249837512, 159433623736768, 89084140327872, 159433623736768, 
    145221573677249, 145221573677249, 299350908473792, 299351445344704, 162814179168961, 369516446224832, 
    299351712993728, 299351712993728, 439955252842944]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [79449387438528, 75870740025792, 75870740025792, 362919376458176, 290555619971520, 290555619971520, 
    290555620233664, 290555620233664, 4153081087726013885702245672149462584160435651081710015101107350678394278549906459400339478532138779635872324045196186797966625519267032865624376304983622028480718923288770118, 88528420603969, 88528017955521, 88528420603969, 
    137871296185277590929123653149795973942921910054426473123275364300250292407580530529559731306050501, 14272531393547573756878262903182275079827620675, 290555619971520, 290555620233664, 308439863661504, 75870740025792, 
    75870740025792, 23014456880272322966934778201244376397464482626, 75870740025792, 75870740025792, 79449387438528, 23014456539989956041034883063490866391518559042, 
    535719680387928928508263128814341137462336024532963996468164481709518578945588176144112556277596595268, 146239484203456, 88528420603969, 88528420603969, 581659376751552, 581659376751552, 
    46028913678132195818436124369258700730615739202, 148440587833792, 146239485120960, 158415729988289, 149817327096256, 154082229621184, 
    149817327096256, 154082363838912, 149817327096256, 158416266875585, 158415729988289, 158416132657857, 
    158416266875585, 145277412446656, 290554815451584, 580628593525313, 286014900801984, 286014900801984, 
    286014900801984, 294819717976512, 294819852194240, 294819852194240, 286014900801984, 290555620757952]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b8_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_15_0
  · exact tv_b8_15_1
  · exact tv_b8_15_2
  · exact tv_b8_15_3
  · exact tv_b8_15_4
  · exact tv_b8_15_5
  · exact tv_b8_15_6
  · exact tv_b8_15_7
  · exact tv_b8_15_8
  · exact tv_b8_15_9
  · exact tv_b8_15_10
  · exact tv_b8_15_11
  · exact tv_b8_15_12
  · exact tv_b8_15_13
  · exact tv_b8_15_14
  · exact tv_b8_15_15

private theorem tv_b8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_0
  · exact tv_b8_1
  · exact tv_b8_2
  · exact tv_b8_3
  · exact tv_b8_4
  · exact tv_b8_5
  · exact tv_b8_6
  · exact tv_b8_7
  · exact tv_b8_8
  · exact tv_b8_9
  · exact tv_b8_10
  · exact tv_b8_11
  · exact tv_b8_12
  · exact tv_b8_13
  · exact tv_b8_14
  · exact tv_b8_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [17127037648222892492088832191254553169902965570, 283777154746433, 582844317977153]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [531566814649450785657876671288681220503688302853484592960740319957002482245795571941930208402616893572, 17127037646893660693337608468486652373311165250, 580097500210033313530898337995684528076011922767533640754824706822032104335926480804358259074734813445, 4217239466888111472080135976067652861039486865225918470277087897724297538690784805359646959838753029, 736459918326967617751318358941169962342263296834, 7183928146899061435596309662811766136741107616290310352614994639126500500258252057811767340437583125166951900436082250995933202699149936537169781316321064060200992343110709830, 
    565252131457089, 265755022059037528606049368800710091551263626200569041458574813089957083939382782372282748352089616645, 532345381924043839394587231136638827431788164464791843856115421029898438119305033327835291741453566084, 864534085750463775437472024363696010114125555654840099293960090748314830633476077024791732707501601029, 864534085750463775437472024712642697737387749635444326403721610387307173690719351504776013275949232389, 4217239420481885636211884274333769221249619918406470700198229186599272284172188406363180931167305860, 
    33283751484824631724446758486592626339414626909687001650335242193193514332911774179094313633661075588, 33283751113574826881504406806559618149486719339474108751154924911311664747493418279123291655557628036, 635621412981313, 265816731696893447730563627300450531955463919580844976519612206675101608510758985677817893879145578628, 582844787739201, 635621412981313, 
    72671459560001, 90263645604417, 91433404103817034175472404877668913798921065282, 90263645604417, 91701014067046502415986223887064516432297464642]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128322476216512, 17127037646872890872075751183139343257636442690]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161224003915968, 1161224003915968, 176061585821888, 583925464646046210032311089356028699147815484221798688925240876006685493968757625095968313786298629, 864534077834335084935312622230326113563315144255024245805499798786670227865183464886039064456182427909, 1161226147205312, 
    1161226147205312, 176063729111232, 176063729111232, 531501965722252339719151417893749385982748779816580615547198072437728481677236116362894153952498470725, 531502947801800442927492773163467800021002412283954851203799009110700548564465259687142662424228129541, 1161226147205312, 
    1161226147205312, 176063729111232, 531501965722252339719151418108316485676987136331602392411780810924942144674025080804788654475924918085, 531502947801800442927492773378087309851561709642737460745710913759943762170011643001940428365979052805, 1161161866217537, 1126054660018368, 
    1128322409107648, 571823633729601, 25690556470361908551796657728989377012701857603, 2854593387065901417756765364343888381097805635, 2860081461121140688163781291040791909445928771, 1126054660018368, 
    1130452710723776, 1130452710723776, 1126054660018368, 79251551291457, 88047375878209, 183045910556442370483193694712342523505812252227, 
    183045911917571838166947548565840953232885098051, 1464361708073129500882287014911023686260772898627, 1464361718792024058891848614007323820361471559491]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161187433711681, 1128322409107648, 1161224003915968, 1161226147205312, 1161226147205312, 1161230450561472, 
    28545062745826614654542989170976931924500550466, 97053213332570484226080655576251206069664092994, 1154573452716865, 1136981266672449, 17127037648222892492088832191254553169902965570, 51381112941428673778384513130846816218415895362, 
    97053213332591253492742957401029665648524923714, 97064015256046791763327138764567979698629382978, 188397414114916412921459845941395364508742980418, 371085815679566731778893623022126762229179093826, 97053213332591253492742957401029665648524923714, 1136981266672449, 
    1128185173650241, 1154573452716865, 1136981266672449, 1136981266672449, 176063729111232, 97053213332591253492742957401031635980878091074, 
    565252131457089, 79267991980097, 97064015256088330296651742414129120997107831618, 565252668803649, 582844854848065, 91701014068043427215791180862678754279475385154, 
    90263645604417, 635621412981313, 72671459560001, 45850507034727868674423523919561280953562174274, 365555209772865926674932633810841226960567276354, 8304733930652940451719901982801144768872511916180091368422812893583755779612095459060107662362852101, 
    565252668803649, 90263645604417, 365555209772865926674932633810841226960567276354, 582844854848065, 91701014068043427215791180862674532138718597954, 365733616415018905501941846483771628716151542594, 
    91701014068043427215791180862674532138718597954, 90263645604417, 8304733930652940465918776659426651251968052435512311295033709834475181099316037308248446282189159173]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128184902914240, 1128253685371072, 1128322476216512, 1128253685371072]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161359425540288, 188407867590598995433876054074561682760154485570, 1161567737680064, 1161361579315392, 1161361579315392, 3957316694277195614994462503114144769307033463553815450570712339360431478875808051027300363013679535835988814037371459145822003524327253094666992703914056043273343831721852486, 
    1161368023863744, 1161368023863744, 316943093993920, 123695392443150858820591777138244336291396694676127880012348308470959859752155427914208293232690456290052550212304997480296464058885970099943991227515690800865161044104835654, 316943093993920, 316943093993920, 
    4158272566466870091383534110015526725823507602172611964368012567025801406072639159820665750206038811210420242480599867612611840481838974266754348767068266256736676787880194630, 8305224599154052166240680337390790880533226594906252264505150666555029609841015119145792510836663173, 1128184905009217, 1136981266672449, 1136981266672449, 1128184905009217, 
    1128184905009217, 1134782243211329, 3957286482768179819527693281777222988744025692529400894336606579745787399523653660005104903997793704485635937785086124867479542972185660668685346054004184135500190241041366598, 1128184905009217, 1136981266672449, 1128184905009217, 
    1128185039297473, 1128185173650241, 2923728051605758559929334276762255195482823340866, 2923728070659203411399534953587449043607842539331, 1134782243211329, 1134782243416897]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [3957316615500313528950177876272529048288155726323241007950100135606601638602707211682971658053146511087598194634684540582714916712758322068585638751562374493544121597921766982, 1161363724570816, 316938794832064, 105624529012801, 2928712374323320047938245962372078769276222703427, 105624529012801, 
    175997568162241, 105624529012801, 176347343753664, 316943093993920, 28545672530831212176498446389348751566034175811]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72670922213441, 72670922213441, 72670922213441, 72670922213441, 565252131457089, 72670922213441, 
    3957286427485527111778661891715742980289809403316088108006812304106211422999039621404241934815456337522369217595597205168907777035615685739308012509164487438563703315090062918, 483126158568166773286909501779970166293965445751328771508515819887039896711342775527383807904754446294375835299554364434992840876207573631055366108494586633598600090537543, 66438248635027102813124237241583724451367411898321183114968081856330380920148341789161228046255055749, 1128861830156480, 90263645604417, 1130852545335488, 
    1130850397851840, 531567321528223829083112477940278025149321491870621794526642264114536414428678258513495851721554981125, 290348657018945, 290348657018945, 571823633729601, 4156413866686451810832326196060372877436855084233147672601697993894557969979166837109979602874639428, 
    265755020079053651050095576156439049301051500042492735491114711641518192903644689350718400806121743428, 1130850397851840, 290348657018945, 290348657018945, 1135250596303296, 290348657018945, 
    290348657018945, 88064621873217, 7172636365189588363607176903218687066369439733807998790634610167874084306646520189772781952105100223448952502443576991264467864889081323692101356298190666226274334673064686150, 88064622348865, 8337158023001882817957897760808819414583201386663325808079021372038858755147760960532775459931296645]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105656740808769, 387108095404353, 387099505469761, 387108095404353, 387108095404353, 28545062745826614654542991458373197064484950850, 
    51381112941387784284643108696242918232703374146, 51381112941387784284643108696242918232703374146, 105624528554049, 387108095404353, 105624528554049, 387108095404353, 
    316739351030081, 72671391975489, 265751027411102706756237512144468974075086430320502062773562197266207687140642489186475377624210489476, 72671391975489, 582844787804737]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72670922213441, 72670922213441, 72670922213441, 72670922213441, 72671123736641, 72671123736641, 
    72670922213441, 72670922213441, 72670922213441, 120767488680169918399165268622602027742280342653253821720913292993952173166060156901174717755653608896388921490676621337812874729538282998565782375796716427635844118130246, 72670922213441, 72670922213441, 
    33271586370207423225362517379271641444025622881879765386887142991792251164544817084110018278361776260, 72670922213441, 72671123736641, 33332411939486704944657046008029710304980157828119295232459058074042110255999289778370363618030895236, 265864505112980430064054871127573132045062604100017069507878055920428296329654291468208000923686781060, 1130865430237376, 
    1130852545335488, 33316286455908288431653864251073937295421064613913359060191156043765266418867650724910935830852333829, 580628585138753, 72670922213441, 143039666391105, 72670922213441, 
    33219377757379689231767999864837256539143287023814230887063087914783010345376625869521044950162358404, 72670922213441, 483126158568163769937114868838473761282906949724489379021146262218300713330482029180406315665268527036589376086788127675677396458423267940772876637767459893707276340376134, 538769060929150387167605773514736849148931784373987043094044224405439912097892485073146163423969820804, 531502440922005843165199561779563581526279536531015403399888381329382996547219661043230978952084603012, 143039867914305, 
    72671123736641, 33219377757379689231769648545196138159099370861916658952561525826930787176297493145768920413961994372, 265751470930873414351167473664739559899181817133814433227980523673316973249952494835606557719617880196, 45716876276521919775377038403397142598434424387, 72671392434241, 72671392434241, 
    72671392434241, 74869945468993, 74870146992193, 74870146992193, 74870415689793, 1135254891139520, 
    79267991980097, 79267991980097, 79267991980097, 79267991980097, 79267991980097, 15473245945369894448001434783851088872574696671724011500879922843173615245921454298091071963540449087871393778004981174911518632728687379280258251530001274588972188270112326, 
    79267991980097, 584559057550438947336412874517033992483262275301403858786902727587776963513328081739992108519145604, 88064085002305]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [4217239420481885405707907810651761728937077123331855913644263850413340052916094075713140544841582341, 580645764483649, 736462602474296063222552360384525036875883775811, 72671391975489, 72671391975489, 72671391975489, 
    735038153295407254265949365575100471625558102594, 265872615188757442269524184549658156030712485687293037900285592807355900378626447750940012429883326596, 72671391975489, 265751470930873414351167693488783971366646566571538298686022043057095441248342488877933403559581466756, 265751470930873414351167693488783971366646566571538298686022043057095457831013613220635459541319041156, 79268461742145, 
    79268461742145]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b9_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 103) (cur' := ⟨4, 128, ⟨1, [1], 1, []⟩⟩) (prev' := [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_3_0
  · exact tv_b9_3_1
  · exact tv_b9_3_2
  · exact tv_b9_3_3
  · exact tv_b9_3_4
  · exact tv_b9_3_5
  · exact tv_b9_3_6
  · exact tv_b9_3_7
  · exact tv_b9_3_8
  · exact tv_b9_3_9
  · exact tv_b9_3_10
  · exact tv_b9_3_11
  · exact tv_b9_3_12
  · exact tv_b9_3_13
  · exact tv_b9_3_14
  · exact tv_b9_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161223936807104, 736459918327297978899165597341552335018518385474, 583925464646046210035169311700543112495737370560400340818668355485842552277242833726014485576085765, 864534085750463775437474882934987212150735677456850815001953192888646404129005235325752764740876169477, 864534077834335084935315480452670627976663066141362847457393226266149384923491950094669110627972215045, 1161226147205312, 
    1161226147205312, 176063729111232, 531501965722252339719151417893762462925942139568124456122449636846320815837917288747685935509512048453, 531502947801800442927492800212142591656481473626200130652390132322243859993997061955603779569957858053, 1161226147205312, 1161226147205312, 
    176063729111232, 1161234884202944, 1161234884202944, 457547442557376, 1128260534735040, 960962612589359618611532028395910518637252014413543773330069459706170758439299782734078755443486714569017602045288140747048921804864955815265939563464113987987469071467814027691857435877016470295355846966495759488133384841213134858544021695187902629243518976496988553, 
    28545062745143825013019818964169652391813059394, 1130453113376960, 1130453113376960, 366090429703230115313587427253627290567827801923, 580697312989888, 72709569515712, 
    72709569515712, 283816003375296, 72710575165632, 72710575165632, 2923059026695296463256125385836157452557299517251, 1128665941819969, 
    33218934237609691583668613635874583311891039549343827778229614350553361667770860123133092347380394565, 1461551814178093912396959819068707169171268536131, 1128665941819969, 1126054660018368, 1126054660018368, 1143646997320384, 
    1130452710723776, 2923059026705660287785760901782706508930421393219, 580697312989888, 72708431876288, 72708431876288, 2923059048473388756027668556620251635663845263171, 
    531501997402235843687492455450506644845432665480153217580199048554386459247388094160394534954521091333, 72723462623424, 72723462623424, 72723462623424, 2923059026695317273087606894964276760030679729987, 1128665941819969, 
    531501997402235843673079032506535546116741675871973025046324523990657685167589542340237534294613187845, 531501949882260587742187637716362761982646324171242140837005543296288403205208274621864177852821496965, 2923036725949931819777555688761884860089402196547, 182711399378464490998058473316705092375557505603, 1461551814178114722228441328787122287003354335043, 1128665941819969, 
    284241213538881, 145275193659584, 426761117503936, 616365761228219484124532512486989478989026516792404629457449633611717112559284693155219963303393157, 145290695807168, 145290695807168, 
    145275193659584, 145277404057792, 145277404057792, 145277404057792, 145277404057792, 426761117503936, 
    426761117503936, 145290695807168, 149675450568896, 149675450568896, 290413073141952, 290413073141952, 
    149675450568896, 149675450568896, 149675450568896, 439955257037248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161292857741504, 1128307777605824, 1130438081384640, 77290809659752224641570850565179192160923234364145788709667211484705319203405149708392542463486844026349131196025008409570121986007553342977906601907764302383224447972494919, 1161088708251840, 1161088708251840, 
    175926290157760, 531501965722252339719151420469812432020520579809320376335738600182426246611998906964769907020616164677, 531502947801800442927492776168874682799921604365435904672868736201476900440003457112568722406451433733, 1128329254211776, 1128253618196672, 2923036725960399412838459165826004253505012899394, 
    290546485563584, 1125917221064896, 1128253618196672, 1128253618196672, 2923059026717914074224623051664358617033226590018, 1128253618196672, 
    299634384704192, 286577671540928, 308705900893120, 531501997402235843691094054311519500343267002393897100404738314524961138709247525085326124978845086469, 531501997402235843673079034223910918672121260868006679184995680358192280525565684572186994334616613637, 531501949882260587742187613673107930069182383842798234143924738899107782116660007440795223046427593349, 
    2923036725950430201681676503727122060293390281283, 145290695807168, 145290695807168, 145139965104320, 145139965104320, 290555083887040]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [531566814649450785657876670215531265998023650808656098826945824754779869371771716067602040785765417860, 1161567670636736, 1128857199972544, 1128857199972544, 1130437678731456, 1161430097465536, 
    1135316702859712, 17127037648015521176116404669265403318733116226, 51381112941387455961885237871902540390912234306, 1128719626801344, 188397414113878274108121883777773022278185915202, 97053213331553114679404995237407323419041600322, 
    583925458845267951738859733850487746260040379428863801484293751228410341833749704057949946693043076, 176061585821888, 1161224004833472, 531502440922011507987688852142983278718900467173717559023594830312502731032005542366005473334201172868, 531567321528223829083115114109994311430434659402829629512586854342111017432851596892781981882271417220, 2923719688834201757094344235052742252880218575682, 
    150223474135488, 572298500248000, 366089384351810970051097662132651854132647318338, 468850913332476241393342124340705371628842799938, 531567321529186848906369252525030507086885214195230403430841780945585946778573305689494888430438728580, 531567321529186848906369252525030507086885214195230403430841780945585966031016795535089221183763399556, 
    33284591003420927995887185010945852286861332589745020583697714117032676458703928906999172695735944068, 163417622057664, 726367575478976, 33283751484824633568464494523555089167676467013013135550816259059624248911321348761768563879599948676, 588272456809824007104837722063016091387720654829062855177761045759635904597979223552704604481207419780, 265751030381101160251914697361723969332882984433199769663192756611795652540431116653601450114081375108, 
    567487725834432, 536173393131732473221824658039167194930743214246879833382176340556122612563407802937922744565755035780, 536173393131732473221824658039167194930743214246879833382176340556122612563407802937922744565755035780, 531501997402235135570264311189313421640219336353171926609452026235394949189442263659222039013178438533, 531501997402235135570264311189313421640219336353171926609452026235394949189442263659222039013178438533, 145825419235520, 
    567900445348032, 145825419235520, 567900445348032, 75387955581120, 145825419235520, 567900445348032, 
    4089164710033246213007359302831900118619751789091336403577432068919550416531602826166131596331397418295608575317451779870038257680246550460464513413204197249443290193646794822, 572298500248000, 48615820536105127092036639525625565032912853826, 75387955581120, 145825419235520, 583925458845267951737703940248531844532762451988572544967618062614739171873337456959285311358387076, 
    97058440069710812891172945498690220517847216963, 583925464646046210034081354418241042661840817254311917046424852876302661184584746808078170562249604, 158469400301760, 3957316615499431320073279171356055356640806737271037387578621426781415056028509443995710752171430173653479517965134612880364053994539135199775553254813707141174889720749141574, 1161155217264832, 1161155217264832, 
    1161292656283840, 1161155217264832, 1130918647959744, 2928723415900934047177917684730361642551275950914, 1130918647959744, 2923036725866004101741512453434809085573065610050, 
    531501997402235843673079044649230570505784453332728509252041570760871091146180489924269695899129867525, 1128719626801344, 1130918647959744, 1135316702859712, 1130918647959744, 531501997402235135570264311186221226746162484336017757929155529576925215960945709054439538734792930181, 
    2923103628355648394305329106798367155052724884290, 2923192831676724883718833713134832355930517017410, 2923371238318877862545842925807762757686101283650, 2923192831676724883718833713134832355930517017410, 1161567670636736, 1128857199972544, 
    1130437678731456, 1135729424470464, 1128857199972544, 17127037648015845695908003135277566749652816706, 1128719626801344, 17127037648015524979065825272171215012684116803, 
    316805655040449, 316805655040449, 1161155217264832, 1161224003915968, 1247177207726153154038098006463783627512013935540556657255957341792308789515530887164147822323305077106444814543144337664534432445601373800292744158009052914568042473597228498332232016099205100591132002347970619635020768845287971045613598277091314578401715288978575512370808464068486039296824623733615911617759429979852429486579668204240116108636468556611913406049787909100141194856168082024173730554763263307787636383861869959621288495660086336258626231393854654835659388212755817542960512741996828805180838605, 457547438363073, 
    6708399811944600532696790260259951571040479240051968516421583058712088867290078696718685866546038411240628912750561834603132311364113411708535990469257654854352837583404424268659640372883950977796194427357578042569542498057993380188801544155629728195874827015738305897197467023565797731950776408653067675339721065592128268439817412731078011281434893083385607104129505732685569994, 2923093000658592447980588729320906541032651365186, 75387955581120, 2923184468907743145133108082163167622172900332354, 145825419235520, 567900445348032, 
    567900445348032, 567900445348032, 145825419235520, 567900445348032, 567900445348032, 567900445348032, 
    150223474135488, 572298500248000, 163417622057664, 4088711893740771381379342781570705588355041718546686461865956551833091056979001689259706078246673102461641861758876481651394960237778308818600589732665575540508959174895291975, 4088680758550766603663186788895256365551859281052934693262494430807046741427580569272915901763208230240158394410557170796722151746126804632888888999814504053372436762085772871, 5943689845820892525614169358606913244565983263799167975061115907447897931742273242825163341625885070030477437674817168824359940889667872272086270926918750495800260946856726087, 
    4156914883483758559037819094677424841245519974828175105429258045252729027828858792872370962157519825261188057460420608821342408373016711842984249957565284324867846252588399174, 75387955581120, 75387955581120, 531566814649450785657874923644777402671711512750950096166187421880228096476545768604771935376345656581, 531566893848442985190980866565838473362175657068085156194334670639486524708682131323076016230238514437, 531571883445859728093837140427385603055051674628485481986039667203719999726863377092585856122263694597, 
    2928712984110318495059646919007336485032694921027, 531570869686387601568153503727630526490278533116331828309879491542255935320824782891380597688808762629, 457536835170753, 316799212589505, 573090402627753161486516680442063703959110230998250254501814378422345183133386836856593180882663369989, 1161226147205312, 
    1161226147205312, 176063729111232, 105697136611520, 531501965722252339719151423904563279495021731943489772826169363790960182818720811989963073500086913861, 531502947801800442927492776168874836345243619789674959719065905041382141120522107549359433573069338373, 176209904800192, 
    531571883445859728093837140427385603055051674634307017238631939284793394299748016726684783022796296965, 5765546543805391563381780853924709238853624682097217448921726523468025461793079394510719890329506292334581915161575705468453578308586525034010986453615906510312346773100078665067648387915358846855909057087186876963248649396505118130469297926964670254424586939775289671364395982823310298858079850647811093277181090444126629903772184660246131597635875438683587919322208029585893199611206498981318469703717996563450588773344431184468919644609481036814239641229991500152062498059281126567201237218232663977172259898049225722777032659423913577198986090325697532848071351329209458223001837673945158940115854156118206461248249421624167973432496560291193165935280010318, 960962622081764875629626206472676079327277374874781596525940651435555211919219491956045054884581775322130128040816507807391756922398468586404677883594024464416976494615298378463982072990360767319256278704350223481788764373133723322703744936524768137806086665249159113, 531567321528223829083112489960438149198804376545405962509925864369240606676787603297008608290488446213, 498163040104781343237773855974131845671883293734900061591288853416102642426126664740991463430876311546798842261167452227987070440949729936822730459775297266512895993151046, 158470075584961, 
    1978643215499139501480111932655952016112534566834475805791071227488675193942005186071021224849202533326164437654398232696305278986913238729826204884776110039015596004181245510, 531501997402235135570264310958079900145370019588344652262386231054880777405460864413218623075942395141, 531570933046339975351025529152217806744001312836172523151030541854518295425420727207725108521830968581, 531566878008451469248290982353197500484908746764260403146110055113348118614123168029392104719075503365, 573029577058473879753042511740591927632196194220010271288749486527830739361082369979707865783388597509, 580065067795137711352198537675952974095634500654255594392466282774296572246853319550668779936338406661, 
    845848463271169320889720537581558360560352067589879993421898280056435586169264105873082000454702066949, 1161161668104640, 2928723415900943782137840300818112327337581220674, 1128657353970112, 1130448688787905, 1139244781810113, 
    1161093145956800, 1128657622405568, 1128657622405568, 1128657353970112, 1161093146743232, 83713619669441, 
    567906896187840, 2141060067972986641489962623164648584329336648643615261780286032027624403642692542209416202924647813, 290279937544640, 285881891033536, 290279937544640, 290279937544640, 
    290279937544640, 571754914255296, 84190499443136, 84190499443136, 290279669109184, 290279669109184, 
    1128184902914240, 1128184902914240, 265750998701117656297987067882619201884752896315138283728167663002607021333567544911934299148455787716, 531501965722251631616338442218049409810977256899298335935140467231180271690690139569227184024003558596, 1128184902914240, 1128322476085440, 
    1128184902914240, 3957286424721394476491768881696603703764903848770318166983563251748963750950720875776116900299057653898949913151443479566117111929768128111805849987853224339449133021034622534, 1128184902914240, 1128253618262208, 1128253685371072, 1128665935515840, 
    1128666136842432, 1128665935515840, 1128184902914240, 1128253618262208, 1132720388509888, 2928723415900954166771171451729943110773217694530, 
    531502440922011507987687974671307298852662048507390360985377533966238448980290142687871096523585766276, 531502440922011507987689092682674858058762562534550482365951843008846848909657822635018625080409473924, 1130452711641280, 531502440922011507987688852250109597757980193307108025327280121064557086841128188820814364705948976004, 286852968878784, 286715395707584, 
    1134781978973120, 324403033014317025013452792266667442372935340253882132342696783432637782545279639989094591330794692, 4217746346624174720573599191810104277284258825278847475284504038723048479123082296576017894662751108, 145290293153984, 163432654443200, 581109629850304, 
    581109361414848, 581109629850304, 581109629850304, 581109629850304, 588487381307595738173260972382405858427612365104210263548053294057725871279884605134159608817087365, 551485155253820933266062457466958802287893320397053648910289043412412566816064778898896028883501956, 
    88734717448896, 88734717448896, 158484847923904, 17609920615104, 531611926944997396214937028473237242885810934252985743261324043754692474276252932131217526814432621445, 2923036726630994937979604706935186254505541940803, 
    531603816869224160557794421692510497801572667029234137886465081566064330350184282770368033773436334981, 9042944782536846948981574166627399384240643254729415806876483399908960075083700666305630933329541281120252144279941072681909659073634594233748546498717607458168238828801226850598750945948754662264210069070974874528169444898931430249236626922479839826117199391725617344618981788527846260228495579665550673031316916090798298159837853403385648407187671823781718449620485187056231523094109388927738353668614156036286506608615737073627204495869010022507472153706766435673749692708103639517440759458073029766121958297840681360429813054107229533120379736878137601663210742718151789930403767338023307073435587343373539126231654575845691833392481617869083186773305472079, 571754914255296, 620927684415644561850433813933519344039768284032471916290634555454224506920342868206084506728067973, 88739012416192, 88326292902592, 
    88739012416192, 88326292902592, 158484847923904, 17609920615104, 581109629850304, 17609920615104, 
    1128184902914240, 3957286427485527111805477507569384677388197674250739130133679843330344177161886871364396286693745900158590414288783911075530269644634508248180068241927249497143947173663039046, 15458150559956068225851132506395768897505380072025275592247127570063413516556477574871253652817132357768580923120990472391055479711629950492811984558738419483953658559248454, 1128322341998784, 1128322476216512, 1128322476216512, 
    3957286427485527111805477507569384677388220299235443485219793535927361868708015771026928091028424586370231408205400553554704717834826420744770438476709824892964080813810343494, 1130383924072640, 1130452710658240, 531501997402235135570264311189313424789097994856964839028254928206704809287030184532281305013660382085, 1130383924072640, 1126054660018368, 
    1128184902914240, 1128184902914240, 1128184902914240, 1128253819588800, 1128253618262208, 1128803575926976, 
    1128665935515840, 1128666136842432, 1128665935515840, 1128184902914240, 1128184902914240, 513262575315785713109034988782640296760438075564874281050404844154274029506142137894678607691033726719169151741943392654207284151724912364701364137612662817382401486847558, 
    531502440922005843165168360517650923420049720453808618315725106908818067518490724000083675379693482885, 1130383924072640, 1130383924072640, 1130521363091648, 1130383924072640, 1130933680345280, 
    2923192831676765773212575119852364948226399277890, 3957317617958184597672899128210835318733529284583726970371325177309938065765155744860584514291484461426826578489517421186915115842779835124340859742328616267857262782869098055, 145290293153984, 567915477733568, 75402987966656, 2923184468907784034626849488880700214468782592834, 
    145840451621056, 567915477733568, 567915477733568, 567915477733568, 286852968878784, 1128184902914240, 
    1132720388444352, 145290293153984, 581109629850304, 1134781978973120, 1134713457087424, 531566814648491542382975402655867125712604534182343094559084769091438495039565119690337711506354922885, 
    854063668270016, 564753244728138667426549824804832936857197572353657915528302025269505665617763235087476412594248708997, 74921548976320, 75402987966656, 551485160692050550417311503508924955102822317381147886419659577387906864949760757409782676147399941, 88734717448896, 
    88734717448896, 158484847923904, 17609920615104, 581109629850304, 17609920615104, 531619530141276267700557274461832567872510859927455563127685597429878351681048325215500874061692957573, 
    1152443081954241, 2923192833038372936644108241599170256640816525891, 3957286427485527111805477507569384677388220299582027196984895393375837913017288150570427465748796558364407671689073224107731583576405032560314521241743654677499927470207360582, 531621304220114566579311466517790443780762697499375362972412861988920033155938131641706009295917052805, 1139249076646849, 2923036726630994938058832869449450592099085922883, 
    531501997402235843687492467472134252733671676030216951097768158067712381864492650594342072099700955397, 1130452715180993, 531566893848442985190980866672964793598485295766810494280377852524310527398721297406382222870032315269, 531566814648489654094462052604028532705188804688722680103002038427226833581283017925190032782667567813, 3957286427485527111966371202725574094032889140597186263575005487352976806448171469348412931511057964323469129069035747318896766787336906825039053124343215746957859156389787206, 531501997402235371604541297741964151506216033423071027041039861554875986665903073521979653874969263172, 
    2923036725950430204216955942522701377235549499971, 3957286427485527111966371202728695842583131401649477762975031414170829524684296566292761932369683376308712280406635099414929226811327379038331897721684112069552228584306767943, 531501997402235843673079044528163154004980686422036758563893633503983607784694098774185071439793051909, 531501949882260587742187613673108083614504399267037289190121907739013022797178657877585934213045497989, 2923036725950430204216977704220474343531477021251, 531599254951833737190261037788891176835599359486611574790707312678322450338710135540840952138345902981, 
    286723994031040, 145840451621056, 4965524312256, 145840451621056, 531567321528223829083112490067564469435114015244131300595969046254064609366826769380314814930282247045, 145277404057792, 
    145277404057792, 531567321528223829083112490067564469435114015244131300595969046254064609366826769380314814930282247045, 531619530141276267714738563214905156958426445603439588578291278991848682840088774444118010874955199365, 2923192854816444419584169903255145132273982059075, 564818125334475614618550950192590259501422762557165747307180348102220756654690576543213284270098772869, 620927684415644563707507341121597685815827987103676199989793951083527565801715557062422710882562949, 
    564790246948754212628487062889464454458873136558678826990690777214378100779477850453582005435399304069, 2108619717975313787150224753205593936726681773318370307879175223363819179513068222487405634422848708, 299076030566848]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161363590353088, 1161372188938688, 457684747293120, 531501965722252339719154054923620842382943073863194746847215318581273412531203308930154874776620290245, 3957286895545320047684324152697190215460328994723811010032159418551240508765011011656093113401066740197270669707185544458374033086002083608781505870440065925052715137907707463, 183402028136003777047981820951956254012701938498, 
    2923059026708588703916805937637658523034563684163, 1128184905009217, 1128184905009217, 531501965722252339719151417920491632846355695692230599568003510796252425001259351840845563008562679621, 132875517170550389995170533287665926974926292182759724234016112881086454304316730003152848783060422469, 290547022434496, 
    1143784301793984, 532150803464395994019471120612925425581683005071228924699805323479776131689220120093646667019365939077, 299360311317184, 580835288289984, 366447260679601595232441744360331160705678013250, 1464361729683385958228367264307970878966786495298, 
    531501965722251867650610633661219106744185412828122805170181363005037459523381512813604447443378112260, 1128184905009217, 531502440922005843165252786462039503554732626320041788730406872687119042335871490349242237505337952004, 531502440922005843165252786462039503554732626320041788730406872687119042448678776989442391342697547524, 3957286427485527111778661891709499483189185650736353921291864555387401284297164156314711640975370513437841933193535298173972260951140545150745060827815217239379841723857320007, 3957286424721394476438137649976833315366653176154437649223098666730968447110778018860828294938687848067344550413720092278019129604307447871960093313879881416254084158365912647, 
    1128184905009217, 2923059026719907911147649695641101884030819315523, 2923059026719243297149786251924321154639581488963, 708382399926976, 708382399926976, 426898422239680, 
    145414847205568]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161223936741568, 1161223936807104, 736459874770490077036656962443802855532167959362, 1128376031535937, 2924441672899911360232830692776385730388248536899, 17132569276842963758942894458877969427712709442, 
    2923059037416497019607617077339783922282026575683, 1161088708251840, 1161088708251840, 175926290157760, 531501965722252339719151444513067647797196131885407859134493585748542302296823136804969098045019258693, 531502947801800442927492800212129898576597156441523387471623721767592956124827686952767913430854527749, 
    1130453113376960, 1128329254211776, 581110166721216, 33218934237609691583666909999527528259666470571293729925408031746124785775645461420082708091324856901, 1130452643549376, 1125917221064896, 
    1128322341867712, 538249572559650780434327630488443664821067304944032966968481131831819520575861552226698631316437746564, 30916771933042085333677033581040167259693948064636813691768121346216332103619348066374811270878255721463881783066253609013140969715696206579767960912301408354198607275404871, 72708431876288, 531501997402235843687717581032614575861391224547131243810491947338227115546681171775854569142947646725, 3969483873812212976714719816551295906464006405796989642144884820698117717773515504152218902946852506597666881492936776927823583187995738983175183776715986691576178100842494534, 
    565373395538112, 531501997402235843673079058267166134448796812944094161983750665924308336210389914412386185359019707653, 531501949882260587742187637716363145845857935918885716942679724465223837801484237280994414070830687365, 531501965722252339719151444566630808713504228262014033289359296502016110568898290711894509389024032965, 145290695807168, 145290695807168, 
    145275193659584, 145139965104320, 145139965104320, 145290695807168, 567503160873152]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161359291191488, 1161359425540288, 1161359425540288, 1161359425540288, 105624528554049, 105624528554049, 
    2923059026737479007375425761442089216273257891651, 290547021648064, 1161363590353088, 1161363590353088, 1161368023863744, 1161368023863744, 
    105624528554049, 4217239420481885636210232966340289828250149733726928783093352156513225234754959843739967953001791620, 371085815683523277197194658833636730835751162690, 371085815683523277197194658833636730835751162690, 105624528554049, 105624528554049, 
    1161368023732672, 960962154094212046835217857624440951243359382280253876264893850380835515611741996856708671079025254350731094848425145796623168453896190240269858365617863227668398236089863249564802476723289549794058256179038036245182003101161605902052319295054911639247667209246991112, 6707465088723695756462041669331607964978116025472644350312872008527489413480729830512419985040705341679014593577293636015152851719097600080060587064390093537934797085498020123474091990892841928670870054808072299412796995442080958840777967305268552177695249957244036934608956092751207649814188340672475331458066490272673911114669261455367053602801241014268454621369879103925342282, 2923103628360840061931629001074405107699049110338, 1161365672890560, 3957286482768179819956743135535386095930348178230646954065738028966237612095302773053601914450469100015392539406461267834458960449239216820326939892006705969458722944478838342, 
    2923728051608344334045009583117213363704120234818, 2923728073386415816985071244773188239337285768002, 1161372188938688, 7759266745547319253286405420057648018066864838672616857503613119803756201174864708723931142728944457001551147887345846520452688574434985370577031972148370381021830207994439, 457684747293120, 457684747293120, 
    316943093993920, 316943093993920, 371085815683523277197194658833637856727068070722, 2923059026737479331895217359908101379704177592131, 2924441672939788230529992574441005578117548377923, 368231309409075616123813067285691943719626888002, 
    365733616418933912545684089864669696841167688514, 366090429703239870199702515210530500352336220994, 531501965722252339719153615275532006652570137262412858188274824630842858430845092499590867553765216453, 365733616418933912545684089864666319128562258754, 365733616418933912545684089864666319128562258754, 573029569385977991062543329206871533031607703794336986393630119107048318388191402639656131312520175748, 
    589639004577298987863247018000754467723838762161568901030871583389256377197630708834600064846559092868, 366090429703239870199702515210527122639730791234, 3957286895545320047684324152697190215460328993337475832443767591232826335975409918193526530398535854438722306993357705748399648561359926244415143858328033334515813041969974855, 580834751943360, 290546217128128, 532345381924043839394585579883518760766813799403198470323167934873088069873793464583804172138570858628, 
    299351445344704, 580834751943360, 589639443289024, 290555083887040, 290555083887040, 290554815451584, 
    290554815451584, 290554815451584, 290554815451584, 145427748885184, 154224118731712, 163020337582784, 
    736462602479280687221814511196224166611755504450, 580834751943360, 580834751943360, 580835287896768, 580835288289984, 580835288289984, 
    580835288289984, 535719680387928928508261480024970401444234395048665818726322902052461522331132749310634829804285150276, 145427748885184, 532475143136476034682091077451801690103529327796605807023763891870137536695965346756686447363676717188, 532345381924043839394585579882313327631432159996699317530722950499989527032300613490233454023581909124, 105639091177537, 
    105639091177537, 105639292504129, 17884798522048, 354321989374144, 283953446523072, 33218934237609691583666965009206201264992175936726138166541215081749984203085941297873794916599517445, 
    72848018313408, 72848018313408, 283954251043008, 283954251043008, 365421404795155814697691617168091148319335650114, 565716458684993, 
    565716458684993, 565716190249537, 145410548043968, 286148170617024, 286148170617024, 286148170617024, 
    290547022434496, 1143784301793984, 1143784301793984, 1143784436142784, 2925868931314211233750039684930286717407825302338, 1130590166454976, 
    1134988351509440, 1134988351509440, 2923728051608375487825929132853392514083903853378, 72852317671872, 79449387438528, 79449387438528, 
    105639091177537, 105639091177537, 105639292504129, 105639560939585, 79449387438528, 25690556512605786755728698461259928835195406147, 
    105639091177537, 538833442545653603971549898359340949138139035875343555794027661603074843226284019830748529924296163460, 538833442545653603971549898359340949138139035875343555794027661603074843226284019830748529924296163460, 537795352846196041671505917809303984629307067977304899710566740789200434624231069170398271956731576452, 105639091177537, 589699837819074158287220465640199794940294362884597382124424433202081580026956498315423974357863669892, 
    589699837819074158287220465640199794940294362884597382124424433202081580026956498315423974357863669892, 581395120223413659886868621239904078869638619700288133456737066691086311210532893032621910617346973828, 105639292504129, 583925458845267980549659432351538066009591859866842404431927786103222411337374398963862935378097285, 589699837819074158287220465640199794940294362890688827412714848679377385276826900561737105809799815300, 589699837819074158287220465640199794940294362890688827412714848679377385276826900561737105809799815300, 
    565716190249537, 145419280585152, 149817327096256, 149817327096256, 976699353505545380826580284877520846237313370823832512863114942533191954699736407355762870794418620034426176628734863109866748954243808121748479435376113563294841633282431643826228133490682269559413845162472587986846040920853157243152299899599800760337956904749554312, 290554815451584, 
    1461529556906314653900893307435014038844078101058, 1562283826109727050376938259828334937648753047743498104504564670668641427751756499369763072432789159437029274078261171316735873461737742528858929459841967522569582070147988437342773133955037450817556483580991416787870655791194956317728665244153384401945772072499877512, 536173836651502472713914947874397287372450340484861844360015307411017609996312711275585223616283034500, 708382399926976, 3967672427131056788308956829268865824658456987278220319423362771574025524348256775675854182128105910118180294204856902360070247850838893500186156380034177327811436263487012422, 708382399926976, 
    426898422239680, 11440630823719329552277192313789707955868799554, 91366501617913810513003605409236749197976277826, 365398058617465896121540455782912976648570688322, 365398058617465896121540458144096218083393295170, 538379777262849792601508406541496302455127224424086513133487390077685692352759756574456907328454411140, 
    708382399926976, 290555620757952, 580835288027840, 72845872926912, 283958550204864, 72845872926912, 
    283958550204864, 283958550204864, 565716458684993, 565716458684993, 565716190249537, 145414847205568, 
    286156768940480, 145414847205568, 145414847205568, 286156768940480, 286156768940480, 290555620757952, 
    290555620757952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161156223897792, 1161224003915968, 387314253637953, 1161155217264832, 1161224003915968, 1161224003915968, 
    531502440922011507987688852142983278718900467173717559023594830312502740658227287849118750411233444740, 531567321528223829083115114109994311430434659402829629512586854342111027059073342375895258959303689092, 28545062745806169907672288095148337286252335938, 316943362040129, 565701960536256, 2923059026696439057511347221835829103482590204738, 
    2923059026696272904011890994598822473709322769218, 1128376031535937, 531501997402235843673079140808834435517016212640303952677106616814697913329596705104777829797796040965, 1130586127741377, 11440761574726576962955716297148793922420478530, 73189470769344, 
    11440630906297679322585746361299540123427279426, 565701960536256, 11440391347511366981907468145575908158606414402, 75388491927744, 567900981694656, 90781673591488, 
    581095138005696, 75388491927744, 565701960536256, 1128376232845633, 1134979745063233, 1130586127741377, 
    1130577403584961, 1134979745063233, 1134979745063233, 1134979745063233, 531567321528223829083115114109994311430434659402829629512586854342111027059073342375895258959303689092]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161156223897792, 1161155217264832, 1161224003915968, 28545062744809569627808834671626492982492926786, 8369598697843136523389518661119113140007740822697123552094059711080353481196289842363703274600051397, 387314253637953, 
    51381112941387784284643108696242918232703374146, 583925464646046181221072788967444589938410699174705280431431772368264548952785396015890797198327940, 2928713681009934868167378245082692871195071627843, 1161224003915968, 1161224003915968, 2923728051604014589599319376093750509309591032642, 
    2923059026695608611999088599620482295034789499714, 2923371238319376324946354721798110498107061965634, 1161292656283840, 1161567737680064, 2923059026695276303732182286557903658906076320578, 1161292656283840, 
    1161292656283840, 1161224003915968, 316943362171201, 316943362171201, 51381112941387784284643108696242918232703374146, 316943362171201, 
    316943362171201, 316943362171201, 316943362171201, 1161224003915968, 28545062744809569627963577766832975884150903618, 567900981694656, 
    567900981694656, 567900981694656, 265751002661115918839352464884297205992486017696398016322007986673533741532379954866959939174498867844, 565701960536256, 567900981694656, 567900981694656, 
    567900981694656, 572299036594624, 581095138005696, 316943093997889, 316943093997889, 316943362433345, 
    316943362433345, 316943093997889, 316943093997889, 51381112941387784284643108696242918265989370690, 176210034831809, 371085815678528917485961395983617312409258038082, 
    1461551814178073752873021556102465442945903366978, 22881000326863946706263625876954302288096139074, 73189470769344, 565701960536256, 22880673485650519144869469305643864074729035586, 75388491927744, 
    567900981694656, 75388491927744, 286700884988096, 567900981694656, 79786546827712, 75388491927744, 
    75388491927744, 567900981694656, 79786546827712, 291098939888064, 572299036594624, 90781673591488, 
    308691142710208, 581095138005696, 75388491927744, 105839008948545, 316943093997889, 316943093997889, 
    176210034831809, 176209900609985, 316943093997889, 316943093997889, 565701960536256, 1461596415859547418375374079757923800662105135938, 
    1461685619180623907788878704983854933018478121794, 1461507213219035662803746381458741883169268568898, 572299036594624, 581095138005696]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155217264832, 1161155217264832, 1161292656283840, 531570869687339291747103522372062087863782221039299958983065813140202029022974143058101607814171437637, 1128376031535937, 2924441672902569826365605326348028556482439071555, 
    1161297018294464, 2923728051608334598332112241477757516553427896131, 1161155217264832, 1161292656283840, 1161292656283840, 316936651546945, 
    28546369434083170030383638208424249678071088963, 176199297413569, 316936651546945, 1161155217264832, 176063729111232, 1161226147205312, 
    1161226147336384, 1161226147336384, 1161226147205312, 176063729111232, 176063729111232, 176063729111232, 
    1161361582203201, 1161164019012032, 316668216086976, 28545062744809569704561117111931756036344517442, 28545062744809569704561117111931756044666016578, 564785685032092663086164932221496120079313509055889068652369187786417989600934256705471729833634354309, 
    72845070704961, 75044093960513, 75044093960513, 72845070704961, 16674323718499770506960884831016262817580557523772610088331808527428408066922568319643293572740917445, 2928713681009934867830622286622481525316876517955, 
    33283751484824631724445106583429594046309940316236151688569296861329201035390032840713185699573978245, 371085815678528937844659062234706516444677412674, 28545062744809569704561117111931756036344517442, 66502625332464833965431435452388194465993875051663214039238517519425291935965909667125592072961108549, 2928713681012593648340898099677408363679557109571, 316936919720257, 
    290548641440065, 17127037647018925489179711767971564913915073346, 583925464646046181221072949971383367868688667520576895305075788083272698204492678550798822791200900, 12993372403592331447569820076407047088587792363790735895221254607475192483360961638664038303661430294765835743130046243474669761460028988889658400410425443504495305649850795974005259943698914780548995696255584002190697061416773070478227839742459287813720161084461075594162814715183666932040790090327116073000748629384652796539326380261015691033725154249728388964698047074378, 513258889805605223322660477602494454133339262160886516704480203820253419458253914350972125777543032348092572098006614054799296552189570929328094346777779444370562781016646, 271725524954383304586472866144771714163632046376573657583036496406028162127539411997382193187703672876525879464315482449751927617510684916093884513547499632742433914662471, 
    538833434641126470158863430298939283618180091511190056501349045271004643505026614508033876587184406660, 28545062744809569783944022721402576522956510018, 3957316615503016392003724570384529582008112019250197669433848659546781744179587640342077201018830065621498424756112562272985006312994284599312535465403735633667505586919484999, 583925460778860723712888582099190564098552566730646806261283819408350182722314073922884646105006788, 4019149215871292525518850200639441379516894856525500629412364423570006050456220607134656301284140826868897842612618204045867433938213009704774759564624119467794632051298184775, 28550550818823270679482760027071236080670872386, 
    2928712374325645891426958855038577426204333195843, 2928712374325645891426958855038577426202185712195, 149810884649281, 2928713681009934867830658554397078408471483793987, 11441676171150510360836522770451774291432194627, 265751028401102427289069447553604734446076100293965825731499510086996050333147038708817375916554763332, 
    290548373004609, 290548373004609, 290548373004609, 387305663899969, 316936919720257, 316936919720257, 
    316936919982401, 265751028401102427289069447553604734446076100299784519738224682815082608129062040237245122965466823748, 290548641440065, 290548641440065, 290548641440065]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161157364748480, 2928712461435606628737923424034265940623999638082, 316934504063297, 1161157364748480, 150958497008678147900342096783323651760357579299909774066252647724688858636897927280121592335276146720256004758518665730480430523493812033499157857428449624940523000475206, 176063729111232, 
    565703567478976, 72709636624576, 72709636624576, 143628541366464, 565703567478976, 567902592831680, 
    581096744948416, 2923036725865007830418698815753344038784609555266, 2923059026695276952772074967337460339004057588546, 567902592831680]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226147139776, 1161226147336384, 1130439822020800, 1161157364748480, 1161294803767488, 1161294803767488, 
    1161294803767488, 1161432242852032, 392492092204286347247775334314785778351253039484107476024848921916042872471761895008408897642338783177250631977705164784962687080597130537505440814542701937420706105306694, 266594411932911499093405665547400227067257444511945599032221132490444587792440241876037958465204011140, 316943093997889, 316943093997889, 
    583925458845267980549659326692702849383006794209622847824523274213197670086846116716138596619534468, 961842399437839889284103792053779316418144121300324526075100356846211720569171805484685472171950815361702176782153571889589634619172553700191414456730650183447088590370898019705028338699199254107209764162217680138693152308877217503327225176933144856281219112246956552, 996326080379589994946213082928518195668409667751262965255904231206526695156042236887161021068148811626033901023903585677787070237304415556163083385447615092688813301083718, 61862792071275594269988712526260074203609479863323162541840140773099912032995381132605153023083275956720124911445761095047248547016551656462960661151896966475982029045542470, 176210034831809, 316943093997889, 
    316943093997889, 1161157364748480, 583925458845267980550099404125362525459897754038882129028309917989725944007031715499269907185680516, 176063729111232, 176063729111232, 1161226148122816, 
    1161226148122816, 72851513155905, 283957745688897, 283957745688897, 283957745688897, 283957745688897, 
    22858786674345843384792710378420107701557141058, 565703567478976, 79448582922561, 141429516013760, 141429516013760, 563504542126272, 
    563504542126272, 563504542126272, 431975476236736, 572300643537344, 581096744948416, 28545062745808441546213477357089084672923669314, 
    316943362957633, 567489869123776, 143628541366464, 284503472869568, 565703567478976, 145827566719168, 
    145827566719168, 145827566719168, 286702494027968, 567902592831680, 145827566719168, 145827566719168, 
    145827566719168, 286702494027968, 567902592831680, 163419769541312, 163419769541312, 141429516013760, 
    141429516013760, 286702494027968, 563504542126272, 563504542126272, 150225617424832, 291100548927936, 
    572300643537344, 163419769541312, 163419769541312, 308692751750080, 581096744948416, 141429516013760, 
    141429516013760, 316943362171201, 316943362171201, 316943362171201, 316943362433345, 158471543591104, 
    1461551814199011120787061872931106287209282541378, 567902592831680, 567902592831680, 563504542126272, 572300643537344, 581096744948416]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [28545062744829689855352168854467645200748516162, 28545062745826610851591226265220590392357950274, 28545062745826610851591228552616855532342350658, 28545062744829689855042682664054679465883603778, 73204503154880, 22880673485670559509960759824413273329800058690, 
    75403524313280, 90796705977024, 75403524313280, 28545324082684409935282928968888252121416209218, 28545062744829689854738032195366916218884723522, 2951548337407964754257892613500836973732427731778, 
    28545062746158917850522948068270934386202907458, 62225092464079550898007962695475014093282875823374457071543714614612159253635330274584022356821348360470357339971089808366508403511961527144865183358686642773122496211496518, 392492092204286347247775334314785778351253060976359138357167161372283791033769235926792519972834204223440672704380887257064991976169224146698661341217963224008755099512390, 28545062744829689854738032195366916218884723522, 72851513155905, 25690556475346532550749095675819675939309111107, 
    2928712635661194888245720018964058282410597421890, 72851513155905, 22880913193662718179838306737398909347980908354, 44950111031974080807851161376330137523458882, 22880913204961156144155163308837347072615126850, 532021042251964506863589615773938111467296454239710301906347019814134577582466442432345853018337723076, 
    531501965722251543103487040183268616042994127252718152040478862918073334654987220840400689361691360452, 532021042251964034795052322106484461517489087093285626696686173220015170729070556335186858976345342660, 2923048573223310770596151351600733373213549041474, 2923050663926148531240394478502529663218298656578, 143220257333569, 532021485771740171149387539381965305198837681519231278569204069483784005157117256246948389968859644804, 
    145290293153984, 145290293153984, 567915477733568, 17609920615104, 158484445270720, 91388541106358686388607393017927498785911477058, 
    45694314204870956538933785402811760471852457538, 283957745688897, 22858786674365281608276180633181363978027146818, 567916013621440, 581110165934784, 565716989251776, 
    730778716555816963144499249916175276195891384898, 1464361729701974451891127397486994667343838253890, 1464361729701974451891127397486998045056443683650, 567915007971520, 567916014604480, 567915075080384, 
    581109361414848, 581109629850304, 581110166721216, 72654746882240, 72654746882240, 565434869883201, 
    145290293153984]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1038105554918292487075689487044752358051168062468994626080348651174768673781221780072616692206024196, 4152422219672461384471281883428742727594239129141489229946656763141875306557414490565645357596033924, 532021042251963798731965622455631172017132408844606764731113172841286066833153412599976451936578978692, 532021042251963798731965622455631172017132408844606764731113172841286066833153412599976451936578978692, 2076195269844596962911890946643072449210920604273551882234328870409941646325922433317933375553811972, 1143784226431809, 
    1143784427758401, 1152580520649537, 1143784427758401, 1143784226431809, 72709636624576, 2928723421255084513510478008657322381883329266499, 
    143215958167744, 143215958167744, 283953446523072, 283953446523072, 143215958167744, 72709636624576, 
    469219808792220334359155696537160104036701585881731916329728125240356865873663177705343839088608483834214211587960880050376222141844678957643658472947339802224262392054950095484158136462251662686618629053058313999637615425374652174358689670455112377565192249197512, 15841925580783211757048864925179640952022061671642955336157219821607217464906775209684223921540, 538379333743079793109418344046343546957850711818184836902051539438418993824563242578658939354399129732, 1134988133409601, 2929437042379178558083424490248302874416539288387, 1134988334736193, 
    1134988334605121, 1134988334736193, 1134988133409601, 72709636624576, 143078380802240, 2340892446912, 
    143078380802240, 143078380802240, 283815869157568, 143078380802240, 143078380802240, 6799168915614215471804887295687208686934898452301474030597235386912751795548774591887410705237135485267299173700765540271387547723460990871852363067732057982082514741785853613121115296284055626988828261395544930972374711594167558277196805099156616827668220067844045264171558522297318561320469766087807288324539709646019553375958353266082237336510810925896789000397560508531019851, 
    2928723418532825578142970300950325522429183574851, 72847213990080, 283953446523072, 283953446523072, 7729078731994588665907057222071600211627729283230562191323110168922294317599332674089163925605611040609286687945015031645508668233565061000429562908226815344824395549880902, 63363835137531266384298561702826565616481586735310249891959194630347365439883676408742207571844, 
    539547184653035249620496659277723119128842005643163713601757210351003105967433125718488465064554045444, 72709636624576, 283815869157568, 4152422173266235548606349011125249007817112903058336362078889168610293522085250425944891144699920516, 284503472869568, 265751028401102427289069447180654201188962128707988577221482074904170853788449525467275304035596680260, 
    265751028401102427289069447180654201188962128713807271228207247632257411584364526995703051084508740676, 564720860112381718081544946717173679720832930477390876408758754429640921868500632059720314176241455365, 4152422219673169487284364839639592968736852436294631928642832964774030998080889775867409532229242117, 33218934237609691583666965009207839081752205338093664187707751524313407659609610637652021960922157317, 1128391264969537, 1128391264838465, 
    1128391264969537, 1128391063642945, 283966872494913, 531550657856897444840950424683310771935430631770051315350461454957115042259804461707131979622391235268, 79306706391232, 79306706391232, 
    79306706391232, 79444283756736, 79306706391232, 551485157187413703439291501099138753684484580099216313914057453169983749305971265509013640051966660, 97049358902081, 551485156945714612344934677186017527250719757583596372709966876408475367869309958193061578078962372, 
    532053411279217730194372624496281262155540255786839330266022633567390299715615158055682417868717441732, 159034603737792, 158484445270720, 159034603737792, 17609920615104, 158484445270720]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [97053213331760485995360497733358229019544261442, 97052864883447526451756370831644468116000346946, 97053213331594332495889801110107854432213406530, 97053213331594332495889801110107854432213406530, 97052864883447526451756370905431444410838553410, 97053213331428178996414268765132242069967868738, 
    1461546326125036362266824436556710703101244348226, 1464361729701995221157789699309467283913485390658, 1461680392443508891667821314267413995624847119170, 563517963112640, 581110165934784, 22881000326904756338017218215926513900619568962, 
    28545062744850459122014470679246104779609346882, 28545062744684305621924801675169763435500016450, 28545062745847380118253528089999049971218780994, 28545062744850459121550241393626656108726719298, 28545062745847380118253530377395315111203181378, 583925458845267980548574051125756360137550170605739096965369916127912911741064904761357853610229892, 
    583925458845267980548574051125756360136024834892563611088671640385556826406491718460571711812419716, 28545062746179687117185249893049393999423476546, 150958497008678147900342096783323651760357622541387304231125849217792175470732398426648442136697328356409850441346395074189226089016179157090345619994393281437130219105862, 28545062746179687117185249893049393965063738178, 28545062745847380118253528089999049971218780994, 28545062745847380118253530377395315111203181378, 
    28545062745847380118253530377395315111203181378, 28545062745847380118253528089999050005578519362, 28545062744850459121434184072221793966842975042, 736461225016249006906417373383265192943089107779, 28545062744850459121704984488833139044744434498, 583925458845267980548670224145544649568109150256337580442046286870812283086235886485083984033497220, 
    75403524313280, 259775869566404136366974259107113228376949475728725082403981668347578481261038048130802896106430724, 75403524313280, 75403524313280, 28545062746179687117185249893049393998349734722, 28545062745847380118253528089999050004504777538, 
    28545062745847380118253530377395315144489177922, 28545062745847380118253530377395315144489177922, 583925458845267980549659432351538066009591865322540954193979902099417714847513694446267643050868868, 28556126005163792673338591914482926427700204354, 17127037646872890872075751183139343257636442690, 97053213332591253492742957401029665648524923714, 
    28545062746179687117185249893049393965063738178, 97053213332591253492742957401029665648524923714, 392492092204286347247775334314785778351253082637841123676033252122212427502611796581984066109858369577111819098855247371639848957389483190259610111610454758116172066238022, 97053213332591253492742957401031635980878091074, 143091267801280, 143091267801280, 
    140892242448576, 140892242448576, 145290293153984, 145290293153984, 145290293153984, 145290293153984, 
    140892242448576, 140892242448576, 140892242448576, 141442400915648, 141442400915648, 145290293153984, 
    145290293153984, 97064363704193597807460568969244178612966396738, 97064363705522825803245484842148196814644319042, 97064363705522825803245484842148196780284580674, 996326397721721777536927936207315319147508386699035717736553189003877388964674305912827072629660319984015312857295312656514387480496318655961912150719304931535825692438086, 996326311342576922307557386244975971582157673075422473953373728386558963944644322779932899009943582483456123709169013488675351007494619835497327887028903507426191529389638, 
    51381112945385219354841983919417053482540090179, 97064363704193597807460568969244178612966396738, 1461546587461894157547022775595194401902905268034, 709065031291584, 581109361414848, 563517158592704, 
    581109361414848, 145840451621056, 97053213331760485995360497733358229019544261442, 97053213331428178996414268765132242069967868738, 97053213332757406992199184638036295421792359234, 469678024263016139997925101829823845339487915731428724891007891899013807755129384971844749710331231091905719115307644788498851759964453948842020427730968316483347339314746828636731025987738762098015154944262993317563079995738909377315314064730841010929672247924552, 
    97053213332757406992199184638036330606164448066, 97053213332591253492742957327242443062142571330, 97053213332591253492742957327242478246648877890, 97053213331594332495889801110107854432213406530, 97053213332923560491674716983011872633891328834, 97053213332923560491674716983011872599531590466, 
    996326080379589994946213082928518195668564958828724586391547871368461467107988850245599439701271454222112631305471631393510347474886534368434332217615188170280731904486982, 996326080379589994946213082928518195674065935503967398973470362518960575219961199092598099713271488029593870868527384770996876078087251605313137819061613043495158108302918, 97053213331594332495889801110107854466304709442, 97053213331594332495889801110107854432213406530, 97053213332591253492742957401029947124575376194, 97053213332591253492742957401031635980878091074, 
    97053213332591253492742957401033887789281710914, 140892242448576, 140892242448576, 97053213332591253492742957401038391406088950594, 143366296703680, 143366296703680, 
    158759457395392, 158759457395392, 97053191565153594519096022936599644786600710978, 145840451621056, 141442400915648, 163432654443200, 
    163432654443200, 143641426268352, 143641426268352, 145840451621056, 163432654443200, 141442400915648, 
    163432654443200, 141442400915648, 28556169561306758552845360706469347416963289922, 28556213117449724432971101879281699978498544450, 97064102368665030522505544970449689216657920834, 97064102368665030522505544970449689182298182466, 
    28556213117449724432971101879281699978498544450, 8814087640000, 17609920615104, 97064015256046791763327138764576705456193409858, 299360311579328, 299360311317184, 
    365466006455704443988878930754779672181787870019, 736462597040100518019010362522298420327224447810, 736462597040100518018391392502655730189774885698, 563517963899072, 567916013621440, 563517962981568, 
    563517963374784, 563517963374784, 565716989251776, 1461551835806980362641955603786665879041050941250, 1464361729701995221157789699309467283913485390658, 1464361729701995221157789699309470661626090820418, 
    567915007971520, 563517024374976, 563517427028160, 567916014604480, 567915075080384, 581109361414848, 
    581109629850304, 563517963899072, 581110166721216, 72654746882240, 11440325928267459949207791059222699318261584706, 72654746882240, 
    565716988727488, 1461551814183099266523630162741219235888042690371, 145290293153984, 145290293153984, 567915477733568, 145290293153984]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [531501997402235843673077274021725842911483841064560594136337044486619117881436770573870099296873104068, 1152580520584001, 1143784427758401, 1143784427758401, 1143784428020545, 73204503154880, 
    531501997402235371604539981213064686716613139783140172416962443529101956399527478546968724585442460356, 531501997402235843688392962931064486575976894963942546720275843055127749389186602021773335356435184901, 1137187357795137, 1134988334605121, 531501997402235371604541320768351005639881617153583958151936387206894233175824525030588783358107730628, 1134988334736193, 
    1134988334736193, 1134988334605121, 565725603566528, 3969483873812212976714719816551295906464040476362190998717879358579827418855021610247324460582908488221892672143347382398468153799149236520720641847483934058092046016472644166, 565716988727488, 565716988727488, 
    1461551814199382371272979595887951723894296024898, 538509094957445109129173573122060466017291425475275499824027287071153143921452258981197854587650096196, 73204503154880, 565716988727488, 565716988727488, 1128391063642945, 
    1128391264969537, 1128391264838465, 1128391264969537, 1128391063642945, 531501997402235843673079140701184017111672217376334797014934291090638954283417228028370802200447139077, 531501949882260587742187637716364374208434059312798157312257075184465763245633440775324378304998580613, 
    531501949882260587742187637716364374208434059312798157312257075184465763245633440775320103403789787525, 1128391265755969, 2923049270124277460077097004029400700235638982467, 531502440922011507987659837301142041274031040853228480179348581693000063040078245332738033068068324036, 1143784427758401, 1143784427627329, 
    1143784427758401, 1152580319454017, 1143784428544833, 145840451621056, 1134988133409601, 2923728051608375487825853648195290108849310221123, 
    1134988334736193, 1134988334605121, 1134988334736193, 1134988133409601, 286014892413120, 286014892413120, 
    145277404057792, 145277404057792, 1134988335522625, 567923824399296, 145840451621056, 567915477733568, 
    567915477733568, 2923718295032351130678381551552889706819079979843, 568056809001152, 145840451621056, 145840451621056, 567915477733568, 
    567915477733568, 88032875188416, 88032875188416, 97049358902081, 158471543591104, 88032875188416, 
    88032875188416, 532053411277163287962389350442714345972601651671339629107911590887843657463443683495253178715990271620, 158471543591104, 158471543591104, 158471543591104]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b9_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_11_0
  · exact tv_b9_11_1
  · exact tv_b9_11_2
  · exact tv_b9_11_3
  · exact tv_b9_11_4
  · exact tv_b9_11_5
  · exact tv_b9_11_6
  · exact tv_b9_11_7
  · exact tv_b9_11_8
  · exact tv_b9_11_9
  · exact tv_b9_11_10
  · exact tv_b9_11_11
  · exact tv_b9_11_12
  · exact tv_b9_11_13
  · exact tv_b9_11_14
  · exact tv_b9_11_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1130852142682304, 531501965722252339719153175627443183717469800790498869384772571818727217051835929572359927622822367429, 531501965722252339719153175627443183717640638391329153326374694246369831076240967235743877729693913285, 565226563962945, 1130865027584192, 283815877546433, 
    1128665935057088, 72602404061249, 72602404061249, 72670922213441, 72670922213441, 1464367293988666786345460835585929877903938491202, 
    72670922213441, 283958014124353, 72671391975489, 735038153274139525203752297001957862872067445314, 1130852142682304, 531501965722311820355295343000136595802133113959347658967798375607001664248784974852633330773870350149, 
    1130865430237376, 145703012667584, 145703012667584, 1130849928024256, 1130849928089792, 1126454091976896, 
    531502060762203795718038741380637189880501640821354318282516477999359619219928091514111650547465240389, 1130849995133120, 1128650906865856, 1133048953508032, 1133048953442496, 1128650906865856, 
    1130849996116160, 2924433315402813672402381236860191311731202495298, 75318833451200, 163280183104192, 1130849995133120, 1130849995198656, 
    1128650906865856, 1133048953442496, 1133048953508032, 1133048953442496, 1128650906865856, 1130849996116160, 
    2924431924328498024125656976618932504475786598210, 172076016079808, 172076016079808, 1016500946211776, 589890434634688, 97231598205936491350660359263071773829072163650, 
    2924433315402813996922172835326203475162122195778, 163280183104192, 726230136525504, 75318833451200, 145687577628864, 163280183104192, 
    1133053248475328, 1133053248475328, 1128650906865856, 1133053248475328, 1133048953442496, 1128650906865856, 
    1130852142682304, 531502187482143476356267063671762043437506508641589031873029778217502413599328374029571050082732392261, 3957340443244109915238528109586043985448832434640056637062048526497910158579920958479931133882092332045517877726494765500070927310663473525087378663218913628084149928268396102, 182866808207136263864215978811709875421280479043, 17127021408847196083121750759367945704492274498, 17127021408847196083121750759374384444584530754, 
    28545046591708432741945982415123546494438774594, 75192136118721, 75050536411457, 75050536411457, 75050536411457, 52897547630930988433218872835188071378869869378, 
    163286768161728, 163286231290816, 172083129619392, 163286633944000, 172083129619392, 1101836620742996991608515348445947153932575888194, 
    736462602484587234854032627426544128258394329922, 581100779869120, 581101048304576, 581100779869120, 581101316740032, 18151363318720, 
    163286231290816, 1128665935057088, 1128665935057088, 1133063985893568, 1133063985828032, 1128665935057088, 
    1130865028501696, 2924431924328538913619398383337473903088199914306, 581109361414848, 581109361414848, 2924433315402854886415914242044744873774535447362, 163295215489728, 
    1135250193387968, 531570901367383692542797550355194181719091974575125145453313647529762199060569528693234983449486270021, 1130849928089792, 1126454091976896, 531502947801755124347351589697314092741901750441794140060569511136538357293569279732368981362694000453, 1126454091976896, 
    531570869686402707761686297389117202236281552858088780410431686737075786286515655623407784374933419909, 1135250193387968, 1135265163121600, 1135267373388736, 1135263481074624, 1135263481074624, 
    531572897206374181958308185599536835979177851826758051002610364797034040619495469550271982378714766917, 1135254891139520, 12131651677057194035006421367755935246161335106, 150105492558784, 150105492558784, 290839088600000, 
    2928723416496427864135960017514810097242029953858, 2928723416496428188655751615980822260672949654338, 2928723416496427864135943092488771888175600636738, 2928723416156146470774386659116411387517522156354, 2928723416496430135774501206776895241258467857218, 2928723416496430135774501206776895241258467857218, 
    2928723416496430135774501206776895241258467857218]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [73152495438401, 73151959024193, 73151959024193, 1978643212691817293584598830314142670096991565944056100368981556509283233971924845458511316430820595150800140124405141017350669856124677947226265994150000456136890591139245638, 494988812095680, 565357824708800, 
    494988812095680, 565357824708800, 424832672993728, 6766417418605052960284403873956034662415087933019357751174634711686152421128370236106196291468030336505308234966939183908257870890931027439678518685677619440202482198603738838052627672866608332873961145481784810297173166059837168989476227257631005135330662053069449156680952147525984028402147584967759407221876835532886241747606075049629154265286055029279599810987736517530953674, 72723462623424, 283815869157568, 
    283815869157568, 284099483800000, 123718979702907296900957969448798360870873626377824732180702756357245573391931476057583603804368562247178344431293461258271847245916035223212941028365569765359824100495687239, 123696335928358367652530274622954401638006858379669000195693308397547635663752629995967882383079843615071841009559242269338327500472436390910267045248771308809942908675257927, 72709569515712, 72709569515712, 
    283816003375296, 283816003375296, 72709569515712, 72709569515712, 283816003375296, 72722456514752, 
    72722456514752, 30916536060390973334392789219594223022841207738600850232126556505379098512641350303830668660273786849414053436988633874966690185044751065135974000939922304672263792479350343, 11462626759741199768997410706151217483789374274, 22880651857531844697587021773696965025688720194, 583325890726465, 583325823615553, 
    581126800425537, 581126800556609, 33218934237609691583667734500700879018965607552233066395366582696375288605112551729931261612438221061, 565733168267841, 2923059026705660288023445389325497336011054679875, 1128650909180737, 
    3957286427485527111966371202728695842583142669952406685939838099898004695599445105319527457963131716141822238702492805846893721692427541764692548515988117870786196643564669511, 2923059026705577860035993460215541050950996248387, 1128683121689153, 284258191557185, 565733168267841, 73151959024193, 
    73151959024193, 531501989977239595604777958266590246907210077719849643890214810377548812184427244189515772895015103045, 4152422219673169487285134331132632905950254647948019775334663091798630518408532879790735456359575813, 33218934237609691583667294852612056084036108681140815859361421562739649606960324545744914209578838597, 565733705206337, 565733638029889, 
    565733637636673, 565733638029889, 16609467366305190829035992418570272698236317637043172693449831413545592983268775239038697172417271301, 565733168267841, 2923059026705577859996379378958407824557450757955, 531501997402235843673079470330230775363297137637080212268951097862716056184207520967903928316539333189, 
    3957286427485527111805477507569384677388265726829047115696438224679927975456096416098154316005244052901084413721307554398407779864317554165801511606627852324871209849263716423, 33218934237609691583667294852612056084036062503985178488398341509027027513844003745897684573278071365, 2923059026705577859996379378958407824557450757955, 2923036725960379004854718034736358096204124431939, 531501965722252339719151636859109374010600548494107721524533470277470747775416975526562626240251973445, 73152495438401, 
    565733638554177, 7729078731994588773182614234970272038156773279364636877127765354306237444966898631880952793711909300025111364430614370685453418847559131887464167366985641869963783907036743, 1128665941819969, 531501997402235843673079910192991513469939473119834447266783141572455297281457741655391169468778049797, 284241213538881, 636102448859713, 
    636102448859713, 73151958567489, 73152428329537, 735038153295407254265949365575100471625558102594, 497187835351232, 567488128487616, 
    123718979702907296900958070943087228744413053056313867216125688855668387715473532790494675144454534755398185782685484058522813594209219842385064605170155050380555978601889351, 2923059026705577859996379378958407824557450757955, 2923371237138357288720360879014225395163695458115, 2924441672907886758631154593491314208670820108099, 33283751483858781319564816128739982923191892298955571051706608214456923181590049020647299712353462853, 2923059026705577859996379378958407824557450757955, 
    2923371237138356964201841070510447821626714138179, 145290695807168, 145290695807168, 499386858606784, 123665259706514723817469992000255752789379054795555447883033573604416149213201801252418953549607882351843797570774597697513494866586641516862518115928553331373128189439082055, 2923103628366116104703131682126640424996346834755, 
    2923103628366115780184611873622863345004526480963, 123695396123260585422513779322611143084593994527087862221254488193128200263184393189661664637173404191632624902323701007150699378088389076853445673602007209320004327330272838, 33219377757385355898274478425002338802635197787403479079808904420471000268913389039912058232559692997, 145275260768448, 531572722965411489262211614652112653890571392491620957230296323881245098360362829836917212692246446980, 297076719096000, 
    3353732746238322116020963563231326792644422537703767127716223924568548674187655352448409931972919654682979793076639620688730788254539800655875416880388223061156687878901618535159196436137574039570003057144329447585937781226521899446074102293389346875297253129600341098053943917600082257602680728741056239568529101632044833558695453383764547387563864902970990218166018884512206922, 33284591003420927995833185577910432186357966179657882351230328016968388343125413291033906832283550596, 1978673408206294763624360309987527955848333673722109684660407881534622700805795696569756410911859360606610087113994058174332916847192387358386346388016711860401960784534435398, 567487725834432, 145275260768448, 85970486563008, 
    508182951628992, 1461730221331979515147245494149263794911024517954, 33219377757385355898274478210540057781608293080767662406949643557349979322502755864517258443790050885, 2923192831687192594116636288463105625874138969923, 2923103628706398147105550337086237952436294694467, 6707465088747716097056592077363274021238854897065343158400050047707950500998719341524183391675321409496970057441757540690410606557287573747251488139544963912943054548085100119424324576958427034334873087468478330392628807636078415649582009511260800722176198949763498798044028233627840689285499641145862012942604749525681358692076765303413013233714108408516982431418474807276705355, 
    83984068383168, 8867811776, 562958821233088, 145290293153984, 7760210236153524638637458676013234798871915889947221852230702807348688769294996818961209645278891984808733514840781673483817676960116877218878907074773182085486586776997447, 501585881862336, 
    290343014895808, 2923059026705577859996379378958407824557450757955, 2924798491466569079041199394015702161682577008195, 497187835351232, 123666144228958092852206876092622838452637789351450489524223266348525584249636199036894919146602627393721421364483025032773856364553683338998756008392548269280890598989987399, 145275260768448, 
    145275260768448, 137284085361621710030000556353067655888143129154, 2923371238329345572943645501136036027629723232067, 2923371238329345248425125692632258947637902878275, 2928723415986004313754537852933648344949050083139, 290343014895808, 
    2928723415986004638274329451399660508379969783619, 2928723415986004638274329451399660508379969783619, 2928723417176992922497614073669046084924042422083, 531566814649450785644819340084031413389891698486306563036071193762820012627908814953434791380210049605, 79306639282368, 79306639282368, 
    290413073141952, 290413073141952, 532085914943017766239685494703179805233974339035105119452838975410652577433462081124345554337184105156, 531505989080216822504544562464942551601149426482642411874062691844592676582071534830629002487422015365, 531505989080216822504544562498485038846551566490484496303279843630861214447849527803752787620874704773, 1135254622585665, 
    1135254622585665, 1135254622585665, 531570869686402707761686297389117202236281552858089451856254100837565319476054259703681400686759920516, 531505989080216822504544562478359546499310328663480385579843117465226435849453072740624816924349978501, 531503961561272569453176849296590621453225986718733634654095615403665281272623020617534350899214302341, 532345469047865660768624110356848139815344057959486246185688371381305733006967915710357180121876808388, 
    5935930579190631616001319176849573227493461240099143296957030727711848769872209422459084875121076879920788683256028132544038939947375169829519249865721576241152424416657766983, 1978644155390614684742611329787861667513156864556970981279354174245290187816680792520850956158298116726105322830068774919213305674519022709856887827905089649766594436141120071, 2967965761340618917561478231531542951065145903390299399483757169101446921799051799401484535601367600385520942480866527222288090301184135517707525679540852567881416857480034887, 4156945546928349518604630377272479820007834827201969210917077057649731366151702308859654025665069468022725525839808875202508765286701869103334117424287916138899986363157805638, 290343014895808, 1135248247907137, 
    2923728051613651530597663926481896831140891772739, 572298496066369, 531505989080216822504544122696100774582772228052084178111223744204805973024121924562642702943787700421, 72709569515712, 283815802048704, 72709569515712, 
    145139965104320, 1135263213437761, 79306840608960, 290413073141952, 290413073141952, 8867811776, 
    523099895412083056701961568785102995499190629434155857492554403435754243343562188804286622922725253, 72722456514752, 72722456514752, 82068515066816, 290839088600000]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1126454091976896, 1126454091976896, 1126466976878784, 1126466976878784, 2923014425055755907847806052055471588967421317954, 72671123540033, 
    72671123540033, 72671123540033, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 
    72671391975489, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 72671391975489, 
    1130849928024256, 1130849995198656, 1130849928024256, 1130849928024256, 1135254622966208, 1130849928089792, 
    1130852142682304, 1130852142682304, 531502440922005843165253198632127688506600639859087277907474580060043143738987107959451995641204836100, 2923192831697908886674815302507333853680167293762, 1464372861018823477429589516038269041656136274754, 33265503442351452126331306229090706639815515675446440866307823883690874866739331128466346530498363524, 
    1464361710646224212118018748179132717475383284546, 72671123540033, 33330384048567549770084055013415606785296572831131718200920138323617454815002967695460191932104786052, 72671123540033, 72671391975489, 72670922213441, 
    72670922213441, 72671391975489, 735038153274139565768571504305298710766570017346, 531621557660220520752150513146082314592552195636180300757603903126366351170190753183270369250787148484, 1128665935122624, 1130849995198656, 
    1130849995198656, 1133053248475328, 368944944160415134053722878186638528975017694018, 1464361729701964067257796246570573589988004401986, 1130865027584192, 531501965722252339719153230583454286584335988149384332492510088116786345471161445230340801350831280325, 
    565802424683073, 2923059026737561759922283370275190891157781514051, 73151959024193, 284258392883777, 3957316703951659838780152004808261855563355920534123062488556975520652436931769909419166354472247557026800888754137522857367008482401090263383330461290433004428141346133343814, 565733638029889, 
    3957317558990021763896597074513483777321179429988810303505790990816728443878441296223981855856133517212096960514156571367497189761345281635317880936951304641027610877674610246, 73152160350785, 73152495897153, 565733705138753, 565733705138753, 565733638029889, 
    960962154094212046835216665290546064298897187864006737062931415346219582426575847177378552277775350718611374702060332024911311854850761807530670807452093857470299238569650069956159152232319387331672625520977069402033759381951899521924245446933154360138416129247956553, 531501965722252339719153615275532006652570137262412858188274824630842858430845092499590867553765216453, 636171168795201, 73152495897153, 565733638029889, 123685131982806624731636947599472465597942826067141657887102180393266284177070176290541891531268771030017101866445080346239354495650139899496735353024919256742857713934923846, 
    1130852142682304, 531566814648484225306163577301943804094645550766493160852035823832285988526039447826278823301534896325, 531568842167428478357530850701453957224191833802426491581053465286168581263678350519796619569340010693, 531566814648484225306163577301943804094645550766493160852035823832285988526039447826278823301534896325, 531566814648484225306163577301943804094645550766493160852035823832285988526039447826278823301534896325, 1130852142682304, 
    1130852142682304, 1130849928089792, 1130852142682304, 1130865430237376, 1130849928024256, 1130849928089792, 
    1130852142682304, 2923103628366162226919935339958930556694097312322, 1130865430237376, 531501965722311820355295343000136595802132923292382446597370670226588905044197315343764340696619520197, 3957286482768179822531042257984468785437016842876743920674496321736278958371152670106324390638863448733274299389309339628051197033253113697326353127571360814580065455040331334, 1130852142813376, 
    2923095265597320640477781096116489869316256176962, 567916014604480, 45761303733508096269845501989850430331355667266, 145689725112512, 145687510520000, 145687510520000, 
    145689725112512, 145703012667584, 145687510520000, 145687510520000, 145689725112512, 145703012667584, 
    45761303733508096269845501989850430331355667266, 145689725112512, 1126454091976896, 531502060762203795718038741380637189880495730145432734799242231124143991301039029133666257093067116357, 290830230229440, 290830230229440, 
    572304938504640, 290829961793984, 2923192831102331992016298457582829561617546482498, 2923192831719094030521271970261338519330933978947, 539742768951196325507865402138699056102340450197875606894334348058039577989282022289613866135697244292, 1130852142682304, 
    531502187482143476356267063671762043437525003337214631804565324891564217087465117607093732827135315781, 531615475103387761601200090448234652778561254456376758670749079523822883523948720678328845253779866308, 581101048304576, 581101048304576, 581101048304576, 308422433051584, 
    581101316740032, 123695471676221042797915710105195680535550393139390880134966757974598658591025081248587257590371839161876970607808558261434691650770261780094935425264463311198526973746839110, 581109629850304, 581109629850304, 581109629850304, 581109629850304, 
    581109629850304, 308415994794944, 308415994794944, 308422433051584, 1135250193387968, 79735007220672, 
    150105358341056, 572314065310656, 1135254488355264, 1135254488355264, 1135254622966208, 290830498140608, 
    1135250193387968, 1135250193387968, 366090429719190666996350316640387456917454213954, 853797648470976, 290821908206016, 290839087682496, 
    290839088075712, 572313796875200, 79267991980097, 79267991980097, 581101316740032, 308439880831936, 
    581095138005696, 581096744948416, 581109227197120, 581109629850304, 274745532017468689803848039066971249828197303107, 581109629850304, 
    581110166721216, 581110166721216, 73120750833856, 73120750833856, 572298496066369, 145689725112512, 
    145689725112512, 532476030175051125568810890530274528309189987059290668932858355235412568351519032297064797028923752580, 88614378162753, 88064085002305, 532086366377952492244812920228283923502860872459586221613286526508628006287186036952809394911066735492, 145687577628864, 
    4184799162934115812467006531811878932024478815227303108363799046136982306205777732963098949877755141, 563508577046976, 88064085002305, 88064554764353, 25690556512564897417967736693685251176602797891, 25690556512605786755728698461259928835195406147, 
    88064085002305, 538834329584228694858269711437813787343799695138028417703122124968349874881837705371126879589543198852, 538834329584228694858269711437813787343799695138028417703122124968349874881837705371126879589543198852, 88614378162753, 88064621873217, 871372386472896, 
    145702610014400, 581101316740032, 145687577628864, 145687577628864, 726230136525504]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [90744681482817, 563534346338881, 72639712399552, 72639712399552, 72646163239360, 72654746882240, 
    72639712399552, 563534614774337, 563534145012289, 563534346338881, 22858351026265797544420420379146467978082521922, 301850645580353, 
    2923059026716211724527477913244979128934212896579, 1144050715542081, 90744681482817, 90744681482817, 581126800360001, 90744614373953, 
    531571883445859728093838005984573371015275453222989363297997857564691512789431255911021779426363115269, 1135254622585665, 1135254622585665, 1135248180134721, 22858351028509527383532186048578453891757119298, 1128650909180737, 
    531566909688434973202219461557252614587781686025470124591971624095238120289787173063293825373713985797, 11451955460767297944068514140156230740863881794, 11440630863596169112004453033220901494786626114, 2923036726045449637149771857905542595956585857603]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [581126532383297, 532410317973131812080648656714270156060592381536589609893487351472106090256347781895432638757381357700, 536692438010464554972587582556171495452322513301567887446957442406563380909888364225226333405827055748, 538768617409379679572675544083912136848863734186044111133219137729056088180558669732936048947790889092, 532150795548267421505637661147626718737520760848372037069699673778529816838762538729637492797124919428, 581126800818753, 
    22880651856534919897796571963262768197530555202, 2923059048494365635494605585268043516020982351683, 2923059048494283207467539574900954004567378429763, 531501997402235843687493332922195703653322799687969577670948486604953746896055899063578761065055673605, 2923036747738455396175041981551837611953662001731, 531501997402235843687493333029322020693895454618899297157134076347610500353000813882013648945436450053, 
    73152495438401, 73152495438401, 45716702053113134554166614414863479636873974594, 182733003226600873697241947225412027925590446914, 182711411639159678339408113457370509612985418307, 583325823615553, 
    583325890726465, 73152428329537, 653694634904129, 2925868942219166618116724333477864400378807780163, 72723462230208, 72723462230208, 
    581126800425537, 3957286424923782331257569556467828053331168425210010546086560143435557043097217568828097116544454033870907027216580373203914836256757461218525825073781994965864405955643747910, 581126800425537, 581126800818753, 581126800818753, 581126800818753, 
    2923371260107421639725642598671598536351346139715, 2923371260107416771930006561720701465162449757763, 581126800425537, 283949951881408, 22880651858778649736908337632694754111205152578, 4142784228360910908802335766957165297584686752429553713591218414793005247489723738595705620903667883051826194319477719921617068314560369524703513283026779969382264217890930246, 
    283958550204864, 283958550204864, 4158242378682424545877174067372260302831595466214329782443051439313895390767125428682498538539463003428685601274898477001223470324476881317739071061181693870061752033151545926, 283954251043008, 22880651866836476162298248719182003534022317890, 73152160350785, 
    3966464703872461186898157878799336234098157318011621207045769850311440232446631214380212369876642769645565116847952843040836216669397369937008410841946012178945986894705406534, 480950554875126826929644583528179280854468969067850750811947600825277030449925936575315751774222591095866266286732972331439562377252866392898794370303574991995269379097864709499515719334495084545053400419890400047968463073944080809363777607034108950718980096246988553, 73122894581952, 354602174648768, 73135779483840, 73151959024193, 
    73151959024193, 73122894581952, 354602174648768, 354602174648768, 73135779483840, 73135779483840, 
    73135779483840, 90744681941569]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [636102448859713, 565733704682049, 1038105601325226656261112741112999207100509286666393382647521464866551546190720057742736820234630277, 565733168267841, 2923059026716294152554543923612068640387816818499, 1128657620591425, 
    2923059026716211400007686314778966965520204629827, 2923059026716231844754557018137733261651234326339, 1128650909180737, 960962154094212046835216466568230249988890382151958133667347307562916465497342476593298410858581677141351845626939716737428015408988734512894287202788467335507517490986589776445971980008188546766582109799392845525641636039252194293468664316105634598600318976746188553, 73151959024193, 1128683121689153, 
    539483191105693307904989621127166661957158843076672128809109189208158024211080576296404968688880730244, 565733168267841, 565733638029889, 284258392490561, 565733637636673, 284258392883777, 
    565733638029889, 7729078731994588773169520666295190370044736057138367577000711215351148773730825284873711213720866435428376839004898402199146253314004926460552850802774666246128713286547527, 123665204429260709805884152655768039672729271479015920671161373315949523592261178329023232215178897785583604594890815598429400884760085049411903678569458531214518010549106759, 73151959024193, 73151959024193, 565733168267841, 
    2076211140774540933269119937789486073586706161992380090843616441385116925754003238058671115871733957, 182733003246539369395965508024691772293812127555, 2923059026716211724527477913244979128934212896579, 2923059026716211724527477913244979128934212896579, 2923036725960379045419537242039698944098643804739, 531501997402235843673079909978224604924631810079789385137073962041224972816257347243421760405147770117, 
    531501997402235843673079909978224604924631810079789385137073962041224972816257347243426037393710669061, 531501949882260587742187830038934959487520271390244335820502019604593704953167310292370176695077135493, 2923036725960461797806664319192544706645060551235, 1128657553736257, 531501997402235843673079910085350921965204465010719104623259551783881726273202262061856648285528546565, 531501997402235843673079910085350921965204465010719104623259551783881726273202262061856650372882652421, 
    531501949882260587742187830062414698959871339678885102289338414748087686833271703957193456929594369157, 2923036725960399490244361901261002340689109910083, 143490706068417, 143490706068417, 565716056036289, 636102449318465, 
    73152495438401, 565733637767745, 73152495438401, 91522607425890448388781968189744411859184784194, 91522607425890448388781968189744974811285689154, 73152495897153, 
    45850507034727868674423523919561280953562174274, 45850507034727868674423523919561562429612626754, 45850507034727868674423523919561280953562174274, 182866808208215607817498856730109829242278646594, 182866808208215607817498856730110110718329099074, 182866808208215607817498856730110673670430004034, 
    182866808208215607817498856730109829242278646594, 182711399388994469185623428775893614118303760963, 73152495438401, 1461685619180706259756309072167718863607716385602, 565733638554177, 22880653047523204120500907478049583359714136898, 
    1128665941819969, 1128665941819969, 132875517170549667140217855486514756485814493334024282925866310532012045412391917741433111343514474885, 565716458684993, 132875517170549667140217855486514760086094903975248972417451346408578128467875753464723197135902955909, 1464361710646224212118018748179132717475383284546, 
    1464361710646224212118018748179128776823561851714, 4395946588256910153339507021746856756526993965635, 565733705138753, 565733705138753, 732180859406542047643711596624480504912541684290, 565733705138753, 
    565733705138753, 73152428329537, 565733637767745, 143508288590785, 636102448859713, 13118309248616667272107690173392736222570352480123600913619309594185293497061910000012742799436464610117150602728684797479181431817217558434319867777828842740703085816971645683890256446625688084587286867679463819060570831369041289273386275260805725470825800546192113140234430244743126330637740224572523879608403734342628655220078940555756239560498060169546727472372224577610, 
    483068399734392256596603452072689932513709894038576676684204153094541681862893414819456972748453862434918885286530370798169125134349241099652625178944598872173024650767943, 3957769494675904269259459758409585899568650036697584459571806323892258860696191546691966396946209913725218452870230586146497581373401184866613989730179678296169141569352354119, 636102448859713, 94377113039711876845755382275474252474458641218, 73151958567489, 735038153274139606333390711018344170516442616386, 
    73152428329537, 735038153274139606333390711608639558661072589378, 735038153274139606333390711608639980875148268098]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [14272542282624853759616613953690723930874118979, 91433404103817034175472404877669124905958904642, 91433404103817034175472404877668913798921065282, 145206474182848, 145206474182848, 537730971229698372133891057151166889629101739708057876080752228710400418396371358042565818295729275588, 
    145208621666496, 426687901733312, 145206474182848, 145206474182848, 426687901733312, 22925253517073164603934738472394639654562829122, 
    33337480364872433620033063122392292188351343667272613683014247267454124785754446501616075620815697797, 3957286431171079471261248611484284558459199474667190469820459079091066522235028647868966365581965099770802686808408360187110201132456464971529396908481543115599146293788978758, 22925253517073164603934738472394639654562829122, 145275260768448, 145275260768448, 2923059026716211724527477913244979128934212896579, 
    2923371237138357004766660277813788669521233520195, 285881622598080, 145414981423296, 285881622598080, 531566814648484225306162698005753055690791736613800684910737548945303556090407239312402718201226686661, 6707465088747716097056592077363274021238845272324962137946396857010650052059691504918520012960426692408131186242657219800893390210052934694794012225222800114995702396294789639112917014046835596866708468448334676333766859502849951039226590638613270576002678580227743731095390275047033215076895306427509412585598855299403748380572944054863460372194548866353945852318890094858551370, 
    531566878008451469248291847910385268445132525352942749205475973393246237103788046661461904778977341701, 616365761228219484122774134810168976315274398510608581417718984757285836194577597825788591838820229, 145690127765696, 145690127765696, 567915477733568, 616365761228219484122773920138249006311148637927689266523073865973301522587612790211007959937546117, 
    145703012667584, 145703012667584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [145275260768448, 145206474182848, 145275260768448, 2923103628376749969234230216413211729373108973379, 2923103628366115820749431080926204192899045862979, 286425741288385, 
    6707465290599979356628218148354348246390697347771048074129348749591642507406691282711097471165069303749107491780819887581419634563591164234428634405244644575429087819415383726433039413545207465102619092276549214160863521430248173076795981970181289781292312363056958004617080010001403944352723137143171628601481937193700356813301477083604293280311004321861337233655790187162808906, 290279937544640, 290279937544640, 8804960833984, 290279937544640, 290279937544640, 
    730842809600966263172718132996298772771879627587, 572304938504640, 145221506568384]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [581126331056705, 581126331056705, 185548483036114594907933588371938036899544891971, 88545121813057, 88545121813057, 88545121813057, 
    539677389416175754180142720732381428101396367631999866091299019051188106667144653456645549544305868932, 5936533528310646667113806574617407077591641402292804242591750871059028137496923511394000249447873146674166017831573732610212360207679500345195244781376968568178125193955193414, 536692881530235262567516252180837327163866389679883347443756637817793045490574824806010077438862966916, 532151239068038129100566330772292550449064637220874485291455509643441696374742716661822089558413820036, 299651555279425, 299651555672641, 
    564721303508401896340443749314800246689835370885154873777405938215245343906811346339501203798754607236, 581126800818753, 581126800425537, 581126800818753, 33997944660723052454634619292816980217158976951309074555820344018374948957062463847406959003542241412, 581126800818753, 
    538769060929150387167604213708577968560407610564359571130018333140285733527602566880404344934741852292, 532410761492902519675577326338935987772136257909086375796877246078481605768636587381737275845438095492, 581126331056705, 145275260768448, 145275260768448, 2923059037435106282537039512341279263034911557443, 
    2923371247857251562776221876910088803621932181059, 145277404057792, 145277404057792, 1144050716525121, 145290293153984, 145290293153984, 
    145277404057792, 145277404057792, 90744681482817, 581126800556609, 90744681482817, 91522607425890448388781968189744974811285689154, 
    90744681941569, 308415973843777, 145277404057792, 145281707413952, 145290293153984, 145277404057792, 
    581126801343041, 581094589088321, 3967612043732259643218270701464363010574791658765243638320885951298311187935000845454357857884137723426774258197145811828854422957977244381441790692767277529583037091241999942, 286156768940480, 286156768940480, 286148170617024, 
    709065031291584, 286165371458240, 286165371458240, 145414981423296, 90744614373953, 581126800556609, 
    971770568674508780509252751302704545651492431609591107316053327173187886948224019762523698552705873797, 90744682007105, 90744681941569, 90744681941569, 536692881530235262567517568549040775521819249173202131286500956769613306277589932386746342010238812292]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130861005534145, 1130861005534145, 2923192831697908886387651936941544393594923725635, 16609689126196327466149880462898959318900269375200180286792794641290245377117494581837161214421638981, 145275260768448, 1978643270781792212041431035879242555566871035108902433643129563067913232041089921111552508403485400109974370187816406695192883879967835062100443326683602031770018516152866375, 
    3965015557814214339220459148890416254270091649435382542129601923529679136043172297427938230213043582047605702885182496004581077420090745119060263285796511981446691973098359111, 163417622057664, 145275260768448, 286012749123776, 145275260768448, 145275260768448, 
    145275260768448, 3957286453284098376896551028664567146332245004469058099311390516680544999621145940517053922068667833202110629744380294155622708707943745821205643532978662883335803040618294855, 2923103628706398187670369544389578800327324413507, 2923192831697826458647734822749676930250901108547, 2923103628706398187670369544389578800330814074435, 286425741288385, 
    281483844522432, 8867811776, 281483844522432, 581101316740032, 581101048304576, 581100779869120, 
    145290293153984, 145290293153984]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [531567321528223829083114236531192012525116514603111965170684267243792379572013550759838713699908207492, 531567321528223829083114250270194788241833061448697483501271359788589217417678459876529331393138017156, 285943962538176, 145206474182848, 2923371238340061865204738286413290941140414047043, 145275260768448, 
    531567321528223829083115114109994311430434659402829629512586854342111017432851596892781981882271417220, 286081535709376, 523099889565986218262491289224620081819933025621341157408885371213817544283378474572292063464957829, 145206474182848, 145206474182848, 285943962538176, 
    145206474182848, 285943962538176, 145206474182848, 145275260768448, 286012749123776, 145275260768448, 
    145275260768448, 16610449074603487350192158912779425439564230646405489915487364804369025546570160584660448132715254469, 145275260768448, 286425468637376, 145687980282048, 531505989080171503924401620500493394305021254555511259503483889020333626000478100393841226185928024325, 
    830475814727703601799828497203070363632255091376532704305389550755564398010167678914312854877694533893, 537796105275778724860766365770801359317317145066018724072477156492332602328982792117555886247869956804, 2923371238339979437474744035422607332006485370691, 2923371238329345288989944899935599795532422260291, 290823787799361, 572298764501825, 
    290280742064576, 435483994755520, 290279937544640, 290279937544640, 154009018044864, 8804960833984, 
    290280742851008]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [11774883299618267346435291120746512726550909506, 23549676765605515298271939803261061505528894274, 23549676765605515298271942090657326645513294658, 11774839743475301466311967808796761460219843138, 90718577115713, 92057827352349384869809606208535335649887130434, 
    92057827352349384869809606208535617125937582914, 92057827352349384869809606208536180078038487874, 92057827352349384869809606208535335649887130434, 290279937544640, 290279937544640, 149675450568896, 
    149673307279552, 149673307279552, 8804960833984, 8814087640000, 149604520693952, 149604520693952, 
    149673307279552, 431561011892672, 149604520693952, 149604520693952, 149673307279552, 431561011892672, 
    33287806150511640961945655581099213456628561860633009089032974790252749802665398718993531847324147973, 537734519387873474264164768669462879741807840785824949313991930004584615638095454490052206395140620996, 79236782166208, 12131651666569038890335484983409351183915029314, 79236782166208, 572299036594624, 
    183045934897078910834226933387451476302696097347, 149675450568896, 149675450568896, 290280742326720, 149606668177600, 290280205980096, 
    290280742851008, 290280742851008]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [283745944932544, 72639712399552, 72639712399552, 1135254622978881, 1135254622585665, 1135254622716737, 
    90781673591488, 283745944932544, 72639712399552, 72639712399552, 90781673591488, 1135248180527937, 
    1135248247382849, 2923728051624285395128762460768468135517653911363, 2923371239690474756673698753789098225278822458947, 2923371239690474756673698753789098225259495106115, 531502947801800442927492992558181451690610560201522772818282412050456805156615153628966956289605239173, 183044606434718451490465572372984062679598573123, 
    853773741220673, 290823787799361, 572298496066369, 145277404057792, 1135263212913473, 1135263212913473, 
    2923371239690557509060862098716539182097773961795, 145277404057792, 286014892413120, 145277404057792, 145277404057792, 163419769541312, 
    163419769541312, 90788124431296, 281483844522432, 281483844522432, 163424072897472, 8867811776, 
    73135779483840, 145703012667584, 73135779483840, 145290293153984]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [90744681482817, 90744614373953, 88519553860161, 90744681482817, 92771453920961300177846456900257787100375552834, 90744681941569, 
    532053419195225453159961223452989326768769381284567048433784117499900101998226761418470086277440226180, 158469400301760, 158469400301760, 4254305046636047378541644972107202048891929538553020190431143210666200547386925953482176841484804357, 17601053856192, 158538052669632, 
    158538052669632, 158469400301760, 88032875188416, 88032875188416, 310614997099329, 158471543591104, 
    158471543591104]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [73152495438401, 73152495438401, 73152495438401, 73152428329537, 73152495438401, 73152495438401, 
    94198707058185130793920158283701001145049682754, 90744145068609, 158471543591104, 158471543591104, 158469400301760, 17601053856192, 
    17609920615104, 17609920615104, 17609920615104]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b9_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨3, [], 0, [1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_15_0
  · exact tv_b9_15_1
  · exact tv_b9_15_2
  · exact tv_b9_15_3
  · exact tv_b9_15_4
  · exact tv_b9_15_5
  · exact tv_b9_15_6
  · exact tv_b9_15_7
  · exact tv_b9_15_8
  · exact tv_b9_15_9
  · exact tv_b9_15_10
  · exact tv_b9_15_11
  · exact tv_b9_15_12
  · exact tv_b9_15_13
  · exact tv_b9_15_14
  · exact tv_b9_15_15

private theorem tv_b9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 1, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_0
  · exact tv_b9_1
  · exact tv_b9_2
  · exact tv_b9_3
  · exact tv_b9_4
  · exact tv_b9_5
  · exact tv_b9_6
  · exact tv_b9_7
  · exact tv_b9_8
  · exact tv_b9_9
  · exact tv_b9_10
  · exact tv_b9_11
  · exact tv_b9_12
  · exact tv_b9_13
  · exact tv_b9_14
  · exact tv_b9_15


theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H2 := by
  intro M hFirst ⟨d, hM10⟩ hRun _hUsed hForm hMissing hLoop hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hM10])
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hM10]) (by simp [hM10])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  let m : Move := ⟨2, 0, match d with | .left => true | .right => false⟩
  have hm_cmd : M 1 0 = m.command := by cases d <;> simpa [m, Move.command] using hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  cases d
  · exact tv_b9 M hG hm1 rfl hv (by simp)
  · exact tv_b8 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R2.H2.R1.H2
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H2 := OMA.BB4H2.step_proof
