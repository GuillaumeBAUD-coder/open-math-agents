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
private theorem tv_b10_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1162192523235776, 1161230450561472, 1161368023863744, 97053213341864731057460873792812928236276175682, 246842648500417, 188397414118862715603836679240523322994332816194, 
    1161368023863744, 1161368023863744, 2923059026737489031994782433108270003917781226306, 2923036725907219914712008682437071028210169303874, 2923192831719103771185641743525885129746305536834, 1161166294815168, 
    1161230585041344, 2923192831697836194241497359674730537644030186306, 1161230585041344, 1161230585041344, 1161368023863744, 106105088837697, 
    106105088837697, 106105088837697, 188397414118862715603836679240523322994332816194, 106105088837697, 106105088837697, 106105088837697, 
    1161368023863744, 97053213352498595588559408669680042971727156034, 985889914280106651719924973826288712043684318479730169496497164527679558014588998369740912979680820755405772109578928494616766799405411329572887502194929266338054798634062906685618445229351269002431945118315857618598142273889314426316805587969925458652300296245997512, 986300481606681895427722655753053326368583723889986813524878326578036852294067907499053623132902443349788211349047888460455792793759774369213984471105067616945340386692844300646201735839664793614843784857956026971956027224222263936224880390231134596382065672245997512, 64888527178777394292726084530644438069374075529142258349331624157991835659082872260827106435462660, 64888527178777394292726084530644438057171389755550550944434849519276132146179893276789023342392836, 
    572854693794240, 572854693794240, 581667966686144, 7759266745547319253283132029449942412559925652816067110688989280332624922651537520929031454999474710403676530026757081107937933005238216907955156682345197897021306645246534, 33283751484824637256498319210394984672175035088843919516823192365638499410766864089871601360896587268, 265751224421003750996681556266260857299344152924196091844706190003795997299451077668383975182434468100, 
    572854693794240, 736462597071960573118131364815653605554618651458, 479600174901430983578310474522501919309756913474, 572854693794240, 566259771511232, 572854693794240, 
    568460942250432, 572854693794240, 28545062787022455079218812018139998298270880578, 105624522262593, 105624522262593, 106105558599745, 
    106105558599745, 105624522262593, 105624522262593, 188397414118862715603836681306558659249802597186, 1461685619201901372444224211602021964651211805506, 150642228859328, 
    91524001263601485326136639974898517690527273794, 4217239420481885636211881718396241121996895082345312794086836267525469162424114352590520647534473348, 8369598326593329836429376000480950749743964767251073467543208054131263541702573101187822702062767620, 33283751484824631724446425762283836221746149921812809320166915086863740099003813990999637272300843140, 8369598326593329836429401759434414719626425658249086019247005487842290790100768789934303109571474948, 33283751484824631724445106818017367416921045251240919612251833609528510926415343107504816478192103556, 
    596966457810749960805340755984358309692571200534275863574133148774981028531476980720163477217934012548, 15488342035310490762460673676091772705252472612117988229446376022676007557192402720366662819703721693859016909411165331390792609413803036893372780840654234898326256916540998, 15488341795068494133853986833984627734271689341328638928502284116372349735127885266764201037434158309544781211930698668204737939428561689884167019417593684233261547949043270, 15488341795068494133853986833984627734271697659168493383766268703331999056730705825393123380919875839201715718698198812130593278809271276644349482503263508347383428393643590, 33283751484824633568462844125612451598521274041525347180320281697844698591785250072572157526664082948, 33283751484824633568462844125612451598509071355751755472915384923205982888272347093588119443571013124, 
    33283751484824755273633521923436043029485874619799508328075090853728021312363860345724549604250285572, 572854693794240, 566259771511232, 581667966686144, 568460942250432, 572854693794240, 
    572854693794240, 105624522262593, 105624522262593, 581395120223413659886869390627426463909128703304873447816465668733001657821266443973340683125721886852, 175993266444481, 105624522262593, 
    105624522262593, 317005641099585, 316730754804033, 1461507215281996944391295781243578430755270841154, 566259771511232, 581667966686144, 
    568460942250432, 1461864025844049158974665033710070905308622910274, 1462220839128360308925541993883560239316120654658, 1161368023863744, 1161162066891200, 3957317621643694791034181319997630199813984359540437279068292281375116768908022258221836439962487129932173204658429136777709511399564708129258197048555146229777290346285223495, 
    531571439926105778932383466683754414254415366513983012490357296471514409535946556116477042130935535493, 2924441673409015413141749008097622393832108741442, 1134980013232576, 3957286427485527111778661891709499483189078032854766494377452646512407294094090371499094231434318853575002582213786962644090683534981877962100942506844505505841942197551746631, 3957286438542057654937405121470994564346813970897303669436962639168614438158654912456589168604147546091738867614109842307289040258395360688393606558461779899435428004912082503, 1161230584779200, 
    1161368023863744, 1135254622966208, 246842581457089, 1135254622966208, 1161165958877632, 1161368023863744, 
    1102970368515424571948412233889837151021649385243829491517916915498320403237105686623651011145813380, 246842581457089, 188397414118862715603836679240523322994332816194, 176473902289089, 1161368023863744, 176473902289089, 
    188397414118862715603836679240523322994332816194, 1161165958877632, 1161368023863744, 123695392677449368553386493471178429479502205860844919282900085640861996919430318870277143993937610328876646812884823367471226792667496555945268613412874485965207376273649223, 123695392670135118874259415819966837262054512654089215527300686440461783328613314510414723335322932683629246455174791043641143820629116834448554724178701673764603522423500359, 736460179664830126306997170297233696473661592386, 
    316943362167232, 371089997073237616976474383349547598989246878530, 3957286424260705703930545572090561063477159175196915907376166662676140462400758948036828680258092899397552820942187192684118345580442472371582868210868398658724065560241679943, 960962161246946106553613076086465357131036759671323635134125297822113308052209484351011208165369165167585729455828723300064517432407811837568855559408312297481478623836337589536748278140847005429440600183959410902179622900818718637618171305242591205055808512249156553, 1161161664238016, 1130856844759488, 
    1135254891139520, 302860714939843493534362401949584212706720400288109217380040198069051387860436502344591765287378642155063049270810756273281712076087905856026110805998151174884995404484167, 1161230450561472, 1161368023863744, 5777511356834555515219647630061847477074702918647034492580000267644424107759305187858171693335561120613301092601108927869281436339017249992738947069412923402862317832662456387116890667247950542555145567328107730873023725020458136249479471563609309248448338870870752591488233847408274250949729578306739540056693151178710352788246251495207536508511086212525130427256661802318671081112579799163939941987588600514141358464089859300136673698110059841684445791511762675968234259309289097409660700527376700461420981570655880742527981200325737724943936123351443382326291864014593536957925160478334247753731829500928012105648068604904111704183352163567745113173521313359, 387099505469761, 
    4217239420481885636213444533290124918089668315388447499760306120234593242876281150848256258046390404, 33283751484824631724448431660043339586902202521825504101652894335913188321997658367203223186693124228, 1161230450561472, 1161230450561472, 1161230585041344, 1161230450561472, 
    1134842574672320, 2928723416146187607405006377856594668239693306690, 1134842574672320, 2923103628356156592299588970364563135031341503298, 531502440922011507987686236580303748944326178567855615118265343644398169661714195309067696898845090693, 1134842574672320, 
    1130448823128512, 1134842574672320, 2923036725865349225239460515353958832178645193538, 2923728051603692018194121214461564138981534225218, 531502440922005843165168365441897534846965065808643746884658228480132777112521542389293554413890223493, 2923371238319386060540102789115703335470365692738, 
    2923728051603692018194121214461564138981534225218, 1161509556654528, 1128595545067968, 1130723701297600, 1134980013232576, 1130723701297600, 
    51381112941397519878449242232109965178484839234, 1130448823128512, 105624528750657, 105624528750657, 51381112940722843231948597316778935594842606403, 150093009916352, 
    6767287374885997093902291746569410401516562736030096685260387596054770198621356829905004381020575856440712208873417660643163690767172507248492580287015461377575345985139061508745500451996405190663663101462151455170974205526079472978868483445672848432555219362146549978389285898337030129289822055620379656985261218352891635486950567727872617254195299076847163970355737246087094218, 2923362178651623597769214953275735501830860337986, 2923719688834211817208348016785164358056950125378, 290830498402752, 284235576119744, 290830498402752, 
    308439864316864, 572305474851264, 565710552568256, 572305474851264, 572305474851264, 572305474851264, 
    572305474851264, 572305474851264, 6059625031706314223707550154661728396192740636449871314918306649817884444022675186291152654844532043355990048385154516023714760416572814287395814614091644176329060717734874695, 4081465830602461327507528779642176134397774141327783471364675099441821308888342557529135202338182853104100934823193066249992841744034666622276491267195010211252349730199391815, 4081435635217552574686924372804637969392972500873030933009469706770203752378123918112068194951308797191233209151372697301015160145172498772514786854189268435212661420141268551, 4184086473139170113139551377906408244332120736991461723925990267582204679616301682622973871527116236367547345819557558558940907498549005058638793046746551988221484175298886214, 
    150093009916352, 150093009916352, 2928723418532815193509639225596081491855743669058, 943478696055744, 2924430615081810508775530735286283366472372770626, 582838882145216, 
    371799420474063851423504315845482329124391375682, 1139244781801920, 1134979610841536, 1134979745059264, 1130448420344256, 1139244647584192, 
    1139244781801920, 1139244647584192, 1130448420344256, 1134980550365632, 871389817476032, 2924433315402834117110101937132143026071945663298, 
    149818131878336, 290555620233664, 308439864054720, 732002495629432090340960182324718831202253959746, 943478696055744, 366090429703240011899271171967684348578860389186, 
    290555620233664, 871389817476032, 146248074531264, 146248074531264, 532345381924043839394587228580701299332535439625827021254190390578454937288667962801542454418498351236, 551485156945714612344931938677766749185404960269287372796916445009045462464603912841366031205199941, 
    583925464646046210032322761879718552918034719655875370994745809412683899127542596306089656005983109, 930128885513709663117093471377052421616564511323571471858714647401482207368242196036652152236750893188, 156209043083712, 97053213332550039479209989992959978697417298755, 5935929639385535577429803503125780323649620057910127867448906346559964672246525825790216583736411111414682439423199127955262291716340387068156758203151989294637829299168574023, 123695392443150858820958396886328704180835870242187726439453002486238387720688085043371051444047312456240092311681427703789799012663347074877407775982532138229399071926242887, 
    123695396123262342757292935738136197860268167280718649810263118275536539591136108077374228011139987859525106974202982857763503409433510200787219110482954005964305673589050951, 33218934237609691583668613582334353027404647282541255635333050550130512604901900712293545108513411269, 537276300084205755764961924168696525500972770977521969075963279112239176127777947883655760180101214340, 33283751484824633568463998202056886966662908155405518760116632386452271230494776857040693778890807173, 567907428209088, 572305474589120, 
    1978673477309610648612325225753955259882136714895893642931657234658799148506035481573122551025847668995834903669766358728148743452035579207366056967280552725353316639571965510, 572030596682176, 1978643215585518646171095656064068763669315682367955551771229793093406090190997195851982664773632348219999078997239770330436657443484239948494396165335502703251999318651927111, 2967964821535522878989962557807750047221304721201283969975632787949562824173355386810400718756207461749177681335349906406377302153529670506698100698616581778068372813034519111, 1462399242410390906282614950250348926568039994178, 549133597408331164252474600524216215481041842754, 
    290555619971520, 290555619971520, 4184116666679525967585436766626298376858117259588101159830069557051822214627639089090615781128348263369365304253940447844029119958275967991772120349792277763535762167131241030, 537796105276741744684020501629611755130445456271463894500083793965740089657655925186543969689174975172, 146243779301824, 146243779301824, 
    1461685619180623542704268465899486437583890748227, 290555619971520, 290555619971520, 146248074531264, 1134979745059264, 1134842171888064, 
    1139244781801920, 1134979745059264, 1134979745059264, 290555620233664, 871389817476032, 79311948353984, 
    79311948353984, 79449387438528, 79724265607616, 75875034993088, 79449387438528, 290418180886976, 
    283821111120320, 299214274171328, 583925458845267951735794218836553334534592207725049883765662838731439605221917755555461922276538245, 581395120223413659886868525070238542403632482699997916094739524046029575447783464417124879683231641732, 583925458845267951735794218836706879856607631964104951617987403440057297799590417335824911856859013, 17127037646852446046594006511604511702962668355, 
    290830498140608, 354604320035264, 290830498140608, 159437918704064, 146243779170752, 537795352846196041671507566507691956330410347606432603434034180867665844880598418481707272351648018564, 
    589699837819074160131238203182591064576023755405719285643747126829862168797695421558464737237473128580, 583925458845267980548559346308943340335940677614917147610024537459734045785078116201487487389430917, 597874794202302459844176738222032291037700726359850857452666572039214007822403573179433007083672531076, 105624268965953, 105624537401409, 7172613131733410130375772333950610988237470931491797415099183765071978095699071877389589218366715611088318725182725699243453282792926693128384266449449252193492778326519968326, 
    566259771511232, 17138188019285557858111373427175232349852140099, 17138188019451711357584487911288208301106659907, 163857843229632, 4152422173266235318099053321687403872139351983163629746053029730044369508543084092836984672021208453, 91433404145939703154661549671229100899273036610, 
    91522607467016192568166156007694301777065169730, 91522607467016192568318481242040399998826337090, 146243779170752, 97053213332550115538246003687879241812620088131, 97053213341854670943921207494865043340079928131, 97053213332550115538246003687879241812620088131, 
    97053213332550115538246003687879241812620088131, 290418180886976, 290418180886976, 7759266976060414801213070427961325411673719582358885995275181567931121550098634189431189829757072577890527525301894252312794851410381571867626128613403276153124024239972934, 30946491887137527512635394397712577111512823296761823934514076658901896438619759386000862258463422778083601639399050759481929700299007868716984128092618311609727700052520519, 16674316293503636767759155338488789874573383475383273916762540505837848875220696401019872641034294725, 
    2076195733906855321612002474673359026728087012909682768786220147972022392550647139071258568154997188, 290555619971520, 290555619971520, 146243779170752, 146243779170752, 146243779170752, 
    1461685619180623583269087673203982458791403787075, 290555619971520, 290555619971520, 290555619971520]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1162188228268480, 1161226155594176, 1161368023863744, 97053213341856942582462510608521005894203364162, 246842648500417, 1161168509407680, 
    1161235014226368, 2923192831697828405766498996490438615301957374786, 1161164012982720, 1161234880008640, 1161368023863744, 3957316615583996840305502105275119275146462354483584645858008412828272418220689533581972247716342617507631939523255966978482127237097631810502091741832596975364596424349363782, 
    315644150232281319585688704440047274065724013520331488019333708472483661730984058615409985961264902276, 106105088837697, 106105088837697, 188397414118873100197553748895780383986991256386, 7759266745491082830854615465272516286695947219170259193229193032845680277271928609702070183409153745425390482043033845228264497877660088695242869581933548039617762857793606, 33283751113574826881503524441640741768576169950949607551338065188493535716951132493214524170132746372, 
    106105088837697, 106105088837697, 1161368023863744, 3957316615583996840305502105275119275146462354483584645858008412828272418220689534290860767521769375914189116393078085580066195202852812546177276587702096847823663435043089990, 176476053967296, 33283751113574826881503524498662970085759807968099669022920617515048280873030983126616949409942040708, 
    1617723703641840315648101931354441611284239374022718320678913565690803504456614515368334511843149237858463555402642672372596272993555216932475359167439158930829464993646144893095612648015099757893960491486739638065256248753868789068244535795556152740746888200245997512, 3294089090345329113525181418652120263633986933570, 3294089090345329113525181418652120263633986933570, 572863283729344, 581659376751552, 736462597071981342345179585383299896336707539778, 
    736462602516499213080195000797293615244998923074, 581659376751552, 371085815683523277117811753219554224322121847618, 736462597071981342345179585383299896336707539778, 570924688307149195025008166154798084985582583362, 572863283729344, 
    566266213962688, 568465237218240, 572863283729344, 28545062787014666604220448833848075956198069058, 51381112945385219077611192589574204322985562946, 105624522262593, 
    105624522262593, 105624522262593, 106105558599745, 7759266745491082830854615465272516286695947565753970958331050480147453295157392060737914547014663726457434291774350584945937844695333966827441866113674544479870465584609350, 106105558599745, 1461685619201893583969225848417730042309138993986, 
    84682268545984, 73687152268224, 91279338312640, 75886175523776, 80284222034880, 709207020671936, 
    150655113761728, 144058043995072, 163849253295040, 146257067250624, 146257067250624, 91522628564564480160368481458899827305853571906, 
    150655113761728, 172645346317248, 15488342252101899237017496154746437805140404184502134242012094905180621061254801855520760079657442436792198065514231942198628014210375451931267902132864348055375229809176134, 15488341795068494133853986833984627734271697659337723697256933060269423403162753533445378956628061171276423459325383095500193663285724662179423189649262574998780811251134022, 371085815683523277197194658829025044817323774786, 371085815683523277197194658829025044817323774786, 
    371085815683523277197194658829025044817323774786, 572863283729344, 566266213962688, 581659376751552, 568465237218240, 572863283729344, 
    105624522262593, 105624522262593, 175993266444481, 105624522262593, 105624522262593, 105624522262593, 
    1461507215282038482885006303636003181116220592962, 566266213962688, 581659376751552, 568465237218240, 1462220839128391462825535446620727928684411966274]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023732672, 90575098211533486263658875835525405557956262325384789411561096367837584018056756665999346799387155741933830245068078368928717095825903206743989882786374883481125897154119, 176476053967296, 513259120171080175753226092837196870740343357413711208872743735545406521996694640062494244155431912229273297616590101396474417815677950181293249552280126172327256519913031, 581659376358336]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226155856320, 1161226155856320, 188397414114211718193375211086718723749283134018, 106105227319489, 176473902289089, 2928712461435939096728503192229893567414777444930, 
    1161226155856320, 176473768067137, 1161234880008640, 163849253295040, 568465237349312, 531566814648491542382947272046950254175005522743756402358304206477694553888936836442413428821875944709]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023732672, 1161368023732672, 176473902289089]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161230584779200, 246842581457089, 246842581457089, 246842581457089, 1161155221459392, 1161368023863744, 
    2928713681017920316200118024811600876564977308482, 176476054491584, 246842581457089, 106105095590336, 317217971900864, 317217971900864, 
    1161368023863744, 317217971900864, 1161368023863744, 176473902289089, 1161368023863744, 2928713681012603383974260210473049508715708830530, 
    17127037646852446124119546352047797124823274306, 371085815683523277117811753219554224317826880322, 371089997073248001689033696776201166372221244226, 371096966056122542508765426688161368985191863106]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226155725248, 387305666062657, 960962623049271792066550222853127700216391238233388630342511442079169491564066320503265385309709892588194564491764103108313298865179883064971183086674359025162856497505490205855152649079206193176215506676135415689459679103771867610828237410619062414880015368749869512, 2923192831719095977640021636541774791055786398530, 3957287367290623191565779142076835871100275577086034096759580964391097153022990195711243382652522260208150548836840749121141801039198066556563110042556327789462996730383398471]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161159583863232, 1134784592352192, 1130384398095296, 1130384398095296, 1161155221524928, 531501997402235843673079251391498396625605312665097025177289656288938192430147855236054781760230295428, 
    1130865434432448, 1130865434432448, 1161228236231104, 1161226155725248, 1161226155725248, 1161226155725248, 
    2923103630738124074265805632697383515061938576194, 2928723416146197992038337528768982772124921944898, 1134855459181504, 17127037647351882010215725306021564419439352642, 6786989525284217980296104277765329144192625998130967865061676583174901665904577925653375850707244479493780080054784518556583337422052719078734559139883209660750435033596220401088714670092525501679293968436894751846429540632769706694363440998347725520685384728528394830190933410904589501128634120853027746468888454638374056668817283638298208065932368269236664943263033780881228874, 28545062745142526938805336373567276776832392002, 
    0, 1130457412801472, 1130457412801472, 1134855459181504, 1134855459181504, 513258889805605223322660477602494454177167359680385778523987163160918799298785694561489060155259322522689009820791894111673779590028702276146522366209840511257557805792839, 
    188397414114211555934098459755508811647340796738, 371085815678861874791532236836240209365629426498, 1161296955707840, 1131007168615360, 1131007168615360, 1161580423614912, 
    1161374265184704, 1161580423614912, 1161368023863744, 531502060762209460540554850491807979999878697559114700297190145738864701914066095432877487310573194628, 960962154094212046835217857624440951243359382280315518482490121334476533306185990189595048697409830025583479115931750073887918846042871854180621295508945741583309341626936967091649550899027742658509871233899840945804589701710234356934680079270449217890435593246988552, 1161374265184704, 
    1161372184744384, 2923728051608344333965626677507742543217508242242, 2928723418532815193549330678400815776194847855426, 387305663899969, 316936919720257, 2923728051608344334045009583117213363704120234818, 
    2923728073386415816985071244773188239337285768002, 1161580423614912, 1161226155725248, 1161226155725248, 316936919720257, 1962460461133904581120051055661515031743141500265131503804660760558819597681332446183386008156141299122240077625885138771565201544707108174050501812506983404074189043641926, 
    531506258360201468241526406609260494532571186939662600175167222363530425292141727991221803521690100164, 1130865434432448, 960962852420952156108866577342046869517301313185600229925932242417537337386704402273726342439597801209705035097878318716212170909209304278620644701171996983605831712829047668602789437944571079846200623469717325480237640274096312540300163765824212436068074504749869512, 1130869327008704, 1130849932284352, 1135265158927296, 
    1135267373388736, 1135267373388736, 1135263481074624, 1135263481074624, 2928723416496427864135943205825999822611313349442, 4152374699697205453578210812462678843257511339888420574023145928562375941121238797791042479849534980, 
    4152422219673169487284364745720631680533805825575917028903490445916333060823360904008926746340554244, 960962154310961563796381349092987151144748375090170272406645434056601509036110545314688252114259625885789893472573917070039537801698584046544082916862614964330498045730834922862597267007520525196185360990221862995668512425312157730258658308859542877111321608249877512, 960962161246946106553613076086465218325102661266057768697720979430207109555524067777828971004691926426173572727874711773197570002640726331273244134434109052772558808194870656401960031318829511440270071298927364683000215624717864912764677311986854811383366664749877512, 2923036725875357780537895060156365969151378862658, 2923036725875357780537931328069304988579441685058, 2923036725875357780537895060377726898035893482050, 
    6707465440523364112167751531215043645898589142114637738100752393845089266622328091197551797422297112616002094817482167332815268125104674335932041935451709964997657826810215892381048109902110738521926083062695477888262894905352451857907601557115875355047335489473843573136739961743604517970409327475042078278144731556384659257028637215435451755413730548874421137896332020707575882, 2923371239701149794513623937203904630659446043458, 960962852420952156108866179897415239361024108221294425755693281533781367665818651474375850183486627175161911000239853280137360688780863369190918989262565005732184638794188869475812766439351400575904332176787556539181348667805927147696764426983987179591566344249877512, 1130865434432448, 2923728059791103090571527337015482366916839953218, 960962154094212046835217857624440951243359382280315518482490121334476533306185990189595078771172902829105508456952616332978182451059046332268236488364312721002263001953528906685707064146866170824260236878469883888574496579390632703190086213016822203014988297246988552, 
    3957316620106304986593311820918825768331474619161198352934768992404644119681652957342703752295506418225560697734893472186900809010331893527713115634455680620167324352919862855, 3957287367290623191565779142076835871100275577086034096759580983630358026942147873426733313853665863834293534521592480683983591869107542208299343420952661162447357494576511559, 3957287367290623150376993181293177581232129621775134213640547544622941715674683641855468391396737237472716147772493884366643837143062828083511816114053315980876295000001837639]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105624520099905, 1161226155725248, 4173730716559838907521224156855810685737056856902172784545311953959516555008880659825660147390942183064862771431879823203547171173685881144870086474713058639893111255156619847, 316936919720257, 1962460461133904581106957493229739927852546993902125008682957726876891679551987603384016381118248908026741802662286742022715614034815490511057936514801802008172690434010694, 1962460461133904581120051055661515031743141500262487259755672592434767288375416216805801822828789154078951514001101357273225380734255155832899442754905135128158421269196358, 
    106105088837697]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161157436117440, 28545062744643415571262815846320327822743197506, 387374385473857, 1161226155594176, 28545062744809609001729837519659450851429209922, 387099505469761, 
    1161234880008640, 2141060021566760805619948035611080667358320270466109414635935582067122313379131891727005723079529540, 105624528750657, 1161226155594176, 4173730716559838907521224156855810685737056856902172784545311953959516555008880659825660147390942183064862771431879823203547077637581091967083321438883764788556481238619093575, 316936919720257, 
    1962460461133904581106957493229739927852546993902125008682957726876891679551987603384016381118248908026741802662286742022671768985951966186996260481541669357882790527741510, 1962460461133904581120051055661515031743141500262487259755672592434767288375416216805801822828789154078951514001101357273181535685435868216537488721895241176834651230416454, 371084770341401239745653416226315238015823270722, 2928712635670479399483337775518561934056961890114, 176476053967296, 1461529513347638476386347103257350473108093666115, 
    106109457338816, 176476053967296]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [316943093993920, 176063737500096, 457547304145344, 2928712635702382940195397476339526405876294374210, 176063737500096, 316943093993920, 
    736460179663825413032072919536632941031702156098, 457547572580800, 457547438363072, 316943093993920, 316943093993920, 371085815683523277197194658829026170708640682818, 
    1464361729723262950219676828343286315042191004482, 146239484596672]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [80268786536896, 80268786536896, 97053213332550399493218394849395384036026749763, 532345381924043839394587228560890267803219799951076824376393939687286849720736025968505713119697531012, 961781914072982554326947800875174227090394140932011133272030275468811910536308172448335333523592454172955071982440930704509081254841316752344426293743398848013098025342028054288333346443958212815747208368938065040349936588664777691595851134999119428665213448245956552, 6788908546439210076729245246080569588370271574375095490805151853352107588362934943118204715555414584539392466394166566595898969755829397195355542337380363734020873110986665158955650146973690770988819731362690643258685016495239569606792831460403182436573159388312985162773005544829677399019815221758330097747010881572566825128799608447584957358748224461934449925756536343551144906, 
    990991763179976232357937877685350807161266908696318179930298669912388256378152414629410193643163016063093270640896441059847125725174720882023093042640252511496536137511246691416999381487336584683099528694905352581836708657292059792346183001317377107011043848245956552, 930128885513709663117093471514576619272731089636914613665743363781940069524210559287151115239584231556, 3965498569491706872499699489452407154688529658460578611213993368459437178933119504942303673154897302384945645392749073269841256964677815619353088220962820629812744677960448070, 961450161018512355988725026902066334706281316218122013853342406523312704098790716990024912293692080627718609497296472527265844840640183179869864001477271052799225541846190187853696592836300995486363813336148457884625442573414284775938117088311630055736345608749877512, 1038343202259883994768923266640158561829485373178150443628987548090679415780022582056566035270652996, 1038343202169246833807740543720626727587617300785395845812386675637128573527716547169091159230305348, 
    316936668324161, 1962460461133904581120051055661515031743141500265131503804660760558819597681332446183386008156141299122240077625885138765625658890580707419793889113809474227895208460594758, 3957316615499469982613701026949970206157261116843783760598096930747172428223431036261196785016095388258149956928433328915761504949033386054559597795422134095085876710338637382, 51381287167288566494271649909317494190049883715, 15015502880113495859264050485694884160399745310558569153899589077804510367438702592869274372590686649420915138280769756843317183941006074922258595944008813374469377338624089339070510778120126363114741605905587950973208829863566205831884129751391544750900232749869512, 291375019069888, 
    3020056487994356235900588060281961423347891835715, 316936668324161, 6810631865913720620457058171311035327782310330655124230545107782487930982815876812596032207241955313299405951392443768422799759867051915326862842544717428084863795959576735161331451364107256241083334877047148182954861523809340697244108981708750318208443281413724089965819282091083178412742577420712246526779967587674135944610720364865011453173238613586443907653587025152685670474, 5784956773199115103783776397074239025554492555712750831006393108340552546209451223893080456213065741080083993329247120105988450191318670616067603528768188541481633105098333783442468344263285171931604520636873062198589766896262866108275059017595255079852944524106561458492147984898625605672155809866325360728057774228303701914179277227691654235508435681523118718002026943635743161283895561213877950294913792846204869329038109500593916224632954639842596685975774549475234415836864373885039018406042140715149703446480036626875329986511866947128736102421874576058858491954176446967151807178323990951837008476550374852835532713800082456934156241564297359552824718414, 8369598326593329836429401746227057171012358197331087879978764043238928737177893702019844377047733125, 960984148772202939775489852405612533455804850080814786982979020217367351276564554763723209398747656978410764339688687061553686472018813116694321128237111292048616994319783040704098632002051836559083204444024562628438695920121377596688868969055061298215141897246988552, 
    284777949303232, 284780029743552, 284777949303232, 15015502880113495859263652749966112872573547049480687073144299086536775311389906829487199454272907587160906529483380360881785394496667674749541901955232587431907533841834040327108994011485866503016765013219500018689067153279661822761977846545808998434604040249877512, 365466006455704444305170270850659030476758471490, 365555209771630480104977683068793074137457251138, 
    365555209776780933718674877187124231354550604610, 365555209792773268890190957238013935489929794370, 291375019069888, 368231309409075616123813067281080257701199500098, 188398111017150392755177291222686647486502683203, 316936668324161, 
    316936668324161, 980281271336710796636931575029092713821678966986401862880592682920402834640318437778204167746857366728216577195917913299360789748676075100071364724103432094181823592205949718087592447877994163468922305270573375415216111406785957466092364142639347874710684168246988552, 316937205195073, 132875735960495930061876752971200258046912243841536599009219596024801506660145502076439467570959023300, 480481546266110744842554508686322220301213297080224476221576583989058135165810506710177553683086680337862520722595673550412548950691578128704148770727147213737639164253264264131484478553208810385470380663347414385102102212121047049359001681680363986584863752749869512, 247360593230090965501624659966305234041047830270056508149236969820521352927646154908216511104655243606314505825275888374417430603759596172034697266133872532506865035143065158, 
    731467232837867824773836406165920945243206767426, 129777547423926009027780781102568141247809614630750972816215814379959977636285776786036271754562948, 2076195733906855321610250751793454803913980796492993811941002800266376297353556591906568139194819012, 33218886717633724322929770282846208316897019609211577292832712416407294898690901696809532253276272132, 581659376751552, 1038216427127841050626293396355569673326158933651021827598302640312507228351327647994806827390994052, 
    365466006455704444305170270850659030476758471490, 480481546266110744842554101926582037516884295026952688057685822915922451476555041798932418578729115370555014336420357743572125930804867973184077134045225392741351259572840640029944724969043680722558461179519755554088356162248097288089348629017050018863907848249877512, 365376805856876505665456302565932502156251779906, 1461685619180623867224060064365498601014810448707]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [366090429703239870199702515205918814333908833090, 1098268501511252861370602039401303312380238811970, 316943093993920, 11446249606038909791595293632431916925033984578, 22880651898655641884198941638312866693444032322, 316943093993920, 
    4217239420481885636213217601802303497115326521374029147114658860942937829314342847275797782536142981, 316943093993920, 457547304145344, 1962460704686820593779992290798329989834049757711014652977392115646431684129812504207018496129758145811134284098791754939300871892342785216809214445031903329977286704672326, 176063737500096, 64880609116516277184813734186923593362560480604678022488897823357108663795628167019326130175926724, 
    316943093993920, 176063737500096, 176476054360512, 1962460692040655099431226208491831903385485126292170185509679446260588540400350100683369653359495465822170418519465795807804209558056784623405270797795965084114116964429382, 736462602516499213080195003158479108488225149762, 365376805856886890259173372221194066765717459778, 
    146239484596672, 146239484596672, 91522607467016192538472520312248781562731057986, 146239484596672, 1461685619180623907788879271669994622239503356739, 123665318678276766716113370088301741753311484091595902776425324917401800048546041823665746994598276685745084181812074415429757505458639784305199320665164444690235727033970246, 
    365733616418933912545684089860058010822740300610, 366090429703239870199702515205918814333908833090, 366090429703239870199702515205918814333908833090, 537796105276741744684020501612001949339104881696594565793659786720081807489899613697586978278321857220]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [75870740025792, 987180268735274236721164190570654642113553882096932472587493340292329456568739926872019955161832706010577600073590516391830707632160048426497882075540031063474585803662384418438363980157274735011197087356898937887837003457043571834290533364756535187007865352245956552, 6810605479372839473312678947313685515888999450940939642987787995526756837538343710895857923223530994946574148252278649910723035125030497535518938738908742523216390987522157255564012301566093795945653189513156577549667634380828982539092083129159423498280428508533947311137847834868913415602742370580757660267453617512269102732528564667225217567850858764754192232721594768705637322, 123695392679681251582055760644742948658005300172004416333658412149568600602428776360705829141086206777631794296168607029881183594369825231163129119366000409578288784031919686, 581395120223413659886868525050427510874316843019434707441899713608543722068787808368804439158768758916, 105624268965953, 
    105624537401409, 105624537401409, 105624537401409, 365733616418933912545684089860054633110134870850, 366090429708556802465251782349202214713877877570, 22881958551052760409978602157834375398577689410, 
    366090429719190666996350316635775770899026826050, 159433623736768, 146239484203456, 144040460947904, 146239484203456, 146239484203456, 
    146239484203456, 537796105276741744684020501612001949339104881696594565793659786720081817341735860740162242862926439108, 159433623736768, 105624268965953, 105624537401409, 581395120223413659886868621243258330693075244354193489877734265255405148105417089149582831220631498884, 
    581395120223413659886869390627426463909128703296509075172314841182015632995667887918699038224128635012, 589699837819074158287220465640199798039190773543900892484645411581795371308298060350388577047822954628, 566266213962688, 581659376751552, 261549947706041557390176538361675074190761867923720445898180746225538557692964671058852946911571589, 581659376751552, 
    37895173739116018876381519242215575713563167298866293257704974100558416907332609088622784439090613109959126044473285271598591266498444704678960060311799124623476790489882456264985193549889372617427956911486388019181155269910342876509121350861991691544495522894800830629431851393031502733661362970585439910608052264104885276811527403646180874158149836038654422126701851268824568798420587619699182526357107625934812398085269187200954576541631008832934614674421803768780802186291556582452925061546228415807308, 4217239466888111241578027001395728598050171987921162959811410130351327234467080501698969015634063492, 163849253295040, 229804448354752, 1962725818090091579651638347060604675358202756129981882174978147264245295070825826987194369241592217806597071581695540766731368302656885891152357237078387182028542457607750, 1932504634610075330541888326597019018174692574434342298315643794977988994244199696733782811690626758876920293851953191930159645084929868405333391360948965865847358441846342, 
    146239484203456, 97053213332550440058037602153891405243539788611, 97053213341854995463712805960877206770999628611, 97053213332550440058037602153891405243539788611, 97053213332550440058037602153891405243539788611, 4217239420481885636211459009447011757397331037038499409718394504232562167625650712101975570646319237, 
    15488341795068494133644489835076226072023621789523985468774741813217046803138248546360433364164626455615415769241154484030994273143548433157026459005997523007285952039398982, 15015789008703664364621442323710524463035778721684877943375810869140854992632250509065913257213580367565029486817663703436621944532231773879024425771242154091479256948629484532966926569514184518705489663781995379565086655735413748473090177597271921420944384496988553, 984031134860398729935032438333938181533334618187470085077173038011176967564846358823996060250939581600991362108177590201206189772174103375346686864890632031874923781336557315991666663278504605656532601034298593304183465210108712569716263008725927001940034568249877512, 188397414114210584911291741378516993596501014083, 316936668324161, 8369598326593387000979265560356319812834796094080789978614383980016580763289836275029659286869382021, 
    371089997073238265976211384383362794333501671235, 15015033881354251346468457295809488271381027041708212402232588244311368243913276078397597483212470435915314556538594539260218318327692114978880502376842915345720131955950099092503205137920375025365275323300759313547557173490526262203167814782323577271091456749868553, 33251310933491616332457798577226144844615965494142563324535519893935401826040348282831800031848124485, 316936668324161, 3957316615499754679502291219524629626874653578324212241901702282177686025862834024344906026180929133002406981213395449578057914662518438203260822076419712211119916679070527046, 316936668324161, 
    3963113421784280567019334247361027607891104697625748922885791126424424314030057337986473555277332392846794966228359189856920559762862823873813053504673019054730010289232719430, 1962460692040655099431226208491831903385485126292170185509679446260588540400350100683369653359495465822170418519465795813042231426513268528316679672093581250819539254816326, 316936668324161, 2076195733906855321612002474673359026728083102767198364344308971456243558107870186589764944138396100, 366090429703239870199702515205915436621303403330, 146239484203456, 
    146239484203456, 146239484203456, 1461685619180623907788879271669994622222323487555, 365733616418933912545684089860054633110134870850, 366090429703239870199702515205915436621303403330, 537796105276741744684020501612001949339104881696594565793659786720081817341735860740162242862926439108]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_3_0
  · exact tv_b10_3_1
  · exact tv_b10_3_2
  · exact tv_b10_3_3
  · exact tv_b10_3_4
  · exact tv_b10_3_5
  · exact tv_b10_3_6
  · exact tv_b10_3_7
  · exact tv_b10_3_8
  · exact tv_b10_3_9
  · exact tv_b10_3_10
  · exact tv_b10_3_11
  · exact tv_b10_3_12
  · exact tv_b10_3_13
  · exact tv_b10_3_14
  · exact tv_b10_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161221994844608, 1161221994844608, 1135246033031616, 1135246033031616, 1135246033031616, 106107236389057, 
    1135246033031616, 1135246033031616, 1130439757021889, 1139240486834624, 1134971155124672, 1134971155124672, 
    1161359433929152, 1161359433929152, 2928713681017909931566786873899211646775546893122, 317209381966272, 317209381966272, 246844728940737, 
    317209381966272, 317209381966272, 3957286453284098376038451321148240931959496092091848580117833555939956294793094855578250662849319524187174116480719513788198836047545677422041720846681272661864763929426284103, 1161166361858496, 1161157368943040, 1130439826215105, 
    1161359433798080, 1134971155124672, 1134971155124672, 1134971155124672, 1161157368943040, 1161166093160896, 
    1161157637575104, 176063733305537, 317076107964865, 176063733305537, 176063733305537, 1161157368943040, 
    2928713681012592999301237606755925994587174228802, 316934504059328, 1161359434715584, 1161359434715584, 72709640818881, 72709640818881, 
    74908664074433, 74908664074433, 583925464646046210032528848549142634165963574687313643932211154248300066469092686748599198157409796, 143078384996545, 143078384996545, 563500255547840, 
    581109621461952, 282025547272640, 282025547272640, 563500255547840, 427174101258688, 565701426287040, 
    563500255547840, 567902597026240, 176476050690241, 143490701856961, 572021202227648, 583925464646046210033188320692203937169199032612393893443549540359684594159696503221438210193788420, 
    90575098211533486264477223487511349508520508283931030681254463423603578956287863878594014764253704796557724531153587550556146974223892500802999431653036526405073985777222, 513258889781001788508752372384011230216198211446080363634990166979188729044093013380941140376675049326145827188858423582703147710042805591794375891410248417132548909382214, 583925464646046210033188320692203937169199032612393893443549540359684594159696503225715198756687364, 583925464646046267658742618891931016445229715976052867333303189001030256292315590935517959322897924, 143497685373376, 150092607656384, 
    145698856112576, 163308222026688, 150092607656384, 150092607656384, 284226718011840, 284226718011840, 
    282025547272640, 308439596143552, 290830230229440, 290830230229440, 308439596143552, 282025547272640, 
    290830230229440, 290830230229440, 284226718011840, 284226718011840, 282025547272640, 286427888751040, 
    308439596143552, 290830230229440, 290830230229440, 308439596143552, 282025547272640, 563500255547840, 
    565701426287040, 563500255547840, 567902597026240, 581109621461952, 572304938504640, 572304938504640, 
    176476049707201, 176476049772737, 176476049772737, 176476049772737, 299342318539200, 1461551814199009254797950837232658299739999065922, 
    563500255547840, 567902597026240, 581109621461952, 572304938504640, 572304938504640, 1130719271719360, 
    1130719271719360, 581659376751552, 581659376751552, 290555083887040, 290555083887040, 145273251697088, 
    145273251697088, 4535763341760, 145273251697088, 145273251697088, 145273251697088, 145273251697088, 
    158485107971008, 286010740052416, 286010740052416, 286010740052416, 33284385084494712632638531821882354590088529999742802665149313087092048640171546857277812645524290949, 424557929304512, 
    33219377757385355898275814330050409486995068037841236248948427487257491011279415213503482774457026949, 286010740052416, 18159668040640, 576290533937600, 286010740052416, 576290533937600, 
    73676011672000, 565703582171713, 73676011672000, 426748228407744, 290545957081536, 150642228859328, 
    150642228859328, 572854693794240, 91279338312640, 163849253295040, 581659376751552, 163849253295040, 
    290555083887040, 583925458845267951737113164577006047042602439525695413977381248462280187782765464490526278252263301, 74909079308353, 17127037646853419605659315719223550270863835971, 105626693011521, 105626684885057, 
    105626693011521, 105626684885057, 149808737161664, 149808737161664, 73669972332992, 143078800233153, 
    143628560257729, 73669972332992, 9071248806336, 290417242280384, 290829961793984, 290417242280384, 
    290829961793984, 286148179005888, 290546225516992, 290546225516992, 299342318539200, 299342318539200, 
    290546225516992, 143628560257729, 143628560257729, 286148179005888, 290546225516992, 290546225516992, 
    299342318539200, 143628560257729, 143628560257729, 290546225516992, 290546225516992, 33218933866359174949876067095137005966473614880526735990574261584280175203012984685081586211003600261, 
    9071248806336, 431081649082816, 431081649082816, 290546225516992, 290829961793984, 132875485490565941905506620202759736912914288813742658394879708828169078294623432373004100487553802692, 
    581659376751552, 581659376358336, 73671649595840, 565703582171713, 73671649595840, 290546225516992, 
    290546225516992, 290546225516992, 290546225516992]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [106107236389057, 1161367822537152, 176476049903809, 28545062765744990579237307101155715941027305282, 960962612318422722514276120579029485995887052264404733803492738587652128064625435033862841978854379236664378699397460550450053680800963383633787881044931947600576279073921730403133446905479277806618024208296383887324145763555203294709579708451470394177618952249877512, 1134838011138497, 
    1128240733766209, 1130439826215105, 1134838011138497, 1134838011138497]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1128670505341888, 106107236389057, 1128670505341888, 1161226289811904, 1135263212901312, 106107236389057, 
    1135263212901312, 1161155422851520, 1130865165996992, 1161164080026048, 1161235014095296, 1161368023863744, 
    123695392520532176087520368668498964167765860521866567404282814782946282688101452997004289403734589490615705948029570896972914070892963701148080145374448823734767573880057414, 106107236321345, 15121341268955300454560687058317760675804896124643772855640321490097963233144917338838306941178170005223793357217524085409586083207107847802964867881091127199157114436564199219266113689471987383838337811969881927592931049267197245621000337872564223215128496956552, 30946491887137527512635394397712577111473074314849674795086644395861206193840131426362096455553043426810858305986210358781743338894500053098941582553159740249957277906546246, 106107236321345, 106107236321345, 
    1139244781801920, 1134979745059264, 1134838011138496, 1134979745059264, 1130439757021889, 1139244781801920, 
    1134979745059264, 1134979745059264]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [22858351068388466800296415174393955260722860866, 22880651898657589153672566758510255480170894146, 22880651898657589153672566758510255480170894146, 23549676806731259754957114281999262063611892546, 24263303375343175062993964973720869093465150274, 25690556512567005679067666357164083146729214786, 
    2076195246641484044976885370241558467496539062731451265407867139338675772718944592366580374412779972, 259649206675262503700158378804345852033651807665281829674453551065767536865166065331778536107071940, 3957286438548131188546637175438305938039366142412183245213188893831077710837500379500010852624858682321754102322109989925265940342048335877163803107797415324067170422921408070, 176063733305537, 316801360073153]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 246844728940737, 316801360073152, 316801360073152, 316943093993920]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155221459392, 17127081203036625782721933749296776542920127042, 1161368023732672, 1134979745059264, 1134979745059264, 1161155221459392, 
    1161159650709952, 1161164080026048, 266594411932911499093404785498504934513857636213620729964618737285307635395699175925094352864345813124, 176063733305537, 176063733305537, 317076107964865, 
    583925458845267980548559480583713391177709692934585104808384948649770533268701457091893565351751812, 176063733305537, 176063733305537, 1161155221459392, 2928713681012603383934568757668315224376604644162, 583925458845267980550099590646493615935118350449752165953708187346557897945778862245358505645273220, 
    316943093993920, 1161368024650176, 17127037657320805558879493943852041607915263810, 72709640818881, 2923049270129584007669778485813772244746191820610, 72709640818881, 
    74908664074433, 74908664074433, 79306710585537, 74908664074433, 79306710585537, 28545062755111125968913028733031741550938314562, 
    143078384996545, 143078384996545, 581109621461952, 563517435417536, 581109621461952, 581109621461952, 
    563517435417536, 565716458673088, 581109621461952, 567915481928640, 563517435417536, 572313528439744, 
    176476050690241, 143490701856961, 572029792162240, 17127037667954670169206191334983493936910194498, 28545062765744990579239726124163193879933245250, 90575098211533486264477223487511349508520508199315852281441596616471538763068820963668238353141956975964110557804250150811533906023262970393798465539161018994663621701190, 
    90575098211533486264477223487511349508520510822385939970090217222108681814802512305488324595156352461303402684780188257797579364676242699224771599909390430752233141481030, 28545062765744990579239726124163193879933245250, 28545062765744990579239726124163193879933245250, 145707446047680, 163299632092096, 308439596143552, 
    853797363520448, 284250340332480, 286449363588032, 308439596143552, 286449363588032, 308439596143552, 
    290847410099136, 308439596143552, 308439596143552, 565716458673088, 581109621461952, 567915481928640, 
    581109621461952, 572313528439744, 176476049707201, 176476049772737, 176476049772737, 176476049772737, 
    1461551814199050144291692243950190892035881391938, 581109621461952, 567915481928640, 581109621461952, 572313528439744]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 1161368023863744, 316943093993920, 79306848997824, 286156768940480, 286156768940480, 
    581109353026496]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226290729408, 1128670504817600, 1135263213425600, 143362125468096, 143362125468096, 75192404545984, 
    567773613789632, 79306848997824, 1135263212508096, 172104583484352, 568341086344128]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1135112893247937, 282042190271424, 283816011764161, 282042190271424, 290838283293632, 290838283293632, 
    299634376315840, 308430469338048, 563517435417536, 581109621461952, 563517435417536, 286440236782528, 
    299634376315840]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [732180859438381333674704630431738142616482534210, 105624528556480, 316943362036160, 105624528556480, 387108095398336, 28545062744809608924977555083965873807683508034, 
    283815873351873, 316943362953664, 732180859438381333674704630431738142616482534210, 290555083887040, 712642994901952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [145277546664384, 145702748427200, 145277546664384, 145277546664384, 581109621461952, 145277546664384, 
    145277546664384, 145277546664384, 158472223068608, 145277546664384, 145277546664384, 145277546664384, 
    158472223068608, 158472223068608, 143628560257729, 294819852194240, 290847410099136, 145206679704000, 
    145206679704000, 145206679704000, 435557340549568, 145702748427200, 286156768940480, 286023759172032, 
    286156768940480, 286449363588032, 294819852194240, 290554815451584, 299351445344704, 424562224271808, 
    435557340549568, 576294828904896, 572313796875200, 572029792162240, 129777547423926009027780781102565142315753786178973515911885283130728663145684658919350936839179652, 424562224271808, 
    424699663225280, 426761247527360, 286156768940480, 435557340549568, 581109621461952, 576294828904896, 
    22858351068388466800310922339569351924910150466, 565703582171713, 22880651898657589153687073923685652144358183746, 426761247527360, 286156768940480, 435557340549568, 
    290554815451584, 431159294038464, 290554815451584, 290554815451584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [123695392671695679596741587065254242806862682383296486115391462691264081170442092437765086705249606004201385905646747166704124603554418992362868810780472616589563364581355078, 371089997073248001570191453004804659981905318722, 51386513902451585926615030049402227701592382274, 1978643226843600527308614323863389164844584279914989389625026667235688865996128023422812997675478192583287505487787326630681670117618239710428701054855516923521694010931719750, 33283751484824631724446425728741345977411954196981884002069236177180055163219620215710468591796318340, 290555083887040, 
    572313528439744, 581109621461952, 1461507215282038483043462627483940235585897190210, 1464361718834227208908102322543829804221099758402, 1464361718834227208908102322543829804221099758402, 581109621461952, 
    22858351068386519689279115082720808413289273154, 1461529513368741998433686316367436668615880934211, 22880651898655642042655266666837108632737306434, 22880651898655642042655266666837108632737306434, 290555083887040, 290555083887040, 
    712642994901952, 290555083887040, 290555083887040, 290555083887040]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [583925464646046181219642020544493836866945337416872723235679389603658296578379015221037712270389380, 582173687498006831640714275609924194970788483707286492939578585283517330495694694397486063496778182788, 74909079308353, 105626693011521, 105626684885057, 581395120223413659886868621243258330693075244360103100979669289345665139133758812578188305421139406980, 
    17127037652171710163778038942639645362680517443, 583925464646046181221292185132233903301347068088414544210366560472453921190308570360451239419344005, 583925464646046181221292185132233903301347068088458937315323888519253147049200311216636146658866309, 149817327096256, 11440325970595550242135845588452746147670283074, 143628560257729, 
    290554815451584, 431150435668416, 431150435668416, 2928712330767093355636065619780760113681614778946, 123695392678893941668010701277751104419160586077851355394805759816521724352149048184693294972524940961851639783600752724593041214953110249388869493712114461495318207750516294, 532345381924043839394585471685884124357262325992706243530575145932913892559999819714316286474834899076, 
    532345381924043839394585471685884124357262325993153726104560325759068133198383730055504959236805456004, 532345381924043839394585471685884124357262325995608487646776129219794154060405258043278604239520362628, 532475143136476034682092729134973136747705552886761781512049685724019501218805782687531698895780540548, 581395120223413659886868621243258330693075244360103100979669289345665157182924867760241879180442300548, 143628560257729, 143628560257729, 
    581109621461952, 581109621461952, 581109621461952, 439955387060672, 132875485490565941905506620256427718104988142541047592954575904192173592505439619621787516026681024964, 1464361718834227208908102322543829804221099758402, 
    1464361718834227208908102322543825441342317744962, 22858351068386519688974464614033045217561564994, 565703582171713, 22880651898655642042350616198149345437009598274, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_7_0
  · exact tv_b10_7_1
  · exact tv_b10_7_2
  · exact tv_b10_7_3
  · exact tv_b10_7_4
  · exact tv_b10_7_5
  · exact tv_b10_7_6
  · exact tv_b10_7_7
  · exact tv_b10_7_8
  · exact tv_b10_7_9
  · exact tv_b10_7_10
  · exact tv_b10_7_11
  · exact tv_b10_7_12
  · exact tv_b10_7_13
  · exact tv_b10_7_14
  · exact tv_b10_7_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161359299580352, 1161359299580352, 105630964713537, 3957286427485527111805477507569384677388243018328455666079766738251596518336578620495032736071012614513715620139643542658555203000134667771807297350003511796663589802405231175, 3957286424721394476491768881696603703764903845916415270785722545237327847286408454184998575484682840409691404443257343987046119318483121873060261906697835663519351648858582599, 1161230450561472, 
    105630964713537, 4217239420481885636211459244034785128008435974957801383675895482957318402716536464819957321136566404, 1161165959205312, 1130861139726784, 3957286427485527111805477507569384677388243018328455665837680812180948838056472901290049311097875977803968598157271522375025248909109301658137492610278919365824122660530911815, 3957301523335226397970886499367316251753047029954145032524126202245200438130444064716486586767383210819819193297390412072331197269727497266838601003162222900714226198920519239, 
    176068032467392, 176068032467392, 532345381924043839394587252627284302906700368276091089244433314792401844646009287474446127971943280772, 72713935786177, 143082679963841, 143632855225025, 
    871389817213888, 871389817738176, 871389817476032, 871389817476032, 551485156945714612346253472188418277530366474055436674970173038161088733259501335865536846861758533, 145698319241664, 
    726257638577088, 581109621461952, 581109621461952, 532345381924043839394587245754428666273818154591183782513016689868243853581338255640839237463870500996, 551485156945714612344052655694372894586506322881252114208931317795003209432943126521811583137542213, 106111548065857, 
    72714878521792, 72714878521792, 565707877139009, 145410556432832, 145410556432832, 1135254488355264, 
    1130860736811456, 150092607656384, 282025547272640, 563500255547840, 563500255547840, 163308222026688, 
    308439596143552, 308439596143552, 581109621461952, 308439596143552, 581110158332864, 16674316046003773019189936114363085810836845717216220097143622214992470538512594340472631036924191172, 
    106111548065857, 106111548065857, 106112017827905, 551485156945714612344052655687821627595199460505514859162362310038991476018799406993431726509846597, 106111548065857, 28545062765749533700341516866965586403964487491, 
    537795352846196041671507583681419323271693062571789364692860480157454761173268711321004055397020168324, 4152989022987072960328209257074960466135974817092101661374951751740783349279601498084908630481833177109231262750953888317699477692061222081005651580576256358152041889192212550, 7729078731994588773169520666294999833543339133274738177802784375286565296603294473452008666805128475254611150799584987649230448709988073188065654462883966493956449201258055, 426692192506304, 426692192506304, 427173698605504, 
    440298648900032, 145281707413952, 2076195733906855321610243882291887809736542929444660162770419005231977055492943987128757070204035524, 563500255547840, 581109621461952, 581109353026496, 
    72650454012352, 72650454012352, 565707877139009, 145281707413952, 145281707413952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [960962612318422722514276120579029485995887052264404733803492738003668640030994337853923382876166591537305823477303555362496530297635651331192021766394825960003871678146298500452889648243859361371490740263206911619649492606725924266905990936395527218331124744249877512, 960962154094212046835217857624440951243359382280315518482490122125738730098024829755723285347109844888239342624799798493857152853764856633074727943498121867480440437896548269718918257985225241981825943133679129672249578827891566097450518098999190748210937857249559113, 571833028449216, 1161367889514944, 105630964713537, 531501949882259879639372883726243813390957502081530724936505807947513964104867485007629413295107536388, 
    1161157436117440, 1161168509407680, 105630964713537, 188397414113883790944883821505896061168034805570, 3957316615513757548701185265680621633635424460897731885283746459919765842102682894529163030276046821639093329151096260576151631833200870176155303980583957351363247147842711110, 79253966689216, 
    571833028449216, 580629121471424, 3958161983082584315783377305838629048360584189274436247038706637810177186608226863742141379476662837971091404282253546278056331005845287904011349152736968893262809665929951558, 571833028449216, 129777547423926009027780781102568141247809428432542757610719523840796178873988920637810912876612996, 1161226155594176, 
    1161368023863744, 105630964713537, 818982257500273022899745771748955030458532749643196524251233070500069225194824008802867860959531771060224764443196674639840229700913364043611015409768051297572242879335131863069227453070805641324212964634067829903868346410713331335859314207294058779264821113294186720964815510178839488443151227451713456250493480132528090235068950264051218236025531672110948624286999646700618, 457822182052288, 316943093993920, 960962612318422722514276120579029485995887052264404733803492738587663266840975931649575993447377030997014020390733898953638218975834180433436056703771840495911819196463544281146868827009493327424989055924281276205687744061256326996471017988626344748133647368249877512, 
    176063737500096, 176063737500096, 316943093993920, 571901211579328, 143082679963841, 568052920882112, 
    1161234879746496, 123695392671695679596741587065254242806862682383296486116061296796602787317119087531335825061361901607239307733988121721289573348011519037652135530234479852108656756839984710, 149693041480640, 571901211579328, 580697304601536, 424562224271808, 
    143632855225025, 145286136598976, 435557340549568, 145286136598976, 145286136598976, 431159294038464, 
    158497992872896, 158497992872896, 571901211579328, 143632855225025, 431150435668416, 456741910946651840557753849108081470352966832962, 
    513259120142961964537331115444631005067305970827513490513621155315030549041252634073283826062781304656581872513783638941639635985512339478380175799997029571499942403681862, 572313528439744, 563517435417536, 581109621461952, 143082679963841, 143632855225025, 
    581109621461952, 581109621461952, 581109621461952, 581109621461952, 581109621461952, 79306714780096, 
    17127386106468751301444613831724721838108185155, 79306714780096, 79306714780096, 79306714780096, 513259120142961964537331115444631005067305970827513490513621155314896159982220516254626530780942743764651843077610698183120763787913299146203367744522330474877291930627654, 106111548065857, 
    4080951628229277640960629114006027705366148792960945003932273890867412815902625971441557810675078365827140133699429445535750807145462268577304649103726353954675925281572644934, 4152989022756841046879059921035904353189284551263581981754876995186233102643058495689535166197420415569111350428330168536705140023605627727226880313529133821519200980274509894, 424836967961024, 6774210443576695379785539423776976701868206374763172037442616979180009647428171487959687158598653222098005567180360708501111682499087875318537647120550390036560018106644430046213550185864627496320173617932539497814683104991072136080123011399096044067073754429142966872547909226102855607348176310943348015206704745237463634975963067858127225419839587088217804056877825617022551114, 283815877546432, 283815877546432, 
    284099479605696, 565707877139009, 145419146367424, 145419146367424, 371085815699474074033166398212501170313674904386, 290847678010304, 
    176476053967296, 513259120142961964537331115444631005027556978090606574030776884938378043426091999909010165881973597957515830645063562538516634573737676137676278163244858240582132885139014, 853797363520448, 308439596143552, 308439596143552, 572314065310656, 
    581110158332864, 581109621461952, 581109621461952, 73120752931264, 73120752931264, 22880651877387912666330914305620875841810487106, 
    537796105276741744684019622315804649667832666493252434622938069758506340246732130329869075856287244996, 145689729307072, 145689729307072, 990141234549696, 16674316046003773019189936114363085810836845717216220097143622214992470538512594340472631036924191172, 106111548065857, 
    106111548065857, 106112017827905, 3965046722488752238797939231919101635782396474621457287225603822571031448500248693989937298319145301927894814804643056529966887080031576335624009872319801241938852792533772614, 551485156945714612344052655687821527630798349489931733200198276311002458254013917290993955038621765, 106111548065857, 28545062765754726017007092323160201298679695171, 
    3957316615500260807304147868602224556643527479921026238584239199174047645516279437510131512872289889195319835102852105636857237121806723995932782093364585758686739829129129542, 154073505468864, 154073505468864, 145277412446656, 736462597050703228649651517015231651152859792195, 581109621461952, 
    581109621461952, 581109353026496, 72639716594112, 72639716594112, 283958550204864, 565707877139009, 
    145277412446656, 145277412446656, 286156768940480]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1134850895647680, 291388038583232, 291388038583232, 1134988334732224, 2929459343204296902304627236097969932546139542338, 1128184905012160, 
    1134988334601152, 1128184905012160, 1132583085806528, 1136981266666432, 1128184905012160, 2928723418532825578142970376508477477070384976706, 
    143224422281665, 72709640818881, 143078384996545, 143078384996545, 143490701856961, 143490701856961, 
    143220257333569, 72709779231169, 143087117545921, 143220257333569, 143645740126913, 143645740126913, 
    91277190828992, 163844958327744, 581659376751552, 581659376751552, 581659376751552, 143645740126913, 
    143645740126913, 581659376751552, 581659376358336, 1139386246894528, 736461208688022691041007677589137812219733529410, 1130452714918848, 
    1441443975742222822104577926557302146391725766925392137959329916202759396408613549405730227037681374816850385688954185106820596313071883313280633952185926760890864684074847660732035341792338280990805057635381558395918555106183617462946280927627492555082437640246197512, 74917396623809, 581109621461952, 581109621461952, 17127016039108744813344941081280023783083661122, 583925464646046197433974099083655411740788828240384486640134483128563477512639056729737844943390596, 
    28545041136899390375759852262940436888828303170, 75050536411457, 75050536411457, 145290297349056, 2928715058480951996792890876297630435703076737858, 145290297349056, 
    163432641860544, 585507265319872, 581109621461952, 581109621461952, 581109353026496, 581109621461952, 
    163295337124800, 308431006208960, 581109621461952, 163295337124800, 308431006208960, 581109621461952, 
    581109621461952, 581109621461952, 581109621461952, 581109353026496, 79306710585537, 580629121471424, 
    580697304601536, 581109621461952, 581109621461952, 581110158332864, 581110158332864, 300183996994496, 
    300183996994496, 168242601661376, 299359498408896, 12488464953387753290700870440817778883981013570, 11774838384775837982664095306966653445991363394, 79457977373632, 
    871106349896640, 290564209775552, 4142815831847351501733523158230794308145579523367216052598048673735435713320944213988031756274861962417543726292135420377327855306347972914986781946855917449841246404983384646, 290564209775552, 297194374456906221681086841812971744999716844703441252118404902340226846343059893728836748192300206126620157205127272059416271378745852849188716378049240607027465804295382252668949800219892400387952388480027111228411076919544650520449260660108438284939957784118727426226771332991491080650679271296210710017959982069217196772054868733159416410621040035147612291030018381661508902925613667634154405365804528435620802610662598844495035042376566217085505127446241740771440548803341730365061677385547952231885, 871106349372352, 
    871106349372352, 871106349896640, 290564210168768, 290564210168768, 871381227541440, 75883624928192, 
    23014456880290496075264368003651437409119294274, 261581628146507880495587293551552130535249084435028831685913737242258382016202976398302604998277764, 411779005811161373478442628608637397377149620071630037209638555437811661680600384505564763160749284672132337141803417924496381329352436804047656384633897623981700912216437799804022198194624000543548127555165763755819427296218980277648574998232314671282847533542577291403042233427058515103965997869502098327835750181400199579596234563911974093633115887077351044806957403382752395862195003435022304892870949301218081562190221372332798494810519643774140002303841693835906126907522770716115353953168990542104549804453070135922797812250993551394691839806280158253336163593884747353987381696797343106140169243822762727421179335219587769459865332791730529063200120305429496552351305486026267694006398651212317130689122144274861096928383790419965460878924603402122462737278671872807311695708798515775466259247365803416649270996798021482819751277141187164062654290731499255178029759448497174979776099246296610982606362065380841413053649482084770935348389792267205611949478585002396975111057243790360440434370747601663060567006897936203749100686890864715436364762594977863229475709316755657158371536107827593448121000619435029995727758252841503063934869768765441113531410485153516592904894528835765755074332188791147156319800465360951612422526266549458441377643803816445955244854079789687821727269565095532257217680494237028048312367091141826805131924338202693588956567611850488462048389009212217376420547087468261702214294039761325435828967249314109165484759888461028110824218513333112269510172436137955763344327244592228033839241538415314478455168186263965846091332207174702497055437785954287764955578526182380881247522737039428634992333660046912225845304642789015274519220873348168255896722915551985993055172546313510554358355300600067107659565280590182709951346947679378533443801185413073513389550017388994340474119370574378221622034087855874427583376789345894052290654744377698572089496835365965827360834059716699373156637328002616777419935760504794377086310237891456085184773428643170796078648793816534482498288642748854449374373429243673371657612974406345542743495821281495033993983694266928883591397965637094338778336720890073116303172964847497373997178614152053458766394952630369842136817009430379085929328862938612103731413102940206733422957884400407522778020455648959854250847641045913267151621250675178679061655353196527819190986042161178741234528358714269275495883856384438493277018181150010982018651329334711554768177086223144257528062443236801019551043002051500868535854670720016062614538548560115583604382896396235797105648943069421940239775364141884172284095381499388975061380659385973544754514480371803815223097251335719450662011214490602922127165681052716515245766209983995491494122413656668405071975221303643084423534538356760152533503737406082099813142316151496959933705084298043045786139273400532365923019469390717412420723103611011802917702606453214253014704304034688557817722007449341298471272676185432505201358794798669058976582135112753667190300307524538426217612227215147332254599895578453847049794358200969206908908373290673535937024325572860512059840680285886627805363069701769252570973537367797141723538616986063016244545363925301498729473091232661506907974030953417093106114220065140942512832270189119997767866700410621019068232056169845550705582902925375713362899906178368250971760878491515761054866137429653357918638917350755049747708446106469492238391407868880939079977572674698145618076640743597636191970255319707993912065443425947243528570106293254866203087978673345512596464179920433843550843226471519845628446705001610738295528000344480177189993606579624965670737262767735983947837889139043354160209344293440162613622531991142779777514418353999344303035922484972234912971474413686911414568574380756787946648565191141456641086979593623685457314746260684833407750877716200702737861338333909415403836292074353506668688369893851956037783719955947624615714411959587385984901871003247455587900424299803207756905602696187588116423730767462, 79457977373632, 79457977373632, 564789732273735344921673781874312416709392249345721235815221750316531469627369535442905926897635225732, 
    146252369105856, 581659376751552, 46385725601324262738697497935930828079008641858, 149825917031360, 149825917031360, 581659644924864, 
    581659645187008, 581659376751552, 871655166448576, 871105410634688, 871655166448576, 580834475119552, 
    581109621461952, 581109621461952, 580697304601536, 581109621461952, 581109621461952, 581659377275840, 
    149825917031360, 149825917031360, 172504015442880, 149825917031360, 149825917031360, 171816820675520, 
    4080982759733772265525728496982386161057153974320744732555339347434241250296684963795262071506863186425435413197050809256956814961211591830329578594213179218902620454007073094, 435698806035392, 290563942257600, 581109621461952, 290563405386688, 290563405386688, 
    581109621461952, 290563405386688, 290563405386688, 290563673822144, 290563942257600, 145221577872320, 
    426765274059712, 292557074731968, 294824012944320, 290564210693056]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [371085815720731418620478969458332678545981068098, 371085815720731418620488640901783224464823046978, 105776595146945, 105639151999169, 105639286212673, 105639554648129, 
    3957316615506559286616511616928790261601833419865142522449334657741801648710266275264481018757332605902909644794273396145976782706665173148992891744518446892001845705301995078, 105707804430529, 105776595210433, 105707804430529, 3957286424264322408834782460213906390211914191063211702606165099325140497412023484244963083155339114362023616398190802297774998967526075248244121878842886715866937104394661446, 426688903188928, 
    427169940378048, 426688903188928, 427169940378048, 862585134781376, 284777882194368, 290547030299072, 
    290547030299072, 871389817476032, 290409590952384, 290409590952384, 290821908206016, 283816816153024, 
    283816816153024, 241534516580182981861307981157575458020754603741198741551111290745269406792766261111221977998009069184093290767328163384317212775339059897479465578002822778921439515291207, 586521187104198254813645053532168626105420952735416532703152134040220108188719579141898222304090091652, 586521187104198254813645053532168626105420952738320197398965771572589825121850245060686639044578472068, 290409590952384, 290409590952384, 
    290821908206016, 290821908206016]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776595146945, 28545062755131246119312244772586320414485250883, 25690556491317449418804977125493900021760000835, 97053213373766324928055044935943188880048542530, 105776595146945, 105639151999169, 
    105639286212673, 105639286212673, 105639084886081, 105639084886081, 105639084886081, 105639286212673, 
    572854693794240, 564050010837440, 581659376751552, 105776595278017, 17127037689224021982623040195642197567374119746, 105776662321345, 
    105776595210433, 284778083520960, 730932012943292308569336701024598321680483373890, 105639156256961, 105776595210433, 105776595210433, 
    105707804430529, 105776595210433, 105707804430529, 105776528103617, 105776595210433, 28545062745826610851591228548041215903119971139, 
    106120121290945, 51381112940732903622486450468935704762275353410, 371085815683512892761701799559486371707165365058, 3957286424260719763022745916236227742819265831699568903212611379691485104047015021762543682422066548031726556739534546138182488078177405818682655619893683505456358782280445510, 3957286424264304834952824695516593235453631610461841924321801404770619401215989568535185070058910495580890337200966606862856462468877355978110459201658787537714734596976324166, 23192863565144762642012027708528283121550140227, 
    23192863482566482911253630816099780726907511619, 105776595278017, 106120121223233, 324403039781655621515434535743637919327946121335631634779571525715231723501657636509257185728304581, 23549675405742972881518202308462717463112508227, 51381112940732903622486450468937393618578068290, 
    371085815683512892761701799559488060563468079938, 73671649661376, 73671649661376, 284778083520960, 73671649661376, 73671649661376, 
    536692881530235262567514504771521129154836536089997166122174610940496253593828592639934096096751743108, 28545046421577633914807599363830083633402643267, 80268719428032, 80268719428032, 89081992844224, 89081992844224, 
    89081992844224, 259538272591457719330497462963486464606774842232850722952677358820739852741728343776070699544106821, 259538272591457719330497892307323205754262264456749588698623496636368977441573387741742517000230725, 144049050882496, 146243779170752, 146243779170752, 
    146243779170752, 259775872474346333411709944770439476569845449095167679584999211472962820284787397427025287473406789, 159455098573760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176145272281281, 176076617814209, 176076617814209, 176076617814209, 176007898337473, 286156768940480, 
    9071248806336, 7775365053957718559579597671664242524272040866747054545432256283987388152685317427442288067311785072625779536033765002105718238879321659389824287753387541575968296401882695, 427169806291392, 581109621461952, 143641445159617, 143641445159617]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [3958161983082584315783377305838629048360584189253880050633205067377134473659346473624215732254781846597536157232473253931015881857356071556288973153546839065291769535929465158, 176145272281281, 4217239466888111472080273688103668648365242168503149450838301469891249895027436595424667388893230981, 176145272346817, 94198707078061318989726117345120799547086603075, 4217239466888111472080135868731690876749345125542705938117016979880939633238376449440493745994789125, 
    176076618207425, 176145272281281, 176145272281281, 176145272281281, 176007967480001, 435690216100288, 
    143086979125696, 176007898337473, 299359766844352, 290545957081536, 581109621461952, 581109621461952, 
    176076617748673, 176076617814209, 176007898337473, 176076617814209, 176076617814209, 176076617814209, 
    176007898337473, 15488341795066791663667654694697035730377966841928738439672026527444889011267689674650926020812337535023857811629342690570216344125900623562219849869535435979412304021048902, 15488341795066743610084033780429030694260499029960274070576392557394007554807810581889303486059341225647768509874795495521722408281678939804887055629130268625828566879587910, 290546225516992, 290546225516992, 290546225516992, 
    176076618731713, 143091269898433, 143091269898433, 563500255547840, 581109621461952, 283953450717632, 
    494862248972736, 424699663225280, 505857365250496, 508056388506048, 501459318739392, 1073223081923520, 
    581109621461952, 581109621461952, 290546225516992, 286156768940480, 567911186960832, 581109621461952, 
    290546493952448, 424562224271808, 143641445159617, 145281841631680, 149679888142784, 145281841631680, 
    286156768940480, 145281841631680, 149679888142784, 572304670069184, 158493697905600, 158493697905600, 
    11451432787134601598066467498002989476011323970, 2076195300782788956301356523062313155264093754374837000783108643835218619438308456406188233358464837, 143641445159617, 143641445159617, 143641445159617, 143641445159617, 
    286156768940480, 567911186960832, 290546225516992, 290546225516992, 290546225516992, 290546225516992, 
    299359498408896]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [291370724102592, 291370724102592, 290409590952384, 290409590952384, 290821908206016, 286981267526080, 
    284777882194368, 284777882194368, 284777882194368, 290546225516992, 290546225516992, 308439596143552, 
    296950155973056, 286019329987008, 290546225516992, 290546225516992, 308439596143552, 182777604928272491304697865278729782853028041538]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [33283751113574825037484909273484443740322546308347282019519150310084983555868044609290426616181223685, 316745325807681, 581109621461952, 15458153778478996681317252369848986837080623924931352753084020394936162316352938373715351863326583065108456100509600422938332275831810024648747983614164420851409676727504455, 9071248806336, 9071248806336, 
    283815877546432, 11441327723343495532322295548235886148381061698, 283815877546432, 479601568672752410562509191191805158226359505730, 426687897539008, 427169403638208]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [6767303366728955361338858020691928854773103564592880878259777991636075645430706129701694566574902696197642661141673206817781344364097141430300136547850345567800644691506945174542195798398802503525340976907440830987291278310519768928220959101747243124199568719423448070685985186725330557687011216270682304101949857510275816936795855709478049572897684910491689712418598460882526154, 316745325807681, 316745325807681, 4022983576437287596354050139202407331305053726698939149830103631049781931035138523654115057499409584466940890067772215287835186860834729514735493773134094292880398407020686918, 316745325807681, 316745527134273, 
    316745325807681, 33283751113574826881502646815875692283563193868687215315925540561504768976735681974796320910716990597, 371085815678549037712426335883504164078453524291, 188398111012020059368484253040821676696922227267, 143086979125696, 33218934237608983480854871581501395354763428388165425197269363946286348694137729932849382596133025669, 
    143086979125696, 33218934237609691583669880253857686451264504278404938041854845635967592845401787608313680884063064325, 145281707413952, 145281707413952, 145281707413952, 426756818342336, 
    426756818342336, 143086979125696, 182711399298544637389823700524105491278458835523, 143086979125696, 182711399383615229120058316389949143136400891459, 145281707413952, 
    145281707413952, 145281707413952, 158493026816960, 426756818342336, 426756818342336, 426756818342336, 
    426756818342336, 426756818342336, 426756818342336, 426756818342336, 145281707413952, 145281707413952, 
    145281707413952, 708236358455744, 725845724369856, 426756818342336, 426756818342336, 708236358455744, 
    33218934237608983480854761240135352879883661575463385052542844635568790730319321835532044185722451845, 72709577904576, 424836833743296, 283816011764160, 72709577904576, 33218934237609691583666868836186822429738658957193458736589849108640038984581644225169727102125782789, 
    497404534067648, 989986213073344, 497404534067648, 989986213073344, 33219377757385355898274052408577105148337795543999216834438886053858158330988990186921724178560059781, 88669676377024, 
    18159668040640, 188398111013183097736753796800123847388218528323, 708236358455744, 15488342021811998855061131474848414288938310930184573776262402886227407488615882391889037808171798131634044405807290971501956749768989207832458421058336084006257676640472646, 286157574246848, 290546225516992, 
    290546225516992, 33218934237609691583666909999527528259666470571293718827130634773504509283553579459001884543828884037, 283966872494913, 18160204911552, 143086979125696, 283953450717632, 
    143086979125696, 73121894764992, 73121894764992, 284228328624576, 354597139911104, 3957920452942559774011439111213755252686269257527929192149412905855699754193710145100738828088512626327075720573395912619288765306768877954759135737094220938373264177549538886, 
    284516645102401, 72709577904576, 72709577904576, 283816011764160, 532345469047865660768624110573826104194972757739581446356114688253984789910377120189248069560762016452, 11451432787134440606440240855605496755817296450, 
    145281707413952, 286156768940480]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [66438758485720862846686996639947889544926626111574447646095897731827321357794333821710645464585580804, 143091269898433, 572029792162240, 589639694947264]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [425523960418752, 4152475765709822164888452251670546109520883132917440949116256156783113074226005508672188972864161945240762699556765256665017374924627125441304349738952109028174418335756155462, 286981267526080, 989321606871381778045224032412724137007070548622224358849833134954427299928946852602131015203537417574576323671855996080369264362905900682262642733519662641795331800343948871, 3957316615499415510444267685974968730066344978484337343277860458963730595778168086284812339712773245571135552151237037243609488222614309482549609600888316375732336577285637702, 286019195769280, 
    286019329987008, 9071248806336, 9071248806336]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [572854290747840, 572854693794240, 572854693794240, 1461507215281996944351681699986446261958498865986, 568460539204032, 581659376751552, 
    581659376751552, 581659376358336, 480481546266110744842554101926582037516884295026952688057685822915922451476555041798932418578729116029575589708958890381834645230825118526766109072244413132375528125058464018747520347301127424805483633409535543143128487309878521189887521794987059008973571080249877512, 563225109205440, 563500255547840, 563500255547840, 
    563500255547840, 572029792162240, 572029792162240, 581109621461952, 581109621461952, 581109353026496, 
    576294828904896]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [548087505526881151358608753891152238884681691714, 73672656228800, 144049050882496, 214417727951296, 144049050882496, 365399103964886692344315616700286641950121022274, 
    376817085501386189408960319324630167007583556418, 182711399295867957584509646452913977922829701954, 365399103964886692344315616700277634750866281282, 354116840985024, 11440325970597821564695256503220059156481332034, 535654348311007583219220530212096713780992547072089192797149631974549208673495929356241575420291621572, 
    730775907131406180436117470005856337186418348866, 11440630863601178873987711552033784868255052354, 91366501655140124510127261243513169170747380546, 596585030916676750471931164953278183974375516342068643160110204278569568129882867397011223021496791172, 132875501330558638018205846738710772492753777890805980163787670727077664389829832357685000678593156933, 4055037888506132447723663373383685709025918025685749825995495115526442388837726138856244613543428, 
    290547029905856, 290547030299072, 532287082837304853857219408792445780473986583543539829202877625096423859091255693128893579742220034756, 590616141864731671365364751947741311757561467420477516486560916410582775195958190813430584085132308612, 642197477659072, 532287082837304853857221167384801072214094874305664370917006641910651141086867548609393292986806346436, 
    132875501330558638018204967013189289881161945137395420845908507474747455524515515800690676264805488453, 132875501330558638018204967013189289881161945137395420932529131664708847339065870014431044052464326469, 565304150213185, 1461529513348157059012705351945112181989653414723, 565716467073601, 565716198638145, 
    565716467073601, 565304150213185, 132875501330558638018203208850177834882591055747171349036949194617876764720310011550878821871945930565, 1461529513368760171542325315473939157020015919939, 572305474458048, 572305474851264, 
    572305474851264, 73672656228800, 73671649595840, 144049050882496, 114224765568707201108850748587459204628623676226, 22880651898657588846968087484423499394683261762, 
    214417727951296, 144049050882496, 707001554440640, 91388802485409246863503412827628624998551278402, 283954255237568, 283954255237568, 
    22880651877389859785080505101693856430549914434, 354116840985024, 283954255237568, 847181234049472, 365421404795155814697691768284395060900285928258, 73671649595840, 
    73671649595840, 4153200366495387900827873951498842478103725840948588146232550577462324988684855241427073380665875257721256853016385386933219761850762939046962963934223583912007649326025112134, 114224853191416683290133679050089112650117043010, 73671649595840, 588402312849511981333498738016951603344631933739087692927281794919498521495358966676173838218931905220, 214417727951296, 
    73671649595840, 537796105276741744684020501629611755230409858128727161560998171806099131030440829664349861403330519748, 3957316615499415510444320060224698116918833857480650043455340645125437742430173515207591388748984104516102375650077650446552675350938436212173180325648221877934939138693187142, 565716064424641, 588409060682130665965264616729073877589442689540027440321440838286084172662753296070399929856005677764, 565716198638145, 
    565716467073601, 132875517170550389995170533287665928174499114469919095439169942954102849060583629412223266852994207941, 565716467073601, 565716198638145, 91283632755648, 75879262785984, 
    411137932617642844489381242256715292672719344450, 365466006455694059434154630329449332980639093570, 75879262785984, 45761216642489893605841749521599367719497529922, 216616751206848, 45761216642489893605841749521599367717886917186, 
    75879262785984, 146243780088256, 286156768940480, 145281707413952, 286156768940480, 286156768940480, 
    75879262785984, 519298297334960417723530276511126561540813643964450133159300026362247130092758793784864945129816324, 91522607467023981013470883496536270657009242946, 91522607467023981013470883496540703904803869506, 75879262785984, 114358309213464139978078279163307624944904459074, 
    216616751206848, 75879262785984, 146243780088256, 145281707413952, 286156768940480, 182866808249348988324135087314922608253489664834, 
    286156768940480, 286156768940480, 91522607424820831155673575546715343276403086146, 426756818342336, 990123517809088, 426756818342336, 
    426756818342336, 286156768940480, 286156768940480, 1461685619159542453087059722587838326416368276291, 532345469047865660768622333090341906276664111579798987567971631203042387187328535005061061350135079620, 582173774869328525925783379720064175142245382296998908570761952147014971445728160867009857703945347780, 
    532345469047865660768624091682697198016772402341923529282100648017269669182940390485560774594721391300, 145281707413952, 145281707413952, 426756818342336, 435690216100288, 145281707413952, 
    426756818342336, 426756818342336, 145281707413952, 290546225516992, 290546493952448, 290546493952448, 
    290546225516992, 1461685619180644028015958376562753258556152156995, 163307685155776, 79238933844416, 290547029905856, 290547029905856, 
    79238933844416, 91701014109176802612191586390536726004711314242, 149679753925056, 149679753925056, 548419972200835735836527665045506500948989588034, 79238933844416, 
    290547029905856, 290547030299072, 79238933844416, 360713910751680, 642197477659072, 23549676764528270582391042233629597599554097986, 
    290546091299264, 290546493952448, 149679753925056, 431154864853440, 431154864853440, 431154864853440, 
    712630109999552, 149679753925056, 290547030823360, 290547030823360]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_13_0
  · exact tv_b10_13_1
  · exact tv_b10_13_2
  · exact tv_b10_13_3
  · exact tv_b10_13_4
  · exact tv_b10_13_5
  · exact tv_b10_13_6
  · exact tv_b10_13_7
  · exact tv_b10_13_8
  · exact tv_b10_13_9
  · exact tv_b10_13_10
  · exact tv_b10_13_11
  · exact tv_b10_13_12
  · exact tv_b10_13_13
  · exact tv_b10_13_14
  · exact tv_b10_13_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1135812834104256, 1134850761429952, 1152580520776640, 2923728051603390863826918211054002176787356930882, 2926582546989799708388883300202201475666367566658, 1156772408923072, 
    1152443081954240, 1152580520776640, 2925868923147434427647516108460384401302537458498, 572863283729344, 572863283729344, 23549676806770201822954308732664817792791434050, 
    84680121062336, 150650818794432, 572863283729344, 1461507215282038482885006303636003181116220592962, 291388038583232, 291388038583232, 
    1134988334994368, 1134988334994368, 1134850895647680, 1135263212901312, 1152580520776640, 1152580520776640, 
    1134850895647680, 308706152289216, 572314064786368, 572314064786368, 1841870162698525361240322946250400638322956391234, 290564210168768, 
    290564210168768, 79320538289088, 79732855542720, 79870294627264, 290426770822080, 290839088075712, 
    308156395951040, 308156395951040, 290426770822080, 308156395951040, 308156395951040, 1131414787593152, 
    1130452714918848, 1134988334732224, 1134988334732224, 1130383995442112, 1139249076638656, 1139248942420928, 
    1134988334732224, 2923728051608375487825928679506210158597963338562, 581659376751552, 23014456880311265341926669828429896987980157762, 163844958327744, 581659376751552, 
    581659376751552, 581659376358336, 82480896545728, 291388038583232, 163844958327744, 581659376751552, 
    14294832160013833441906927664491996702805414722, 1134988334601152, 1134988334601152, 1134850895647680, 1134988334732224, 1134988334732224, 
    2923192831719134920015013452463234402766150521666, 183045235268598296434478370947402740692213134146, 1464357548312270496665950208013379424602852250434, 1464361729701995221157789245960555546170634621762, 265856395036478320592505678676601135255137476060406855316964702288657055168642074706786938574153871492, 1464361729701995221157789245960558923883240051522, 
    265872615188032345003444305520771183226437239218957206010836618020339484910256745132257209891563139204, 146252369499072, 82480829436864, 363955604820928, 1098268498820905904031186449895131554991099204418, 73684534563776, 
    73684534563776, 293586860643264, 293586860643264, 3957769494445566912370758382200966777530261105519384318125818322350747926034454643726555899235900020006541902626231575670028257963195630833577433867276713174224615415025196615, 291388038583232, 291388038583232, 
    620836637882915730956668679695678580603389867713789312306264045016094496812413746142302820555157548230659532237372587591140556622623982935661357907725526767863642316360391301416663089191130248042849522727042070843533539265346990783520677627873077558144411635460031216340811303971956659773513958338834060095865631168570665128854450991748409131082749978970082939154682170789079870905320671487428335242214287316249963559971628350557393383956011110170782278454788921861059991164837393232599977495450127916169464588, 6626524740013463535830307783162115251411677106937497665327590355809844238475512287881836578997425538256802217029819075324416692475796699694288438682089862302196130912661371462, 581659376751552, 480481889932903142167854800630407608450563993282697590645993910056489149020120820103452121515442875730895744488538833658824817574460527191250652239015072451630612068139926274656278423059989407662200805178446514995394564539087401581708150729455532099114140680748877512, 1464361710667450402646890759751500826331972719426, 6626524739984670267013396996019050100327454785942999750990006058620084120822665741142517774086522773981276332507326420216152609314070006214141663964933461761911788368100817478, 
    146252369499072, 75883624928192, 146252369105856, 146252369105856, 1143646988669888, 93475744388032, 
    300184131605440, 300184131605440, 581659376751552, 1147976114312128, 1143784427754432, 581659376751552, 
    1147976114312128, 1143784427623360, 1147976114312128, 1156772341617600, 1147976382944192, 1147976114312128, 
    1143784428540864, 299359498408896, 581109621461952, 2925859174743503808868118817581947470982846436162, 581109621461952, 581109621461952, 
    167968529978304, 299634913186752, 299634913186752, 299634913186752, 581109621461952, 581109621461952, 
    581109621461952, 299634376315840, 581109621461952, 167280529904576, 581109621461952, 581109621461952, 
    167280529904576, 581109621461952, 158485107971008, 93476281127872, 93475743798208, 171609924047808, 
    171609924047808, 299359498408896, 581109621461952, 299359498408896, 299359498408896, 299634913186752, 
    299359498408896, 870968776987584, 2923728051608375487825853723753442063490511622978, 1130452849136576, 1139249076769728, 1134988334994368, 
    2923192831166508376964468370453612523717212066626, 532539897021795096686880881803708965210400040735456108091229700414897272654978519405372388553351655556, 14272542303851044288489154435428510846096069442, 1128184905012160, 1134988334732224, 2924107165717779020513679290591386235336369762882, 
    1128184905012160, 1134988334601152, 1128184905012160, 1132583085806528, 1136981266666432, 1128184905012160, 
    1134988335518656, 290563405386688, 581109621461952, 172504015442880, 308705884115904, 163295337124800, 
    308431006208960, 581109621461952, 581109621461952, 581109353026496, 290563942257600, 290563942257600, 
    308431006208960, 581109353026496, 581109353026496, 299634376315840, 145290297349056, 581109621461952, 
    581109621461952, 581109621461952, 581109621461952, 290563673822144, 265783407325692137575226381985169414376715065732597837294304783194910693212968839626182634861624751620, 2206209924082192741132619679207427323615125289648971376694399426996601513437820164209808203927975428, 
    145290431566784, 294824549815232, 290563673822144, 290563673822144, 290563673822144, 435562038170560, 
    1016104311854016, 593891846788032, 1016104311854016, 581109621461952, 593891846788032, 589631105012672, 
    1016104311854016, 290563673822144, 290563673822144, 149825917031360, 290563405386688, 308431006208960, 
    290563405386688, 1143784293405632, 1134850761429952, 1130383928333248, 282042190271424, 282042190271424, 
    563517435417536, 563517435417536, 74853772235712, 862860012164032, 74853772235712, 92720836383680, 
    75403528508352, 75403528508352, 23025520098421449036053112386400835609949197122, 168105834714048, 149688343860160, 563517166982080, 
    149688343860160, 167555542029248, 150238502327232, 149688343860160, 563517972288448, 563517972288448, 
    580629121471424, 2923728070664188035398424602728449563008461525826, 2923192852774438676444075307543075703405718623042, 2923192852774438676444075307543075703405718623042, 2923192852775435601243865795132441763191038497602, 531567448248157844913174823736097128844121960795751845974434306341994933126652925557665858848943403140, 
    580697304601536, 82068580078528, 290838283293632, 145702748427200, 163432641860544, 581109621461952, 
    2923728070660200336199320681031687754952082543426, 581109621461952, 72654748980160, 14294821334947027643883130301945363522115425090, 871656105186240, 72654748980160, 
    90796691297216, 22891715116806714915796202881703034293260998466, 172504015442880, 145290297349056, 581109353026496, 145290297349056, 
    163432641860544, 145290297349056, 581110158332864, 581109621461952, 581109621461952, 581109621461952, 
    82068512969664, 871656105186240, 290839088600000, 300183996994496, 862172818052032, 168242601661376, 
    532539889101799220683992589817442196904918742896506078774597119529422869149610871153586480073811587204, 563242289075136, 563242289075136, 299359498408896, 167281200993216, 299359498408896, 
    290564210168768, 871381227541440, 581395745902124843139278367478821046963152470659552222654858506268635129133497067158473492328262037636, 75883624928192, 23014456880311265341926669828429896987980157762, 146252369105856, 
    581659376751552, 146252369105856, 146252369105856, 580834475119552, 149825917031360, 172504015442880, 
    290563405386688, 581109621461952, 290563673822144, 308706152289216, 308430469338048]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176076617748673, 11596433824214822256170632680344663460489024322, 11774838384760261032667368938382808761845707586, 79449387438528, 72852317671872, 980735308902498431997701485221357084771536168664656037504984851965575934579626644738769121791949664325, 
    11507228461405188624840636281607168882194273090, 11596431782481678038345242618072369759986406210, 1461691542816108156979392648812690009026625344323, 79449387438528, 79449387438528, 73671649661376, 
    95677451867072, 79307653386688, 79732855542720, 79307653386688, 75870740025792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776595210433, 105707875733697, 105639156256961, 105776595210433, 106120121223233, 106120121223233, 
    105639084886081, 105639084886081, 105639084886081, 105707804362817, 105639084886081, 105707804362817, 
    105639084886081, 106120121223233, 106120121223233, 105639151999169, 105639286212673, 105639286212673, 
    105639554648129, 290555619840448, 290555619840448, 105776662321345, 105776595210433, 1683062796666087482455218032204149148387388503690641542173667872134640634459214755288803413294554931027445763234720860788234538068628310959596272565039303375800231715331984623011045658145064731609215379593645211178395219553675327957255726488283271562262557615980263080915283507266584691851933622069996328934161233306974134379709623685003125523980930455034494366774627074111433738949521781612821798654275495757271725878626000876082087525780653662274843983580557464290679406811017582165051339201904640173408297028332570277219757146802011546318611897110869917027642428280747717448718871570484760962929978266633024540182725697052846534985061375002093982837726008203100502545527924687344053513344218022725038504390196050497591389721244085875814341440621449504807413451787853805696350491056129840234098890259475213147789487907818959159702765912585833336830233244687874117436005430490664201606831417625688538060112599100441505144741046724109503376662162865867581412685098921888455134478750767863889450082059519967921236831956562, 
    645595635082061105784563843682232354512291949759998157872383986214355769719835957114030248969938410704853201609754473273980725323073733999454398808208783665352266797574738071196254072026924116353098048792475039391980979061151471710983259830620208291449801390084919698267665035567904325834424999073754279281275432646570201351549107189696512583690475338220883664363252773747843218920330250495833844629566417875503068745505670351218735313222131683062657855861691804172735606331807925553884021535311568381510108864257303053470747160148048756815322144235943860473670594595706892340512165004107148152236815708777011163069121754961870156213625858982161865537383174215957905761986476964961555315725191212435566630176705187785502278111929027714657229585275600235281254638519073118677300492011640072738580671084764567720133733725079365168272, 105707875733697, 17127037667974468336428502840759516096653167171, 105639223367873, 105707804430529, 105707875733697, 
    17127037647392122459441439975469696266361899843, 105707804430529, 105707875733697, 290555619840448, 290555619840448, 105707804430529, 
    9141764793860607894203101208071535377971475549914782468179310538781690946474113444101353139327866434585238406732252437174328646407782179461137308848163981851164129397729461786807319116160054388198097340365396135518770876418407336038706751127405998151658353668843989078371992446114527153991691654505366403936411225448564060926199778847596425392494748142508363153870019557413851251862700571171646347557437817472598816429186637887257320692930807288769543463298379536422197075621221416364020034134150232886269874052629095679596885511863045615037947314340876277839179825072725561978786862614717842407689743325663922428742141642714891864106365690236513448174794290254, 14272531393547573756877663160342396266619081539, 290555619971520, 871389817213888, 290343018959296, 290343018959296, 
    290343018959296, 393921778761834660491047924465781875345228584770, 105639084886081, 105707804362817, 105707804362817, 105639084886081, 
    105639084886081, 105639084886081, 105639286212673, 105639084886081, 105707804362817, 105707804362817, 
    371085815683523277355496240762347237098458731330, 290555619971520, 290555619971520, 371085815683523277355960470047966685777662858050, 123695392729281776154324680830907950924395418773420513711774277433948379611839455540674987384233624363911137099744867168088638264208791100697000028571151554727473007039917638, 1119008186549250717972877797205634454652828309314, 
    11596431745302094555091818029891226754896450371, 862593724715968, 862593724715968, 1124672583986153395524573297181108906447983400770, 371085796627710871799887822917814931930375803714, 371085796627710729823020597356121964299616801602, 
    1101836620743017761192089998096321304803107984194, 283816816153024, 354615057585088, 290413885919680, 290555620233664, 290555620233664, 
    290555620233664, 871389817476032, 290413885919680, 290839088075712, 283816816153024, 586521187104198254813645053509003345801582898131341410945831859858981260071462232524432505883308814468, 
    586521187104198254813645053669692823761587531051663339205994487953047687277818608311185602047411810436, 290413885919680, 290413885919680, 290839088075712]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [28545062787014666911229576289226118991196476226, 246514083502273, 246514083502273, 105639286212673, 105639286212673, 105639084886081, 
    105639084886081, 105639084886081, 106120121223233, 105639286212673, 28545062787014666911229578576622384131180876610, 176076617814209, 
    105707804430529, 106120121290945, 246514016458945, 176076617814209, 81444399747520, 79449387438528, 
    79449387438528, 91279069811648]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105776595146945, 121002670259927234406472746862566689836206058689245600441129357318572005962985478317286193487993553685552330402380302100848347309795936319253403900457886085089958332509767, 25690556491338218685467278950272359600620831555, 97053213373758536482767242694500393135554712386, 105776595146945, 105639151999169, 
    105639286212673, 105639286212673, 105639084886081, 105639084886081, 105639084886081, 123695392498937389873713026031008379330873147599292021254716145819189694294113370892887670405059358277984117666919117711963374164847763910230277944192294279571238432451898950, 
    105639286212673, 731467232869769418366667779740016535594145469250, 581659376751552, 265750967022100742200056346271123354975386203364984610897514658418107890493754861168491758488524456196, 265783407325208791029135914950560770933036259608709011479497973507619824905215155671440320393241985284, 581659376751552, 
    105776595278017, 105776595278017, 105639156256961, 106120188399809, 105776595210433, 105776595210433, 
    6766417618502702711772487940764974169326030630412874781113794170334463301140426726675249240880121732864930022439174612512871378547301969717945226638662951399152321508087864744355852591372313536312493422840299120468324659264747745216034052068081207591267584536595448008035582556331551192119510556493534657844021623363156509851035964829347357550649999364358094176633517623193502794, 28545062745182767388031051043033423022264422211, 105707804430529, 105776662321345, 581659376751552, 105639156256961, 
    105776595210433, 105776595210433, 105776595210433, 105707804430529, 105776528103617, 105776528103617, 
    105776595210433, 371089997073248001847490021804729841559309144898, 106120121290945, 51381112940723817102984014520585776393699220290, 97053213336539995412115169952748291332558050114, 15132089597824606029294938579764493745169796443384291387955427529834668362862204821468609399004813120639954213263715394815614089204267251739008569243254634568852729850457805213734890924350307002379253797025576810469275387706505393416951639187132984075264746988553, 
    105639084886081, 105776595278017, 106120121223233, 51381112940723817102984014520587465250001935170, 371085815683523277355418869214745121556126520130, 73671649661376, 
    73671649661376, 73671649661376, 73671649661376, 89084140327872, 89084140327872, 144040460947904, 
    146239484203456, 146239484203456, 537800160313693666801786317717183131979374947421342043205663627968014413552512479802207573600540730052, 581659376751552, 146239484203456, 573029569385977991062543329210225784855044328448242342814627317671367155283075598756617051915804700804, 
    159433623736768]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [246514016458945, 246514016458945, 149817327096256, 163299632092096, 46028913718009035691403391721109846825642259266, 45694401263967809232331051087002111728720828226, 
    1461523981738624274032783955847876506853000151875, 45716702094236931585707202671118411948168861506, 1461546326125036362266283430743942558338779252547, 145419280585152, 149817327096256, 149817327096256, 
    149817327096256, 979960733553356403045394092346077206128045485299074263612761660811814303347704933664553129376410128453, 46408025067953432608219533389963802671679820610, 149817327096256]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176145272281281, 371084596106858830460040071677272686943434464066, 176007967480001, 176007898337473, 371084596106858830460040071677272686943434464066, 176076618731713, 
    426898418045376, 299350774256064, 7729078731994588773169520663173251283296907801640110954566326392461407902589179010824201006206595624384034249679197139738901826122469110271954324683457548639214530598008391, 426752389157312, 176007833258049, 176007764115521, 
    176007833258049, 290554681233856, 290554681233856, 143228851462977, 426752389157312, 426752389157312, 
    176076617748673, 176076617814209, 176076617814209, 176007898337473, 17867341828544, 426761113309632, 
    431159159820736, 979753408009561441403821085877675560297771701180358304078786250706770420876921972708662868161585894566608767845429839715650417483777713123531621475651614699327938458556702922806257186251537950066265075002730897254235607712523156343607400479407124371050856969246988552, 4050035796103150511514478395439818754354514104258973876441152487528550318155475782109386997880756624793958637680422149152239475040914966784557402776723050991418579190493399622, 456743304743237133622503763453563951170398999362, 985937581325649841630162394998519639200251432609887395420495737128750867714985128487558625125349591609093729670185984770324529083850703654741099843772767065529058165181327523419136180764860248599499784661046663997838237160258466695334750208615064568527324428749837512, 581109621461952, 
    431159294038464, 431159294038464, 143641445159617, 143641445159617, 431150435668416, 431150435668416]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [246514016458945, 246514016458945, 246514016458945, 97053213341856942889471639834786480012834919234, 246857613842625, 176076617814209, 
    176007898337473, 176076617814209, 176076617814209, 176076617814209, 176076618207425, 176007898337473, 
    149817327096256, 176076618731713, 176488935592129, 91701014109171615405761835991292696255214416706, 149817327096256, 149817327096256, 
    149817327096256, 149817327096256, 92057827393514071553238442363179781741900550978, 163849253295040, 163849253295040, 163436936827840]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176076617814209, 176145272346817, 176145272346817, 3962147287403470016010702432308645357506668248651544168968039659837861734850877599031543432705693201509532693011198807150308255619598351249939881314139746086546686442575539782, 176145272281281, 92057827377563193468189475209975653601582076739, 
    94198707078082088256388419169899259125947433795, 176145272346817, 4080981816248566486622747978161616224421528568769333410407207199332498767289399556565523954191601411595135777940129717163387437158745710009217632404219625272485453398694735430, 3959248884274359365548419067457206717069019400319716417426288999055236660788395602615264067538354604009793740129177219952428115466193983138853946207292012181113633800837180998, 176076617945281, 176076618207425, 
    176145272281281, 176145272281281, 435694511067584, 435694511067584, 286156768940480, 290554815451584, 
    290554815451584, 176076617814209, 176007898337473, 176076617814209, 176076617814209, 176076617814209, 
    513258947384672241508770081198767529029528120476883228694076763406433457368536062294145592635566923626776628088168188713519888649592443891807036862224882537979239082536518, 176007898337473, 290554815451584, 176076618731713, 143091269898433, 143091269898433, 
    581109621461952, 563517435417536, 581109621461952, 581109621461952, 143366290420673, 286156768940480, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290555083887040, 290555083887040, 
    145281841631680, 286156768940480, 145281841631680, 145281841631680, 290554815451584, 572313796875200, 
    158497992872896, 299351445344704, 158497992872896, 143641445159617, 143641445159617, 532150795548267421505637658571878159108952396334665541067527104970043012461355695048811312633464713348, 
    143641445159617, 143641445159617, 290554815451584, 581109621461952, 286156768940480, 567915481928640, 
    290554815451584, 290554815451584, 290554815451584, 299350908473792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [188397414113878598942350365559499709935104579394, 183045214891496774834478724531658395114358731586, 290555619971520, 283745949127104, 283745949127104, 1461546326109085565469944662157316214272888489795, 
    286014900801984, 286014900801984, 308439863792576, 308439596143552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [426685817164224, 94200100853515505560790686895552127626408647490, 92772156262528581988687718766620031499263554114, 145221980525504, 188397414114916412921459883716003771822555272003, 188397414117574868913029715461811385960295830339, 
    188397414114916412921459883716003771823629013827, 188397414116245640917244799588909549215188783939, 145221980525504, 3959248884261713200054070301374900504787186648309658798780682691903566592414038266300240000915910215491626339616934714806643645666349797103727844081826305107932115979325451846, 316745325807681, 188397414113919488121669396126637712037235922755, 
    3965015557814664228012186897656180333172568134776402773959307762878331079072938579465118851890008882862359261610733735737287053059748754282242478971280909612528702970979670342, 283816816153024, 283816816153024, 365399103960235674681222881499677307806022654786, 283816816153024, 123665204423862013091695744586263243078332998781788532443937729108824167316601303465923524800550402188448545940316143953459162093348005521786529748236926260657988406370852423, 
    123696340535246148183249400972245181624177526025726223924698647449929569560573958237196050814774798201249377309206487813761074689582613880672772487531685925652047222181682759, 283816816153024, 283816816153024, 354202740593600, 354202740593600, 123665204429260709645147580245635889287654848008836846424307615232086719432836670709970083437415410646788564129229916432207711768464830820285290478226245794269544377684556359, 
    15015033664604734385304171617226701436605314496455237494291795681606021681079827736075617074811617342380978787129425599223626254634291809215979749825612586198191405910132609334920639918923026833240762551613068150412865007987835282957421676745377897733169697248877513, 284241213538881, 284241213538881, 365466180675625289890224018189037585997878025026, 426754469532096, 286014900801984, 
    286014900801984, 286014900801984, 426769971680192, 426754469532096, 286014900801984, 286014900801984, 
    286014900801984, 426769971680192, 182866808228112565279967155395384909796598690627, 15015033881354251346468457975036149315255745592249626807130963813530430696979169062042352290376891651855992138139960607797816754048365006110807534918824188602283939297982743186520619222551560804150058726295098955509631648888784784050923450850649034155106848249877513, 286014900801984, 435557340549568, 
    286014900801984, 286014900801984, 435566064702400, 435566064702400, 290413886837184, 290413886837184, 
    3957829878074701413907686383239865501658171837967551860237145669736323934851191706140079383456429908679022819247051147354365924974865014835058517931718691008960206582268819526, 983485173535472516292983558099259672340416835892789215131387921690848427180952659264109468581401338848375301458172474061836979836873826344643667220914757848109627509829112915738621966671650072552982360758225568191253976769120753135510955170836196468639925256249877512, 426823189008832, 427319727494080, 426823189008832, 427319727494080, 
    6774196050954635362461461967602982022548002716692884825353129154306731405264943405496774878105943513079369238456748650463643557859837424280056231767766317289248166829356872612579755956072068423242285210450708009443621424277468157730798605023316730241652748165289608155978670200425886081431709551581701604462634265559215331397600102590841920418897810445199187035295986768223798346, 290412880204224, 990553148756928, 2219655157321364988704558315492936806446652486030628537745237583264940623010269544427226925908996681428397034012560562243824547546794912515233761567011089210307148690209982328767286412999444799456115264018065326355519274346574710841694798768933984146950942491179399771552348344339714339526815596656240927936529785466304308115688151456594935655714524001772252163844620467846455076055594541044362344421981808069964478614211348348981945974769524387910076446781883122161365774495529352997026407602234982961804213900, 989865953989568, 989865953989568, 
    283958550204864, 990553148756928, 127214941311622704256526298211844695893270623086573357001146077483017346225896805051960697867652, 286156768940480, 990553148756928, 365399103964897076933080926198393315377658483522, 
    365399103964897076938032686355534977215280206658, 365399103964897076938032686355535821640210338626, 1461529556906314653900892778528220560788394422850, 365421404795166199291408837939651277434728239938, 1584806376596168463253968013908706081342648324518585627243378283275113548289568895156944396007966929045608555120826038077844916423354476375630679414412877977457788052119898244051260743419833626678787201120974601430434073219645188279871559664483730879764513832498877512, 283966335624001, 
    426898418045376, 426898418045376, 989865953989568, 426898418045376, 989865953989568, 283966335624001, 
    286014900801984, 286014900801984, 286014900801984, 990553148756928, 354615057060800, 145703016862656, 
    427181885887424, 290839088600000, 354752496407488, 990553148756928, 290839087682496, 145703016862656, 
    73135785776064, 73135785776064, 145206478377408, 145703016862656, 145206478377408, 145703016862656]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105639084886081, 105639084886081, 30946491887137527512635394397712577111467401421869053931423480197210555848490741530571694691444298637454440404714861679400811931037368747989281518304777692052556589045165638, 283958550204864, 286156768940480, 290555620757952, 
    290555620757952, 283745949127104, 283745949127104, 283966335624001, 286014900801984, 286014900801984, 
    308439863792576, 308439596143552, 308439059272640, 308439596143552, 308439596143552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [316745325807681, 290555619840448, 316745325807681, 316745527134273, 52402071030052510226571306715644277499972362470266378992173871549475382662366924380793745891579781800662363531271423719196554160694383830205800793826175474123178440298881351022300741932098554012186771387746093665016443464520353142376699801445544332809497132152219011821827287771762118368787927202061258484309260574178481901473205758580225237112127236775457400668118069087536075, 316745325807681, 
    15015491880072522916433016304135929284359156940133935635973506323406995497285647122261209856094157300819743572791087912310147621163438626061746688727445777937295922261586884913959276227850809200952828171670709169714428994048017560831101577862237961307815937246956553, 371085815678569806979088637708282623657314355011, 3957316615500260807304151141993611365631737584608255211625976834062548623992585898034778024102235607758465992721828477863741189041684767464095645045352381316679496975430889030, 290413081530816, 284241213538881, 284241213538881, 
    426761113309632, 426761113309632, 426761113309632, 290413081530816, 290413081530816, 439955252842944, 
    426761247527360, 435557340549568, 188398111013183097815981959314676415357914190403, 316676806017089, 145277412446656, 290555619971520, 
    72639716594112, 72639716594112, 283966335624001, 145277412446656, 145277412446656, 73120752931264, 
    73120752931264, 284516645102401, 145689729307072, 145689729307072, 72639716594112, 72639716594112, 
    284241750418241, 145277412446656, 145277412446656]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [581109621461952, 590189718410176, 732180859396178183579687064224734714265551819586, 448458807431084501734840576071712681273559349856749467232355169981524902537735782346991462871560507461, 315581302341600454162980438385081013047762242618292642185958804983852361622108952196963921772582105157, 581109621461952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2076195733906855321610250751793454803949015874625542905023717685644146870777358242094797772183101892, 33218886717633724322929770282846208316909174814442074122836055103559240864881504107036958791236122116, 129777547423926009027780781102568141247809428432542757610719523840815426617176300214442814007725444, 129777547423926009027780781102568141638247729720950328861052970571161682915071093471066967127412100, 2076195733906855321610250751793451608177390250222496765028063275349193198618746324677786622287208900, 456741910950649929728244397489098419508716000066, 
    2076195733906855321610250751793454803913980796492993811941002800266395474592459125086604557891461572, 456741910946651840864762976563459513387965240130, 41523604313294222723281532232352798101976243670243762534684172182216438835877916718125656370607826436, 66502625331739736685845951987862070047603822321133703065636459289366969623524894719964200049852404997, 33218886717633724322929770282846208316897019609211577292832712416407312947856943431186793170145965572, 411092285609664332416856013581923724914719742786, 
    7089992252700859969487171186172208911008898232883260323297872729411723860437239424915604755750918478824280692275026579537920628393011895125631904880325871041964756371662435910, 581659376751552, 365466006455704444305170270850658186048607114050, 1038216427127841050626293395988698719079573027325193086294139506105652934147270431040069777005530500, 1038216427127841050626293396355569673326158933651021827598302640312507228351327928154607205608457860, 1038216427127841050626293396355569673326158933651021827598302640312507228351329609114169271807772292, 
    1038216427127841050626293396355569673326158933651021827598302640312507228351329609118586113095763588, 1038216427127841050626293422770278379080344189110691201498048303206016411043482849037360660664256132, 1038216427127841050626293396355569673326158933651021827598302640312507228351327647994806827390994052, 1038216427127841050626293422770278379080344189110691201498048303206016411043590430449332897420379780, 1038216427127841050626293395988698719470058972080127723250836294544555446560165758529288435983764868, 45762523284908034719455770089311860452757634626, 
    427035856998848, 45762523284908030916503969404623655962648018498, 426752389157312, 426761247527360, 426752389157312, 426761247527360, 
    426761113309632, 989728515036096, 426761247527360, 989728515036096, 426752389157312, 286156768940480, 
    365466006455704444305170270850666911806171140930, 426752389157312, 435557340549568, 1007732615287744, 581109621461952, 8305731417022698958352097782075148137966489218630742390475078754831753390201949667768638273556106628, 
    8305731417022698958352097785376986726185762375652697577746239282234413100114757685273050951104073476, 8305731417022698958352097785376986726185762375652697581810550114854269353643052160189784563576737540, 8305731417022698958352097808856727797967260381142156687681637569611088398775647418072955948383702788, 8305731417022698958352097785376986726185762375652697577068854127272259304519181979881242546352426756, 8305731417022698958352097808856727797967260381142156720196124230569938427002003217406824848165015300, 183044866400560245299219600275978356503615648322, 
    290555620757952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1462220839128391462983701627165148605588829197122, 1462220839128391462983837027373458500252430586690, 1461507215282038483043462627483940235585897190210, 1461507215282038483043462628664531856303308493634, 591634974905280, 589639962596288, 
    589906250568640, 589906250568640, 589906250568640, 568469129139136, 581659376751552, 581659376751552, 
    581659376358336, 480481916521385581297853212313707405463849895553539535509176267796488054283372442442719493135054456599089114842813613920702502828498747899720139532815776348282158144921938446973798957118933279824461901706431255003917817827621043179840075494707391977857491976246997512, 581659376751552, 480481889932903142167854800630407608450563993282697590645993910056489503791618570091768622831126190722040686638384928368825083785486769103506407699876834065728914582714819445455014527405657706359485746142769063252140230891404894434622142701828691104117064712748877512, 1464361710667450402963803409808558176706148520770, 580834475119552, 
    581109621461952, 581109621461952, 581109621461952, 581109621461952, 581659108840384, 581109621461952, 
    581109621461952, 581109621461952, 572046972031936, 581109621461952, 581109621461952, 581109353026496, 
    593904731689920, 589639694947264, 581109353026496, 581109621461952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [376817085501394302402512340935650033589955875650, 283958550204864, 1096149922635686237522569070110328800701828879170, 73670508745152, 144040460947904, 144040460947904, 
    214411285500352, 144040460947904, 365399103964897076967743247298392829540358443842, 354123283435968, 283958550204864, 11440630863596311095682835151132037527946408514, 
    91366501655132336064839459002070373426253550402, 362919376458176, 713670124921035323315652138314541372410975042, 290555619840448, 290555620233664, 532287082837304853857219408770119062390332177485363506637560520741324261089116939018937186157458562116, 
    362919376458176, 642203920110528, 532287082837304853857221167362474354130440468247488048351689537555551543084728794499436899402044873796, 565304150213185, 1461529513348177828279367653769890641568514245443, 565716467073601, 
    565716198638145, 565716467073601, 565304150213185, 290555619971520, 1461529513368780940808987617298717616598876750659, 572314064393152, 
    572314064786368, 572314064786368, 73670508745152, 73669502112192, 144040460947904, 144040460947904, 
    214411285565888, 73669971874240, 214411285500352, 144040460947904, 91388802485401458418215610586185829254057448258, 22880651877387912666330914305620875841810487106, 
    354123283435968, 283958550204864, 847200561402816, 283958550204864, 73669502112192, 73669502112192, 
    4153201855441500818701610578049673258631686710515226850029317199127947990018738035342015558391114932961184338268419131505021848037637987942689378456271626255785080967357495878, 114224853191406947696385725069724209722526029634, 73669502112192, 218809332076992, 214411285500352, 73669502112192, 
    537796105276741744684020501612001949339104881696594565793659786720081817116121574343530077818028466884, 565716064424641, 588409155722081177827047457669990376747846963691417518556147904119760935911429618403304916428852994756, 565716198638145, 565716467073601, 565716467073601, 
    565716198638145, 91262157918656, 75868525367744, 411137932617644142563595875963622425296801651522, 365466006455704444027871699984706393973297533762, 1096216825126493604582697522796647677974953384770, 
    75868525367744, 216610308821440, 216610308755904, 45761216642489893568703548343037959470913191490, 75868525367744, 146239485120960, 
    286156768940480, 426761113309632, 286156768940480, 426761247527360, 286156768940480, 75868525367744, 
    91522607467016192538472520312244348314936431426, 91522607467016192538472520312248781562731057986, 75868525367744, 216610308821440, 216610308755904, 638835659117504, 
    75868525367744, 146239485120960, 145277412446656, 286156768940480, 91522607424813042680675212362423420934330274626, 426761247527360, 
    990141234549696, 426761113309632, 286156768940480, 849398780138432, 286156768940480, 1461685619159563222353722024412616785995229107011, 
    532345469047865660768622333088140680540250989525782413097054333067290222948038628089958588401972354116, 582173774869328525925783379737988441853037947570716238949902121358965199062243510735206108435107224644, 532345469047865660768624091680495972280359280287906954811183349881517504943650483570458301646558665796, 145277412446656, 145277412446656, 435557340549568, 
    435831950021056, 145277412446656, 435557340549568, 426761113309632, 145277412446656, 1461685619180664797282620678387531718135012987715, 
    163281915351488, 79236786360768, 290555619840448, 290555619971520, 290555620233664, 79236786360768, 
    360720353202624, 91701014109169014176807304463376972459410477890, 149675458957760, 149675458957760, 431159294038464, 431159159820736, 
    431159294038464, 149675458957760, 290555620757952, 79236786360768, 290555619840448, 290555620233664, 
    79236786360768, 360720353202624, 642203920110528, 23549676764526323463641451437556617014035896130, 411761136293176523780012746484295148286901246786, 149675458957760, 
    290554681233856, 290555083887040, 149675458957760, 431159294038464, 431159159820736, 149675458957760, 
    290555620757952]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_15_0
  · exact tv_b10_15_1
  · exact tv_b10_15_2
  · exact tv_b10_15_3
  · exact tv_b10_15_4
  · exact tv_b10_15_5
  · exact tv_b10_15_6
  · exact tv_b10_15_7
  · exact tv_b10_15_8
  · exact tv_b10_15_9
  · exact tv_b10_15_10
  · exact tv_b10_15_11
  · exact tv_b10_15_12
  · exact tv_b10_15_13
  · exact tv_b10_15_14
  · exact tv_b10_15_15

private theorem tv_b10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_0
  · exact tv_b10_1
  · exact tv_b10_2
  · exact tv_b10_3
  · exact tv_b10_4
  · exact tv_b10_5
  · exact tv_b10_6
  · exact tv_b10_7
  · exact tv_b10_8
  · exact tv_b10_9
  · exact tv_b10_10
  · exact tv_b10_11
  · exact tv_b10_12
  · exact tv_b10_13
  · exact tv_b10_14
  · exact tv_b10_15


theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H3 := by
  intro M hFirst hM10 hRun _hUsed hForm hMissing hLoop hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hM10])
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hM10]) (by simp [hM10])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  have hm1 : Matches M (baseTable.set 1 0 ⟨2, 1, false⟩) := matches_set hm0 hM10
  exact tv_b10 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R2.H2.R1.H3
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H3 := OMA.BB4H2.step_proof
