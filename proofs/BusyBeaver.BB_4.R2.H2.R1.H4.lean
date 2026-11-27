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
private theorem tv_b11_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161157431922880, 176007898337472, 176007898337472, 1161164015079872, 2926047329103871894500397539599507536832125555522, 105639091177537, 
    105639091177537, 2923103628355649043345064893418267210537546849090, 88064621873217, 88064621873217, 72670922213441, 283777154746433, 
    72670922213441, 72670922213441, 72670922213441, 283777154746433, 72670922213441, 72671391975489, 
    72671391975489, 2923059026695110798638776533868285602931350182722, 1161155284439232, 105624522264768, 1161157431922880, 736461225016239252020611922737686042278021318467, 
    105641702133952, 1161157431922880, 28545062744644064534248331768592456701458782018, 1161157431922880, 28545062744645362613124612948571607843645428546, 316943362040129, 
    28545062744645362613414725632641110425137583938, 7759266745884737787867324976944749980485722624375035250067026618173873121655095158826676605278186391594791347470899107736782885057838547342102842199388598299896765166383686, 105639156256960, 105639554650304, 176007898337472, 176007898337472, 
    1461551814177927718966802813083140508057218389826, 1461685619159542453087059722587838309373906588482, 1464361718791837135492197912681794335707670582082, 2923728054330613674209183686974062803386152043331, 2923728051608354738841675979267065943932006351683, 105639156256960, 
    736461225016249006906417448941417149233564238659, 105639554650304, 176007898337472, 176007898337472, 97064015254883712830238274351438535409233040194, 736462597029632807621210545061950931699069129538, 
    1461551814177948488233465114907918967636079220546, 1461685619159563222353722024412616768952767419202, 1464361718791857904758860214506572795286531412802, 2923728051608375548673157488395185251405369787203, 2923059026700301878071872940871696244821928789827, 2925868931314211294597268040470350072472380982083, 
    2923728051608375548673157488395185251405369787203, 2923059026695132865974237472842459703569821996866, 2923371239680027774975382019335992857489536242242, 3957317799008873970763761087600879064355349768222307227823009895186894345464850552884558577587570585657343013183326204198912114978524210747931749569711917015096112631334828102, 4122072778085587604135317497207966599391823681702799072397628402997300760947198444949474626087446531662455736956979728320499903168662998492694330838424831101769458083461855302, 354123285533120, 
    362919378555328, 369516448321984, 362919378555328, 1161157431922880, 105641702133952, 387374383376705, 
    176008300990656, 176008300990656, 73221215373889, 636171168795201, 565802424617537, 567434990326464, 
    74869945468993, 571833036837824, 90813401418305, 90813401418305, 1128584672983489, 1128176516859969, 
    1128176516859969, 636171168795201, 73221215373889, 73221215373889, 365555209771702847741843769402179107210917843778, 565802424617537, 
    2923103628356146553102912887598425071514746636867, 1130719271727553, 1130723566694849, 1130723566694849, 1130719271727553, 1130719271727553, 
    1130723566694849, 123710547255613018228348411142505057998181807326591802087084713443152720578991573927422672915048542396672609685286737146873183725142089826460086718505174140527390546896834118, 1125908774125633, 580614097474240, 2923728051608334579317428267299204586957942310723, 1134971155128641, 
    1134979745063233, 580629129859776, 580629129859776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161157431922880, 1161157431922880, 176007898337472, 176007898337472, 531505989080171503924627602730668462947096288158612346587480898640016841059646993111555723558917796997, 1161187433711681, 
    1161187635038273, 72670922213441, 74870213904449, 74870213904449, 88064621873217, 537795352846196041671507569279952325299455087475904461258978390803441652633241965525854702358807213189, 
    581395120223413659886870272707617451862079527438797565435372240897817044558833799765779204380370171013, 33283751484824631724446758483998282963383523775345330851677092576751280428005072725496196894568248453, 565252131457089, 72670922213441, 72670922213441, 72670922213441, 
    1461685640257277664118065548106308916232797098818, 105656740808769, 105624528554049, 105630971004993, 72671391975489, 79268461742145, 
    143039666391105, 149636736157761, 4217239420481885636210124823264605328798184035944545049769453061068939475632327179968554065035804804, 188397414113969463843049580055301381630942263106, 188397414113883141907776438539059533101827897154, 188397414113880545769250691441834153062069974850, 
    188397414113883790944883755392513099413869049666, 33283751484824631724446758483631415207216873055400705851425990098864539836687399302926211978635015301, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 
    79267991980097, 79267991980097, 72671391975489, 72671391975489, 72671391975489, 72671391975489, 
    79268461742145, 79268461742145]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161157431922880, 1161157431922880, 2923192831676891686892331857971211080878925028162, 2923371238319044665719341070644141482634509294402, 2923192831336609319971393394507836473447156816706, 2923059026695276952772074948466513279562236828482, 
    2923728051603351272410466812825045137181028392770, 1161157431922880, 1161157431922880, 2923036725865007830418698796882396979342788795202, 176007898337472, 176007898337472, 
    961578463299327237377672734290142200631025010630026512836437250688914458290332136583342627066982594119442469555783589517075827937515374918731579763881345256508255971953092029827261829069905511785493427969625652573684611597027590296956357508613335079760953368246197512]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2923059026695317195761007399259447548966695685955]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176007898337472]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130371530101696, 1161164082123200, 590608166306099525328571617575567872744187068034581869736699980166939635990935231343567059602965229700, 145216076255680, 11441676168657864343435068292608088897990177346, 590616252744673935204111399712143894211080115680331694050611155081055799873539044089862740801544745092, 
    388257367873469144944101173266606174640034304834, 388925086097253839141686021431602643233543312194, 393921778761834660491047924470429590160674936642, 4081464883438992850785358374033573555988170995106787438201214591105341372011600408649789637042557790303738975914966168291072562571170803013332598180663889654011374654752861766, 129777547423926009027780781102568141247763251276905386647639470286044418502448246036744426645147012, 354123285533120, 
    362919378555328, 354123285533120, 360720355299776, 360720355299776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72671391975489, 1130371521974976, 259775872474346304570794861899807299688635041448163778901837578323946549999492910257291563320873284, 132875738930441511880114383112647046282648624617247888141963968498560211978899773226283105209008394564, 74855930663616, 567434990326464, 
    736462602474296063222862073249387112259945272130, 45850507033398638143327887258441336434852889411, 91522607424561220392997203428533394313526117187, 79253977174976, 571833036837824, 580629129859776, 
    580629129859776, 580629129859776, 580629129859776, 732180859396240491379674120818832770101200065346]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [532345381924043839394585471685569663539336728579425720792526200257865007856619901120107746520337760388, 581395120223413659886868512815490779319294179563963339699702884897982466989714258056885431652973822084, 597874794202302461400066704273791789939787055835885018850693724696275807734689517976428164784847077508, 90813401418305, 23192863480302672141767185263145513620831995715, 996326080379589994933119520496743091777794366958514459569193963077839165442708115462282127422270493287427112931742998829383005960305421012779728711342591558516320983363142, 
    996326080379589994933119520496743091777794366958514459608595969276527143270977227074038535219853036444871288158186550446233045153137793723631354559433409291735064762428998, 565733168267841, 565733168267841, 565733168267841, 565733638029889, 565733369594433, 
    581126800818753, 581126532383297]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [565733638029889, 565733369594433, 1130371521974976, 567434990326464, 74869945468993, 981230230681843689449189081081973547746330706239295001358958049426379793908978714229549540697144055562023874588600954154526523101397623052402684756620644437574927076601414, 
    15015934901227361551021311223829871171380923692652681855766858788408077767505568957711904761501106680343530028779589528748172162796241117095118778821419372289545447684822781992163222476233750726880647400889059203776511383001961846419541883001208520984018968496956552, 285976178001985, 74869945468993, 571833036837824]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [636171168795201, 11462627949732559191911268076304973784449816386, 636170833250881, 28545062744811623229150929020351233038473516867, 28545062744819385083467344820072816018719246147, 537795352846196041671505809612560320537211636560031302972369990547075915448550356800272564453487427716, 
    171826676859754011028522233684303235495009780610186054717712868711311536907632695552425154546470811907524317222361941918490318792658254370789978566468017098219099413587811320622309680699519179045142293008017348398010468760975087797439942920696278060052325270359852158401288759517272118789890088233810652575503030020395330537552031107903142130462594029351118707506930686489086386332139580342066334076086742209623546727238558245843801674667779981668162793339006707298032125967871889893364484490617790351559070073727998454048633881531855730842681865168502344296716485416622206597955271919163066520159224237812038711163267541373031923122412445788722464534095, 22881261642536442218942783389336077859289044802, 22881262833524726442227405511147203870477784898, 7759266976116651237019934406609902287483102732879349909718690764862993955939360957707372528382541146012093195217561559882205242494312694143437849084577399824504218350562886, 73221215373889, 90813401418305, 
    97053213331554088238777339717889696355141555010, 97053213331555386317943733581938350078820356930, 176347473785281, 97053213331557982476276521310053671924687442754, 176068032467393, 97053213331563174792942096766248286819402650434, 
    176063737500097, 35193239371841, 316936651546945, 316936651546945, 316934504063297, 316943093997889, 
    316943093997889, 563534614774337, 563534614774337, 563534346338881, 290349455052992, 588343926851645907328321837564062108668569230177526888225920805260696923712410215088328632451088038980, 
    290349455052992, 565733638029889, 565733369594433, 91433404103817034175486912042844732677184033602, 581126800818753, 581126532383297]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨0, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_2_0
  · exact tv_b11_2_1
  · exact tv_b11_2_2
  · exact tv_b11_2_3
  · exact tv_b11_2_4
  · exact tv_b11_2_5
  · exact tv_b11_2_6
  · exact tv_b11_2_7
  · exact tv_b11_2_8
  · exact tv_b11_2_9
  · exact tv_b11_2_10
  · exact tv_b11_2_11
  · exact tv_b11_2_12
  · exact tv_b11_2_13
  · exact tv_b11_2_14
  · exact tv_b11_2_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161159514394816, 1161159514394816, 246376577503424, 531505989080171503924625842850281660983936116414791458100709158212594194589074306498577837570538370181, 176007831228608, 97064015254883712830221349325400326342803723074, 
    653213599025729, 72671459560001, 635621412981313, 3968729083630699560964075902362029628063327047848247627791577557224294583635574877376841177134867969651032479359297897633301181222880409727514619155876520762645383515905932870, 635621412981313, 565252668803649, 
    565252668803649, 582844854848065]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176076617814208, 105776662384832, 283777154746433, 582844317977153]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [33283751113574826881502646815875691083990377550963979501440233531026413562184023832286249308430824581, 1128184905009217, 1161155217330368, 1161155217330368, 1161155217330368, 1161161670529472, 
    1161161670529472, 2923103628355834668665709044154670410802313302850, 2923192831676911158079213650491135611680642306882, 2923371238319064136906222863164066013437300314946, 2923036725865214224371716010433579428474607637314, 2923103628355855437932371345979448870381174133570, 
    2923192853455003410285937613971888946892668670786, 2923192831676931927345875952315914071259503137602, 2923192852944579859904529918776827035745016353602, 2923371238319084906172885164988844473016161145666, 2923192831676931927345875952315914071259503137602, 2923728051603390863826903590334705276529477161794, 
    1154573452716865, 1136981266672449, 1136981266672449, 105639084888256, 3965649587878131208883460940364844451279921343390911641318833099812236577141935032742565257869078389366426940024193355847698505559876552358492310888700101023024286569687151174, 90263645604417, 
    90263645604417, 72671459560001, 90263645604417, 90263645604417, 582844787739201, 90263645604417, 
    91700752730188707135246255681167111616439785282]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2923036725866190380617914583852746440586544812610, 105639084888256]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161224003915968, 2923192831676892985013066089480552921016694232899, 2923728051603359709889844585577618803100916123459, 1161224003915968, 97053213331555386518584462618587385993420625731, 371085815678538653198010106239388398838524413763, 
    1161157705480641, 1161230446366912, 1161230446366912, 176068028272832, 531505989080171503924625843064953579354509860124984292537889600874033555250990297408811093149414356101, 1161161866217537, 
    97053213331563175070315765646824481064986609475, 2860081461121140688163856849192748199921059651, 285950610507841, 567430016416193, 571823633729601, 88047375878209, 
    17678631700545, 2924430527799382744556857392048762468904806647619, 88047375878209, 88047375878209, 176076617814208, 176076617814208, 
    105776595275968, 176076617814208, 176076617814208, 176076617814208, 5720162922200742842393525768293283987898506050, 1462220839086188312811835063792808377352266008387, 
    3957286427485527111805477507569384677388197752060051652729996753382972449793947249485911536061608457065777600394253231908016601208923628725595528680101940678125982499569917510, 79251551291457, 360726528011073, 3957287367290623191565779140878084427802216213286506017857991018671715379244991432551158729767460208880575852777361794982081087755051369382071975824909439006870213263007666758, 531505989080171503924625842850281660983936116408053649098292779063888990054896413044635462020133057669, 167212481518529, 
    88047375878209, 88047375878209, 88047375878209, 650997329316417]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [6707465090285017895107818191389901621926133054257685855525791364560159653211020209671377933933401792413443986069145816305038416077576282507155909462808839490572717863979023762415453167264216245555305923204298859739710265085280781912118799601257685850970672822534170091608093093750865353585958229398080821034493593903888598455914318629155012027174055545485412446161055567401031242, 6707465290317740354642250853982272085327249495267424299173368799134817048895976581470149896209164965057803021502078480202732665892445888212580138136788982163563929091913840703591367251940959161974864542716197957642554855816014087623705551138209925446974672441333128186422907658604935582228718818268157068612549770605439134750731364133557962839271145116516383523890319093608919627, 176076617814208, 176076617945280]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161187433711681, 531566814649450785657876692755873057561058574624967249286978283030288697046251541507296091565176668292, 1161224003915968, 1161226151399616, 1161230446629056, 2923103628356831593465514038909212078358858306370, 
    2923192831677908082879018645245677279237187310402, 2923371238320061061706027857918607680993845318466, 2923036725866211149171521005188121131215524729666, 531566814649450785657876689321122363631879437915036905068175173641273992667535504922488239424142590084, 2928712635661257196045706962217318768679130764098, 3966977959076672256971232807554050299232938779681435635647164338630971258871635011348315382085501894558710320255499749018595807037014125997581032226141252665417883801819804230, 
    176063733305536, 176063733305536, 176063733305536, 176063733305536, 176076618207424, 565252131457089, 
    565252131457089, 565252131457089, 265751470930879079173625990593753080964209891387315479669662697425455516227880961839306975587241325701, 3967944174538650542346113567387258296924358342001061481783214127391733418968238398982191086297871048931861386321761811693643899273032029142183108428403185238997260049355633222, 90263645604417, 90263645604417, 
    996326080379589994933119520496743091777881706056527201096785548209996931451653678659942041214862220623012574496266089929174426284623384909317728350166327176472774684487238, 4217239420481885636211902306774912349440754979958782807633082870870782705912121386921211952693002372, 33283751484824631724446779524440940144001730970033865548963398665974538611054788509071419324135391364, 33283751113574826881504427844407618465709599022215469622294174018133283754661199024533471075829563524, 33283751113574826881504427844407618465709599022215469622294174018133283754661199024533471075829563524, 635621412981313, 
    265816731696893447730563648338298532271686799263586337390751455781923227517926766423228073299417514116, 265816731696893447730563648338298532271686799263586337390751455781923227517926766423228073299417514116, 582844854848065, 565252668803649, 4152865693042607965995069177739958329511498795945467500771156724001255848246313359467453428263043204, 582844854848065, 
    74869945468993, 79267991980097, 88064085002305, 97064363705232057337638366688658994084918072130, 97064015256088330296651780193060983954269541186, 565252668803649, 
    565252668803649, 91433404104813958975277399632215014603260695362, 582844854848065, 91701014068043427215791218641610617236637094722, 635621412981313, 90263645604417, 
    91701014068043427215791218641606395095880307522, 537795352846196041671507587096070627557854207506909961914684289146773051988838437478776189649749819524, 3957316615500260807304151141992831500103344884535467570324121745176846991985807377761381584982430091069911911740621161325496332202124968368959241088361240984769931848509992518, 3968910228068469036001766895125066278449836009470395657905861091054779038888584778512759564433537251097246796591671800698987465655300287671609496589429745852117319898407843910, 365555209772865926674932671589773089917728985922, 365555209772865926674932671589773089917728985922, 
    365466006451789437261428065253307889039936852802, 365555209772865926674932671589773089917728985922, 365733616415018905501941884262703491673313252162, 3957316615500260807304151141992831309566934254062380027132100791853866600646739817085991542725913483608991353828358975182979786819233982349731201074043741373986436410447670854, 3957316615500260807304151141992831119030523789603651955899915922174428091309662868716944737715959297422901156776084976709205218004649536265124879407003636153708626123332693574, 3968910228068469036001766895125066087913425467722822939161670917974809795631704750493442095672864684258517740562427231737121483387014726574138885967953657245484154004634024006, 
    3957316615500260807304151141992831119030523789624636516557989324557936835536131930148596267429194392198006315874505334610227324055346470636695869297406191287904233271042682438, 565252668803649, 565252668803649, 91433404104813958975277399632210792462503908162, 582844854848065, 91701014068043427215791218641606395095880307522]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [3957339337591055769107053545864656162519075236374334189532962770466037522181448595860383036318744008745233176638508473638933855205707413699985287259721443790615842271321388615, 6810605479372839467676686575988707432105478129026264635705998860926826766647170267710467233212195942761625152014563179259649078980197922037926105601289138613136305074758764325729907916811338622012017293513681554172277364652626754866057113716455051213218795573755089685960613395255603576621729076096464331874575109992474456334867839743764281970769075906743596251537108203564354507, 188398111014491906338793875293194513772953236034, 538580850148118187424936391308467065105863925515978889602693531461748210273162002716171114762797784133, 145212987939265, 145212987939265, 
    105707875733696, 105639084888256, 3864567008898268209855935384570472752230604793519486511525948587724649738202839230495694625276401011709825348762739452216026175682535902168149532499274899572872808937180743, 538580850148118187424936391288341572671153788583326325323555170598312467138486641495994591097920887877, 145208692971969, 145208692971969]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161368023863744, 1161368023863744, 1161368023863744, 2928712984111730155855994636736367829576029582146, 97053213331553114679482479827091651439802992451, 266594411932911499093404785391064154659195186632900150291824168070803934832648991689609222542419588229, 
    266594411932911499093404785391064154659195186632900150291824168070803934832648991689609222542419588229, 188408564488886449535656343252475743710312674114, 188408564488886449535656343252475743710312674114, 583925458845267980548559346308943340335940677614606395823229413579985575909007924718815994839594117, 7759266745884737787867324976944559444075180876167705075617573173554365237872717539787181405995559843175587190953274518437637442829229180860800980365331336133789291728812103, 15015491880072309539971164536928681804323212865234115017722660854226675176185803216055622160117977909396543926086974433802332005374385042695800269572616597109850518497279157455142422401414415546458925300333684842670949170307612203409324926490023373966409985745997513, 
    1161361581412800, 188397414116204756494125174450991927353369704258, 1161359433929152, 2928712984111647079086451038860845340841796973378, 316934504059328, 1161368023863744, 
    2928712984111652271403116614317328186112663892802, 316943093993920, 1161368023863744, 2928712984111652271403116614317328186112663892802, 316943093993920, 1128184905009217, 
    1136981266672449, 1128184905009217, 1128184905009217, 1132583085808577, 1136981266672449, 1134782243211329, 
    1128184905009217, 1128184905009217, 1136981266672449, 1128184905009217, 1128185039297473, 1128185173650241, 
    2923728051605758559929334276762255195482823340866, 1134782243211329]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [6708709454003498711712893720301969512853088724843040759837900541143406465717631566625276611971480008669755918976504901886503221981473367809460304578580537153405617093922561470621064453023191955829882789045213506075206439147216775229402147860092712197048791576947047128457692588964901267944517406240052655755645119646244115000777916424663471394568550867199445057472722578982522955, 1161363729027520, 28545672530831212176498521947500707856509306691, 15121341268955092079109659562871695680436436085337612081943056528982723273771759213441244267027355813619225171031473199732179149074655419668362662296872053919022161064489321362654127300950217961788922664022842653598408169758804808232655297114450222383112245956552, 176347343753664, 176347343753664, 
    105624529012801]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [513258889781001788509570720035985265731968141806702144541163691612551015439548369316646175685868760021903981322251315966690459439192410357592829888520025403765686634757702, 106174278078656, 106174278078656, 513258889781001788509570720035985265732063972932810994878576520927802486476726203516297122533471274484567087622455338387289388271372266473973393985548682296011154511576646, 5777511356834555515219647630061847477074702918647034492580000267644424107759305187858171693335561120613301092601108927869281436339017249992738947069412923402862317832662456387116890667247950542555145567328107730873023725020458136249479471563609309248448338870870752591488233847408274250949729578306739540056693151178710352788246251495207536508511086212525130427256661802318671081112579799163939941987588600514141358464089859300136673698110059841684445791511762675968234259309289097409660700527376700461420981570655880742527981200325737724943936123351443382326291864014593536957925160478334247753731829500928012105648068604904111704183352163567745113173521313359, 106174278078656, 
    106191457947840, 513263957357499961965874025930937844684687755509034700457331070021919002657736208453064040864493699554359739999048942959870871764339755777419621940202920010577860548836934, 72670922213441, 519108211630325995749163152320071978886436882708079592448056326571139683790314565820614696488170629, 519108211630325995749163152320071978886436883117206517336114223651536246370383581194875170719298693, 72671459560001, 
    90263645604417, 74870213904449, 74870213904449, 88064621873217, 7759266745547319253286405420057457481651520827188237384294715472799794950081142025682043225350483246862036169907544440179775650023214100984438992561463436460886613920046662, 176474304942272, 
    537795352846196041671505809399565523336294915725345763769790271227313801628491385458934440820022473861, 290348657018945, 597874794202302459786551183924199431720058198209105808611286459207167705997988571202655581305166132357, 123695392678943148537638517488188094684088047980923624725711966272128745695210382098822573891420289594897776698079250850350780527468062497020228611187784289939524761379188295, 581395120223413659886868512827230649898919355688238867946184121321689193554083219698858942841585431685, 853307737271105, 
    33283751484824631724444998603506660727581470337262126848647669400660456940470309468388740233768236165, 2928712635670479399483487569554815279923908842306, 535719165589160008864095959973165177952639864209766663449546980468152943098653672695558809115155788933, 290348657018945, 290348657018945, 285950610507841, 
    285950610507841, 265755020079053651050095576156439049301051500042493046242902664405975706027437650451224420899689440324, 290348657018945, 431081984637377, 290348657018945, 853307737271105, 
    565252131457089, 3969846174205101288043620558039672284235688039050254419199317763359991499785517512973042828897914678349138206584833870392917314650076882139550663218700532437250058249052336710, 565252668803649, 72670922213441, 72670922213441, 730778694809709219337979637835778616269599740482, 
    72670922213441, 587500716325144747500371213144797737697921083577527879386290135244273926195837748829885668276477392005, 3353732745949935050668354960890948598241340268178191102085203869943202996658419757200250003444304889287791564268245088501745259208536645832704057526790825151831481883636664062593091390954735943673139287846608945927726990958258214530788421369533701489738500502295267152484694341604194526548055995161897087131443197671524370028801203182408656385185891494637668889020707683082543051, 571823633729601]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105656740808769, 23014456839146578817244339563401578457912578882, 519108211630325995750944070581072928708144539509232109123721905032689721878461591042265919762219140, 387108095404353, 387108095404353, 150958497008678147900342096783323651760441105890494707020687780555064386874623674774049414387864027705039324108467670678578655538443188930621723508884741846791456191458886, 
    387108095404353, 105624528554049, 387108095404353, 316739351030081, 72671391975489, 1461685619160767839819535334074161335489435538242, 
    265751470930873414351166178763727948598599229417831093628394994857138119847117183464340711135640830084]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72671123736641, 72670922213441, 72671123736641, 72671392434241, 176474304942272, 176489337327808, 
    143039666391105, 143039867914305, 143039867914305, 4217239420481885636211459223909292780767198892747729071515133004449734879936641331589600336568139908, 7729134014253644380808226066748522678926094992404318798487032536507106058357910048733309578667603482962723217659767361575720695673507180428006228972303132481923332844761670, 4218126459056976522932464163831125384393172883087168024143158358742621214415871752548784194078392452, 
    4218126459056976522932464163831125384393172883087168024143158358742621214415871752548784194078392452, 72671123736641, 74870146992193, 4156413851247922482656873748831850459650821676658225887614505309378707400614716384105808741278171268, 4217239420481885636213200642537217579202479411725254542942548138419533071187295987099445502543151236, 4217239420481885636213200642537217579202479411725254542942548138419533071187295987099445502543151236, 
    33283751484824631724446425946767516071457919959945176410476881697724917018754819830408809301411065988, 33283751484824631724448431841172770712073758559264579842896226576883126281273856340803408443036889220, 33283751484824631724448431841223546080548926648187531856947380427588394947115033230667173323521355908, 317211797623232, 33283751484824631724446425728741345977411954196982427817694101772852561392173905807884371237633486980, 582173687498006831640714275388229315184330056827872214793789514985906806787646607199957105875564917893, 
    989322077752893486994204211112992893429643555281817028700077039663807414195740086661600167552008766317921948159397951993194788257486827740167065362113953573633571089013979206, 72670922213441, 72670922213441, 265751027411102706756238804040073728187637940755499410225882485664261306652375304135491705871818768516, 72670922213441, 72670922213441, 
    79267991980097, 79267991980097, 265872615188032345003444305628126799011506052606411668973715655295076482178175598230572338284548538500, 265856395036478320592505898608001162507671038883402993138344869050926001959306610063693064390019858564, 265872615188032345003444305628126799011506052606411668973715655295076482178175598230572338284548538500]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [387108095404353, 580628585138753, 736462602474296063222552435942676993166358906691, 72671391975489, 72671391975489, 265751027411102706756239023864118139655102690199042144488528597729936491584679724562828793041743462532, 
    72671391975489, 735038153295407254265949365575100471625558102594, 72671391975489, 79268461742145, 79268461742145, 1978690386430320492280268009207877730187255961980803920004303992422097616498222124125433669670486604634237898323784552877975626280724515584251469877331649817132659566299836998, 
    265872615188032345003444305628126799011506052614412373232962767755820198775591905692707351020787155076, 265872615188032345003444305628126799011506052614412373232962767755820198775591905692707351020787155076]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 103) (cur' := ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩) (prev' := [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_3_0
  · exact tv_b11_3_1
  · exact tv_b11_3_2
  · exact tv_b11_3_3
  · exact tv_b11_3_4
  · exact tv_b11_3_5
  · exact tv_b11_3_6
  · exact tv_b11_3_7
  · exact tv_b11_3_8
  · exact tv_b11_3_9
  · exact tv_b11_3_10
  · exact tv_b11_3_11
  · exact tv_b11_3_12
  · exact tv_b11_3_13
  · exact tv_b11_3_14
  · exact tv_b11_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [17127037646893740555325536179699309789936091971, 143078384996544, 176076617814208, 1161223934644416, 271725294617026576778587223680276627038125798480115150594820631617674603730028641866035804789204629825939403650137811540662025808495183528230433788678204606514036735656518, 1161223934644416, 
    457822182060481, 105707804364992, 105707804364992, 565304150201024, 563105126945472, 567503173456576, 
    580697312989888, 580697312989888, 105707804364992, 105707804364992, 28545062745182767387997134877826174654330443586, 105707804364992, 
    563105126945472, 565304150201024, 563105126945472, 567503173456576, 580697312989888, 580697312989888, 
    2926582557882823209905246862501370372664751899459, 2923906458250528527500108672407414346330987909955, 1128665941819969, 1128803648820161, 145290293153984, 145290293153984, 
    1139244651778496, 1161234884202944, 457547442557376, 457547442557376, 457547442557376, 143087117537728, 
    158497460196288, 28545062744684385483917565098884251405678543683, 290413081530816, 284241213538881, 284241213538881, 426761117503936, 
    426761117503936, 290413081530816, 290413081530816, 439955257037248, 426761117503936, 290413358355392, 
    23014456838481962284050643317772173420391306050, 531567448248155956624631563661565778669274727921193943892106734364477886087763591032388992032921789316, 6707465288651853479360495980958811345921609375746675568970714380959931488484015875868622091053248403566506894901015251889425515589624072847027273533206813734124220414125540964566937137922100968833727162609609570095005134494076800848605556261369393406586952712586432470250060605650169791769616349589905188264808553864714198898407019758212951118009110692431274053816358049136618058, 294824566592448, 294824566592448, 94198707057520514261017247657215916548175237954, 
    1461512798593285618585439387753370289777974252354, 1461507223406985985929654003823802127687597757250, 94198707057520514261017247657215635057092399938, 733608112533796630262035467439773275278805111618, 732180864841090670380977181470328283750639702850, 1464361718792397905691770575762701117960363250498, 
    735038153264170277205847118285400244185448157762, 94377113019108759246149533403396821966320112450, 567503173456576, 567503173456576, 571901219967936, 571901219967936, 
    1461551814178488489166375476164047290309911058242, 2923059026695609261038671777662968632824010120002, 735038153264170277205847421108303879706054332994, 735038153264170277205847421108297265018868699714, 531566893848442985190980866565838319814510725970038352137472845857340833307965674835776787600474547076, 3957286482768179822531042257984468785437068082030258016383769115544942809057608321147370888756246284286255693059950817639862260315512013855012130446437285934927226024354608711, 
    145281569001664, 312416337400768, 312416337400768, 2923728051603682931639956325186457639407451118402, 149675454763200, 149675454763200, 
    149675454763200, 149675454763200, 149675454763200, 149688339665088, 149688339665088, 149675454763200, 
    149675454763200, 2923059026695608287479296972801716333552219461442, 2923059026695608611999088571267728496983139161922, 366090429703230115313587502811779246858310797123, 580684428088000, 580697312989888, 
    580697312989888, 158488727654592]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161223934644416, 1161292725424320, 1130438095606464, 2924441673409005353028209606766414086653685568322, 736460005439583261659593149001266642145497860931, 2923192841886358645760592555771045387912758760258, 
    51386513902450287887062717442484616599899753283, 1161223934644416, 1161292725424320, 1161223934644416, 1130438095606464, 2924441673409005353028209606766432136236701356866, 
    1161223934644416, 2923192831677887638132283606544289657538786399042, 2924441673409005353028209606767557965783121302338, 123695392437752162267297064228050704891931953232392857209965434562195525412895398249253533934232014555082304969400906757094743142347449805722689569569392983291353154990340678, 531566814649450785657876670215531265998023650814469149445962678396974550855641480900928967934390477700, 1128307859395264, 
    2928723415891629091193415133217131434807367078722, 2928723416487123232671248800015070982561261949762, 1130437626303168, 2923192831677887638132147941883454188907778806594, 1130438093968064, 2923036726461497923770140233772942061223291130690, 
    2923192831677887638132147941883454188907778806594, 2924441673409005353028209606767551210383680246594, 2923059026696272904645699412188197311218051978050, 1134842306105793, 1134842171888065, 1139244781810113, 
    531501997402235135570266057528833763471682157651696387902154135095012962116346792151183095000307549060, 1128307322524352, 1128170351235776, 583988817845715522282548277057316118034242066726001551816895432248113847622710215999529601363035012, 1130506553398208, 1130437626303168, 
    1128170082800320, 1130437626303168, 2923192831677887638132147941884609362220789273410, 1130438093968064, 2923192853455959121072209603540584237853954806594, 2923036747642912185665507549982626855135656088130, 
    3957286895545320061413919472958409645424085186261335607198354468214506283902308234226851265542558106707857435551514029830420640234258369851367470619126668493135111716970475078, 2923728051608334274446298948382990576094680273730, 33251311180870637908850362346532789462154372962339655884440062191249805143996469626718623616042214276, 33320817064557699315718245208452227334774223121968803112560286138454195804553410831699237208856150916, 1134842306105793, 1134842171888065, 
    1139244781810113, 2923192831677887638132283606544289657538786399042, 1134842306105793, 1134842306105793, 1134842171888065, 3957339332984168043494820449866664730648709415620473584837467617283755975736734667435069339337563622868884245518104840654559129936665604913092196844736817062989590191461596742, 
    2923728051608334254163888740266685466162673767234, 33251311180870637908849606701380125042695486034569822421310516445121656221240162115429772072142939012]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161223934644416, 1130438095606464, 469678024263016139997925092733038148265021498842876956298899586531685883355582303001179184179484421505256473335555695682572593678469943427326089789243350715906782197321511398600367900246175960134773535431392425133688886754632352241094341393512964122738728749535112, 2923192841886358970280384154237057551343678460738, 513258889784516564910739244558081963448152154053759574390080210393235551783210799614336310876033095827373151273664681914249514836972170100563990566103931347903534153562694, 1161223934644416, 
    1161292725424320, 1161223934644416, 1130438095606464, 3958161982852239929516173254380978619403184328274099921641252158115666795481697524248544194229144757116520398718548948582373663893513306882365824203913593675212566168355174982, 1161223934644416, 1161224003915968, 
    2923371238321369853829870283440062922772571045442, 2923103628696429223626470449069872177170108980034, 2923371238321369853829870283440063344987452030530, 1161292931142080, 1161567947461056, 1161567611916736, 
    1161567947461056, 1161567611916736, 1161567947461056, 6707465390364365307182095125680381202604781665227609877328574156601727837705869409039535838733798526089830611224902398092939828445654538508177808970880009785881228387377778044972296904404234289644434375946643860355757921812174761143343958352578074515722619043879131173698053671971036301571056132237624565684563133360225817524369442886024518088916964712497316474466030790139724362, 2928723415975703082009977653683026330563047864130, 531503486361603566275760653220519167430128034432585754209242425308879491362098076808896265269632361284, 
    960962154094212046835217857624440951424096275637579796069636816868642619264984785735035035233159779123873894784105522962006944061387967525299830948233227962960507173447202066213000921174324906279652650463844006422091132013856551239973742609450114369047233064499877512, 960962154310961563796381349092987141023482347080576280328732927650018768590002535445326502868749945654328487325878141426743632794923418040965390371636405517744364308925008086054178346212446573993770133999868561300655409331624781512045027757814438056855339560499877512, 2923371238321369853829870283440063344986646724162, 1241673271418550916396520376575730307540178349248654888986342499781980523833003359678130618967144495355375247878611979269935328552090049822727441431498363516596854523599460406346019893258988385028762334054296295675416490048876598575474269615835495363515257797547724224731831809652044908322745263378386696615118235344170368721756988023768459969739642396170380162451989596124324268706684102759167462281964331762988994398623781702700405784282383367016942362884716605009232598699741549410557652649622216277737721996, 960962850714049710040085628873609825802750427199226412457475441315295320467282615802139671429763247131503308992727617149271589935272404068657789616807057977244950933366442408181616720959548670762524733992606946770400653272203573821493730554059483890873008680499877512, 3957286482768179822531042257984468785436994218109606309930234532562980941598398225378073911498917026042393541056101850350873541938853003773173799117632595723917690409479797319, 
    3957286482768179819956743135435490142320235095902675067235294942625017422144181710904869853845358986894794954384283188081039807268475209140374578660951386650069499003568880199, 1161292662706624, 1161155422982592, 1128170342584768, 1130506821571520, 17127037647350908525252730186018423426786544451, 
    1128307859395264, 531501949882260587742187610211575808429016602674890689220920176913593323479167887967834110454298681092, 2928723415891629415713206731683143598238286779202, 2928723416487123557191040398481083145992181650242, 1130437626303168, 1130438093968064, 
    2923036726461498248289931832238954224654210831170, 2923192831677887962651939540349466352338698507074, 531505989080216822504543739506933666532098555589091239672336767272436127382411072883958701082366222596, 188397414114875523427701518915615177720647914306, 457547304145345, 6708707854819202884603636176463012108275106188018871525410317605420485298173177239391271040804994390939444670675304637642598103426392960448823243829310950313614222498375136128620182622192123406006692395420123847061904761902192414415189849435634182303620932461687551170554279555971604293708250251710432404755890494070856847791788553979125550136905191054059114549564845323962975306, 
    371085815679525842285135295996346575438936544066, 176063737500097, 176063737500097, 1128307322524352, 1128307859395264, 1128170082800320, 
    1128170082800320, 1128170351235776, 1128170351235776, 1128170351235776, 3957317794862675017712751301202686775671948970471113989644739306733616777002398946886346849952058556984040205422925154294805554256831536723390849030727781783431479816196423239, 1128307322524352, 
    1128170351235776, 1130437626303168, 1130437626303168, 2923192831677887962651939540350621525651708973890, 1130438093968064, 2923192853455959445592001202006596401284874507074, 
    960962161246946106553613076086465357131036759734445265952704583892608121699889201417465547452352078905714281121615382651059410505247127097265534266940790355068065121667465879483907934496929324859610837293975661863466069849915511879355934624910469995803198488496988552, 960962161246946106553613076086465357131036759734445265952704583892608121699889201417465577640365967297555312577253637411714181501830834549476031170755071700726930095338330103503316309929346644574099847128060571483361575854149071618040396581222838424314070040496988552, 51381112941387784284626186105048579849049871170, 97053213332550363998984630375231429278622028610, 123695392443150858820748899887420302518541014260326841061158186576529611100498503793981114644910379067544109727358190191350206942874425679651380597416081380556891046597852743]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161223934644416, 1161296953413824, 1161223934644416, 1161223934644416, 1161296957673920, 1161296957673920, 
    960962154094212046835217857624440951107806712262279983817202050448170655034580029768328270786130071086255209997667329915222847213978934493506894479760741258540216311797478417141812949510751527537735416576355285350567129064275513333446765515775448629278408977249877513, 960962161246946106553613076086465542205615557573065515190921183565451612352787909040766079651138504729560130847144480128054657021091273596257255677441175188003488634192908011397797557038327425985696040234368119260657581080499582776292379833173043636877656337249877513, 2928723418528153142183535662865341642988447616835, 531504151641267062747400581313134447814776641310020136407040600421095136971018494699882397050804997829, 6707465390550522946789860969267752413002088172480926926541585090883387819013547084458945004730414139790283293070701334527544043748459028808557486946071787493952723610901651723461976923565990621044545831332474965983261825946061646445214050015887480410611159304617642589943727007581707197414776706452717812727263249325011955224053987889730113471294446059336556949617795332672078411, 3957286427485527111966371202728695842583086004901931236426995506072616775467236419197880985702117199732300272127969839083181903243704474501254127869454457735409499212361988678, 
    3957286427485527111805477507569384677388288559763998033758561781701494055501347887043305732098769822285575360460981172691317294826805862336704176590911882168293987249492556358, 1241673271419102399023427401133548204471370824065041576931930751793245901092937601375328472750869528716746384022830975495660185690178315642122727179826232549738257263072802218181797474442858829895469816834511231689340764301839590437087960378183908898204340194813175771655560307727029625104367850038390135927112611265014671134205332874743476389962985081200629236542068282858462937114549855491166107546704954165083013132243328098020608170382930046506745984569209047269480853129615180579419389316073912484609089165, 2923103628356146532186677983832639946819143748163, 960962849765770573335414260340456838955501032558072554501011143307895769897686897087650781750248923248430203378468996578137453723023060965205965129494716045943761917513471052103537293181196325162830112350391848023053113231124683945121667374530847616209518865249877513, 6707465088723695756462041669077627629859943211427288058831457131341713279935809002271610882710813650485932675803784137863628345841985103568306745798581158147074384868595037607039921568856802764523077785237723707149458663997015577662365705601035296011234305753111001077961187066934169305745251765191385971926028346252459572608401380585183041787493444181934441944049748146458592330, 3957286427485527111966371202728695842583086005118546056260009108200713492655297261866719173303911703721646443879684709915012693108972297993093731426110884722610876029629068870, 
    12995352556590391547090711667250586426391464357400076912311375531663343041567560235921482852927579133498948800089452705365656115620026971764559472355651110622181767127857590587927179238076744149701088107269902873047117215703868736895155459350219604231982115670174825017692413245610156680971634011868477351001548578204349992936331137670883174982342212605507445228146260197963, 15129686125361116623662076964425833005300797141065786733771617122180420467800614305581003132509406426081820115971944083728535400350138856055965882219289475661849478727905111567136729357121261803806524436290884170232385150084321080018460196674985032417553249877513, 74906789228993, 976563712720603260717777208750273388250964354637735816037109208872807088797734534422239527110693287867625175355091054681840218667956039101278308826770678063676805075758418892739755570867542993144119977818300023679158541664666348610788485954023038737390240017249877513, 976564170999001315532889733368560382196048653792845013125397604553351615971739256936707821033609179570993235993437151075672307392693014210318830869321238190238546648645050696628398084573719567137091969899038660482915993533584565483038374436874249341142827281249877513, 3353732746239847217010914814318849298566905040794536831012404095733855747015685328105455445614511438747860069146739202176916172054926006715991653242498100339323605223143262503674726879258102296563997567577195456737890012686995592247419021381276322840265517165278041021951755024528224512932768467024239214731342252799698110236944158590070528170832997529251349291066893776252584523, 
    480481543610929162069102182369623637111361219363730816803003684398040793415174390128664562072029200448464726304424941761958425749148170173470610399787612253549960695277237647187638784797851857228654951883595831998347037543821604132457978340149899358659150097249877513, 15407740796022820280058372756542060607757472298366080610665729006692088462919363511911619188621057648357570321524917160670434088752609718255196776881183792203418856019024805437798534338484836664891000007689371276988194940494833215676780089686602964549641246988552, 978462815493721806278134885430146034205676095304594973089764006051352659120935699267056063013479087928900653210361051580144021980659710616549762709878643817470668494384776292862222111402248264634900175948900512175693105652568945233783308441362338627947856145249877513, 439944649650625, 64880622651665479313570421941734428103329393415307907375364420830872620750229776869725410527645381]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226083111104, 105694919921856, 1128172498719424, 1130440241976000, 74913231679937, 145277823488704, 
    2923036725864841676285091483993723892218483249986, 1128309945799616, 1128172498719424, 1128172498719424, 2923192841886359619319967351171369706816222073666, 11596442630309896371493455873971242593641632578, 
    531501997402235135570266057959618885364843945119649996695113265960375500761426589461802113610699719556]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161226083111104, 1128240733753536, 1134838011138496, 1128240733753536, 1134838011138496, 105694919921856, 
    316801360073152, 1161226290729408, 1128172498719424, 1128309939311296, 1128309945799616, 1130440241976000, 
    88652976755392, 299759215580096, 163419769541312, 1978643215499139501476759980673466366837641082419634725217316849180467675371691424846428161795472944102266062071535185640373199643838906357575393595692246502019106527801997894, 572163074560448, 1128172498719424, 
    2923192841886360917399133745035418360539900875586, 2923192841886360917399133745035418888307495473986, 11596442630311194450659849738019896317320434498, 313228237214656, 513258889784516564910739244558081963448152154688373304437953710590429281036325532766740036008266566811423691687121005099007201418620862075209443223827333043817359960144454, 51386513902451585926615030049402227426713422659, 
    572713384022976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2923059026695286044396378167530761086920820823874, 2923036725950082318941076920140305752668086771266, 2923036725864850767909858660842160036384792976194, 2923036725864850767909858641952698467784994132802, 290279660720320]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105707805348032, 105707804823744, 17127037648035969725953415877778136662720648002, 105707804364992, 583925458845267951737559787845705858078069422078953452252870657727135882444280837827823654859457412, 74921966310080, 
    271725294590665780579838582906530425241001979754924540940371749673933795902132261525798371270406481307669588476372105058610166631050494127404626305364425977194100696205894, 11596442630329367558989363832413219838119449410, 105707805348032, 105707804430528, 105776595144896, 105776595275968, 
    28545062745826614654543026945341863418623169346, 105707804364992, 74921966310080, 22858351027200414543624372995685307459374682946, 22925253518007781603752827692693975896590127938, 2928712330768194127084839835472144625729577947970, 
    72709779231169, 83713619669441, 72722456514752, 91366196720943522954298776217293308340905972546, 72722456514752, 91388541107355611187798251113377374225194554178, 
    17127015955035078516109412005043323733551354690, 11440325928725681894328383885796911526022499139, 143086979125697, 283816011764161, 424562224280001, 123665204429260709806041275404950103065106839006371825385887742384525504741431190098856672538069473033701390782185833154404304975798942197773725826176420164092253956925814854, 
    182711399383615229120058316389949143136392502850, 143086979125697, 33316191787932682377736156598914966886223234806159449376287367214012985907029481669818082140308120452, 33219377757385355898276676558133420927633009508555753967628598589638704107931478782362227714807309188, 33316952107536777270252622523404637640295426669632118437616922537135571102989902273999706339065734020, 11596605965191786516834128977657726817316916035, 
    308705900893120, 313240719463360, 299634376315840, 299634376315840, 14272531372904220926604199939954193483414129475, 308705229804480, 
    132875514200551213644534943466699757943913113481531885460569004211995459697284908673494695994392100036, 424561955836353, 567502705791680, 568052530811584, 567503173456576, 265751030381101160251914683300529874584537523200926801998866621618494077194568517710875160529360864132, 
    265751030381101160251914683300529874584537523200926801998866621618494057942125098465582083880917615492, 567502705791680, 562967687992000, 581109361414848, 567502705791680, 568052530811584, 
    567503173456576, 567503173456576, 585644716856000, 581109629850304, 581109629850304, 265751026421103222257673731594671456316706378116872244712286550381837024397207851725655527060393116548, 
    2923092521540375294034049636274836970428673561410, 2923181724861451783447554242611302171306465694530, 567503173456576]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [3957286427485527111966371202728695842583085996584535613842205048532931637559024792454676594885102530300326874915430557200564843686240101516439781353523324332893815637085747782, 3957286427485527111966371202728695842583085996584535613822031221059764213607287271275062586856623376003749114044050296952064157115542802480544484574112730521911805733804930630, 143078384996544, 2928723418528173262410614767758102531130679937859, 72709779231168, 283816011764160, 
    1978643215499139501476759980673466366837641082419677032799321887716186797528880044286962371098750802617672973149194224654242296885267189409649612888270026505836691182839626310, 3957286427485527111966371202728695842583085893995756930222147094929657700017230586965463770213679233447073219249255551686190996045575467353576994022483000614697262923756041798, 3957317558990021722707811217621617241899455792712998545897505020871721015964960858576339838852076527262401400707611589775995748003734029386733327720270461186289006376101305927, 960962154094212046835217857624440951107806712262279983817202051032305909028505607052679838320672778845095049841217856243603849385796115252505321835475675341065510428351930151868775859847687494995239146840468358833571914579672284591186471487166100603412676648499877512, 72709779231168, 3957316621027682531930283469287840356503070084155185420312377571513895226036658818375155384434455899024341213408320040503500599653478164790654640209284022677149014617009125958, 
    2923049270119604375078001797464796007911740460867, 79306641379520, 79306848997824, 79306848997824, 79306641379520, 514441938550696451800852168418246012599396848631606762116069806470162270161030665220851666174386518037494121215601151110054705649698322250288304769884726851702264956935751, 
    290546493952448, 88119914270912, 12845278236346304838727439830892752979621843778, 88669879800768, 88119914270912, 24263303334136949767317050898456479735524365122, 
    3958026120435310950272415561010871165701690878757941519967916877189444258053882503978388137504624738121278944312605649603582967744044951823376025522949129092294366903131929158, 88119914270912, 88670223733440, 88669879800768, 88119914270912, 25690556471360780462618914796164031373742445378, 
    159322110694336, 158488727654592, 88119914270912, 18159659651264]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105707805348032, 105707804430528, 105707804364992, 105707804823744, 105776595210432, 73272422044608, 
    73272422044608, 82068515066816, 82068515066816, 74921966310080, 11596442630350136825651665657191679416980280130, 11817588341826699396317970302767653210963611185882153913679623398069348454260600086407679955076200607055172234813416090469942163514607148194469584070212729216199194471796902614094712559184434442907052108560256553156335531171279495733257947037267578810315720170704498550129829246266356694315627194877171084467243774900256282420269831830637242682201863956353048171561043439032599627, 
    6596795743491659889631815078102655738080388990084945831753243356064616085725985103364067106020480594810109411248505434439745044689794157093613045258291454219767847759437069895, 246514016391360, 35201686311104, 298361598154858736684295120604870072349307936449131751858627461007079088732740502906317379879879888711330173385244450807635832977117684099223670630280757754250776880337972907316085918690168510587958430036424219260630063836584622505922751127928268616068346952423884660211181299848609159232522639518980301752827428956001296497052406254184636265975316711226252564236469306829255572711615899420096341184058316154500991477791545604653990627996407388106094908752221775435062753130553296249380834916915530614541, 105707805348032, 28545062745847383921205328770120322997484000066, 
    105707804364992, 583925458845267980551799711377795049308086085399811146184188763902463013035507390191242477029310596, 513258889784516564910739244558081963448196690018413810497298718240619332172135219707525983134099381484601228388249135010864460401227756949204629923085059900752906531338822, 74921966310080, 22858351027221183810286674820463767038235513666, 22925253518028550870415129517472435475450958658, 
    513258889784516564910739244558081963448196690018413810497299018854069927222787933213759285040973409213848777201703119696256594189236808721957711886443809275952048107387462, 105707804364992, 246514083500224, 105707804364992, 246514083500224, 105707804364992, 
    105707804364992, 105707804430528, 105707804430528, 105707804823744, 176076617814208, 176076618731712, 
    45694401223467090200652287561921186431619832642, 45716702053736212554030861729266570815917268802, 145290293153984, 163432654443200, 143091269898432, 163432654443200, 
    163432654443200, 176145272344768, 176145272213696, 176145272213696, 176145272279232, 176145272344768, 
    105707804364992, 105707804364992, 105707804364992, 123665204423862013091695744586263243078332998781788532443937729108824167316601303465923524800550402188448545940316143953459162024929319252363569025041935812941769520032210502, 365399103960235674681222881499668458386685446979, 365399103960235674681222881499677324848451832643, 
    365399103960235674686174641656810120224307170115, 365399103960235674681222881499668458386685446979, 284378453251008, 1247795335031679740211755820867567658480886057824150441860710899214638449120397363202936635480417289862134534403552837248809046347695392550364377704510455658777022910025458327001828441433619029094462221121046663863178117212697780503612852906363162027865749447185893232181234711149417156371019058369127380014563219816169835246338221773071851770013178070100935094841209540479578801845469055278170666470026535639666769606307313186295931187813300891875706458355720550685865900643364477785742973453778608734068891533, 123665204429260709645147580245635889287654958915624612548026939817015984744549619529060323945780795294368614152585940953452286067509007634933849711662548787237835425391278662, 15015033664604734385304171617226701436605314496455237494291795681606021681079827736075617074811617342380978787129425599223626254634291809215979749825612586198191405910132609334920639918923026833078032612311753068285899564227583555518907634320631966795309609248877512, 
    123665204429260709645147580245635889287654958915624611256901998368654085156184808168726255668631932398534921866647624125484334249239569044458419361319126873244571446596827718, 284378721686464, 284241213526976, 365421404790504797034599033083784758606133480259, 365421404790504797039550793240926420443755203395, 365466180675615229776067913288732542660198288195, 
    299634644751296, 308705229804480, 299634913186752, 299634913186752, 15015033881354251346468457975036149315255745592249626807130963813530430696979169062042352290376891651855992138139960607797816754048365006110807534918824188602283939297982743186520619222551560803989415138683059648793330372839059494246350461168582697859162664249877512, 286852440396736, 
    286853245703104, 286852440396736, 286853245703104, 286578229384128, 286853245703104, 365555383996691719189572519625197743537990421315, 
    308705900893120, 313240719463360, 308705900893120, 308705900893120, 365733616414272509981865155261421828173995199299, 366090429698578467635883580607282631685163731779, 
    284378453251008, 284241213526976, 284378453251008, 284241213526976, 304169662550976, 299634376315840, 
    299634644751296, 286577476506560, 286440236782528, 286577960948672, 299634376315840, 293174546273216, 
    282042190271424, 282042190271424, 293174546273216, 290838283293632, 365555230955401810099649026171064542342724801346, 308430469338048, 
    132875514200551213644534943520367738736129365738126414663182246494013883153221939729806370531322576068, 736462597711360620395576480229845721093811213122, 567502705791680, 567503173456576, 1978674347003634112218199995566338988832912183588640546304204714223072158528591288348600150942804823285205454608948385692021558914042724342302296695287698348270132987078598215, 567503173456576, 
    567502705791680, 562967687992000, 567502705791680, 568052530811584, 567503173456576, 567503173456576, 
    585644716856000, 581109629850304, 572588691559360, 562967687992000, 581109629850304, 145290293153984, 
    567503173456576, 480481772431995833936977635595058420856696696400866965468298777672980886608954939286177861865716603764065919412666578866712239511616264433690789175962263888360271958298313807903937871472519636324421802757500467319309247657133922918915014276817907262934778128249877513]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [3957286427485527111966371202728695842583085996583901000112159022001775974898460997604587533080905206625930433367066715127016441011480512660979073945684687739754042164644903494, 1152442948129729, 3957286427485527111966371202728695842583085996583901000112157175032735518907247923067545258732264969682596322764855773509150852414470878293151875831008069909979482069814704710, 1134850761429953, 1134850761429953, 960962964310898367382301938902646276349377519627757552540401868042180777248320108221814391545751077208583700358376607925680190956995426044781419772607336861244773452362120906079825087230313950277939574083510665485239321678311851662533963370221740755077071120249877513, 
    1134850896040897, 1134850895647681, 1134850895647681, 1134850896040897, 1134850896040897, 33218933866359174949877372674399432634343736118208805752558438466148870432097754168208672471810208644, 
    132875514200551213644534943439865769747021837150540490529241855995902909421377311899824289493453683908, 3957340527089466535057134519817468916524261375970515950134004926747441005182718644414907784517257780201416706539228155132037153921864302748267186490590877833918660618848533063, 1130452714918849, 1130452714918849, 960962964321386247235056381253461827797765469288975759184695917556199717483712209159929176243987798912963861102689240340834509557865411060012965750565810170580705988224201767023743208786965891718628590235860800374090717664754998099038585219708253339734016273248877513, 1134850895647681, 
    1134850895647681, 3957286428406904657088817821929855003232605641917737774910070203597475306224504309091224925363371038781774563297741287984482810289903783603596214615033682603648042760495128134, 1241673269674354631661583483792702917289146103012755030367832985387752201327204752918835362528563757907210425608592592790103110853033084887175018453424497656007029091400457806870824125194495438299988959454030269490762957354299259888975240211171759249964284622710569864538255181224080183887443805768230234775118116738160853513739710455801204382695722340659648888723948399421218584685000896543425592192571469935813288648164633444323570616243674690737989273380965143163662802215723502888879936906095029755406768012, 3957286429328282202264895672847662803729832874854110013482035372848509214884458285388636460367108075432957274687753981981107703383041123799075718430646429193888531466623613510, 960962154094212046835217062735177693144831915984781891015893758922530030516304011605573163101835244119791208582505006540332078075036196470796044316184263873682906512662854818610038689061627980858081891117625138773977020151598218412423474866834884418991063313248877513, 1128253893530561, 
    1128253825881025, 1128253893399489, 3957286482768179822531042257984468785437039667493644440214733377798282814588238147466117280930717378191047784854173491835470213605103452774862588813963687423373277315242883654, 3957343033236389474055868572116567475524140360006627866971631389379461384180206809195567571292430416306795982450679946727658914255349388708438342068342248992199867289344899655, 3957286482768179822531042257984468785437039667493644440214733377798282814588238147466117280930717378191047784854173491835506131834717906398973740058368265019020813137214405190, 3957286482768179822531042257984468785437039667493644440214733377798282814588238147466117280930717378191047784854173491835476199915810308602359298429196743426604841817939606086, 
    286582255915968, 6707465440524460278504407947217064193565144913477838832915923365910817711847894720380013894508772549479915123592700578131793860462899094996569086035081738717069754626849807139254440754856174056036313147392194427917604408015820700038723698772176938183423000590416155528955556028127344471024411647666569556409815325901569525771748674633810453723711153192003589989990828965322048075, 960962964310898367382301938902646241647893995021180950029750172500901218725489372880962134428916139248126030067792362797595051915879036857279433143428568194875282366180451328521659386190575544001032300795803106026018605267548561435575265359980058570238492944249877513, 960962612589359618611493873711274145089832674245279469494933829144313762538157790426175286328577647597616455987094026122544183819627912398403626389920584027534901302846443928060476125249635346995081937603713257243127698082344406966011729581585923919436611856249877513, 6707465440524460278504407947217064193565144913477838832915923365910817711847894720380013894508772549479915123592700578131793860462899094996569086035081738717069754626849807139254440754856174056036313147392194427917604408015820700038723698772176938183423000590416155528955952790675652261050169366582329041789253715337798463430778112833064329461715597791079275406787705975886594635, 960962964310898367382301938902646241647893995021180950029750172500901218725489372880962134428916139248126030067792362797595051915879036857279433143428568194875282366180451328521659386190575651837527960308239052974785620169415793905178556317768587051333091600249877513, 
    164355756867840629297624517120193371162607798818869224158203524522212048504272454274402124986489797, 15473349476422865172402064722852595413522650061700783273762056920914168010606341532069811101509294610002856285470389469507354421276177828288180275908732720509594985364036532586737861874522811763186133937219549473896983202595344558004504307053618146607376249877513, 286582255915968, 286582255915968, 567503173456576, 708794716787392, 
    567503173456576, 567503173456576, 960962620364374549603910442865360528676463723758862272072103780586770449121558082299511922264467487830030034724064617938087423281031413882176754860693894483846499540468134593781750054962789161126622627130265504658138267133647055095054090169497160342023733520249877513, 290555083887040, 7744170896184572928367605492308398962918322100044047392462223627950619324256281460698045561057973222631771548675776970105160303446211040320174464033006040736141232069114438, 7744170895847154393776865763597799111252415208201536270500323368881330808072369953608466525815805349562628431779790050464863029844248802643403308008742721507211093630483014, 
    158755158233536, 14892230037610365927376964827022806198444545536537706258966878375343996092944422490223168176748225220020785526260571049830094962057719048816409562930418283300566774607447811980130789862987282209044813119253013551559040316192556249112750570399869391864840749871112, 469686358631619202126767564541658546003566768368157574066152597399496376710451263232788417363529609707118410171656917531924986728451347071504887149950995651710994469416465168305238738050344702897700148977332629094962440079502422184589726997394624635502864249877513, 961549145396301712888233932915903532238216493621725906621316756328618737719485750390829676222672359549440302807698076025655867830242294996651479446297983230112471907445835401336144371525546338198993420017333825986585444205056903135984877987795219263799722256249877513]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 103) (cur' := ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩) (prev' := [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_5_0
  · exact tv_b11_5_1
  · exact tv_b11_5_2
  · exact tv_b11_5_3
  · exact tv_b11_5_4
  · exact tv_b11_5_5
  · exact tv_b11_5_6
  · exact tv_b11_5_7
  · exact tv_b11_5_8
  · exact tv_b11_5_9
  · exact tv_b11_5_10
  · exact tv_b11_5_11
  · exact tv_b11_5_12
  · exact tv_b11_5_13
  · exact tv_b11_5_14
  · exact tv_b11_5_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161224003915968, 1134704867147841, 316668216082497, 1161226152317120, 1161226152317120, 176076618731712, 
    286027789898688, 145290293153984, 145290293153984, 145277408252096, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 721438697853632, 567489873318080, 567489873318080, 567489873318080, 
    176076617814208, 176076617814208, 75815711701953, 79251551291457, 79251551291457, 88047375878209, 
    75815711701953, 79251551291457, 79251551291457, 88047375878209, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 1161223934644416, 1130448420344257, 1161223934644416, 176063737500097, 
    105707804364992, 324403033980877376724792265494057886010407732018087535292715172116177671346562732714989721940666500, 105707804364992, 565304150201024, 565304150201024, 563105126945472, 
    567503173456576, 580697312989888, 580697312989888, 580697312989888, 105707804364992, 105707875733696, 
    105707804364992, 513258889805605223322660477602494454131821906417436425401954131678589188043617615869024416369775915524836131041587477539724146942973341322231844948095281765125775685548614, 105707804364992, 150958497008678147900342096783323651760374258554442482869308600899621325748552629907475280140323260605753139019145061334051369936521687823288664909265913570772532619226694, 513258889784516564910739244558081963402702725677279480281182334527220246357053258615938065774926797822529802323224436913058772031776564043128562108981036355347293772151366, 105707804364992, 
    563105126945472, 565304150201024, 565304150201024, 563105126945472, 567503173456576, 580697312989888, 
    580697312989888, 580697312989888, 1134850761429953, 1130452714918849, 1128665941819969, 1128665941819969, 
    431159164015040, 3957318030735326623977467098143893436221372734628537056023189273985612203448364188614295704988074761134951721014452164602277256034414089925139682768283701111557228183337008710, 531501997402235371604541297741964151506216033423070360103893110266016177980798396564002092520869982277, 580697052943296, 1128665941819969, 1128665941819969, 
    1128665941819969, 1161234884202944, 1161234883940800, 1139244651778496, 2928712330767010603405032701554041134169840681795, 105624529012801, 
    105624529012801, 176061992669633, 1161234884202944, 1161234884202944, 457547442557376, 2928712374323320047938246037930230725566697834307, 
    316937188417857, 105624529012801, 105624529012801, 176061992669633, 105639091177537, 143087117537728, 
    143087117537728, 145286140793280, 565716458684993, 565716458684993, 426761117503936, 431159164015040, 
    2926582546989799708388883299025645080215080227650, 2923906457565976033611899012832927276834362577730, 426765412471744, 105639091177537, 105639091177537, 105639091177537, 
    426761117503936, 426761117503936, 456741910946662225458538074884174806672027439938, 431159164015040, 565716458684993, 565716458684993, 
    426761117503936, 426761117503936, 431159164015040, 431159164015040, 1130440241976000, 145277823488704, 
    145277823488704, 567503173456576, 567503173456576, 531502187482143476356237171037180367409888194274759943660699032364826606309462253195201734780861944132, 145295007552192, 708244960973504, 
    708244960973504, 567503173456576, 567503173456576, 145277823488704, 145277823488704, 162887193596608, 
    162887193596608, 580697312989888, 580697312989888, 149693054063552, 571901219967936, 162887193596608, 
    580697312989888, 162887193596608, 580697312989888, 88064621873217, 1591594326637577600647941483606635186317604045925679886301118391049474428870400935549834564511388548476471017792702479516761007046092988263064621488110822964193771877505840627966285309198677474975277954962986907567267359818174444355674349064145188908657819656246197512, 1591594326637577600631662151495112104592011274040546679571523390270932411359645637650370532973769069291060295925456982066739779604126980148806151653729421148863442381691393164912185698939335874002224392442206515330754037232651716908419367728835335144867905544246197512, 
    1591594326637577600631662151495112104592011274040546679571523390270932411359645637650370532973769069291060295925456982066739779604126980148806151653729421148863442381691393164912185698939335874002224392442206515330754037232651716908419367728835335144867905544246197512, 88614378228289, 88064621873217, 88064621873217, 88614378162753, 158489281303232, 
    294824566592448, 563534614774337, 581126800818753, 72670922213441, 283777154746433, 283777154746433, 
    72670922213441, 72670922213441, 72670922213441, 283777154746433, 123685552124668716964593401259976672143884867360692665728364351358132232992228045026131486171641770218893403051252267765652686889450805906844254441444425492297947509178710086, 283777154746433, 
    72670922213441, 531502187482137811533747440811209723809112975222517406794007534883014172457120404713992090352425243716, 531502187482137811533747440811209722209682545506305133819377489437269481613901143318152438129328002116, 567503173456576, 567503173456576, 708244960973504, 
    567507468423872, 571901219967936, 571901219967936, 158488727654592, 532215620711611644107079985924085209306506344382539751160664147184823426042957778928780812297015829380, 3958161982852239929516173254380978619403138834309758787311036041731953396395882442808937794839305503546873831886611898929396335836668657856524391753623316717829471453526850118, 
    316934772236609, 316943362171201, 290417238085824, 435552772952256, 290417238085824, 72671391975489, 
    72671391975489, 735038153264170279741148017101846260697687757378, 563534614774337, 581126800818753]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161155215167680, 1161155416494272, 1161155215167680, 97052951994695319398814934404883112480695392066, 105624522264768, 317005641093568, 
    105624522264768, 15015491880075510186898946866980240133138633850871926095099288191923415731983681695637612608616657831272039420191083181679602521812897554533972715096279627719302863274910334528551209802459606660012359524989608972905859821883166561837654602186681055612764168245997512, 3957316615499469982613701026949970134706107163677637049482056031673668179493822684662937313670739005730673944106189473697454408072584700007541359263651444110953419189037215302, 1161292658380992, 4217239466888111472081033948911911090723115095701422148294400255968512562053252437724562309733696388, 869984056672615977916084678938091954347359896361437496532782265934476080496272031877953766540456510340, 
    338482122661285688195662983179639853183876869822911406399565008553369461268663805669337954144093488004, 736460179664830126306997170297233696473661592387, 1161292658446528, 4217239466888111472083012365311614297905860015578807091210244425301422783690334930106508750272873348, 869984056672615977916084678938091954347359896361437496532782265934476111856697846727155354866481906564, 869984048783557585818182782961577136704415037014297558188423530267698427841433019237457917450593256324, 
    736460179664830126306997170297233977949712044867, 2928712330767010603405032701554040008746677064514, 105624528753088, 387374385467840, 531566878008451233214018804595757111584413080691598135607677833726825052702266985334622990065847255940, 519551737206768539845371963960358868861511854413975519386190453845460028174387355613251880255077572, 
    583925463686802920756302398407720731955998245297226165024213550582766202937391601720926326509911236, 523099895412083056702840543082620617654604548860040302178486015590414799433155049629228491729542340, 1134842306105793, 1128247450948545, 1130448420344257, 1139244781810113, 
    1139244647584193, 519108211629617864126928102893067682170168214688142375658358707034396340051667011478302552002872196, 583988817845715522282548277057316118034242066726001551816895432248113847622710215999529601363035012, 584432337618311376975107105251316735604525171917081014993297262500517205061115854733005836317574020, 616365761228219484123654826578024136089869414397355209731563686758358176944482015259143044381229956, 797771997395037670914329805378565143967467438717830736752006091371049693027090085808764992451671180164, 
    1134842306105793, 1161155215167680, 1161155416494272, 1161155215167680, 97052951994695643918606532870895275911615092546, 105624522264768, 
    7759266745547319253286405420057648018064745132688693403369457741039117005247691238538972162655508311768991198030199349566474206610201077150443885937990064658116026988198470, 317005641093568, 105624522264768, 3958161982852239929516173254380978619403184182708940979088042399895683726564489886850217773548526528601798354751521522725675108156164356545373052867311579859901346078068275782, 537795352846196041671505821657877172492377355633971245512669409794201748010818051808117631629679180421, 1161292658380992, 
    537795352846196041671505821657667532046277022203406536563453042373247388385426969689363383839442909829, 2141060021566760805619958339863162448647961151603781882358819279201296727536136810457312274011428037, 548111488095409560198014945598504422642712341342042183063808410423041622354137148464903497186088996677, 531502052904088552333204831556982386178563819770374328137867514341477674637004020465542227209570635589, 483126158547075540575865916427061310057260709485834365906897126517371747867208475420517810347536851250177418892427732153096886690730229984434868890004742606578233391406662, 188398111017150352190319398145544176944581464642, 
    188398111017150352190358084509641608026554126914, 16609561973137537182290751526316306357249402635669633828242213621854882748109377371988426733597904709, 17127037648015850766510413492928138475756066626, 176063737500097, 457547572588993, 457547438363073, 
    316805655040449, 1161292658380992, 1161296953413824, 188397414124184667727311679710653564572529603394, 1134835863654849, 1128238861013953, 
    2928713681008605949141658853330486082307734132547, 537795352846196041671505821419725513050022113918006256636331319153897868567532409491733362410583538309, 6935395655930469910398077417638322420772058911600190443821750500073242595414486298536113088858973347865251676513714855550417875589189410695042657330869046231556095516885352006, 17127037646852466605837501641345280452558082626, 90575098211533486263658875835525405512541319067890695926653018156550426850861679026810345565233135285358199719712218660637232426639224126765015218074364636911909553352263, 513259132768038800474175964706704692215687323335298469485210754465879468935606785420924542234847811458899275547115097480239174019740302872273230198262040296895811759156807, 
    532345381924043839394585483492734856052147205937440450685197304721294747070572883139296921764510087813, 371085815683523277197194658829025044817323774786, 30946492127316258178995131472793951164346851918616230180733066051849813369939930762591126683372422025110814904606259131431850798792250838734279696914960171927875273599921735, 1161226082193600, 1161226082193600, 106107236782272, 
    1134833716171201, 1128258188366785, 1134833716171201, 1134833716171201, 106107236782272, 316797065105857, 
    316797065105857, 106107236782272, 106107236782272, 145277823488704, 145277823488704, 145277823488704, 
    162870009533120, 283815873351872, 143078800233152, 158471963022016, 158471963022016, 1161226082193600, 
    106107236782272, 106107236782272, 1134838011138497, 1128258188366785, 1134838011138497, 106107236782272, 
    106107236782272, 106107236782272, 140879776977600, 140879776977600, 145277823488704, 145277823488704, 
    158471963022016, 162870009533120, 563504558904000, 563504558904000, 581096744948416, 143078800233152, 
    149675870000064, 158471963022016, 1161299100831936, 1134846601073089, 2923059026696273228925333169803710908365287774019, 17127037648025586360258367473293041403347081026, 
    324403033980877376724785785085323545110961549440855704299366436025978546393480695531479105150401732, 537795352846196041671505821660602499680249709454013166493886347446902241577876489088454820390944946821, 833535301821033078197094502345517333207618458434, 290279929155776, 290279929155776, 290279929155776, 
    159026152215232, 105905851208128, 513258889805605223322660477602494454160133474203318410536949208382254794632262244623805168739871730798989614250025695078792301778777783926248329251854758587650674129862214, 583925464646046181219545853813918507147474569568530087588209965726488176576428642043216195018078853, 563508853871296, 290279660720320, 
    105776662253760, 105639084888256, 105639286214848, 105639084888256, 105707804430528, 105707804430528, 
    291962730389430358255065549124031663228198513391666585210269762670011608764689567846058101418769604, 583925458845267951735947601712544179192701984263859588437597962168765231393740139538404500113212292, 324403033980877376726543988373962108531692698033287685333191247561185241818254673125086616503991492, 105639084888256, 105639286214848, 105639084888256, 
    105707804430528, 105707804430528, 513258889805605223322660477602506362659528382209838204432578318469912044314247578986744369859336859764078554732393325677877245362109370427546690416596173326736047174842438, 513258889805605223322660477602506362728372384382655120168340072357821676781195023537628929459970438611007642802737029571496279562130169495327505499692029694511278716876870, 106120323010752, 106120121684160, 
    105707804430528, 106120121684160, 51381112941740212778304580556473372804732950338, 176145272279232, 176145272344768, 4217239466888111472081253880099224491962888354275469193042410039182227694763087095839838833444406148, 
    4217239466888111472081034056038230129802841229091888451979691008022887473209959728082473090029994884, 531501957804189230382695363707091504638436981970408045837009817090119485326478668119180513805175372996, 708790421820096, 188398111013183097736753796800123847113340621378, 188398111011853864670441428978660688019264115266, 299084620501952, 
    833535301821043462830425653257906562997048873794, 565716467061440, 565716198625984, 565716467061440, 565716467061440, 565716198625984, 
    565716467061440, 563517443805888, 567915490316992, 567915221881536, 567915490316992, 581109629850304, 
    581109361414848, 581109629850304, 563517443805888, 581109629850304, 581109361414848, 581109629850304, 
    581109629850304, 581109629850304, 1134850895647681, 1134850896040897, 143078384996544, 143645740110528, 
    870568038588502396666659898542722388349060930763277150772642055257861313429839524216260137793380795268, 143645740110528, 1134850895647681, 143078384996544, 1128253825881025, 1128253893399489, 
    498163040083692684825827049565582885655953330916193946101899920490904830069334416145458734400311057629101003683079601067162841362053651796356284287895985654190700022947398, 159038902899392, 159039037117120, 158488727654592, 299359766844352, 105639084888256, 
    105639286214848, 105639084888256, 105707875733696, 105707804430528, 105707804430528, 513258889805605223322660477602494454133516007600563610155242053940535953614464459835875004739229979226393827836450129699057630616683851383337703256382498641456577606811206, 
    105776662384832, 105639084888256, 105639084888256, 105639084888256, 105639286214848, 105639084888256, 
    484010680990405960825093326566560644588228667926695128786694218193218071290817090404580864935830656744855649046492173522340431926973620020400479665830377840858790405037638, 513258889784516564910739244558070054945096271426815236933093297158619012129480773659182405687098127426031234147168046107910986637920701112802245304515891852389946268540486, 583925464646046181219545844170453424094357176034536339325071427934404704660406257081414283568396933, 176076617814208, 3957769494675932387296373331950072729104347818216540865706960547824497319576178570660356181419647957040451631021624930102353447798972899406375847214833708456051224114634907206, 105639084888256, 
    105639286214848, 105639084888256, 105707804430528, 28545062765785879917034395110138928214730348354, 105707804430528, 150958497008678147900342096783323651766030504731438431058007711295363176669167158252246475347853331940020225887278227679140489338167535114433751832751559823489865006558790, 
    513258889784516564910739244558081963442372697326242275744056435399474695206276432053100221528678347866002801369829871187394638309894583038823188293100336519314966681975366, 106120323010752, 106120121684160, 105639084888256, 28545672530851981443160682100743757219959412546, 105639084888256, 
    105707804430528, 106120121684160, 246514016456896, 246514016522432, 176145272279232, 4090643159813280760437425141056665775805359973477781171211225668032900472958380302676410270947520362390172515357697958342549161616283769246413904190057240936252636239964926535, 
    163432654443200, 145840468398784, 163432654443200, 163432654443200, 163432654443200, 246514016456896, 
    188398111013183097815981959314676415083036283458, 188398111011853864749708277267019380329034027586, 290563942257600, 16609561973137537182290751526316306357249402635669633828242213621854901398914293888016219049585692485, 2077193653402100029587205108054967324915818600624529664368124952569032082271038316973793253553265093, 563517443805888, 
    563517175370432, 563516906934976, 563517443805888, 563517443805888, 563516906934976, 563517443805888, 
    565716467061440, 565716198625984, 565716467061440, 565716467061440, 565716198625984, 565716467061440, 
    563517443805888, 563517443805888, 563517443805888, 567915490316992, 567915221881536, 567915490316992, 
    581109629850304, 581109361414848, 581109629850304, 563517443805888, 563517175370432, 563517443805888, 
    563517443805888, 581109629850304, 581109361414848, 581109629850304, 145290293153984, 1134850761429953, 
    531621557660250733138761542221330899994272767628772113165815378618315257282236965432384884275431187141, 1152443081954241, 1134850895647681, 1134850896040897, 519108211629617864128245490578488554047386157558718454404317703956745085092249700551172199989658500, 3958011028271135025048524738931952261246208698685396720862443343978236992350333947859521507303500771111089321898802123573721585276353981078822973629010044633122973801156402758, 
    1130452714918849, 1139249076646849, 1139248942420929, 1134850895647681, 1128253825881025, 1128253893399489, 
    1143646988669889, 145840468398784, 1130452849136577, 145840468398784, 708794716787392, 2923728070660200336199320681031687754952082543427]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161368023863744, 105624529012801, 183402028136003777047981896509819979927025365826, 960962161246946106552188634526707087480201830394741335189666882919984826144676576187843769675172808086375302592761204555625208029251098511684736373482917607757814436030842851127672670479768043601644481013914425904036317836267272807364644896802039305907225736246156552, 580835028767680, 589631121789888, 
    1128184905009217, 531501965722252339719151417920491632846355695692230610666282065409489895151537623558253888890803244869, 132875517170550389995170533287665926974926292182759735332294667494323924454595001720561174665300987717, 290547030823360, 708378247566272, 580835028767680, 
    299359498408896, 589631121789888, 290563673822144, 3957316619184925684297189135165343748734441777755736966890242703393197053613353795175308343941530529861781529862284377213928076087438296444621909332206400175416978829932977734, 286156768940480]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161292792533184, 2923036725949911298892420738389280604927333241410, 2923192831677887638132147941884609362220789273410, 2928723437583466907273104775285591114700208214594, 1161292654121152, 17127081202995416362877276380294988442334401090, 
    97053213332550039479209989994115152010427765570, 1161224003915968, 2923059026696937518009773799981289903537227045698, 1134979745063233, 2923371239680007010146582249151779078144723522114, 2928723437584629981769433534747762163269922460482, 
    2928715058480931516551339288382584126063012516674, 23014456840475811566738462659409634732848194371, 28545062745806169907672325878547489632074863426, 730778694767257288931108104308465983466883781186, 1461685619160685087272677725241068527100501168962, 531502187482143476377818619855298188867150774844081443105714296981722962051134229590665350278342648260, 
    531501949882260587742187610640932542974807645288718787159258359276071519261369751487658703919732362628, 531501949882260587754793200643663733273399277000704587559796742886554155369913756405635147438314098052, 2923103628706398111610211875375280288138142978626, 129777060159262446238422811503203643686845212634435217573208488514032403018124995332322383748533636, 91522640114182568184866291352428233366660256578, 129777060641716494936562169218017892090865933014533700821321902706178511329047346603174009498111364, 
    94377123929994012635075105536590570959306560322, 1464361729701953931084911194244059196936981386050, 259775872474346340734494496237376779717631190860734371120257524878508783488642358406593784689861060, 94377113721523005006921201635352348006260216642, 316934772236609, 316934772236609, 
    28545062745806169907672325878538763907796833090, 176205873820097, 316934772236609, 66437760565274650815391970859409088130775720314414130179415934863934938011945396206652517079549873540, 730845597523744101648899242963889249931787014722, 1464361729701953931084911196605242438371803992898, 
    1161296953413824, 1161296953413824, 1681702556773223372025779039082047975160891038391612539042977033474208837775768404569079043122394797140100850237884485115007088798029396053440397282844026728005092939700238775149552865029692773741342790309519539634287720156753355236124608569645971325973430280749871112, 1128376031535937, 1134973369738049, 6431345230814476999516792228354305107893828394351460477494440924272788223775181000467206029647981534065693543146551775458373198927337946106100545352832610670018958943177374278, 
    2923059037416497019607617152897935878572501706563, 1161576335872448, 1161368023863744, 2928712984111652271403116614317328186112663892802, 8369598326593329836429401746227057171012358197331121174813435619547218916551656552280963885625774981, 28545062748464960577589134621688073079947801410, 
    176347343753664, 316943093993920, 8369598326593387000979265560356319812834796094080823273449055556265727436259350854334548610697401221, 72845070704961, 143213814882625, 143213814882625, 
    6707465088747716097056592057044847211785017742511363564315519141123414899959941057390130493328243102964908091651434380531121473832008755752266682471855329528294623338969207376676567722482149883978252615812633742401017742158586657966035919839614596562391384827985797553688806415923171511683537619667224846833007263532878588042335272994681903924500581950006321056147405837244095050, 3957286482768179819956743135435490142320314616111810030344696593651721324007809315540422430692700720171346622425879243595339621018403319253173131398773377016631096842787977798, 3957287367290623150376993181293177581232188345792858320693918860941725795956629121518203157172498055509568363915677147395409831345692808024650841696544613686074759980469156422, 531501997402235843673078394370202012189031973137347305445790812637943366126795403318989555866873905284, 259538272650938341294947767169113093325635067094950858434229167130748701232626785480151989349058437, 551485156945714612346251258390801551517872774763147615065613975798769071263536993816534233129466948, 
    290548373004609, 290548373004609, 299344466026817, 1130581832774081, 1161294801604800, 1161294805864640, 
    1161294805930176, 1161294805864640, 1161569692291520, 1161294805930176, 1161569692291520, 2924486279832833090386478609973687294596365721154, 
    2923036725950410729147263372871971432190185610818, 531566814649450785643489625298385510092493004557859318314847116133985937659079788171675280056686913092, 2923103628356147504477157211758476680990587657794, 2923371238319376972717671030767872283623964065346, 2923103628186006321016687980026789377274703552066, 2923371239680506440401424884621370713351036919362, 
    2924441672897918158405180123123148278965062377026, 316934504063297, 2928712417879795969856746367469438327126602292802, 35459527352641, 176205739864513, 35459527352641, 
    316934504063297, 316934504063297, 316934504063297, 2923036725950410729147263372871971432198775545410, 2923103628356147504477157211758476680999177592386, 2923103629036712238319034138685225895862714015298, 
    2923103628696429871398095675221851288430945800770, 2923371238319376972717671030767872283632553999938, 2923103628186006321016687980026789377283293486658, 2923371239680506440401424884621370713359626853954, 2924441672897918158405180123123148278973652311618, 35459527352641, 
    176205739864513, 316934504063297, 35459527352641, 316934504063297, 1161226152317120, 25690556491297937666025632576929645307138938690, 
    72842923221313, 75041946476865, 72709640818880, 25690556491297978230709440779922386597386917698, 159021857247936, 581096744948416, 
    129777060159262431828520058003339599079716807593464332396309333901886560264650857385104672713991812, 11507272315958460350008018996701151615235658306, 129777060159262446248977371395605286642688353112934656672920049199098304328599725770586055247521412, 194641826383608102212024793110882656818963601612769409429189227582998744384142499139474125701637764, 11507283630347160471211929153906848721528689218, 25690556491297978230999582976629897599316399938, 
    1038105554919000589888667791951627596821966661058901901685911761263313477198969711967228343820609156, 145827583496896, 129777060159380794717048560242760432046740436548996701950303643225876580664257022104909383904913028, 708777536918208, 145827583496896, 163419769541312, 
    163419769541312, 163419769541312, 159021723030208, 163419769541312, 8304733559403131920742078009139868234940234453690802694763918000986057414093462084736255486688040580, 286839958148032, 
    1038105547184658891025249418612479145866196104555366580480403233355918848421222073177121105158727300, 708777536918208, 8304733930652940451719904773955361484382386172958004604853412567636686225452994373632557678799005316, 286839958148032, 66437760565274650815391973865169739335423590548883624320103924451973039400125659378058890166498102660, 568040044368576, 
    581096744948416, 2923059026696625651954756173487696723901421721410, 2923059026696625651954741628525142509099325331266, 2923059026696625651954741628525142509099325331266, 2923059026696625651954756173469249979827712169794, 2923059026696293344955809935056291273430389494594, 
    2923059026696625651954741666304074583198153054018, 2923059026696625651954741666304074583163524880194, 2923059026696293344955809935056291273430389494594, 531501949882260587742187830062401799953215849079026943354492420063848471352652912485240046385537326852, 2923059026696293344955809935056291273464749232962, 531501965722252339719151417920478735039370464156461321356592191633207068031340928061933560489470911300, 
    531501997402235843673079044447661183416441387491179182655763862949035275717492152334841279536377952132, 531501949882260587742187830062401799953215849079026943354492502752463633403916537179603088307849056004, 2923059026696625651954741666304074653531463751490, 2923059026696293344955809935056291273429584188226, 531501949882260587742187830062401799953215849079026943354492420063848473721605920162725860327895179012, 531501965722252339719151417920478735039370464156461321356592687764898039060440100656135099337607902020, 
    531501997402235843673079044447661183416441387491179182655764359080726247348230184021737631985489315716, 531501949882260587742187830062401799953215849079026943354492998884154604132196280227457220355498860292, 531501965722252339719151417920478735039370464156461321356593349273819335169729668664692027915602604868, 531501997402235843673079044447661183416441387491179182655765020589647542855880892937599746962509645700, 531501949882260587742187830062401799953215849079026943354493660393075900542305277782361555733980749572, 531501965722252339719151417920478735039370464156461321356597318973351909353992163649554569996945994564, 
    531501965722252339719151417920478735039370464156461321356597318327347103402523049418304338700698530628, 531501997402235843673079044447661183416441387491179182655768989643175315901785146432770566555400585476, 531501949882260587742187830062401799953215849079026943354497629446603666368543222165194612115178655108, 143220257333569, 72851513155905, 260282747372651161212903225843974082412994490023174186669276392053522896870299549306040994924608708, 
    513317857966736529804287377832471779733921983965610793583895691553220819577224260712032850696214019294918817351421953638824212622538308964709791017323522917614338306963526, 11596431741293626088667823016935682239608394562, 3958041289995212968397553248671716484861253594691677304115089301813983020361837037262376002833433660089762399674472941191544870033226859961555530521021390806815172719506586182, 371085799355296981772496073061743110782600663874, 265816607946957885396184671811826340294809054067532915479131228410120589165165673209793635700632208260, 562967687992000, 
    581109361414848, 2923192831677908082879018645245677068130149471042, 2923192831677908082879018645245681501377944097602, 2923103628695950885890123742910424362979013169730, 2923103628695950885890123742919674791763912954434, 145290293153984, 
    2923192831677908082879018645245686004994751337282, 23014456839084271017257434084499408995510915906, 568053067682496, 2923103628706418556357082578734046584286084108866, 568052929270464, 324403033980877365921752557461513281167436944902601627728862438440932930168388594178696663542283460, 
    324403039781655621515434535743637919327946121335631634779571525715231721160686088874719604748476868, 28545046421577633914807599363830066590957705026, 145290293153984, 172503365325760, 163432654443200, 581109629850304, 
    2141060067007134623143062694756765395406564391272087419740371142746069136989649619497116625352856772, 145290293153984, 163432654443200, 581110166721216, 158897688088768, 88528942796992, 
    12856477618929251834571839558599497324435608130, 158896682438848, 158897689071808, 158896749547712, 33218934237609691583666909999527528259666470571293752121964644840906291035155431576218026886465845829, 72860103091009, 
    143228847268673, 283966872494913, 143228847268673, 283966872494913, 6059641067476281988648990779362422469953458162361642738353269607466412728208331322813288070593838684175276740774449068859644096840650436413781789131868716417346658210154534471, 243420576405382887722894995025380542555837810346566019446622409830614862209001595961718959348012037541247245292195640377490467590535938171327851631029449606252330921150022, 
    12845283712765775040426583168491713422881305154, 12845283712765764899220799090427536795456508482, 537762904653304503692742592672783709152845711984711478500218142677326103717006464663231926074245137092, 18160195604672, 18160195473600, 551485156945714612346274229963188378808147325411661199656862361966469036036824595332359409904172100, 
    532053411279217730194373964049058433007097683354667395092969529052948274150140109329546249059323657284, 23192863482566482911253706374503938596515390275, 23549675405742972881518277866866875332711981891, 48526606687543884775186521684641575747987708738, 159038349250752, 159038483468480, 
    538541471927897675417775580661059992163428395372310219847455409113834552558254907806689567024997483204, 18159256998080, 18159122780352, 4184799132117481470136590384804912716631711481930189956367360876904346571741896068571371550359700164, 159038483468480, 18159659651264, 
    18159122780352, 18159659651264, 18160196522176, 2924084864890064517583333434774755740380458656579, 2923192831253074353992912680416568138762947663682, 2923192831677928852145680947070455492524503995202, 
    25690545772443660675905679853973299177189283650, 94198696869611080628851069788616468078128010050, 18160195735744, 581110165934784, 2923059026696480267721928393282578873446295409474, 2923036725866024222047819687789738788734275424834, 
    2923192831677928852145680947070455598078022914882, 45761303712945224195000282668839431503492420418, 145290293153984, 145290293153984, 562967687992000, 25690546282867211056771774215820401528516122434, 
    172503365325760, 18159391215808, 581109361414848, 299634913186752, 15121578994231863346194646252285204089463426227677758856305609596208903234679795524617231418726741307072675907960417072488465158888134553069545083708504097926422958155137126532889425545865363626474029267176223340429663659510394078113872924855549789470764746156552, 145290293153984, 
    581109629850304, 308705900893120, 2924430527809705070088485477137584102265078158146, 2924430527809705070087866507117941412127628596034, 18160196522176, 130014654237596239297271792083490816575478600337087968944669845606237963766353617992215976049185988, 
    11596431741314395355330124841714141818469225282, 45761303712945224195000282668839431503492420418, 158897688088768, 18160195604672, 88528942796992, 25701619751651552236791400185509199390789605186, 
    2865656668356194139858815229552715920150893378, 158896682438848, 18159256998080, 158897689071808, 158896749547712, 18159659651264, 
    18160196522176, 25690556661479402145936510681964114706377480002, 145290293153984, 145290293153984, 163432654443200, 3957286425642772021614215500889958493038270111059487942233511113109997309326662754090791192480055088311977902091347125502893343687363171984319542315847498732215818531707989574, 
    1143784428020545, 1143784428020545, 1742525631811259563293252532985757070180870609017440473753100349909090211485386140737983987655568163549159752981794509888720854604956001332660328045783570095427394461585285902521722771703823509989993641578532218503975489948023817054345609034373986897264410632249159112, 937005778363786898938722978379335981311233725456463833803353661102298313851330862795735772423834256260, 283958550204864, 1978643215585518646329475387231881846403692219709812386182779538427882290416409009058521461858001588914181473573950452607718759217179575019923622094010585445256367644321239622, 
    538379777262849792601510077977051104322875638007368583243326261163230190074160617433042823321896633220, 16609689126190662643631579766809599731947675847607965175098664460632736644932036152107246656292137092, 708794716787392, 6708539740594511671084603868066853898227080819564986650430195350470651349754669578171551990343840485516587080521087283279889576081437127738577463365191673167933030598784695553754490951569313808828337127340833141030895651210783261598383530735482463533026862443790363351974791610946767221773335691047747944639260103648390953941422408736754069994639354493807557479750247935809477194, 3967672427131056788308956829168969871048389362912191121491771376972129532642078328703511531054371052518806375483229003824745748636840175201029117500384593989592535551172377158, 286156768940480, 
    568336141259712, 708794716787392, 708794716787392, 249081520052720181906982371079378026031147705009005921719670247154613193624829464719053026852490869063346965484915885301379680592834013734930956909125537718583456207121990, 551485161054599160949027408895524450534332997108279515471173462822045779273009807621880817717101252, 158471547785408]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1161367889514944, 1161368023863744, 1161368023863744, 1161368023863744, 1161368023863744, 64888527178777394292726084530644438057171389755550550944434849681920774757862638406422031404955140, 
    4217239466888111472080135761448141428706796460770295487278445782208685478647792114049786043235917061, 105624528554049, 51381112945374834483894122934317143330327122754, 105624528554049, 105624528554049, 4217239420481885636210233041391608226202741985955576732733150974919101614712730766578795046897938564, 
    33283751484824631724445106821371616141461259251934954545948386242870102205413946404683897570887692420, 33283751484824633568462844125612451598509071355751755472915384923368627530884029838717752451633575428, 33283751484824755273633521923436043029485874619799508328075090853890665954975543090854182612312847876, 105624528554049, 175993272736193, 105624528554049, 
    316730761095489, 1161368829039040, 1161368023863744, 1161368023863744, 1161368023863744, 371089997073237616976474383349547598989246878530, 
    2928723418532815193509639225596081491855743669058, 1134980550365632, 290555620233664, 532345381924043839394585579903696666436741286529437285192836705285848569740956579215530728817861816452, 51381112942052109256960923385871402824857836355, 97053213332550074973426909719602348724288770883, 
    589699837819074158287220465640199798039190773543901636070630101367690770513641555007310572554298814596, 290555619971520, 1461685619180623542704268012551727621345646826307, 290555619971520, 1134979610841536, 1134979745059264, 
    1134979745059264, 1134979745059264, 149818131878336, 290555620233664, 537795352846196041671505917830687323434616194510042867372680495575059477332887034895695546751011483780, 589699837819074160131238203182591064576023755411538723235102216852391869984930547171387231661943124100, 
    469678024263096156171119672210160399660265126676396637222044838783415648420899669744859334922503222302818647087075637990826647966696461733992022489632914108954509512100921495038126474550537316613863478574435581475142187299860831041717051132543877272043792749877513, 51381112942052149821780130689214502527764028227, 97053213332550115538246117022945448427194962755, 97053213332550115538246117022945448427194962755, 3894729222530060908604147091557245241200436209806034724911944401619598107810210937562331681241904347784145593110680992986492187836733271939579336136029370694009348656090695, 97053213332550115538246117022945448427194962755, 
    170376978805149628973502015288812659393637142607302973438502839047929144885401079020508016979863388677, 290555619971520, 1461685619180623583269087219855070721048553018179, 290555619971520, 290555619971520, 1161363598741952, 
    1161368023863744, 1161368023863744, 3294089090345329113525181418652120263633986933570, 371085815683523277117811753219554224322121847618, 105624528554049, 105624528554049, 
    371085815683523277197194658829025044817323774786, 371085815683523277197194658829025044817323774786, 105624528554049, 105624528554049, 105624528554049, 1161368023732672, 
    1161374271476160, 1161372188938688, 2923728051608344333965626677512354229235935630146, 531503961562178941065939689227052601091872534272466044560015968666961643318623781628624186866634227972, 387305663899969, 316936919720257, 
    2923728051608344334045009583121825049722547622722, 2923728073386415816985071244777799925355713155906, 457684747293120, 316943093993920, 316943093993920, 371085815683523277197194658829026170708640682818, 
    532345381924043839394585579880531386182885432853993773382132745751665884622510470722443980983789383812, 4217239466888111241578026998041479823527757052505514180070973955356654836631036393584111138028875908, 4217239466888111241578027001395728598050171987921906544441328393801679552990875933069063335563194500, 365555209776780933718674877191735917372977992514, 368231309409075616123813067285691943719626888002, 371085815683513561766781950086125462647656695619, 
    33218886717633724322929770282846208316897019609211577292832712416569939541302584441939165261338834436, 365376805856876505665456302569967727422375744322, 366090429703239870199702515210530500352336220994, 365376805856886890259173372225805752784144847682, 365733616418933912545684089864669696841167688514, 366090429703239870199702515210530500352336220994, 
    365733616418933912545684089864666319128562258754, 581395120223413659886868621243258330693075244354194211265808066555767430205477487702404564516085133444, 589699837819074158287220465640199798039190773543901636069275329845245723626821855781758671367752085636, 4217239466888111241578027001395728598050171987921906544441328393801679552990875933069063335563194500, 366090429703239870199702515210527122639730791234, 365733616418933912545684089864666319128562258754, 
    366090429703239870199702515210527122639730791234, 2923728051608335247372312066421852925612542417730, 1134971155124672, 1130577689318336, 565703573783105, 565703573783105, 
    290546225516992, 960962612318422722514276120579029485995887052264404733803492738012784614595180564899611510714785712260476098493168229733472560874418871043571893016023348837390089483686641979850920728111360275670343077846593966675936434955989176399802383307471012949586347016249877512, 1161368023863744, 1134979745059264, 1134979745059264, 286156768940480, 
    299351445344704, 424699667419584, 565703573783105, 572047257244608, 1461529513368741998433685863018524930873030148931, 290555083887040, 
    290555083887040, 589699837819074158287220465640199798039190773543901636070630101367690750358739775402030175611111305348, 17127037652171710163778034218543780236125033283, 565703573783105, 290554815451584, 290554815451584, 
    72709645013441, 283815877546433, 143086979125697, 290564210168768, 105639091177537, 105639560939585, 
    290547030299072, 105639091177537, 105639091177537, 105639292504129, 259538272591457719330497892307323205754262264456771438428920569731979583890393579381732155989579589, 143224422273472, 
    143224552296896, 143224552296896, 143224422273472, 143224552296896, 143224552296896, 143224552296896, 
    143242021573568, 22883352347638052929493300967077774727510525763, 145420085891520, 48526606670938856039062264002223371786284718914, 158634899149760, 158634899149760, 
    158634764932032, 286156768940480, 286156768940480, 143641432576961, 286156768940480, 567635910595008, 
    365399103964886692344315616704312860016990245698, 11440369486862507520805723326157816451106353730, 365399103964886692344315616704312860016990245698, 1461529513368760171542324862125027419277165134659, 22880651861439062988432703675872125127529354050, 365420707896870956764147862711047968171111764802, 
    365421404795155814697691768288430286136345121602, 365421404795155814697691768288430286166409892674, 565716458684993, 565716458684993, 565716190249537, 365466006455694059394540549071740703431563694914, 
    145419146367424, 145419146367424, 286156768940480, 286156768940480, 286156768940480, 286156768940480, 
    290547030823360, 2923728051608375487825870648783506772095565648706, 2925868923147434427647516106398384290313191641922, 2925868923147434427647516108464419626568661422914, 290564209775552, 290564210168768, 
    308156395951040, 2923192831681916551344843010764715566828812849986, 2923728050244566794963132091203300995613354750530, 2924084864890002220300904370550234744395520930370, 2923728051608375487825928679510245383864087302978, 365466006455735597927865152721874083341588847426, 
    145427740496832, 286165358875584, 708378247566272, 286165358875584, 171816153781184, 299359498408896, 
    580835028767680, 299359498408896, 299359498408896, 580835028767680, 2923728073386446970765990339100188300954388484930, 541406973809109697134427777592910947458798470398271077176537859574431216540629344993538186917516838882682826035607350942451317857716850203640607702089205455101757956782662, 
    171816824869824, 149825921225664, 290563405386688, 871106098500544, 290563405386688, 290563405386688, 
    589631121789888, 290563673822144, 290564210168768, 79449387438528, 72852317671872, 79449387438528, 
    79449387438528, 105639091177537, 105639292504129, 105639560939585, 290555619840448, 290555619840448, 
    290555619840448, 299351712862656, 290555619971520, 371085815683523277355960470052578371796090245954, 290555620233664, 290555620233664, 
    105639091177537, 105639091177537, 105639292504129, 105639560939585, 79449387438528, 105639091177537, 
    105639091177537, 105639292504129, 573029569385977991062543329210225784855044328448243064202701118971729437383135997309438785211258335364, 565716190249537, 565716190249537, 145419280585152, 
    149817327096256, 149817327096256, 45694401243405505067210609680605083117594692419, 290554681233856, 290554681233856, 143091274093505, 
    290554815451584, 290554815451584, 154219538551232, 145414855594432, 143091274093505, 149817327096256, 
    149817327096256, 4080981816248566486622747978162396661559107566827178809714655490908935916825065799353238743431507995160276165642878409082244248254428907737720141366673807565817544353709862470, 4080981816248566486622747978162396661559107566827178809714655490908935916825065799353238743431507995160276165642878409082244248254429269798158545245198933776991472472498155078, 143091274093505, 290554815451584, 290554815451584, 
    143366286226369, 290554815451584, 143641432576961, 290554815451584, 290554815451584, 365399103964897076938032686360146663233707594562, 
    365399103964897076938032686360147507658637726530, 1461529556906314653900892778530526403797608116802, 365421404795166199291408837944262963453155627842, 1584806376596168463253968013908706081342648324518585627243378283275113548289568895156944396007966929045608555120826038077844916423354752823878658999346624344903558003853616194506987744241674839899966023154157819433614202739604766949177896435966219377333781544498877512, 283966335624001, 426898422239680, 
    989865974961088, 426898422239680, 989865974961088, 33218886717633724322929770282846208316897019609211577292832712416569957590468626176316426178208527876, 286156768940480, 290555620757952, 
    589639979373504, 283958550204864, 72845877121472, 283958550204864, 1461529513368780940808987163949805878856025965379, 72845877121472, 
    283958550204864, 283958550204864, 565716458684993, 565716458684993, 565716190249537, 365466006455704444027871699984706393973297533762, 
    145414855594432, 286156768940480, 145414855594432, 286156768940480, 286156768940480, 290555620757952, 
    290555620757952]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161156221800640, 1161224003915968, 387314253637953, 4217239420481885636211459009447011759740246693930719218008231716707284503742370822740980676046372996, 1161292658380992, 1161224003915968, 
    316934772236609, 316934772236609, 1161292658446528, 1161224003915968, 316934772236609, 324403039781655692647088007821301667198396256771944731613634334653699525851601226272190744861414980, 
    97053213332550074973426796383383220605107049282, 565701971022528, 567900994278080, 1126175062106433, 2923059026696272904011891032377754336666484478786, 1128376031535937, 
    636139436774080, 17127081202995492422529844575575664447885152834, 1102970368515542617896172687962525255428290906041628146779008017300459051501816079219365639975839108, 1102970368515424571948192825821603358479436035586220133618658775503870172831614896926999548995020164, 97053213332550115538246003687879241812620088130, 97053213332550115538246003687879241812620088130, 
    97053213332550115538246003687879241812620088130, 11440630906297679322585746363461267944565117506, 565701971022528, 567900994278080, 581095133811392, 565701971022528, 
    1128376232845633, 1126175062106433, 1134979745063233, 1134979745063233, 1134979745063233, 1134979745063233]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161156221800640, 1161155215167680, 1161224003915968, 28545062744809569627808806337319509373564753730, 387314253637953, 1161292658446528, 
    1161567746331072, 2923059026695276303732182258223596675297148147522, 1161292658380992, 1161224003915968, 1161499024429504, 316943362171201, 
    51381112941387784284643146475174781189865083714, 316943362171201, 316943362171201, 316943362171201, 1161224003915968, 105624522264768, 
    97053213332550399493218394849395384036026749762, 3020056487994356235900588060281961423347891835714, 3020056487994356235900588060281961423347891835714, 7183239312607841750779775743275536352613639600624194042416712907887156666376688669189352791297820139120313794094609455850452557039672638299397037507921909748284887751194571334, 581095133811392, 736462597040059628525269258032755211749604496194, 
    736462602484577499260284673446748930657895879490, 567900994278080, 581095133811392, 736462597040059628525269258032755211749604496194, 502750920750644668891194207713356234686294187586, 565701971022528, 
    567900994278080, 567900994278080, 572299040789440, 17127037648015849498874310985141379010987561794, 316943093997889, 316943093997889, 
    316943093997889, 316943362433345, 316943362433345, 371085815678528917485961367649310328800329865026, 1461551814178073752873021527768158459336975193922, 636139436774080, 
    73189483352768, 73189483352768, 22880673485650519144870035991783536253292582722, 75388506608320, 75388506608320, 79786553119680, 
    90781669397184, 95179715908288, 97053213332550440058037602153891405243539788610, 97053213332550440058037602153891405243539788610, 4217239420481885636211459009447011757397331037038499409718394504232562165564677752716142049323401348, 97053213332550440058037602153891405243539788610, 
    284501880607680, 286700903863232, 288899927118784, 291098950374336, 308691136418752, 565701971022528, 
    567900994278080, 567900994278080, 572299040789440, 581095133811392, 105839008948545, 316943093997889, 
    316943093997889, 316943093997889, 4217239420481885636213217601802303497115326521374029147114658860942937824903218094559125145584418948, 316943093997889, 565701971022528, 1461685619180623907788879271669994605197041668930, 
    1461507213219035662803746985923813418304993825602, 572299040789440, 581095133811392]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161155215167680, 1161155215167680, 1161296953413824, 1128376031535937, 513258889784516564910739244558081963442372524097847763678341462119322553913772024308689219249574908711180919529804515306533364243744321390766637433569087183701404312107590, 1161297087500480, 
    2923728051608334598332112317035909472843903027011, 1161155215167680, 1161296953413824, 1161292658380992, 513258889784516564910739244558081963404033433880928535218402325917022788325591231375586339473331589236029757671376666782388726726323105879930730694581580115782578296814151, 316936651546945, 
    28546369434083170030383713766576205968546219843, 513258889784516564910739244558081963442372524097847763675878836732047898963004584302430243383978414865081240422893612603993343514738225042933674172295823528822190959983174, 1862771912242165652843398957547466467620506365395872802101552661682054016951388531025561481832547885408302702136577531972696398500726144101988137235878063510861758193444626554132601266558789575477433074324763266946929238966335231491648906356513739932233105416246956552, 3957316615512914002351405356928354737105499913128815553575500078503183272219543287050254281466715874554855711555593318019135453090169253849406224821059153538782321990224227911, 176199297413569, 316936651546945, 
    1161155215167680, 513258889784516564910739244558081963442372524097847763675878836732047898963004584334258930514204759963025704304293284921290230506150396853834972526666082515346559011355206, 176063733305536, 1161361582203201, 1161164006428864, 316668207698112, 
    513258889784516564910739244558081963442372540322805462294172548550168886716865465354003962317343780688634800435538976770606671853524441522034873659782320196638341488147014, 105641702133952, 105641702133952, 17127081203161890658570681095987885601437261378, 72845070704961, 75044093960513, 
    75044093960513, 188398111012331902686419061334552080206912314946, 105641702133952, 2928713681012593648340898175235560319970032240451, 316936919720257, 290548641440065, 
    105641702133952, 105641702133952, 90575098211533486264477223487511349534073453679028298407165298405837874137032738784004696605600463353623662632703342634440830116374366391445779242315257849035030441143878, 105641702133952, 4050065516057230157794282668569750880526849546903012688426423258396565652475587254490067567554752223679588720735620831205619810153611342609583167387983518584828890603003620935, 28550550818823270679482731688152566453315311426, 
    149810884649281, 4152422188735213528166535053721975608662291842260646782126342810497117474434459974800612663206853700, 290548373004609, 286150326493505, 290548373004609, 290548373004609, 
    299344466026817, 16674315922253828236781220379183689059877952370862543678015821053923117706964451100628460413375006660, 260536679396684181049248953103489095909743378276927810441479935530373253024329701006102699699966149, 265751028401102427289069447553604734446076100293966357408385390086151063885012604398609637672373173316, 290548373004609, 290548373004609, 
    290548373004609, 387305663899969, 316936919720257, 316936919720257, 316936919982401, 265751028401102427289069447553604734446076100299785051415110562814237621680927605927037384721285233732, 
    290548641440065, 290548641440065, 290548641440065]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161157362651328, 1130581832774081, 1161157362651328, 1161294805930176, 1161294805864640, 1161294805930176, 
    316934504063297, 316934504063297, 316934504063297, 176205739864513, 316934504063297, 1161157362651328, 
    176063733305536, 1161226152317120, 28545062744810257964560610345572175332469905218, 72842923221313, 75041946476865, 565703582159552, 
    567902605415104, 72709640818880, 72709640818880, 143078384996544, 283815873351872, 17127081202996467249091011506551730081514918466, 
    28545062744810298529534560745272427624647366466, 17127081202996465981440411278288516420145779266, 17135443982445916232769087400903973217079661122, 708777536918208, 143628560241344, 145827583496896, 
    163419769541312, 163419769541312, 163419769541312, 708777536918208, 565703582159552, 567902605415104, 
    581096744948416, 2923036725865007830418698787419181170363757238082, 2923059026695276952772074939003297470583205271362, 567902605415104]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1161157362651328, 2923059026696441324713111315021351724340645729090, 1134979745063233, 1134979745063233, 1161226151334080, 1161226151530688, 
    1130439826215104, 1161157362651328, 1161294805930176, 1161294805864640, 316943093997889, 316943093997889, 
    316943093997889, 176210034831809, 316943093997889, 316943093997889, 1161157362651328, 176063733305536, 
    1161226152317120, 28545062744811556043727004209620829056148707138, 72851513155905, 75050536411457, 75050536411457, 79448582922561, 
    283957745688897, 563504558904000, 581096744948416, 581096744948416, 581096744948416, 563504558904000, 
    844975584203575910019615504572259328988016580418, 994925446435776, 565703582159552, 563504558904000, 567902605415104, 581096744948416, 
    572300651926464, 28545062745808441546213515136165062818161234754, 316943362957633, 567489873318080, 472395693875842482956046913392939744696981894344502252394457110387779620296581413491328976561767727236, 472395693875842482956046913392939744696981894344502252394457110387779621481057921742590850848549781636, 
    28545062744811596608700954609321081348326168386, 513258889781001788508752372384011230221984426090761528496969611538775695048092312526040383399720275402700216841501237472386162153188475053436590889326500832454382995847238, 28545062744811596608700954609321081348326168386, 513258889781001788508752372384011230223304216865169491994824153961901942688858064103720685153071493012635290298849532918329073210819799017689873884031588249152162203908166, 15121341268955300454560687058317760675804896124643772855641161530271676940097517645367644241470617776362471646784484213091683849195801144848853623815585243479933782260327626931735494833929035527252690443073274514328938652222867791331570501633938447925257246956552, 28550550818825297504239691914989740906040530754, 
    163419769541312, 708777536918208, 4217239420481885636211459010914495579850478051834331480633611333426392334692182368737416746323165316, 565703582159552, 567902605415104, 581096744948416, 
    572300651926464, 581096744948416, 316943362171201, 316943362171201, 316943362171201, 316943362433345, 
    1461551814199011120787062467951552942996774262594, 567902605415104, 581096744948416, 572300651926464, 581096744948416]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105640091521216, 105776595210432, 105640091521216, 105776595210432, 28545062745826610851591228548041198310933926722, 105776528167104, 
    105776528101568, 105776595210432, 28545062745826610851591228548041198310933926722, 28545062745826610851591228548041198310933926722, 105776595210432, 105639554650304, 
    17127081203514317805215536662316159062780157506, 17127081203514322875825191185635800234919468610, 28545062745826610851591228548041198344219923266, 17127081203514317805215536662316159063585463874, 17127081203514322875825191185635800234651033154, 28545062745826610851591228548041198344219923266, 
    28545062745826610851591228548041198344219923266, 73204515738304, 22880673485670559509961326503815560465817343810, 75403538993856, 75403538993856, 90796701782720, 
    95194748293824, 105639084888256, 246514150609088, 105639084888256, 246514016522432, 105776528101568, 
    105639084888256, 2928712635661194888245720056738522574537407599426, 72851513155905, 75050536411457, 75050536411457, 28550550818843470612569206011670893037543757634, 
    176145272213696, 176145272213696, 176076617748672, 176145272213696, 176145272344768, 176145272279232, 
    97053213332902791225012424598498878331639830338, 1102970368515424571948412247303579007569981664179232600548237794730884721995889129938148039405790852, 97053213331573563229227470946662926839221065538, 176145272213696, 176076618207424, 176076618731712, 
    143641445143232, 145840468398784, 163432654443200, 163432654443200, 163432654443200, 91366196719946597521282589673529834935400011586, 
    91388541106358686388607364683728601568040195906, 45694314204870956538934068744800732650565312066, 283957745688897, 145290293153984, 708790421820096, 143091269898432, 
    143091269898432, 1027663288861981544434363037134624928077837285186, 844975584203594047633728212277508432895299065666, 585508212249280, 581110165803712, 581110165934784, 
    581110166196928, 565717003932352, 1461551835806959593375293896982334075249681831746, 1464361729701974451891127397484688824334624559938, 1464361729701974451891127397484692202047229989698, 567915020554944, 
    581109227197120, 563517443805888, 581109361414848, 567916027187904, 585507273708224, 581109629850304, 
    581109629850304, 581109361414848, 581109629850304, 581110166721216, 72654742687936, 72654742687936, 
    565434869883201, 145290293153984, 145290293153984]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1143784226431809, 1143784427758401, 1152580520649537, 1143784427758401, 1143784226431809, 2928723421255084513510478084215474338173804397379, 
    283953450717632, 143645740110528, 91366501613926146501184731904124236344063955522, 72709640818880, 143645740110528, 1134988133409601, 
    2929437042379178558083424565806454830707014419267, 1134988334736193, 1134988334605121, 1134988334736193, 1134988133409601, 143078384996544, 
    2928723418532825578142970376508477478719658705731, 72847218184640, 283953450717632, 283953450717632, 143645740110528, 22880564743836239526991616807231090143927472962, 
    72709640818880, 283815873351872, 143645740110528, 284503491744704, 265751028401102427289069447180654201188962128707989100574659411042167841008391317327611930407236779076, 265751028401102427289069447180654201188962128713807794581384583770254398804306318856039677456148839492, 
    1128391264969537, 1128391264838465, 1128391264969537, 1128391063642945, 531550657856897444840950424683310771935430631770051307026752874919687343577192543873110405175316888644, 79306710585536, 
    79306710585536, 79444287951296, 79306710585536, 551485161054599160949015281399527600627153221871381660619777391944797718023169200236380321195801668, 551485157187413703439291501099138753684484580098853538949984661410565341663646023005349752892341316, 97049358902081, 
    158488727654592, 551485156945714612344934677186017527250719757583056372118147707473031807548550839877750907872787524, 532053411279217730194372624496281262155540255786838790265430814398454856155294398937367107198511266884, 158488727654592, 158488727654592, 158488727654592, 
    158488727654592]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [105640091521216, 105776595210432, 176076617748672, 176076617748672, 246514016391360, 246514016391360, 
    176076617748672, 35201686311104, 581110166196928, 565717003145920, 1464361729701995221157789699309467283913485390658, 567916026401472, 
    563517979890368, 581110165934784, 636154469159616, 105640091521216, 105639084888256, 105776595210432, 
    28545062744850459121550213054852101669447014210, 28545062745847380118253530372819657889794757442, 105776595210432, 150958497008678147900342096783323651760706978917778538736433208750063996791941753920982603384547702913322574253456206693024691222153710683516225573224402983133407612284486, 105776662319296, 105776528167104, 
    105776595275968, 105776528101568, 105776595210432, 513258889781001788508752372384011230195043953622777658304224379201057319822478333293950863052555775002700148453465259835972192144104343970537642935353347931164625279596614, 28545062745847380118253530372819657889794757442, 513258889781001788508752372384011230219177270641386485795667921523907969662550470556698043565841414558023559936037915334916978231533217146255088972699936583932570859681862, 
    28545062745847380118253530372819657889794757442, 105776595210432, 105639286214848, 736461225016249006906417448941417149233564238659, 105639554650304, 75128652436416, 
    75128652436416, 92720838480832, 103715954758592, 28545062746179687117185259333206702516231739202, 28545062745847380118253528085423392783096353602, 90575098211533486264477223487511349505858766871860494260045355757216553622604165527732262863385989092612607512615890717615497089548403209986244158370152730019705325268550, 
    28545062745847380118253530372819657923080753986, 90575098211533486264477223487511349511359743547103306841967846907715661734576538819644427889028390236703688212810900395820146029247114190762544473446972840294462770032198, 28545062745847380118253530372819657923080753986, 73204515738304, 22880673485691328776623628328594020044678174530, 75403538993856, 
    75403538993856, 75403538993856, 90796701782720, 95194748293824, 28556126005163792673338563575708371988420499266, 105639084888256, 
    176076617814208, 176076617814208, 105776528101568, 176076617814208, 176076618207424, 176145272213696, 
    176145272213696, 143091269898432, 246514016391360, 246514016456896, 246514016522432, 246514016456896, 
    996326402273357218109927400851526269960105248795421382739998720182090520650510331407544195673293637749330119195194414192685813951788936987033480899605377828544545123642950, 996326527343160706410786843079002843264608698114789021533217573384470084971430727409899468453882429729489876114139537216141351259030794282873951900070794751500305571163718, 97053300443880264256136419395340888950744028994, 246514016391360, 1461546326125036362266283430743942550092410591042, 990540016391104, 
    581109361414848, 563517175370432, 581109361414848, 708790421820096, 176076617748672, 176076617814208, 
    176145272213696, 176145272279232, 176145272344768, 176145272279232, 996326080379589994946213082928518195668570504168111214115093299032323937080599706757103496796310703306557858909477375807202432728942919591023812179790401145328020699065926, 37895173739116018890760751996630483019218920843790094762211611662036861783836937424729206323197632312890429587681508953571343756002908564451129645361848147206467716253304218478881553906530622179899182353288098443134481861701557132185444839666227012157295376210283191183515867616215428346646929410923189355008432556473068144200149848971185868521619951597574501016707070411570537862993804294679297886320191104718379386112289469756714101398800817712255034664020584491476756213825633615801227204312222676523148, 
    996326080379589994946213082928518195674071480843188762704818228033085556309726214239297896963597435663987097245155469617937513774107106595820864842401339040364523924074054, 97053213331594332495889772771441386418081896258, 176145272213696, 176076617945280, 176076618207424, 176076618731712, 
    145565313668032, 154361406690240, 171953592734656, 163432654443200, 163432654443200, 163432654443200, 
    143641445143232, 145840468398784, 145840468398784, 163432654443200, 163432654443200, 163432654443200, 
    163432654443200, 105639084888256, 105639084888256, 246514016522432, 246514016456896, 105639084888256, 
    176076618731712, 145290293153984, 308156396475328, 365399103964897076933080926198393332420095001411, 365399103964897076938032686355534994257716724547, 308156395951040, 
    183045236629706994930798009932235091868616045122, 365421404795166199291408837939651294477164757827, 365466006455704443988879006312931628472263000899, 299359766844352, 299359498408896, 299359498408896, 
    365555209776780933402383612649396829350055134019, 290563405386688, 290563673822144, 736462597040100518018391694730651869333248054082, 736462597040100518019010664750294559470697616194, 563517980676800, 
    585508212249280, 581110165803712, 581110166196928, 581110166196928, 565717003932352, 1461551835806980362641956198807112534828542662466, 
    1464361729701995221157789699309467283913485390658, 1464361729701995221157789699309470661626090820418, 567915020554944, 581109227197120, 563517443805888, 563517443805888, 
    563517443805888, 567916027187904, 585507273708224, 581109629850304, 581109361414848, 581109629850304, 
    563517980676800, 581110166721216, 72654742687936, 11440325928267459949207758002657319230745088834, 72654742687936, 565717003408064, 
    1461551814183099266523630238299371192178517821251, 145290293153984, 145290293153984, 145290293153984, 567915490316992]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [531501997402235843673077274021725842911483841064560589280840357724673930170459758502121706259873053764, 1152580520584001, 1143784428020545, 1143784427758401, 1143784427758401, 1143784428020545, 
    636156616643264, 531501997402235371604539981213064686716613139783140165133717431474319011008406032441629104561390402628, 1137187357795137, 1134988334605121, 531501997402235371604541320929354944417811889186862475624481607899517730610381301894690400398798535748, 1134988334736193, 
    1134988334736193, 1134988334605121, 565725593080512, 6937448691489467385440750068787062186885616665577801344132201073430500415271184974291486959224913765267281657359022672089623342078725673307701448557662884321208761477872187974, 565717003408064, 565717003408064, 
    1461551814199382371272980162574091396072859572034, 636156616643264, 73204515738304, 565717003408064, 565717003408064, 1128391063642945, 
    1128391264969537, 1128391264838465, 1128391264969537, 1128391063642945, 1128391265755969, 2923049270124277460077097079587552656526114113347, 
    581330302976198009799261525613809957314638369308175611521468928201425303804919612368507245360285131909, 531502440922011507987659837301142041274031040853228475323851894931054875329101233260989640031068273732, 1143784427758401, 1143784427627329, 1143784427758401, 1152580319454017, 
    1143784428544833, 145840468398784, 1134988133409601, 2923728051608375487825853723753442065139785352003, 1134988334736193, 1134988334605121, 
    1134988334736193, 1134988133409601, 1134988335522625, 567923811816128, 708794716787392, 567915490316992, 
    567915490316992, 2923718295032351130678381627111041663109555110723, 568057362649792, 708794716787392, 145840468398784, 567915490316992, 
    567915490316992, 88032873091264, 88032873091264, 97049358902081, 158471547785408, 158471547785408, 
    159038902899392, 88032873091264, 88032873091264, 88599826010816, 532053411277163287962389350442714345972601651671339620610792398098506997056905948370834975666964176900, 158471547785408, 
    158471547785408, 158471547785408]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_11_0
  · exact tv_b11_11_1
  · exact tv_b11_11_2
  · exact tv_b11_11_3
  · exact tv_b11_11_4
  · exact tv_b11_11_5
  · exact tv_b11_11_6
  · exact tv_b11_11_7
  · exact tv_b11_11_8
  · exact tv_b11_11_9
  · exact tv_b11_11_10
  · exact tv_b11_11_11
  · exact tv_b11_11_12
  · exact tv_b11_11_13
  · exact tv_b11_11_14
  · exact tv_b11_11_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [176473902289088, 535719680387928928508262249315211790043800904100680798194342126502350872680351353718441731798748054596, 72576635240513, 72576635240513, 2928712461445908185002432382697755260693117934402, 176488934674624, 
    75815711701953, 79801307122497, 88597131708993, 106105088839872, 106105088839872, 106120121225408, 
    15015491880075510186898946187753574751556412114141009501157290458110295674639292416584694498377759973325484679858805799723969723490737781130176123771299197292699552381596896654966451351659275812832828198638481167501254231887237666809210384485435327259870216246197512, 315644150232281319585688704440047274065724013520331876459065755326633320315834625820092725894961131652, 581395120223413659886869390627426463909128703296510162803564572373518361470654454492263457341803032708, 123695392498937389873713026031008379330873147599292021254716145819189694294113370892888727216937027601078762810012756927741905225260625999316449695889315624205286446057434694, 75046241444289, 88614377704001, 
    88614378162753, 6766436808714252632737273865956557597569202668128533978826908726598803611992413954778805629476373320047573216598054496145768205916791936412635906316587934156168959734803823880171532508322662095690684534984234228246276075404903871312826147980730520886577197191195875103783151735899901467233207010417833512082166915104164751462828749422511552396261243248782819027484657259203953739, 176489337327808, 143516631045056, 158901044515008, 158901044515008, 
    158901598163648, 158901044515008, 246842581389504, 246842581389504, 51381112945375625460657926278988331512219330371, 2928712374333621279683420232168416862858240857922, 
    176473902289088, 246842581455040, 176473902289088, 97053213341854670943921207492707819102463333186, 97053213341854670943921207494865043340079928130, 2928712374333621604203211830634429026289160558402, 
    106105088839872, 176473902289088, 246842581520576, 736459918337267226897142980726781806680328902466, 246842581455040, 176473902289088, 
    176473902289088, 97053213341854995463712805960877206770999628610, 106105088839872, 106105088839872, 97053213336538205175016370549171180941791487811, 246847010574528, 
    106105088839872, 246846876487872, 246842581455040, 106105088839872, 97053213336538205175088906375057665178942326595, 736459918337267226914435455504128431309451171650, 
    106107236323520, 106107236323520, 246844729004224, 246844728938688, 106107236323520, 176476050690240, 
    106107236323520, 176476049707200, 176476049903808, 106107236323520, 246844729004224, 246844728938688, 
    106107236323520, 176476050690240, 143490701856960, 143490701856960, 158901044515008, 106120121225408, 
    106120121225408, 246857613906112, 246857613840576, 106120121225408, 176488935592128, 4271982446720362678929490552409326234582905009315688334122046632055282832463910806957539511283865285, 
    4272742766112970863757579415470423357565237917123566944636124662476265716750659562135333145765074629, 143228847268673, 145689725112512, 145689725112512, 158883864645824, 299634913186752, 
    2928712635670479399483337662181333999621249176386, 2928712287221337619561115135868052714890182267714, 73135779483840, 290839088600000, 123665259711913420370712330660723045920375066272762722792612405426671465952784306927935906448863087380884105541961280486000954278974625379023493718242036543539143828633024582, 423201418669900436894417346185342967410023744323, 
    468873519061063016608775790455525957577621128003, 308439881094080, 284252772766656, 290847695049664, 308439881094080, 371085802077566301694106769168011028512028808002, 
    308439881094080, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164447072354331192915657762337793580403624261472104201492538901389108252674512484253374085190, 366090429708556802465251782354390361484608688962, 371085815688840209422975101621124966807578366786, 2207891062849, 16611463205385845350240742841008783679067940038725230171725206270922124447388264516427401581822509508, 
    176473902289088, 176476049772736, 176476049772736, 176476049772736, 176476050165952, 176476050165952, 
    123695392436852379508388424951488597190394651499170539944560793554970187448512661530917438987332575687947553230095259101970544988183732519253840532112740455086381884541712455, 283815877546433, 73121888473280, 73121888473280, 284228328624576, 73121888473280, 
    3957920452942559774011439111213755252686269257527929192149412905855699754193710145100742682950678823764154570270101304172962907019650316529246160080122319746648494769478563398, 73120746639552, 73120746639552, 284516628325185, 145689725112512, 145689725112512, 
    2207891062849, 72670922213441, 536757350297632015557065429965716794350645091018284442124589173478570895517717151593292361194990223492, 565226563962945, 565252131457089, 72670922213441, 
    72671391975489, 581110165803712, 581110165934784, 1464361729691402895160015768674762119416280847170, 72602404061249, 72670922213441, 
    72671391975489, 735038153274139525203751994769350037710166921794, 567916026270400, 265751090771077031726494845045363044277985876845089954931336330694022152937812004578622981429587266308, 567919386825408, 145412703924673, 
    563508853871296, 563517443805888, 563517443805888, 1464361740580438636629737113312336591446727529282, 1464361740580438636629737113312336591446727529282, 581101039915712, 
    145412703924673, 581101039915712, 581101039915712, 581109629850304, 581109629850304, 572314072781760, 
    565252131457089, 1096172223465924855102190768643887475217028634434, 847200578180032, 565802424617537, 565634720086465, 565226563962945, 
    565226563962945, 565252131457089, 538834321680677798773598620115276163213045110872527081709825075604588176197499980136157002477779304580, 538834321680677798773598620115276163213045110872527081709825075604588176197499980136157002477779304580, 565252131457089, 565802424617537, 
    565802424617537, 145702610014400, 6059625031706314223707550154661728396192740636449871314918306649817884444022675186291152654844532043355990048385154516023714760346726880324934587010969510043391605279501012550, 2923181724870736943724769552151322256780935828290, 2923181724870738241803935946015370910504614630210, 849377322079168, 
    145689725112512, 849398796915648, 572322663109568, 73120746639552, 73120746639552, 1462220839091132028457958050653357908828440512323, 
    145689725112512, 145689725112512]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [563534145012289, 563534145012289, 563534145012289, 90744144611905, 70952935768641, 70952935768641, 
    70952935768641, 563534614774337, 91366501614338898914080676127645201571923367746, 563534614774337, 91366501614338898914080676127645271939325368130, 563534614774337, 
    563534614774337, 11451432787134444715784545940866033436233568834, 11451432787134444715784545940866033436233568834, 283815804145856, 8304733930652938607698653482023569652679522766682352961665499681692860565896535569000761990077226692, 11451432787134444715784545940875005451116220994, 
    16609451526312730749257019139755621499183353105004212119791240419460840353791592869667261257506690244, 11451432787134444715784545940875005451116220994, 11440630821309764079556171128527841354575778370, 563534614774337, 563534614774337, 563534614774337, 
    90744144611905, 563534145012289, 11451432787134444715784545950089405438997041730, 11451432787134444715784545950089405438997041730, 563534145012289, 563534145012289, 
    563534145012289, 1135254622585665, 2928723415815867998090976523802380808245504672579, 2928723415815873190407680785032377043863486890819, 143091269898432, 143078384996544, 
    91366501614006591915148944879870617561723835202, 182710702396331751036856703677606123433961198402, 91366501613923839368291336046768942677200212802, 143078384996544, 283815873351872, 283815873351872, 
    283815873351872, 143078384996544, 143082679963840, 91366501614006591915148944879870617561723835202, 731467230115671196968166887104846162481666622275, 563534614774337, 
    563534614774337, 563534614774337, 736459858447570324292259325925985831132153807683, 129777056292194962637718395595851078983462307159534998860830360605859770513949921767314671251017476, 129777547423926009027780781104177171385278515580803939357287225289307232585037654894281691150470532, 283816011764160, 
    283816011764160, 424828382220736, 563534614774337, 563534614774337]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [581126331056705, 581126331056705, 73151959024193, 581126331056705, 73151958567489, 11440325938776708879716073214513810158104118083, 
    73151959024193, 73151959024193, 581126800818753, 581126800425537, 581126800818753, 469219808792227002373687925420293652424159928649468681277453441047704230390403543294155844452294355087892956425588148681318860602331225542973921526949798478173475459120949814307078940769840931061776860806709887789510658645194703383743243965900707850092553246156552, 
    581126800818753, 581126800818753, 581126800818753, 72709571612864, 72722456514752, 72709571612864, 
    72709571612864, 72709571612864, 72722456514752, 581126800818753, 981485938198129445952565290611119015062394574222794697707348949635771946069391345256785930324548219589945821444828182132140123144476351561225992803877949866976500593083830397340895516666585963452518966017070035810525229116353060504464200417373280593516691464245997512, 73151958567489, 
    581126331056705, 581126331056705, 91388802444275714268525096463978473499658294082, 581126331056705, 72709640818880, 72709640818880, 
    72709640818880, 72709640818880, 28545041147190562006388805607453408801539000131, 143078384996544, 283815873351872, 143078384996544, 
    143078384996544, 143078384996544, 91388802444275714268525096463986917781171868482, 182733003226600873390232855261722423653409231682, 283815873351872, 283815873351872, 
    283815873351872, 283815873351872, 73152495438401, 581126800818753, 583325823615553, 0, 
    581126800425537, 581126800556609, 91388802446934169972912257540783189965320237890, 182733003229259329401629146081148888824464552770, 91388802446851742233048336287469556724085569346, 143361995444672, 
    143361995444672, 143361995444672, 284099483800000, 143366290412480, 143361995444672, 143361995444672, 
    283816011764160, 91389499366447733741321569958191511415398938434, 354747398755264, 581126532383297, 581126532383297, 283816011764160, 
    581126532383297, 581126532383297, 73152495438401, 73152495438401, 90744682007105, 72710056055488, 
    72710056055488, 72710056055488, 73152495438401, 581126800818753, 73151958567489, 12845278330802008872723117017785090653548479043, 
    11804813857773979614755196014476642063957793862915126836458324986019588655989242666163980876291247742631575481430400239823499572253017740167973987826791735436029593611486824995771654736794393380326526545334300659833208857332700605806599778634803874287880023033335594737031200248305678230375940188187636544378869925808632634830921473865956728167554608954384808490639162576052628554, 91388802465543362201374498196869793484747380546, 182733003250526977492915529957965472362708154178, 123691028792797361560258551675728934420908892118358658238831916157607938069551762789541321337209733052695882156314494280986953670293440680276056388573966919635086407544815175, 13206933071602446336550894114957137148539673951191151661899749706387021787482249241011159505491573424931676790607059198121632268867105664712429670551113320024599126981157101872085812307893844205011378296852218992539771822361578107310729931569553205833764415238334565277728923748940047703021291854839621711019983915745588437818056712795566792441681471391373655242205966379328916426, 863690695288658164592981944579899582493124273280552962250267840554589916195111809962988175477196669060, 
    73151958567489, 581126800818753, 581126800425537, 90744614898241, 532410317973131812080648677752118156376815261219291186038797647437099396150726205138477694901744320644, 182733003226600873390232857549118688793393632066, 
    1101836620742989203133207196839787368194401948483, 182733003226520392788925567716264780081863332674, 73152428329537, 581126800818753]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [73152495438401, 6707465288621971031835132697190279390877547052123107247825090773972256777994121116798437386848173509973660817664628159842055867063324543920466853158535712435278139222606045962444596049495972841195545502460507647186625749270179761531380632314090637427429430334785817761851714426616033233377174332554616480009854906728384354611475908352998520626078673419983863434425587238785047114, 1128650909180737, 1128657620067137, 6787310963707271593047490618342430243421323160957026664142750599390248325869293334144208201536937793815349775578071734171764087409461491540593411500088126581294595862487591564884709751068069085743493973056260779659447470060588423854222008558442465940807252783513005705075707136154096898556956246676467066618773509889349488685820338958058531065129067243349538897240457091391292490, 7760525347272199341705156789529932210115349322908591399568390346757495377862136516055356765362915144113934604893347240797137422832018604985914503037669421473726647850991174, 
    2923059026705577860035993535773693007241471379267, 73151959024193, 1128683121689153, 565733168267841, 284258191557185, 565733168267841, 
    73151958567489, 73151959024193, 73151959024193, 565733638029889, 565733637636673, 565733638029889, 
    636102449384001, 565733638029889, 565733638029889, 3957316615499466468212719094225360144690030576193401326336176225563880792474660491750709789220521317904490689962216329872920372967147657015317969530776042648644147663859002950, 123695396123260585422513779322611143084594008737823888648488820666983576921622347887368783222057903019207773616799909268359534297135181945061858604790490644129921884907099718, 3957316615499466468212719094225360144690030576193401326336176225563880792474660491750709789220521317904490689962216329872920372967147656940881222046754477339130615685612744262, 
    565733638029889, 565733637636673, 565733638029889, 73151958567489, 565733168267841, 3958131796911442227299865864612431999304107343535334080602125508309095516285683046796553395950236807053290717152065605547380631224506822439245035561819907208537178779638790726, 
    565733168267841, 2923059026705577859996379454516559780847925888835, 531501965722252339719151636859109374009038628548458645621288762925965574117652089572644905425041379141, 73152495438401, 565733638554177, 3957286427485527111805477507569384677388265727109133885469174485938400837146355648543989569038032184035623952487150786971389566167876809028946180645693182702892724347738225223, 
    1128670504833985, 1128665941819969, 960962621259340297057677422063182199245840617938388148096835402268020387733275207765024462706128980588707503671014813324349295268446704631925299327998312358231314773816045950471307936211617807282735030474848144285478772487826135717043345540760678042798391304246988552, 284241213538881, 73152495897153, 92771453931595159638478330492603361684097110850, 
    92949859893183409694213017151702717515058680642, 819094724547689046692294113858450459903427921425627552301372002683041496736621848608300331865470707612729224595928737885511600770258654638204993113983254804979948209734076716881114513016452388274238236519192099719582715830741011680100977994820456621846293265759072786517254988920699233840460840788619087866117662981444183911569072217660949535941141455877211844017732347711562, 565733705138753, 284250340352833, 565733705138753, 66437805115251438498460996820496420607349404312803139216634408890439242835508994651390812884326572933, 
    565733705138753, 1427253137306948247696859085716632393096368706, 73151958567489, 565733638029889, 1891923037283693717032062335410709978026517395481973560092923343744026414596003938235769960261279574949235257365603165584074682316904356669091425511955122902409212505618803666934153616018217822599802088587052666134734194749625369073131816428338225267523747848245956552, 636102448859713, 
    636102448859713, 73151958567489, 636102449384001, 565733638029889, 565733638029889, 73152428329537, 
    735038153295407254265949365575100471625558102594]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [145207477735616, 145207477735616, 145207477735616, 2923059026705577860313292104573617131222101690179, 2923059026705577859996379454516559780847925888835, 2923371237138357288720360954572377351454170588995, 
    565701426299457, 565701426299457, 145277408252096, 145277408252096, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 145277408252096, 427027405476288, 145827583496896, 145290293153984, 
    145290293153984, 145290293153984, 145840468398784, 145290293153984, 145290293153984, 145277408252096, 
    145277408252096, 145840468398784]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [960962621521537293379979556454214614816879939158999368111922360097167671287111974086245154287976443772186300180164100333240201567448050508407135749937076602727591508392418692617335607918771078939298960964473806393203537879860813043396254518789519043813442057246991112, 1130861005534145, 531566893848442985190982632027721153298974477039181845727692407481501007018660946012629567639888556932, 531566893848442985190982632027721153298974477039182200872590278890944639315755260370169481374003852164, 531502060762209460540526932838284008223569222564131113543963862755709990040225088294634811120303936645, 562967687992000, 
    299634913186752, 299634913186752, 562967687992000]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130861006058433, 1130861005403073, 960962154310961563796381349092987140300534773651272601109761063753628270890533113124306455439617455967588188662125391583243788144481475754480825080846446781297179869698504627824979610632529512033688914217177329333396545536339463755614266714138011686066471172249837513, 2923192831687194541621695782678886395318913520451, 531502440922011507987686434078471823144490727441255193011203247165108951455453122644695538789370259717, 125691878918129693493783394816696916882606847555, 
    567900449555393, 567900449555393, 531572897205346960813053586246472961869587765350608661900433813730418093169203568008606169196654773124, 567489873318080, 145277408252096, 72710056055488, 
    145277408252096, 72710056055488, 290413358355392, 83984072577472, 514202380385463515241139586161635078410688986624763101920421075198042071779084697497216874400286692569397115670143843515082581651371729116946872756556354465366530458635846, 172503365325760, 
    172503365325760, 163432654443200, 581109629850304, 163432654443200, 308705900893120, 581109629850304, 
    581109629850304]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [149605524246720, 149605524246720, 4081435634987215259147902240561829092450605837772288908711909046125484282167616829695328326869657935732542189527043426390243426910066846590186962430904486230976931596154697798, 290343019090368, 983484711733143416758284759350834243573552108981590457820256009415469240541679843966623251808802090552781541883876702767808339915242059490529919089063313455901849113010376268666431776592239513583375668921261202833323509312999558756812331353395385730156479512496988552, 581094589088321, 
    581094589088321, 79306641379520, 79306641379520, 79306641379520, 79306641379520, 11775143275264820397667391612402724349656699458, 
    149675454763200, 149675454763200, 149675454763200, 290413081530816, 290413081530816, 431425451987392, 
    431425451987392, 150238095478976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [91344201462890542310196355290660744747953427266, 531566814648484225306163577302677546008594848531308561761224158580391135107348483123674124676961156292, 72709571612864, 72709571612864, 519076537507080908344362193818004329642150064802537230771376243605042645409088071232959907757837892]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [149605524246720, 149605524246720, 531505989080216822504545441425927894600129048394091335845287042994591954481742645668229179213212825092, 149880410739136, 290343019090368, 92057827351270032357989517169260258875251103554, 
    2928723415986004638274329526957812464670444914499, 2928723417176992922497614149227198041214517552963, 79306641379520, 79306641379520, 79306641379520, 149675454763200, 
    290413081530816, 290413358355392, 150225630008256, 149675454763200, 290412943118528, 150242809877440, 
    150238095478976, 150238514910144, 149675454763200, 149817327096256, 150242809877440]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1135254622716737, 3957316621027680774542082373564540321482664065521719412090731549915495369561945031466348726599268933136967068562803597910521654087075697734352808232621123914160736946047909446, 531570869686402707761686297389117202236281552858089490700227594933126821163870356277668544982762562436, 3957316619184925684297189135165343748734485873947333919467745773701685480151136059254356671545768756957589054654312539754863293613874907849095359872841232727821546962118729286, 979746076449939809731335274314589080849127594013935360025482241992544157271737945857433326421343175310091858839748602122331494967632477299995305376773318972826776361362979386265140824060174366886834367144101550147460798922570102416350964476954704597015855656499877512, 818984051495632020652039655804615544499890324135165325949095874018110009116439897787280181456946962979382062940661865460795932606620142447798992006196616913156283766016757935581726493664518381453554146146679003096453821996860296043524230668236311529215818453959224023455827998583621564323704596776312554637487002614981868193292652891548765568418979893834533498121142685418058, 
    469687317398635759755275189391451669165155153116673744159535664390165911623069412878086764629415261746033778871968850124827492677707250147112221190204053172295794035619648261005321386151137935471891129579976207442769404593427796208712601255838565663769128499877512, 3353732746053689577403148970731478088170981789197854567558981016789814358045213061831964934684629118667353939146196299676736199590153173525366024640020399429450048725997384248372980919151216826588751589376765966970813487412548250744329427883491741743384766494242342479021587839918389494082594308015028117509360775924667086768389660015823701208889097465373568765621680147916931658, 480481544559208298773773550902776623958610614004884674759467982113444144456949614850118468986724879538371207454775726776024241170745538807907726679283009133647659636195720204204554668936132633849374265301077114728323286195092126869827563720679305867981488680499877512, 290343019090368, 581095133811392, 531566814648484225306163577301891393959875876369159785164467980674765342921701774333070150214625803460, 
    1135248247907137, 572298496066369, 531566814648484225306163577302677546008594848531308561761224158580391135107348483123674124676961156292, 72709571612864, 72709571612864, 3957316619184925684297189135165343748734485873947968533197793647201883748957865419333530142843195663281826603584564668709830788875181056312579598349864052793147435670730399302, 
    72709571612864, 145277408252096, 1135263213437761, 290413081530816, 163419769541312, 581096744948416, 
    581096744948416, 72722456514752, 72722456514752, 3958041221582930242412316992220802673878394518160826139846580469297350018351820479952846069080365523882981808473566601705747663874042362532865291550677479541699110749350100550, 72722456514752, 82068515066816, 
    72722456514752, 290839088600000]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [243420576429546975486548347881097322600702188721975096977029226645937522675705709088721150500212735547643404717473897717746653301778246382588337282814701174905486609803334, 243420576429546975486548347881097322600702102076047155701564864747138148387095483617604733599980318541178401519335823080861763012585429857347179328460523390475138256922694, 88545121813057, 88519553860161, 651602460414656, 299688867926464, 
    88652490215616, 88652490215616, 299758930366912]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [73152495438401, 124540760033609317283011069906777433309309331109417141642192466939757901614809833909998897802112269627676696627853743876201584784776631160627210187980631736464710439516230, 124540760033609317283011069906777433309309331109417141642192466646261750651094059020653503333903852370685521420690961949293117156246795598891749683860669025049364510783558, 73152495438401, 90744681941569, 90744145068609, 
    159038483468480, 159322110694336, 159039037117120, 159038483468480, 581126800818753, 581126800360001, 
    581126800818753, 581126331056705, 581126331056705, 581126800818753, 581126800425537, 581126800818753, 
    581126800818753, 581126331056705, 94198707079452854785805611489279266655878320962, 581126331056705, 159021303599296, 159021303599296, 
    159026152215232, 581126801343041, 581126801343041, 159021303599296, 159021303599296, 159034188501184, 
    18151086494400, 185542907863107242071967655474533528196777849666, 581094320652865, 651602460414656, 299688867926464, 299688867926464, 
    88652490215616, 88652490215616, 88652490215616, 88652490215616, 299758930366912, 299758930366912]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_13_0
  · exact tv_b11_13_1
  · exact tv_b11_13_2
  · exact tv_b11_13_3
  · exact tv_b11_13_4
  · exact tv_b11_13_5
  · exact tv_b11_13_6
  · exact tv_b11_13_7
  · exact tv_b11_13_8
  · exact tv_b11_13_9
  · exact tv_b11_13_10
  · exact tv_b11_13_11
  · exact tv_b11_13_12
  · exact tv_b11_13_13
  · exact tv_b11_13_14
  · exact tv_b11_13_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [35751442124992, 35751442124992, 5709012570246128593160424297542081653499761474, 72671123540033, 17127037649345234683319261330543580319475312451, 73151959024193, 
    91433404124752454971072644254356169290638431042, 90813401418305, 90813401418305, 853797648470976, 183050877158176070545050561016594388340183219778, 853797648470976, 
    366090429719180931125303793857215068650942256962, 366090429719190666996350316642116839174364484418, 366090429719182878244053384655593892245674152770, 853797648470976, 290821908206016, 290839088075712]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176476049772736, 176476049772736, 97053213352571288021877350616839643469805785922, 72671123540033, 72670922213441, 22925253517073183618693855505297186403796911939, 
    23014456838149654017439458418321364831040964419, 88064621873217, 106107236389056, 106107236389056, 317213676540352, 106120121290944, 
    176476049772736, 28545062747135879611908872398089292676868351811, 176476049772736, 176476049772736, 176476049772736, 176488934674624, 
    176476050165952, 70952935768641, 73151959024193, 73152160350785, 73151959024193, 73151959024193, 
    90813401418305, 90813401418305, 90813401418305, 90813401418305, 73152495897153, 91433404124752454971087151419531988168901399362, 
    90813401418305, 90813065873985, 92057827372287880865619395774788394329552458562, 90813401418305]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [176473902289088, 176476049772736, 176476049772736, 176478132310208, 176478132310208, 176478132310208, 
    176476049772736, 469678024263096156171119660081112803560976570824994383608742994714423205456177000511392500225258753929224450213863525481751775939535724058068846756318798925108353196372914746115787636185749809293346863462381071362899838642047192899902686722572958040065048249871112, 176473902289088, 176476049772736, 7759266745884737787877145148768247869707928956658233390514133441169626715139761082634133985774728768439309400775956985870221268406337908348105628720016858296505132738641478, 176473835180224, 
    176489337327808, 145689725112512, 176476049772736, 176476049903808, 176476049772736, 469678024262996135954626474396049201883404307809439465847209469036293517491662853868777365327554786199044271007167583316742716881029232605415329987486170661629921476336782700808944639187026876486184352385882573413847886813390504831827153888766743329898520246197512, 
    145689725112512, 163286759772864, 145689725112512, 145707324412608, 145689725112512, 163299510457024, 
    158897689071808, 176476050165952, 176476050690240, 145707324412608, 163299510457024, 150105370923968, 
    163299510457024, 158883864645824, 143490701856960, 143490701856960, 143508301157056, 45850507054584585683350108326387688803185728322, 
    145689725112512, 145689725112512, 48526606686879268241992863291730869224441125698, 158901044515008]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [246842581389504, 246842581389504, 990140584432576, 172213702513601, 597813960960527290976094133971908173373739148041654284595482607509685154866197222996090333195090960516, 290829978571712, 
    853797380297664]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [854023419870960011236627802010097679097868147134809660628665189460710117407963691920351114754433131396, 176473902289088, 64880730932859096344032658499980910768042536981449543630859397463586982860997805638096830647198532, 18151086494400, 708644527149760, 18151086494400, 
    18151086494400, 106105088839872, 106105088839872, 265750967022100860209987475400698700642985871362512850690766706999080307499633799629332845527040669188, 1464372861018823477429589516038269041656136274754, 106105088839872, 
    106105088839872, 106105558601920, 106105558601920, 11451563423661946516976354343763199406276350530]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [45768272717046277528868664777451796336720562755, 91522607445746516357816004025188922380548921155, 290847426876352, 286453008438208, 286453406897088, 308431006208960, 
    299634913186752, 308431006208960, 290839087682496]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [283777154746433, 283777154746433, 284258191557185, 284258392883777, 145689725112512, 708657277833920, 
    145689725112512, 708657277833920, 145703012667584, 853797647815616, 91522607445746191837734148922904239919733936962, 91522607445746516357525747388916403350653637442, 
    823700679248421806075577567570261703412022285122, 145689725112512]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [371085815699474073874710073185701877383497274178, 324410952043160650859974030848767479835062692201186926807968369422735110609415634418902542565723845, 15015491880072522916433016692265452359580515945483623649988975255275310110108900507927035805356958221677495114067783219606867874521778266072277790468576885387376404238363822916112661411800245198480613643559621149883548931905719783805099156320508774629508104246197512, 1102978226636332548769622337346846429261623513427542260925652726079421808411823819631641161844870853, 33283751237324762443823554423958000340146145984530851938681001185152501036029693000406479491804865220, 308439880831936, 
    317213546516928, 33283751113574826881503524441640741768576169950950084777294579894926474418183664229308439652855935108, 33283751113574826881503524498662970085759807968100323821326067926185781321970689891097753088469201028, 513259120171080175753226092837196870740343357413711208872743735545406521996694640062524841190256452314723440362954293053238810926744565900254343528567137832978193468141127, 365555209792773268890190957244931464517570876226, 286427637093312, 
    30946491887137527512635394397712577111473074314849674795086644395861206193842267413398017365635650130930164826770571877090783614662878288831690414054862765795048525934145094, 286449380365248, 286453008438208, 286453406897088, 308431006208960, 308431006208960, 
    299634913186752, 308431006208960, 308439880569792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [730842809600945818425847656311988328427132328770, 567902605415104, 567902605415104, 567902605415104, 132875738930441511880114602507350890244861752721157929325008698131872232389871549546074746903849472324, 567919386825408, 
    567919785284288, 567919785284288, 567916027187904, 730842809600946792059498852296260204163491732290, 567915490316992, 736462602495211039271591609267314827003162563394, 
    736462602495211039271591609267314827003162563394, 736462602495211363791383207733320235069000946498, 581096744948416, 581096744948416, 411227135938211784948209295296228910612930102083, 585511572869824, 
    581109629850304, 581096744948416, 456899062104803799221240840182661408700856795971, 581109629850304, 581109629850304, 736462602495231484018462312626081123176873497410, 
    572300651926464, 265755020079053651050093817564057552493173034142096504571744353372508200131434791297151662857538348100, 572313268392896, 572313268392896, 572313536828352, 572313536828352, 
    572314073699264, 563517979759296, 581096744948416, 572321724109760, 572313805263808, 572313536828352, 
    732180859417093159628416751358966341594014323522, 581095133811392, 581096744948416, 581096744948416, 581109227197120, 581109629850304, 
    457433236683831554579308718714658583575664001859, 581109629850304, 581110166721216, 581110166721216]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [565802424158785, 565733168267841, 990140584432576]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72670922213441, 265750967022100712688568472009397377696347321951545877532997366477235412440128935081288687756520338948, 72671123540033, 72670922213441, 72670922213441, 72671391975489, 
    581110165803712, 581110165934784, 72670922213441, 1464361710646224212118018748179132717475383284546, 72671123540033, 72670922213441, 
    72671391975489, 735038153274139565768570899841235981947375817282, 1464361729701956278782797883390316892924940456770, 1464361729701964067257796246572302972244914672450, 565733168267841, 565733638029889, 
    567916026270400, 567902605415104, 567919386825408, 567919785284288, 567919386825408, 145275264963009, 
    563508853871296, 563508853871296, 563517443805888, 563517443805888, 74869945468993, 145275264963009, 
    581101039915712, 581101039915712, 581109629850304, 581109629850304, 581096744948416, 581101308351168, 
    581109629850304, 572314072781760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [11440369494919715325275011960477919146747630146, 581126800360001, 563534614774337, 563534614774337, 563534614774337, 563534614774337, 
    22880651877470340693396783005751126471376639810, 583394610203201, 583394610203201, 581126800425537, 581126800425537, 581126800818753, 
    581126800818753, 581126532383297, 581126800818753, 581126800425537, 22880651877470340693396783005751126505467942722, 565733168267841, 
    565802424158785, 565733168267841, 565733168267841, 565733638029889, 1461551814199091523101041218842834364359778568003, 565733638029889, 
    565733168267841, 1461551814199018990391466676570213486574356727619, 1461551814199091682825016847599747819439971698499, 22886228254758257571886502450106103723936716610, 565733369594433, 565733705138753, 
    22925209981865619519409208342070645366873659202, 11507271985727082384786912202086861564878524994, 114269105871190017787265289338582760755732420418, 114269105871190017787265289338582760721104246594, 114269105871190017787265289338582831123134420802, 22925253538008585399534949514882997928408913730, 
    91433404124752454971087151419540713926465426242, 145702610014400, 849377322079168, 581126800818753, 581126331056705, 581126331056705, 
    581126800818753, 581126800425537, 581126800818753, 581126800556609, 581126331056705, 145689725112512, 
    145689725112512, 581126801343041, 581126532907585, 532345469047865660768623210452172779275560895643470799451774814268582418982072058175317214408426699844, 532345469047865660768623210452172779273998951876088448917398370632985506669843137228465139981595491396, 567900449555393, 
    145689725112512, 145689725112512, 91344027248952259365819571539208731765881442882, 91344201484158271372393461642735216458605794114, 145689725112512, 73120746639552, 
    73120746639552, 572298496066369, 145689725112512, 145689725112512]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_14_0
  · exact tv_b11_14_1
  · exact tv_b11_14_2
  · exact tv_b11_14_3
  · exact tv_b11_14_4
  · exact tv_b11_14_5
  · exact tv_b11_14_6
  · exact tv_b11_14_7
  · exact tv_b11_14_8
  · exact tv_b11_14_9
  · exact tv_b11_14_10
  · exact tv_b11_14_11
  · exact tv_b11_14_12
  · exact tv_b11_14_13
  · exact tv_b11_14_14
  · exact tv_b11_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88545322680897, 90744614373953, 45694401221847087400999984630773642043230000962, 1038105601325226425755159398259884754816672447901262635629669173324412258497029679114535357032701636, 2076195269845423313358769181551325633333386860215257060010495816457201890744074329741287652568861316, 539676945898339347431183000665951489235077234891212776954463777412077029041128370659036608333730824324, 
    11451824793418054830788595578823495186984735298, 11451955462677719969140690103133002886696407618, 563534346338881, 563534614774337, 11451563456061799052245864367341202208307810882, 45705377412077478058231608522965712185218568770, 
    531501942024138971432050989280639261308838171650065839030579138047505842236854601888139919678180234436, 11451432787134440913449299766917787152245854786, 11440630863678902642865118403379473102141395522, 11440369484451964996480985082908144254737977922, 1157240694338497, 1144050715542081, 
    90744681482817, 90744681482817, 90744681482817, 538768617409380387675483264215295903829515660072753042527675721351724070906504697882132396314399621252, 538768617409380387675483264215295903829515660072753042527675721351724070906504697882132396314399621252, 581126800360001, 
    90744614373953, 3957769494675904269259458121709599304855121671632245881239321978696997660274090767951609559632537108229325235033861708341905650991767839174488363435327476423796114162483984454, 1135246032651073, 1135263212520257, 1135263212520257, 1135263212520257, 
    1135263212520257, 182710702416228708806950648826534121477888881474, 70952935768641, 282059369628225, 282059369628225, 563534614774337, 
    563534614774337, 1126458529956417, 1126458529956417, 90744682007105, 563534614774337, 563534614774337, 
    1128650909180737, 960962154094212046835217857624440951243359382280315518482490121323070426323277455699297059175538939419593693333797690981723307594003155694007602096057773658415023000518012293814292953099664337727248978538383433816528626210766128166183634468110730717040738313246988552, 91366501614006607126956147618615554192749630274, 532150803464395994019471282958774145585060550316055734381728350257546591090122477707965320439827440516, 11440630821309779291363373867848675787951575618, 91366501614006607126956147618615554192749630274, 
    70952935768641, 70952935768641, 282059369628225, 282059369628225, 563534614774337, 563534614774337, 
    1126458529956417, 1126458529956417, 90744681941569, 563534614774337, 563534614774337]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [73152159892033, 73152428329537, 45716702052116209754376136214889942262678034242, 45672100752795752764220705974573161575069320003, 581126532383297, 581126800818753, 
    3958071411439552635652121272354445634660917244688260331573570631943746103765445682593843518814748360563658105267700421513862899870078377706635521434945085387637531047605779014, 3958071411439552635652123113636662683417450056840474450342661713213058513601405951097923375698389510712179848249931016211311138492670938565118938931319116201397776312474483270, 72639710302400, 532280556760699734867903915729482694186183203220721286079364966272539738698480049761187809785878461508, 72639710302400, 72646152753344, 
    72654742687936, 72639710302400, 22880651856534919897796543629063870979659274050, 2923059048494365635494605660826195472311457482563, 2923059048324151759600890908533661607584340182851, 73152495438401, 
    73152495438401, 73152495438401, 182733003226600873697241985004343890882752156482, 583325823615553, 73152428329537, 653694634904129, 
    6707484278935245677443871926042663546428451696335479928125394343202035005707895149821991662309759551252189069364600070056838241962833178935214887938163509470974848600417342337879195245494720323324317888258551516895588194714350094337988897126950803254021743626956331922360347596500797897894939281051763007230534452956350522827872758965828644697345849904484447419062309438034936906, 2926760986318959465246822282636117070324529451843, 2925868942219166618116724409036016356669282911043, 2923036747578943168864441935011821590815512265539, 11440325949410573410814607501085114534866256707, 581126800425537, 
    581126800425537, 73151959024193, 581126800818753, 90744682007105, 538768617409379679572675565121760137165086613868781210265583929922652793340206759935434558937520947332, 536692438010464554972587600588612638580513648363120199554392296090834891463236798122591239348106313860, 
    581126800818753, 581126800818753, 483070875915456208615035990446623592629548687235456895394391576110234042336562234422725376790026764094813997094116511138268023308945891622922124540703358460568374534468166, 538768617409379679572675565121760137165086613868781210265583929922652812705457536981553146620092366980, 538768617409379679572675565121760137165086613868781210265583929922652812705457536981553146620092366980, 581126800425537, 
    283958550204864, 283958550204864, 283958550204864, 469964748914436200411615462179390012196485388946442197664154329422414404061921788308312865783347626541518735207062553157324645899784720713590912046771979074689305709165194209293607637371328070457005008735457866791828138687817268916950786672396529301471520246988553, 1464361740590990722173661867003038113295356724035, 15008466959166475145822119029636068685455119171, 
    1464361740590992020252828260867086767019035525955, 283958550204864, 283958550204864, 182733003227849625855912549492006038705610437442, 91388802444275729480332299202731854412197663554, 73152160350785, 
    73135779483840, 581126800818753, 73151959024193, 90744681941569, 354602191426496, 354602191426496, 
    73135779483840, 73135779483840, 73135779483840, 90744681941569]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [4152422219672461153971700860087374445029905492763729035961579946243871562385329141021122841377664517, 3958131796911442227514390791491513552897291597941468676088585603218590741412052392497743371063667882832442413080517398995770062994268524264786044623475011209809701504500595270, 565733168267841, 2923059026716294152554543999170220596678291949379, 2923059026716211400007686390337118921810679760707, 2923059026716231844754557093695885217941709457219, 
    1128650909180737, 4122285245674505847143378038682325532780561649984459292953562054229768522310403176464356902532242023653823350575266670014422101491096919650886260548324734505213925934856370758, 1128683121689153, 45716702563868993202171186048492105709423433538, 565733168267841, 3970812310658842606243409763219332193309600602732137481385080615665610406047073591883834892880821803181990874724106368677817323589588485583953053910660384063170046271577619014, 
    3958131796911442227299865864612431999304107197970175138048915750089112447368475409398195146582488352193470728721156780018364778600166459930441362926863523134239434321300519494, 565733638029889, 365420098126900712146843956507366608516111468355, 284258392490561, 565733637636673, 73151959024193, 
    284258392883777, 565733638029889, 73151959024193, 3970812310658842606243409763219332193309600602732137481385080615665610406047073591883866721567952029527088819187987768350134620476579897755763955209014754322156570639628991046, 3958131796911442227299865864612431999304107197970175138048915750089112447368475409398226975269618578538568673185038179690682075487157872102252264225217893393225958689351891526, 565733168267841, 
    2923059026716221460084160277430812838527122868035, 960962154094212046835216466568230249808153488794632213862604341661820121257320324344402051223638643593944080528739691005858281203826562502150501679238709288476359217300901184775497239757900991242421444983351474027741018874838761778212934916998851562370514945246156553, 365421404811116996275681924507672079662707705667, 1128657553736257, 91388802464141517949917177629442814288502785859, 636102448859713, 
    636102449318465, 73152495438401, 73152495962689, 60384320188748996953713361270138551216993652362094270212453005521901530561086538586919199195267264894615697226892948375508917676914127092676730891911865429943158180195911, 73152495438401, 565733637636673, 
    23014456840475806813029255436305807732268602178, 565733637767745, 73152495438401, 7729134245387100980419546709765111513115876230993414493979970113377534627768159798236022005985189901341107893903411785006419240240198251733274650171862036768366276602146374, 91522607425890448388782005968676274816346493762, 91522607425890448388782005968676837768447398722, 
    7729134245387100980419546709765111513115876230993414493979970113377534627768159798236022005985189901341107893903411785006419240240198251733274650171862036768366276602146374, 73152495897153, 143489095455681, 143489095455681, 143497685390273, 143519160226753, 
    182866808208215607817498894509041692199440356162, 60384089844362716342876909802990039264043478959723066095727268653604847046350608090138070362204572658965826928964570103787886343050984043472881304278866562416202367544903, 182866808208215607817498894509041973675490808642, 182866808208215607817498894509042536627591713602, 60384089844362716342876909802990039264043478959723066095727268653604847046350612036895276022052881886479595672277537414454762368410015225749306927196629913877509297057351, 182866808208215607817498894509041692199440356162, 
    284226718032705, 284226718032705, 284226718032705, 284250340352833, 284252487836481, 365421404811148150175984863140104831836805482307, 
    284241750418241, 73152495438401, 1461685619180706259756309676630628670922303804226, 1461546935911079423121566222054685537540373546819, 565733638029889, 565733638554177, 
    3958133210304596500051360997841081017104641452421440471258132524900569410221524580399184397501832724621660867677744116012517055479035163929557090643335628524047267190347364934, 22880653047523204120500879143850686141842855746, 1128665941819969, 1128665941819969, 989321606928967874533254122535557125569888479846245085006947075618292445050922066283409278675220401348103969151551279576875460607391949060678409959012292023727503847779088711, 565716458684993, 
    989321606928967874533254122535557125569888479846245085028382690473651233902092527075614958403407624352813004741043526049342731159019815688669784130630009699710135833070025031, 1464361710646224212118018748179132717475383284546, 1464361710646224212118018748179128776823561851714, 732180859406542047643711596624480504912541684290, 565733705138753, 565733705138753, 
    73152428329537, 23014456840475806813029255436305807732268602178, 565733637767745, 636102448859713, 636102448859713, 94377113039711876845755382275474252474458641218, 
    636102448859713, 73151958567489, 735038153274139606333390711017191249011835769410, 73152428329537, 735038153274139606333390711607486637156465742402, 735038153274139606333390711607487059370541421122]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [22925209960930198089983668851268689126804690754, 45772279902884845118360063275314612843562668610, 11518335277941807972961200008526729570376749634, 11507271975259332055992885324517086672868872770, 14272542282624853759616689511842680221349249859, 114269105851583824987449965834799312324295399234, 
    91433404103817034175472404877669124905958904642, 114269105851583824987449965834799312289667225410, 22925253518402392599719663790031693963201615682, 114269105851583824987449965834799382691697399618, 114269105851583824987449965834799382691697399618, 22925253517073164603934710138195742436691547970, 
    531502440922005843165170292766406819743994871674924620132331644797675234542208788608137651636622500740, 11507228420279444475150122159390805960752632642, 91433404104813958975277399632210792462503908162, 91433404104813958975277399632210792462503908162, 75479248513869236564314003539780746969839170396924060909615428939136413543628659212020991815184273073790604162757204459116885335347130733818501345422236103748861493030471, 91433404104813958975277399632210792462503908162, 
    22925253518070089403739733226936518318145672002, 22925253518070089403739733226936518352505410370, 22925253518070089403739733226936518351431668546, 22925253518070089403739733226936518351431668546, 91433404104813958975277399632210792462503908162, 3971778498249206391465486329607687329162224467107849155903326710881160735299501866074158728442661737732266729621072562994197100735969053295787840607107806278748908022604445766, 
    91433404104813958975277399632211636890655265602, 3966947826345434818534600772790982864272500708725195642772778360100464469088748678847144189480367387792179418993735624207240346610018584753349330508276380483223119076928731206, 91433404104813958975277399632210792462503908162, 152285188477889, 152285188477889, 145277408252096, 
    145281703219392, 91433404104731206428419790799117843335544312642, 91433404104731530948211389265130006766464013122, 145277408252096, 145277408252096, 426756679930048, 
    145277408252096, 284226718032705, 284226718032705, 145277408252096, 145277408252096, 145281703219392, 
    145290293153984, 145277408252096, 145277408252096, 145281703219392, 91433404104813958975277399632219518220067935042, 145290293153984, 
    145290293153984, 797253407943141529731982798330850982027501575227953348303094888561537591720441465052122670994056981060, 145703012667584, 567915490316992, 567915490316992]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1130861005534145, 6707465088747716097056592077363274021238845272324962137946396857010650052059691504918520009667669386597626852455549003138538311871782493420495270203678150856562192241460833984355209338614664342616255357967562856222399300498188839190186415069120881937269492425752605443015459851858833872932387624858121588971332301730848261107451499000779361302936952479175440547021572413197602891, 531567574968091860714535146135474618407457192071345451360548408300679180699322904207957703030438577028, 531502440922011507987658956443774514321547210362790003662384839489877527930630668667403258707272415877, 960962154310961563796381349092987145361167787657713389617951164985618107792747851905544178417377376502624540592463359047841779352336736476888780957081269300635875520202041717980807598451319376577981618984626781317828060073964527763495183813038511046457835808246988553, 960962154310961563796381349092987145361167787657713389617951164985617650185498760628366169405430576423119591751901597642601230563096839412281911152878132034246409610264449725437613072785540109157407536065769053844567352915838813948599706524979644198654329120746988553, 
    960962154310961563796381349092987145361167787657713389617951164985617650185498760628366169405430576423119591751901597642601230563096839412281911152878150382165345507643486230424855418213302597986019460526176156589668939223792997829487137355783883685000921376746988553, 961665984013443560290120001100922282247251736714171625493199534749555314903314525057660227111873261293911351465540414345367529362332774153742517677748896040685271582176038903895640317351377058152018883560881978530918075604406119858766459822389098736674423072746988553, 1130856710566849, 1130856710435777, 531567701688025876530273738202096154635994909443782046235443451831044039793646845824294541534972643716, 1130856710435777, 
    531567574968091860714535146136942102229910339004679479244727808287624359292614613317371239671193781124, 531567574968091860714535146136942102229910339004679568030953599157819228775214254013450350720665994116, 531502440922011507987658956497442493914190586708596035656525231969881260845299452530031999506703858309, 960962154310961563796381349092987145361167787657713389617951164985618107792747851873885887028807399184255496952076649214872198421207922042025270278750072247314019796186671298878038803461214964549001765483761583468565447642730487216119267083340789008495034656246988553, 960962154310961563796381349092987145361167787657713389617951164985618107792747851873885887028807399184255496952076649214872198421207922042025270278750090308615620717999825234092589307395873737498291465697611016980686767310720016512109139048759418693391237408246988553, 145277408252096, 
    426889962328512, 563508853871296, 584685777486343008397113790163115288660430914245364379764898362283143544232497579839127728018441092, 563517443805888, 961665984013443560290120001100922282247251736714171625493199534749555598263309140831763854046376458491890149935539918097054594856183772749881171693479826814130228799703393319789543338862961131208073150824878541432858543962598205741909433810928197036127830304246988553, 299359498408896, 
    563517443805888]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [4280726152865126802493572857811643688837776284755806092635494255197199970487563435057776772223988869, 581126800818753, 531502440922011507987687974781368610325476896705720919805306584078495041462938923349436719347416712260, 531615475104112858878084760800675182941629683550929241525331067646940115892777286178222686895882237061, 3965981691964736737354108487317947643332031169096169509278040889521531456337817940099799166000360708524882529252844851905882015360819589735754003766456662302350528963223171654, 45850507034727868674423561698492932803686044482, 
    538769060929150387167604234746425968876630490252949458179303952396237642984131091797930913702621757572, 581126331056705, 45850507034727868674423561698497366051480671042, 538769060929150387167604234746425968876630490252949458179303952396237652591551658724832782917631754372, 581126331056705, 581126800818753, 
    299651555279425, 299651555279425, 581126800425537, 88545121813057, 299651555672641, 299651555672641, 
    581126800818753, 299651555672641, 88545121813057, 299651555672641, 581126331056705, 2925868931330130876765535821979424580814864712515, 
    1157240695321537, 145281703219392, 145281703219392, 1144050716525121, 145290293153984, 145290293153984, 
    581126800360001, 483126158568166773286091175980224065836216998944578023527326638667816362832807668750849379327271204353999101525529383735134240540785983859458844544482308073094390361354822, 581126800818753, 90744681482817, 90744682007105, 90744681482817, 
    581126800425537, 581126800556609, 90744681482817, 91522607425890448388782005968676837768447398722, 90744681941569, 90744681941569, 
    538769060929150387167604234746425968876630490247096670262383125333882457789284719599411428049803296900, 91522607425807695841924397135583044213336445762, 145277408252096, 426756679930048, 145290293153984, 536692881530235262567516270213278470292057524741435659551191491502064555912314757786568108460388663428, 
    581126801343041, 163280304755649, 308415973843777, 581094589088321, 286148179005888, 286156768940480, 
    286156768940480, 286156768940480, 286156768940480, 286156768940480, 286165358875584, 426889962328512, 
    90744681482817, 145707324412608, 145707324412608, 90744614373953, 581126800556609, 90744681941569, 
    91522607445746191838024292226416395344236516162, 91522607445746516357815890692428558775156216642, 308415973843777, 427169424610240, 427169424610240, 145703012667584, 
    145703012667584, 145703012667584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [532345374011783750598791458929309759981390344916459905798522614537972613552896258726727006453036817476, 532345469047865660768624092324406907120610135223090523682313516224697832559181252832426046135191518276, 532345469047865660768624092324406907119048191455708173147937072589100920246952331885573971708360309828, 532345469047865660768624092324406907119048191455708173147937072589100920246952331885573971708360309828, 365555209792773268929805038495146121329163457347, 145688118711233, 
    286425741288385, 567900449555393, 145277408252096, 145277408252096, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 581096744948416, 581101039915712, 581100771480256, 581109629850304, 
    581109361414848, 581109629850304, 581109361414848]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1135254622978881, 1135254622716737, 531567321528223829083114236531192012525116514603112004014657761339353863210663605599448713970871083908, 1135254622978881, 531567321528223829083114236531192012525116514603112314766445714103845885136136531000720871406960067460, 1135254622978881, 
    531567384888190836990969573736948910544147210671938209891201808785184776256483129453665818420185310084, 1135254622585665, 3957316615499754682076567428340131713358304911266936092898968258547390679017749547673178036328285734761804327806983895174880169631324255707929152158261548483495741816837680710, 182866808208132855270641285675948743072480760642, 91522607425807695841924397135583044213336445762, 3957316615499642208373604140914235235522875161835290193147831541939832804642287975329444602547409166457806537645738017605326008603781893974387840340489466602455325823129267782, 
    91522607425807695841924397135583044213336445762, 2923371238340020326829870083350405716595653550915, 960962612540416179297681272317137036444875860593623397668097447612218259087555972619434397913460824426266829514599082974054045285632946197571380954841489066219473396706323390489871622833774770412086119121359699051701786795931935238928230828227736910788829192249527112, 1135254622978881, 45850681268521611112905863822398878623373201986, 91522607435112327306771014844782722987621093954, 
    182867505105091116851181862729765459309229003330, 178406642153343911774761542110589500996457026, 730934800504538340765321210116402967671681946178, 730932012911388443307789499080874462018294288962, 91522607425808020361715995601595207644256146242, 91522607435112651826562613310650771505342845762, 
    1135248180134721, 1135248180527937, 1135248180134721, 1135248247907137, 1135248247382849, 1135248180527937, 
    3957316689209620870776808260935523474645644222461326429605951472388156237070390171320891371400321600029317030312724556157212893933446543905470468302872393152190626337090666054, 1135248180527937, 290823787799361, 572298764501825, 1135246032651073, 1135246033044289, 
    1135246033044289, 145277408252096, 286014896607424, 145277408252096, 145277408252096, 145277408252096, 
    435686055350720, 163419769541312, 581096744948416, 290280733675712, 290279929155776, 290280734462144]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [11774883299618267346435258064055031849468039746, 23549676765605515298271977582192924462690603842, 23549676765605515298271979869589189602675004226, 11774839743475301466311934752105280583136973378, 90718577115713, 92057827352349384869809643987467198607048840002, 
    7729193213548252452244917101174675024314794946757258605166766589413764145675061872145625752798639518361081653131436742973771153180602958750083699615914449943293190007336518, 92057827352349384869809643987467480083099292482, 92057827352349384869809643987468043035200197442, 7729193213548252452244917101174675024314794946757258605166766589413764145675061872145625752798639518361081653131436742973771153180602958750083699615914449943293190007336518, 92057827352349384869809643987467198607048840002, 149675454763200, 
    149675454763200, 92057827352266632322952035154374249480089244482, 365733966234513979144671484604210573759309959746, 366089384361115885470781157463745042957582996290, 149675454763200, 79236780069056, 
    12131651666569038890335451926717870306832159554, 79236780069056, 572299040789440, 366090448774993478697625632866510587116296161091, 149675454763200, 149675454763200, 
    290280733937856, 290280197591232, 290280734462144, 290280734462144, 572314072781760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [283745942835392, 72639710302400, 72639710302400, 1135254622978881, 1135254622716737, 90781669397184, 
    283745942835392, 72639710302400, 72639710302400, 90781669397184, 1135248180527937, 1135248247382849, 
    150086165222337, 853773741220673, 290823787799361, 572298496066369, 930132433671875323876521948840236477858989728666343910663177640253861027723673198853890970049192678533, 1135246032651073, 
    1135246033044289, 1135246033044289, 145277408252096, 286014896607424, 145277408252096, 145277408252096, 
    145277408252096, 163419769541312, 1135263212913473, 286014896607424, 145277408252096, 145277408252096, 
    90788111848128, 163424064508608, 73135779483840, 145703012667584, 73135779483840, 145703012667584]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [90744681482817, 90744614373953, 563534614512193, 563534614512193, 563534614512193, 88545121813057, 
    101709532656577, 88519553860161, 90744681482817, 92771453920961300177846494679189650057537262402, 90744681941569, 90744681941569, 
    588240024178366012649841856584208775512405191778624369731445050010868123886755007739306191764741858180, 980451500981820707584169725689562792406022030117741869241050738323941680398031158168027468038262501896242847369113719261879681551913085513021563085748461577554225765023390498820281649185849616968314605230500687442476235828091675289588519445757425571109798440499877512, 6244766299353608099518552330902488402640987473596040914503187486516068983979209439269603013355125956, 3966962863227027669513609145828533571934246840134843074904401864784838395956437661643092695638566766181182199536178511623963556475974330115728066360862480370795232263600561734, 440221545009600, 158471547785408, 
    158471547785408, 92771453920878547630988885846095856502426309442, 158471547785408, 88032873091264, 88032873091264, 310614997099329, 
    158471547785408, 158471547785408]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [369782736294336, 73152495438401, 73152495438401, 73152428329537, 73152495438401, 73152495438401, 
    94198707058185130793920196062632864102211392322, 90744145068609, 158471547785408, 158471547785408, 158488727654592, 158471547785408]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_15_0
  · exact tv_b11_15_1
  · exact tv_b11_15_2
  · exact tv_b11_15_3
  · exact tv_b11_15_4
  · exact tv_b11_15_5
  · exact tv_b11_15_6
  · exact tv_b11_15_7
  · exact tv_b11_15_8
  · exact tv_b11_15_9
  · exact tv_b11_15_10
  · exact tv_b11_15_11
  · exact tv_b11_15_12
  · exact tv_b11_15_13
  · exact tv_b11_15_14
  · exact tv_b11_15_15

private theorem tv_b11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 1, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_0
  · exact tv_b11_1
  · exact tv_b11_2
  · exact tv_b11_3
  · exact tv_b11_4
  · exact tv_b11_5
  · exact tv_b11_6
  · exact tv_b11_7
  · exact tv_b11_8
  · exact tv_b11_9
  · exact tv_b11_10
  · exact tv_b11_11
  · exact tv_b11_12
  · exact tv_b11_13
  · exact tv_b11_14
  · exact tv_b11_15


theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H4 := by
  intro M hFirst hM10 hRun _hUsed hForm hMissing hLoop tbl hNeSp1_raw hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hM10])
  have hNeSp1 : M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
    refine ⟨hNeSp1_raw, fun heq => ?_⟩
    have h10 := congrFun (congrFun heq 1) 0
    simp only [reindex23, swap23_1, hM10, Option.map_some, tblOfList] at h10
    have h23 : swap23 2 = 3 := by decide
    simp [h23] at h10
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  have hm1 : Matches M (baseTable.set 1 0 ⟨2, 1, true⟩) := matches_set hm0 hM10
  exact tv_b11 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R2.H2.R1.H4
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H4 := OMA.BB4H2.step_proof
