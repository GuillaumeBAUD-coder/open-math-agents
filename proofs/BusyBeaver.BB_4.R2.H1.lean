import OMAReductions.R_BusyBeaver_BB_4_R2

namespace OMA.BB4H1

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
  let extra := val / 2 % 16
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 32 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 32 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

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

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      | v :: rest => if checkCertificate tb v then some rest else none
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
        split at hCheck
        · rename_i hcert
          have hns := certificate_sound hcert
          obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 0, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581109144422496, 581109144422496, 580628108150880, 565226355427424, 580613075765344, 88038308972640, 
    564326525075489, 564326525075489, 564326525075489, 564332967526433, 564332967526433, 1461596415859588229274168971387781693606640225698, 
    74852759373920, 79250805885024, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 565426071341152, 565426071341152, 565426071341152, 565426071341152, 565426071341152, 
    580681795176544, 580613075699808, 565426071341152, 580615223314528, 565226355361888, 565226355361888, 
    565226355361888, 565226355361888, 565432513792096, 565226355361888, 565226355361888, 565226355361888, 
    565226355361888, 565432513792096, 565226355361888, 565226355361888, 565226355361888, 565226355361888, 
    565226355361888, 565432513792096, 567425378748512, 571789165076769, 571789165076769, 571892210737441, 
    571892210737441, 571892210737441, 565226355361888, 565226355361888, 565432513792096, 567425378748512, 
    1461596426387717800621932840897606914240223382946, 564195629343009, 1461518362985516617491241738907202425865784820003, 564195629343009, 567494164226465, 565295140970849, 
    580613075765344, 52819542442017, 52819542442017, 52819542442017, 580613075765344, 580613075765344, 
    580613075765344, 580613075765344, 580613075765344, 368230089832420255470096403832045081724608581026, 88038308972640, 88038308972640, 
    88038308972640, 1465075331751636301328260406549693658628469309859, 1462220839088483316933651542317791527809849508259, 88038308972640, 88038308972640, 1461518362935016347435633918330517302885698535843, 
    1461529513350150908612321994122575452995422552995, 1462934465657105616875019543921902366820648649123, 1461864025804187743912964267884319956287143059875, 1461596415840958275672450448874924353653766654883, 94198707057438813867571248047423337334292614562, 283759968651360, 
    730764756679094307405451802725419544341549023651, 72653736118368, 72653736118368, 72653736118368, 53052544417825, 53053618159649, 
    53060060610593, 53060060610593, 48526606666316474607371013562748753338763316642, 143022480296032, 2108623662504510070204107781643184112109953340074324104352718075588604665279070081783292380668167140, 1982522845157666168539792518005747172823886807700710547306401948220455846475868627646764080527396432705724512083352910555225433506073580917098799034396261485753862530903555110, 
    3879633488058325618509967203304951143764264210200574315979545834052943139808911600068901546472222365086304850688315023901913169747474363386660246628962823679318670925518630, 72653736118368, 730764756684411239671001069868705196529921687971, 72653736118368, 72653736118368, 72653736118368, 
    72653736118368, 580578715961440, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    88238024886368, 88238024886368, 981230230566952290560025527830757515894273542794107617909890711816643715308897946933729324951285403399797217495969714986520785305302020454082367843454859125740623310313254, 88238024886368, 88238024886368, 1978658307749821103328700726245097430261063721323732106580176110259740037117871553140590876470640418616038868118254787239665652380249828266138437933231165983806891274088830758, 
    234839012240743482438425180599805310686892120664697085952810785323620674474633946662983844691027363118222084365657628726069193907066004760722942067833106021445221997312273421640096921950965143658093584452869825215263058516373304633653429782405575644020774082250760, 3879633488002089196078177248519819412418189610171941248383584279078610963475525935831244902806645719829284537027357020384486818320339738950775552889807527202243058686711590, 580612001957984, 580612001957984, 88236951144544, 580578715961440, 
    580613075699808, 580613075699808, 580613075699808, 580613075699808, 88238024886368, 88238024886368, 
    3879633372773659626643202710028824009032412250497972752543180900099522018712372159044194260662346631570128232025409502476987221124425512230528339812468455402789543278001190, 61847696218876081133648532114025352445965965699128136345754243197869796781017837059089805213469755808881208089761515770997749801941454087039312964416763452440396302956608550, 53054727620704, 88238024886368, 88238024886368, 7560670634479108855437536186797703994533052022643170831690317376582005065704681182018955815859494584937138450825515204245214687641638535030254750139517515346099327115567681650210173947342896059612664445493720942052548138073172716309216709057021176971270122998760, 
    1978658307750130403652075570996415654783467132576529401807680038276438053742805961390969322726669932558694248300505059053931377135837164462413985020408440441201645626654807846, 1947364611321266876727316719347866800002413845499650686328054386393750453625704943217444943793190100595927182794598790367778751140456265791722014643578192065810595191543591, 1982522845157666168539792518005747172823886807700710547306401948220455846475868627646764080527396432705724512083352910555228338971328593561111913719307556127857124034024029222, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 580613075699808, 88238024886368, 88238024886368, 88238024886368, 88238024886368, 
    88238024886368, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 88238024886368, 
    1464356317835240673301050880071291293851556777378, 981230230566952290560025527830757515894273369586869471527078308877216446984635641412992370237874040080518895442553707121010587523920328253968106600089857419017820444448550, 88238024886368, 88238024886368, 1984455114034234518000883447562533043956712728316072082953094598375293920300786394631407366613014845816239096786113070854563938485661483058860802166347105919994362846692482086, 1984455114034234518000883447562533139224917999189858441034064745909400928425648154285791853377127625259002789167938794996489774155899010864748349387952890054061441672004213798, 
    3879633488058325618509967203304951143764264210200574315979545834052943139808911600068901546472222365086304850688315023901895631727998150076354970392555131935281070369036070, 580613075699808, 580613075699808, 580613075699808, 53054727620704, 88238024886368, 
    61847696221575429410295888569120643854412909826524738579857506073548754361694967025908869024264142883360701773454660475496462389243301672973253650324562060096769229388225574, 88238024886368, 88238024886368, 45287549105766743131829437917762702757679175775907093032975519288614747139894702321483902480160408932139300270593420054690420659313027841519451103825155684733738120927015, 1984455114034234518000883447562533043956712728489406246417648103009277729389443256817531137987933133184642446996676255230312825674492225972362789797847517765160281689717447718, 1984455114034234518000883447562533139224917999363192604498618250543384737514305016471915624752045912627406139378501979372238661344729753778250337019453301899227360515029179430, 
    580615223183456, 580615223183456, 88240172632160, 1978658307750130403652075570996415654783467132403914467227204079175831604568797629269250399466721205009062165440868000619225237045044793992638302884698640498410787277455841062, 88038308907104, 88038308907104, 
    88038308907104, 88038308907104, 88244467337312, 52888297637984, 88038308907104, 88038308907104, 
    88038308907104, 88038308907104, 88244467337312, 88038308907104, 88038308907104, 88038308907104, 
    88038308907104, 88003949168736, 88038308907104, 88038308907104, 88038308907104, 88038308907104, 
    88244467337312, 571789165076769, 571789165076769, 572923069998369, 571892210737441, 571892210737441, 
    571789165076769, 571789165076769, 572923069998369, 571892210737441, 565192095310177, 565192095310177, 
    88038308907104, 88038308907104, 88038308907104, 88038308907104, 981230230566952290560025527830757515894273391163736295352670473980301224500060592199779954471633833280449489003128356287052649403004872138299619163261375384492664695707430, 88038308907104, 
    88038308907104, 88038308907104, 88038308907104, 88244467337312, 16641875556787413440752102237660966418024304451120476121168989534958436253449609791385887167744250692, 158407053215840, 
    88038308907104, 88038308907104, 564092583682337, 564126976976161, 564195629343009, 1461529524151623746352644407962943318734080607139, 
    564092583682337, 564126976976161, 564195629343009, 571789165076769, 571789165076769, 572923069998369, 
    571892210737441, 568490630193569, 569624535115233, 567494164226465, 565192095310177, 565192095310177, 
    565226488604001, 565295140970849, 571789165076769, 571789165076769]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [565427177554977, 580681864448224, 565427177554977, 581094181243104, 580613144905952, 580613144905952, 
    158606838466784, 564326525108257, 564326525108257, 564326525108257, 567633784154593, 158606838466784, 
    565427177620513, 48526606666940848151114952046680785688296168866, 158469399513312, 1461591189122392161799558868651515407690055032226, 265783407324249547732710350891728110217247699866844112342111144685897210924626030152133609152915876196, 265783407324249547732710350891728110217247699866844112342111144685897210924626030152133609152915876196, 
    265783454844217486601109291989952361289037511378047360375732563616053409386551200061789689908646554820, 567427625920993, 567631603311009, 150085623417056, 158400680036576, 564126809325601, 
    564332967755809, 564332967755809, 564126809325601, 564332967755809, 564332967755809, 565195249550369, 
    265783850844012938265135989590185423348299673841699211219060449606000417465191764860106770785095051652, 565195249550369, 565263969027105, 265783787484045930357267132347011171619233005025482999452868779442958718079197734966123094648264551620, 265783787484045930357267132347016085069537498601132805324291077755023854597094315500759421353776655556, 564126809325601, 
    1461864036693207908492419494229423488157460996515, 1461864025804172167022388663401436050340878229923, 567631603311009, 3122383149676804049759275521854715809098465027829564872561427685221659802652342581735068105779620196, 580613144905952, 580613144905952, 
    158400680036576, 564326525304865, 564326525304865, 564326525304865, 564326525304865, 564326525304865, 
    565432582998496, 564326525075489, 564326525075489, 566525615473697, 143494996036064, 567494167366112, 
    145272975392801, 145272975392801, 564332967526433, 564332967526433, 565260747605025, 265783454844217486601109292097497962606543002212780826793395902243756278053090696723055757561688540868, 
    283957536490529, 290554807591201, 290554807591201, 567425447823840, 265783407324249547732709478517868270233747802868777155508476498066154980371001875195437839123078071140, 567494167366112, 
    145694019291616, 567425447823840, 3879633372941493632236854824865284473055870862811319310314301053647107967481105368342880365208480519098769991736811095204699253433046115888652864772372135472557009784497446, 145694019291616, 732180854653160467481549336735547450358271350178, 265783407324249547732709478517868270233747802868777155508476498066154980371001875195437839123078071140, 
    565295144110560, 565432582998496, 247330409031279710613461799202108127414303908845699778625613599995188362419887949548834525989676107135804042099129384937319571829813045977014915636734868500073187018078381350, 567425447823840, 145277404582049, 145277404582049, 
    145277404582049, 145419138507169, 564126809128993, 564126809128993, 564126809128993, 564332967755809, 
    564332967755809, 282857991307297, 282857991307297, 564126809128993, 564126809128993, 564126809128993, 
    564332967755809, 564332967755809, 282857991307297, 282857991307297, 283957536490529, 564126809128993, 
    564126809128993, 281758446125089, 281758446125089, 1461864025802214663426521738718235599187684629922, 290554807591201, 145419138507169, 
    46385726981044820237992771771979780935496768930, 1046199806413757721292132953433353256466842702591735998440965672284004502372244827601535580070773412]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [565432513792096, 565432513792096, 565191995623520, 215574208054305, 145273109610529, 145273109610529, 
    290829551018273, 290829551018273, 290554673373473, 290554673373473, 565191995623520, 565226355361888, 
    565432513792096, 145277404582049, 145277404582049, 145277404582049, 145419138507169, 282033457996065, 
    290829551018273, 36842365002017, 36842365002017, 145694016151969, 281758580351265, 281758580351265, 
    290554673373473, 36567487357217, 36567487357217, 145419138507169]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615292389600, 88236950094881, 580617442101472, 580684011931872, 265785434843201353880842708301710276394937755331885218706106391932234076389357765642913003459002261188, 265785434843669645873327073648629838204349005505444810729100944476668953281599786954287430198738575044, 
    265752994540108411252272281178803296057984686439969978397743290674732530520570601884281285423588728516, 368230612510777939390525540809631618146343453091, 1461864025804172166962968141256550210702026483106, 565253399382113, 567521309889697, 564085168276513, 
    564085168276513, 265785434843201353880842708301710276394937755331885218706106391932234076389357765642913003459002261188, 564085168276513, 567521309889697, 580617442101472, 580684011931872, 
    265751030381104730270277535265267887877453131408416701503771209473969036056203090369219587449305646020, 265751980780636284726588424648300224776703874990108203048915113030664600632604321607126399098510593508, 53052544417825, 580617442101472, 580684011931872, 53052544417825, 
    580615292389600, 1464356840508960158100059012405800438145049175458, 53056944474336, 158608985950432, 158608985950432, 88236950094881, 
    158608985950432, 580617442101472, 456791912024916798872480452023733297145563109635106014674315986135837947868575154557449151775528476356, 191040945127532847629300509356555999372904753959217172962180242200588377362382449860710078111619768004, 16641875742412316784231806828678235166152644401024590069405123379830038217139149702585180051110649540, 368230612510778101650421340042637699896163173283, 
    228773721278688, 158471546996960, 228773721278688, 158471546996960, 565253399382113, 567521309889697, 
    564085168276513, 564085168276513, 1464361718812918590195893712420361200856327529762, 580750586087648, 580750586087648, 580613147134176, 
    580681864448224, 8337158084876851524728486526446717380466427273229131032979319773293678249672692611109909853954395236, 53052544417825, 53052544417825, 53052544417825, 551485184257773599563979394960585784816016885902218952986827693365999045343718223884306423051718596, 
    551485184257712285974206110450973435119369786969070734288945538974214536237008896103453349679206340, 94199055511234149291888319685105895527166780706, 88239131100193, 53052544417825, 53053618192417, 53053618192417, 
    158606838466784, 580750586087648, 580681864513760, 265783787484047818631458183496871788330209802535828999731814274296434407192041260616204353456013843108, 266821493095122442477757434172849719351741393576423300524752595587458103174187310037942706560671423140, 228906865264864, 
    228769426311392, 158469399513312, 1464356840524906411622081501481989059042280482082, 1464356840524906411622081501481989059042280482082, 88315333444641, 33251439385686811160569273645768217023006205429333838491322128621638618418309872740634033866753186468, 
    22881261663389434989934144678244133902987306274, 52853902409761, 53060060839969, 1464357014729539784217367443855384685494252610850, 53060060839969, 52853902409761, 
    53060060839969, 1464356840504967920696874150607585680428928345378, 53060060839969, 88315333444641, 14278063002748050469660628056533714483183354275, 580617442101472, 
    580617442101472, 228773721278688, 53053618389025, 53053618389025, 1464356187166811775660673642385701729391224029603, 53053618389025, 
    53053618389025, 265751030381104730270277535171348923590327180352610351075114631035630380890672948255464693779530990532, 580617442101472, 580617442101472, 228773721278688, 1461596415843597270637536285950170490823745482146, 
    1461551814353199580678626195392294802562908431650, 145139831406625, 48526606666280067543483160247222248312920081315, 48526606670928471350681391262055554515336703394, 25690643587632484590639398200948451791352636706, 551485184257712285974206110450973435119393480691066119188348510082807928773508177476679040079499204, 
    145139831406625, 145139831406625, 578420566329824, 571892213877216, 431567050901984, 46737973905888, 
    150092065802720, 150092065802720, 290829562546656, 290829562546656, 571823494334944, 415284540732747162117829705486018152883658660353634906858820313996794274874649813785505762009043246788, 
    308436323322105728520880430614472526670198252297056079215405661587625647376905142339658993990704836, 282409058830929381025240105966198428225844447575241959027888932274248471530744559539422333607164583620, 16658095893543367776301115112215507906304085005593352917363430821584714426299048828388187499504934596, 132924142480290222037920208731226519360596889737175525387397836176819559177266540217599649247170207428, 132924143965289456161831515790488492358365496614244333027754491425579485813958723772711163300795981508, 2124839861371993694923700854630416521706274072057802480740247512064988884746220795650263274241203908, 
    290829562546656, 45761826407232773384909911167531607101641616802, 37941880883680, 143494996036064, 143494996036064, 565226424568288, 
    1978643219271028833475400513349780785764059803593180872443710857551188889353792323969574785904653037767804115528005628311087773628577868290155058038227938720790606828974778150, 1978643329836334248168994818800014454893647051513678405930581336126604633754343583090099797788096511017972610697812827896024573656435140898149870732927684226426843679307736870, 569624473307616, 567494167366112, 565226424568288, 569624473307616, 
    569624473307616, 265783439004225616607008523913951746123043096944065978590801312805534735164944434790780970954801356484, 145273109610529, 145273109610529, 44263968079905, 44263968079905, 
    9079562436641, 46028912996243421226257700624509243081980671394, 282395884165244226729414774623001986467241705634713756618298433685082678027957572408644772203204304676, 9079562436641, 52819542442017, 52819542442017, 
    53060060610593, 52819542442017, 52819542442017, 53060060610593, 88003948119073, 88003981640737, 
    88038307857441, 88313185960993, 88003948119073, 88003948119073, 88072701117473, 48527303564568802091240952205660977145227783586, 
    79448373724193, 149817185018145, 149817185018145, 143220115251553, 145281699553697, 365466006471646154284629664738497539979535199650, 
    365422798777823352328574893708493090720095675682, 282858226189345, 282858226189345, 205613567969359667089821938218005241891647923618, 182777604888385274562208632254372262045607798178, 66437869465220763316143089532826203076183816467155712307983644292368860857092621607968669950317704293, 
    283957737818209, 290554807591201, 290554807591201, 578420566329824, 576290260388320, 132891703662604454512555867168697828909069262007479854487672653047007674557035041520632238629986719748, 
    519108241116671364975733943594938990081016694416437229233565025866923789111582718647763874907112388, 94199045999288387650736148994912086716028839202, 132891703662604380751846365473047167435749987301996367908787982786085227027282609246610159744726554628, 569624473307616, 567494167366112, 145694019291616, 
    145694019291616, 732180855333725201323445606549341590771517138338, 265751030381104730270278304555510914993640317461704061837512124526542188883530744907537196163516285892, 565226426796512, 565295144110560, 565226426796512, 
    265751030381104730277649446130078588815480744728193591547434771899918675336881315900229901028277044164, 569624473307616, 569624473307616, 72709637148833, 143078381326497, 569624473307616, 
    74908660404385, 145277404582049, 145277404582049, 74908660404385, 145277404582049, 145419138507169, 
    519108241116671375794594113349721735189236322225678867642066138124051429292242894051115273120072644, 52819542442017, 52819542442017, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52819542442017, 52819542442017, 
    52819542442017, 52819542442017, 52819542442017, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52888329061409, 88313185960993, 
    88003948119073, 88003948119073, 75188168832417, 79448373724193, 94198707057438735426767669767552359172416220578, 142120603623713, 
    142120603623713, 1978884747222783456185379191100483388765130552759692159062909161175373963017227321870916896755428448238948496596172269137703625848199497771022380491967032003743911408926961446, 142120603623713, 142120603623713, 141021091995937, 145419138507169, 
    145419138507169, 52819542442017, 52819542442017, 9079562436641, 9079562436641, 142120603623713, 
    142120603623713, 149817185018145, 182777691998350889651594041784203797765525349794, 143220115251553, 141021091995937, 145419138507169, 
    154215231529377, 281758714560545, 281758714560545, 132891703662604380751846365473047167435750017093709682341667389272351434829293138794898694993952856068, 732180855333725201481901931577870265958605039010, 33218935722611761806880484664749187571624357581326648360467859742017385490025374371259118281484878788, 
    3879633489801668436839246347618501545532100722795991394438257467927692209038335033143219006737316285737360559053608605324929159894196974736212526167896676808794470483711782, 282858226189345, 3879633489801668436839246347618501545532100722795991394438257467927692209038335033143219006737316285737360559053608605324929159894196974736212526167896676808794470483711782, 282858226189345, 281758714560545, 182777604888390466720417882682038201753235105186, 
    283957737818209, 281758714560545, 3864655464910453568257511072522472795374019957926804551958585385415209227539367910602160259954495839082935926337352543737251365070445916081295318867984488941961159495014182, 290554807591201]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44540020172065, 88031799543904, 580681864448224, 158469399513312, 88238024886368, 158606838270176, 
    158606838466784, 290554673373473, 286156626862497, 290554673373473, 88244467337312, 88244467337312, 
    16662150931431873879035661911235814165396651080369372517640129643792835843873513268877340807908892356, 16658095893543367776301115112215507906304085008502699961369124825446449536103560471066026396424675012, 16609688878692677949137898630977887529057843484206301311570943228486459561411482292564389013962556612, 9079696662817, 36833774829601, 36833774829601, 
    730842809600955878539077721977649862829041814946, 213375184798753, 213375184798753, 143075160097825, 215574208054305, 145273109610529, 
    145273109610529, 290829551018273, 290829551018273, 22925253537925832852981985252140647472668608418, 290554673373473, 290554673373473, 
    74912955376033, 74912955376033, 145281699553697, 88003949168736, 88038308907104, 88244467337312, 
    61848403839529232214468087892861177496180681898162621828545991845241119140226260349645259114084563817393668864949974586350056562097850511024398857851488305833668287457640230, 61848403839529232214468088692028806377074693131851512655596566116882243662458874969589440778179728955253667615748336970604001179013544878104494319086170079731469325867925286, 91522607445766636584894994473903720401723757986, 145419138507169, 213380553513185, 213380553513185, 
    145206537619553, 145206537619553, 219977623279841, 145277404582049, 145277404582049, 368231298536001055806153132919557142912363414946, 
    22880608321244946802938973368425646347797407523, 145277404582049, 36834848572449, 36834848572449, 213380553513185, 143078381326497, 
    730842809600966263172408872890039092618472230306, 213380553513185, 143078381326497, 424699386933729, 215579576768737, 145277404582049, 
    215579576768737, 145277404582049, 282033457996065, 290829551018273, 44538946167073, 282033457996065, 
    282033457996065, 282033457996065, 36842364772641, 290829551018273, 290829551018273, 145694016151969, 
    22925253519321437720163327736398228749732554146, 182777604888390466720417882682038201753235105186, 281758580351265, 281758580351265, 281758580351265, 290554673373473, 
    290554673373473, 145419138507169]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨1, [], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_0
  · exact tv_b3_1
  · exact tv_b3_2
  · exact tv_b3_3
  · exact tv_b3_4
  · exact tv_b3_5
  · exact tv_b3_6
  · exact tv_b3_7
  · exact tv_b3_8
  · exact tv_b3_9
  · exact tv_b3_10
  · exact tv_b3_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 0, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 1, false⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 6) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580684011931872, 580684011931872, 580684011866336, 580684011931872, 158471546996960, 158471546996960, 
    1461864025806835825412678583131432658718136235426, 72637628284961, 580684011931872, 48526606668273970384418392398631364281246430626, 580684011931872, 48526606668273970384418392398631364281246430626, 
    580617440004320, 191040945127532847629300509356555999372904753959216939898340931399547246124086739196944426639436543684, 191040945127532847629300509356555999372904753959216939898340931399547246124086739196944426639436543684, 16641875742412316784231806828678235166152644401024368103843871060332942088075137478093709091165173444, 291962732323023105017040792183882716068349226897511959278923674891309007423795579466369408460912324, 158471546996960, 
    564085168276513, 567521314084001, 564085168276513, 565219040692321, 1464361709266407596774665301421331909814746903970, 286431641864672, 
    1461864025804172166982813300974795293326077097378, 567631740537312, 2078206948827074159375332889422874939590137389076423151170880409906798680308466164372084064303493988, 145274082689057, 145274082689057, 265783660764111914541556245094158712558996068906704784612334075791772037429517506785635263835129038532, 
    265783407324249547732709478571536249826391226881233229475747986536557712154044511808615161745599775588, 290829688375776, 290829688375776, 2124839861432418469047889324897625585685455500713237997818109983295315661194931613666459051307976388, 81924626647520, 72843721705569, 
    145274183353377, 75327556880864, 286431641864672, 1461864025804172197446119159257036339490260039074, 1461864025804172167022504753779530703569383110050, 567631740537312, 
    74836651540513, 1461864036693207908492535584607518141385965876642, 966163864949330575067660639101841903340483281678925007982733308351952403605275703249339514173968322356365245739748840004236785185550584347072057599281379955134014964848422, 145274183353377, 183045214854273533296870515141649719302077817763, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 
    265783534044183563548419933159424916287270605315382975296643102090471733918175766779926587316802070884, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 564085168047137, 81640091560289, 565425198925921, 
    565184680724577, 565184680724577, 72843990141025, 562985655369761, 564085168047137, 564085168047137, 
    1461864025806835825412678583131432658718136235426, 480481078833541558372121462767058613307873924962920186088194706406010124923268226939886532098741224425175891637053312431695069872734913197141436719131945492178930912715200195697501938512575117016823125087790228818151848229321345239175273267320316075823875138107022760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580683911268576, 565219911008289, 88031864553505, 580684012325088, 580684012325088, 158471681476832, 
    145277541943520, 71814270682145, 71814270682145, 282851783738401, 282851783738401, 282851783738401, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 286014896081120, 
    145277407725792, 149675722672352, 185544998536624000785095688723326351708275619234, 145277541943520, 730764756684370999216842858312302753416413708707, 145277541943520, 
    145277541943520, 145277541943520, 145277541943520, 145277541943520, 71814270682145, 71814270682145, 
    142251736435809, 282851783738401, 282851783738401, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 143078384470240, 143078384470240, 74908663548128, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 149675454236896, 149675454236896, 141908001687649, 
    286156764219872, 567631606712800, 145419141646816, 145419141646816, 145419141646816, 145419141646816, 
    564326525075489, 149817188157920, 154219798071776, 290554810730976, 154219798071776, 290554810730976, 
    154219798071776, 290554810730976, 149817188157920, 154219798071776, 567631606450656, 567631606450656, 
    1461685619845278754530431049358269582390216660258, 426898681760224, 426898681760224, 145423705049568, 286156764219872, 426898681760224, 
    286156898437600, 154219798071776, 154219798071776, 154219798071776, 154219798071776, 564326525075489, 
    564326525075489, 564326525075489, 564326558663713, 564326525075489, 286156764219872]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [732180859417103219741646552571096028979260872098, 290829688375776, 81922479163872, 290554810730976, 290554810730976, 290554676513248, 
    290554810730976, 290554810730976, 290554810730976, 154215503104480, 290314560735712, 290348652300768, 
    290555079166432, 290555079166432]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [564332967526433, 1461596415859588307719953399713296801748937610658, 564092482946081, 564126842684449, 564092482946081, 564126842684449, 
    564092482946081, 564332967526433, 480481077047106023417608928812220475712048137818800171737751120387406436719275197176533274904672894140098364687896727385014741869774464733091026800344425099455506766902882340132742928865222891890352906868447283992574381794009696294307269548711554727666518016249598761, 265750974941130293871093805119180229696112387423225465719412172432125437306600020704316720672220716421, 265750998701117567785135337399778734287374456057272334838877809611977130463277651675415980239042197253, 73121889781984, 
    265785688283061832415414176102327130081379350843061641403582205801031731801182001067991249762921268932, 265783692444095654529754258157132933653233741495699195484660648685283563346634496493094720695008020164, 265783660764111914541557124390336307247081315727011007187349948896249769008261544033900408960472106692, 265783660764111914541556245094158712558996068903636332651711142391133821283244734069739918465278985924, 265785688283061832415413296806149484211520353100894231679781945032085677093148826436962689672593065668, 73121889781984, 
    37939664980192, 73121889585376, 73121889585376, 564126842684449, 564401720788001, 282858024862753, 
    282858226189345, 81928921614816, 290829688375776, 81928921614816, 265751220461005753993844546341317621682939675694486723364493120751120303530710484590202875928299839941, 565226355820641, 
    362922862184928, 265783660764111914541556245094158712558996068906704784612334075791772037429517506785635263835129038532, 72640786598112, 74908663548128, 74908663548128, 74908663548128, 
    286014896081120, 730842809590322014007978904938306793188778576291, 290554810730976, 154219798071776, 75320912840928, 74839944071392, 
    74839944071392, 286152335034592, 145273514952928, 145273515149536, 145273246976224, 74839876962528, 
    215577432426720, 215577432426720, 215577432426720, 356315054999776, 74839876962528, 145273515411680, 
    145273515411680]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [576290260388320, 576290260388320, 730753606960454507600780929026791259587553564066, 265783407324249547732709478517868270233747802871595241414039453732061746482578784331726944183223731044, 265801654994861121644809591719385693117368448515566517904420884528327316475311152927895313741653362276, 576290260388320, 
    154353076144608, 286157032393184, 265783407324249547732710350944544528245248527191015350476459753188153791862184825727933514881230324580, 265783407324249547732709478517868270233747802871595241414039454375543096160799972335511354263470228324, 154078197975520, 154078197975520, 
    1461864025123623010071203430819158246129893160354, 290829688375776, 567494167366112, 567494167366112, 567494167366112, 732180859417113604374977703483485258768691271074, 
    290829688375776, 145694019291616, 145694019291616, 91522971547888857395043688949275964138152564002, 290829688375776, 290829688375776, 
    290829688375776, 567494167300576, 567494167366112, 1461685634813684030859603079684764069293292295458, 567494167366112, 732178425706991521291988479732015723888100545954, 
    732180864850997610578894585201201794802640262562, 132932253051187826038216600160633821912733318628792445810531936654202295780415130060727081661416539940, 132928197518239160296252839338300567627568738030203427658482599210172780792077480314606629879088825668, 732180864850997610578894585201203483658942977442, 132936307594016172501722152760385591613218619609478603005418557076013995662884815527341765537793459524, 132875514200551213644534064180571755713789664955394532205846980777143850355863748065873559265606137893, 
    145694019291616, 732180854653160467481684471974821248125706474914, 265783407324244827047202888824329598517106474595004228889892674607339666133582215839654971309214148964, 265783660764111914541557124329959829405642254442371872873000396231510036260982346041722933822489898180, 265783660764111914541556245033782234717557007618997198337361589726394088535965536077562443327296777412, 265783660764111914541556245033782234717557007618997198337022897158691404697003462356296596336924699844, 
    145694019291616, 732180854653160467481549072283024409658139383202, 732180855333725201323445342096674434883309311394, 145694019291616, 732180855333725201323445342096674434883309311394, 91522607445766636584894994473903720401723757986, 
    290829688375776, 73126184749536, 265783407324249547732709478517868270233747802871595241371364190209093951593101274134627687044344857444, 24307904844490680048574324743678009382734960034, 37941812464096, 73126184552928, 
    73126184552928, 265783407324249547732709478517868270233747802868776811461856685138289891984819223577938243243707876196, 81922479163872, 571892214270432, 290554810730976, 149679749204448, 
    290554810730976, 290554810730976, 149817188157920, 290554810730976, 16658095707978888284936390092739011560132949983119440263989784339057180843171274592131891862505146052, 16658095707978888284936390092739011560132949983119440263989784339057190394188305009906401566779393732, 
    435484388493792, 154009143347680, 290829688637920, 1461864025804187743912926824097645053462578771362, 567494167497184, 732178425717625385822932270923380545371777832354, 
    435553040861664, 91522966103370986660028273535286467363101775138, 145281971128800, 290554810730976, 732180864861631475109838376392570556951023883682, 568490633333216, 
    154352942057952, 290554810730976, 567494167759328, 290554810730976, 154215503104480, 290554810730976, 
    290554676513248, 290554676513248, 149817188157920, 290554810730976, 1676866272193029428224668747729329813283935139089169660721959467708462956904925217182976993634276637624988923245421837832753016488666279681327020981945238313850569392335469385868558290514247917128265678796435960394703167552783795695057493068667094534243801093991211133478246567138606766983193216521756177038720270235733818648207672939993184210947413055947362204031115085924882731, 290554810730976, 
    290554810730976, 290554810730976, 290554810730976, 145281836911072, 72610988165217, 283717220698209, 
    265783660764111914541556245033782234717557007622065650297984523127032304682238308793457788697146830020, 145281836911072, 294815552506336, 145281836911072, 294815552506336, 145281836911072, 
    145281836911072, 290554810730976, 145281836911072, 154352942057952, 74912958515680, 145281702693344, 
    145281702693344, 154215503104480, 431430006082016, 281758583491040, 281758986144224, 281758986144224, 
    290314560735712, 183045214849122755164619662596591743744591799203, 290348652300768, 154352942057952, 154352942057952, 145419141646816, 
    145419141646816, 290554810730976, 290554810730976, 290554810730976, 435828052593120, 45398345648608, 
    290554676513248, 81716320930272, 290555079166432, 145419543841248, 435827583224288, 508464070134240, 
    145419544300000, 72851508431328, 149679749204448, 145282105084384, 290417237559776, 74912958515680, 
    145281971128800, 145281702693344, 145281702693344, 154353076144608, 154215234669024, 145281971128800]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [182699551982448538483871585870120436487502181794, 177061641717984, 141979275102432, 564092482946081, 564092449357857, 265783407324249547732710350998212508637607160194970589769867792677302300990370559273977811455718369636, 
    265783407324249547732710350998212508637607160194970589769867792677302300990370559273977811455718369636, 564161202390049, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 564092449357857, 
    1978658779495010857921506726200232164528366838699012772719397962302619655919008423645291325574162769445726095809830140478843302902742075953910171079142816872601772234632061734, 1978658779495010857921506726200232164528366838699012772719397962302619655919008423775152369066431120893736001765391488026156327108997908966715037020333792788594842191700943654, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 39724693719264, 39724693719264, 
    282858091979041, 71545633899553, 71545633899553, 71545633899553, 71820713133089, 71820713133089, 
    45688651768710295826204242405163238663634551203, 71545633899553, 71545633899553, 71683148358945, 71820713133089, 71820713133089, 
    365387953549772900424076687473194784146648465827, 294819981298144, 730764756684390470404493508777943231771598389667, 3880105118047768846394620327283782093906973322392707030678619764866093703414944052293556817807879468197293099426186646868134473607109491904001994574569304319993241500902182, 286157032393184, 1461529513368780940654873184803806379990997015970, 
    265750982861126169859575712062919439118885473262705519378809920469697500622777743723809452544267944612, 72029021997536, 177061641717984, 141979275102432, 423600280701408, 265750982861126169859575712060836187381901825641925603183642976093626336587611897850977116665022284452, 
    36426158835936, 141979275102432, 141908408076512, 72020230473952, 564126809128993, 564332967755809, 
    564332967755809, 282857991307297, 282857991307297, 2108651412944397531248975787398815768503372911912022126785821771912679366014506495951811615950161604, 288883718757581814639357502268263608443556619061697295821962734157977466187276923088106278310172477124, 365400497777422781968571539224039523926692894498, 
    265751093741551359815597357742025736477031684847739505043953262227883620024068628245151179779112469156, 1461596415859588307715001639556155280649341115810, 564126842684449, 564126842684449, 564333001114657, 564126809096225, 
    564332967526433, 265751093741560801186412709230651528542611869959522053443466751091364939718712477893831119560315273892, 265750998701117921836539515394583362414103864088443582216233754924302842966324483738004218339540350213, 265751093741560801186412709230638937826269143936509197155749002189158621896686769844285999157084979876, 265750998701117685802269164924509481987166814854404721376687276611779660223477377309629506086103545893, 265751093741557024638086212107827582504101473898755778006348080600805244750335079359970926132231701156, 
    564126976976161, 265750998701117685802269164924509481987166814854404721376687276611779650597255631826510417815240570917, 91433229900140350837969651909778910487111015842, 73119742298336, 4152489478245602117955526758703453987170327755107281322127504604204307814394009096889994354017206948, 4152485765747535248354634534461186861078629238806133865958687819838338866034090278208847334775489188, 
    73119742298336, 37935370012896, 73119742101728, 73119742101728, 71545633899553, 45699802183844857002892318197230395972613308835, 
    71545633899553, 282858024862753, 564126809128993, 564332967755809, 564332967755809, 282857991307297, 
    282857991307297, 265751980780607960614139557135854550829071753816617439658305889261277971747595721958358078651001242276, 265751980780609848888302800541157235821504972276301404728686813571001389699192895080688048138804298404, 71545633899553, 282858226189345, 142120603623713, 
    81924626647520, 81924626647520, 1046199806655456814187289393594413257587936909703652206502778551305981597252821962769338994877301412, 81924626647520, 81924626647520, 989329153831664413307367360831762574958688210718350727286345516776997829561037152940185599306628707724280030804318251811574814218121628005406517354647144357090647193510881062, 
    290829688375776, 290829688375776, 143078384470240, 72709640292576, 143078384470240, 143078384470240, 
    143078384470240, 213380556654816, 143078384470240, 564332967526433, 566531992915041, 143078384470240, 
    72709640292576, 143078384470240, 283824462760416, 143078384470240, 283957740964320, 565432514250849, 
    143224681794016, 283957740964320, 213380556654816, 143078384470240, 424699390069216, 213380556654816, 
    143078384470240, 424699390069216, 72709640292576, 143078384470240, 1462216657701427443207918435248570820287176655267, 143078384470240, 
    143078384470240, 143078384470240, 143078384470240, 565501300779361, 2056190593532831424095101229665769924006714840994099866984816984117853030709734507365486021127700995869072132569587419514032725628522790310616124465537295995408585916068904742, 565226355361889, 
    565226355361889, 565432715118689, 61847696334955086639193660342125235548647797212825073714617519020510908910759352988928277499025276705475720542289689917751744724064655541740266170897703757862161917835695910, 213380556654816, 213380556654816, 213380556654816, 
    217783032351200, 37701493983329, 72640920815840, 72640920815840, 217778670274784, 296952365844960, 
    730845771408054078489696041063275168424015169955, 5798215870075658211420407184615404719312994723, 1978658307751508209731300482704683227442739315060202944742355810210052925488133860707147554529465363902491473403150856877441974211778165720607072601573412913097483662964512550, 74908663548128, 74908663548128, 145277407725792, 
    145277407725792, 74908663548128, 145277407725792, 145277407725792, 145277407725792, 286023486015968, 
    294819847473632, 730842809590332398641310055850696022978208991651, 86052291742176, 290554810730976, 86052291742176, 86052291742176, 
    154219798071776, 154219798071776, 154219798071776, 154219798071776, 290554810730976, 39724693719264, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277810378976, 145277810378976, 1461864025802879279964657466935371208675916518818, 145277810116832, 145277810116832, 1461864025802214663426512048385318981052773440930, 
    145277541943520, 39724693719264, 145277809985760, 286514784692988995531271664605112892427522164224121171407313906901527830849294242339521686549914240324, 74908663548128, 145277407725792, 
    145277407725792, 74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277810378976, 
    36567487357217, 145419544300000, 426898815846880, 145419544037856, 145419544037856, 426898681760224, 
    149675454236896, 149675454236896, 149675454236896, 149675454236896, 92771453940858257491769166654789332028654884258, 79716811868384, 
    44542070163936, 149675454236896, 149675722672352, 184758223112416, 219977626421472]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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
private theorem tv_b9_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581093006804001, 580719347894496, 567624392152225, 564325454480417, 567624392152225, 265783407324725392828938334356413918702589570505240580092137003913060430364252468447195058293360897732, 
    53052547564577, 268378631573369239685731794257359673725133098866138037034041463652942340877849672179051677969763348164, 580577608599648, 25690556475346207874670512835084176336689300898, 1464356230722953767981422770040175273810497897890, 565425335307489, 
    25690556480663140140219779978369828525061965218, 25696131666962772796005163907937990615438460322, 567624358565025, 2108619733444055736041387255672459763647159296912187452323279329495591523570302109936254350383984324, 2108619733444055736040946318305748046402426023840951589531717250155100031539309240135736206435055749, 283125355676705, 
    132877511029518764303025562730626967391514495691560812747115827995374115282195062323066026476250364037, 265783439004225734624146363710623967609188187511895733582098320529620450457624195750531963242042961604, 265751220461002921582585052678911041117164793722668037809534702820203681792926165111020349837155577540, 265783439004708896775665392355877861128863183497789899809980194996863786468660290629165109563100788869, 265783439004708896775666271652055500601000462375108217635260273982831077803816419676835160954037106821, 284225102417121, 
    37934531349729, 45761173065078225069484203645041179491656014755, 1461592234469822369363201861400975379011580730275, 148523311832908097666560981655091297310680030115, 2111201651623782884804442453882779589530527947263467818822007706433021200782081037312404466827819141, 45631112750369, 
    327106089461025, 44531332449313, 1978658307751508196001678975318213461311629267118586113391266038151901087615461667071756707642437925289038499413504697980158517083489887297903092425027280893129717441776670503, 267859582771376891514114293355240242126695240497403767703847273165407105296402001050331616856886030020, 398918407322093383054215344794859828004161662284038492408623394742409745077377297117821088909119008452, 14275275409577789394897237455367834695648150946, 
    36835019719713, 36835019719713, 283125590787105, 283125590787105, 36835019719713, 142388236649505, 
    283125590787105, 22925253537925832852675517834519870505744860578, 2044581912755849578502657307445964262543947881133363500367789867661303290797627774532897232369771272821036222790478313393549200981365065855198051450661500012867862421080874023, 284225102417121, 265752994540085751962201258592594098555013113341775792559779018567964142756149149336371338760031383236, 265752994540085751962201258592594098555013113341775792559779018567964142756149149336371338760031383236, 
    282621948258170769435039093683824267660797578775802827573373488661714073627937904565901902822581997317, 282621948258170769435039093683824267660797578775802827573373488661714073627937904565901902822581997317, 36835019719713, 142388236649505, 580578715961440, 580578715961440, 
    580578715961440, 87997506914400, 368230089831912706516036393544253044181988541858, 265783660764111914541556239077474971753699818838349150004434546592294914429935427928464341037721136836, 265751220461002921582584174242141720904728610158548674549963024254931910758488207246171296124444421828, 580681795176544, 
    228842373646560, 580680791098401, 564327634536544, 265752994540108411252272281240018335430790194086664623538017390049432832720301743718323381370788585156, 567633686694368, 1464361708248215067887250603388447620491794451874, 
    1464361708248215067887250603388447620491794451874, 286149248029857, 564327634536544, 564326558664800, 565426071341152, 565426071341152, 
    565426071341152, 565426071341152, 265751220461002921582584613031549408829008720137533474982836024494046929158912484468393692654750215876, 567625096693984, 286149248029857, 142113359004705, 
    282850713142305, 154207986922913, 290547294545185, 91522967448539455417113466693725738151331500835, 91522303217359225745232786186492031339782738723, 91523348564790406868192545673286061731728331555, 
    145411893892257, 286149248029857, 142113359004705, 580684011931872, 48526606668273970384419034640617149741071345058, 580617442101472, 
    191040945127532847629300509356555999372904753959217528107083240304137531716687339119319421523101507268, 16641875742412316784231806828678235166152644401024945214308121483379192571444038961194523462592388804, 368230612510778101650421373099329180773246043043, 88104952400096, 158471546996960, 567521313035425, 
    535265009258875743553122105331639457575449674705736344746301452315084401860726208787763004985911300, 564085171422241, 36834751054881, 265786306042740395551258923833542319640633054985375422171229960750110719102439102301613133726708430981, 78616327160865, 480782587427450532404815488919616092825910528637996136889167788205389108904255060763094162829867877286294879291136382754360313420838132068894623746020215082654846997781416201990612594611578967733141081788286866791845535729041606744855141555933864377165283338248095560, 
    1984741937021275166721257406612242987235293405082631412421611953025815149369533941603105313156680048848524276041329882453748412624619811051077120937111424165451567254139283238, 2076211109836584743643006813666602705894022748450855757475236467044349003098781849342681706108381220, 2111201651623782884913475179910867452046247974355933709749728879255226990189555084567466038131193989, 565192196950112, 565192196950112, 565192196950112, 
    265783660764111914541556244980219074599402188272702981254962932184620303338385768903057094260920187013, 265751220461005753993843162257540103398796966885230240385066222289660659435507614516313729081362339012, 265751220461005753993843162244123108500636110882457029208402693573726557527147480112388734325306152132, 132875735960437393561945257729544290316199400617296180146062489674384964442074380407561992383733372004, 1461864025804172166982813338753871271471314642338, 265752994540108411252272061361467382189546970026633266357984394373250367223195324709261387785262930788, 
    1978643683645311575188496590646588790616064811147483736863185483200031051732883082320578534694484231954115798533549901580173502081472011362659733470232577338776236591330343974, 731110419564195731373076798820378824998723823010, 265752994540108411252271848460590725947186740043184533195261694608736412718816926991530744815391940292, 1461864025804172166982813338753871271471314642338, 567631740537312, 2078206948827074159375332889422874939590137389076767197795902720528311869811700422715107678737996644, 
    251239652721697, 286424025007137, 145274085835809, 145274085835809, 564600567268385, 564188250407969, 
    567486785393825, 568620656759969, 568483217806497, 567486785393825, 142388102202401, 182710702416187819312595634354649713964514543010, 
    45631079195937, 1461596415838445843446165928985569511505004070306, 36834851816481, 36834851816481, 1461529513368761145097522061466239338860312528802, 1038105570387270466635219360532557730474141494531006707692189950057752106647723891460985526346160164, 
    36834751054881, 989321607749569750738379990335147920483158569472289591737763439250443933398487300940836500965867066978262364981926787685706523822675225587936283995348555787663735885523839782, 564164627105888, 564164627105888, 45631112750369, 1978884747337952134629729879204792949784336375290505937631986258070695446502999381402510266199021063884559568478794520046947675833928593096766328723409919238414155728120964262, 
    36834751054881, 36834851816481, 36834986165281, 1461551814199029293895237237770157240028683044258, 36834751054881, 265751220461002921582585712231441425034812505616828128537106091725726762528973151900012055970606821060, 
    265751220461002921582585052732474200836242977533939340246944485565748864373243502275125179256638877380, 36834851816481, 72019223905313, 72019257492513, 265751220461002921582585052732474200836242977533939340246944485565748864373243502275125179256638877380, 565192196950112, 
    565432715118688, 565226556688480, 74905442321441, 145274186499105, 145274186499105, 154207986922913, 
    37934262682657, 37934262682657, 37934363444257, 37934363444257, 108303241972961, 143075163243553, 
    91433404103568131932107989405854937229602063267, 565192196950112, 565192196950112, 145274186499105, 145274186499105, 1039103489897385333647715559967426470721694953408481929834904565971687462094325748829531855478390436, 
    731110419564195731412768251625114235246324786594, 1461864025804172167022504791558606681714620638626, 567631740537312, 1461551825066880383686554891110541079938916156706, 1461864036693207908492535622386594119531203405218, 145274186499105, 
    145274186499105, 183045214854273533296870477362573741156840252323, 44531332449313, 292216171708600680540126683266424055238778200675284162562738366451503775955294142131871352572948164, 149672233010209, 1461529513352788929998496723580712561679373174178, 
    3880343294172176471769792434163645101475708675294007114254948208222756466024251595705044914795390410677972488433651135771980530398476496839561297658827846942626340321345319, 81914962980321, 290547294545185, 145274320721057, 564085171192865, 564188250506273, 
    564085171192865, 564085171192865, 564085171192865, 1978643683645311575188496590646588790616064811190807196630843264860531480355809822412679126048406708102877152119232321122998374106360189830643375003940467550212200451382689062, 1461864025806835825412678620910508636863373796770, 36834985935905, 
    275742580346025275209528179282281242264944832183647512720891402308691817960880529363972377999912644, 36834985935905]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580578682407008, 580578682407008, 368229959163483808875659170025815986497382778274, 265750998701117921836539516307040573723322637140751136469259050119505247240211944465227087518514051205, 265783439004225734624145485273120907081441486658137271080771675978972215107089454666709908822376872069, 265783439004708896775665392463213821912018517457167757406915753125372513997421822420935438830562474117, 
    580681862285408, 158469397416032, 564429841336416, 567625298151648, 1461529513347805279558919076318739648600095589794, 564429841336416, 
    565426272667744, 565426272667744, 265783439004225734624145485273120907081441486658137271080771675978972215107089454666709908822376872069, 565426272667744, 580613073668192, 565219911010400, 
    580578682374240, 580647401883744, 580647401883744, 580647401883744, 580716121426016, 256629473692336120754385040599383764514766139804504133694386234988788614406406317709385938956569271164103756764774143962370067021973615355146075844369313618274583289943846, 
    158471546998945, 158471546998945, 75479248504339073950171048391661825880178789692262469035702234195840383686552171766340467155723554169710833276663304945997536687306053926938794250283821889991276617160486, 1978658307751508196001678975318213461311629267291875325060185711835874134221411632355604429293295379056704225118545765339916717413116621173675929558888096410582037793608390439, 1877108318434229920971104870761035114202571889840181308321990150220444739798789127269214308375061682116701274991469347955723422280776872494241737301125778726230406457938847769262903292929156014712498820223593411176404490089222257470614510110819624849244198092950760, 158471546998945, 
    158471546998945, 580578682374240, 16641879454910385497850024458770165664584740870729962077226194988769475594157483740845163673971284709, 88031864555616, 580613074061408, 580613074061408, 
    36425756577953, 141978872844449, 141978872844449, 141978872844449, 141978872844449, 282851783739488, 
    39724291461281, 70714758006880, 70714758006880, 281752271063136, 281752271063136, 281752271063136, 
    215987738118368, 286150321768672, 290548372474208, 36354818312288, 36354818312288, 39653353195616, 
    39653353195616, 185542907839763894701950904691730227559917946274, 283744934561888, 71814270683232, 142251736434784, 282851783739488, 
    72913783359584, 72913783359584, 72913783359584, 143351247013984, 283951296415840, 72913783359584, 
    72913783359584, 72913783359584, 143351247013984, 283951296415840, 81709884770656, 81709884770656, 
    70714758006880, 70714758006880, 143351247013984, 281752271063136, 281752271063136, 75112808712416, 
    145550274463968, 286150321768672, 81709884770656, 81709884770656, 154346375875040, 290548372474208, 
    70714758006880, 70714758006880, 8563518823510435908909445239935494456626120098, 14272531372405758373204250773708350635322639778, 14272531372904220773106738678540179320240342434, 79235771795552, 
    730775907099505560393530936465553143467201791906, 283951296415840, 283951296415840, 281752271063136, 286150321768672, 290548372474208, 
    36354784757856, 36354784757856, 141908001687648, 141908001687648, 36355287582816, 36355287582816, 
    16609467118804845791833647426306026642516407484685348973863836475956874854255937867710808652339033381, 142120606769441, 39653319641184, 39653319641184, 145206536570976, 145206536570976, 
    265752994540108411252272061348050387291386114026042089055611872102402986512060962281321351471893850213, 36354784757856, 141907901024352, 36354784757856, 72569982552160, 567631606718881, 
    39653420304480, 145206536570976, 145206536570976, 565426071341152, 1978658779495010857921506726799607886189048659443339760563504402128171071409623755649598519142699761066729546220487374599229886367408112308666248925217645539526399451152230182, 72844862556256, 
    36320929941600, 1978643212360718326897592662703287971240786565707137314887695921102686767736591903790274290808410996536443022555474938406418973323792122902568910189291432414213372578659718950, 36320929941600, 36561447290976, 36561447290976, 36561447290976, 
    142125170177441, 282858229343521, 308182880614109742061387067405084488157637199255304290708859492378642918097288785780397782507043781, 72604310833248, 72604310833248, 72707490711648, 
    308182880614109742061387067405084488157637199255304290708859492378642918097288785780397782507043781, 72845063882848, 72845063882848, 72604310833248, 72638702028896, 72638702028896, 
    72638702028896, 72638702028896, 72707490711648, 72845063882848, 74837725284448, 74837725284448, 
    567631606456737, 567631606456737, 1461685619845278754530431049358269582802549772579, 72638702028896, 143007446206560, 72638702028896, 
    72638702028896, 81709884770656, 81709884770656, 79235771795552, 79235771795552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [71610128666785, 282713139971105, 565432513792096, 565432513792096, 565432513792096, 282850713142305, 
    36833777975329, 36833777975329, 36833677312033, 36833677312033, 36834986165281, 565432715118688, 
    565432715118688, 565226355329120, 265751220461005753993844546341317621682939675694486723364493120751120303529530818553281907865157833924, 565191962036320, 565260681545824, 565191962036320, 
    565260681545824, 565226355820640, 265751220461005753993844426125054798878990096653554012663640060532278543420564094410304584723453908164, 37460774488160, 143426484439392, 143357697853792, 
    72645146576992, 72645146576992, 283957738866784, 283958007302240, 72645146576992, 72645146576992, 
    72851506333792, 72645146576992, 81716327221600, 72851506333792, 290314567027040, 290555083098464, 
    290555082901856, 290555083098464, 290555083098464, 290555083098464, 290348656494944, 290348656494944, 
    290554814925152, 290554680707424, 290554814925152, 290554814925152, 290554814925152, 290555083360608, 
    290555083360608]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [36842267255073, 256631287657014189269483192926505959467911002723715710844981199713849750818454977478094816777528032130242549200178733961215352577061179482955843373362785080361256631657255, 265783403612227268787808659431459149642327996819893208830666229344550462898858964516783437773049440357, 265783403612227268787808659431459149642327996819893208830666229344550462898858964516783437773049440357, 71607979083872, 71539190401120, 
    16641875742412316777254151964021417623950713855242292983630964005179449700963668201283708157812287589, 16641875742412316777254151964021417623950713855242292983630964005179449700963668201283708157812287589, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 212345400330336, 16641875742412316777254151964021417623950713855242292983630964005179449700963668201283708157812287589, 
    71539190401120, 61848167966877660273688269300874155158971894133002908448549533939933876001744973005056684371788604501289917334793422488965089423106786721696517697808760379554037800786453287, 61848167966877660273688269300874155158972601163774914400664656634570755675325425216127169449339011209482924091514466012175067547955106855238539923218569399126690473670861607, 5731313400432822919761313276378882843890681250, 11440325949328145384056118810151756614840354210, 291929199781153, 
    290829688185121, 290829688185121, 177058418395232, 177058418395232, 141977125521504, 141977125521504, 
    141977125521504, 36561447061600, 177058418395232, 177058418395232, 141977125521504, 141977125521504, 
    423590615976032, 182710702397577907346369928505474813472430097826, 265750994988619797802388814285386488391813846149725795787984382457533678076627053461290398262488806693, 16609467118804845791834306817948756373436563185074879940949117118162664878731757145790668647251653925, 283133106988321, 283133106988321, 
    16609467118804845791834306817948756373247421555584208476173217111262571474281760971538078359309071653, 132875514200551213644534503818597832874809699257546108203319945951832389119124769979601181964010076197, 282858229343521, 1461529513368749706412563928862870940092981068707, 282858229343521, 282858229343521, 
    36842267255073, 318317512631585, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16642889501884443302937788663776494188534713743718286888772381665722885218758738110254010131276376165, 
    72604344387680, 16641875741929390659782189125740798177131772402750003443954080229818868458788699060073646069873718565, 72705274021984, 143074085308512, 143074085308512, 143074085308512, 
    72604310833248, 72636554545248, 143074085308512, 72845063882848, 39619464824928, 39619464824928, 
    180356953278560, 180356953278560, 39619464824928, 145273510955104, 39619464824928, 39619464824928, 
    180356953278560, 180356953278560, 321098740926688, 11774838382263486251612862534281288563900810658, 145273242781792, 145273511217248, 
    145273511217248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [565191995623520, 571892150896992, 571892218071392, 36834851718177, 36834851718177, 36834851718177, 
    281758981490784, 281758981490784, 149817594612064, 281758981687392, 281758981687392, 565191995623520, 
    565226355361888, 565295083227488, 565432513792096, 567494175754720, 567494175754720, 36834851718177, 
    36834851718177, 36834751054881, 732180864850997610578894849654733641819303216546, 732180864850997610578894849654733641819303216546, 11440325949332688660983187555282260284177129891, 132928197518239160296252839338300567627568738030203982572390484604302725882211025864765832604233149764, 
    732180864850997610578894849654735330675605931426, 132936307594016172501722152760385591613218619609479246705550910322496221626871948591694412360839769412, 36842267484449, 318318586373409, 91366501633903549258791849241762937209593283491, 283133106988321, 
    91522607445766636584605418961174153757219919266, 732180854653160467481549638968011160332096013730, 91522608126331370426501688774824178982389847458, 732180855333725201323445908781661185557265941922, 36842368147745, 91522607445766636584895561157881664759149401506, 
    36833912161313, 265750998701117685802270648870982075753059205968440813222327133411682317596057407722768352134093731877, 318318586373409, 70446121224288, 70446121224288, 70446121224288, 
    281758512187488, 37460740933728, 70446121224288, 149817192352096, 281758713514080, 565226321774688, 
    565501300770912, 16609688693064942194413550488509004117522169846150922871886485237695381233705549637544915846991785284, 565226355361888, 565226355361888, 565432715118688, 132875735465436707175583626866669766323324127155409703310851992916263951401008417909863713907123760452, 
    37460740933728, 143288835770464, 1461596415839296730853389699033536807069731524002, 72645146576992, 283957738866784, 1461592234453892017313424744440350107096951819682, 
    72920225810528, 283957738866784, 283957738866784, 283957738866784, 37460774488160, 143426484439392, 
    37426884020320, 730840196221754445833910657133706997674984082850, 37426884020320, 37701762156640, 11512760049210724518026490079853484710388305314, 72645146576992, 
    72645146576992, 354532515645792, 72920225810528, 72645146576992, 72920225810528, 72920225810528, 
    72645146576992, 283958007302240, 72645146576992, 283957738866784, 2127120843387391410897558068663039683119387332195463653408529369482910516506867775193316650516068805, 495132556658784, 
    72645146576992, 72645146576992, 143082685729120, 72645146576992, 72851506333792, 72645146576992, 
    143082685729120, 72645146576992, 1461596415843637510928276701327483584710888659363, 1461596415848954443193825968470770362803463133603, 566531992914016, 566360194254944, 
    37943121292769, 72645146576992, 72645146576992, 72645146576992, 283957537540192, 72645146576992, 
    565432514250848, 72645146576992, 72645146576992, 72645146576992, 290554680707424, 290554680707424, 
    1462216657701427443207918435248570816026561234338, 290554680707424, 290554680707424, 72645146576992, 72645146576992, 72645146576992, 
    290554814925152, 290554814925152, 290554814925152, 81716327221600, 81647607744864, 565191962069088, 
    565191962069088, 281758981556320, 37426884020320, 46360424483168, 37701762156640, 37701762156640, 
    11468158388672479811274186911584855474473272738, 70446121224288, 70446121224288, 70446121224288, 70721200457824, 70721200457824, 
    281758579296352, 70446121224288, 70446121224288, 79379728697696, 70721200457824, 70721200457824, 
    70446121224288, 281758981949536, 281758981949536, 290314567027040, 1461596426387219338222037587658190918608273018274, 1461551824896822276975747262639021718833616913826, 
    183045214849122755164619624817515765599354233763, 290348656494944, 36327373441120, 290555082967392, 36327373441120, 45398352988512, 
    11445857558403357457898035327450540856515757986, 72645146576992, 72645146576992, 290554680707424, 72645146576992, 81716327221600, 
    81716327221600, 72645146576992, 290555083360608, 36361228257376, 145419544300000, 36567889741920, 
    72645146576992, 44531332449313, 275742580346025275209528077816257349133599886173459726917344296642214411439247941244647293790484613, 70446121224288, 70446121224288, 79379728697696, 
    70721200457824, 72645146576992, 81716327221600, 154353084533216, 154352950446560]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44538848649505, 44539083530529, 44539083530529, 44538848649505, 44539083530529, 282033461141793, 
    519044880673818367870617757574278685526004337001004603266004933607235501955714699580398231573575877, 2135484335776450652494329980893331141458238489180606585356091983684722958266789725686447189734281797, 234972585769355288166312476553064494542463001528489501505951463158382163333366800715377943245441871456146309400208749059687412947878061344962309656522265238971723853727169040919429009795063430624704614055327738248486054968407744425082779266372995699970112124598761, 141872972466272, 267827178100032633491904496351340897074709294321925239121399051411181546213764597344336388306858225348, 267827178100032633491904496352179459258187263490648057894729026233107818353902506005513338713760935620, 
    267827178100032633491904496352179459258187263493557404898091612112647492788258171096289538766031367876, 268086700524897024081321880116858409418953562033830049716097215573628097675265601503890942243215847108, 267827178100032633491904496351340897074709294324834586124740469005239802908185132827533472922230402756, 141872972466272, 36319856199776, 36560375416928, 
    36319856199776, 282033461141793, 11429175534193259687576444552117471871215601058, 44538848649505, 150092099133729, 571892213784865, 
    571892213883169, 177061644863712, 177061644863712, 141979275102432, 36842267255073, 290829554164001, 
    24263298079706546934003821453176948143197028643, 81922479172065, 81922479172065, 141872972466272, 141872972466272, 36319856199776, 
    36560375416928, 36319856199776, 11440325949327820864264520344175621980939617698, 1461529524151457592853132640770943042876575089571, 1461529524151457592853132640770943042876575089571, 1461518373865247772181260761806842797814764831011, 
    36842502137121, 36842502137121, 291929199781153, 145694019297697, 145694019297697, 91522966783935720501905200462031460505730715939, 
    290829688381729, 290829688381729, 290829688381729, 145694019101089, 290829688185121, 1461685629369166160124587664861066169402376884515, 
    1461685630730295627808341518124268780524406870307, 1461685630730295627808341517681542702279994413347, 36561447094368, 36561447094368, 1461685630730295627808341517681542491172151267619, 290829688185121, 
    11440325938693956333165386317060993159386367394, 177061644863712, 141979275102432, 423600290138592, 1461518373864001611427832901325924648603437007139, 36426158835936, 
    141979275102432, 11440325949337880977804072790535764660636354466, 36842267484449, 36842368147745, 1051177557671194853722871629381885795834744842353054059864042461920527966033122099025587934943193520250000840309361283411962500730715543989780004874412110619178685781630762279, 3462625622495011615410524509355442224181102366558801189892833524043255326986081375073984417543949656312488049011315515065842681724442333411296023662215157098633624372555792166, 
    2071407915806704857173143649619147240638971930522733509157915326812231185138496314899542860742167423633348658059065304635261207143890740980920831739021954403021495363477420839, 1978884747222783456185379191100483388765130552759692159062909161175373963017227322123509295609850297551749768951612288320888437991541760332204659286546943485011581351409725222, 290829688381729, 290829688381729, 2135801135725730665097901476834232933096487679355124185425614317258203524004050609307982889346025157, 81922479172065, 
    81922479172065, 36361731311712, 36567889741920, 290829688381729, 45638595388705, 22847287786815192394392934413734493039693431075, 
    283132872106273, 36842267255073, 283133106988321, 142395484414241, 142395484217633, 1461518362976212030711229932011877520732441313571, 
    36842267484449, 142395484414241, 283133140575521, 283133106988321, 283133106988321, 1461529513358126267079614543866210085576795784099, 
    1461529513347492443113336425808799256917934375843, 1461529513358126267079635095605143798156563088291, 22858351047138830677431803239482183876509471651, 91366501633882704051935777494620274130493146019, 132875514200551213644534503818597832474952094807664371402950375239022837188521007585470128727839602725, 564092586828065, 
    91355699689232245499029236658352545672382677283, 730775907089057361114220664393561139172350133155, 1461518362985516617491241774265124966054404063523, 282858229343521, 564195632881953, 1461529513368760091045895079775260169882419889059, 
    142120875205921, 282858229343521, 1932269682998647193302200343080204111862945463781013818691916463061792872083727143428214206415055549904787776096748983177161836763501659587432020447516010731479313955968807, 282857994461473, 282857994461473, 1978658779495010881948298536857158074196872516290678244898824590925489362907905557380341476143393947333590118338879121779314318307558466137126616356055334390373482386001226534, 
    1978658779495010881948298536857158074196872516290678244898824590925489362907905557380341476143393947333590118338879121779314318307558466137126616356055334390373482386001226534, 142120606769441, 282858229343521, 36567389839649, 142120606769441, 318317512402209, 
    318317646718241, 318317512631585, 1461513484688199852137417721073505378918394265891, 283133106988321, 36842267255073, 431567310758177, 
    267827399859917987289356521017186770752455264120739232986594998351551612591643382695268446951482404548, 16609688693064941272390052738599126436838095433393458492352447711660046201369351479246189891730616004, 267827399859917987289356521017186770752455264120739232986594998351551612591643382695268446951482404548, 150092065808673, 150092065612065, 22880651877387588145923214666291738499149727138, 
    290829688381729, 267827399859917987289355642580417450540019080556619869727023319786279841557205424830419393238771248836, 72604344387680, 72604344387680, 72604344387680, 72707423602784, 
    571892214276385, 267827399859917987289356081369825138464299190535604670159896320025394859957629702052641789769077042884, 72844862556256, 72844862556256, 72844862556256, 213380558751968, 
    143078384470240, 481730391140743824740241801299598365912783096380027679965320244157985495731917954437192782059063065541, 267827399859917987289356521070749930471533447932010535424004781097096795171960719859373276370965704388, 44538848649505, 44538982965537, 44539117314337, 
    143361997015520, 267827399859917987289356521070749930471533447932010535424004781097096795171960719859373276370965704388, 2482762156128, 290829688643873, 1461864025804187743912926824097645057723202576803, 22925253537925832852675517834519852913491707298, 
    22925253537925832852675517834519870505744860578, 22925253537925832852675517834519835321372771746, 22925253537925832852675517834519905690251167138, 5798226440003300162034117761202633712005585187, 22925253537925832852675517834519870505744860578, 72603237091424, 
    3354397805040921975307541445505413680163908101705531687194744670985779913581730925625972379596321466615837397206132682627059306925337791763998522622850921363683515818080008355548389514262378808647554462191898439328640554295046720062879117928476203902439929455778448117400153904977033176155398955193581181491825257351468914442760956063891319517382510040309991974921152113761296426, 22925253519316569923252483092481231833799329186, 284471298975169323160176358146588507288229798313119585918585506156004164475644098520072617930371840453, 72603237091424, 72603237091424, 16641907236287754313950483990952271376546304286484813616414708809475706880560487811102590143760562309, 
    72637596829792, 16642128996173934231361243805386399677662339861701220701512654536587901043479873432270629823798524357, 72603237091424, 72843755260000, 11507228440135187924085906766974158148351821218, 34343191523431195058125799131619681827023226274, 
    34343191523431195058125799131619681844203095458, 241540966556903348016094442032654549733589264338561500865711815612601567742087100944644059073477397293616887570552612857703561783638663427761155671876727754677886774826790, 241540995012533098917532170512120628339099613186500868949024951780709893481829474020919185869017600952092904628266767896467591675973964228671732877578562598383898354931494, 11507228440135187924085906757750786111497045410, 5798215891240189979585117560044506314149725602, 143007446206560, 
    143007446206560, 91522966103370986660028273535286467775434887459, 72844862556256, 22925253537926157372469534161363074867150718370, 72604344387680, 72604344387680, 
    72604344387680, 568490633339297, 72638702028896, 72638702028896, 72707423602784, 567494167765409, 
    72638702028896, 72638702028896, 213380558751968, 495070292216288, 213380558751968, 213380558751968, 
    143078384470240, 424699400554976, 72709640292576, 143078384470240, 5720162964133729974449171324010268872214086051, 91522606786552546612432772217647974779352813987, 
    732180853993946377509376992223476178885988614563, 1983473913172745526191366720185803350047753023151506151178415363009152897733619149470032092507519163912578865526963225488383007605663945532990056900546375377793734121446424358, 72610988165216, 283717220698208, 72610988165216, 265783660764111914541556245033782234717557007622065650297984523127032304683991742362356519136426932677, 
    5720163603409323950946899804545232538429325731, 72645347903584, 283751580436576, 5720162985318301157271268048414693895432077731, 354191199963488, 5720164285303290859211143517115860449058914723, 
    72920225810528, 283957738866784, 283957738866784, 284028404500576, 265783407324242112653080909837740563839032958308366308039525271063801703521198538036705661028040030309, 72610988165216, 
    265751220461003865719681402674602400110055831600649361614411585622286621359592057403431000870672864356, 72645347903584, 72920225810528, 72920225810528, 283957738866784, 72851506333792, 
    72842647963744, 283957738866784, 267829173939000817668971839906450698048026863826429474039859254449712279445935080263393780913385057988, 267829173939000817668971839907289260231504832995152292813189229271638551586072988924570731320287768260, 267829173939000817668971839907289260234628720553191769909096823006188512701221669949166776442893184708, 267829173939000817668971839907289260229161917329534873153994605694871502806798110169302147595551977156, 
    284438609130321815391684397518488748552095016567690933950615596200876238002252585319661116640786449284, 267829173939000817668971839906450698048026863829338821043200672043770536140355615746590865528757235396, 74804441385056, 282751709410638931287782119234815618531498132205269874345240580568509758617992135891233810913956015812, 74802260346976, 74804441385056, 
    74804441385056, 74804474939488, 215548577712608, 74802260346976, 145171507447904, 39618391083104, 
    180360179747040, 267829173939000817668972719202641433656522659049838908135951443193208195060403518445931139959510609604, 268348214836466031797398759630235131412040269713720144900640399586012109480577783882556983682741120708, 39724693719264, 74908663548128, 145277810378976, 
    145277810378976, 145277810116832, 74802260346976, 74804441385056, 74804441385056, 74802260346976, 
    74802260346976, 74804441385056, 145171507447904, 39618391083104, 180360179747040, 321101962152416, 
    11774838382263161731821264068305153930000074146, 74837725284448, 74837725284448, 145206536570976, 145206536570976, 74837725284448, 
    74837725284448, 74837725284448, 145277541943520, 39724693719264, 286514784692988995531271664605112892427522164224121537650494798109390696736737586837345998634282960196, 74908663548128, 
    2077193189339841670887114191044738779733917287119546276100448193532294369603737357516707172844906052, 145277407725792, 145277810378976, 6065825838528597017503210683877967485641188770, 5720162974684517439053241406674226588317417891, 36567389839649, 
    36567490502945, 75052746279392, 75052746279392, 145419544300000, 145419543841248, 145419544037856, 
    286156898437600, 44126632943905, 79235771795552, 79235771795552, 79235771795552, 79235771795552, 
    79519449352544, 519044880673818375073812044849244570435508172421461975002224139687403709722292085544658200214714565, 79235771795552, 2040724893673154581851846193619226953378091237102747148230732600146915048739349312827603048367936237442007504073479398274636042994237156909423722764786724757268002442620959782, 184758226258144, 219977628518624, 
    79235771795552]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581096261617888, 580684011931872, 123421324250209, 580615225280736, 580684011931872, 580684011931872, 
    265785434843201353880842708301710276394937755336067049919180384592638538843931464163435007490682543812, 265752994540108411252272281178803296057984686444151809610817283335136992975144300404803289455269011140, 53052645082145, 48526606668268778087869380359900156998879552930, 284230471125216, 1461596415838616540856546788350514238187750565282, 
    1461596415840937506425866057898073110155090208162, 565219047803233, 265751220461005753993844547146442135645670954098644518877582373326416576155445923574026077765462057413, 567521146082465, 81928921614816, 290833983343072, 
    22881261833530618465316119079441416536092845346, 22881523170388413746056058951139924134079243554, 73124238657760, 284230471125216, 22880750048850769373867070164031839156702815522, 75321114429664, 
    286427346897120, 75321114429664, 564085168047137, 564085168047137, 564085168047137, 265785434843201353880842708301710276394937755336067049919180384592638538843931464163435007490682543812, 
    284230471125216, 565184679676001, 564085168047137, 567521146082465, 567383702933665, 580615292389600, 
    368230089832415063153498585148616848099391317410, 268897676423098020835752910825479517298598297845802809793481871978889120089933591501452381999640632644, 16641875556787413440751329480805183564132736223320395355991504034144367568875571796534288907745910084, 580684011931872, 185544998536618808488237191674773799357183960482, 565430503016672, 
    81100758978617535373904881910503923977613046820686057813285086970069487008991665474811725936866565, 53052580105313, 88236951144545, 567627311483104, 265783407324725392828937461936328260973340400881991266715894493267112789134352060642120764567984299716, 580754778327264, 
    565361850648800, 565361850648800, 567490006616288, 580617339242720, 564123826194656, 25690556470698759939224621116054982451802940834, 
    94198707057442629510762287521329256596161176994, 565224411564256, 8563518824012792546311190295065240603055367586, 185542907839767788939450161842023782142647477666, 2108619710240942702853959832755081173570523381991913077911934924213132137528130443309399132578275012, 158471681083616, 
    580684414585056, 265785434843201353880842708301710276394937755334612376417499092218122906834289106570390859848763858628, 11440979275521512288035140278052286485032871842, 1461525331963064205525226858229935928259006441378, 142117788059872, 282855276284128, 
    216964037239183405135560328339111106308754384802, 265785434843669645873327073648629838204349005508353802586205927359079061581895511101450110717389725380, 265785434843669645873327073648629838204349005505444455584198111750350122503388140895737298626607603396, 265752994540108411252272281178803296057984686442697136109135990960621360965501942811759141813350325956, 295320810091988165656855468244036106116063091826798709870977354542344007645183859535045208652668612, 435694908869088, 
    154219932158432, 291962732323023105017040791135679989649532354408371268991381512354674673483403107453901156943683268, 293682064039582975411785877199428464390043004891084410852227756007521543998051188501020887932541624004, 132875736950435933923408548050475631016215565175873823899455986091031676557542072065007679476067229380, 286015298341088, 75046504958176, 
    145415249201376, 286152737425632, 2044581885114101451459901653399317583943996782130056562728223343693773156987326955349290581186039974202034172191033632208753999675660509064045976588879549763035501096086772774, 282855276284128, 92949865336317527948875369299643328907790824866, 284436831098978251208475314375622459112215555607937931057689641337839406770938620288427919700965481796, 
    284436831098978251208475314375622459112215555607937931057689641337839406770938620288427919700965481796, 265751220461002921582585053644934673784160744669036241284558345185255177939855679207713769560759614405, 265751220461002921582585053644934673784160744669036241284558345185255177939855679207713769560759614405, 145415249201376, 286152737425632, 145415249201376, 
    286152737425632, 75046504958176, 145415249201376, 1978658307749821103328700726245097430261063721323732106580323867782391674267840381616484446153487531795437788444297763280177115616218472177760707792089755916768104409721296678, 2108619710240942702854833548511032895102107181873250621115791158614572907936375655843566276398046916, 185544998544594369126496316829367092608271253923, 
    2108619733444055736041001388243589516429034062865380578154437381461040541902170497928180549444198084, 149675856496864, 1464361709266407596754819612798040745790432355746, 567489805420768, 565224210172128, 569622390900960, 
    569622323792096, 565224210172128, 567490275182816, 1462216657701417058555050968566071512898533352866, 74909065939168, 154219932027360, 
    265783439004225734624146363717227644834827963598037524306572463549029042138874130033851282220211265220, 267859836218979294226255815674783841942388957047427489484218720818552133343452438196223011859129720420, 265750998701117921836540835143972706765100933621869457010751998074372214750691537204375353426496010373, 265750998701117921836540945485338749239980700428381720299868463942745198967045342868511798507464898693, 564085041398817, 564085041398817, 
    564085041398817, 248528823847136, 283953714104544, 73121889650912, 73121889650912, 265751220461005753993843987496762408277364857231370812872103017127403081720699000139893555529160516037, 
    1461596415838943819066073970941727094453889403299, 565219046984033, 259775868603384269922685981980179434430755927206987759693095226922730015253089311402545420181626469, 1461596415838943819066073970941727094453889403299, 265751220461005753993844099770124994949621442915462141776210462852709017582620895957302622058042023525, 1978643241384089909978371567717745071160151618234453085241664465541863592652859767840605508452984642363942094498370131804973244465894833148537024805384519695336228977283939367, 
    730842809590311771352134232949743218791929645475, 265786805002488844025069840217880877632797215770499067392776998084215786893529672010514874639504662212, 42920149453024, 1676866372978041557017497393061027105843445470385380739663568675052418331801264143192981609593517544258796263461921360757278370725145168795852463221732816120540476101430975544212107345443192800968841048345278724486807888752902404484144971327563069050998311472182840581359564664457047877172653490657458865772438260920916412873608604246909315671051134089786972587025892567465175082, 256658928972823935696541149439739135789763975987094272938685107359577844533592298052877282779252380507832164278109434674750960622477198231455206493133407960743041725098790, 261549947706041528351420271541310308827302274430020151089243007795207400882473158410533733049264229, 
    145277809985760, 295320810091988165446353336166077431251182526441214344548320542931342777874302723968840848794214084, 290833983343072, 73124037265632, 567489872529632, 567421085944032, 
    567489872529632, 567489872529632, 567489872529632, 1461596415838943819066141803272144828769393199523, 1978659015367662433294633052353903200427384750431432330874466077349645608106486055008437296359838714651382916118710088772739238942904568558307755306452341496953663901427285798, 1461864024610857724873775985238100333297496761762, 
    257263352643302525729737022945778826364094381271882702210819360458598540925794112509855574677389001547274914814042260439077110414069127449374006598311307369336357564432166, 45403714357728, 267861614242116419587613743861396958727759822301872632520087247066536850274072771452237579728012205764, 145277810116832, 145277810116832, 265785434843201353880842275523121229092469351903801437343026951535188924288466498330490553092170342084, 
    265785434843201353880843209775309977829407702669055234425804091789227416667502464186507450595666845380, 39655974176992, 145209090443488, 1461518362932420351363013087393052303439469609379, 145277809985760, 265785434843201353880842708301710276394937755334612376417499092218122906834289106570390859848763858628, 
    39793413261536, 141910555560160, 141910555560160, 141979275102432, 177302160017632, 72022377957600, 
    22858351047123333589456778951371387586667357602, 141979275102432, 564084940735521, 37937517496544, 73121889585376, 73121889585376, 
    564085175616545, 564085041398817, 81928921614816, 73121889585376, 73121889585376, 564085041398817, 
    564085041398817, 73121889585376, 73121889585376, 1461596426727979560536104801770292118926977403299, 1461518373821456092832753774991313427464747876643, 45761303733508096284159240621020199861973691810, 
    1461596415838943819066073970942304681110394636707, 565219046984033, 129887936237173166706074353688465364900655971856288126151343053838152809464376112704171198090409893, 730842809590311791634543836601991229395686164899, 145209090443488, 145209090443488, 
    145209090443488, 145277809985760, 145415249070304, 989322077652117790538083959611194994588071111467567570504911919345987255614225200261537502748066630369552125469674519147853975535637791382874413844591133405453726851066227495, 567521054037153, 567521054037153, 
    1461864025804250213973118148437544750284250685859, 130774975801719715161626530963904245120703490858488323611533823535116133630490216163431720601684901, 145277809985760, 2040476284013587729298224698291850964746590086068788872469018115771499585891023434863815326561290457396534344941658300788362857960798989251549976835007193032168431438519067815, 154219932158432, 79718959352032, 
    267843366571663460705901424538004017820915920012097477904460667412248058233088101508848956129737203396, 149675856496864]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_0 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_1 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580754811848928, 1461551814348214979509821877491715304423888004386, 1461864025804172167022504791558606681714620638626, 1464361718791983170821738214689037735721043502370, 580613077928160, 25690643582647842767884190168480725965092693282, 
    185542907841761638598597329414512522264779957666, 580684011931872, 1461596415839610869507908008526066243831138366882, 564085168047137, 1461518362975205374474752170211638886270992131362, 1464361718794313870680016674589103126779412358562, 
    1464357529240475998515287681920208346389661902242, 46028913675551939272039813989832245869839122851, 48526606668273970523338514994281278278054978978, 365422798756887947987963233058827683959776224546, 731110419545570891672152588845151911328078112162, 519108240874972279057902703935700662297495997703542862312995706724803923918580746595651110266160068, 
    184472472080228336352944560572341073466794485154, 732180864850997610658122785494543799391282046370, 265751980780636284737168116257735330920164708096608374554317276064391512182320033032116443423803919844, 265751030381104730270277535265267887877453154499858059090569746276274794558910753918335672720398959556, 265751030381104730276580330266633483026748946612675747124127560967135661664348753610319218022189056964, 1461685619845247600828798145693906795839743354146, 
    519108240637049734531439429689054076876897614204900754333118984688677940065419950348883150831305668, 183045231193169714890655543870383726965775967650, 1039103489897385337726990325689769028355917716509052114771883537084256224072980776215646099732647396, 184472467996839933301682999011845784285575947682, 53052544417825, 53052544417825, 
    53052544417825, 48526606668273970523067715610687601342920795554, 158605664879649, 732180864850997691787761200101225495180287190434, 33218935722611761806879715280587196168506442965671350897046756944699441404128845767352382038745498564, 365556604253920616209779595357845211593400935714]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_2 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_3 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580617507113184, 580684011931872, 53052544417825, 581094114134240, 580684011931872, 123421324250209, 
    16641875556787413440751762232560241070303430086482272597205743525148628808405006703318061343264759108, 580617440004320, 580684011931872, 53052544417825, 53052544417825, 1070530033986493666498307113778476560855143382517919700181631686532106076036365620531977957651258020, 
    185542907841761638558905876609777112023621445026, 284232618609120, 286431641864672, 562985656418337, 1461596415840942698722724592725701640651419428258, 565219047803233, 
    22881261833530618524737240965139669731250808098, 354603510335968, 25690643603583261028183229088709178469846099234, 4184799348921628307522312186918547802802313476321754787997918953062793593021960684830508180241818564, 4184799348921569183703602233998564465594832345207647577110675447042144244954776690184685573775467460, 185542907841761638598597329414512522271222408610, 
    185542907841761638598597329414512522271222408610, 185542907841761638598597329414512522271222408610, 290829688375776, 284232618609120, 286431641864672, 564085168047137, 
    564085168047137, 564085168047137, 284232618609120, 565184679676001, 562985656418337, 564085168047137]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_4 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_5 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_6 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580684011866336, 580684011866336, 88236951144545, 16641875556787413440751762232560241070303430086482272597205743525148620911894976909299489706609761604, 16641875556787413440751762232560241070303430086482272597205743525148620911894976909299489706609761604, 290829688179168, 
    268897676423098020835752910825479517298598297101009976932659886816732455231059010924612737781457771844, 290697560111706829943434310619952039434819309853098500487021003570256418949922631231122339952805829956, 290697560111706829943434310619952039434819309853098500487021003570256418949922631231122339952805829956]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_7 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580615292389600, 580684011931872, 1461529513347638151866091143278951934799995996579, 1461864025804333452665682830778454773252316474275, 3353732544361847878231020834665803982489058087929606401878730169816067366497701070229691740194240691637303559038801513357731868803397831193990798608962225595541852569635828772811288142120818753973022487646036867953119419951246930319619035056582821104176814546102189384240376355320927894864716104796478400526507129844746586220517376553220010072284843497627404779566940802620508970, 3353732645497406852575570240187429523088447220606522246932041415020783112689446234757650657204059444868585354858640826686427512412667218561141511366637644324348272325389668529684223116628364481042983501762644575936761753678197627024989719513183844573575888468332392919985100246034814412803048190657755253111736720559139473400607070914696814626957732720641572440631032276066195755, 
    580684011931872, 580684011931872, 580684011931872, 580684011931872, 1464356840506301691987130105236524754220414936482, 185542907841761638558905876609777112021473961378, 
    16641875556787413440751377567315077708854116308352862244994577874911612905182636642080686877545880900, 185544998536624000844516848388100583048671143330, 185548483028061271254382713344080684355156452770, 290697560111706829943434310619952039434819309853098500487021003570256429403397951128416742863994379588, 1978670256173712906548994319048682252558666979804164767575041440512432838285922798567495837931932105945782480258890570558926948065274983407918852158891199434833153349749046055, 8563540601664184695444461689229515276490909474, 
    1699133317294631717207704971570282511259686404849958357996013558839685805107279310479560100856830304828208569826740228017935843437696261755887330977477153420915224741518812335595304650504137681601200197835399926221746937159340467494943283672286710572769162019769281353959954213967771463253279037487010587881402657021899475437958361695956426006956573066020067802773384923499, 3879633372745541415433854513852050427088000162355834265511830072314937021388789707652579835383916140906327486416891862260687223654857375832392189063237387355003335109222182, 88238027245792, 61847696218876081133648532114023828154670230499747643436587358142346381874713988243688223589855142921675241442322338564721186329059854080971359374437138155951148490346721062, 53052580105313, 123421290728545, 
    123421290728545, 88236951144545, 158608985950432, 16641875556787413440751762232560241070303430086482272597205743525148628808405006703318061343264759108, 16641875556787413440751762259394230866625162946955260243595050059804018643908542115201540465563295044]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_8 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580613077862624, 1947364611433739721585986543006381318093422601235450631885942670187472435924362448260063439904174681551000016816285422614257890954996682853156082660245587431174425650487590, 265785941722929864046919444035801939253827620918186126940031253508166486590564814629632813425046363012, 1461596415859547988820010818270887395390453722530, 265783724124077978312316655652892103834771613113563759921495699479618275471373149843183995695257394052]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_9 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [265783407324725392828938334356413918702589570505240244369220773529445971320415210605458970359238794116, 580613077862624, 580686092372192, 1462220837730012315345500341641065554742826526114, 567633686694368, 368230264061634374609396100839152640411415348131, 
    1461864029895551545285763668507741183320980497826, 94201146211413098998660567317321297328840377251, 580613077862624, 580686092372192, 580613077862624, 1462220837730012315347981057441361517883033150882, 
    567633686694368, 580613077862624, 1462220837730012315382943192402871010647469483426, 1461864025806835825412678620910508636863373796770, 256629444892258282455369622279040981724065160127820438257222776953423691961398625637059718552862824726185903694711619822727707083954250205820544084165581193416601657916710, 1461551815369062037132902816348691757393529808290, 
    1461864025804172166982813338753871271471314642338, 1462220837730012315382711078645505001845925897634, 565503584307680, 1464361708073098996019168764384491385925021492642, 1464361709266407596774665339200407887959984448930, 567427729590752, 
    1461864025804172166982813338753871271471314642338, 567631740537312, 564085171291169, 564188250506273, 568620657808545, 1461596415838617189893654105203967734131315975586, 
    1978643212821386010807107750448100995069496641389945844396047098621518295509966071532867615090972549380150590285298428589463147078028047099625466950076084683134093896312444710, 1461529513352809699263766414278116851394768578466, 265751220461002921582585052732474200836242977533939004524028255182134405329406244433389091322524720836, 565432717216224, 565228706400736, 2108873149626520285567050569496103076377643235347818900853320097012201865650391258038190348626943684, 
    567392296176096, 565192199047648, 567427729590752, 567427729590752, 1461864025804172167022504791558606681714620638626, 567631740537312, 
    1461551825066880383686554919444992178735920227618, 1461864036693207908492535622386594119531203405218, 275742580346025275209528232111699053630928717380749698382842895999242621624513196456138304899177348, 310495522190382098799099326673112421792647339304957819114407699728329681296832142637945022384299716, 564085171291169, 564188250506273, 
    564085171291169, 1978670219318611101651129551064750797595114239298471612128320442342558456895019144375637694179435056644708889036599174610028923443378324172413426112623730177835048216338349862, 1461529513352788929998496794416462006303184136098, 564188250506273, 564085171291169, 568620657808545, 
    1461864025806835825412678620910508636863373796770, 275742580346025275209528185990778691345372833751728675648091375947940958259933753437540556167224196]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_10 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580684011931872, 564085166965793, 580613077862624, 567486785393825, 53052544417825, 268378631573369239685731794257359673725133098866137700617482854614231379639685433184860953753626385284]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_11 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580617507113184, 456791912024916798872480452023733297145563109639924032480541442978544057112738797334476516647500799684, 456791908188668796440559530058682954448601687839746180109166998968032555866100214555172664727617691332, 16641875742412316784231806939368443075979706428721588638005444319900202591116964215863710145760485060, 368230612510778101650383934035034838842818692003, 1464356230722953767981422241135381393989366720418, 
    88236919687392, 123423439292640, 265783660764110970404461427929761164671223986946678848704442800608119805202921469802069842577717223108, 580578718058720, 580613077797088, 580613077797088, 
    185542385170700619872826708113157618870472158626, 88238026983648, 53054728669408, 88238026983648, 7560670634479108855437536186797703994533052022643170831690317376582005065704681182018955815859494584937138450825515204245214687558275762215955843814495622008030357126939590153660509119224583016163736492553711884034465981884738275326811481556146100109442122998760, 1978658307750130403652075570996415654783467132576529401807680038276438053742805961390967341204399747908160772128397068669633430268206222213070432490386015123335768713890191142, 
    580617440004320, 456791912024916798872480452023733297145563109635105426465579051991234410655388380475976796466278588100, 191040945127532847629300509356555999372904753959216939898341179465393963644610025836011499193977822916, 16641875742412316784231806828678235166152644401024368103844119126179659608598424117160781645706452676, 368230612510778101650421410878405158918483608483, 2108619732990869929884433882075171882784382928076395184396284483315176274518413878669718759234411364, 
    2076211109836584743643006813666602705894022748450522809128520703816014251230394414829350287129270308, 2078206948827074159375332889422874939590137389076434249449186957297551310063451242713337131082521444, 568620657808545, 568483217806497, 567486785393825, 564085171291169, 
    565253410786785, 2110647228716903754759645893196866741025302504055338355712461860582992749770055514721915068933070532, 2124839861432418469047889324897625585685455500713237997818358049142033181718218252733531605850250948, 2076432846518471456501550628901021036471574699672625445977702499650109024329314490177418088541707972, 2108873149626520285567050569496103076377643235347818900853320097012201865650391258038190348626943684, 400702877438222498284136709685035365591524925667992749875618114367476358196094270915588839036118752964, 
    564085171291169]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_12 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [158471546996960, 88031868750048, 185542907841761638539330949591003646787056051618, 1464356317851191470097698738169763202800707710370, 158471546996960, 228773719181536, 
    158471546996960, 185542907841761638598597329414513085216880862626, 732180864861631475109838414171643157383656023458, 73119742298336, 2968221476721395911463059958353637030322414197924683716333860813541162146582843238778885679134196903836800593403937881335228534483873777686595898291634437512145902845026084646]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_13 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [142388974651616, 142388974651616, 265783439004225734624146363710623967609188187511895397859182090146005991413786937908795875307920857988, 564084940735521, 1978658351975829919390076002404130927781666647948487748713508071334730045911427357502438717783473104865813555215951511416271446673385892189629227110065017560267027685143723814, 22881261642454015615778646946920668767703278882, 
    22886139930466194189590857885297243827665904930, 22881261642454015615778646946920668767703278882, 564085041398817, 182733003227852222152585135425329515100939756962, 182733003227852222152585135425329515100939756962, 182733003227852222152585135425329515100939756962, 
    182777604888390466859337438593562115539835823522, 182777604896386634445095478619006967607525420450, 480481306159211361205044992421904139309116810276696193309304011708559916188545629281915133179791458265111617267290289405163740572486879286318082418004927073554939597387653772020712829106139716191208002007470375985659070917427578291145160748223204920710398082123494280, 565253276700129, 565219046984033, 1978658307750102288444220109193682500779982993312867584616715852014250335752425202112433842734881997068014341070780487950412453914826877966989394046386435996628967417235330854, 
    730842809590311933612030032182749300507389495715, 145687509534944, 145687509534944, 567521054037153, 265783724124077978312315775927331316819994843470762741228865708468096027483846600650923028942540529348, 480481310354363302387925279167597941792341734797724518518914413275027457397732829757761795017425767368345521074420046321043453486907287142420365720223321071947994470248899768353961620297583435682701624432029407776324745252049857430410621402168943991647633554373495560, 
    265783724124077978312315775980999296412638273430012510051189705753141943595699750866852919722917256900, 567520919819425, 567521322472609, 44531332745440, 184115654704537808061906533640540128713160271266, 184115654712533975647664573665984980780849866146]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_14 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [183045214851619935099851257602959407029514937762, 158471546996960, 158471546996960, 158471546996960, 228773652072672, 88031868750048, 
    426557545570150979292886852015930290358822704518262636259917213075445889387282365282275333220691123076, 88031868750048, 88238027180256, 366090429719190666718742185201839699486231258530, 290829688375776, 365555209792731730237714547183048494219478463906, 
    368231301258249606540329614156013942190805378466, 368231301258249606540329614156013942190805378466, 182688054477970490102718666277445269396614817058, 73119742298336, 73119742298336, 45761303733508096284091540627548953942715542946, 
    73119742298336, 730842809590311953894439635834997311119735949731, 182866808209466956272842044930029005273930671522, 183045214851619935099851257602959407029514937762, 183045214851619935099851257602959407029514937762, 268898052638370872342010250806000974669552440848297282896829893360040903744949806848861887557992072292]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_15 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1461518362932420513622609071879095820151563616675, 480481309846575119507226613771215384544901847850468063456865502520995091900465889430512254432520260318707030660036076409296655255637198698492247333114119276185179218997809019178468368211700220536489498830760370404567033985429735559044021058253840791191425154124763560, 564085175616545, 564084940735521, 265785434843201353880842275516517551866829575814752805008146650787229117267750141009161969722396285828, 564085175616545, 
    564085175616545, 265785434843201353880842275570080711585907759626024107445556433532774299848067478173266799141887532740, 564085175616545, 265785688283069385512264064847160202541508369588684349368086387721852728234269095763960684602564057988, 564085041398817, 6065825835864938706712286055999176633620112802, 
    183045214851619935099851257602957718173212222882, 1978658307751508209731300482704683227442739315228079430128577022410507173145243761448758190635129763049917337560821391970091322759035720949501027215234838278245168272896644902, 1978658307752407999355006782111855050126177310681246586821751509892825522612654146230635958834459782788238687287041827716322829773084220505574813342414469039130701761054725926, 183045214851619935099851257602957718173212222882, 183045214854278401252432894024235328660723737890, 6065847616590020001243667103782705115695687458, 
    91701362521096968864702591979467639932227953954, 356813289622890078333541487308190147813057826, 365735010215529589817526813111199672587000538402, 365733616418933912426532246561161341273727591714, 182710702397583099799208983841213214881491723682, 11429872459070405313140457847376999519571420962, 
    72020230473952, 22858351047118790312374400427201099553791550882, 564084940735521, 37935370012896, 73119742101728, 73119742101728, 
    564085175616545, 81924626647520, 268346444709646768439378511291838382052624662163432396564105065240667503564029006768232166749048445828, 73119742101728, 22881261663389435148375395802283457969568359714, 73119742101728, 
    73119742101728, 73119742101728, 1461596426727979722796000601003298200642437253539, 1461596415838943981325969770175310762825854486947, 565219046984033, 1461596415838445518926103824052967920448199231907, 
    730842809590311953894439635834997311111146015139, 265752994540085751962201342325753595842097161414569570351413697078861626526421931092411586657484053380, 182866808209466956272842044930027316417627956642, 182866808209466956272842044930027316417627956642, 567521054037153, 3353732545142508947553909095694950810962758535436650273245993579966465460556619333454460742907229312561562038762956331846210659920416901908161371334488718803021136908221403688805632427379688726467732736483165572173739002334299360703298530760917788191531350519410861106635560813203324949664485641096964357715212768568001815212900300278254152354337391926376269572933659831028918315, 
    265786448602673480406525912296669777947002613149537103602587745076104799049482320867583952303321374404, 1462934465654592860128672919099945933615096955299, 183045214851619935099851257602957718173212222882, 286514784692988995531271664603435766515803851897168121404500017733107427551015027987564212883152723268, 294819502288649493931623509000377233861919381080784078723120749874211456955734681085036179650172181828, 183045214851619935099851257602957718173212222882, 
    183045214859595333498175158317887885312073934242, 268897672494043231662686758464849299396777228436100830375961495382819709868404119767100095918631034276, 268898052638370872342010250806000974669552440848297282896829893360040908670867930370149519850294363236, 183402028135925892753869682948818521684380755362, 79716811868384, 293665847845670322919496313130563292487986235003303980327981612944240290839735350543779822693260499844]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨0, [], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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
private theorem tv_b10_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580679716899040, 567485577562336, 567485577562336, 158467252029664, 158467252029664, 580679717357792, 
    580679717357792, 37454332037217, 37454332037217, 281750127773920, 141012773636320, 141012773636320, 
    281750127773920, 281750127773920, 213587050629344, 283951298513120, 290554810730976, 88238025345121, 
    286010601113824, 75046303828192, 141012773636320, 141012773636320, 281750127773920, 281750127773920, 
    72849428056288, 143213944375520, 283951298513120, 81654111013344, 154219798071776, 154219798071776, 
    290554810730976, 75046303828192, 145415115114720, 145415115114720, 145415115114720, 286152469252320, 
    75046303828192, 145415115114720, 145415115114720, 145415115114720, 286152469252320, 154219798071776, 
    154219798071776, 141012773636320, 141012773636320, 88238024886369, 149671159269600, 281750127773920, 
    283951298513120, 290554810730976, 286152469252320, 286152469252320, 72636625848544, 72636625848544, 
    1461596415838362766379284749877366205707669490083, 259775865702995140774971271277239109653187052792816183811854023041045167764170216211354610863055301, 259775868603384269923235542877360150664453863099591285439722947210842173767332281274261322000916101, 148472930502880, 148472930502880, 16609688878692677949138448138259498589235589870566143166940225714483256586337807105545012614813123781, 
    218841674680544, 565220120988001, 72636625848544, 72636625848544, 41923381823712, 41923381823712, 
    145272978540768, 41992101300448, 265785434843201353880842275523121229092469377225303081087616829291269993545823062066695827171878919876, 265785434843201353880842708301710276394937780656114020162088969974203976091645670306596133928472436420, 1461551819452450441493904901989334927059003647266, 1461864029887560570014345231233403717700681213346, 
    81924626647520, 290829688375776, 81924626647520, 145277541943520, 564086250177569, 265750998701117567785133694248087745524965547099048198757609976303913481982811900240218879303814495173, 
    564086250177569, 564086250177569, 564086250439713, 564086249358369, 564154972900833, 564086249358369, 
    71539400115233, 71814280129889, 282851791078433, 265751980780621178533282367467017635107146556920383709590802443035125017832479327290888581087889479684, 265785434843201353880842708301710276394937780659023367187127880105964815475640414279480262452524900036, 265750998701117567785133028765150623647067652291060578762922045218851002608247267177580874510874983365, 
    265785434843201353880842708301710276394937780659023367187127880105964801637946520670735051901488881348, 265750998701117567785133035634652011505426307044851708241980730793085982376696526980095081908472819397, 265785434843201353880842708301710276394937780659023367187127880105964815475640414279480262452524900036, 143074089502944, 143074089502944, 265751093741071738178133755094820357365099460643187973233610329484671222768775828080102744026028799909, 
    265751093741071738178133751660069663435822702447068898130134914483247626801182887458771200581497092005, 265751093741071738178133751660069663435822702447068898130134914483247626801182886338131498103641831333, 265751093741071738178132872363892017565768461732524021087856305320082128056609573155697694983470282661, 74904368580832, 145273112758496, 145273112758496, 
    145273112758496, 65007330021075508547826595426886163451065368117159109654919917559637237166161574828768699373942693, 154219798071776, 154219798071776, 145208621140192, 145414980896992, 
    145414980896992, 145208621140192, 145273112758496, 145273112758496, 145273112758496, 145273112758496, 
    145414980896992, 149671159269600, 149671159269600]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580683911268576, 88238024951905, 61847696221575429410295888569122168145685836984712591577978497999059917937636908006816703823891922504669006864521300262951819309857365767927860273784473543542082400450246950, 565219913107553, 567419005569249, 580617507113184, 
    580617507113184, 580613144905952, 580613144905952, 567419005569248, 53053618389025, 53053618389025, 
    53053618389025, 569622390900960, 53053618389025, 53053618389025, 580684011931872, 580684011931872, 
    580684011931872, 567489872529632, 567489872529632, 567489872529632, 567489872529632, 567489872529632, 
    565432582998496, 53053618159649, 53053618159649, 53053618159649, 265751030381104730270277535265267887877453152262575895801430822502022209006975477447280385838110950340, 1461685619845247600947408274674919625300780803362, 
    567631606450656, 567631606450656, 53053618159649, 158400680036577, 158400680036577, 158331960559841, 
    292773767353874293100052443275407498543558248334143297892735441372724203297272833512752037052426510020, 365400497777412721975112170588488459421473056546, 53053618389025, 88031866652769, 25690556470112352675150954066475757337718564770, 158469399513313, 
    158400680036577, 158400680036577, 480481077047106023417608928812220475621679691140121801280980570410987408711367860847130332735108649889724619450414631887351141038045375249632861573336178609816643572164684726376039516701064808713338693634068481260756407526393210582897083434795237521441693696624777161, 565219913107553, 265750974941130293871092047372513272416074009002926972971298991347563632685019577617879114514452587525, 580684011866336, 
    567489872529632, 580582040013024, 88031866652769, 88031866652769, 158471546996960, 580684012325088, 
    37454332037217, 39653355292769, 39653355292769, 290554810730976, 281758717708768, 290554810730976, 
    290554810730976, 281758717708768, 495070617274848, 290554810730976, 283957740964320, 281758717708768, 
    286156764219872, 88238025345121, 286014896081120, 16641875556787413440751762232560241070303430086482272597205743525148620911894976909299489706609761604, 154219798071776, 426898681760224, 
    16641875556787413440751762232560241070303430086482272597205743525148630462912008167553776269275454788, 290554810730976, 283957740964320, 290554810730976, 286156764219872, 88238024886369, 
    290554810730976, 283957740964320, 290554810730976, 286156764219872, 39653424498912, 143078384470240, 
    143078384470240, 143078384470240, 290554676513248, 580754945902816, 565361783343328, 565361783343328, 
    567489872529632, 580790412937440, 256629444890500894254069305822515351835809908151876476823440332491965089880377430949797159924444898666701794732034471471311639890366055479242287959637961664617606166845734, 88173736888544, 580613145364704, 1464361709269071255204259821825881564491939341730, 
    564335252408800, 564332970904032, 567631606712800, 268587543360758126600185884932718958242587867672881719051674529098585866633209637165953666151610169775975569972726392361184783121232589955911974548199060547120248860421926, 79450859899360, 44326349965537, 
    154219798071776, 1464356492059812536821553863652083056186538072483, 283886806894816, 567631606254048, 567631606450656, 564332970904032, 
    86052291742176, 158606838270177, 158606838466785, 284170543172064, 52812264507616, 580577711491296, 
    52812264507616, 158469399513313, 256629444890500894254376186192005615109522102104721823124539985196916557226005740332637908940329307725019451187702459671784281231654926904847295213810889042246455063976998, 36354889615585, 1461524635064786811537953336679228302882469603234, 36354889615585, 
    39653424498913, 39653424498913, 39653424498913, 44326349965537, 44326349965537, 141021095135712, 
    141908005882081, 142120606763488, 141908005882081, 141021095135712, 145419141646816, 145419141646816, 
    149817188157920, 154215234669024, 281758717708768, 290554810730976, 281758717708768, 143220118391264, 
    149817188157920, 158471681018080, 193554047699168, 158471681476832, 145277541943520, 356321497450976, 
    72638773332192, 72638773332192, 213380623763680, 213380623763680, 143078384470240, 143078384470240, 
    143078384470240, 72638773332192, 143078384470240, 72851374213600, 143224681794016, 1461596415838363415418867946809390532569508891043, 
    489288346087263500381072930022711200453851714844168102167696518807840101114483326923186467590564399462691959901939465432320074720177332506654315875106838778692016685054033232326709644591093353408254702890375674340654770670911890676187076495834089106423414930123494280, 489288346087263500381072905188486247434913126647137103894213431983830497981894741068467168704098062787565658758836233066561644304878245960944933992523364451560671184555777913699572464556278336170538278064104767599839231449000875358733533752392540497112989842123494280, 293750358285355512940925011092151264110289031204220046397081134235883323164801266814980656492786507076, 565220120988001, 72638773332192, 145277407725792, 
    3379933736864476015231514933156092806495937325501796113585462294517076061129628601991947039371929338461611200703622099456918457697987263904141567787434054573983986633328371483069791700151971277388192631542022827380986894564873482883055633574350723513091803984681688878860908807369526112813685254486209318214003370650012442512700621345425414052366281948794424671503003860198336554, 86527524943621269157626681606394904430369114783886196580636374249112518495511727563387572950793768464769576223346396097520492952882448429281082923188162541043777570846312010910583865351776175857463915669581992887451468892755667142335557550882295317505798794317074523844253485208295271300278603181916625262947685375687898786851351873293476660604387620000509540405212538117246991818744231303450724203378285218260542912457283134540372749520801126623833892105108825934827257401725097497037830864854716236453791220866562605600768409681785035997589686817741795704276554425399630238523512434573308505230236221223055040833843581972173107597649089795272723126830, 290554810730976, 154219798071776, 290554810730976, 41994248784096, 
    215579647019232, 145277407725792, 145277407725792, 145423705049568, 480481306322647488913651718499145479449750488530043158618303447750326298941259409040351410545079490227744562777638113701161874085521394052995750041520081368007998475509947174813739599026853441693981482038169524640312436199736449961267221770031937846077554834373495560, 567419143852513, 
    41856809830624, 145277407725792, 72851374213600, 79236111534304, 79236111534304, 79236111534304, 
    149675722672352, 149821751560672, 22881261833530618623772444107970091723180746018, 25693256951225794315060628892948682097648215330, 185544998536624000785095726502402329853513180578, 185544998536624000785095726502402329853513180578, 
    25693256951225792963307515024701113713356711330, 145277541943520, 286156764219872, 290554810730976, 132891703662604380753422064223388566223073959142295265575623059825611243540687392233336087490309871620, 366091826238024510448034493935738350967571670306, 
    732180859417113604454051161271914901973110400418, 290554810730976, 730764756684370999216843158183718329944237015459, 145277541943520, 145277541943520, 356321497450976, 
    145277541943520, 145277541943520, 145277541943520, 1461596420943180458699566872517709444153747736995, 564086250177569, 564086250177569, 
    564086249358369, 564086249358369, 564086250177569, 564086249358369, 71539400115233, 71814280129889, 
    142251745873377, 282851791078433, 143078384470240, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 215575217834208, 145277407725792, 215575217834208, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    290554810730976, 149675454236896, 219977693530336]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615225280736, 88034016233696, 565430569863392, 565430569863392, 565430569863392, 132924142480290222037920648486651301480666804402433759546162282488535761464693859870545329298873327300, 
    212416403605728, 142047659428064, 212416403605728, 265783439004225734624146370586729032692991375379451164617417707716274441800808969765004834706524495556, 282853938562081, 72705278216416, 
    72705278216416, 41992101300448, 41992101300448, 567627244177632, 519108240874972279057902703935700662297508705731253550088117536022733189463697257037479427514254276, 184472472080228336293523438686642820271636522402, 
    732180864850997610578894622980279461797738096034, 565430368405728, 265783439004225734624145924070075653037287621098960778873780339262661415597330059875556864544631462788, 75046303828192, 141012773636320, 281750127773920, 
    281750127773920, 154219798071776, 154219798071776, 290554810730976, 154219798071776, 290555079166432, 
    265750998701117921836540394744438814027433848277094921853098075468974240000335355477374641320628344836, 142116588623009, 282853938562081, 72640853706976, 72640853706976, 72640853706976, 
    213586849302752, 290554810730976, 290554676513248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [285916514224608, 580683944757472, 265783439004225734624146418676580303346154995467527280634560056780212784326092577756565704117180194500, 580578718058720, 25690643582398609352023897950308518955772814626, 1978643329836335141665315320984264572402854381768892296065643358080522664321490345135915003070899957883193204924684545073626256727066409222348390115310321259623750948770043686, 
    39626983344608, 285916514224608, 290314560735712, 1013759487232776840238303359547232881194427625734600967349270879995776458026907996699883520148420, 285916514224608, 1464356317830006169542883541724226275169542874402, 
    580613077928160, 580613077797088, 580613077797088, 228911091026144, 88031868750048, 1464356840524906333188661418534371817633788470562, 
    94199055528181768369545574767534342002367276322, 88031868750048, 1464356317851190742627181538790974802437815674146, 1947364611236912243079631787170169202981884856844543913862613515838507685354374774698079747061035354694616595427306895871141554285234611130657411622524533456419203404736295, 3879633372942368893938572574384219203083424220396155680469944084513623703902010277458749146906299791390555206167683617409846170101580951702577025923696357244442283114232870, 25690643582315572533281247897478178154213811490, 
    25690643582647879532227476865704129925726348578, 25690643593281703498506803848934586408237540642, 132877509544519530179114695480352936032184208703404860509678107610433328794928327074796224913817777860, 132924142480290222037920648486651301480666804402433759546162282488535761464693859870545329298873327300, 285950605789664, 580617439873248, 
    580613077928160, 39586848313505, 74846520740320, 285950605789664, 39586848313505, 290348652300768, 
    290348652300768, 268897676423098020835752910830301249840124854727006583246943173723451120787758578489967442829975248196, 285950605789664, 25691166256363432140869097239031609866129515810, 1464356840503970992247621354444122707354970498338, 1464356840503970992247621354444122707354970498338, 
    1464356840503970992247621354444122707354970498338, 213376194578656, 212418551089376, 141907938773216, 141907938773216, 212418551089376, 
    286156764219872, 281758717708768, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 
    141907938773216, 141907938773216, 1978658943960902658872645038924875586054885662660143198589553699382062507832600374953322532339156172758169253598564547257824583670708759332349018837580318114114087900011282214, 265783439004225734624146370580963917648486676615215624540147174576578469320026242881927702477725014916, 282853938562081, 72709573183712, 
    72709573183712, 41994248784096, 41994248784096, 185542907849737037016583199106250585019397973410, 145423839005152, 65339969812461898038710211723667840648082120146251416282142617341648534104170827966573309019076, 
    365559391847070412176034521156694531097793946914, 88238026983648, 426898681760224, 154219798071776, 154219798071776, 368231299205921540483310156671128805145410303394, 
    368231301247615742008998966112078880820920083874, 286157032655328, 290555079166432, 732180864850997610578894622980279461797738096034, 290554810730976, 290554810730976, 
    267859836218979294226255376021234537935622776159015050894712493084826497899284778180041958515939624036, 72844864653536, 72844864653536, 495070617274848, 265750998701117921836540394744438813980575534208259484611273849766784074265428294392380389698336479236, 141979275102432, 
    282853938562081, 72638706223328, 213376194578656, 72638706223328, 72638706223328, 143078384470240, 
    143078384470240, 290554810730976, 290554676513248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [71610061557921, 71745350928481, 732180859417103219741646590350172007124498441634, 265751980780607016487862726761810993489367034875438646582494538141580712049396237933260893873563192420, 3891581796777935685094822000810561401191019847481731136212021999840434662406252339249773317622634873152403769443610297877030598029698974981359183485982174695304166848314150, 290829688375776, 
    81922479163872, 265783407324249547732709526604378087006019092529037106645997147548404654328736400019831610187479035044, 265751980780613625443945055502466486538738431426790169651316157672089032601101335064711840220739488868, 290829688375776, 265750998701117685802270660464677472208905944593431237292009038046571307939260787788742811872361849189, 1461685619160695147386507457658753067081995416994, 
    290829688375776, 569693123447264, 1464357529240476059243674249103823111841099834786, 565226357459424, 290554810730976, 290554810730976, 
    37525201096865, 37525268205729, 72645148674528, 1464357529240475998396445438148815217714098890146, 72645148674528, 81716320930272, 
    292753632659936, 290554810730976, 290554810730976, 290554676513248, 290554810730976, 154215503104480, 
    290554810730976, 154215503104480, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 
    290554676513248, 290314560735712, 290348652300768, 290554810730976, 290554810730976, 290555079166432, 
    290555079166432, 84121300830688, 83640600496608, 149679749204448, 6244232476693876645350435220408889441989981474, 5887419192387918991332047653483326585556202914, 
    39728988686816, 436549607098848, 44264202969377, 7136265696753017691004692269661439026773623203, 435553174948320, 435553174948320, 
    145282105084384, 145282105084384, 145282105084384, 37941812464096, 39728988686816, 39728988686816, 
    44263968079905, 148597187228453110582768391757167285658619921584523359327569801660893296801521061592577783418410096730916428337420138153632373576136057470845941328435870938312705919928687087504796295054639882376047819662229505183701315447319065972225272010145543723041081128160893443768198654172303639748978947007677391107396150679158889662637900268415525184338329647977449273063082565661606554051323990973300551421725840832688321748763935500613327938285309599997245121363200352530998779956604712290649758910907589993869, 290829688375776, 3586318182594794181805264427600586358752501732151023189376291685397171099975880867475098974530252152621198639781564644837310471650041800957412567664727515079340669353442933030, 290829688375776, 981230230509837395243425089791080917627534315748234650717808376557565986365570274027094703720842508863955179343189905519358535331113170726602001266495421284985140196943654, 
    73126184552928, 290700601760904725129766619016589205088817020817726984538159219055062340573316479827615637759502966564, 44263968079905, 9079594942497, 74912958515680, 74912958515680, 
    23562133842359560576016044018561493130168264098, 364496732654048, 290829822462432, 290829822593504, 290829688375776, 435827583224288, 
    435552705317344, 435827583224288, 290417237559776, 290554810730976, 290554810730976, 290417371777504, 
    290348652300768, 290554810730976, 290554810730976, 290554810730976, 290829688637920, 290829688637920, 
    74912958515680, 74912958515680, 86252007721440, 45850507054593596177879281179938270332240557474, 74912958515680, 74912958515680, 
    85908410337760, 282394870282022164641411108182438834331598840835597544049986939406164741523608597554182953959351246628, 145281702693344, 290554810730976, 290554810730976, 146278537365984, 
    147412006472160, 145282105346528]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [52819542442017, 52853902180385, 53060060610593, 48526606686883162464027522467971594302584792482, 52888297606241, 53060060610593, 
    72024525441248, 73121889585376, 73121889585376, 73121889585376, 79727549286880, 52819578129505, 
    53128815971425, 11507228419542135508628717042249704497755457955, 44264001635361, 52819575997473, 52888297606241, 52888297606241, 
    259775868603384269922696339847830877829637299104836452252464645803405350447172574022969683264043461, 44264068751649, 44264068751649, 37666998985057, 365466006471646154284668350512299160702802210210, 259775868603384269923235595706777758977743463127588876452026517482171393967644916996803709129350789, 
    37460983155041, 1461549026776000540986347740600932292173631071522, 1461549026776000540986347740600932292191884682530, 5753636162973532723427539908632013597891383075, 88003949168737, 2108619733444055736041506236220553303479071560366536819431414106942035445791001589552559653331804613, 
    88003916631137, 88072636140641, 88072636173409, 268897676423098020835752910825479517298598297101009976932659886816732464782076042182867024344123465028, 212418551089376, 143078384470240, 
    143078384470240, 145273112758496, 145273112758496, 145273112758496, 145273112758496, 47099353539030659495171335932542064912078211491, 
    88038309103713, 88038309365857, 212349831612640, 71820722580833, 143078384470240, 145273112758496, 
    145273112758496, 149679749204448, 141976725358816, 212418551089376, 281750127773920, 495061758904544, 
    283955593480416, 283955593480416, 290554810730976, 290554810730976, 286152335034592, 143490633763040, 
    143009664993504, 145273112758496, 145273112758496, 145273112758496, 145273112758496, 154219798071776, 
    154219798071776, 213584701819104, 218843822164192, 4535624403168, 4535624403168, 265750982861125756828414396982106008458777873180850625806372260126224153609647848076520218683503565668, 
    71543489562848, 71543489562848, 265750982861125756828414396982106008458777873183757131650551874730490830463867431101508455687166909284, 1978884747222783456185379191100483388765130552673384691772630548306025393764125279657822328564465695297209909551853673858886016778292115142266915770472055836637857984975712038, 71543489562848, 2040475813996767279036676692917856389751479123634140620313394207462623933389239616034595169684909792480551432596886445302342606951268281871948388225158490955432268461985738534, 
    1978643212821386010807107750444613416610963030056899480255767622787934060633012627096814006321098096391995457171480070831462433597158364202751091025107569723442650542822415398, 212281112135904, 212418551089376, 212418551089376, 1978899843072482742350788208465535590217910939314355370475667720102535332362005618195295064707557388008559149823443752618004976116738360251085607696479233500927795806333808422, 16609467118804845791834747780889983191600596382466694902789538009880429232935384172979083144240904325, 
    142120875205921, 91355699691807614560029158194974572530280456995, 284955875948704198218485432771182189476965516051990780512828290854769669315430374158489936151134101188, 284955875948704198218485432771182189476965516051990780512828290854769674119140711307586617588392681156, 284696353523842641797892259298069207393376191806089318895556981719457244979874412567699975096264318276, 284696353523842641797892259298069207393376191806089318895556981719457244979874412567699975096264318276, 
    267827399859917987289355648597101113023206094497489919610352487705603971361742974890194153226105806532, 248702267033824, 494993106536672, 107827339725024, 354118179227872, 143078787123424, 
    61848169806933395430846284208724093005617278931201403058880967934972992460584414872855522911853516239961263080356841390965099927085657066845292065431958888263019683896076071, 182776995100062786532783822418101806727057384866, 107827339725024, 72640853706976, 72640853706976, 213378409171168, 
    72640853706976, 248702267033824, 494993106536672, 107827339725024, 72640853706976, 143078384470240, 
    16609688878692677949137908935229969316400773306571355212329223839009166021565077768904316336088709573, 2888527492591104447984738066218920660054433177316902026519389009593911020297104037024834979074556211314882353352226474461896545709621690440943549948717318044074984299460550545413514938496724519511807139860244463330784313048501708047016853547004007538079701129759259556680603108635797140923351367564204925374634309702457244270093298052527283369745019426111746307215020766399244928437056233157289023651395062712606451071193768462300164122401274637688576071408662736912614998510793381170649751331142040766377108187238244667974132831896050905010010809101583181517116955513932609751276399178839627906602578016405530378000833125724692797450328256972655200531491265070, 2046288230258875350271964777634457595244189602528683425403302338654554250917964528843847306205446410602565180444523353705122206869768453127094343828197001863691487011157294886, 16609688878692677949138338279066710463816504754277876983814299294819352055719172973109743147960635845, 16609688878692677949137026204288552574168897771999608417219443026929079166217442180477926316381704645, 16609688878692677949137898630964784994782365300888614725482079434985255953055706422670963745390256581, 
    145273112758496, 145273112758496, 431430006213088, 44059960281568, 79246513408480, 44334838188512, 
    9079834020320, 44059960281568, 9080102455776, 286014896081120, 294819847473632, 292773767353874293100052443275407498543558224547322198400233290256346028005355051326540409689372384964, 
    218843822164192, 143009597884640, 143009664993504, 4535624403168, 4535624403168, 286427145373920, 
    285946579060960, 286152737425632, 365422809305641307345055438313253780782538302754, 731110429073477165478236606448207003815974020514, 732180864850997610737350948008808136984825996706, 732180864850997691866989362615489832773831140770, 
    284230269602016, 290829688375776, 365400497777412721816655845559959784234385155874, 281612554602720, 281750127773920, 281750127773920, 
    281750127773920, 286014896081120, 286014896081120, 290554810730976, 290554810730976, 290554676513248, 
    240240771832510474327134544362346117735092369170114308903241134352263946846574067173689483152282982831477572161539729754480256065802099517174707246868972671739025618224232389373349633263406096077897358962170610973947140701867408563012970681868915728768303250373495560, 1676866372978040160745750176076398957697037098257783554157438152996772889515076805764709117628806749711591908571355452620144241800708395740236738668769379923375895013348242530561462543273250099249841061394893608620582906499727406313495027115308962456422320686729467897586441844543747537468265835439433048025624501806239961860972297250114305605862085637784566111436424382523222058, 288147414452448, 294819847473632, 72024525441248, 72024525441248, 
    182699551982443346169681928271572560287822783906, 265750982861125756828414396982106008458777873180850625806372260126224153609647848076518082276576222052, 267827174155503791609610265106048356890496273489495044344773441914639813387057323225769985292649913956, 145273514952928, 293620541632952185633424810848572701148019965629620553186601865447848631365078017462093781962369031492, 490346839950744598838960499198458482868119101080285797142273403494739449058084053232717002276561561270726156952083660183314042778783172472328974258944659464126917639032187402371484073604743211066845837686249783634739285503728121012507780380100169770926604418124598760, 
    1013759487232776840238303359547232881170594255083054663824081867029534849603269365871684139107268, 265751980780621119639965766512248089092003190346959914134773254452388739517160636679915842085065873412, 265751980780621119639965766512248089092003190346959914134773254452388739366750919665462700331446065156, 267861614242116419587613743861396958727759822301872632520087247066536846062600695047550078193977286340, 267861614242116419587613743861396958727759822301872632520087247066536855162388573301323368630722780868, 267861614242116419587613743861396958727759822301872632520087247066536855162388573301323368630722780868, 
    282652075099169, 282858233529377, 282858099320097, 282858233529377, 282652075099169, 145273514952928, 
    730764756684380085771162657736969578509991281059, 286152737294560, 286152737294560, 286152737294560, 286152737425632, 286152737425632, 
    72024525441248, 22858351047123333572125618401376063738079618466, 107208863975648, 72024525441248, 353500777220320, 45694401242704623429275826335243551812037911970, 
    177058420492512, 141977127618784, 423590617024736, 182710702397577907346370004063626769762905236898, 282857998648353, 107208863975648, 
    267859836218979294226255815674783841992371157976059123014675909738731654330664319981473364516694679140, 282858032211233, 282858233529377, 282858233529377, 73121890044128, 143078384470240, 
    72640853706976, 143078384470240, 143078384470240, 45761303733511990506735441748270351814962455970, 73121890044128, 72640853706976, 
    143078384470240, 143078384470240, 143078384470240, 213378409171168, 495061758904544, 213378409171168, 
    213378409171168, 143078384470240, 143078384470240, 730842809579771226543529861293919163208168409507, 66437869465220763316143089532826203076183816469337811173324744278456952072545375273679045457136678821, 72640853706976, 
    72640853706976, 213378409171168, 217845108050144, 72640853706976, 213378409171168, 213378409171168, 
    72640853706976, 145273112758496, 145273246976224, 145273246976224, 145273112758496, 730842809590322014007979188281376629278060349859, 
    81653842577888, 45850507054588401306095793195268362864916178338, 74839876962528, 74839876962528, 145273514952928, 145273515149536, 
    145273045649632, 145273246976224, 74839876962528, 215577432426720, 215577432426720, 215577432426720, 
    356315054999776, 74839876962528, 145273515411680, 145273515411680]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1462220837725027692691023284257529965084754339106, 1462934461573717213823874110075857536786866152866, 365735010231459617268013350523274501665040393506, 567906417052128, 576290260388320, 576221540977120, 
    576290260388320, 730753607641019241442657893732616452596327556514, 23192863501175745840095779653551053655664797090, 365733616434895093697784111679921228108804957602, 730753607641019241442348408722795107527602775458, 75325409397216, 
    1461551815368832926123128211632372211198017971618, 1461864025801861586047057333599365914037473289634, 265801654994861121644922141630124364459320159512994962550854097576193227683847684338470048259828735588, 567494167497184, 567494167497184, 1978643329836335140592690686526421833430612537154823769351938224490029921573027795498658007259620032974403815851170687845163022815922939385224941616514041311708185588077975334, 
    567425447823840, 576290260388320, 567425447823840, 567631606450656, 483185126816298234820171351724501363679806337778400351658588127492887094813368914105477460866138203509950085579225274185841126963695137912317470362410844312668365541627686, 123665318701671983413866819025650106695757048883368721278050779362242673695839192960410312099193094027284055744015302392654739690446453136819514226770219446488773512085133094, 
    154353076144608, 1464361709285021973446150602550081826811036591394, 154078197975520, 286157032393184, 83984332032480, 295090564499936, 
    549133572907912476917807655750492275991397295394, 145282105084384, 39660269144544, 145213385411040, 1464356308323294282905195726018535562581583095074, 154078197975520, 
    154078197975520, 145213385411040, 435553174948320, 145419544037856, 154078197975520, 286157032393184, 
    8305731603115938492920571009233281592937514445359178765361604142137423672376025556679918262163820004, 132891703662604395503988265812177299730413842243092909848667136779743517721192021549799693169927084036, 519108241116671371953828409392562191087098537843898660672870875833978280130435413864861852451947460, 519108241116730373346372956322793320320942213263676985642132414049623019096777253089432238477755332, 8305731602636274911227397069121149706749833399645219944371984070122237143096277516602898945847545316, 732538373664486156232808466748909940510525269410, 
    8305731603115896087687664343824449295200507578667502602275450862083353700974380070729893359594458596, 183045224379541785697475676546070231957979571618, 33222925916013647518885782615837792460351229938745275969008544877287232792559873798514047352026699780, 129777054357776070718133912971731955115520846189196740357625803703021495504200890602903288909146757, 132891703662604380758824459938844790636756069145287293468055198095656852389658393923676142199388723204, 1461551815369071773996777212709350514239574926626, 
    1461864025804187743913080395598770415434579092898, 7147416080006916720998194082959912737511613858, 24307904844490680048593705335867891963243570594, 290829688375776, 565707393796576, 567494167366112, 
    567494167366112, 569624471210464, 567494167366112, 732180859417113604374977741262561236913928840610, 81922479163872, 290829688375776, 
    145694019291616, 45638595414496, 81922479163872, 290829688375776, 567494167300576, 567494167300576, 
    567425447823840, 567494167366112, 1461596415859567460007506726231617201245635784098, 184472472082881569544813289498750183585195009442, 91522617634299148217239185473701370208667088290, 732178774156135248332975104006689712163986646434, 
    732180864850997610578894622980277772947877832098, 732180864850997610578894622980279461804180546978, 73126184749536, 145694019291616, 145694019291616, 145694019291616, 
    91522607445766636584895032252979698546961331618, 1978960227047137337937550353967343415532603947628306018436219608623120684340357441179700943772017950447709344586659152250884384758127007497526647879376399765315678000570694694, 732180855333725201323561436754433417429318673826, 365400497777422781967333599184898258839869613858, 732180854653160467481549110062100387803376952738, 732180855333725201323445379875750413028546880930, 
    290829688375776, 73126184749536, 37941812464096, 73126184552928, 73126184552928, 571823494334944, 
    79723590257120, 1982507778792047447813099745238826145080490504249711556737909883741471754512636703052196055499995119954855121625796294150108993923497353534874554900862732293560668894631274279, 265751980781089470530943922150141062749314963993357458917967315101525958649463920281767972972460723684, 150092065802720, 290829688375776, 571892213877216, 
    290829688375776, 571892213811680, 573988191472096, 571892214270432, 149679749204448, 290554810730976, 
    1462930284270039358515993896155942087481690203554, 290554810730976, 290554810730976, 83984264989152, 149817456593376, 149817456593376, 
    149817456593376, 290554810730976, 290554810730976, 290554810730976, 79654870845920, 149817188157920, 
    290554810730976, 83640264952288, 290554810730976, 290554810730976, 83640264952288, 290554810730976, 
    79242553985504, 270472221129415927921911579156950594438578550429103657707254791299989516076583929639303513258759129356635294335097206922302649604203512177390720717714725177785786813103398, 149679749204448, 290554810730976, 92771453940837412314633365073023161840333006242, 149679749204448, 
    149679749204448, 149817456593376, 149679749204448, 508017829743072, 435484388493792, 1461864025804187743912926861876721031607816332706, 
    519108241116671372178928230869904874990520529797123246866659438241363569838654202242598237875946436, 8305731603115896087687664343824449295200507575849072671091620832490372633633906941502580606904782308, 132891703662604380758824459938844790636756069143832619944697580197098093713422138805750173221200812036, 565226424568288, 1978658337233789195929255607019526488043792779762954713959044679902283942670434296828660212279821346688013888397492745555226581813328830571711882571945021641867437027263249446, 480481306159211361205044992421904139309116810276696193309304011708559844123742763904871993587876554234101521370282335971446342873296268559226201403484196634271746517990829774265574312216700297965931268894724361236648758167827448215340857579465691378785198226373494280, 
    567494167497184, 1461551815624449700785402111983664041260455847714, 265751980781089470526216849942372440436434910608999412886021434634381439701790402429365534483858804196, 567494167300576, 567494167759328, 145281702693344, 
    290554810730976, 86252007721440, 154352942057952, 81647668562400, 154215503104480, 290554810730976, 
    290554810730976, 290554676513248, 145281971128800, 145281971128800, 145281971128800, 154215503104480, 
    290554676513248, 290554676513248, 149817188157920, 72645148674528, 290554810730976, 290554810730976, 
    290554810730976, 290554810730976, 145281836911072, 132891703662846066943595453450193440651524550998661831482680274840932285418233723795806143886437603332, 6846376585964146635852517423483800440743159074, 6846376590948770634804955370314099367342531874, 
    6846376585964177059466922900989436361620088098, 789589162433971101954725259937001143280514552194844104488075141645593803005135572043718763759620300308763699522943122408002590564682439471596113594892612396567129484533653700335464229488675716492167044825402460464885244248430197209009722489756401482667663506373494280, 77112250206688, 72645215783392, 147412274907616, 145281836911072, 
    145281836911072, 145281836911072, 217781019085280, 508052155927008, 296945923394016, 789589162433971101954725238201747851064952463496241034993738607821195169472271524499505246570245953376554335627697850238780408735867637334994960547281018430419958739459966767455180783368041274143172931252022302180269885163729666367858571120548455225992683666373494280, 
    508052155927008, 290554810730976, 296945923394016, 294815552506336, 508052155927008, 145281836911072, 
    145281836911072, 145281836911072, 74912958515680, 145281702693344, 154215503104480, 145281702693344, 
    571892146702816, 286514788529236939876521249966844314527623111065295314332003045960315182453498555997011549249396528069, 149955029633504, 567425380714976, 565191964166624, 141021095135712, 
    141021095135712, 281758717708768, 281758717708768, 431430006082016, 37701764254176, 37701764254176, 
    84052917357024, 74844171930080, 281758583491040, 74844171930080, 83777771014624, 75119251163616, 
    74844171930080, 281758986144224, 281758986144224, 290314560735712, 519108240874972279156275694392533670196802110141951485889056845330545911599697703322669849566725060, 154353076144608, 
    295090564499936, 1461864035332094017699212301364224781366791284130, 154353076144608, 1461596426387219338222037653771537851565419834786, 1461596426387717800621932897566220881458079772066, 1461551824896822276975747328752404680587782694306, 
    132932252556490215032027325598086552396264520638510421450137372161824828636941057098893660490864336196, 290348652300768, 41034290039264, 145419141646816, 72851374213600, 81716320930272, 
    154352807840224, 290554810730976, 265751980780847771439849564413872288447942985021105321683443985627022607640947422215195176960042159588, 1461864035330100168099660340515843877338601792930, 290554810730976, 435828052593120, 
    72645148674528, 290554676513248, 72645148674528, 77180701247968, 81716320930272, 72645148674528, 
    290555079166432, 290554810730976, 290554810730976, 435828052593120, 145419544300000, 150091998497248, 
    1013790893067621651452821627234581376713748168999199140399991591803688362280275137618542797737444, 84121300830688, 1978972169482188442710410721212596428335675104344016044271622441051799741202064799170829966027412546478661100605297694992648009345091526460290441697967915593762308546528017446, 281621144537568, 281621144537568, 149679749204448, 
    83640600496608, 3029820533684153960141529059138382891262100527190129406980324166180822762932324685321755637834027023077494799378437253750636746043915620840712063569286873979247073894845117478, 3544291016414190361441758630772792783979870391503066265956795240329787150629867846308316492208637196908557969708524248188825771919409643039540577526514130822874193551770516518, 435690613901792, 145282105084384, 37941812464096, 
    12845278235097714872136777554356777378979512739, 73126184552928, 290417237559776, 8305765022864604554528549968506889025086165026777084293732914850960426063974070226047205080710762884, 519108241116671371953828409392562191087098534940233975676226900835473820935257000218852769661141956, 74912958515680, 
    86252007721440, 145281702693344, 290554810730976, 154353076144608, 183045214851635582899632312352427707683849151906, 154215234669024]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [5887419192380130516333684469191404243483375010, 39724693719264, 36426158835936, 465453501664267720797795209429916886521042138783559987548995957224517491080502672306412857393191352357, 5753614230702594312420318140803584303657659810, 5798215891240839019172621309036184742553726370, 
    730848384776632031297095723123330080493160925603, 39724693719264, 39724693719264, 39653826693344, 37935370012896]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 52853902180385, 52853902180385, 52853902180385, 25691166256363432141173746545574496418155472162, 
    52819542442017, 52819542442017, 52819542442017, 52853902213153, 52853937867873, 52853902213153, 
    52853902213153, 52819542442017, 52819542442017, 52819542442017, 231214834006359803346208245375415963971043732898, 52819542442017, 
    231214834006359803346217916597505440267345866146, 1464356840503970992247621354444122707354970498338, 1464356840503970992247621354444122707354970498338, 145206943156448, 8305731486617877442339044042076964185842155957611411085236416249137242974942357004718766996484803684, 1464356840503970992247926003750665593906996454690, 
    8305731386073887209241091207182881895234835296019329943822973658755289299600266351208602024908429796, 1464356840503970992247926003750665593906996454690, 52853902180385, 52853902180385, 52853902180385, 52853937867873, 
    52853902180385, 1464356840503970993515271953528653976281681503522, 1464356840503970993515271953528653976281681503522, 141979275102432, 44264068751649, 6422639122844939304852713745168301801380774307, 
    7136265696773786878438831580175561012090503587, 185542907841761638677980235023983342751391950242, 8563518823446830029792405559545473509992956323, 52819542442017, 52819542442017, 52819542442017, 
    145277809985760, 185542907841761638677980235023983342751391950242, 185542898313855364911510298678060982012368922018, 182733003227852222152585135425329515100939756962, 145277809985760, 145277810116832, 
    145277810116832, 145277810116832, 145277809985760, 149675856496864, 5753614209537413504668113461052719625125626275, 20761861556619841419988321335348821939034818885040434145244181604487793866848005601360605602021328004, 
    519110189698536447370165170891302735150430759346441485194458449221446641370340303729496897655882692, 426898815846880, 145419544037856, 145419544037856]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 8563540622682844899221214088292641757578405154, 52819575997473, 52819542442017, 52819542442017, 
    88038308907105, 52853902213153, 88038308907105, 39724693719264, 39724693719264, 8563540623679687304198566921318364824436483362, 
    45639534905824]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 52853902213153, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52888264051809, 1464356317851190821214091112705485413568987276578, 
    25690643603583261112290615657535837193164563746, 52819578129505, 53060094198817, 48526606668269997706057584976374145528839548322, 1070533978515689484947038003168967104592652373452120565812104042810177802931673445772814486481161316, 1715551911768436610296182157688140210719829796130, 
    551489151990021713864485973180724018285712356224855976990174632590533518393062159921816608934216260, 298483232857638547424267314471374099526436733831483435523444613274900752701970774450017673435935694148, 1601372096331024478892762135605370201907778823458, 52819542442017, 53060060610593, 1532864207102073737914817952229228424280203076898, 
    1464356317830255401686141473557027770695238034722, 1070533963046947539657034285554931905992273121129537942682170538911524362106995149602730463150217700, 1464356317851190821214091112705485413584019662114, 52819578129505, 40003406673313, 44264001635361, 
    52819575997473, 52888297606241, 52888297606241, 52888297606241, 294849918909537079143610232820099897470147181442434694911357181119039023194440440159246677900014935364, 294849918909537079143610232820099897470147181442434694911357181119039023194440440159246677900014935364, 
    2040490908117984763998987327019999519126053333480672013532852457991004951977254914758403485285418981443032860769742947779073537656026481413501370684303911355714876398107622438, 36567487357217, 36567487357217, 11440325949337880977803542714391650557458147234, 35467975729441, 36567487357217, 
    36567487357217, 52819542442017, 52819542442017, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52888331160673, 489288346087263500381072930022711200453851714844168102167696518807840101114483326954844275911938600899755274147157997260455684421097320695695142452121587764103842808404491445392919414239819691539888394365722437461911016498148094744389327841400379515644936338123494280, 
    37460983155041, 25693256951225794466089313685765075635341370658, 185544998536624000923745010902364920642215093666, 185544998536624000923745010902364920642215093666, 465064439786856385438922903408617226965507330293298308673593821066325040407509658290892171739363139268]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [74908663548128, 81649816046048, 730761990869312137016391977923938253426483397027, 72709640292576, 74908663548128, 74908663548128, 
    74908663548128, 81924626647520, 74908663548128]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [123257008229473, 52819542442017, 52819542442017, 53060060610593, 123257008229473, 123428806921313, 
    88003949168737, 88038308907105, 88038309103713, 74908663548128, 74908663548128, 88038309365857, 
    88244467796065, 74908663548128, 74908663548128, 74908663548128, 45850507054585807702880917995646347990167729570, 74908663548128, 
    22836138690274803194855758005653349975275889954, 519108241116671366551432693936337777404994678301736743761140488753396877440731033818242518924608452, 81924626647520, 81924626647520, 81718468413920]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2061655289281225833874618904457487938326072042592502817932512220643533186752975742597876021849775130457443740324883265785218449796701943915906714460248471939835264817767096102, 266046002711381184379424523688343375107337012571898428582829114572851997698795813095619020666430316324, 1978900314817796389399478764382877701021308138230212120514905411354062441013728170470164995349341902613718897839564142025726922531009995548519268065933546529500798936276791078, 88003949168737, 294849918909537079143610232820099897470147181445344041914719767634489667883388618860262721274210442564, 290697560111706829943434310619952039434819309853098500487021003570256418949922631231122339952805829956, 
    88003915614305, 88038308907105, 266172690962021919697292735851170452031570670506998911488364747222541960292635062053526537193053510980, 77041114810592, 77041114810592, 88003916631137, 
    88072636140641, 68530364305397518190321767670843422602171000226, 72640920815840, 72640920815840, 72640920815840, 79248996436448, 
    79248996436448, 205535602220898081670538502400400015172607419682, 47099359323841281784456365722295680376861886883, 2094595317851095771304483548430715479423313084503385162367402275620346898309409754869224112012809870948264177572128802767364614485127652547518903040339014831685728144798510886, 143078384470240, 143078384470240, 
    46028913688781596734403014864969491939324897699, 149675454236896, 149675454236896, 47099353539041044128502486844931294701508626851, 88038308907105, 2055949058095781387003101637550174258092772887047365449471316915051993713886687537890958022500254443997252848953826280049903039710559079497541438769776584955459947336131672358, 
    88072636107873, 88072636140641, 88072636173409, 88038308972641, 88038309103713, 88072636140641, 
    88038309365857, 294849918909537079143610232820099897470147181445344041914719767634489677434405650118517007836876135748, 205546665480879106932982911363402548978226046370, 143078384470240, 145277407725792, 149675722672352, 
    290697560111706829943434310619952039434819309853098500487021003570256428500939662489376626515471523140, 2136371383162228786594542792296385123352331445452078294165780759759046489946749703306625047958448997, 2112041155725448815469932363044860630960763269127525007077518729194131069846932753309547968323971941, 290554810730976, 290554810730976, 290554810730976, 
    283957740964320, 281758717708768, 290554810730976, 290554810730976, 286156898437600]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [145277809985760, 730773163054542782734972331078658106105648153507, 143007450400992, 143007450400992, 154219798071776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [265750982861125756914852728429405599075739489441390583035347204343436207838281403496459041504381409316, 267827178100032633491904496351340897074709294321924903398482821027567087169927339502600300372736121732, 267827178100032633491904496351340897074709294324834250401824238621625343864347874985797384988108299140, 267827178100032633491904496351340897074709294321924903398482821027567087169927339362520337563004214148, 141908408076512, 182699551982448538466540463099196657551389762978, 
    182699551982448538469016343177767488470200624546, 141908408076512, 182699551982448538469016343177767488470200624546, 182699551980117837340611440749838653765571847586, 141908408076512, 182699551982448538466540463099197150132599006626, 
    2061731269759991664846052836663579457891158008231588906808168532526001000591816967998795872890828035730921543526612456082802701383936417609685740054270346868544052105392930086, 1984455585664477028568809030374346478108303835686229062568202306217894670059775830506787279049615971739376194273593796773026813645904403685039925361583291290322969739506203430, 2055949529841084496554073920909042172475589975382329359627253410081576389191794124670587277371312807943559252998395019798331638023967068688474340609513475202503580059488468262, 2055949529841083617859763927192093301712629584714892372184487179095745613156224677602404428316776051888282526109280544383906341135088827637897566365864686625692101957257247526, 145277809985760, 91355351208114354403475324413267069268765213091, 
    145419543841248, 145419544037856, 265750998701117862943223901984317738958324097915146820584408074810103994801838179669143949166488098852, 141908408076512, 177307528530400, 182710702397583099645704418969825638579924641186, 
    141908408076512, 182710702397583099645704418969825638579924641186, 141979275102432, 141979275102432, 274054903178909382097658228604688634568434529698, 1978884747222783456185379191100483388765130552759692159062909161175373963017227322123507368239475599001387279487259153398521750940868570781464215182889323726495553948043161382, 
    177101370296800, 36567892888032, 142120506106145, 142120506106145, 265750974941130352994913394462208287709038552884347990028099816596076612092351486195509153118735603748, 266172738481514013483871839099566530331691939443502937101089678349316317422764283875190163189055445892, 
    2055949087579862832631098460003907426653871721291415115516535196592893381546902092478850002921325882386147011201549551167413145383438508414148098366829192169305976584228814118, 141983335589153, 2055949087579862831343948898729418105095492160187949494169065401623911621819793860273346051292689658797874772330557749958021702110327958749165373232163255472844696070038469926, 141983167815969, 141983167815969, 7507516832302367192652483253244979699790055386976665147800043603409528310921065727677256072511933292263619987216868489598956821832204933392748807857420404339928174482827169814457602913890587914350444222417440471940879423331648569208962534515670342604689408624938761, 
    142120506106145, 142120606769441, 142120606769441, 267827399859917987289356521017186770752455264120738897263678767967937153547806124853532359017360300932, 143007450400992, 213449209022688, 
    143007450400992, 213449209022688, 143007450400992, 143007450400992, 267827399859917987289356521070749930471533447932010199701088550713482336128123462017637188436851547844, 72603239188704, 
    72603239188704, 61847698525019292216490946797538490115393894473320702541477920257723991018837399702550405595137103054667343456125344709446030508543985654392957833217156428537219267577233191, 213377234766048, 213411594504416, 72843757357280, 72843757357280, 
    72603239188704, 143007450400992, 143007450400992, 213449209022688, 143007450400992, 143007450400992, 
    143078384470240, 792306961689388506684453617584087131700937112478872206797726003026398118531135045449497015417409183509011798730569770269769551950173541071002117560537609084280144784040335639428691065734091221444092858515700964714062634176865696775713863198772485135412503174124938760, 213659863747040, 495276574378464, 494932976994784, 495276574378464, 
    494932976994784, 495276574378464, 213384985840096, 72851508431328, 2061745908606541914952150974943445585610870548683565264337434472195226997204009294216098617533775004787195661917929523797012201552314332814577514529394851681947290844438445350, 143007450400992, 
    217778670274784, 143007450400992, 143007450400992, 217783032351200, 217783032351200, 2061745910909984898205864368490382008694135299717469822196240806941287661193336792425361971725779166466454842205510535611105484647799271033404816336134404135870534657792523046, 
    74802262444256, 74802262444256, 23014456837900747337317209065869166747343923106, 215548575615456, 74802262444256, 268348214836466031797398759630235131412040269713719808484087072282594607453891499590257337585869298564, 
    145206943418592, 74802262444256, 2061731240275910219211561607993001517250670233704376903137807578193119270772279968800145127656248359045107191665736498732682649778509968569478218639872264820393408921093520678, 74802262444256, 145206943418592, 145206440102112, 
    145419544300000, 24264000231259053209556543032274940697388787618, 24264000231261649358002735472127415011982718882]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 141979275102432, 143078384470240, 145277810378976, 145277810378976, 
    141872974563552, 141872974563552, 141983167815969, 143007450400992, 143007450400992, 154219931896288, 
    184472472080223144155121228887542964962395202978, 154219798071776, 154219529636320, 154219798071776, 154219798071776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [182699573757944794617084688246001841376428828066, 36319858297056, 36560376465632, 36319858297056, 265750982861125756828414396982106008458777873180850625806372260126224144021028388124972502096068762468, 177061641717984, 
    265750982861125756828414396982106008458777873180850625806372260126224153609647704914796093861597829988, 293620581232945847493211593727647236985827085781476059375169064428129716293163798421976042561522917060, 181459688229088, 181459688229088, 142120506106145, 142120606769441, 
    145277809985760, 36319858297056, 36560376465632, 36319858297056, 16644916896610468799500667002392999934239683651223317077601827062003096010959942945736259253586946917, 1978884747222783456185379191100483388765130552673384691782717461892302380442468713923459093698566108550449063898848436970372927397801950722682997536099106467919521425157762854, 
    142120506106145, 266140298178405964661995464641367308297761028640811635586734995548465049601815520976699171409379745476, 1978960226931968659573647587527104413491235024342355099104501753468739598685597348265049992646295083894402286557294304464845045926690584166281956506808100454938914290247118630, 141983167815969, 16609466995054674195244532438047471809325590814198399817917516559413619403642658162805794135925717029, 142120875205921, 
    142120606769441, 149817087500577, 267827399859917987289356521017186770752455264120738897263678767967937143996789093595278068279986396036, 268086922284782377864367516155324933515514546220378553412493992115760363069212496045000632050606185348, 72638706223328, 72844864653536, 
    72638706223328, 213380556654816, 213380623763680, 72638706223328, 72844864653536, 72638706223328, 
    213380556654816, 2060175898774820516892233155551772666500216796965897871287526449776490690232195924813495577515915516601089301561798788542860875643892850465144151339356189684664781156679401254, 2056311361251803258540819578611959834985449549431826431822817976523128155354877815494970937951259838099274546306849413056034945164383895194682292629006012370693679020759826214, 143220017734113, 213380556654816, 217778670274784, 
    145277810116832, 145171509545184, 141020994478369, 145206540765408, 145206540765408, 145171509545184, 
    145419040989601, 145206540765408, 184115676480034064056470313837386905311378941346, 184758223112416, 154215134011809, 219977626421472]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [290554810730976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [33239147552566898678563874142506517370087268623019593213977125988759228976825051697911986692109101701, 480481077044049878458912907417718748290626573045958609004026016343487814498964475572246920704138878351345714889004766477229361986775118360322891423643928200370233848189392646273630503553560544916099481215472632471849438502942329540574338108123095226562642051101894760, 293685469759142831205881779647695335677473993825384518448654942212292009188776358877465152464436108164, 15473246058853430599390408588228780699319226675480632828478765955111084406752071790257495154299415296456242219363195474329066941063883773436010666170862465786745831903942438, 282857998648353, 282857998648353, 
    182733003227852222152585135425329092886864078242, 213517928499424, 22881261642454015615778646946925102013618857250, 213376194578656, 143078384470240, 182733003227852222152585135425333455765646091682, 
    293620597072923317653419513523449053683005999894095278030689724847555044967653697440199218760629902660, 217778670274784, 217778670274784, 503866307643872, 290554810730976, 145277809920224, 
    215575217834208, 215579579910368, 215579647019232, 215579579910368, 497063280773600, 215579647019232, 
    497063280773600, 145277810378976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [730753607641019241521576571237059445121146725794, 365556604269871372441303539034119245609224922402, 730753607641019241521576571237059445121146725794, 294819981298144, 294953125284320, 294953125284320, 
    132891703662604380758824459938844790636756098937000607900934604581923060191668923471964677448615024644, 290829688375776, 284234564569568, 290829688375776, 290829688375776, 732180855333725201482017761782962092616406574498, 
    365400497777422781968571539224183639114768738082, 732180855333725201481901704904279088215634781602, 290417237559776, 290554810730976, 290554810730976, 290554810730976, 
    290554810730976, 290829554420192, 290554810730976, 290554810730976, 290554810730976, 132891703662604380758824459938844790636756098935545934377576986683364301515432668354038708470427113476, 
    286023486015968, 290554810730976, 290554810730976, 290554676513248, 296952365844960, 294819847473632, 
    295094859467232, 290554810730976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [141979275102432, 72020230473952, 72020230473952, 72020230473952, 182699551982448538483871623649196414632739743138, 141979275102432, 
    45683163715280236269697202798564923492958481826, 183044539728828574733976927207389737759537636642, 181459688229088, 145277809920224, 181459688229088, 282652075099169, 
    282858233529377, 282858099320097, 282858233529377, 282652075099169, 730764756684390470404493808649358808299421696419, 286157032393184, 
    72020230473952, 22858351047118790312374400427201099553791550882, 72020230473952, 72020230473952, 45694401242700729209107805293092914489589247394, 141979275102432, 
    141979275102432, 282857998648353, 109404666038496, 267859836218979294226255815668913906680691357010599455061440022269377831463920149203646336150214427748, 282858032211233, 282857998648353, 
    282858233529377, 282858233529377, 281758487019553, 108305154377952, 73119742560480, 143078384470240, 
    213380556654816, 143078384470240, 213380623763680, 143078384470240, 45761303733508096269236260156124390643926052258, 108305154377952, 
    73119742560480, 72638706223328, 143078384470240, 213380623763680, 495070617274848, 213380556654816, 
    143078384470240, 424699390069216, 143078384470240, 730842809579781611176861012206308392997598824867, 72638706223328, 72638706223328, 
    217778670274784, 217915975010528, 72638706223328, 217778670274784, 213380556654816, 72638706223328, 
    730842809590332398641310339193765859067490765219, 81640957675744, 145277809920224, 45850507054584507088403652231688486092265762210, 74837729478880, 74837729478880, 
    215579647019232, 215579579910368, 215579647019232, 74837729478880, 145277810378976, 145277809920224, 
    145277810116832, 180360176601312, 74837729478880, 145277340616928, 145277541943520, 74837729478880, 
    215579647019232, 215579579910368, 74837729478880, 145277810378976]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

private theorem tv_b10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [1], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580612001957984, 580577642219616, 580612001957984, 580612001957984, 88236951144544, 88236951144544, 
    1461596415838943819066141803272144828631953722786, 36833677312033, 580612001957984, 14272531372903084953836162937035596384640175522, 580646329190496, 169241061330642844097831491589819926591938434911455703199782504276684730634331902834566379442526164164, 
    2108619733444055736040516974455955545361557547850711074147200127984256281026626218759683525346268356, 169241061330642844097831491589819926591938434911455703199782504276684730634331902834566379442526164164, 16641875742412316784232257566029626371375643636297592541635400495133515354707770948498688220822967492, 580612001957984, 14272531372903084953836162937035596384640175522, 88236951144544, 
    565430503020769, 567627311485089, 564325454709793, 567627311485089, 1464361708243561616335624400007535491143191514530, 1461596415838943819066073970941727094316449942946, 
    565219046984032, 259775868603384269922685981980179434430755927206987759693095226922730014082603537482679015459246436, 283950497139040, 73117594685601, 73117594685601, 265783439004225734624146363603288008423510853539136781768284152145582552341306118535602767749997211332, 
    36834985903137, 73121889587361, 1461596415838943819066073971495707003184241741218, 1461596415838943819066073970942304680972955192738, 565219046984032, 37694253304160, 
    283950497139040, 37933188939809, 1461596426727979560536104801770292118789537959330, 268346440765117631283758124814127022345128734839012224742345670040950418581141374730956925012657793605, 73121889587361, 45761303733508096284159240621020199999413168547, 
    265783407324242938773040517788746352726518614462695014733373971528285669464926031930727151741236325220, 290547566905696, 308182880614109742061827413289012068044934707198677604865781843379179088472241007526973892669910724, 290547566905696, 45390834698592, 45639669130529, 
    564188116419617, 564188116419617, 564085171422241, 36834986165281, 563087531048993, 567489872531617, 
    567489872531617, 1461596415838943819066141803272144828631953722786, 480481077099545422682419265944113133141282504613097243343720657884441890750682224023574175446043707614527355213940466720739218457808234589192612970365518864775426831841803942599215845812486547254500257655332576193422060072385734248346733119530796474903314466107022760, 265783423164234690750004324612180051388730070258309611647188224306268488718040014684243390126677387300, 265783407324242938773040517788746352726518614462695014733376617563951175498281100102989468976508135460, 265783407324242938773040517788746352726518614462695014733376617563951175498281100102989468976508135460, 
    265783407324242938773040517788746352726518614462695014733376617563951175498281100102989468976508135460, 567489872531617]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580612001957984, 580577642219616, 580612001957984, 580680725629152, 580612001957984, 88236951144544, 
    88236951144544, 1464356230722953767981429428604622335286845115810, 88236951144544, 551485161054599252787988895017918044733462245858815589912980910746174105318112906017684354607936516, 16641875742412316784231367965586808976709091425926981789136221745565389600382828527746122385388270596, 53052580104288, 
    88236951144544, 88236951144544, 158605699516640, 268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 291962732323023105016161381018474482305508768725846788929609031616708031115628198849315309206434820, 2108619733444055736040073891616489864368968325111015578584936645033550915604687535029340383113180164, 
    268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 580680790706400, 581093107467297, 580612073392352, 580680790706400, 48526606668269102587545057650434698277275838370, 
    268897676423098020835752910817277330914779316246829700504291708656512897315263140810134224468999682629, 94198707059431611313507970450807273965348206498, 185542907841756770742224858991028576161439950754, 8337157961126915040399697926093429867676917339950111405565199488100261075607936967580425491974212708, 36834751054881, 36834751054881, 
    731110419564175286665820176719609388776009803682, 564600567268385, 1461596415840937830925850615735519189187623921570, 36834985935905, 1070530010783380518061108374468429168074762601874704643645948715347802131957314092800724998615485540, 2108619710240942818105729504726730330420949364844807885078727694022144476941968104298302564686966084, 
    7507745940037755093449473433490120066569316925435963047549644266088334985627070674018392591318553281965412518238046823966505954660635160975758646078666864166795874663849014460459941522784628373444363207791253599120778328821482730227738950138433887862259978249938760, 94198707059431611313585341998410515416177194914, 30931396034738014376190465486022130231392233066662287727986142085845502645105290083969916831113652393928535040318878703072571130762908244190892245462824040894441730991793958, 185542907841756770742302230538631817612268939170, 185542907841756770742302230538631817612268939170, 185542907841756770742302230538631817612268939170, 
    83827770757906992197027132560565223727344151818176841190108093235568687796968320851787392748709577092, 36834751054881, 36834751054881, 36834751054881, 731110419564175286665897548267212630226838792098, 564188250407969, 
    564085171192865, 564085171192865, 564085171192865, 142388102202401, 36834985935905, 1461551824907269542626679691847602394153183872418, 
    580646329190496, 580612001957984, 580749512214752, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 25690556470693892142321573237587390457493065122, 
    185542907839929074642041993834789134438127636386, 7560670634477546039554829970952216529291147244499708391564956530749636980267856197212295711345661052441883610296435374791084934987324536281450616384569574533844712175087069066643469565471625823492928040373201925559843339817232355508944610847034492059674247998760, 2108619710240942818105621310079871561278143002039008692250637211138592345828763223419839621856570692, 61847696221575429410295888569120643854407946574120795219496089964728619452921077268574564204384700432377775789552897002435665529646469769162777131212681466899557500409846822, 14272531372903247213731962170041678100100025762, 94198707057437761713859239642861664601851301282, 
    580646329190496, 580612001957984, 580749512214752, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 136022191427531850685163010752682271685435170271065708493655892372809286424045559651947175912136584516, 25690556470693892142321573237587390457493065122, 
    185542907839929074642041993834789134438127636386, 1978658307756457001175676491339305053670083847336631991890751242200445304622619723136463140379294878323507745156405545394747867640609410686176502672026272454447458402431489831, 2108619710240942818105621310079871561278143002039008692250637211138592345828763223419839621856570692, 61847696221575429410295888569120643854407946574120795219496089964728619452921077268574564204384700432377775789552897002435665529646469769162777131212681466899557500409846822, 14272531372903247213731962170041678100100025762, 94198707057437761713859239642861664601851301282, 
    123421290727520, 88236951144544, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351526178370926382825721534092318953103670718174424119329185788576830694338878844557781286032910710689422553902452623873990057666526701974999530886347673382191768792548486618074901339582464486231871538912960222515656341996994752960799037203108568009715665921153204216701908497077194728422621327257706615989181783185410547749396684621433172105626132111176179217887604293375585249575061890587333070652089718419241680632333119825792068387873447150074385988539986849667476727416845296400413797898030, 3879633372745541415433854513852050427088000117636720104180501520882363705875575086950881571382111014117885115789965009470225529863325236900046457883608445097515589106114343, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 
    268897676423098020835754222784629449697508914397199707173454007144514416875423302826728710623033634116, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753791723415774950540978816935120839323607496020639148230205615305797115337321796, 268897676423098020835754222784629449697508914397199707173454007144514416875423302826728710623033634116, 580577642219616, 580612001957984, 
    88236951144544, 291962732323023090610657254772178293171664489403645248142160383110305540511948644479431920431738180, 8563518833978308804298379707902786119182461347, 269416721272826801985775785432765670043568572725798129600296712030446645944750525532875624888011926852, 580612001957984, 580612001957984, 
    1461864025142214023833124976117491504732488864163, 1464406309568469972113685397546951697302909617570, 1464361708078072910867402326110406400579897656738, 1461529513368741919844010188983178934685372791203, 1461551825077410726087148923579325797035099555234, 268897676423098020835752910830301249840124854773556135300744547796085902187742673734700779388487559749, 
    290829688185121, 290829688185121, 290829688185121, 294849918909537079143611153333285870490155820079071965399734158208058396504680399731268051561222203973, 2108619710240942818105842851499629993332460792546121325184346295138245333466923179694351232165555524, 568487512773793, 
    1461551814188374984617118092751338359201336919458, 1461551825077410726087148923579325797017919686050, 580612001957984, 580612001957984, 1464356230722953767981497128708739072386530805154, 568487512773793, 
    88237152471136, 88237152471136, 158605898811616, 265751980780613625436517173604054780705892322982543114378925411945865652551958083734664420928430172261, 265751980780613625436517173604054780705892322982543114378925412571682808317443788163698077847886391397, 368229994557999773226442495693887441112220059042, 
    274055744047704776410971997714469678247690206935746917202959971698474688800576362478529295353633777573, 265751026452044276166602415778491193089281909885187164068933757170738837318497420092549764309637605285, 8304780986568768591145375763158153178624701317834816914121106810927441374050098545772864071651239845, 2855889187304084711713420837306850823379633570, 368231298520029814262634629016377605737362769314, 368231298520029814262634629016377605737362769314, 
    565253276699104, 565219046984032, 241563079273537770287932958213530655028630354742917182953448563258685873933604237710258905173768425625088709446213866076548443345365114992217434444926813439562102869045030, 283950497139040, 368231301242288749630142336723374465191508460962, 368231301242288749630142336723374465191508460962, 
    368231301242288749630142336723374465191508460962, 368231301242288749630142336723374465191508460962, 368231301247605681895691603866660117379881125282, 5798215880631800410887509447884956026183788963, 182777604896386634544130681761837398258129873315, 366090429719180606605203162546239534537992848802, 
    290547566905696, 290547566905696, 36843609662753, 45639702684961, 37943121292769, 45639702684961, 
    125665047919343617216252820948522021537792395170, 242005340505767904011487671634643433504737492155277540854817659156418760284083539250883594019534248943194269591323450128441857752838164609771224652997163691932660042562599, 217009248701668776644989052375788530758570215330, 34610801486660014261534719139200947406573667746, 45639702684961, 234839012131501401984529677125161640868286971066506092906173614941987112300637658334319072332966851951856592571976177619657059476285360865382242941748921385367480977640730283563607510772615291597911566352553207775176758638527158372739003740724802313256962123098760, 
    283133106988321, 283132972769569, 290829554164001, 22925253537925832852677935695346407836603647394, 145274589710560, 286431507653025, 
    145274589710560, 36833912161313, 283132972769569, 265751026428841163594421611852727993497435433042382902114557289600231982615179209489328552577548176485, 8304780963365655673211246048196591111122040374848601116406117348572512697936314897029611674013813861, 45716702072969851720940281905737890841555380643, 
    1461596415838943981325969770728713084899701591458, 1461596415838943981325969770175310762688415042978, 565219046984032, 37694253304160, 143350451931616, 283950497139040, 
    37934262682657, 37934262682657, 37934262682657, 1461596426727979722796000601003298200504997809570, 268865485614847297792796352618851042197989992187417771103196579790859561048805964678854012970336342373, 45761303733508096427692585073970491280451447203, 
    1461551824907269542626679691848757567449014502818, 37694253304160, 144449963559392, 283950497139040, 45390834698592, 154345568209376, 
    290547566905696, 45390834698592, 154345568209376, 290547566905696, 318318418601249, 1070533963046947539657058221526342712726549979971262112255902338339607315857488093891029168167079012, 
    14272531374897096891332229679021916181357659043, 4184803061419635131295651447518274647129661373965263450336255496782421733566623013410378740736740452, 480730579174438581968289717475574934246283507193188650921838329547458500783809725172236344242044307581129060692063852570225903715140935782121298180541471278171308631651145319229195394362812112943829387097248372370167317197779482519332162032111174243005235202123098760, 8337161859249885253480418372252480585866386038977688922054852126185349722143133516704324194581630052, 45639669130529, 17729763672097, 
    318318586373409, 318318586373409, 158471546998945, 155307641014752, 3354202804493645814748870298199752719705254241588016358342634337923820016949415689613989862007182004054652638919985186226517921330431788446400121691678523596789852730623100325340585383832176406099910314106850710421447909948480166577943632920701216204163062820829662668955604314465325617829930536024367105732699202548987036064846141556154960963356693042176603859279278253577273898, 158405042116833, 
    158405042116833, 158471546998945, 158405042116833, 158471546998945, 158471546998945, 282033461141793, 
    45716702072969851720940281905740001911933774243, 730842809590311953894439635834997302461081357730, 45761303733508096427692585221546555215384160675, 45761303733508096427692585073972602350829840803, 730753606439376647941404261230219405299173328290, 290307048737120, 
    290547566905696, 283132972769569, 290829554164001, 145274588760288, 286431507653025, 145274588760288]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580646329190496, 564325454709793, 567624123810849, 2415337909841188095370712234775366329940453084132835857266049504924725359055737824086313825244435698113625555515733320703791997618422932927130876340507898974831970862671654, 580646329190496, 580646329190496, 
    123421290727520, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351526178370926382825721534092318953103670718174424119329185788576830694338878844557781286032910710689422553902452623873990057666526701974999530886347673382191768792548486618074901339582464486231871538912960222515656341996994752960799037203108568009715665921153204216701908497077194728422621327257706615989181783185410547749396684621433172105626132111176179217887604293375585249575061890587333070652089718419241680632333119825792068387873447150074385988539986849667476727416845296400413797898030, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 580648478836960, 564325454480417, 
    565425436073185, 567624392152225, 567624392152225, 580577608665184, 580577608665184, 580648476706912, 
    580687135738080, 1461551814183058052351566407747190105717760066978, 265752994540108411252272281131948634137862342345329376603206483602215547622169549049995749800335678340, 564325823677473, 564325823677473, 1464361708588496461248882028300339658628276687779, 
    1461507212527836739910363371722207058301473523106, 1461529513358105862263739523306341408103803127714, 1461551814188374984617115674890475757906132731298, 1461551825077410726087146505718463195722715497890, 265752994540085751962200810330748666540694791401796776248839312137504071611063059066227675669033714564, 564325823677473, 
    564325823677473, 567624358565025, 1464356230722953767981422175021998432235200972194, 88236917590112, 88236917590112, 94198707067427454380637360583561794639385597858, 
    567624358565025, 1982749284860969392887280207987783610871466996499715810074701766986012142199930256843420905335557281536995470394971298990700930294072251032205285481135405141467279224284882726, 1982764410194750122970980988588570105092407386125972114495166369041701948151521137401203421325884975014295109256012642819327829699128722755981148234415443998050459234917656358, 2968221476721395911463059958353637030322414197924683716333860813541162146582843238778888601151044450904936008831456644952262218590266075805562031838614423566094237396703880998, 283125590787105, 283125590787105, 
    284225102417121, 36835019719713, 36835019719713, 37934531349729, 45631112750369, 91411103124259396610367800923972526316529911714, 
    3381578341693589203573397599502001423639513874536637613221310728339829316874796487253223026680119849966547847779811295526602203675139398579783224951447040395043042776665879888771289405782298835781885756287199381360951160787191653843175950355377602966232978134527769802133505143970573051151282948859550946683343286998854869092510922792053880067272728644218934002996092895288807403, 142388236649505, 182710702416187494792801618027792928452528048034, 283125590787105, 283125590787105, 283125590787105, 
    283125590787105, 2062153481806272082696230099498809485374663185562076457660896771723864471687240533595123451007167003469957402452784032660537998172102876044099509281235822902922248959058492711, 142388236649505, 142388236649505, 580578715961440, 580578715961440, 
    1461864025804167289658714133649602292448175063971, 580613075699808, 580613075699808, 1461596415838362441859455598862257813112626611107, 1461551814177824197152664610067797544538059572131, 1461864025801591910099930732245425747610332038051, 
    580578715961440, 185542907841756801165800578694734280144485352355, 580613075699808, 580613075699808, 580613075699808, 1464356317830588357568695271320917333352907279778, 
    88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 
    580681799370976, 580686094469344, 1464356317832582207168276303168047247359289601442, 228842373646560, 185542907841756780883390975043062730293032256419, 580680791098401, 
    88238024886368, 88238024886368, 1464356317835240673301050880071292279017733361058, 48526606668269102587544453187528831558675071907, 88238024886368, 88238024886368, 
    88238025082976, 88238025082976, 731110419545566014228979025326678953383424164771, 132876499250053204127652857062343501514054441412196596376778551283343757072117136448543640861693941573, 551485161054599252787988895751659964160240593110359001461221882560037137441668838095124126113264644, 488939176371167750122479837506656181880713256327783968008718928137630499674157553141026467699594272342208380717694967334119649877412147711245273705106453586113949278238775788022828987654694102913814260144579999718710659035175260194100678821683777910097313920622998761, 
    551485161054599252787988895751659964160240593110359001461221882560037663875678388681061817867629572, 234839012131548078085559836105080199830132563338198318611022250068046974525065296633660349376597227498932487400348255543883611114902617517719545809388974783844475022006519385603974406137512067969002604175890734842711639481328222617932207504951225870188562122998760, 282850713142305, 282850713142305, 290547294545185, 16641875742412316784231373977134354840303423123443909307375798524182157023640718156546980745872471044, 
    61847696218876081133648532114025352445965965699128136345754243197869796781017837059089805213469640129870189656078346966552879686632455327101377501606759866467488212049706022, 239867512599282460298726820536461589501687638947, 368231298520029814262402438815419302682451772323, 282850713142305, 282850713142305, 282850713142305, 
    283950224772321, 282850713142305, 286149248029857, 53054727620704, 53053653846112, 88238024886368, 
    88238024886368, 88238024886368, 88238024886368, 551485184257712170723207426278453692238237792974056778249639716234397629292367806759544118629702756, 158606773258464, 730764756684370066222287342824270999519756551075, 
    730775907099504627398975418616329149663840306083, 730753606354306096775833882898056501233614848931, 290547294545185, 283950224772321, 286149248029857, 291962732323023090610657363470801025536376144116876581682062578581469852247580880010041601814506820, 
    45287664297291153648993808650978138268244481317250563670330160614406471449324272285505525987296899035862993609343178554740246496181212267370373719589899750409497238656807, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 269416721272826801985775785541464292775933284380511360933836614225917810256486157768406234569394695492, 2108619733444055966542291085149140100899869405817194885692192211412797122692729368549036842889311236, 291962732323023105016161381752216401732287115977390200477850003430571063239184130926755080711762948, 
    2108619733444055736040073892350231783795746672362558990133177616847413947728243467106780154618508292, 1978658307750130403652078844387023550925337190128941335339870008173111329784261698424267587418865036631653673914376007536767498120442862374124968042252530295595862118915200806, 2108619733444055736040073892350231783795746672362558990133177616847414474162253017692717846372873220, 1978658307750130403652075570996415654783467132576529401807680038276438053742805961390967333919391516468557901239719110707364130424259195728813801516938705951306234377877935910, 183045258415733431442659162770716032405625643939, 142113359004705, 
    16641875556787413440751762143777470093037922804221074878260175784881357109795955222746260086824122949, 282850713142305, 282850713142305, 282850713142305, 290547294545185, 283950224772321, 
    286149248029857, 580584157186272, 265785719963038019306933667855116887407957207679802917800136637640007690955765678458397693222433418116, 1978658810821847388679108615728090579101047978651067971390831864667978036068914964279267975461877719973145713458247487217472370067234666897373050072632793955033044407770146598, 580684011931872, 564325454480417, 
    1462220837730002255269132840286975734142606771107, 1978643241384089909763846640838663517566217621753008739587996067383891851968163714416576312575760263035096576365305019323099566474405700406895824989303594373791173648048973606, 1978643329836334255033792478930624166828642580121624955203296598685449033502152596269628231799593697231084375488892598070056567149897712844548243021114342535062640154720818982, 580584157186272, 580584157186272, 256629561980004568547537148242723635068352586470684813130995139968140735703653191367933689101704056524915884114980518457546403268038815154592510599874165501662802299475750, 
    256629562921964637577751621226329656263099133917018383194382296224208889934676538586616993256519272046398497064536421679184748467731469186822593655338578177267449182443302, 580617442101472, 580617442101472, 228773721278688, 564085171422241, 564085171422241, 
    580617442101472, 580617442101472, 1464357014728881003962411330610203687763667594658, 228773721278688, 16641875742412316784231394584905083586404828919108361468810981153902126270517065813883039218458996357, 158471546996960, 
    580684011931872, 1464356840506301691967284378834157612050862843298, 158471546996960, 53052547564577, 368230612510778101650421410878405158918483608483, 480481077047106023417608928812220475621679691140126938132446925915845818451067871585851485674779503600845030881056129750655237608253697744866894986898412447880805374588361001744356287680997204065845466733522940692808401884709191053896157578041545593395879938624578280, 
    1978643215585518646978916083887156159871267932237536735174074438944238569036254857207932212696333830359420182067519764989913271592453338160472424492767452828466360228944434982, 48526606668273970384419034640617149741071345058, 256629444902802611661739412627240199085161552244778173243235960756986740629479012524466927876685169630196651010660950068126077086006890664238863144024107773695580581127974, 256658928973702200747542086469917423923579749103233441683948161990923798346693511671057231103149319381624985341298556766003577177861368323591714707605544658233161775294246, 259775868603384269922686089263728683130131485468566016744427326236565791813395494038655170418665508, 288621376783731252276945334416367344685631943167213647335793373173177097307585339572461144268354632261, 
    291962732323023105016161448155859307603112226308791559182205673817679543385067670516841524379085700, 283125355906081, 286424025007137, 2967964847334094142790534565495942894290806081588745824760363666416087143454039040971400032281964117562013341988928980736524487739552181626804592627772791707390608062505008422, 268897676423098020835752910709862756525011056959003128318165659576948934283754155627785639305082059333, 2092399566058740735068065036014131628472055539333215595492349126397264093748269972767056759030486116, 
    2108619733444055736040121984730598892290064572253298904587185658392444794017452800824077821914738180, 465066216835937661938260974420118238929494864333171955331588820126930513860957300690797535541515270725, 148985071338529, 185542907841761638558905876609777112021473961378, 989321635434085677161180641965087114300653893817659666921525389682807852426274726002283072800574735964671661775949301924111670603124108066973411608864548411697693072246684966, 283125355676705, 
    1984440019912342195969222754386660348744783430703271039525651334900562624373468978272959509454090119334829458194915764463288214899187813372483771881778855272441588476353160998, 36834751054881, 36834751054881, 36834751054881, 36834751054881, 17160510691429025185760866878542165099105616675, 
    2062168592398009454738483073582752505135686806555657344191751879816041378989950389955011373384394234210699757771692549331437069259438179541574865077308736997365389976064212263, 132875735960437393561945257729544290316199400617296354943943213104411722037246814990504141715744265316, 731110419564195731373076798821243516127178958242, 145274085835809, 145274085835809, 731132719118385533065640293497218937665729332131, 
    1483982438409087793570614092836927756076648413234323876023726887110886219417453821481492099791862292729260962945004370035641778919709488547275921178719928762804513259320753446, 564600567268385, 22858351047118790312341079409045840127043569058, 399673823145441, 1462215438485637117535219554264088352308708273059, 293021195251169, 
    564085171192865, 564188250407969, 568620656759969, 567486785393825, 568620656759969, 568483217806497, 
    568483217806497, 567486785393825, 36834985935905, 142388102202401, 327106055906593, 182710702416187819312595634354685742761533506978, 
    45631079195937, 1461596415840942698722724592725701640651419428258, 365767153431434634298232246806513907940846863139, 36834985935905, 24263303354094267839379794032493113305297618338, 399673823145441, 
    327106055906593, 145274320721057, 145274320721057, 36834851816481, 162201519890827817511536265787101897056688430089044941540925893613117369005752599293441561715644260, 75479248504339073950171048391661825880178811269791609704816428123630267173093951473673537873593226185371165783743980864686518509561406950282497291308893924052517132064550, 
    45287549105766743132238611743755674752840668836765965462870242264128797823041825421436451638355902483502400082387368534219350395076108937133483371175779989151133829977894, 36834851816481, 25690556491317449418341342858051310647612278178, 2108619710240942702854620989769378371493332699280136643416557431851649308117252986145175367680339652, 36834851816481, 37934363444257, 
    44531466765345, 2108619710240942702854620989772628414078086633454879002907031792481733166579700258732935756126432964, 2108619710240942702854832306403898621896351482245503451496233976121316639492875668088214478861184708, 36834986165281, 108303241972961, 36834986165281, 
    72019123143713, 72019123143713, 72019223905313, 72019223905313, 72019358254113, 74905442321441, 
    298937397101151230930536545322285907068455008716405370289812855926230733386576862681559111381363210821, 88004150495328, 2108619710240942818105621363643031080818009042086879280656051476713042161879809224100738728112237892, 88244668663904, 145274186499105, 149672233010209, 
    1070530010783380518061108401250008830808941323650020090672272810615024616868070985346791216033844324, 290697560111706829943434310504335278661232069711091651872526776330472898002617775934295241476430117445, 966149122907510248296126204581808566603189877065825473055087098563131319285553601390346849682955695287455925608994834009148524735293456218521750626645390215573554569369382, 283950224772321, 16609688693064941272390051504078365796348309773574930072459219318007600310722599722875078786511161028, 182866808207135930470836328696010979763768533923, 
    183045214849288909297845541368941381519352800163, 183045214854273533296870515141649719302077817763, 25696131656432430395413549300015874831639119138, 25696131656432430395413539855282838723604514082, 154207986922913, 185542907841761638598597329414512522271222408610, 
    185542907841761638598597329414512522271222408610, 145274186499105, 185542907841761638598597329414512522271222408610, 185542907841761638598597329414513085216880862626, 989336701756513946551633305859901898115936771060957333712967801314443117209407033117605087431733340660226519630279920940350038322847302712359872640711260359131573531414867750, 36834751054881, 
    36834751054881, 36834751054881, 36834751054881, 36834751054881, 145274186499105, 145274186499105, 
    731110419564195731412768251625978926374779921826, 145274186499105, 145274320721057, 564188250506273, 564085171192865, 564085171192865, 
    568620656759969, 564085171192865, 36834985935905, 327106055906593]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580578715961440, 567485577560097, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 565219913107552, 565219913107552, 565219913107552, 565219913107552, 565219913107552, 
    580578715961440, 158467252027425, 580613075699808, 580613075699808, 580613075699808, 580613075699808, 
    580613075699808, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 
    580613076158560, 580613076158560, 88238025345120, 72844862556256, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 72638704126048, 283744936659040, 72638704126048, 79510651799648, 
    88238024886368, 88238024886368, 88238024886368, 72844862556256, 730764756684369903962391543591264917804296569251, 730775907099504627398975418616329149663840306083, 
    72844862556256, 72844862556256, 72844862556256, 72844862556256, 72844862556256, 71748842689697, 
    142113359004705, 142113359004705, 282850713142305, 71748842689697, 142113359004705, 142113359004705, 
    282850713142305, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 143007448303712, 72638704126048, 72638704126048, 72638704126048, 
    74837727381600, 74837727381600, 72638704126048, 143007448303712, 72638704126048, 72638704126048, 
    72638704126048, 79235773892704, 79235773892704, 565220120988000, 72638911744352, 72638911744352, 
    283951302707552, 72638911744352, 72638911744352, 36834986165281, 36834986165281, 36833677312033, 
    36833677312033, 36834986165281, 1461551814348214975630118361056176158382355940642, 1461551814348214975630118361056176158382355940642, 1461551814348215056759756775662862287402244277538, 1461551814348214975630118361056180591621829068066, 
    354388768459104, 72913791748448, 354388768459104, 283951302707552, 354388768459104, 284020022184288, 
    81709884770656, 81709884770656, 79235981511008, 81709884770656, 290548372474208, 79235981511008, 
    81709884770656, 290548372474208, 81709884770656, 290548372474208, 81709884770656, 81709884770656, 
    81709884770656, 283951302707552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580613075765344, 88238024951904, 14272531382872495289618653550577857764354425763, 3879633488283271308237127022445478069148563303144059817457111187435128332419296479853459130020922157195460269839746976012994841792372220327809646156328562092116858722998054, 565219913107552, 567419005569248, 
    88031866652768, 158400680036576, 580578715961440, 567489872531617, 580613075699808, 580613075699808, 
    565219913107552, 565219913107552, 565219913107552, 565219913107552, 580578715961440, 158471546998945, 
    580613075699808, 580613075699808, 580613075699808, 88031866652768, 88031866652768, 88031866652768, 
    88031866652768, 88031866652768, 580613076158560, 88238025345120, 72844862556256, 37454332037216, 
    72638704126048, 74837727381600, 74837727381600, 79510651799648, 283744936659040, 71539192498272, 
    74837727381600, 282858229343521, 72638704126048, 72638704126048, 74837727381600, 72638704126048, 
    88238024886368, 88238024886368, 730764756684390510969158046183037295667714228643, 730775907099525072145846121975095445811797984163, 72844862556256, 72844862556256, 
    72844862556256, 72844862556256, 291962732323023090610653820755226275218338619010369664010978989490203098856654128942559288312802628, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 8563518833978308640271324502589899695048501667, 
    291962732323023105016161381752216401732287115977390200477850003430571063239184130926755080711762948, 2108619733444055736040073892350231783795746672362558990133177616847413947728243467106780154618508292, 1978658307750130403652078844387023550925337189955691787029207652894257074690548685097681052620524591009714317233839875294203864895868392266665764371597575545326035966550955814, 2108619733444055736040073892350231783795746672362558990133177616847414474162253017692717846372873220, 1984455114034234518000883447562533043956712728316072082953094598375293920300786394631407365641680283939554883781690996261135909942638124884223925211815345933074805822923447334, 143007448303712, 
    72638704126048, 268897676423098020835753791724149516861767552324333036874781215910617558970699990928363931610965421380, 282858229343521, 282858229343521, 72638704126048, 72638704126048, 
    72638704126048, 72638704126048, 565361783347425, 88173736892641, 580613145364704, 424688661039584, 
    564332970909985, 564335252416993, 564332970909985, 564332970909985, 567631606718881, 149879465183456, 
    217911749249248, 158606838270176, 424688661039584, 567631606260129, 220110772504800, 72844862556256, 
    72844862556256, 154209069042144, 290548372474208, 580750586087648, 228906865264864, 14272531377555562984456514080591337358092403619, 
    14272531377555562984456514080591337358092403619, 141908005882080, 145206540765408, 141908005882080, 142120606769441, 141908005882080, 
    142120606769441, 145206540765408, 145206540765408, 145206540765408, 149879465183456, 149879465183456, 
    212414191110368, 215712725993696, 213513702738144, 215712725993696, 213444981164256, 213444981164256, 
    37458763323617, 70439888488800, 70439888488800, 281752279452000, 281752279452000, 37525268205729, 
    37525268205729, 281752279452000, 281752279452000, 281752279452000, 565220120988000, 72638911744352, 
    283951302707552, 11440328570565367743033308425719527867049853859, 72913791748448, 284020022184288, 284020022184288, 72638911744352, 
    37525268205729, 290548372474208, 145206679177696, 290548372474208, 290548372474208, 39724291461281, 
    290548372474208, 290548372474208, 290548372474208, 286150325963232, 145206679177696, 79235981511008, 
    366090429719181580164345843301466300491149886882, 7136265707388342634524319919982323222617139619, 366090429719181580164345843301466300491149886882, 366090429719181580164345843301467426395351696802, 81709884770656, 81435004766560, 
    290548372474208, 290548372474208, 22858351047119439351919440637755609306152568226, 22858351047119439351919440637755609306152568226, 71539192498272, 185542907839182355235406472487471489145278827938, 
    185542907839763894701950923581263853753754717602, 15473245943568763756317697198856288555756411648462535514092352657905584472081764052843226046144860436390577905821329231195889201160587423491565172070603099765569535661987622, 141907936675936, 141907936675936, 185542907839763894701950923581268216632536731042, 283744936659040, 
    286081537280224, 11429175534194233246646589481466198968246994338, 11440325949328794423334665273524349077971010978, 22858351047119439351919440637755609306152568226, 22858351047119439351919440637755609306152568226, 22858351047119439351919440637755609323064001954, 
    1461596420943180458699566872517709444016308260258, 24263303354074147614771733514997364886413542818, 732180859417094133187327619702831531053103482274, 354388768459104, 72913791748448, 283951302707552, 
    81709884770656, 74837935000032, 75112815004128, 81709884770656, 81709884770656, 290548372474208, 
    75112815004128, 145550280755680, 286150325963232, 75112815004128, 79235981511008, 81709884770656, 
    154346373777888, 290548372474208, 81709884770656, 156614118607328, 14272531372904220773106757568078168392859127202, 14272531372904220773106757568078168392859127202, 
    25698832137525425619092898954269284462387275171, 74837727381600, 217843027675360, 497256766114272, 730753611724388173306269333733382035916720735650, 283951302707552, 
    286356692011488, 290548372474208, 286150325963232, 290342214044000, 290548372474208, 11429175534194233246644171620585583274533324706, 
    11440325949328794423332247412643733384257341346, 22858351047119439351924276341070096619870356898, 74837727381600]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615223183456, 580615223183456, 580615223183456, 580615223183456, 88034014136416, 88034014136416, 
    88034014136416, 228908945639648, 88034014136416, 290550519957856, 290550519957856, 564325454480417, 
    564325823677473, 265783439004225734624146370479393073482713426520553944321377951062398286185558108421523209513670356676, 2125093301300450100468358697445578821046335593247926585678523813163758314649594863508015754252037828, 290550788131168, 732180864850979437470565335558054178544102704546, 265783439004225734624145923961796311422433966033303569026171190688902569886287075280948685287575972740, 
    281754426935648, 72847018428768, 495059621906912, 154211216525792, 290550519957856, 81643379886432, 
    564325689361441, 142113359004705, 142113359004705, 282850713142305, 72640851609696, 72640851609696, 
    72640851609696, 72640851609696, 213378339965024, 72640851609696, 72640851609696, 213584712305120, 
    145140367231072]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [564085171192865, 145140366706784, 580615223183456, 564085171192865, 580615223314528, 5887419191224840058862115485528911268961866147, 
    365555209771630155308815894093576160389393043875, 183045214848961549958066283142791848103441335714, 88034014136416, 228908945639648, 88034014136416, 365555209771640539902532963748834347286261715363, 
    145139830360160, 145208619042912, 217776386476128, 145208619042912, 580649550415968, 268897676423098020835752910830301249840124854727006583246943173723451120789069063540535865114826336837, 
    71541339981920, 71541339981920, 145139964577888, 145139964577888, 145139964577888, 79513076107616, 
    281754426935648, 145139830360160, 281754426935648, 290550519957856, 290550788131168, 290550788131168, 
    290550788131168, 53052547564577, 1983307829457088769429797309470913580882050960887440899865002156957561731920466005503410358557293810274860453993952538476905323485159347189985463333480849107182478756448042022, 71541339981920, 71816427604320, 79512807672160, 
    79513008998752, 11429175513262706688850182165612667843293742498, 11440325928397267865538257957670817953017759138, 72572130035808, 732180864850982033628898123286151485985017857442, 145415123503584, 
    281754426935648, 281754426935648, 72847018428768, 495059621906912, 290550519957856, 86041560615392, 
    290550654175584, 45394055924064, 291962732323023105016161387622151757146513893989737492863777777941475320227631587546273252754387972, 2108619733444055736040073898220167139209973450374906282519105391358318204716690923726298326661133316, 1978658307750130403652078844387023550925337189956326400759394049072504593922926367543609712806304396321153991484115303066920890831045568538989774845941721600485865004005414694, 2108619733444055736040073898220167139209973450374906282519105391358318731150700474312236018415498244, 
    1978658307750130403652075570996415654783467132403914467227204079175831604568797629269248410659442788918925818380082052272657990333466825259038119381228906008515376028678969126, 81712032254304, 177301095713248, 177301095713248, 213378339965024, 213584712305120, 
    282858095124769, 282858229343521, 145140367231072, 145140367231072, 281754426935648, 290550519957856, 
    290550385740128, 36323076376672, 36323076376672, 282858229343521, 72640851609696, 72640851609696]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [88003949168736, 88038308907104, 88038308907104, 88038308907104, 88038308907104, 88003949168736, 
    88038308907104, 88038308907104, 88038308907104, 88038308907104, 36421461606433, 36421461606433, 
    39719996489761, 39719996489761, 1464356317830597444122860028369261287131264322978, 88244467337312, 88244467337312, 88244467337312, 
    37456481620129, 37525268205729, 37456481620129, 37456481620129, 44263971234081, 37456548728993, 
    88003949168736, 88038308907104, 88038308907104, 88038308907104, 88038308907104, 88003949168736, 
    88038308907104, 88038308907104, 88038308907104, 88038308907104, 88244668663904, 88244668663904, 
    88072636172384, 88072636139616, 88072636172384, 88038308874336, 2108619733444055736040626940042907433620073815289424947370696049047182806073723338637167832349217988, 88072636139616, 
    88072636172384, 2108619733444055736040517028019115064901420614545944225989845504011443736604979863938638915494417604, 141974577872929, 141974577872929, 72645146576992, 72920234199392, 
    86251682662880, 81716327221600, 72645146576992, 81716327221600, 79448844535904, 88038309103712, 
    88038309365856, 72920234199392, 81716327221600, 81716327221600, 81716327221600, 72645146576992, 
    86251682662880, 86251682662880, 81716327221600, 79517094250592, 79517303966048, 72851506333792, 
    1237089517601, 143426220198368, 143426421524960, 154215503104480, 141974577872929, 141974577872929, 
    142113359004705, 354395210910048, 72645146576992, 354395210910048, 72645146576992, 354395210910048, 
    72645146576992, 72851506333792, 16662150931854847291602735010499995435936558194535665299057769048228636246695806735369687908028849860, 71541342081185, 141978805735585, 71541342081185, 
    141974577872929, 61855273627806509114174205571252528999090903663295901043542356721576360289495786963711336457524271198336304842643368573436591862571044913229718840698853085673185103584405286, 16662150931431873879036211471346842833887687070030227342804624814545521634348174583160528272137985732, 16662150931431873879036211471346842833887687070030227342804624814545521634348174583160528272137985732, 156208168700384, 16658095893966341188868078299457483443111617403079724688143683607006492953514740834806443440633355972, 
    149542310250976, 185542899677648490886248036530871555253860853154, 16609688878692677949138540929357652285385570642293446444969101643764740444056179566847471860558267588, 16609688878692677949138338279066710463816504754277876983814299294819352053965739391078516227883074756, 143426220198368, 143426421524960, 
    147412283296224, 107825192243361, 16658412693801380727257013511749920061628984300903048823262674422955877650949962018622239028974264004, 154352950446560, 156620359731680, 149817188157920, 
    149817188157920, 154215503104480, 154215503104480, 146278537365984, 147412006472160, 154352614902240, 
    145282105346528, 141910086258849, 1237089517601, 284026265405792, 283751586728288, 284026265405792, 
    284026464635232, 283125355676705, 268378675140597766436307679246101858268862437160241843330867168230360159129676564603915547486458031812, 283125590787105, 282713139971105, 72645146576992, 
    354395210910048, 36838005837985, 36834985935905, 290555082901856, 290555082901856, 290555082901856, 
    72022377959585, 732180864861621090476662535260372308920214521250, 36833677312033, 36838005837985, 36833777975329, 36833677312033, 
    45694401242704623446606986885238876622701994403, 107206716493985, 107206716493985, 72022377959585, 353498629739681, 732180864850987225945563698742344412029872801186, 
    732180864850987225945563698742346100886175516066, 732180864850987225945563698742346100886175516066, 283125590787105, 283125355906081, 290554613598560, 73121890046113, 
    290554680707424, 290554680707424, 290554680707424, 730842809579771226543529861293919154549513817506, 283958013135200, 283958013135200, 
    365422798761882351792454754708936659053612401954, 365422798761882351792454754708941092284495594786, 283751586728288, 284026265405792, 283751586728288, 283751586728288, 
    283751586728288, 283957745158496, 283957610940768, 283957745158496, 284026265405792, 284026533841248, 
    284026464635232, 284026464635232, 283958013593952, 284026464635232, 45761303733511990506735441748270352777038799267, 37937483911329, 
    37937483911329, 37937483911329, 292822358428000, 292753636854112, 73121890046113, 290554680707424, 
    290554680707424, 290554814925152, 290554814925152, 290554680707424, 290554814925152, 290554814925152, 
    290554814925152, 290348656494944, 281758721902944, 732180859395918567746098956340897167716395812258, 290314564929888, 290555083098464, 
    290555082901856, 290555083098464, 290555083098464, 290555083098464, 290348656494944, 290348656494944, 
    290348656494944, 290554814925152, 290554680707424, 290554814925152, 290554814925152, 290554814925152, 
    290555083360608, 290555083360608, 283125590557729, 290829688185121, 282713139971105, 282713139971105, 
    730775907099504627398975418616329149663840306083, 282850713142305, 72645146576992, 72645146576992, 72851305007200, 72645146576992, 
    72645146576992, 72645146576992, 72851305007200, 72645146576992, 72851305007200, 283751586728288, 
    284026464635232]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [265750982861125756828414396982106008458777873180850958754718975889452488361516235511033550102486673444, 282033595359521, 1978884747337952134529170910556397484519752008648674045508824395945504120816365275663467456008695506022277275063175711830965955414864109386550046571580147178288400839330489126, 2040475814111039689397857420643758795689708851591337060684747891134538663367397210361611930915421217662980132632774311894968685133962083744452719974848688875556930929643479846, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511033550102486673444, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511033550102486673444, 
    290829721706785, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511031413695559329828, 265750982861125756828414396982106008458777873180850958754718975889452488361516235511031413695559329828, 567494167306657, 571789033906465, 571789033906465, 
    571789033906465, 571789168222497, 571789168222497, 1461507212517379170121915390068049675977473671587, 571789033906465, 571789033906465, 
    576187147563425, 571789168222497, 571789168222497, 1464361707903954088321324674728018087323545649571, 71612211136736, 1464361707905283321387731334400740310732272320931, 
    71745350928480, 71745350928480, 1978884747337952134529170910556397484519729297711208179822545758877931602696980553007513116903549313454443773739118959241060389663820978553296044477546101226311940952676098854, 141976725358816, 44539083530529, 282033595359521, 
    265750982861125756828414396982106008458777873183757464598898590493719165215735818536021787106150017060, 265750982861125756828414396982106008458777873183757464598898590493719165215735818536021787106150017060, 290829453500705, 290829453500705, 1978884747222783456185379191100483388765130552673384691772630548306025393764125279657824255934840393847572399016206808781252703828965304693007359874129675595153885396933259046, 290829688381729, 
    2076195269844596962910139223763065850744109725584943466560754848046564765094632692049846078913455684, 1978884747222783456185379191100483388765130552673384691772630548306025393764125279657824255934840393847572399016206808781252703828965304693007359874129675595153885396933259046, 265750998701117921836539516306935753456928530646428830703484854628345961701913507803790040728961611716, 265750998701117921836539522317749557401096751331072458106674895727511920858083703382176648900609636292, 265750982861125933832504980636721537844497694058277556915268938197950403390073909998588467665065645893, 212349699492064, 
    36354820409440, 36354820409440, 141907936675936, 71612211136736, 36354820409440, 36354820409440, 
    14272520570942007187085344688278493201298375587, 71539192498272, 71539192498272, 141907936675936, 71745350928480, 71612276148448, 
    212349764503776, 141976725358816, 2040475813996767279036676692917856389751479123634140620313394207462623933389239616034597158977855431627120060865865699373362957442625243017725818490352169228563438871390433062, 212418486077664, 212349764503776, 71680997722336, 
    71612276148448, 5954006363464895581091524976614863824486294635390292553502705106580754364486906074020514240682148079373731314775599232741753208208171908724591985657057527929702542421900194096160097844098341856906511104504298741227068526423831555153404523694844511877068294606724672512504778764360099082687069569956887702426133730840504228613863724431209775981782374329130958849118356524448022796100264489976016100769843873615169863698180781274617919516757924158169571395007926814152413468234088656411534605099166754329156405557256499026611713309312720842793140545804855533783382737166435223716735061228855894898726060261441834502974683967819191200914741403997148906356516485821143463936684334635022299697497603523556661761768802735136231740647448744329034192309774253670009662399436422334247169375392047970501035338003898512602111675783942893460997978900473574992637280642235276327736441912129000880308601888437028530436935572446151730685048626996302881572728339336603825743225514502843503711273904430293940092473136844579230946244444607026782399057508790363173173572582691378236804168652456853535639037607748179632153609067172140165425042931100665243807951316882163674297841733428003052875185223052849753406639646137014429442831149247541, 141976725358816, 2040475813996767279036676692917856389751479123634140620313394207462623933389239616034597158977855431627120060865865699373362957442625243017725818490352169228563438871390433062, 290829554164001, 290829554164001, 
    11440325949328145383785318393828641928123000226, 290829554164001, 290829554164001, 36842535691553, 45638628975905, 480489325051325295666342253388956945115538779346589577666126262277530851069531532253996457279965911310956058043481948408454164119039791090533652941115611996734693721037541189401037413136867936007439963636124989518399427254476259569127239058774758052149084170248495560, 
    1932269682998647193295653558742663277806926810021254210167560034023342270890865364066740258923838535814834888621729035119342167469007031358925618020046478264131907613383718, 71822870055264, 71822870055264, 265750998701117870204043743557483350953351739257964208172433925645167675870571059310822500504287717412, 36842535691553, 291929233335585, 
    22858351047118790312341079409050203005825582498, 71539192498272, 71539192498272, 71539192498272, 71539192498272, 36842502137121, 
    290829688381729, 291929199781153, 290829688185121, 36842267255073, 75371410127349642867478165369235408653623609024435525404206700266401347092714145110882298537827160604074152155683263248183736007635644641036008567900048740483208979730420420934607882311016211835333328380004606369719921187854463817489634758730428064605128310625111347930492857156191142857782455107780201818890256393775507950212249874895031394387050484970965882623727816041214118205477869635480577703080652092046123965816013807479539390366636819572291569688128276903414480429876012763600164915902571291624346357351570972911383132377502296167872461877468847340500281524274374400992681148173197784605723234660192549050871180994599301575409251377586524079902111166474862178650825072459651727735537800596521752147339619582699256895806332931675421508502486696187559591264066501131189984132118936490843963428153323742741370722855846753329959870444613040727759084887776214681639838319166341030402768687771264882351149754992862034717066337123999404156909593608718080468060419504286144340733501549130574872921489347440498451186750451825759750784174578213138319061758075936953572476427092249342624016735415059291860951497813917373000390655994462656033163028872173913139570590266485220048923234216469473450489911820288693871751820107744105524, 71822870055264, 
    71822870055264, 36842267255073, 36842502137121, 290829688381729, 81922479172065, 81922479172065, 
    290829688381729, 290829688381729, 2077188920579703643766219717397407380534037619405772766119846853600807156347919310448346753804274739532972793270167807356565344765926315963108458556058264996729963426549332774, 45638595421473, 290829688381729, 81922479172065, 
    1978899843072482742350788208465535590217910939314355370475667720102535332362005618195296992077932086558921639287796887540371663167411549801826051800136853259443823218291355430, 318317512664353, 318317512631585, 318317512664353, 1984455115761929009283051194308495906516972684524245350247757179599294811383073020542579828672054957207950789811494342135243846093164170883655963609846590428464319887904324390, 1978899843072482742350788208465535590217910939314355370475667720102535332362005618195296992077932086558921639287796887540371663167411549801826051800136853259443823218291355430, 
    283133106988321, 1461529513347648292475291541652165976196921705379, 564092452512033, 564092519657889, 564092586828065, 11441676173819026464746650483538885233451484067, 
    282858229343521, 730775907099514687512514971062706216022359163811, 142120875205921, 282858229343521, 282858229343521, 282858229343521, 
    3887181297622863362303984241384831197859476471368066140163586366524902017664164223400343048011083749639867543292348567406640941256640845152432416208779169913885693521674022, 36842535691553, 36842267255073, 318317512664353, 318317512402209, 36842267255073, 
    318317512664353, 318317512631585, 72603738867808, 72603738867808, 1461529513347648292475291541652165976196921705379, 22925601965970581122164799689713642900864636834, 
    72608038127840, 564092452512033, 566291542913505, 568490633339297, 72643070396640, 213380558751968, 
    72710042945760, 143078384470240, 143078384470240, 143078384470240, 72709573183712, 143078384470240, 
    143078384470240, 143078384470240, 143078384470240, 72844862556256, 72844862556256, 72844862556256, 
    72844862556256, 72638704126048, 72638704126048, 143078384470240, 143078384470240, 39653355292768, 
    39653355292768, 39653355292768, 39653355292768, 145273515149536, 145273246976224, 215579582007520, 
    215579582007520, 145273515411680, 145273515411680, 245307557627514211885146954933307963719983428943077129254285080044323386236951623068924337352457697551555202762598915823893504245810671907182332864868650879741305561244454, 245307557627514211885146954933307963719983428943077129254357227272465918562322785986269631378934996658780976258891696896970799969435842193203298791205505505004154200744742, 44126632943905, 
    79519451449696, 79244363827296, 9080097802336, 9080097736800, 137871290263649813197002402691657551399067633803624007420983356540881497662689549597464117243094596, 249081520045470955577462486712308026749408244218304520642429108172418059973170201220093216616669303935224035100003489731365624775961105447967414253862496707105767713332390, 
    249081520045470955577462486712308026749408244217309466790989295251409800512571787933964589124414276237623633524220571212090531787052159883964607282475684001840738167872678, 11596431741283241455626853187251969298263986595, 11774837702871486440759138933433437666362282403, 290829688152353, 290829688250657, 290829688381729, 
    79450522257504, 79244363827296, 79450522257504, 79519241734240, 79519174625376, 79317449574880, 
    290314292568353, 79386169051616, 79248730098144, 79661055347168, 79317449574880, 79661055347168, 
    290829688643873, 290829688643873, 9079628499040, 9079561390176, 2092399566058740735068295192402456358315855740965094978183680438452173285870948034354084194010993764, 79244363827296, 
    79519241734240, 79519451449696, 79519241734240, 79244363827296, 79450522257504, 9079829825632, 
    9079561390176, 9079829825632, 24266090926142509238219088944453964782698497442, 325534942234976, 9080097998944, 44059957135456, 
    44059957135456, 9079829825632, 44059957135456, 9080098261088]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 36834851718177, 36834985935905, 9080097802336, 9080097802336, 
    732180864850997610578894849654733641819303216546, 5753614230702594312420318140803585265730857379, 283958013200736, 5798215891240839019172621309036185704626923939, 281758989945184, 290555082967392, 
    45639702684961, 45639702684961, 22925253537946277599546221193286166653685990818]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88038308907104, 88003949168736, 88038308907104, 88038308907104, 88244467337312, 2108619733444055736040073945179649982523787674473684621606527587445552260624270576682443703002133508, 
    36834851718177, 36834985935905, 88038308907104, 88038308907104, 88038308907104, 1432828334178097069929407614776357822635967906, 
    2108619733444055736040073945179649982523787674473684621606527587445552787058280127268381394756498436, 88038309103712, 36842368147745, 45639669130529, 45639534912801]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 88038308907104, 88038309103712, 9079628499040, 22858351036505046087704026701463228968681382819, 
    72645146576992, 495270008195552, 290554680707424, 281758587685216, 290554680707424, 354395210910048, 
    81924626655713, 81924626655713, 1984440489929837483293235241291086758375741837860202614833627185401425533326208190765865034442555685500416473033491816736567212240531016896023039557550153891441492212176648998]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 294849918909537079143611153333285870490155819706675548969323165626980068907155268111914444870606875205, 88038308907104, 88072636139616, 88038308907104, 2108619710240942818105126759540034372597267683280560935644183952026953949156605679393023547884514628, 
    2108619710240942818105621363643031080818009042086879280656051476713042161879809224100738728112237892, 3879633372942368893933662488472374990280982834119452482988331851785776201820863331890703335598394804820014736778666464327288578917016497952935506509888895225151265786820902, 2078206925601301951481966219823460129171699391076949008810496939888034363125669094049311381916822852, 2092399558263944989199394209130074898575743497171668906384750099236691785738398286330559558238416196, 88003949168736, 88038308907104, 
    88003915614304, 88038308907104, 88244668663904, 75256901929440, 79517371074912, 81716327221600, 
    72920234199392, 81716327221600, 81716327221600, 81716327221600, 71545634949216, 47099348434805540314425534894308233901624528290, 
    86251682662880, 72645146576992, 75188249561568, 79448844535904, 86251682662880, 81716327221600, 
    88072636172384, 88072636106848, 88072636172384, 88038308874336, 88038308907104, 981230230566952290560025527830757515871604043744272048388963252183562419046457259960424288245957115758348763288178619919250999435054589855218693365722972545842048571954982, 
    88072636106848, 88072636139616, 48526606665797166247944886385720693071601471394, 88072636106848, 88038308972640, 88038309103712, 
    88038309365856, 2108619710240942818105126759540034372597267683280560935644183952026963500173636937647310110550207812, 81716327221600, 81716327221600, 81716327221600, 2108619710240942818105621363643031080818009042086879280656051476713051712896840482355025290777931076, 
    71545634949216, 72645146576992, 72782656834016, 72920234199392, 81716327221600, 75119047739488, 
    75119047739488, 79517094250592, 72851506333792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [123257008228448, 123257008228448, 123257008228448, 123428806920288, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351717142984214254662347383686083590644867514403640469517019407014118370049617879117055983964809807886972864025622581570419213603682712442395599112349605641516208329741783448167392099499040473080079728415519920417388674947597616311532368730176083550323265613926877108787448443396460552997483026703540052458472036787201631336472754167448202837960499327191419378093946161178641950460701706036238144440645692730114056418587382450856814804232882843262651519955831306953229231819553510355256549562158, 88003949168736, 
    88038308907104, 88038308907104, 88003949168736, 88038308907104, 88038308907104, 88038309103712, 
    497400244865504, 79448374773856, 88038309365856, 88244467796064, 72645146576992, 72645146576992, 
    215581796600288, 9079829825632, 266140254622296127312129299213221869627250625909798475537396539540831788541009512089385598645109364772, 81924626655713, 81924626655713, 74844169832544]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [182699551980117837340611440749834229193342723491, 182699551982448538466540463099196666210047500707, 182699551980117837340611440749838662424225916323, 145419543841248, 182699551980117837343087320828405060112153585059, 182699551982448538469016343177767497128858362275, 
    154353084533216, 91522607424831215789295322887996872250614125986, 154078197975520, 145419544037856, 182710702395252398517299516541892379303066740131, 182710702395252398519775396620463210221877601699, 
    182710702397583099645704418969825647238582378915, 91522617634299148217239147694625392063429514658, 91522607445766636584605418961174153757219919266, 91522607445766636584605418961174153757219919266, 91522608126331370426501688774824178982389847458, 91522607445766636584895561157881664759149401506, 
    182733003225355042218518944632370882091092812707, 149817322375648, 149679883422176, 154352614902240, 149817456593376, 149679749204448, 
    149679749204448, 61857131127637483263755009076775401996465851725186789839515489699136229627862977748692393910118788487737424678568120878452245891749452156503334872552486461830498486422847270, 143426220198368, 143426622851552, 143426220198368, 143426622851552, 
    143289114692064, 143426622851552, 182777604885893286925271247800603482529988879267, 154352950446560, 156620359731680, 154352950446560, 
    145281702693344, 145281702693344, 145281971128800, 5280026789543376283667659932019425984407506103603905942303596721776440011921292092560552725314331830863924708895930913205534653805505777613732711935507532796483233667006948613984246313940111459652418517429078326951635450021502118448224767438226572386570312668674072008052527024990600323271998482772785352385089021010705782297417669946364477942006233696035070558451760202054246699, 147412283296224, 147412283296224, 
    145281836911072, 154352950446560, 145281836911072, 145281836911072, 154352950446560, 154215503104480, 
    182866808206969776337537914097783303132881888163, 182866808207136254990932577630710914086997599651, 183045214849122755164547126770713704888466154403, 183045214849122755164619662596591743744591799203, 183045214849289233817941790303641315842581865891, 145419544300000]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [25696044544229575384828505936284314909561849250, 25696044544229575384828496491551278801527244194, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269518246845658697122, 290417514383840, 
    435553049250272, 36567889741920, 72851506333792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [16644916896595362606194719733137530198452223968205265722021357604898191729631200863325446124574727780, 154353084533216, 8340199424715012154549699770557994538954024863845222243612596443653748321047420327311608465526948260, 149679749204448, 149817456593376, 149817456593376, 
    149817188157920, 149817322375648, 16609688693064942194413866485572845602054608574280450093608263118845854563723652457336820354294891844, 143220118391264, 143288980474336, 145281702693344, 
    154352950446560, 154215503104480, 149817188157920, 141021095135712, 141021095135712, 145419141646816, 
    154353084533216, 154215234669024]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [88003949168736, 88038308907104, 88038308907104, 88038309103712, 88038309103712, 9080097867872, 
    9079695607904, 9080098261088, 9080098261088, 149679749204448, 145281702693344, 36361228257376, 
    36361228257376, 36361228257376, 61832602211931006545952620795707570920629961556582665318838464320757278005018180782647807751939661129647415584881517083439809957099473292603705926824644700917782604733726503, 36327371343968, 36327371343968, 182710702405574075087992431570052414887610581923, 
    72645146576992, 72645146576992, 72645146576992, 143082679437792]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [368231298514733347026056182693119085570651866530, 368231298520050259009195846184734313811773244834, 36834985935905, 11440325949328794423484043742211855044299467171, 11440325949332688660983225334358238429414695331, 36833912161313, 
    368231298514816403810605272530975465712095085986, 368231298520050259009505332375142916719127315874, 989336701756513946551633305859901898115939610101432257544833080886329657572483162615939414065826290204338389686058779831571048314798289717672398024251824231730676669569019686, 281552563472736, 281552563472736, 8304780986568768591145375763158153178624701317834816914121106810927450699452556803786760229645133733, 
    290554680707424, 368231298520050259009505332375147279597909329314, 284026334611936, 283751586728288, 284026464635232, 284026464635232, 
    281758989879648, 91522433200238746533710073470342660892449184035, 281758721902944, 281758587685216, 281758453467488, 281758721902944, 
    281758721902944, 281758453467488, 281758721902944, 281758990338400]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [72645146576992]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [36834751054881, 36834784613537, 36834851718177, 36834985935905, 72020230478049, 290555082901856, 
    290555082901856, 72020230478049, 290555083098464, 36834751054881, 36834784613537, 36834851718177, 
    36834751054881, 72020230478049, 45694401242700729209107805293092915451662444963, 72020230478049, 732180864850997610578894849654733641819303216546, 732180864850997610578894849654735330675605931426, 
    283133106988321, 283133140542753, 732180854653160467481549638968011160332096013730, 732180855333725201323445908781661185557265941922, 108305154378977, 290554613598560, 
    73119742564577, 281758721902944, 281758721902944, 281758721902944, 281758721902944, 730842809579781611176861012206308384338944232866, 
    283958013135200, 283751586728288, 284026265405792, 283751586728288, 283751586728288, 283751586728288, 
    283957745158496, 283957610940768, 283957745158496, 283958013593952, 284026464635232, 45761303733508096269236260193017880028296260003, 
    37934262682657, 292822358428000, 292753636854112, 73119742564577, 290554680707424, 290554680707424, 
    290554680707424, 290554814925152, 290554814925152, 290554814925152, 281758989879648, 281483843996000, 
    290348656494944, 281758721902944, 281758587685216, 281758721902944, 281758721902944, 281758990338400, 
    732180859395928952379430107253286397505826227618, 290314564929888, 290555082901856, 290555083098464, 132932252556490215032027325598086552396264520638511020757157739547965310120690464655434109864344677700, 290348656494944, 
    290348656494944, 290554814925152, 290348656494944, 290554814925152, 290554680707424, 290554814925152, 
    290555083360608]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [11429175534213704434447147910865753620647249826, 1038097623321096073894050850658663711185768498961356785832629030709583160251095483018018375990351908, 177064863992288, 11440325949348265611135223702923903730371266466, 291930273522977, 290829554164001, 
    290829688381729, 290829688381729, 290829688185121, 290829688185121, 102784483166724243191840649282227841814600652706, 141983570069984, 
    36567889512544, 177064863992288, 141983570069984, 423595994122720, 141983570069984, 283132872106273, 
    283133106988321, 730775907091549633261815119149685599387806368675, 730775907099525072225074284489359783405341934499, 730775907099525031660255077186018935510839362467, 283132972769569, 290829688381729, 
    290829688381729, 72713870248416, 72645146576992, 72645146576992, 72851305007200, 72645146576992, 
    143082679437792, 290829554426145, 213382706235872, 143082679437792, 11507206662084149730893739539316263617015842722, 11507228440155632670956610125722439897783469986, 
    11507228440155632670956610116499067860928694178, 72645146576992, 72851305007200, 72645146576992, 72851305007200, 732180853993946377667833355031080832218314080675, 
    283751586728288, 283957745158496, 39625906227296, 39625906227296, 22880651856306457963897681911005703819691034018, 39625906227296, 
    39625906227296, 11774838382283606478691962704686952809786509218, 74844169832544]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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
private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44538848649505, 44538949312801, 44538848649505, 282033360478497, 282033461141793, 519044857478258431224927348913358577860456706946898352136632176955061585460679309884105158674298117, 
    266529538259592713261084123339689282262670312031212436050035342328378926152146714291314930460641040420, 266529538259592713261084123339689282262670312031212436093176308139508280139940854537552190859284420644, 267886954284390445574071078493450397308759794386031781446571119598062259318942787106971927180902722405, 84121267315105, 2135991223254437984746673734937780556798411501574317053291269305080394540947142966953732060909988709, 266140254622296127312129299186440290769307979327943446858122296418142644139076025152119188581832038436, 
    91355351197792352758278187256483970604033640354, 141872971417696, 265750970984999482815610430483453287654720476041595239667395950134249470782536131160317453919024420900, 265750970984999482815610430483466287825253209414949977460405333147096644468692756544807131083335374884, 141872971417696, 36319855151200, 
    36560373319776, 36319855151200, 519052773592314808620951952878429528499687685824660793738222441783778821940779783000071940679505956, 11429175534193259687576444552099457472706119586, 571789033906465, 1461507212517389554755246540980438905766912491939, 
    571789033906465, 571892213784865, 35742755856673, 141295972786465, 141295972786465, 563096120992033, 
    563096120992033, 519052773592314808620951953245298884096815844001878235966239972047389959731348967837099172441462820, 1038097623321096073894050824243954207278306299171730693471514646715681313533111146990003211752020004, 571789033906465, 571892213883169, 567425447829921, 
    177061642766560, 177061642766560, 177061642766560, 519052773592314808620073089333369249175410802349572862293192422692837790373524405521134468995323940, 177061642766560, 141979275102432, 
    61832600598648638020570484964173728965800415309145707011219247430918064923509617443035525406669674676445523033360990694982933502699656427947531190752809713633409444409648934, 141979275102432, 35742755856673, 141295972786465, 141295972786465, 563096120992033, 
    563096120992033, 268086696572633456944473943235793159315930706974597350010997670356238355588508488977327167771408150212, 401481222952930212500126771340084097847224634114064840642560768271170241801574665029668293250677550788, 730764778453157326950446389265263201898803537186, 36842267255073, 36842367918369, 
    36842267255073, 290829453500705, 290829554164001, 22836050387010971646546585449079425585419157923, 81922479172065, 267859962938431858908404585158080272904445380002028743049414247542502765231922026912406642013778923877, 
    74225662665185, 2108999877295851319080180399567656152483997117571278656134397249520900453926382772388446893786190181, 81922479172065, 91366501612926913934966263048542120713757656994, 141872971417696, 141872971417696, 
    36319855151200, 36560373319776, 36319855151200, 290829688381729, 11440325949327820864264520344157607582430136226, 1461529524151540669285956585730406476968523498403, 
    1461529524151623826848418907526698991945001239459, 1461529524151623746352605793034131996904347698083, 1461529524154116058352118279920486170193756717987, 36842502137121, 36842502137121, 36842502137121, 
    83021990505953, 291929199781153, 36842267484449, 145694019297697, 73126251864545, 45638595421473, 
    290829688381729, 45638595421473, 81922479172065, 290829688381729, 145694019101089, 36842267287841, 
    145694019101089, 1461529524236694338082845244603254143563006518179, 290829688185121, 1461518373778941403974384608945450520566342648227, 1461864035332094017699241315694576423383941030307, 1461864035332094017699241315694576001169865351587, 
    1461864035332094017699241315694576001169865351587, 81922478909921, 290829688185121, 177061642766560, 177061642766560, 141979275102432, 
    234839179937625725399785637170026631905791442318244139240761352556851894793540841549500167086573721909217168821110234999747824250231339354401499247709445993959818928543200940140226929902426912180625618004737454192103263063350298457329886160329890452218000123494281, 11440325938693956333165386317042978760876885922, 177061642766560, 177061642766560, 141979275102432, 141979275102432, 
    423600289090016, 1461529524151623746352644478660360197203579405219, 36426158835936, 141979275102432, 36842368147745, 488927266614483527188666297671265138138231160342456660308215515478150195860818728940971640348494930510471421205511727851498656121261255892701331139423825376713200670136530577424803526330487453414830152084163308519250188992099775978930420842800017353081897088124938761, 
    1978884747222783456185379191100483388765130552759692159062909161175373963017227322123509295609850297551749768951612288320888437991541760332204659286546943485011581351409725222, 45638595388705, 290829688381729, 36567889741920, 290829688381729, 45638595388705, 
    22858351047138910539610666257579863707628897187, 283132872106273, 283132872106273, 283133106988321, 283133106988321, 36842267484449, 
    142395484414241, 177579889860897, 36842267287841, 142395484217633, 142395484414241, 283133106988321, 
    283133106988321, 1461529513350150899104942563246621978563360883619, 564092452512033, 564092452512033, 1461529513347658677108622692564555205986360525731, 564092452512033, 
    564092519657889, 564092586828065, 141983167815969, 282858229343521, 564195632881953, 45694401224110967890824698060184156271556985763, 
    182710702405574075642589569169902778042418234275, 730775907099525072145846121975095445811797984163, 71752063923617, 142120875205921, 282858229343521, 564332970909985, 
    564332970909985, 282857994461473, 282857994461473, 36567389839649, 142120606769441, 282858229343521, 
    282858229343521, 142120606769441, 36842267255073, 318317512631585, 36842267255073, 24976929922695149516470799243815114423536763171, 
    290829688381729, 290829688381729, 265811792590005360315000283544750211689065523584806084539262089115086989585203733232451731961627343429, 79723590263073, 290829688381729, 290829688381729, 
    44538848878881, 150092065808673, 150092065808673, 290829688381729, 44538848682273, 150092065612065, 
    150092065612065, 290829688185121, 1978643226642049188448275514282335596360334153916591705545571203266111934756485911779450602938525638149413622843903736911000338623614780312303907709066347647824836608274421542, 265807737552056429439041995755217920631544499608146838780830061328379358059949560130303250816518912581, 267827399859917987289356521017186770752455264120739252408581600694254743145051321482077415516658008964, 150092065808673, 
    290829688381729, 150092065808673, 1462934465657105647298634020235175039534737949091, 571789033906465, 571789033906465, 1461507217961907425490261956394432624675203875235, 
    571789033906465, 571789168222497, 571789168222497, 213449211119840, 72707427797216, 571892214276385, 
    72844862556256, 72844862556256, 72638704126048, 72638704126048, 72844862556256, 72638704126048, 
    72638704126048, 72638704126048, 2052371371315403541614559934292352371708363918009079696877117222637762781027665102380355344071577886433240535861246868602575022030417201507659756204906286921336954565718697766, 143078384470240, 495070292216288, 241537395990455532404661607022772314804523262191177869786697130884535018194882324987273827821308005168166669084639520559219005995437555796326056955693086049214837369231142, 
    44263971234081, 213380558751968, 213380558751968, 213380558751968, 213380558751968, 143078384470240, 
    495070292216288, 495070292216288, 72920234199392, 44538848649505, 44538848649505, 44538848649505, 
    44539117314337, 44538982965537, 72920234199392, 72920234199392, 143291127957984, 22880651856306457964047589284486984122350699938, 
    149576703549729, 354397358393696, 494932987480544, 72851506333792, 72851506333792, 8305731417490991822198750988250692466801143723125570014684467186718712480143613388964821325217687653, 
    11507206662063704983404066160907277331625150370, 265815784267942908839380841476552725439264220120388200709031968028485073768323732822143885558332333381, 8305731417490991822198750988250692466801143723125570014684467186718713077082177825095652088836417637, 1461864025804187743912926861876721035868440142243, 11507228440135187924085906766956143749842339746, 22925253537925832852675517834519905690251167138, 
    11507228440135187924085906757732771712987563938, 567494167306657, 564092452512033, 564092452512033, 1461529513347658677108622692564555205986360525731, 564092452512033, 
    566291542913505, 568490633339297, 213449211119840, 72707427797216, 567494167765409, 72844862556256, 
    72844862556256, 72844862556256, 72638704126048, 72638704126048, 72638704126048, 143078384470240, 
    284168070629856, 283961905908064, 143078384470240, 72844862556256, 213380558751968, 213380558751968, 
    213380558751968, 143078384470240, 143078384470240, 424699398457824, 72709640292576, 143078384470240, 
    6559998005155875671795276005997647789902152602174762625604399404117417065935997527971294023111235392136759542020291619114137023820374324012857883704173123032327190092380811577800534872248024462474358933150740587733950518564325381772113812045549899634725638159458207573952838609726233641081931896193930554956572997287475958743066428468826280697071433785127138398307621839915, 11440328570585812451527870566639035493134680995, 354397358393696, 72920234199392, 143291127957984, 91522606786552546612432809996723952924590379427, 
    354397358393696, 354397358393696, 494932987480544, 354397358393696, 143291127957984, 283751586728288, 
    284026464635232, 354397358393696, 283751586728288, 284026464635232, 283957745158496, 732180853993946377509377030002552157031226180003, 
    283751586728288, 283957745158496, 284028681324896, 22925253537946277599698546427630048251549844898, 354397358393696, 72920234199392, 
    72851506333792, 283957745158496, 283957745158496, 39618390034528, 39618390034528, 265751980780621178533169708502942808043426501670120649039660670347236940229473550247493808884040398788, 
    180360177649888, 145171509545184, 180360177649888, 180360177649888, 282362429731406690676345327770024509745648094966542045806405476232422908495307235237568497501207905156, 571789033906465, 
    571789168222497, 571789168222497, 35467878211873, 145206540765408, 145206540765408, 215579582007520, 
    215579582007520, 39724693719264, 39724693719264, 145277809920224, 145277809985760, 281758482833697, 
    74908663548128, 145277340616928, 145277407725792, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277810378976, 145277810378976, 39618390034528, 180360177649888, 145277810116832, 
    145277810116832, 39618390034528, 265752994540108411252271842382692025685938813880171198419623098311608482187255858523174602410685691844, 180360177649888, 180360177649888, 180360177649888, 
    11774838382263161731821259345920656661845378978, 1461529524151623746352605793034131996904347698083, 36567389839649, 145206540765408, 145206679177696, 74837727381600, 
    74837727381600, 74837727381600, 145206436956256, 145277541943520, 215579582007520, 39724693719264, 
    39724693719264, 145277809920224, 145277809985760, 290554575855905, 74908663548128, 145277407725792, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277810378976, 36567490502945, 
    145419544300000, 74837727381600, 74908663548128, 249081520042175852701008967875103546052691429028832122841110366012771736957970197074685083815900635637666742658164775363776965385185003547980719153351579303204077353025318, 44126632943905, 79235773892704, 
    79235773892704, 79235773892704, 79377579116768, 79235773892704, 79235773892704, 79510651799648, 
    79235773892704, 79441932322912, 184758224160992, 219977628518624]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 0, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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


def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_branch (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (q' : State) (hq' : q' ≠ 3) (w : Symbol) (d : Dir)
    (hM10 : M 1 0 = some (some q', Stmt.write w d)) : False := by
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M 1 0 = m.command := by cases d <;> simpa [m, Move.command] using hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
  fin_cases q'
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
    fin_cases w <;> cases d
    · exact tv_b1 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b0 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b2 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    fin_cases w <;> cases d
    · exact tv_b5 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b4 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b7 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
    · exact tv_b6 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · fin_cases w <;> cases d
    · exact tv_b9 M hG hm1 rfl hv (by simp)
    · exact tv_b8 M hG hm1 rfl hv (by simp)
    · exact tv_b11 M hG hm1 rfl hv (by simp)
    · exact tv_b10 M hG hm1 rfl hv (by simp)
  · exact absurd rfl hq'

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2.H1 := by
  intro M hFirst hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 0, false⟩ rfl
  have hv : HistValid M [h1, h0] := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact ⟨by decide, hrun1⟩
    · exact ⟨by decide, rfl⟩
  have hM10 : ∃ q' z, M 1 0 = some (some q', z) := by
    rcases hForm 1 0 with hnone | hsome
    · have h2 : M.multiStep (Machine.init []) 2 = none := by
        rw [Machine.multiStep_succ, hrun1]
        simp [Machine.step, h1, startPos, Position.move, symHead, Position.view, hnone]
      have h107 := Machine.multiStep_eq_none_mono h2 (by decide : 2 ≤ 107)
      obtain ⟨q0, t0, hr⟩ := hRun
      rw [h107] at hr
      contradiction
    · exact hsome
  obtain ⟨q', ⟨w, d⟩, hM10⟩ := hM10
  by_cases h3 : q' = 3
  · subst h3
    have h01_base : UsesOnly01 baseTable := by
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro q a m' hget
      fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
      subst hget; exact Or.inr rfl
    have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
      intro h hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
    have hM10' : (reindex23 M) 1 0 = some (some 2, Stmt.write w d) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    exact solve_branch (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01)
      2 (by decide) w d hM10'
  · exact solve_branch M hG hm0 hv q' h3 w d hM10

end OMA.BB4H1

-- Step BusyBeaver.BB_4.R2.H1: hypothesis H1 of reduction BusyBeaver.BB_4.R2
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2.H1 := OMA.BB4H1.h1_proof
