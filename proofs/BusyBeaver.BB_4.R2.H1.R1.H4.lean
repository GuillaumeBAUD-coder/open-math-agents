import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1

-- Checker and branch certificates from @hyprspacecoyote, PR 4446.
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
  let extra := (val >>> 1) &&& 15
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := (val >>> 5) / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val.testBit 0, ⟨extra, (val >>> 5) % dfaBase⟩, payload >>> width, payload &&& (initialBase - 1)⟩

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
      by_cases hrep : (Nat.beq (cur.step + 1) stop && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01


-- Each three-bit tag selects a recurrence time, a certificate, or traversal to the next missing transition.
-- The soundness theorem below applies to arbitrary tags.
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
      | v :: rest => if checkCertificate tb v then some ((code >>> 3) :: rest) else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some ((code >>> 3) :: certs)
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


-- A subtree starts from a partial transition table and an already verified history.
-- Each group of successor moves is checked by separate kernel computations.
structure SearchNode where
  tb : Table
  used : Bool
  rem : ℕ
  cur : HistItem
  prev : List HistItem

namespace SearchNode

def Valid (n : SearchNode) : Prop :=
  TreeValid n.tb n.used n.rem n.cur n.prev

def result (n : SearchNode) : StepResult := stepLoop n.tb n.rem n.cur n.prev

def branches (n : SearchNode) : Bool :=
  match n.result with
  | .missing .. => true
  | _ => false

def child (n : SearchNode) (m : Move) : SearchNode :=
  match n.result with
  | .missing q a r c p => ⟨n.tb.set q a m, n.used || Nat.beq m.state.val 2, r, c, p⟩
  | _ => n

def atMove (n : SearchNode) (i : ℕ) : SearchNode :=
  n.child ⟨⟨i / 4 % 4, Nat.mod_lt _ (by decide)⟩, ⟨i / 2 % 2, Nat.mod_lt _ (by decide)⟩, i % 2 == 1⟩

theorem check (n : SearchNode) (fuel : ℕ) (certs : List ℕ) (hCount : (holes n.tb).card ≤ fuel)
    (ok : guidedTree fuel n.used n.tb n.rem n.cur n.prev certs = some [0]) : n.Valid :=
  guidedTree_sound hCount ok

theorem split (n : SearchNode) (h : n.branches = true)
    (children : ∀ m ∈ movesAllowed n.used, (n.child m).Valid) : n.Valid := by
  cases hs : n.result with
  | rep => simp [branches, hs] at h
  | done => simp [branches, hs] at h
  | missing q a r c p =>
    unfold Valid
    apply branch_one (q := q) (a := a) (rem' := r) (cur' := c) (prev' := p) hs
    intro m hm
    simpa only [child, hs, Valid] using children m hm

theorem cover12 (n : SearchNode) (branching : n.branches = true) (used : n.used = false)
    (h0 : (n.atMove 0).Valid)
    (h1 : (n.atMove 1).Valid)
    (h2 : (n.atMove 2).Valid)
    (h3 : (n.atMove 3).Valid)
    (h4 : (n.atMove 4).Valid)
    (h5 : (n.atMove 5).Valid)
    (h6 : (n.atMove 6).Valid)
    (h7 : (n.atMove 7).Valid)
    (h8 : (n.atMove 8).Valid)
    (h9 : (n.atMove 9).Valid)
    (h10 : (n.atMove 10).Valid)
    (h11 : (n.atMove 11).Valid)
    : n.Valid := by
  apply n.split branching
  intro m hm
  simp only [movesAllowed, used, moves12, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

theorem cover16 (n : SearchNode) (branching : n.branches = true) (used : n.used = true)
    (h0 : (n.atMove 0).Valid)
    (h1 : (n.atMove 1).Valid)
    (h2 : (n.atMove 2).Valid)
    (h3 : (n.atMove 3).Valid)
    (h4 : (n.atMove 4).Valid)
    (h5 : (n.atMove 5).Valid)
    (h6 : (n.atMove 6).Valid)
    (h7 : (n.atMove 7).Valid)
    (h8 : (n.atMove 8).Valid)
    (h9 : (n.atMove 9).Valid)
    (h10 : (n.atMove 10).Valid)
    (h11 : (n.atMove 11).Valid)
    (h12 : (n.atMove 12).Valid)
    (h13 : (n.atMove 13).Valid)
    (h14 : (n.atMove 14).Valid)
    (h15 : (n.atMove 15).Valid)
    : n.Valid := by
  apply n.split branching
  intro m hm
  simp only [movesAllowed, used, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

end SearchNode

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb3_6 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_0 : (nb3_6.atMove 0).Valid :=
  SearchNode.check _ 4 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_1 : (nb3_6.atMove 1).Valid :=
  SearchNode.check _ 4 [0x6, 0x2108404210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_2 : (nb3_6.atMove 2).Valid :=
  SearchNode.check _ 4 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_3 : (nb3_6.atMove 3).Valid :=
  SearchNode.check _ 4 [0x6, 0x2108404210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_4 : (nb3_6.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_5 : (nb3_6.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_6 : (nb3_6.atMove 6).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_7 : (nb3_6.atMove 7).Valid :=
  SearchNode.check _ 4 [0x3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_8 : (nb3_6.atMove 8).Valid :=
  SearchNode.check _ 4 [0x2492410492482092480032492482082090080410400082692c000924824d26924134964920926924921860c379e6db61249249a49248049208269a41809248001a49248208041049248201041249249241249049049249049249a49249a49248209248208241a4d3402092492492482492493492490492492c924920d24924124904124820926804104924924904924920924920924924924924124924820824900800100004104924820820824120924000100324924824934964d000008289a41801049249249240000201a492480410492492490492492492082092402410402092492492482492090492490492092c924920924d249241041249a692680412492492490492412692492092412492492412492492486492490, 0x2101404220860, 0x2021204220860, 0x2101084220860, 0x501204220860, 0x2014082108021, 0x2014082108021, 0x2014082108021, 0x2014202108021, 0x2014202108021, 0x10004400110080022000804020101002040080da2, 0x441404220860, 0x481404220860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_9 : (nb3_6.atMove 9).Valid :=
  SearchNode.check _ 4 [0x249a0000104120926904024104820004136934120934d04da4d048081e0e36e30d84dbc136934130936de0f36db0d84004126924130db983adb8c36104920100100020924104004104124834c24124824904924924900000d39936aa0104134f349241248041a4d24824904924924900c601879b6e30104030f26944124104134da49341209a6820c000008249249b0924120804124824904024238c36db8c36124806000206c00c201bc3379bc330124904100924904924924124924104d04004800c0410493c924904924124d249240318081e6dc8c24d0183c9e59049e6c0c1e6f3cc249049349249079b03079bcf30820000806124020104124d841340000208049248041249041249049279a49209041048349a68041049369249049249269249209249241249241249a4924830c00d86db6d80000186dc71b0c301b6db6c30186206336dc8c66f36db8d84986186c301b6000006db79e7986186db6d86db0c30db79e6db633cde6f3cc2490, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2024084210860, 0x2024084210860, 0x2024084210860, 0x2024084210860, 0x2024084210860, 0x2102084210860, 0x2101084210860, 0x2024084210860, 0x2101104230860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2024204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2024204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2024204210860, 0x2041204230860, 0x2080a0a122121, 0x2080a0a122121, 0x2082208122121, 0x2082208122121, 0x2082208122121, 0x2021204210860, 0x2021204210860, 0x2024204210860, 0x2041204230860, 0x10004402000840021000804020100802020080da2, 0x2012208122121, 0x10000c0004802000d000300840041040041008123, 0x2012208122121, 0x20422081221a1, 0x2022208122161] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_10 : (nb3_6.atMove 10).Valid :=
  SearchNode.check _ 4 [0x2490416cb659049241049248209a4000d2c9241248001a492480012480c8619040008201209241040209a4b00034964104924924921866180de79b61040209249248049348249a4000924d00124920820804104924820104124924924124904904924904924820824924924820924101b2586012480012492082490003492490492000c924920004920c2410410402092492480002490492490000492c924920d24924134c001a69a08249200069249208000249208248041049249249008209249249209241349249241b6c0012492482492482082496cb6590000490d924000820824d2c82c000120364b0c02496cb659000048249a4b20104924924924000120124924804104924924904924924920820924da4c300209249b4924824920934920904920926924920924d249240001a49289800041249249249008261249248201041249249241a49a4924824924000104d2596402082492492480000403492490082092092492192492492410, 0x2101084220860, 0x300a02108021, 0x300a02108021, 0x300a02108021, 0x2101084220860, 0x2101084220860, 0x2101084220860, 0x2101084220860, 0x2101084220860, 0x4080022000820020800804020102002080080da2, 0x501204220860, 0x501204220860, 0x501204220860, 0x100a04000020200808020010800420204008041a3, 0x100204008020200808020010800420204008041a3, 0x501204220860, 0x501204220860, 0x10000c000220400810020010800420404010081a3, 0x100014000420400810020010800420404010083a3, 0x100404010020400810020010800420404010081a3, 0x1001040040204008100200108004204040100a1a3, 0x10004400102040081002001080042040401008ba3, 0x1080042000804400100804020102002080080da2, 0x1021404220860, 0x8000a00024080102008001200048000c000201a3, 0x421404220860, 0x421404220860, 0x421404220860, 0x304042108021, 0x304082108021, 0x304202108021, 0x304202108021, 0x880022000880402000804020102002080080da2, 0x821404220860, 0x3db307983cc003db30798000001e600798003cc1f53000f303cc1e60f33cc01e7e60079bcc01e6303e4, 0x80404000000810000800040000008100008040402020001000000100008200000020004040200004100000020000800040002004000020004000080020000040040000100018fbc26, 0x404000200c10000800040000010100008000000820180004000100020200000020001040000008100c00040000800040002001000004008000040040000100040000100018a5726, 0x421404220860, 0x8000a00028080202008001200048000c000201a3, 0x421404220860, 0x421404220860, 0x421404220860, 0x421404220860] (by decide) (by decide +kernel)

private def nb3_6_11 : SearchNode := nb3_6.atMove 11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_0 : (nb3_6_11.atMove 0).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_1 : (nb3_6_11.atMove 1).Valid :=
  SearchNode.check _ 3 [0x660479e0000006006f3d23000003633600000030a336dc6c66db79e7b0, 0x2100884210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x504084210860, 0x504084210860, 0x104000000810000004040000004100008000400020081004000104000200000020001040000008100400040000800040002000400010200800040800000100010000100018b5726, 0x504084210860, 0x504084210860, 0x8000400020081000000084000000410000001040002008100400040400020000002000084000000810040004000040004000200008001020080004080000010001000010001895726, 0x77536165ee6b2f73597ba8c4242e5001dd4d85940077536165ee6b2f73594000f047fe5eea310927848ebf047fe5ee6b28001dcd65ee6b639acbdd4d8594001deb396123bae6b36e6b28ee6b2f735a2e6b2bb9acdb9acaef59cb091d9bd664ca000ee6b36e6b28ee6bb5de10808, 0x404000200810000800040000010100008000400020081004000104000200000020001040000008100400040000800040002000400010200800040800000100010000100018b5726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_2 : (nb3_6_11.atMove 2).Valid :=
  SearchNode.check _ 3 [0x20820100804100004006924d30820804d209a60001043249b6c24d3496590, 0x2101044210860, 0x2101044210860, 0x504044210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_3 : (nb3_6_11.atMove 3).Valid :=
  SearchNode.check _ 3 [0x660479e0300006006f3d1e0000336336000000306336dc6c66db79e7b0, 0x2100884210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x504084210860, 0x504084210860, 0x404000000410000002040000004100008040402020001000000100008200000020004040200004100000020000800040002080400020000800080800000040008000100018fbc26, 0x4004000004010000020040000040100008040402020001000000100008200000020004040200004100000020000800040002080400020000800080800000040008000100018fbc26, 0x3040c4318860, 0x504084210860, 0x504084210860, 0x3d77a050000f5de8140003d77a050000430e234000059682fee9d7a0f5b94d4704862f41b92800ee6b2bb9aca3c8967729a8dcd6c75367ae534fe44b3b94daf3597b9acaee6b28ee6b36e6b2f82431729b5e6b287735cf9aca3b9ad8ea6cf5ca6aae6b36e6b28ee6b3ecf58be8, 0x80004000201e100000008400000041000000104000201e100f000400004200000020000840000008100f00040000400040002000080010201e0004080000010001000010001895726, 0x204000000810000002040000002100000800000048000000440000002040000002000800005ce800004080000020100000020080400000801000f04000000404000003000195727, 0x80404000000810000800040000008100008040402020001000000100008200000020004040200004100000020000800040002080400020000800080800000040008000100018fbc26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_4 : (nb3_6_11.atMove 4).Valid :=
  SearchNode.check _ 3 [0x30c00180006000006006f3cf30c30186c3018600018633cdb6c679b596590, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x504084210860, 0x504084210860, 0x504084210860, 0x504084210860, 0x504084210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_5 : (nb3_6_11.atMove 5).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_6 : (nb3_6_11.atMove 6).Valid :=
  SearchNode.check _ 3 [0x660379e0180006006f3cdb00001b633600000018c336db6c66db596590, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x504084210860, 0x10080022004004100100804020100802020080da2, 0x104000000810000004040000004100008000000820180004000100020200000020001040000008100c00040000800040002000400004200c00040800000100010000100018a5726, 0x504084210860, 0x504084210860, 0x806040002000100000018400000041000080480020000c0001000200010200000020004040300002100000020000c0004000208050002000020008080000004000a000100018f9c26, 0x806040002000100000018400000061000080480020000c0001000300010200000020004040300002100000020000c00040003080500020000a0008080000004000a000100018f9c26, 0x404000200c10000800040000010100008000000820180004000100020200000020001040000008100c00040000800040002000400004200c00040800000100010000100018a5726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_7 : (nb3_6_11.atMove 7).Valid :=
  SearchNode.check _ 3 [0x60379e1980006006f3d23000018c036c000001883391c78671b79e718, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x3040c4318860, 0x504084210860, 0x40040000100100000080400000201000080484024000c0001000300010201200060004040300002100c00020000c00040003080500020000a0008080500004000a000100018f9c26, 0x504084210860, 0x504084210860, 0xc000000090000000240000000300000800000408000004040000020040000020000080004ca080004480000020140000020080400000801006004000024004000090004985727, 0x806040002000100000018400000041000080484024000c0001000200010200000060004040300002100000020000c0004000208050002000020008080000004000a000100018f9c26, 0x806040002000100000018400000061000080484024000c0001000300010200000060004040300002100000020000c00040003080500020000a0008080000004000a000100018f9c26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_8 : (nb3_6_11.atMove 8).Valid :=
  SearchNode.check _ 3 [0x20820900804100004826d248208209b6d20924000024b2492482493696590, 0x2101104210860, 0x2101104210860, 0x504104250860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_9 : (nb3_6_11.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_10 : (nb3_6_11.atMove 10).Valid :=
  SearchNode.check _ 3 [0x24036860100004826da48200009b6120924000024924924824d3692490, 0x80004000201e100000008400000041000000100040201e0040000400200200000200000840000008100f00040000400040002000080010201e0004080000010001000010001895726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_11 : (nb3_6_11.atMove 11).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_12 : (nb3_6_11.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249208008001049208200208209a49a6120924124924824924824004006d248208268200240060000002249248463600379e7b0082c006f3cb2090c1e00379e7980824006d2ca303078011e79e610, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x504204210860, 0x301a04318860, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x504204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x500a04210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x504204210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_13 : (nb3_6_11.atMove 13).Valid :=
  SearchNode.check _ 3 [0x269a0000000030926906004800c20104920904100900c30e46de7984800306dbcf3c020180008db0c3080630cdbcf3cc0, 0x2080a0a122121, 0x2080a0a122121, 0x209120c122521, 0x2082208122121, 0x2082208122121, 0x2080a0a122121, 0x2080a0a122121, 0x209120c122521, 0x2082208122121, 0x2020a0a122161, 0x2020a0a122161] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_14 : (nb3_6_11.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249200008001049208200208209a68001248201a69208249248041200369e5904004006dacb200008011269240000001249248463600379e7986b2c006f3cb20920924006d249b090, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x104000000810000004040000004100008000080020180400000102000200002000001040000008100c00040000800040002000400004200c00040800000100010000100018a5726, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x504204210860, 0x1e6f3001e9cc00f3f306bbe6607981e6007a73003d977903cc3cc1e60f3e79c7980f31e61e601e631344, 0x901204230860, 0x501204210860, 0x501204210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_6_11_15 : (nb3_6_11.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24a20000104120926904004000820004136d34900904104db4f2c8000611b79e780000c1b6f3ce00800306dbcf3c0000611b79e7004004136d3caa0001848de79d010, 0x2010a0a122121, 0x201120c122521, 0x2012208122121, 0x100014020002400090022010800420400810083a3, 0x2010a0a122121, 0x201120c122521, 0x2012208122121, 0x2080a0a122121, 0x2080a0a122121, 0x209120c122521, 0x2082208122121, 0x2050a0a1221a1, 0x206120c1225e1, 0x20422081221a1, 0x2020a0a122161, 0x2020a0a122161, 0x202120c122561, 0x2022208122161, 0x2080a0a122121, 0x2080a0a122121] (by decide) (by decide +kernel)

private theorem vb3_6_11 : nb3_6_11.Valid :=
  SearchNode.cover16 nb3_6_11 (by decide) rfl
    vb3_6_11_0 vb3_6_11_1 vb3_6_11_2 vb3_6_11_3 vb3_6_11_4 vb3_6_11_5 vb3_6_11_6 vb3_6_11_7 vb3_6_11_8 vb3_6_11_9 vb3_6_11_10 vb3_6_11_11 vb3_6_11_12 vb3_6_11_13 vb3_6_11_14 vb3_6_11_15

private theorem vb3_6 : nb3_6.Valid :=
  SearchNode.cover12 nb3_6 (by decide) rfl
    vb3_6_0 vb3_6_1 vb3_6_2 vb3_6_3 vb3_6_4 vb3_6_5 vb3_6_6 vb3_6_7 vb3_6_8 vb3_6_9 vb3_6_10 vb3_6_11

private theorem tv_b3_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb3_8 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_0 : (nb3_8.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_1 : (nb3_8.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_2 : (nb3_8.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_3 : (nb3_8.atMove 3).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_4 : (nb3_8.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_5 : (nb3_8.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb3_8_6 : SearchNode := nb3_8.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_0 : (nb3_8_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_1 : (nb3_8_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x30c30db79b6d80c301b6db6db0db6db6db6db61b6db6db6db6c3692492490, 0x20240c6108421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_2 : (nb3_8_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_3 : (nb3_8_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x20830925924d008201241249209249a492492412490492492482c92492490, 0x21020884208e0, 0x20240c6108421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_4 : (nb3_8_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_5 : (nb3_8_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x6, 0x21080884108e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_6 : (nb3_8_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_7 : (nb3_8_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x208309291a6d00004c60d248208219ac92796400033482492484692d936d8, 0x21010884108e0, 0x21010884108e0, 0x9040884408e0, 0x2014082110021, 0x2014082110021, 0x2014082110021, 0x204428a1129e1, 0x9040884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_8 : (nb3_8_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x20830925924d0082092492492092492492492412492492492482492492490, 0x20240c6118421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_9 : (nb3_8_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_10 : (nb3_8_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x480590410082092492492000092412492402092482492483492492490, 0x880022001004400101008040202002080081da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_11 : (nb3_8_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x30d34d211808201241249a0104034da49440209049a4924826d2492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_12 : (nb3_8_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2490080590410492082092492092492412492412492482492482490003c92492490492490, 0x9020884408e0, 0x10004040110004400101008040204002100081da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_13 : (nb3_8_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x269a0c2012c9209249348249248318361c79b12049208369a49bcd049b6d8492492486590, 0x1e60f3079800f4e6003d398007b66001ed98003ccf3f3001e60f307983d398003ea60007987981e6aa964, 0x1e60f3079800f4e6003d398007b66001ed98003ccf3f3001e60f307983d398003ea60007987981e6aa964, 0x1e60f362b800097e0001e61e67980799e600f33cde705fc1e60f307983d3aafc7b660007983cc1e6aacc4, 0x204128a1429e1, 0x20442081421a1, 0x8880884508e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_14 : (nb3_8_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249008000041049208209249209241a41249241a4924824924804134925920c0400092492492410002492492490492412410412492410, 0x9010884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_6_15 : (nb3_8_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a000092492092680402c820831860126930d8000c12692412090418492c9068208309a6db0d04024024924920f3cc0cdb7b6612490492492482180092d930d84c30100000820c60036f66c3610, 0x2011202140021, 0x2014202140021, 0x2014202140021, 0x2011202140021, 0x2014202140021, 0x2014202140021, 0x2020ac6140421, 0x1e60f65a18003ea60016c81e67980799e600f33cde7028b3e60079f983d42fe07b66000799e601e6ae984, 0x2020ac6140421, 0x2021ac6140421, 0x1e60f5e098003ea6000f6cc0079bcc01e6f3003cde79a101e679807983d42fe07b66000799e601ea76cc4, 0x1e60f5e098003ea6000f6cc007a73001e7e6003cde7b8701e6f3007983d42fe07b66000799e601ee42cc4, 0x2011202140021, 0x100104024020100810020010800480102004021a3, 0x100104004020100810020010800480102004021a3, 0x20442081421a1, 0x5b5cc79f9f9801e7e6798007b66001ed98003ccf3f6cc1e60f307983d3f3203eaf7e07987981e6aa964] (by decide) (by decide +kernel)

private theorem vb3_8_6 : nb3_8_6.Valid :=
  SearchNode.cover16 nb3_8_6 (by decide) rfl
    vb3_8_6_0 vb3_8_6_1 vb3_8_6_2 vb3_8_6_3 vb3_8_6_4 vb3_8_6_5 vb3_8_6_6 vb3_8_6_7 vb3_8_6_8 vb3_8_6_9 vb3_8_6_10 vb3_8_6_11 vb3_8_6_12 vb3_8_6_13 vb3_8_6_14 vb3_8_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_7 : (nb3_8.atMove 7).Valid :=
  SearchNode.check _ 4 [0x249a4904120820924924904924824db49241241809201801b8f3cf30920824934d249209249249349248049369261a41009249a49049248269b4d04120820900000006186184000134184186120000920c249209a4824934924820924924804104934936c249241249b6db6d86db6c24930805906126d84924824924108136a2c320000da69249041041b5924b2c80006692492490692cf2492092490, 0x21010884108e0, 0x21010884108e0, 0x9010884408e0, 0x2014082140021, 0x2014082140021, 0x2014082140021, 0x2014082140021, 0x2014082140021, 0x20242084109e0, 0x2014082108021, 0x2014082108021, 0x2034086110421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_8 : (nb3_8.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_9 : (nb3_8.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_10 : (nb3_8.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_11 : (nb3_8.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_12 : (nb3_8.atMove 12).Valid :=
  SearchNode.check _ 4 [0x124a692cb269a61809249269209209249009241809a08209249024a4926920920924900000c36c3cc309261009a6824db09249040209249249201241041249241249249049249001241009a0030104124d24924124904924924906100db4826db09b6de6c36db6c24120924924920986c36db6db6c2049248, 0x8282084409e0, 0x20422084209e0, 0x842000180021, 0x842000180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_13 : (nb3_8.atMove 13).Valid :=
  SearchNode.check _ 4 [0x12494d25966120820924926d249241241201248201241041249204a492cd24924124120926104926d24db0920308238f36e30900020024924920124104124924124924904924904104824d24904124920924924906104134d271b092c124124924920b06d86db6db6c2049248, 0x2014202108021, 0x2014202108021, 0x2021a06110421, 0x1e60f362b800097e0001e622357e088b0000f31e7e705fc1e60f307983d3aafc7b660007983cc1e68c6c4, 0x1024204180421, 0x1084210182121, 0x1084210182121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_14 : (nb3_8.atMove 14).Valid :=
  SearchNode.check _ 4 [0x24924926930d30c049349241208209249249049248269b6920d30c04924900920924904930820920920d360248249241249248249248029249249a4d34c30124924da48249241249040268208249240a69a4926d800049249241208209a69ac82610412492498492482c924924900004924db69b0c24104120804924924920820024924924802924b2c9a4824104124904024b209268249240a4934c249209041049261809a68249a092490080000018080013410412492402482482c1a68249049049249060009a4026980104124d2492402080413cc20824904934924906180924826db0826c208249a48261819b6826db0840000c36c36c204a000092c130d8092082092492033618c32493402482482492480090000492090082092492492092482492492482000692c136d841b618c1a493412490c924924904d360249a4924102db6036f36db6124024004024924124d241a4b2492412492408, 0x20412084109e0, 0x1e60f3079800f4e6003cc0f4e6003d398007a7300f3f3001e60f307983d398003ea60007987981ee24364, 0x20422084209e0, 0x8482084409e0, 0x20412084109e0, 0x4040000010001000020001000040010080002000200008000800010002000020000200400000200010002000010002000100800000102020000100020001004000001010a8f6526, 0x8482084409e0, 0x80402002100404010010400402080022000895a2, 0x1e60f3079800f4e6003cc0f4e6003d398007a7300f3f3001e60f307983d398003ea60007987981ee24364, 0x20222084209e0, 0x20242084109e0, 0x1000000834000008050000010040000020800008002000080008000100020000200002004140002000100020041400020001008030001020ac000100020001020a00001010a8b6526, 0x20412084109e0, 0x8421081810a1, 0x8421081810a1, 0x8421081810a1, 0x8442081821a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_8_15 : (nb3_8.atMove 15).Valid :=
  SearchNode.check _ 4 [0x149249a4924924180924d24024104124924904924824924d241249201040001341641249a4100920820924904824924820524924934930904104924934904924824900805904104924814924924924180d34924d34000124924984924834d35904120c059249249340001240001249351641240049269249a0900104924924820524965934934d20c04920c04965924d04924824d84db6100020936d0498490482cdb6db6e00000926930004238d38d20d36d049b49348024a0000920c249a092c3369261a418092c30092cf249a09249049241009208209249048249248241041249249a01040001041041249049249248249241259249209249241249249209209b6c06db6db6c24b0cdb6d88d86024b0c036f3cdb6c2492412490490080410410492490496492482492480, 0x2011202110021, 0x2011202110021, 0x2011202110021, 0x2014202140021, 0x2014202140021, 0x1014202180021, 0x1014202180021, 0x2011202110021, 0x2011202110021, 0x2011202110021, 0x2014202140021, 0x2014202140021, 0x1014202180021, 0x1014202180021, 0x1024204180421, 0x2011202110021, 0x2011202110021, 0x1004200180021, 0x1004200180021, 0x1001040040088002010100c040201802040081da2, 0x1084210182121, 0x8442081821a1, 0x820020810008400101008040200802020081da2, 0x1e9cc00f4e6001e9cc7980131a600f3798007987983cc79bcc007983cc1e601e63cc1e61e601e6c82a4] (by decide) (by decide +kernel)

private theorem vb3_8 : nb3_8.Valid :=
  SearchNode.cover16 nb3_8 (by decide) rfl
    vb3_8_0 vb3_8_1 vb3_8_2 vb3_8_3 vb3_8_4 vb3_8_5 vb3_8_6 vb3_8_7 vb3_8_8 vb3_8_9 vb3_8_10 vb3_8_11 vb3_8_12 vb3_8_13 vb3_8_14 vb3_8_15

private theorem tv_b3_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_8

private def nb3_9 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_0 : (nb3_9.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_1 : (nb3_9.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_2 : (nb3_9.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_3 : (nb3_9.atMove 3).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_4 : (nb3_9.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_5 : (nb3_9.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_6 : (nb3_9.atMove 6).Valid :=
  SearchNode.check _ 4 [0x249a00041349209268041049248209209a4920900004124104120906104924904824134134924120924db01041249209049201041249209241041049241248349249348349049349249008049249241008001249249248249249248209249248209a6800801134824920124924d208248249248240001849041008249241249241209249b6c061b6db6c24124804104924824904104924904920924924920924124d249240001249249248249249248208209249249000001341041308208249249a4104104d34904c269a492690000090412492010412412492400002492492480412490492490492492492090410492492480410490492490492492492492092492412492412492492482410412492412010412492492412490492490482492492492490492492492092490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_7 : (nb3_9.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_8 : (nb3_9.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_9 : (nb3_9.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_10 : (nb3_9.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_11 : (nb3_9.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_12 : (nb3_9.atMove 12).Valid :=
  SearchNode.check _ 4 [0x124a692cb2c120000924920920000120820924902494130106934920124104124924104924904924900124000120030104124d249241348249a4924824904934924906db0186db79b0924124d249241279b0db6db6db09e6c36db6db6c2049248, 0x2024204210860, 0x2024204210860, 0x2020a04210860, 0xc41048180421, 0x842008180021, 0x842008180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_13 : (nb3_9.atMove 13).Valid :=
  SearchNode.check _ 4 [0x12494d259641300009249241248208249a41249204941341249241201241049269a41049249249269041048249208041249209249209049248249248241241b6186db6db61204971b00061b79e09269241b6c30c36db612492048, 0x1088208142121, 0x1088208142121, 0x1084208182121, 0x1084208182121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_14 : (nb3_9.atMove 14).Valid :=
  SearchNode.check _ 4 [0x249249269209208049349241208209249249049248249209241249209249308241249209249249049248029249249a48248201249248041049248249240a69a49269800049249241208209a69ac82618612492490492482c924924980004920000924924920920804924924920820024924924802924b2c9a48260041249040249249248249240908000001008001341041049240040248241248049049049249040009a6130800104124d24924120c041b4d24804904934924900c30186dc71b0104124d24d34121830186de79b09204a492082492492092482492492482090002082090082092492492092482492492482492092492492092490292482000482082412492482492492482492408, 0x2020a04210860, 0x2021204210860, 0x2024204210860, 0x8421081810a1, 0x8421081810a1, 0x8421081810a1, 0x8442081821a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_9_15 : (nb3_9.atMove 15).Valid :=
  SearchNode.check _ 4 [0x149249a4924124100924d248261841249249049348241040008208241249a4104124d20db6186006db6124924904934820524924934920986104904900820920904936d861b0db6d84814924924924100d34924d36000124924904904834d35904161805924924924000124000d24920824136db49a69208040049249241201b61b6db6000100104924904820524965934924920804920c34924920904906186db6db0c04814000124920824104104924904830834924920904800924924820124820924924824124c00db6db6c30120494d34104124920db6000006db6136d049049348371b1840de79840041249249201b6000824124100104924904824000c24920c34136db08209249859b6000c36dc6120524904900820924904924930924920904966d80c30db6d8480, 0x1008208142121, 0x1088208142121, 0x218208142121, 0x218208142121, 0x8482081421a1, 0x1004208182121, 0x1004208182121, 0x1084208182121, 0x214208182121, 0x214208182121, 0x8442081821a1] (by decide) (by decide +kernel)

private theorem vb3_9 : nb3_9.Valid :=
  SearchNode.cover16 nb3_9 (by decide) rfl
    vb3_9_0 vb3_9_1 vb3_9_2 vb3_9_3 vb3_9_4 vb3_9_5 vb3_9_6 vb3_9_7 vb3_9_8 vb3_9_9 vb3_9_10 vb3_9_11 vb3_9_12 vb3_9_13 vb3_9_14 vb3_9_15

private theorem tv_b3_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_9

private def nb3_10 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_0 : (nb3_10.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_1 : (nb3_10.atMove 1).Valid :=
  SearchNode.check _ 4 [0x24920020124920924824834924800030f30db0d800261241249209249a4904924800030e209a0980c00100920820900030a20b2090482010092082000cc3c82c8241049201009208209248248249248200069249209a09249a4904924820806924120920134104124924120920820924920920924006c36c36c3c124106c368269ac1249241248001e6d86c36c24820186904824824904904924904924800036c30db0d80c30186000030000db6db6f36030de6c00f0cc36f26b26902900034826924900820d04180120000d24924b24020904800800834a26b2690449248, 0x21011084108e0, 0x504044110421, 0x21011886308e0, 0x21021084208e0, 0x1e6102379801e7e60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x1e610237983cc1e60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x1e600f379803cde60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x40800820040009000220010800420008800201a3, 0x100104004020100804020800804040021000825a2, 0x2021850140861, 0x204285a1414a1, 0x2010850140421, 0x2010850140421, 0x1e6102379801e7e60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x2010850140421, 0x204285a1414a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_2 : (nb3_10.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb3_10_3 : SearchNode := nb3_10.atMove 3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_0 : (nb3_10_3.atMove 0).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_1 : (nb3_10_3.atMove 1).Valid :=
  SearchNode.check _ 3 [0x34c2c9269808219358209a0000d369a4924020824c3692483cd2c92490, 0x21011886308e0, 0x21021084208e0, 0x1e60008118007b66000f3f33cc0f307981e601e607a7300799e600f3079803cc1f5300079bcc01f6343c4, 0x1e60079f9803cde600799e63cc0f307981e601e60f3f300799e600f307983cc01f5300079bcc01f634de4, 0x304042108021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_2 : (nb3_10_3.atMove 2).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_3 : (nb3_10_3.atMove 3).Valid :=
  SearchNode.check _ 3 [0x2482c92490082012402092000092492492402082482492482c92c92490, 0x21011886308e0, 0x21021084208e0, 0x304042108021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_4 : (nb3_10_3.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_5 : (nb3_10_3.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_6 : (nb3_10_3.atMove 6).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_7 : (nb3_10_3.atMove 7).Valid :=
  SearchNode.check _ 3 [0x248269a4900004c60d84c20000926926b24000164904b6c826926b2890, 0x21011084108e0, 0x100800820040101004020100804040021000825a2, 0x3041485408e0, 0x9041084408e0, 0x9041084408e0, 0x504044110421, 0x9041084408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_8 : (nb3_10_3.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2080090490410082092492492092412412492412482482492482492492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_9 : (nb3_10_3.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_10 : (nb3_10_3.atMove 10).Valid :=
  SearchNode.check _ 3 [0x2482492490082092492492000092492492402082482492482492492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_11 : (nb3_10_3.atMove 11).Valid :=
  SearchNode.check _ 3 [0x248269a0d00004000db7020000926926b24000164904b5c826926b2490, 0x21011886308e0, 0x3435f307983cc00f3f303cc686a3cc0798f301e61e7a1a87981e60f307a50d40798f3007a73001e705ec4, 0x15d5f3003cfcc00f3f303cc2baa3cc0798f301e61e6aea87981e60f3079d7540798f3007a73001e705ec4, 0x1e6f30079bcc00f3f303cc29c43cc0798f301e61e6a7107981e60f3079c8240798f3007a73001e705ec4, 0x40800820040011000420010800420010800403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_12 : (nb3_10_3.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2490080490410492082092492092412412492412482482492482082cd2c92410492083cd2c92410492490, 0xd011886408e0, 0x9021084408e0, 0xd011886408e0, 0x9021084408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_13 : (nb3_10_3.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249200201a4920924824824924800120da0a20b04830d069049268001b0da09a6b0482098690492682490, 0x2021850140861, 0x204285a1414a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_14 : (nb3_10_3.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249008008041049208209249209241241249241a482482492480402492492000400092492492412082492492410492412410412492410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_3_15 : (nb3_10_3.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a0000124920924804004820800020da09a0980004124124120900104904906800030da09a0980026124020820820904904924800020920b20904820100100820000c3682c82810, 0x2010850140421, 0x2010850140421] (by decide) (by decide +kernel)

private theorem vb3_10_3 : nb3_10_3.Valid :=
  SearchNode.cover16 nb3_10_3 (by decide) rfl
    vb3_10_3_0 vb3_10_3_1 vb3_10_3_2 vb3_10_3_3 vb3_10_3_4 vb3_10_3_5 vb3_10_3_6 vb3_10_3_7 vb3_10_3_8 vb3_10_3_9 vb3_10_3_10 vb3_10_3_11 vb3_10_3_12 vb3_10_3_13 vb3_10_3_14 vb3_10_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_4 : (nb3_10.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_5 : (nb3_10.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb3_10_6 : SearchNode := nb3_10.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_0 : (nb3_10_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_1 : (nb3_10_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x6, 0x10080402010002400101080080400402080082522] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_2 : (nb3_10_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_3 : (nb3_10_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x4c3d9a4d80005801b24820000338da796400032418092483cdad92590, 0x21030886308e0, 0x21030886308e0, 0x21010886308e0, 0x21020884208e0, 0xf3f3005b5cc016d7300f3003db30007a73003ccf307981e7e600f307983cc01f53001e63cc01e704c64, 0x304042108021, 0x304042108021, 0x304042108021, 0x1023000f6cc1faf1300f3001f53001e7e6003cc798079f99e600f3079803cc1f5300079bcc01e740fc4, 0x1023000f6cc001f5300f3001f53001e7e6003cc798079f99e600f3079803cc1f5300079bcc01e740fc4, 0x1080082004002200101020080404002080082522, 0x5040c6108421, 0x304042108021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_4 : (nb3_10_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_5 : (nb3_10_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_6 : (nb3_10_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_7 : (nb3_10_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x4c271a4d800048609248200001349a7964000124d86924834da492498, 0x304082110021, 0x304082110021, 0x9040884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_8 : (nb3_10_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0xd0490490082092492492010413412493402092482492482493492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_9 : (nb3_10_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x208009000041000009009249208201241208201041a4c2c9a683492496590, 0x21030886308e0, 0x21020884308e0, 0x1e60f5e098007b66001e6f3003db3001e6f3003ccf3079879e86a0f3079feb881e63cc1f30d401e741aa4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_10 : (nb3_10_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x4034934900820924924920000104d24924020924824924824d2492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_11 : (nb3_10_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x20800100004000004000926a208200000200000000061ac820824da4d3550, 0x1e7f53000f6cc003db300f3003db3001e6f3003ccf3079879e6840f3079fdc581e63cc1e679801e741aa4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_12 : (nb3_10_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x269000049041049208209249209241041249241a6924824924824930dbcdbd9b000492490, 0xd030886408e0, 0xd010886408e0, 0x9020884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_13 : (nb3_10_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249008000040069200009209209a6d2012c82012480402c8208061b61b6d880048260201200001208361a480c1041001009000009861a012482086590, 0x10080082010002400101080080400402400082522, 0x10080082010002400101080080400402400082522, 0x505284140421, 0x3ccf3f6cc0079bcc01ed98003ea6001ed98003ccf3079879c08c0f3079fdc581e63cc1ee4e401e741aa4, 0x402080090002400101080080400402080082522] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_14 : (nb3_10_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24900c00004104920820924920924d361a49241a6924824924804134d24930004000d34924904130c34d2492410492413410412492410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_6_15 : (nb3_10_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249008000041049208009249209a60200200001249260049248041b6026d268049268049208008240200001040001a01ac820020836026c06004106804924920c30d80db0f361041a012482082593c02d900004c66f00f66000134c0400002080, 0x301202140021, 0x304202140021, 0x100800a2001002080101080080401002400082522, 0x304202140021, 0x301202140021, 0x304202140021, 0x10080082001002080101080080401002400082522, 0x304202140021, 0x505284140421, 0x2804020004400110002010080480002000001a3] (by decide) (by decide +kernel)

private theorem vb3_10_6 : nb3_10_6.Valid :=
  SearchNode.cover16 nb3_10_6 (by decide) rfl
    vb3_10_6_0 vb3_10_6_1 vb3_10_6_2 vb3_10_6_3 vb3_10_6_4 vb3_10_6_5 vb3_10_6_6 vb3_10_6_7 vb3_10_6_8 vb3_10_6_9 vb3_10_6_10 vb3_10_6_11 vb3_10_6_12 vb3_10_6_13 vb3_10_6_14 vb3_10_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_7 : (nb3_10.atMove 7).Valid :=
  SearchNode.check _ 4 [0x249249249208049249041208209a49248249241249a6d04924824904da69249060249241008049249208001249249248049349a49a0000924d261048208269b49041208209000000041061840001241041641200009a08208208208261249248209249269a48201249a61048208249249209249049249241249209248209a6124926824924134da6c209860249269b41249209b6124c00924824806006020820820004d04124d001009a08249a09248249041b6db6d86800034db4d20004108db69369a0000d36d348301b6da69a68200069a69acb00000926924904000237904b2c8000349e4d249049a49acb209208249209209000049349248208209249249240001249249248249249249048209248248240209a410482482492492492490492492412492092492492410, 0x21011886308e0, 0x21011886308e0, 0xd011886408e0, 0x304082140021, 0x304082140021, 0x1008000a0040041001002010080440001000001a3, 0x304082140021, 0x304082140021, 0x1e60008118007b66000f3f30798f307981e66a5007a7300799e600f3079803cc1f5300079bcc01f6343c4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_8 : (nb3_10.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_9 : (nb3_10.atMove 9).Valid :=
  SearchNode.check _ 4 [0x249249261208209249249049248249249249241809269b4d269a0c060049269261809209a4926920c00824120120920c36db6db6c301249248049248049249269200009249249849248249649241208209240001241341641201049209208208249249a49248209249249a4d368249a4004104804820824924124924806186030c30c20824905924d0492482292410410010002000092492490410412482412480002496492490492692cb2049248, 0x21011886308e0, 0x21011886308e0, 0xd011886408e0, 0x10004400104004100502010080400802020082da2, 0x10002400104002200d81020080400402080082522, 0x840100180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_10 : (nb3_10.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_11 : (nb3_10.atMove 11).Valid :=
  SearchNode.check _ 4 [0x249a4936d20000924924934906024d24924d241809269b4d269a0c040049b6d200009269249349060209a49269a0c00004100120920c36db6db6c30104104804820804924926126180924924824104124924984924834964b00124904924924d04820836db6db0d86184924934120820104800935964120824106920820800124824924820924934d868208249249261249209249a4d36824a26004104804020826db69b41249209241249249a49060249249009041049249201249209249240249241248268240009248041208059041049248249224a0824920920d00004d34924820820924924924000124924924824926924900004926924980104920824124000124b04924804104800124904924924920c30db6db6c36030db6d86c36c36db6db6db6d86db6db61b6db0d369a49241041249a490680412482090490492492492492092492482492412492492480, 0x8800220008101004008010200440011000403a3, 0x880022004004100d02010080400802020082da2, 0x480022004002201f81020080400402080082522, 0x1023000f6cc001f5300f3001f53001e7e63ca1a798079f99e600f3079803cc1f5300079bcc01e740fc4, 0x840100180021, 0x840100180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_12 : (nb3_10.atMove 12).Valid :=
  SearchNode.check _ 4 [0x249249249649200009349a49a8800026836f200000048269e4120820db6c302360061249a7904820820d30f20d000049200009209a0c36c3cc360001249840268208029249249a4db68200041248040268208249240b6db4db0d000069acb20820000db6d36d34000124900000000c041008241809a0820d34c30134104124902480000db01b0d800000009a4000006030c36e3c000100026820000020000c001800009b4824820000036f0ce36000026da09b6c00006da63289808209b49249a0000c30db6000020826d2492480000cdac126104000336f06d861000209a41208201341041249240061860300000249249049249000241009a0030104124924924124904934924900000db6c671b0a36de6db636cc20020924d24920830c36d86db6c20dbcc30c3c1861a4820824924826924920924920c2483003400602082492492483cf3cdb6ded9809209269249200001b698ca2613cf3cdb6ded984004336b24924100180db0db6d8409248, 0x20e12086309e0, 0x20822084209e0, 0x1888208c409e0, 0x2a82085509e0, 0x8882084409e0, 0x8882084409e0, 0x1088208c409e0, 0x1088208c409e0, 0x20812084109e0, 0x2f776c80f307980f31e67981e61e601e679807981e77bb07981e60f307a364007b660007a73001ead1ec4, 0x9066601ed98003eae1181e61e601e679807981e7026d3981eda7307a373307b660007a76cc1ead1ec4, 0x20476c803cc7980f31e67981e61e601e679807981e702307981e60f307a364007b660007a73001ead1ec4, 0x1e76c807987980f31e67981e61e601e679807981e702307981e60f307a364007b660007a73001ead1ec4, 0xf316c80f307983cc1e67981e61e601e679807981e77bb07987980f307a364007b660007a73001ead1ec4, 0xf316c83cc07987981e67981e61e601e679807981e77bb0798f300f307a364007b660007a73001ead1ec4, 0x3e2c8003d39800f4e67981e61e601e679807981e702307981e60f307a05d70798f3007983cc1ead1ec4, 0x1088208c409e0, 0x804080110020400802010080404002100086da2, 0x2282085509e0, 0x8282084409e0, 0x8282084409e0, 0x20212084109e0, 0x80000008200000200800000202000100800010040000040100000401000000401000010040000040002000400002000400020001000004004000010200000100040000102108a2726, 0x80000080200000200800002002000108000100040000400100004001000004001000010040000040002000400020000400020001000004004000010200000100040000102108a2726, 0x20612086309e0, 0x20422084209e0, 0x20212084109e0, 0x20612086309e0, 0x20612086309e0, 0x1e60f344580005b20000f32046000204600081181e702307981e60f3079fa7307b660007983cc1ead1ec4, 0x842008180021, 0x842008180021, 0x284202180021, 0x284202180021, 0x84200180021, 0x8100202010200408020800804100024000875a2, 0x204709d04e41e60f30000799e600f33cc01e67981e7023079c08c0f3079f98007b66000fa98001ee9df24, 0x84200180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_13 : (nb3_10.atMove 13).Valid :=
  SearchNode.check _ 4 [0x24924d259641208209249249049248269bcc2c9800061818061e003092083cc20800104920020120920820f308200041249248349248049249249249200009249249049248249069a4120820924000134164120924100920820824924824924820924924920db6826180024904024820824924124924924186d04820804920805904104924824924f34d30000924926836da0b00180124100100020934db79058008249029249249a0db68262060049040048008249a41249249b41b6d04000804920804904104924826926d24180020824904800800836db6db0db6d84db6db6c36c363249b6904000826d66826d3cdb0830c30f3cdb6c04104126926908346d86f36f300001009a49a4104104100100020904924824124824104920904100820100924924104924824904000004034924906d00c04d6513092c101805924920b060601e6db6c2049248, 0x300a02108021, 0x300a02108021, 0x304202108021, 0x300a02108021, 0x300a02108021, 0x304202108021, 0x500a04110421, 0x500a06108421, 0x501204110421, 0x505204140421, 0x500a04110421, 0x500a04110421, 0x501a06108421, 0x8800a2000814022002014080404002100082da2, 0x484204180421, 0x884208182121, 0x884208182121, 0x824208182161, 0x8422081821a1, 0x4004100110004400402010080400802020082da2, 0x4002200110002402501080080400402080082522, 0x1014210180421, 0x1014210180421, 0x24040801004100120020800804100024000825a2, 0x20040801020000820020800804100024000825a2, 0x79800f6cc0079f9800fa980798f3079879807987980025f8000fa980025f83cc1e6001ed980079843465, 0x1024210180861, 0x1084210182121, 0x1084210182121] (by decide) (by decide +kernel)

private def nb3_10_14 : SearchNode := nb3_10.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_0 : (nb3_10_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_1 : (nb3_10_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x4d00004d04004124124024924100004024104004124124924924104104e2692490490410cdac92490490, 0x20e12086309e0, 0x20c22084209e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_2 : (nb3_10_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_3 : (nb3_10_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x4d00000c0400092082092492032010c0209340248248249248000040241040008209a49249201260209241040248249a4924800004da412498413410c12492410000cdac124104336300366db610, 0xf307983cc3cc2d90079f981e61e607987980f301e6798079bcc00f3079bcc001f5300079bcc01f635804, 0xf30798f6cc001e679f980799e607987980f300798079f9bcc00f3079803cc1f5300079bcc01f6343c4, 0x1080080410020401001080080404002080086522, 0xf307983cc3cc0798079f981e61e607987980f301e6798079bcc00f3079bcc001f5300079bcc01f635804, 0x20612086309e0, 0x20422084209e0, 0x8482084409e0, 0x8482084409e0, 0x804020041004040100204008040800220008a5a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_4 : (nb3_10_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_5 : (nb3_10_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_6 : (nb3_10_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x4000000c04c009a08209249201341041a0924124824826924800004d241040008209a4924920104030b261041248249a6924800004d24136d8413610412492410000cdbc1b618590, 0x1e60008118007b66000fa980799e607987980f3007a730079bcc00f3079803cc1f5300079bcc01f6343c4, 0x20212086309e0, 0x20222084209e0, 0x20212086309e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_7 : (nb3_10_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x34db4db4900004d30d34c24104000000020830c3cda49b7980004d20004b2482cb20900004134134104100124d24d2410, 0x1e60008118007b660f9a503d39803d398007a73007a73007980798f3079803cc1f5300079bcc01f6343c4, 0x20612086309e0, 0x20612086309e0, 0x4221081810a1, 0x8221081810a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_8 : (nb3_10_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_9 : (nb3_10_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x249b4924d20804924d2482492413cf249a79000049200049a482c82090080412412490412412492492410, 0x20612086309e0, 0x4421081810a1, 0x8421081810a1, 0x8421081810a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_10 : (nb3_10_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_11 : (nb3_10_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x24924da4d208049249241208209a693c8261041a692480092482c9a49a7980004924d34920824104100004da41249008049249249201800309a61040200249a092480, 0x4421081810a1, 0x8421081810a1, 0x8442081821a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_12 : (nb3_10_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_13 : (nb3_10_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249249249a4d000049249248249241249a4c209041009a0000920b20924920004d0410492492412492410, 0xf30798f6cc001fd499180799e607987980f300798079f9bcc00f3079803cc1f5300079bcc01f6343c4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_14 : (nb3_10_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_14_15 : (nb3_10_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a49249a0d000049349a4120820924926824104124d24800924824824da4d00004924820000c04104930820920920824900020134124d2482692480] (by decide) (by decide +kernel)

private theorem vb3_10_14 : nb3_10_14.Valid :=
  SearchNode.cover16 nb3_10_14 (by decide) rfl
    vb3_10_14_0 vb3_10_14_1 vb3_10_14_2 vb3_10_14_3 vb3_10_14_4 vb3_10_14_5 vb3_10_14_6 vb3_10_14_7 vb3_10_14_8 vb3_10_14_9 vb3_10_14_10 vb3_10_14_11 vb3_10_14_12 vb3_10_14_13 vb3_10_14_14 vb3_10_14_15

private def nb3_10_15 : SearchNode := nb3_10.atMove 15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_0 : (nb3_10_15.atMove 0).Valid :=
  SearchNode.check _ 3 [0x249208049041049208009249209249201249241249240249248249208008001049248201a400412490402082082080802692490492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_1 : (nb3_10_15.atMove 1).Valid :=
  SearchNode.check _ 3 [0x208201340208209a69a4c00924830db6db6db0c00001806dbcf30c36db6c36c3030cdb6c00c0002c336c38f3cf309001841a69269840001009a492410, 0x300a02108021, 0x300a02108021, 0x301202110021, 0x304202140021, 0x304202140021, 0x284202180021, 0x284202180021, 0x300a02108021, 0x300a02108021, 0x300a02108021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_2 : (nb3_10_15.atMove 2).Valid :=
  SearchNode.check _ 3 [0x2492080092492092492412492480410402490400400010082492402480002082082080402692490492080c02c92490490, 0x300a02108021, 0x300a02108021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_3 : (nb3_10_15.atMove 3).Valid :=
  SearchNode.check _ 3 [0x208201240208209a49a4800924820924936920c00820c36b2cf30826924c2483030c9a680080002cb24826f2cb209041041269249040001009a492410, 0x300a02108021, 0x300a02108021, 0x301202110021, 0x304202140021, 0x304202140021, 0x284202180021, 0x284202180021, 0x300a02108021, 0x300a02108021, 0x301a06110421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_4 : (nb3_10_15.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_5 : (nb3_10_15.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_6 : (nb3_10_15.atMove 6).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_7 : (nb3_10_15.atMove 7).Valid :=
  SearchNode.check _ 3 [0x26db6db6180030830c301861b6c36db6db6db0c06db6db6db6c30336336c30c00026830c30f3cdb6c041041a69a6984304d88db6da00001009a69a40001341b69b880, 0x505204140421, 0x500a04110421, 0x500a04110421, 0x44621c1835a1, 0x484204180421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_8 : (nb3_10_15.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24924924920c04926924120820924924c24924124924804924824924934920c04924924da4830124924826800020000826b269a092490, 0x1080042000804022002010080400802020082da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_9 : (nb3_10_15.atMove 9).Valid :=
  SearchNode.check _ 3 [0x24db4926125130924d64934160c20934d24d859348269b6c20980004006946135130920b26820b06004160000100120c3cdb0c3c18012092400413480, 0x814208182121, 0x814208182121, 0x80040002000040002800400020000400028000600020000800080001000200004000040042028040002000400420280400020040000020040000020200000100200000102129faf26, 0x814208182121, 0x814208182121, 0x804208182121, 0x8442081821a1, 0x8442081821a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_10 : (nb3_10_15.atMove 10).Valid :=
  SearchNode.check _ 3 [0x24924924120820924924800924824924934920c049a4924da483032c9a48208000249a48249acb2090410412492490400010092492410, 0x300a02108021, 0x300a02108021, 0x84200180021, 0x84200180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_11 : (nb3_10_15.atMove 11).Valid :=
  SearchNode.check _ 3 [0x249a4d36160000924924d34160000924934d858000269b6c20b00004834db41e0000924936d05800024926820b00004120000100120db6db0c3c00010090400400080, 0x814208182121, 0x814208182121, 0x884208182121, 0x20040901004120104020800804100024000825a2, 0x824208182161, 0x804208182121, 0x8442081821a1, 0x8c42081821a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_12 : (nb3_10_15.atMove 12).Valid :=
  SearchNode.check _ 3 [0x24924924924984924826834c209041009201809a082092490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_13 : (nb3_10_15.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24924934d64d84800026836c209860009201801008209269e6d0482082490, 0x1004210180021, 0x1004210180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_14 : (nb3_10_15.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24924d249a49000049349268241041249a4800924824834c209041049200009a0b2092590000490590493410012412410, 0xf307983cc3cc0798079f981e61e607987985b201e6798079bcc00f3079bcc001f5300079bcc01f635804, 0x804020041004040300204008040800220008a5a2, 0x3cc007d4c0079f9800fa980799e6079879815d50799e6079bcc00f3079803cc1f5300079bcc01f6343c4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_10_15_15 : (nb3_10_15.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24924925925920000924d649048000269bcc209800041059c412082092496490482082482c82c8000049200001209209a0f30b2000012490400482080, 0x404000208810400010040000010002000010002000081044000400080000400080010040000080104000400400000400020080000010200000040800000102000000100108b5726, 0x1014210180421, 0x404000208810400010040000010002000010002000081044000400080000400080010040000080104000400400000400020080000010200000040800000102000000100108b5726, 0x1014210180421, 0x1004210180021, 0x20040801020100804020800804100024000825a2, 0x1024210180861, 0x1004210180021, 0x400080018c004000100020000100020000100020000800c6000400080000400080010040000080104000400400000400020080000004200000040800000102000000100108a5726, 0x1084210182121] (by decide) (by decide +kernel)

private theorem vb3_10_15 : nb3_10_15.Valid :=
  SearchNode.cover16 nb3_10_15 (by decide) rfl
    vb3_10_15_0 vb3_10_15_1 vb3_10_15_2 vb3_10_15_3 vb3_10_15_4 vb3_10_15_5 vb3_10_15_6 vb3_10_15_7 vb3_10_15_8 vb3_10_15_9 vb3_10_15_10 vb3_10_15_11 vb3_10_15_12 vb3_10_15_13 vb3_10_15_14 vb3_10_15_15

private theorem vb3_10 : nb3_10.Valid :=
  SearchNode.cover16 nb3_10 (by decide) rfl
    vb3_10_0 vb3_10_1 vb3_10_2 vb3_10_3 vb3_10_4 vb3_10_5 vb3_10_6 vb3_10_7 vb3_10_8 vb3_10_9 vb3_10_10 vb3_10_11 vb3_10_12 vb3_10_13 vb3_10_14 vb3_10_15

private theorem tv_b3_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_10

private def nb3_11 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_0 : (nb3_11.atMove 0).Valid :=
  SearchNode.check _ 4 [0x249208241249209249249049248208249241249209249249349248241049249241209249a41041249209049201061269a09249249a49248201009209208209249248049248261b08249249201341041049241269208249249209209249249249241249249b6db6db6db6c049249349249049248149141041a69361a0000904d249241041269a4d248000249349249049269269a049248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_1 : (nb3_11.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_2 : (nb3_11.atMove 2).Valid :=
  SearchNode.check _ 4 [0x24920c209249049208208249209a4a348249a41249249849248241049a4d20820000db6c36db6000124904924820c049a49249009249249001049248049300001249a0924820824924820000820920820820826804824820000820900000134104104924104020824820826920820824920920924830824924124820904924824926da4926904924924924920900036db0db6d84904936924934824924124800184e2c824924826924920924986d841849a6c04924944924904924926924920924820820124924900004824d24920820804924824000124934924824d249249048208049249200208249049a68249200209209049249249249209349a4924110004806136980000904d34924000120984d24800024934d24904a249269a04a288, 0x28824814a521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_3 : (nb3_11.atMove 3).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_4 : (nb3_11.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_5 : (nb3_11.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_6 : (nb3_11.atMove 6).Valid :=
  SearchNode.check _ 4 [0x249a4904930000926920124904024184824924100820824924826124920004134104120904104d24904804924824924100924820824104124900104934834920000124904924000d34134020904104820804100065904104d04800d259241208241049249208001041249248209a6900105030824924004124d209801209049348208209249209049041049249048248061b0d86db6c24124900124904024920030904104924004124920924800c24924124900034d34d00024104924920104020d34104104130834934d049248200069a6e30800000924d249040001a0a04c20800024964d249049269ac9a0820924924824000134d64d00020826924926900004d34924100924924a241041a49b6d868000249349241041069269369a0000924d249241a49a69a682492000482492490010482002412400013010492480412000012490492492492090412492490480412080090490492413492492092480002492412492492480, 0x501080240860, 0x21020884208e0, 0x9020884408e0, 0x504084210860, 0x9040884108e0, 0x9040884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_7 : (nb3_11.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_8 : (nb3_11.atMove 8).Valid :=
  SearchNode.check _ 4 [0x24924924120820924924904924824b24924924100924920824924124920924924934924804924926120000924924984924824924924120820926d849241208200001040041041201009201208208249248049248209249249041049249248249241249249b6db6d86db6c008049001041049248149141049a69361a0000924d249041041249a4d248000249349249049269269a049248, 0x1084208182121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_9 : (nb3_11.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_10 : (nb3_11.atMove 10).Valid :=
  SearchNode.check _ 4 [0x249249249208049249281208209a4b648249a4124924984924824db6db6db6c301249269249040249249a4924100924100824d249208001249049248049349a61200009249249848208269249261208209269849b61200000001040041241241249848208200008201209208208248048248209249248248201249249048208249249209269049249241249209248209201049248249241249a6804c000249249201249209248000000040208000049001041041009a01208209248249100049a6936980000924924904000126984d248000249349249049a49269204a082412492090000492492482082080492482400012492492482492492490282090492482402092490482482492492492090492492412492092492492408, 0x10442081821a1, 0x1084208182121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_11 : (nb3_11.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_12 : (nb3_11.atMove 12).Valid :=
  SearchNode.check _ 4 [0x2492492492412082092492490492482482410492410092492082412492092492490492480492692cb2c920000924924984924828dbc23cf3000090400000590412692000012cb209a4924984924820924924824900104924824924124924904920030134d049248149269e69a000092492000000000082010400006410402480c00c8208249209249248048000048208249241249249b6d86d86db6c04900000d04104924814100100100020904924824124820c24006926db0020c00d24904104804004800c00020034924900c36006db6db0104800d24d34121836006db6db0860d801b6db6c2049248, 0x504204210860, 0x504204210860, 0x1e78ae07987980f31e67981e61e601e6798079a04709cf9801e60f307a4570079bcc007a73001ead1ec4, 0x1e76c807987980f31e67981e61e601e6798079a04702379801e60f307a364007b660007a73001ead1ec4, 0x1e601e67980798f300fa981e61e601e6798079a04709cf9801e60f307a4570079bcc007a73001eaf04c4, 0x84208182121, 0x218008108021, 0x218008108021, 0x8004200110020400810040201008002200088da2, 0xc21048180421, 0xc21048180421, 0x822048180421, 0xc41048180421, 0x842008180021, 0x842008180021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_13 : (nb3_11.atMove 13).Valid :=
  SearchNode.check _ 4 [0x14924924b249200009a4934905040824924f349241001040000001a412493cd24904044930004124d20d24830904d34820524924904900800906104934814d35964130000db69b6826184136da6da09861049240208208249a41249204941041349241201a60008249861069a08209269840008269208001208209a49209848208269249a612404018618cdc61204951300041379e0db6186006db41b6d861a09b6d049a40208308249a612492048, 0x1088208142121, 0x1088208142121, 0x4040101100014000500010080402020080807a2, 0x1084208182121, 0x1084208182121, 0x4422081821a1, 0x4422081821a1, 0x8422081821a1] (by decide) (by decide +kernel)

private def nb3_11_14 : SearchNode := nb3_11.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_0 : (nb3_11_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_1 : (nb3_11_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x249200209249049208249249209249049249a41249209249248249208200209209241048208241a482098482482082400492492092490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_2 : (nb3_11_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_3 : (nb3_11_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x249200209249049249049249a412410400492482082000082082400010012492482082400492492092490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_4 : (nb3_11_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_5 : (nb3_11_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_6 : (nb3_11_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x60300349840048208001208201041b00349b4d80106006924820000904c269240001001a4924806db0036e36d808260069269a090cdb0036f36f0490, 0x500a04210860, 0x501204210860, 0x504204210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_7 : (nb3_11_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_8 : (nb3_11_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x34da4900924904935924d04130c04d34934004924134da71001249009200001a09a090590000190410412490406492410, 0x40043000100008000200000000200040080002000200002000800020002000020008600430001000080080000100008000400d0000020040000080500000100400000101208fbf26, 0x40043000100008000200010000200040080002000200002000800020002000020008600430001000080080000100008000400d0000020040000080500000100400000101208fbf26, 0x10080402100404010100080402080022000895a2, 0x8442081821a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_9 : (nb3_11_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x24926924920804924924120820924924824a2412492490492482492492412082092492482618412492498482082080482492492092490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_10 : (nb3_11_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x249b4d31904104924934d35900004924d34c64104124c34db59800009200000209a0924d36d6400010490000010490412410400412410, 0xc211881818e1, 0xc211881818e1, 0x841088180861, 0x841088180861, 0xc811881818e1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_11 : (nb3_11_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x249249249208049249248249a4124924924120820b2c9a48260001a492498482082492410410492492080010012492480, 0x8421081810a1, 0x8421081810a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_12 : (nb3_11_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x24924d359340241041371b0c309b4d008240080269a092402182594412490, 0x40801000100404010100201008040021000845a2, 0x402008090002400401000880040402020482723, 0x8421081810a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_13 : (nb3_11_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249249249248249a4120924004124d2092690] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_14 : (nb3_11_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249249649649000049359258241041359651e490000482000002c92092592592400012490000096490492410402592410, 0x218048108421, 0x218048108421, 0xc211881818e1, 0x8221081810a1, 0x8004200110040401010040201008002200088da2, 0xc211881818e1, 0x8221081810a1, 0x18243081831e1, 0xc411881818e1, 0x8421081810a1, 0xc411881818e1, 0x8421081810a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_14_15 : (nb3_11_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249249349a49200009249a48249a4124d26924904024824004924100924930004125920924d0610496480, 0x1008208142121, 0x1088208142121] (by decide) (by decide +kernel)

private theorem vb3_11_14 : nb3_11_14.Valid :=
  SearchNode.cover16 nb3_11_14 (by decide) rfl
    vb3_11_14_0 vb3_11_14_1 vb3_11_14_2 vb3_11_14_3 vb3_11_14_4 vb3_11_14_5 vb3_11_14_6 vb3_11_14_7 vb3_11_14_8 vb3_11_14_9 vb3_11_14_10 vb3_11_14_11 vb3_11_14_12 vb3_11_14_13 vb3_11_14_14 vb3_11_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb3_11_15 : (nb3_11.atMove 15).Valid :=
  SearchNode.check _ 4 [0x149a49a4934924100924934826004126924904934824924d00130d048009009260001249a4104124d209341000069a4126924904924824924d20936d00524924924d20980104924924824824120024024920804924d040209a69049249248249a4014924924924100924936826004134d24904904834d25980120d05934934d3c0001249269a4d24920804004924924120000800920824100104924904820000124900100524d269209801049249a48248241679a4d34b00004924900020024820904924824924824014800800824000104104924904c20020820920805800934dbc0001349240008009a0824120824926920900494d341041249209b60001069b4136d04904924836da1824926d040041349249200008009208041001049249048200001249001040008369209341269a0c209249059b600000cde61205249001249a69049248249249a4104120024820104924824924824120820da4924904967980000f3798480, 0x28820810a121, 0x1008208142121, 0x1008208142121, 0x1008208142121, 0x21820810a121, 0x1088208142121, 0x1088208142121, 0x8482081421a1, 0x4040101020100804020800804100024000825a2, 0x20040801020100804020800804100024000825a2, 0x1004208182121, 0x1004208182121, 0x1004208182121, 0x1084208182121, 0x1084208182121, 0x8442081821a1] (by decide) (by decide +kernel)

private theorem vb3_11 : nb3_11.Valid :=
  SearchNode.cover16 nb3_11 (by decide) rfl
    vb3_11_0 vb3_11_1 vb3_11_2 vb3_11_3 vb3_11_4 vb3_11_5 vb3_11_6 vb3_11_7 vb3_11_8 vb3_11_9 vb3_11_10 vb3_11_11 vb3_11_12 vb3_11_13 vb3_11_14 vb3_11_15

private theorem tv_b3_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_11

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
private theorem tv_b7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 6) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_0 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_0 : (nb11_0.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_1 : (nb11_0.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_2 : (nb11_0.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_3 : (nb11_0.atMove 3).Valid :=
  SearchNode.check _ 4 [0x24920824124920924924904924820824924124920924924904924824004104924920924904920106924da09249249849248201009209200209249248249248269808241249200001041240041279a08241249209209249248041249049248249241249249b6db6d86db6c0080490590010492481491410002010000000090492592410412082412480002496492490c92692db2049248, 0x2101044210860, 0x2100844210860, 0x2101044210860, 0x2101044210860, 0x504044210860, 0x504044210860, 0x10004400100800820024020100810002100084da2, 0x218002408021] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_4 : (nb11_0.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_5 : (nb11_0.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_0_6 : SearchNode := nb11_0.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_0 : (nb11_0_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_1 : (nb11_0_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x261a480c900820db01248200009b6924124020936c249a482492c92490, 0x2101044210860, 0x28000a000800820020804400100802020080da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_2 : (nb11_0_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_3 : (nb11_0_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x20800900920000004824820920820904120924000124824824824924924d0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_4 : (nb11_0_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2080490092410082492092492092492412492412492482492482492492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_5 : (nb11_0_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_6 : (nb11_0_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x2412480490082492092492000092492412402092482492482492492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_7 : (nb11_0_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x20124806980006824000da0000b3492602000032496484c824926928b0, 0x2101842310860, 0x1358130007d4c001f5304d5c80f31e6010230004bf09ab9f3003cfcc00f30f307983cc07987981e6314c4, 0x3db3000f6cc001f5303e2c80f31e6010230004bf099c6f3003cfcc00f30f307983cc07987981e6314c4, 0x1358130007d4c001f5304d5c80f31e6010230004bf09ab9f3003cfcc00f30f307983cc07987981e6314c4, 0x1e6f30079bcc00f3f307b0ae11160000f307985b288d31f079bea6000f30f307983cc07987981e6314c4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_8 : (nb11_0_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_9 : (nb11_0_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2080690092010082492012492092492412492412492482492482493492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_10 : (nb11_0_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_11 : (nb11_0_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x2412480c90082092012482000092492412402092482492482492c92490, 0x2101044210860, 0x28000a000800820020804400100802020080da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_12 : (nb11_0_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2490410080410492492082092092492412412412492482482482492082412c92490490002493492490490, 0x504044210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_13 : (nb11_0_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249249200209a0924924824824824006db6c3cc36100120b209a0984820926904924820826d349a69009249249249209249249a492480, 0x202418c4718e1, 0x20441084410a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_14 : (nb11_0_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249041008000049249208209209249241241241a4924824824824124924104124104020824924d0400092492492410002412492490490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_6_15 : (nb11_0_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a4920000120924820804000800020920920b04c30820100000800c36c248341000209a09a0a00004124124120900104904906820820d30926d00820826124820000826c3682c02092490492480, 0x2014042440421, 0x20441084410a1] (by decide) (by decide +kernel)

private theorem vb11_0_6 : nb11_0_6.Valid :=
  SearchNode.cover16 nb11_0_6 (by decide) rfl
    vb11_0_6_0 vb11_0_6_1 vb11_0_6_2 vb11_0_6_3 vb11_0_6_4 vb11_0_6_5 vb11_0_6_6 vb11_0_6_7 vb11_0_6_8 vb11_0_6_9 vb11_0_6_10 vb11_0_6_11 vb11_0_6_12 vb11_0_6_13 vb11_0_6_14 vb11_0_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_7 : (nb11_0.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_8 : (nb11_0.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_9 : (nb11_0.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_10 : (nb11_0.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_11 : (nb11_0.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_12 : (nb11_0.atMove 12).Valid :=
  SearchNode.check _ 4 [0x124924a692418c324120924920924c30000d209269249209249049000041301209201249241041241049249249049019249249209208049248249248201260340019a0104924124124031936c668248049249049249001001b01a4820804936d248248204a6924924124920924924924920924900100920b2082092490248, 0x10080400100800820020804020804002100084da2, 0x10004400100800820020804020804002100084da2, 0x2021050840960, 0x799e601e679803ccfa9800097e0000f30f305b20f307980799e601e61e6003cfcc007a73001e9fd164, 0x1024060840960, 0x4280044210a1, 0x4280044210a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_13 : (nb11_0.atMove 13).Valid :=
  SearchNode.check _ 4 [0x124924900041341241001249241049241049249249049048049249249048241049249249241049249249249001049b41241201249249241241204a492492010492492012092c90248, 0x1e60f3445800097e00025f800111600016c80003cc88ce60222c0003cc8127307b660007983cc1e612ec4] (by decide) (by decide +kernel)

private def nb11_0_14 : SearchNode := nb11_0.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_0 : (nb11_0_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_1 : (nb11_0_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_2 : (nb11_0_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_3 : (nb11_0_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920c309a6d04924924c249a43249248009248041241208049041009248241241249208209249008209a000082092492482492412490, 0x218050400421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_4 : (nb11_0_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_5 : (nb11_0_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x2291492c8041208209041009209208204a248, 0x4281044110a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_6 : (nb11_0_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x40040000041009a492082492002013412400002492482482480cda410002c1040001b6186db6100004c04d2000082492092092010c90432096402492482492480400600002410410092412412410, 0x10004400100800820020804201008002200088da2, 0x10004400100800820020804021008002200088da2, 0x2021050840960, 0x224860940960, 0x1024060840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_7 : (nb11_0_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x268000249268049008241249209a018082c9a01241249049a482080412092490080092492092082012482492482c80002482c800000824b20920522f3010482492408, 0x228002408021, 0x10004402100800820020804021008002200088da2, 0x1eabf1e607982046000fa984366e60079f983ea603ccf3003ccf301e679faf0b66e6003cc03cde60f6a45, 0x4281044110a1, 0x8040201100044004040101004040041001029a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_8 : (nb11_0_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_9 : (nb11_0_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2492490092c902914900d249000209008249209209204a492490092490248, 0x1e60f30798002046000811800097e0000f30f303cc88b0002046000408c3cc003db30007b66001edaab64] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_10 : (nb11_0_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_11 : (nb11_0_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x26924900028b0492492082492092492482482482c924900124904124924124924120920900020b00824920920920424924824924800800900920102f3492400492408, 0x1084060840960, 0x904800088b000222c799e611160000f307985b216c87980f31e603cc3cc007a730007b66001edaaec4, 0x1084060840960, 0x294860940960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_12 : (nb11_0_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_13 : (nb11_0_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x22914924920c209269049208201008204a492492092490248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_14 : (nb11_0_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_14_15 : (nb11_0_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24924924120806904934920024920924924024924124924904824824920c209a6984800826120920524924904924824920820924d0288] (by decide) (by decide +kernel)

private theorem vb11_0_14 : nb11_0_14.Valid :=
  SearchNode.cover16 nb11_0_14 (by decide) rfl
    vb11_0_14_0 vb11_0_14_1 vb11_0_14_2 vb11_0_14_3 vb11_0_14_4 vb11_0_14_5 vb11_0_14_6 vb11_0_14_7 vb11_0_14_8 vb11_0_14_9 vb11_0_14_10 vb11_0_14_11 vb11_0_14_12 vb11_0_14_13 vb11_0_14_14 vb11_0_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_0_15 : (nb11_0.atMove 15).Valid :=
  SearchNode.check _ 4 [0x149249248241009209249249048248249241041249201041040000241249249049248124904a48a4884904100800102524924904924812414824824100920924924934824824924004924924120104924d241041249249249248124909249248249348249248003249a4800824b3cf30c061bcc240a48a48841249349249025249249049248124140041049249200001641240041001249048248000049059001041049249241209041249249248240019649240241124904a48a48800649349001025124249c0824164d2093492490493482002492496412090492492490482000cb249a0100924e44204d349209049c91a4800946824924924004924100124904904824924920904904904104824924124924920924904b4418412492092048, 0x298250442521, 0x2012048440421, 0x2012048440421, 0x2010850440421, 0x218050440421, 0x2002008440021, 0x20421084410a1, 0x20421084410a1, 0x10004400100800820024020100810002100084da2, 0x3b9aca001ddc4bb2800eea6c2ca0007823ff280077712eca00077712eca0001dcddc359401dcd82cd650861c4680007735b1cd650861c46f7359b7359b735943b9ad8e6b2bb9aca773597b9ad1735a2e6b28003bd664ca0003c11ff94000f224d4a000eea6c2ca000ef5a1236fdda8, 0x1e60f325f8002046000811800097ef300f30f303cc88b1e6222c0003cc25f8003ea60007980f31e616824, 0x1e60f30798002046000811800097e0000f30f303cc88b000222c0003cc25f8003ea60007980f31e616824, 0x1e60f30798002046000811800097e0000f30f303cc88b000222c0003cc25f8003ea60007980f31e616824, 0x1e60f30798002046000811800097e0000f30f303cc88b000222c0003cc25f8003ea60007980f31e616824, 0x20421084410a1] (by decide) (by decide +kernel)

private theorem vb11_0 : nb11_0.Valid :=
  SearchNode.cover16 nb11_0 (by decide) rfl
    vb11_0_0 vb11_0_1 vb11_0_2 vb11_0_3 vb11_0_4 vb11_0_5 vb11_0_6 vb11_0_7 vb11_0_8 vb11_0_9 vb11_0_10 vb11_0_11 vb11_0_12 vb11_0_13 vb11_0_14 vb11_0_15

private theorem tv_b11_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_0

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_2 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_0 : (nb11_2.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_1 : (nb11_2.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_2 : (nb11_2.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_3 : (nb11_2.atMove 3).Valid :=
  SearchNode.check _ 4 [0x249a000496493092690c124924c200059b4164930db6db6c36db610416cd04924c2400400492492092490492400492492092430682db241249671049b4834937180126d00825834104900c30f49b06dc6000136d0480480003c1c1986d84905b00000000124800104d34836d881b0db8d84da6800104d448209a6800105934824924204126d20934804166d04924824b24124908104924c2490c1a0b2cd04924db4124d209249b6c249a413d1bd230048008db71b81b6db0000f36c361b6104100060824004924946d84934834820004a05944940104020800024000136d04a448041000001001059b59c4e21904106934d24c04100820020104924db4926d20924800024024166d349b482000c90692db20000b0692db240001609858040000679e4d2790da349adb2092490, 0x2101044210860, 0x2100844210860, 0x2101044210860, 0x21020446108e0, 0x2101044210860, 0x504044210860, 0x504044210860, 0x10080012004001100040802020100802020080da2, 0x504044210860, 0x1023000408c001023000f300f33cc0445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x1e6f30079bcc00f3f30001e60f30798445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x304044310860, 0x504044210860, 0x504044210860, 0x9040446108e0, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x88b000222c0004bf000f300f33cc0445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x3db3000f6cc001f53000f300f33cc0445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x21020484208e0, 0x2108048408421, 0x21010486308e0, 0x21020484208e0, 0x8800220020014000420900804020020800827a2, 0x1ebc1307983cc001023000f6cda94f300f379809a3f8f303cc0f4e6007980222da942d90000f303cc3a45, 0x10800420020010800440101006030021000837a2, 0x20800820020010800440101004020021000827a2, 0xf3f3001e9cc00f3f301e60007d4c0011160007d4c1e63cc00f33cc0798f3001e6f301e6f3001e704c64, 0x218042408421, 0x218042408421, 0x801020041000140004408010100800210008a7a2, 0x2018050408421, 0x100044001020010800500100804020020800827a2, 0x218050408421, 0x1f53000408c001f53003cc0079f9800f6cc0081183cc0f300f3798081366001e60f31e7e6001e704c64, 0x3db3000408c001f5305c4fc0fa98000f33cc088b0b8a0730f30798007d5b307980f31e7e6001e612d44, 0xee6d04d6503b9b4135940ee6d04d6500ee729b59400ee88f5667955d33ed4aef40a0001dcd651dcd662a05f20000ee6b29dcd660c388ff2abadf0f3b735943b9aca0003f5476a07735cf9aca1dcede55d33fbb6b28077394dbb86b280ee6b639aca0ee7a0eb2800ee6f07dbba748, 0x10800420020010800480102006030022000837a2, 0x200400000401000004004000004010000002000010004000020040000200040000220001000040002040400020000400008000020001004000001004000010040000010040ad2726, 0x20800820020010800480102004020022000827a2, 0x20800820020010800480102004020022000827a2, 0x20800820020010800480102004020022000827a2, 0x994d73003cfcc0079f9f98001116000445800088b0f303cc3cc07983d3b69cc1e60f307b66001ef98184, 0x218042408421, 0x218042408421, 0x218042408421, 0x801020041000140004808020100800220008a7a2, 0x2012050408421, 0x2010850408421, 0x2010850408421, 0x2010850408421, 0x818050408421, 0x218050408421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_4 : (nb11_2.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_5 : (nb11_2.atMove 5).Valid :=
  SearchNode.check _ 4 [0x14920004124d205249001049348100040041041209048048249241001001049048140040049249204a25049241049249205249209049248141049249209209a0926924924824900824124920000144124924094510492436c30e06db6c00db6db0db6d80db6db01b6db04041001049248129a4936d049a48120924a4880824904904d02512412c30c06db61b6030c36f06db6c36db0db6db6d86db6db61b6db09249a4d2409410402410092000090492492410410092492480002492492490492492692049248, 0x100024020080012000404800100000024000805a2] (by decide) (by decide +kernel)

private def nb11_2_6 : SearchNode := nb11_2.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_0 : (nb11_2_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_1 : (nb11_2_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x36f0600cd800071e78019b0000f3618c030000341186c4cc36f3cdbcd8, 0x2101842310860, 0x2101044210860, 0x21030486108e0, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0x480012000801020040804400100802020080da2, 0x2080082000a01020040205400100802020080fa2, 0x3d77a050000165a0bc0003d77a0500007ea8ed400009502f9c1dbe8ef65f3594773595dcd82cd6577536165000ee6c166b2810c388e83b7d255f2940010c388d0003bd664ca3b9acdb9aca01dcd66dcd65ee6b287735cf9acbdcd65ee6b2bb9acaee6b2bb9acaee6b89c80ad28, 0x3db3000408c001f5304d5c80fa98000f33cc088b09ab9f30f3079800798f307980f31e607981e612d44, 0x4004000010010000008040000020100006450000200200000118000001000a000024000322802000010020000c00040000050004000200002000800020000400040001000a9f9c26, 0x28000a000801020040804400100802020080da2, 0x1080042000801020040804400100802020080da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_2 : (nb11_2_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_3 : (nb11_2_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x40048040000048248209200009040260200001249a6824835134924d0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_4 : (nb11_2_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x410090410082492092492010492412413402092482492482493492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_5 : (nb11_2_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x20804d00924100004920920940820800124820104126804826c24d2492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_6 : (nb11_2_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x34104004d0082492092492000093410413402092482492482492492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_7 : (nb11_2_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x20804000920000006834000980820800020826000020184020c255a492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_8 : (nb11_2_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_9 : (nb11_2_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x36e06c08c00c371c11c7230000e381b8236030e495b6dc8c38e36e38d8] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_10 : (nb11_2_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_11 : (nb11_2_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x24b0400cd800051658019a0000b2410c03000034110483c824b3c92c98, 0x2101842310860, 0x2101044210860, 0x21030486108e0, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0x480012000801020040804400100802020080da2, 0x2080082000a01020040205400100802020080fa2, 0x8000400021e0100000080400000401000000804000008010f00040000400040002000100004021e000400040002002000002000080400021e010f0080004000010000100018095727, 0x3db3000408c001f5304d5c80fa98000f33cc088b09ab9f30f3079800798f307980f31e607981e612d44, 0x4004000010010000008040000020100006450000200200000118000001000a000024000322802000010020000c00040000050004000200002000800020000400040001000a9f9c26, 0x28000a000801020040804400100802020080da2, 0x1080042000801020040804400100802020080da2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_12 : (nb11_2_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249041000041049249208209209249241041341a49248248248249061b003cdbcd84900024934d2490490, 0x704042310860, 0x504044210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_13 : (nb11_2_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249040008040049249a00009009a4830124020124820804020024000000c30c06100028b36dac9841040009001008041269a69248000261309a690000492002492080012498492480, 0x4000212220000000100000000800000000000010020000000000000008800000000000200020000000000000800800000000000010020000000000000008800000004000272a0000001010000000000000040000004000000000090000000000000010000001000000001000000002000000004000004000000000090000000000000001000000202000119500000008000000400000000012000000000000002000004000000000200000008000000000800000010000000012000000000000000200000200000020000000100000000800000004000000001000000080000000200000004000000020000000020000000080000004000000001000000100000000020000000080000013487ffd6bfc7d72e, 0x40400000021000000404000000410000400062281000188a0200000040200188a0c450020000400010080000200311400200cc5062281000188a0c45062280800000100108f9f27] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_14 : (nb11_2_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249041008000049249208209209249b61241a41a69248248248241349241041241041b0034924d04820904d2493410002413492490490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_6_15 : (nb11_2_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249041008000049249208209209a680002002012492480482480032483c92c804000000104900134c20804000004126836da68048008069248008209241a4926000024036926d0410492692492000c9a0f36b200040209a492080, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc0010230b64000f6cc0016c800088b0f5dccc3cc03cc00798f307980f31e607981e612d44, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc0010230b64000f6cc0016c800088b0f5dccc3cc03cc00798f307980f31e607981e612d44] (by decide) (by decide +kernel)

private theorem vb11_2_6 : nb11_2_6.Valid :=
  SearchNode.cover16 nb11_2_6 (by decide) rfl
    vb11_2_6_0 vb11_2_6_1 vb11_2_6_2 vb11_2_6_3 vb11_2_6_4 vb11_2_6_5 vb11_2_6_6 vb11_2_6_7 vb11_2_6_8 vb11_2_6_9 vb11_2_6_10 vb11_2_6_11 vb11_2_6_12 vb11_2_6_13 vb11_2_6_14 vb11_2_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_7 : (nb11_2.atMove 7).Valid :=
  SearchNode.check _ 4 [0x149a00049349005249001249248100040041041209048048249241041001049248140040049249204a2504924004924920924104824924124936d0493482492490010490082482410492080012690482482290590400010c124820904924814510524830d05934814924db4124d20408126904a34c00c36db0db0d82404100104924812b36c30d87a38c14124900104924824904120934d049248241249209249248249240a4884104160824002524924984924812410004804924920104124824124000120904a248041249001249049a29145100001b0030dc0000036f08f360000361c0d80d8000cdb0036f619b6dbd1c61041069249248041049209041049249a49289209249240249240a48a251241000c906928b60000904924924000120984c0400002496492490ca249269e049248, 0x2100844210860, 0x2101044210860, 0x504044210860, 0x88b000222c0002d907b2940f31e6016e294079bdb652840994a1e608132947980f31e607981e612d44, 0x180006008004a031209102004008948201229a3, 0x1ecb4307983cc00102307b2940f31e6016c800079bdb6528408c001e608132947980f31e607981e612d44, 0x2101044210860, 0x2101044210860, 0x100104002100080402010100404008080202011a3, 0x100824000840011000404800100804024100805a2, 0x100804000840011000404800100804024100805a2, 0x1000140005000802030101004040080c0202039a3, 0x100024020880012000404800100804024100805a2, 0x1ebc1307983cc001023000f7439a0f379807d4e06bf8f303cc0f4e6007980f7439a1023000799e60f6a45, 0x1088210412121, 0x1088210412121, 0x1088210412121, 0x21b37307983cc007a73086ce36507987983cfdb51b28f303cc0f4e6007980f736501023000799e60f6a45, 0x3db3000408c001f5306bf940fa98000f33cc088b0d7f3730f3079800803f947980f31e7ed981e612d44] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_8 : (nb11_2.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_9 : (nb11_2.atMove 9).Valid :=
  SearchNode.check _ 4 [0x14924d30000da0524930d04834814d34824100930920000926804090004104104020504900104904820820120924802430db0d86036c049248241009205249269248248149249208209a08a4104b24124920134924104124124926904924814926330024da05904925b6db6c30c36c06db6db6d86d86db6db0db0db05129248009248241a4936d048248120924a48849249049049025249249049248124128900048249009201049241241240001269248248041249049249049249249a04a0826920924a00820d30134e20924b369249a4124936d04934826da692690248, 0x20509504214a1, 0x100024000880012000404800100804020100805a2, 0x100024020880012000404800100804020100805a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_10 : (nb11_2.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_11 : (nb11_2.atMove 11).Valid :=
  SearchNode.check _ 4 [0x149a4930004930524920d04024814d34824100920820000824b0c090004104124100504100104924820820120924902504924824100920924924104924124936d24834824924934904902826924820924820824004924920800120924924814510524936c00104814924db4920120530d26924804006c36db6d80c025129208049248240000001249008149240049241201249209040248249249041349049249a49209209249249241240a48a24001249249248124140009b68249a60209470451c6804126e269a69008252469a5120e38924a341100048249009201049241241240001269248248041249049249029249145105041249049248041249049049049249a49249209249241249240a48a2512420824920924900004c65864d20820934924b2400013cd24844825a2c92490248, 0x2101044210860, 0x2101044210860, 0x100800120040011000440021000804020100805a2, 0x20509504214a1, 0x504050210860, 0x504050210860, 0x9040504208e0, 0x1e60079f9800f4e6003cfcc1e60f307981e63cc0f300f33cc03cc0f307987981e61e679803cde61026865, 0x1e60079f9800f4e6003cfcc1e60f307981e63cc0f300f33cc03cde6007987981e61e76c803cde61026865] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_12 : (nb11_2.atMove 12).Valid :=
  SearchNode.check _ 4 [0x249675e8200036d84928a20006930820000004906124920a04026830db0030c06d840000001209009249041849268269c0c00927185902924936db6d80d86d84c36c00c301b61249208040268249249b60249a41240924801e61a0801a00034000000b30006d86820030000d20d04026c001e8120805984000000824900100180020800180004d30920800800024824920000000000920000024924920920007a068201660009249b4824800000030120920134924104124006030db40000049249349049019a49269a09208009248209248200300061818301049241341240319c79b6048c049249049249000001b01a4820800936c2082482090492082082482412492492092000da069241e4134c0002492010400c00082030c0209248248248249249209249208200000249041001bba24900d040b6db08049b4d86924920124920d36924024d241249000049008000000009209a082082012412490612490248, 0x40800108040011000500024008040021000845a2, 0x1f5300798f307b753007987d4c003cc1e607d4c1e60079f9803cde6007983cfcc1e9db3003cc0799327a5, 0x1e6000798f307b660007987d4c003cc1e607d4c1e60079f9803cde6007983cfcc1e60f3003cc0799327a5, 0xf300798f30798f3007987d4c003cc1e607d4c1e60079f9803cde6007983cfcc003db3003cc0799327a5, 0x801000040011000500204008040021000845a2, 0x40801000040011000500204008040021000845a2, 0x40801000040011000500204008040021000845a2, 0x2021848c409e0, 0x2021050840960, 0x40020000040020000400200000400208004000200004000280040002000040002800060002000080008000100020000400040000020040000020200000100200000102018faf26, 0x1024060840960, 0x40801008040011000500204008040021000845a2, 0x40801008040011000500204008040021000845a2, 0x40801008040011000500204008040021000845a2, 0x40801008040011000500204008040021000845a2, 0x40801008080012000500204008040021000845a2, 0x104004108050a0343001040040a18008142a9a3, 0x200408010805020341001040040a08008140a9a3, 0x40201008100014000500804008040021000845a2, 0x1084060840960, 0x1084060840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_13 : (nb11_2.atMove 13).Valid :=
  SearchNode.check _ 4 [0x14494d359b0004c20000860000834136d60d04834814100004160c2053490c104934824921820924902504494924824100920826926904824824924004124920904104000104124920904924814934da41259205104925a4424930d040248129249b68249a41120924a4884904100804102524924904924812412db6c06c301b6036db6c30c36c36db6db6d86d86db6db6db0db09248061b6db6c30c24000c36c36db61240941040241009009049369248040248001c9124946824820924924104100024924924900024304124900924924d249049004a6920024924906920c34164d20924b368249a4124906d04934826db0e361b6f30db6db6c36db61b6f36c06dbcc200241049209009279b6dbc1ecdb090248, 0x218252442521, 0x298252442521, 0x228252442de1, 0x298252442521, 0x16030400d00014000410800400c06020180807a2, 0x402000001008000002010000004020080006402a0000000280000000a00001000cd0502002000008008000010000404020040006682900010000080000008200000020001ffc27, 0x26030800d00014000420800800c06020180807a2, 0x6100084100014000404800080804020080805a2, 0x298252442521, 0x775361650003c11ff940077536165000eee25d94000f047fe5ee92459497735b1cd6503b9ae7cd657aef40a0000ee6b9f359412a0fbb42489a0fd2f7359400079126a5ee6b28000ee6b45cd653c895c45957ea6c2ca0003c89352800ee6b287735a2f599328000ee6b2fe8bea88, 0x1018210442521, 0x1018208442121, 0x1088208442121, 0x4040101100014000404800100000024000805a2, 0x8420605088e0, 0x10482084421a1, 0x8420605088e0] (by decide) (by decide +kernel)

private def nb11_2_14 : SearchNode := nb11_2.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_0 : (nb11_2_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_1 : (nb11_2_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_2 : (nb11_2_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_3 : (nb11_2_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x249318309a4d849a49b6c249a4324924800924824924d00004d04100934004134124800020924d0082082000082092410482493412490, 0x218010400421, 0x1018208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_4 : (nb11_2_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_5 : (nb11_2_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x24900c24924902924904824924104020824820c208041049041049a493412412413cf0002682c8000008249208208a480412092490288, 0x1e60007983cc7b68d9081183cc1e600081183d1b21e679803ccf301e679807d51d08d93cc079a04704c65, 0xf3007983cc798f30081183cc1e600081183d1b21e679803ccf301e679807d51d06003cc079a04704c65, 0x8020200900044021008100204008100201029a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_6 : (nb11_2_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x40040000241009a492082492002092418480002492482682480cda6b0002c18420724a238246100004004900c0082492092092010cd2432016402492482692480400600002410410092413412410, 0x10004400100801020040804201008002200088da2, 0x10004400100801020040804021008002200088da2, 0x2021050840960, 0x224860940960, 0x826060c409e0, 0x1024060840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_7 : (nb11_2_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x34c000249b4906980824124920db0904824da61a61248009a48000041048000008009a492092030090412012402012482492483cc0002682c800000a24b20920934c00020924902f30000dbcf3608, 0x228042408421, 0x228042408421, 0x228042408421, 0x10004402100801020040804021008002200088da2, 0x1ebb21e607983cc1e60fa983d7826000fa98003cc3ccf300799e601e679faf094241e679807983cd15165, 0x8040201100044021008100204008100201029a3, 0x100024020080012000404800110080022000885a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_8 : (nb11_2_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_9 : (nb11_2_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x51240008048021b493402412410ce28b0002c904d00004004924000824920920920d04934124924084d0410012410288, 0x224860940960, 0x836060c409e0, 0x1024060840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_10 : (nb11_2_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_11 : (nb11_2_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x249241808049049249208249209249341240201a492482482483cd24b0002c984db8e38188e36100804004920000824920920920120904120924024924824924834904000024002f36dbc000f3608, 0x294860940960, 0x8c6060c409e0, 0x1084060840960, 0x294860940960, 0x8c6060c409e0, 0x1084060840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_12 : (nb11_2_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_13 : (nb11_2_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x22924924100804d049a4934024124124800020924c00920a200008209249048249240a288] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_14 : (nb11_2_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_14_15 : (nb11_2_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a49a4100804d849369a0024920824934024020124d24804824824800020924d84800826120920924904824924124d24800924822c8] (by decide) (by decide +kernel)

private theorem vb11_2_14 : nb11_2_14.Valid :=
  SearchNode.cover16 nb11_2_14 (by decide) rfl
    vb11_2_14_0 vb11_2_14_1 vb11_2_14_2 vb11_2_14_3 vb11_2_14_4 vb11_2_14_5 vb11_2_14_6 vb11_2_14_7 vb11_2_14_8 vb11_2_14_9 vb11_2_14_10 vb11_2_14_11 vb11_2_14_12 vb11_2_14_13 vb11_2_14_14 vb11_2_14_15

private def nb11_2_15 : SearchNode := nb11_2.atMove 15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_0 : (nb11_2_15.atMove 0).Valid :=
  SearchNode.check _ 3 [0x249249249a002492000000000480412492490482482410082412492092492490492482492182092490490, 0x1218248442521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_1 : (nb11_2_15.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_2 : (nb11_2_15.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_3 : (nb11_2_15.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920024924904924004924920926804824b2412493618494482400400580002180016010480482002d8049a000092492490412492480, 0x1f5307983cc001f53003cc0079f9800f6cc00799f530003ccf301e681918001e60f31ed98001e704c64, 0x28000a0020010810020100804080012000403a3, 0x7a7307983cc007a73003cc0079f9800f6cc0079fa73007980f3079879f98001e6f301ed98001e704c64, 0x3ba2b66baa500077acc99400079126a5ee6b2f73594001deb3265ee6b280007aef40a00004a817c80007aef40a0000fd51da800012a0d673660e06332f7359400079126a5ee6b2f73594001dcd653c895a68bf2ea6c2ca0003c89352800ee6b287735a2f599328000ee6b2fe8bea88, 0xf3f307983cc00f3f30007980798f300f379807a73f3001e60f30f3081918001e60f31ed98001e704c64, 0x298250442521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_4 : (nb11_2_15.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2492002492490492082412cb2092490482492412492498492481491082c9269208004a248, 0x102008440021, 0x1218252442521, 0x1218252442521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_5 : (nb11_2_15.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_6 : (nb11_2_15.atMove 6).Valid :=
  SearchNode.check _ 3 [0x14820820120920104904920120020924800924804124d2492480400093492412412482ca249208008a492082492490282083092492408, 0x9021084410a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_7 : (nb11_2_15.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_8 : (nb11_2_15.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24924120804904924920820b209249349241241249249a482481491410492692082048002492092490248, 0x8d4060c609e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_9 : (nb11_2_15.atMove 9).Valid :=
  SearchNode.check _ 3 [0x20000020930904820000100020904000820c241a0900000904800024d26934980008e36dc0c30c019b6dbc1860001b8e3cdb6c001269a4924800006d389209800009a692492012000ce3cf36f30000db6c36db610, 0x2b413d6ec0d800000ad553f602b3fb0159fd800005684c7f6000002b554fd800000ad553f602b413d592102becaec0000002b3fc853d3002b3fb00acfec059335b0000000acfec0acfec00acfec57d95dc0df880567f60acfec057d95d8000000acfec0567f60159fd82b3fb00159fd859335b81bf1acfec00159fd8567f6002b3fbad098fec00002b3fb0002b3fb15aaa7ec00000159fd83919963022a, 0x90118c4418e1, 0x90118c4418e1, 0x9021084410a1, 0x90118c4418e1, 0x9021084410a1, 0x9021084410a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_10 : (nb11_2_15.atMove 10).Valid :=
  SearchNode.check _ 3 [0x14924920824920924924924824824d04124d249248041049269249200009349249240a49240208049029a690482012408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_11 : (nb11_2_15.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_12 : (nb11_2_15.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2492492092482600098092692493092490490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_13 : (nb11_2_15.atMove 13).Valid :=
  SearchNode.check _ 3 [0x14511257230046db08909250341009004a69a0d209289071c71c00251a052490c10493480, 0x1008208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_14 : (nb11_2_15.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24924965100034f04935934004104124d00060934f0482c82000480092010582492412490, 0x8020200900044021008100204080102001029a3, 0x8004200108001200050040401008002400088da2, 0x8040201100044021008100a04080142001029a3, 0x8040201100044021008100204080102001029a3, 0x80002000880012000500404010080024000885a2, 0x1080860840960, 0x1084060840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_2_15_15 : (nb11_2_15.atMove 15).Valid :=
  SearchNode.check _ 3 [0x144949359b0004920000860004836124d60d0402481490000412492052490c10492482492182092490250, 0x1018208442121, 0x1088208442121, 0x8420604208e0, 0x10482084421a1, 0x8420604208e0] (by decide) (by decide +kernel)

private theorem vb11_2_15 : nb11_2_15.Valid :=
  SearchNode.cover16 nb11_2_15 (by decide) rfl
    vb11_2_15_0 vb11_2_15_1 vb11_2_15_2 vb11_2_15_3 vb11_2_15_4 vb11_2_15_5 vb11_2_15_6 vb11_2_15_7 vb11_2_15_8 vb11_2_15_9 vb11_2_15_10 vb11_2_15_11 vb11_2_15_12 vb11_2_15_13 vb11_2_15_14 vb11_2_15_15

private theorem vb11_2 : nb11_2.Valid :=
  SearchNode.cover16 nb11_2 (by decide) rfl
    vb11_2_0 vb11_2_1 vb11_2_2 vb11_2_3 vb11_2_4 vb11_2_5 vb11_2_6 vb11_2_7 vb11_2_8 vb11_2_9 vb11_2_10 vb11_2_11 vb11_2_12 vb11_2_13 vb11_2_14 vb11_2_15

private theorem tv_b11_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_2

private def nb11_3 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_0 : (nb11_3.atMove 0).Valid :=
  SearchNode.check _ 4 [0x24920024134d20924904904934820004124934120924904924904824924d341849249209049201869249a09249249849348201001a09248201341068269a41a4904824904824000006124124134d80034d24d069a0824134d20db6000db6934120924924804106d24904824924124904924db09269049b6db6d86d86c20800d84d24104936db0c379a4d048100069869249a0104126820824000126d849348041049801201069a4934d2091410c128926b200009049249a41041289a4da48000249349269069ac9249a04a448, 0x2101842310860, 0x2014042440421, 0x204404a440421, 0x280002200200002800800020000400028000400420000000180000001a00000001000140000000250000002400040002100010000008020000010200000100200000102829ea726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_1 : (nb11_3.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_3_2 : SearchNode := nb11_3.atMove 2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_0 : (nb11_3_2.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_1 : (nb11_3_2.atMove 1).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_2 : (nb11_3_2.atMove 2).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_3 : (nb11_3_2.atMove 3).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_4 : (nb11_3_2.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_5 : (nb11_3_2.atMove 5).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_6 : (nb11_3_2.atMove 6).Valid :=
  SearchNode.check _ 3 [0x64c44937980004c349a6d20000905828da6000136f249b68671b6da590, 0x2101842310860, 0x2101842310860, 0x704042310860, 0x4000212220000000100000000800000000000010020000000000000008800000000000200020000000000000800800000000000010020000000000000008800000004000272a0000001010000000000000040000004000000000090000000000000010000001000000001000000002000000004000004000000000090000000000000001000000202000119500000008000000400000000012000000000000002000004000000000200000008000000000800000010000000012000000000000000200000200000020000000100000000800000004000000001000000080000000200000004000000020000000020000000080000004000000001000000100000000020000000080000013487ffd6bfc7d72e, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_7 : (nb11_3_2.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_8 : (nb11_3_2.atMove 8).Valid :=
  SearchNode.check _ 3 [0x419c75b7580006036db0db00019b7466de6000186c36db6c36dc79b6d8, 0x21018c25208e0, 0x2014042408421, 0x202405e439ce1, 0x204405a4294a1, 0x204405a4294a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_9 : (nb11_3_2.atMove 9).Valid :=
  SearchNode.check _ 3 [0x20821920b24b0082096436cf20924b3c9259a412496cd049b482d9a696c90, 0x2100842210860, 0x2100842210860, 0x21018c2318860, 0x21021c27388e0, 0x100024000840011000402800080804020100805a2, 0x1e600f379803cde60079bcc26076cc001f530007988a3ae0222c0003d398c570798f3007983cc1e709b84, 0x2014058420421, 0x2014058420421, 0x100804002040011000440101404010090400413a3, 0x100004000080012000402800080000020100805a2, 0x100014000480012000402800080402020100807a2, 0x100024000880012000402800080804020100805a2, 0x100024020880012000402800080804020100805a2, 0x1e600f379800f4e6003cfcc2da023000204600079889fe20222c0003cfcca71079879807983cc1e690384, 0x2014058420421, 0x2014058420421, 0x20440584214a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_10 : (nb11_3_2.atMove 10).Valid :=
  SearchNode.check _ 3 [0x40261b4d00820904004120000106836db4020824000800834da6da690] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_11 : (nb11_3_2.atMove 11).Valid :=
  SearchNode.check _ 3 [0x20821920924900004064b64d2082093492502800010cd24a348251a69a490, 0x100800120040011000402020080804020100805a2, 0x504042210860, 0x504042210860, 0x10800420080402000402080082010020400817a2, 0x20440584214a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_12 : (nb11_3_2.atMove 12).Valid :=
  SearchNode.check _ 3 [0x24931404936d04924930024da4100930c069a4d00924980026d21836930024da4036d86030db6c00000004900004000000004820820000020904136db0c079b6d86db6180f349a0db6c301a693610, 0x80440002200000002002000020000400028000402220000000280000000a00000002000460020000440000004400000004400040000020020000010200000100200000102029fa726, 0x80444022200000002002000008000400028000402220000000280000000a00000002000460020000440000004400000004400040000020020000010200000100200000102029fa726, 0xc0044020200000040a00040000000400408000600220000000280000000a00000002000460020000440000004400000004400040000020020000010200000100200000102028fa726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_13 : (nb11_3_2.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24920028b249049200041ecd209249388259a41249261049b48241249a412cd30c36db6c37a36186336c071bcc20824c04d0490093cdb6de0f66d84d349bc16c92090, 0x1018050440421, 0x1018050440421, 0x1028050440ce1, 0x218052440421, 0x218052440421, 0x228052440ce1, 0x298052442521, 0x10030400500014000402800080402020180807a2, 0x2b9b9d6b1fffb00159fd8acfeeb9b9d6af77405cfec000acfeeb3fb0000567f60159fd80ad0173fb0000002becaec000000afb2bb0000000360f9c000000afb2bb0000000614f4c0000000f3a22b6b1fffb567f6000acfec567f60002b405e6e75ac7ffec00567f60567f759fd8000ad0019fd815cdcebae256000000164cd6c000002b554fd80000016f9d580002b3fb2b3fb00000159fd8103782cfeb, 0x818058440421, 0x20010800500014000402800080402020100807a2, 0x1018050440421, 0x1018050440421, 0x1018050440421, 0x1018050440421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_14 : (nb11_3_2.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24980026da4d049241008369a41000000000041009a08041b4d20100000800024036c001b6db0c200000000008211b6000db6db61a6c001b6d26834d84020da6906db0006db49a090] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_2_15 : (nb11_3_2.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249200249249049208041b4d209a48048252a61249061849b4824004804c00c2104c00104d0460001001348048269b6d8623cdb8c24924900134d2480, 0x85670020004040080002200100000800108000000220000000280000001200000002f567020004404020000220100040000200400042b3840000202200000110400000040123fbd27, 0x818058440421, 0x818058440421] (by decide) (by decide +kernel)

private theorem vb11_3_2 : nb11_3_2.Valid :=
  SearchNode.cover16 nb11_3_2 (by decide) rfl
    vb11_3_2_0 vb11_3_2_1 vb11_3_2_2 vb11_3_2_3 vb11_3_2_4 vb11_3_2_5 vb11_3_2_6 vb11_3_2_7 vb11_3_2_8 vb11_3_2_9 vb11_3_2_10 vb11_3_2_11 vb11_3_2_12 vb11_3_2_13 vb11_3_2_14 vb11_3_2_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_3 : (nb11_3.atMove 3).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_4 : (nb11_3.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_5 : (nb11_3.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_3_6 : SearchNode := nb11_3.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_0 : (nb11_3_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x64d24d00100824124900120104c24930c24020904820904864d6492710, 0x2100884210860, 0x2100884210860, 0x100104004020010080420100804080012000403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_1 : (nb11_3_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x2080410482010000c104b00120820900024020104000b24d0082513c9e698, 0x2101084210860, 0x2101084210860, 0x100044001001010040421100044100010800403a3, 0x100024000801010040401100044100010040403a3, 0x100104004001010040401100044100010040403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_2 : (nb11_3_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x66024d04000824024900120000c04930184020800824900826d2496690, 0x2100884210860, 0x20800820020012000420100804080012000403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_3 : (nb11_3_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x2080400080010000cf34b3400082093002012400033cf24d0c065934966d0, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x10080022000804020100804020104002100080da2, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_4 : (nb11_3_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_5 : (nb11_3_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_6 : (nb11_3_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_7 : (nb11_3_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_8 : (nb11_3_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_9 : (nb11_3_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_10 : (nb11_3_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x34134d04000004934934020001804db0186000326da498c825924d66d0, 0x21020846108e0, 0x21021846308e0, 0x10080022002004080100810020104002100082da2, 0xd021846408e0, 0x20800820020011000420100804040011000403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_11 : (nb11_3_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x6, 0x2102048480421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_12 : (nb11_3_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x26960da4d000049241a4900020924c349300041a690482090480c3641b4967180820006a24c20007030d269b416492000ac36db6eb000d9871b79c610, 0x504084210860, 0x504084210860, 0x10080022004004100100804020104002100080da2, 0x8800220020014000420100804100014000403a3, 0x504084210860, 0x504084210860, 0x504084240860, 0x504084240860, 0x80102004020010080420100804100014000403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_13 : (nb11_3_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24964f64b218069241b49800009a683cd24c2c124806f24d00020c3c80692ce30db6c36db8c361359341e6966920830f6023cf4ac30db0c06c36d8000c1b6d80c309b6d86db6db6c0, 0xf30079f9801e7e600798f300088b0001f5300088b0079bcc01e6f30079f9800097e0079f980007a79745, 0x1023000408c001023000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x3ca765455e90077b43ced4000059682fee6b2f7359401ded0f3b577359400079126a500002540be400077acc994000eee25d940015239eb1ecc39401dcd82cf41d650773594000ef59939f35940ee6b29dd4f9ec6d187b5a2f599504d6500773772b32650001dcda0d666a928734e9, 0x1023000408c001023000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x77536165001dd4d8594007753616500077acc99400079126a5ee9d7a0f5b94d4704862f41b92800ee6b2bb9aca3c8967729a8dcd6c75367ae534fdcd65ee6b9f35947735a2ee276b94d46e6b45dc4ed729b5e6b287735cf9aca3b9ad8ea6cf5ca6aae6b36e6b28ee6b6b83703e8, 0x1014050480421, 0x1014050480421, 0x1084050482521, 0x1e6f30079bcc00f3f3000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x4004000004010000020040000040100008040402020001000000100008200000020004040200004000400020400000040004080400020000800080800000040008000100028fbc26, 0x2a04080104001100046010100410005400042ba3, 0x40801000040011000440101004100004000403a3, 0x1014050480421, 0x1014050480421, 0x1014050480421, 0x1024050480ce1, 0x1014050480421, 0x10440504814a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_14 : (nb11_3_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24964decb61804924124900020924836da4c241a680082490082482000482cda0d348269200041249bcda09a6b3cc04160024d66906186c36dbcf30020c049369a410, 0x3040c4318860, 0x304084310860, 0x504084210860, 0x504084210860, 0x504084210860, 0x504084210860, 0x1023000f6cc00102301e6003cfccf301e6003cc1f530003cc7981e608118001e60f31ed98001e611c64, 0x9040846108e0, 0x8000a00028001400048010200410000c000403a3, 0x80012000480014000480102004100014000403a3, 0x80002000480014000480102004100004000403a3, 0x1084050482521, 0x1024050480ce1, 0x10440504814a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_6_15 : (nb11_3_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24964d6cb618049241b49000209a6838e27124124906db4984864db75b76bd450134f269a48000349061ec0479e7584000c0480cd20030307b07a36020b3032413a80, 0x88b000222c0002d907b2d194a1e608132943cc3db652840994a1e608132947980f31e607981e612d44, 0xc0002001f0000000440000001500000800000048000000440000002040000002010000403fe1e0400000082001000002000080000200801000f04004000004000008000495727, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x1ecb4307983cc00102307b2d194a1e608118003cc3db6528408c001e608132947980f31e607981e612d44, 0x3db3000f6cc003db3000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x88b000222c0004bf000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x80004000201e100000018400000041000000504000201e100f00040000c200000020000800040008100f00040400000040009000080010201e0004080000010001200010004895726, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x80004000201e100000008400000041000000104000201e100f000400004200000020000800040008100f00040400000040008000080010201e0004080000010001000010004895726, 0x201008840800120004a0102004100114000423a3, 0x814058480421, 0x1e6f3001e9cc00f3f303cc000f6cc00111600092a78f303cc0f33cc079f983cd8ae0f307980003cc3a45, 0x1014050480421, 0x1014050480421, 0x1014050480421, 0x1084050482521, 0x1024050480ce1, 0x10440504814a1] (by decide) (by decide +kernel)

private theorem vb11_3_6 : nb11_3_6.Valid :=
  SearchNode.cover16 nb11_3_6 (by decide) rfl
    vb11_3_6_0 vb11_3_6_1 vb11_3_6_2 vb11_3_6_3 vb11_3_6_4 vb11_3_6_5 vb11_3_6_6 vb11_3_6_7 vb11_3_6_8 vb11_3_6_9 vb11_3_6_10 vb11_3_6_11 vb11_3_6_12 vb11_3_6_13 vb11_3_6_14 vb11_3_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_7 : (nb11_3.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_8 : (nb11_3.atMove 8).Valid :=
  SearchNode.check _ 4 [0x24924124900020924904934904824004924924100924920004124124d209249049349348049269269240009249049a49048269041249000200001241241e4124d34826930004100000005906100100920924c200000301041c6024924804934820924804104924934824924804306da49bcc241249008049041261049b6d86db6d86c34920db4930904900800004d06184814100000920020000924926804104126804124800024934920906926924f209144a41000000000200001341a680010432000402c800004d36da0006db6b26a2048, 0x21009c87388e0, 0x1e61045a5800097e0001e622714b079bcc00f3f31e70452de9cc0079802682967b660007983cc1e616b84, 0x80004222200000002800040002000000020004422200010010000040040000040100040042220020000020200400000200000284440020200000010800000100008000100029fe726, 0x21021084208e0, 0x2014042408421, 0x100204004040011000420100084020010800403a3, 0x800000202000000108000001020000001040006a00100000100400000400400001000400600000200200002004000002002000d4c00020200000010008000100008000101028fe726, 0x80000080200000400800002002000002001000080008001440040004000040000100020040000080140000200400000200200010000010288000040040000100400000101408b5726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_9 : (nb11_3.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_3_10 : SearchNode := nb11_3.atMove 10

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_0 : (nb11_3_10.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_1 : (nb11_3_10.atMove 1).Valid :=
  SearchNode.check _ 3 [0x208249209209008241040001209249269248241249001048048249a492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_2 : (nb11_3_10.atMove 2).Valid :=
  SearchNode.check _ 3 [0x360360040000009a0134000001800da01640001a6980d060269b593590, 0x21009c87388e0, 0x21009c87388e0, 0x4400020889000080004000000110000000100800000904440004400000004020001004000008010444040000040040000088000000420888004000080010200000010000ca5726, 0x4400020cb90000000840000001100000001008000009065c000440020000402000100000200801065c040000040040000080004000420cb8004000080010200000010000ca5726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_3 : (nb11_3_10.atMove 3).Valid :=
  SearchNode.check _ 3 [0x20824920920900004924d3402082092492492400012492490482492492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_4 : (nb11_3_10.atMove 4).Valid :=
  SearchNode.check _ 3 [0x20834d409e11000049a6d34000820936dac9240001a6b34d060669b493590, 0x21011886308e0, 0x21011886308e0, 0xd011886408e0, 0x2010850440421, 0x2010850440421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_5 : (nb11_3_10.atMove 5).Valid :=
  SearchNode.check _ 3 [0x20824920920900004924d3402082092492492400012492490482492492690] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_6 : (nb11_3_10.atMove 6).Valid :=
  SearchNode.check _ 3 [0x34d34104000004934934020001804d80000000326da498c824d25966d0, 0x21011886308e0, 0x21011886308e0, 0x100800a2000814020402010080504002100082da2, 0xd011886408e0, 0x1e6f30079bcc00f3f3003cc00f3f3003cfcc007a730f303cc3cc3cc0798f3000f6ccf300f3000f30ae85] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_7 : (nb11_3_10.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_8 : (nb11_3_10.atMove 8).Valid :=
  SearchNode.check _ 3 [0x471c5541500006924d34020000c34db8d34000124a3c904844d44d2710, 0x9021084408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_9 : (nb11_3_10.atMove 9).Valid :=
  SearchNode.check _ 3 [0x30c36db6db0d80006db6db6030c30db6db6db60001b6dc6d86c2492492698] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_10 : (nb11_3_10.atMove 10).Valid :=
  SearchNode.check _ 3 [0x34134904000004924934020000804d2002000032692490c824d2496690, 0x21021084208e0, 0x100800820020100804020100804040021000825a2, 0x9021084408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_11 : (nb11_3_10.atMove 11).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_12 : (nb11_3_10.atMove 12).Valid :=
  SearchNode.check _ 3 [0x24900034900004924800d240241008008049061000009a0824c20c30126124984006026820930c34c04030820000924000820120824800d24024100c04d04126100100180820c3002003012418610] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_13 : (nb11_3_10.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24924020820804924004000020924800924024124900124804820824904924d200049209249a60209a41a4936c2512402492010090412482492690000cd80926f3090, 0x304042408421, 0x40800820040011000420100804020010800403a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_14 : (nb11_3_10.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249a4120000004924800900004134820824000100000920820d20806028820930c269a41048000200001341341a400000402083c800004d04906900000180a20f301001368249a410, 0x3b9aca0001ebbd0280007aef40a0000fd51da8000218711a0000430e2403e00b64dc500ee6ee1acaee6b2f735b1cd650ee6b283b9ad8e6e3780265bb34135940773770d6500ee729b59401dcda09ae27c01310fa729b594003b9acbdcd73e6b281dcda09ca6d65000eee2675afe2e8, 0x80000004200000040800000102000000101000008008001040040004000040000200010040000080140000400400000400800040000004280800040000800101000000104008a5726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_10_15 : (nb11_3_10.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249241249208049241048000209a48049a40201249001a48048240049208249a6104120904104024c008069acd208309a41a4936824000804d24d2080012410493480, 0x8800220020104004020900804020020800825a2] (by decide) (by decide +kernel)

private theorem vb11_3_10 : nb11_3_10.Valid :=
  SearchNode.cover16 nb11_3_10 (by decide) rfl
    vb11_3_10_0 vb11_3_10_1 vb11_3_10_2 vb11_3_10_3 vb11_3_10_4 vb11_3_10_5 vb11_3_10_6 vb11_3_10_7 vb11_3_10_8 vb11_3_10_9 vb11_3_10_10 vb11_3_10_11 vb11_3_10_12 vb11_3_10_13 vb11_3_10_14 vb11_3_10_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_11 : (nb11_3.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_3_12 : SearchNode := nb11_3.atMove 12

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_0 : (nb11_3_12.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_1 : (nb11_3_12.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_2 : (nb11_3_12.atMove 2).Valid :=
  SearchNode.check _ 3 [0x269b0c36db6d06db0c36036db09a7936c26d641b6db6c00db6c081b603d9b6d86826c06004d30c3003036600602083018010003593524924904924810, 0x44000000110000000440000000500008000600020000100080000400200001000400040020200000022000400002000000280400020200000010800000100008000100029fe726, 0x44020000050000000400100000400408000600020000100080000400200001000400040020200000022000400002000000280400020000800010800000100008000100029fa726, 0x799e601e679803ccfa983cc1e601e67980798798f300f33cc03cc0025f8003ea60007987981e616824, 0x20fd33000f6cc010323000f300f33cc00f33cc099d173303d3a75046079879bcd6cfa733cfcc003cc3a45, 0x88b000222c0004bf000f560ecbcde60079f98f30983c1307983cc002321d979bcc007980f31e616b84, 0x1018042440421, 0x104804a440421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_3 : (nb11_3_12.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920926006824da0934126036b24180926db6006e36db090, 0xc00000203000000208000001002000002080506000000418000005040000004010004000700010001c0002000100002000100080000020200000080800000102000000102818fbd26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_4 : (nb11_3_12.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_5 : (nb11_3_12.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_6 : (nb11_3_12.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24964934930004aa4824d26824106d80180db01849a4820000f20b240260268001b6d86db6d86c649200249240209249049a4904820104c04824d201b6006036c0600012002483480, 0x1ebc1307983cc001023000f300f30f300f379809a3f8f303cc0f4e60079f983cd8ae0f307980003cc3a45, 0x3d398007a73001e9ccb645b20798f301e60798f30f4e9cc003cfcc00fa98007b66001ed98001e631464, 0x3db3000f6cc001f53007983cc1e62d903cc7983cc0f30f303cc3cc102379801e7e6007a01181e816e04, 0x35280f379800f33cc079bcc000f6cc0011160009a4af3303cc0f4e61ed9f983cdc7a0f316c80003cc3a45] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_7 : (nb11_3_12.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_8 : (nb11_3_12.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249209200009a4c30936db0db6db0d869260369a4180920180000c30c3090] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_9 : (nb11_3_12.atMove 9).Valid :=
  SearchNode.check _ 3 [0x24920120000924c30920d200309240009261b0008f36e3090, 0x87804a410421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_10 : (nb11_3_12.atMove 10).Valid :=
  SearchNode.check _ 3 [0x208008049001048249240209a4130c36030036d84106804004d20824020026806000120184804830db6030036d80924920024da0924924804934826c30f00c00c3610, 0x20800820020100808040101004020020800825a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_11 : (nb11_3_12.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_12 : (nb11_3_12.atMove 12).Valid :=
  SearchNode.check _ 3 [0x24920926006824da0924926036b241809269260069a6db090, 0x400000201000000202000001002000002080506000000418000005040000004010004000700010001c0002000100002000100080000020200000080800000102000000102818fbd26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_13 : (nb11_3_12.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24920924004924d2092692403492410092693c000926f3090, 0x1018042408421, 0x80600002001000002806000020008000028000640020000100080000400200001000400040300200000402000400002000004080600020000800010800000100008000100028fa726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_14 : (nb11_3_12.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249349619b092000482000482cc20924824c248241249ac034b200009a68061acb3c8349008349279069a0006aaceb0d24824c249a410, 0x218042408421, 0x218042408421, 0x218042408421, 0x218042408421, 0x301810070000c0004200800c400401810060323, 0x85674030004010080002000100040000400040000200100000200200001000200002850702000040002000002010000400020080004003a00000002800000012000000040003fbd27, 0xf3001e7e6003d39800fe645b20798f301e60798f316c83cc0f303cc3cc798007b66001ed98001edc9464, 0x801020041004040080408010100800210008a5a2, 0x842042480421, 0x842042480421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_12_15 : (nb11_3_12.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24924104004000020924904934904824e20038b24000924d30004324d2092490490493480, 0x80112000900014000422100884004010100403a3, 0x600000201800000206000001008000002080506000000418000005040000004010004000700010001c0002000100002000400080000020200000080800000102000000102018fbd26] (by decide) (by decide +kernel)

private theorem vb11_3_12 : nb11_3_12.Valid :=
  SearchNode.cover16 nb11_3_12 (by decide) rfl
    vb11_3_12_0 vb11_3_12_1 vb11_3_12_2 vb11_3_12_3 vb11_3_12_4 vb11_3_12_5 vb11_3_12_6 vb11_3_12_7 vb11_3_12_8 vb11_3_12_9 vb11_3_12_10 vb11_3_12_11 vb11_3_12_12 vb11_3_12_13 vb11_3_12_14 vb11_3_12_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_13 : (nb11_3.atMove 13).Valid :=
  SearchNode.check _ 4 [0x14924904334da00001040001341a41a6906d34000824d34c66d3400013798006cd669849b0004e24d20db60011c4db6124800d04934820524904900c04926104934930db4920c04936d800479371848100041341041001a60008269861069a08209a69840009268269a61008249a09a69840209248249a6124920494d341249241209a68369a00001269a09a69a08040009340079b61349a68249248261240009b68269a41008249209a6900496e3018a1bceb0db6001036db61bb1e0e07ab6c36de0c001b798600cec01bcf600019b6006db61b71b6e079b6c30c66d80db798d2c184a2e92c0c30186c3cd861bcdb050, 0x2018050408421, 0x4010100500024000804800100808020200805a2, 0x16b8050412de1, 0x10020020910001400044010100400824020046ba3, 0x10a8050412de1, 0x2010850408421, 0x2012050408421, 0x20528504214a1, 0x20420504214a1, 0x20528504214a1, 0x20508504214a1, 0x20508504214a1, 0x20420504214a1, 0x218050408421, 0x818050408421, 0x1298050442521, 0x20010800500024000804800100804020100805a2, 0x298050442521, 0x100044001020100804100100804020020800825a2, 0x4011910070000c00044008100400401810060323, 0x218050408421, 0x4400110100424010084802010808020200885a2, 0x16b8050412de1, 0x1298050442521, 0x8420504814a1, 0x8420504814a1] (by decide) (by decide +kernel)

private def nb11_3_14 : SearchNode := nb11_3.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_0 : (nb11_3_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_1 : (nb11_3_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x249200209a4904920824134d209249048249a41249209049b4824104804004d2092400482c8261a48009040048208240041049209249001209a690490, 0x218048420421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_2 : (nb11_3_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x26db0c361b6db09b6db6c00db6c06236030035186826c06004d30001800c201640209b0180106034db6000d241b013590, 0x4bf000222c0004bf07980f31e600044580f30798f303cc3cc0798003cc1e61e60f307981e61e619764, 0x1400000009000000044000000050000000408002808940448000400000010200010004000080014044400040000400000088000000428088004000080010200000010000ca5726, 0xc00000009000000044000000050000000008002808940440000400000010200008000000080014044400000000400000080000000428088004000080010200000010000c85726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_3 : (nb11_3_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x249200249249049a6904824a24124820904d36824004804004d2082600082c826000120104804824920824124c2092482090493482490, 0x218048420421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_4 : (nb11_3_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x249000409e71049a0c34126da09a690782cd24126830d049b686482cc00004d30de600183cc36020830304100036186180c00004936d861b0db6d8590, 0x4800120100404010080802000804020100805a2, 0x3db3000408c00102305c52a27e0f6cc1e60f30f30b8a34c001ed980079f9807987980799e601e612ec4, 0x218048420421, 0x228048420421, 0x28804a420421, 0x3db3000408c00102305c52a285983cc003db30f30b8a34c0f307980079f980799e60079bcc01e612ec4, 0x3db3000408c00102307985b21e603cc7980f30f30f4e9cc3cc0798008127307b660007983cc1e612ec4, 0x218050440421, 0x628050440ce1, 0x218050440421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_5 : (nb11_3_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x24924920924920804900000820d2092482492482412493c1b69200009bcb0c0249bcc24920824926908d800069a6f309248248249a410, 0x418042408421, 0x418042408421, 0x418048420421, 0x418048420421, 0x418050440421, 0x442048480421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_6 : (nb11_3_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x249a683792c1241649a482000cda1b30c30db00001b6d86db6000c24920da4800104924124900020938826d20000124904924000800064104906d00104d84820d2000090432002000032032483880, 0x222b0d07983cc0098d3086ff28f379800f6d3989baa29303d3a74e6007980f737f9502300079803cc3a45, 0x500a10210860, 0x3db3000408c001f5304d5e6607981e6003db30f309ab9f30f3079800798f307980f31e607981e612d44, 0x504210210860, 0x842048480421, 0x882048480421, 0x1f53000408c001f53003ccf300798079bccf307983cc0f300f3798081366001e60f31e7e6001e704c64, 0x2139f307983cc007a730079800f379800f6cc009a3f8f303cc0f4e60079f983cd8ae0f307980003cc3a45, 0x100010000800040004000100004000100040400028081400010004000001002000100000200800140404000080004000008080000010200000040800000102000000100048b5726, 0x1024050480ce1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_7 : (nb11_3_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_8 : (nb11_3_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x34e209061209049359001359200009a0000820c30d34004de48041269a00369a000080000c030c30c04d00c04126100000000db0c3013403400498410, 0x1e601e61e601e6798081185b21e603cc7980f30f310233cc3cc079803d3a7307b660007983cc1ee246c4, 0x20080802004010100404100104100104000423a3, 0x20100804004010100404100104100104000423a3, 0x20100804040011000440101004100104000423a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_9 : (nb11_3_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x249a692c820804924124900020924824924024124904904804820804824104d209248249a000012490493400082692413490002092492092080010000cc00920f3090, 0x480412000140009004002200080402010080522, 0x480412000140009004000200080002010080522, 0x8c40584835a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_10 : (nb11_3_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x24034030006004820900020d24100034044934d84106804004d20000804d200200001a0204800820834020026900920824134c201300000209a0024820904d34830c3c060036d8690, 0x20800820020100810080102004020022000825a2, 0x20800820020100810080102004020022000825a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_11 : (nb11_3_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x2492492492080492482492402412696482600cd20b208209a00001a69049340008249241249000209a4904924000824104c04824d2080012012483480, 0x842048480421, 0x20800820020100810080102004020022000825a2, 0x20800820020100810080102004040021000825a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_12 : (nb11_3_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x24934930034936d00826000824e201000000209841000001849000049a00389a4000924037924800144d40c04127106928000826e30da6c30d24db610, 0x4000400004000000020004000020000000e0006000040002000e0006000040002000400068000400180004000100004000400080000020200000020800000102000000102008faf26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_13 : (nb11_3_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24920924004924d20db6c36db6c36126924234924100934920c249269869b4004d24d3090] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_14 : (nb11_3_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24924960d2490000482000482cd2093183492000412492c1b49200009a48001a4b3c824d000249669069a00069acf309260048249a410, 0x218042408421, 0x218042408421, 0x218042408421, 0x218042408421, 0x218042408421, 0x842048480421, 0x842048480421, 0x801020041004040100808020100800220008a5a2, 0x842048480421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_14_15 : (nb11_3_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24924904004000000db6c36db6db6124d00d34d040249249300051b4d20926d0612493480] (by decide) (by decide +kernel)

private theorem vb11_3_14 : nb11_3_14.Valid :=
  SearchNode.cover16 nb11_3_14 (by decide) rfl
    vb11_3_14_0 vb11_3_14_1 vb11_3_14_2 vb11_3_14_3 vb11_3_14_4 vb11_3_14_5 vb11_3_14_6 vb11_3_14_7 vb11_3_14_8 vb11_3_14_9 vb11_3_14_10 vb11_3_14_11 vb11_3_14_12 vb11_3_14_13 vb11_3_14_14 vb11_3_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_3_15 : (nb11_3.atMove 15).Valid :=
  SearchNode.check _ 4 [0x149a49a4134924100904800900004126904924904c349001a4930104937980046de6d849a4104924d209340008449a4126904904934c24920180126900524924120024000104d24836924c24124924d00020d269049248368249a4014004924924100800800920004100104904904c000000249001040009340059a4124800934936000100037980de6d84104924124d200009b61049a4104124924934c200251a4926900526da0da4c00104db6836924c24100024d00d669049269a4d249a08049000279a4d269049b69369249a4014db7846db6000124904d24904036db0db6db0c048008269a00001269a09a69a08049248300008269a41241208209a6900494db41049249209b61008269b4136d34904934c36da5000136d040049341249200009360069a4136d24904934c30c24da0936d049b60009008001349205249041a09a6906924936824da4104124da09a6904d24936824da412412002482080492480, 0x8420504814a1, 0x2012050420421, 0x2010850408421, 0x2010850408421, 0x20528504214a1, 0x2010850408421, 0x218050408421, 0x1298050442521] (by decide) (by decide +kernel)

private theorem vb11_3 : nb11_3.Valid :=
  SearchNode.cover16 nb11_3 (by decide) rfl
    vb11_3_0 vb11_3_1 vb11_3_2 vb11_3_3 vb11_3_4 vb11_3_5 vb11_3_6 vb11_3_7 vb11_3_8 vb11_3_9 vb11_3_10 vb11_3_11 vb11_3_12 vb11_3_13 vb11_3_14 vb11_3_15

private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_3

private def nb11_4 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_0 : (nb11_4.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_1 : (nb11_4.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_2 : (nb11_4.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_3 : (nb11_4.atMove 3).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_4 : (nb11_4.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_5 : (nb11_4.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_6 : (nb11_4.atMove 6).Valid :=
  SearchNode.check _ 4 [0x249a4926d20000924b2c9b4800066de7b37980004dbcb269200019b79ecde60001671e71b798000cdbcb26b20000b3cf2c9ac800060de78379800000041201209218379e0de600010400080482080492cb2d96c3009249249241041249249a4924834924934924904b2492492482082492082c00692cb208001249a49248209249249e68208249249269249209259bce36db6e3612cf3cf379b0c30924124b269a4800024924924904104924926924920924924924924124b249248659324b0c0600000018000cf36f36000c30186c301860001b6f3cd8606593596798000c9a69208001049249241240001249a492480412490492490492492c920c30db0180c3600033cdbcc36c30c36db6c36d86186dbcf36db19e6f379e61043269a4806804124924904904924926924920924924924924124b2492480, 0x2100884210860, 0x2042008440021, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2021084240860, 0x2021084240860, 0x2021084240860, 0x2021084240860, 0x2021084240860, 0x2100884210860, 0x902008440021, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860, 0x2101084280860, 0x2101084280860, 0x504084280860, 0x424084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x1021084280860, 0x421084280860, 0x485084280860, 0x504084210860, 0x504084210860, 0x504084210860, 0x424084280860, 0x8000a00028000c00028010200410000c000201a3, 0x80012000480014000480102004100014000403a3, 0x424084280860, 0x424084280860, 0x424084280860, 0x424084280860, 0x424084280860, 0x4141544814a1, 0x814058480421, 0x814058480421, 0x1014050480421, 0x4141544814a1, 0x814058480421, 0x814058480421, 0x1014050480421, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x821084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x441084280860, 0x441084280860, 0x421084280860, 0x821084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x481084280860, 0x481084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_7 : (nb11_4.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_8 : (nb11_4.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_9 : (nb11_4.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_10 : (nb11_4.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_11 : (nb11_4.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_12 : (nb11_4.atMove 12).Valid :=
  SearchNode.check _ 4 [0x124924a4924926924d3cf24100924904da4924924920d249249241041249249249249059249249249209b4936d249a4828d26db5b26180b24124924924920104924124124184936d249a482492490492490049248, 0x2021090880960, 0x421090880960, 0x421090880960, 0x1024090880960, 0x421090880960, 0x421090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_13 : (nb11_4.atMove 13).Valid :=
  SearchNode.check _ 4 [0x12492494d34d2492412092492492410412492492492490492492492492492412410492492492410492492492490049248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_14 : (nb11_4.atMove 14).Valid :=
  SearchNode.check _ 4 [0x24924924926920804934924920820d369b69a4d241249249249248224a4920c26924d04920824124920d369b6824d241249249049248028a4524924b2c9a48000128920a6924926b0000492492492082092492492492482c92492c904104f34934b24104126928926b000024a0924920904100824920920920c34924824104024924824924802dbc9a69ac0040a4524d389a49ac0041128920a49b6db6da69860249249249208049249249249241249acb249a00009249208249249049249248249241049b6ab49a00009349249241041a4b2c9248208249249349249079b4b25b20000b269b4d34920000920000800000820104924124124020b2c80402c8249249049249004a6d80020b24904920824124920924924904924820904120924900820920924920c36104824934024924824924836d800268208024ac904120924904f36104824924102dbc00682c9a40a4524d2000482082400402082482081289208, 0x218050440421, 0x218050440421, 0x218002408021, 0x218002408021, 0x218050440421, 0x10002400100402200084080201000402200088522, 0x10002400100402200084080201000402200088522, 0x10002400100402600084080201010002200088522, 0x10002400100402200084080201010002400088522, 0x1425090a80960, 0x425090a80960, 0x1425090a80960, 0x1024090880960, 0x1425090a80960, 0x1025090880960, 0x4a5090a80960, 0x4a5090a80960, 0x481090880960, 0x4a5090a80960, 0x1084090880960, 0x481090880960, 0x4a5090a80960, 0x1084090880960, 0x4a5090a80960, 0x1084090880960, 0x4a5090a80960, 0x4a5090a80960, 0x4a5090a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_4_15 : (nb11_4.atMove 15).Valid :=
  SearchNode.check _ 4 [0x14924924924924100924924924924822934d249240000949a41049249205249249049248104a48a48a4934d34930c025124149a49249241009269249349248249229c6d349240000940049241249205209249249248104a48a48a69b4d34930c025124149259b6d34000124944d24904034936db4d30c049a69249241041269a49249249049248201048249241200249209249004949a41049249209269249049248240049241249209209249049248220001240241040945104a48a488080410090410251240, 0x1024090880960] (by decide) (by decide +kernel)

private theorem vb11_4 : nb11_4.Valid :=
  SearchNode.cover16 nb11_4 (by decide) rfl
    vb11_4_0 vb11_4_1 vb11_4_2 vb11_4_3 vb11_4_4 vb11_4_5 vb11_4_6 vb11_4_7 vb11_4_8 vb11_4_9 vb11_4_10 vb11_4_11 vb11_4_12 vb11_4_13 vb11_4_14 vb11_4_15

private theorem tv_b11_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_4

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_6 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_0 : (nb11_6.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_1 : (nb11_6.atMove 1).Valid :=
  SearchNode.check _ 4 [0x14920004134d205249001049348100049241041208209a6924824104124924904812524db4004924920484924004924920524900104924814104924924920000d34924124124124924924820834d35934d04001924d241241149200041249204904924001249040048208249249209041049249241205041249249048129a49001049a4812092480034934d04904104924924920820d24d34d340a0824934934d0251241000c80893c9a0000904924124000120984d2480002496492490c9269249208208249249240001209241048208209249269000049249241209249249a41041849a4da6800024134904904104926934920000924d249241249a49a68141041249241200009049249241041049249048000249249249049249249204a248, 0x2101084220860, 0x504084220860, 0x28000a0080012010001100044002010080403a3, 0x404000201c100008000400000101000080000008201c000400010002020000002000100020201c100e00040400000100008001000004008000040040000100040000100048a5726, 0x2021084240860, 0x20410884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_2 : (nb11_6.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_3 : (nb11_6.atMove 3).Valid :=
  SearchNode.check _ 4 [0x149a00049249205249001249248100049241241208209a6924824104124924904812524d34004924920484924004924920924000824924124900104934824920000124900824924924100924d34924800000124924924804134d35920c04905924924800112524800104924810524800105134814924004124d204001209049248208209249209025041249249048129141249001249248249000209249049240041249209248008249240a4934924920000024924924100104d24d34830084124934920c02512410004804924920104020024904000120104924804120000124904924912510820824924924000100104904c208209249249000041049241309249249241041049249248041008209241049241249249209248000249240a48a251241252248, 0x501084240860, 0x9010884408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_4 : (nb11_6.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_5 : (nb11_6.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_6 : (nb11_6.atMove 6).Valid :=
  SearchNode.check _ 4 [0x2496496cb618049249349208209a69a6e27124124926db49a48649251256ad450134f249a48000349061ec0479e758482080480c920030187b079b602092032412480492c9ad96c300924924924104124926da49b4834d249349249049a692492482082492082c0049ac92080412092692482092592d92c860124924d24c00026924b34928b0492493c9341009269269349b8984d649659a59248248268301209a6036f269b6c20824d369a69349a0124b269268000249249249041049249a49a0820d24924924924124b249248649228a080400080010000cb34b3400082083002012400012cf24d04065934964d0000c9a49a080010492492412400012492682080412490492490492492c92082010412080400032492cc24820824000900804104b2c934920934f259a60003269268008041249249049008249249a6920104924924924124b2492480, 0x2100884210860, 0x20421084410a1, 0x2101084210860, 0x2101084210860, 0x2021084240860, 0x2021084240860, 0x2021084240860, 0x2021084240860, 0x2100884210860, 0x9021084410a1, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860, 0x501084240860, 0x2101084280860, 0x504084280860, 0x424084280860, 0x221084280860, 0x421084280860, 0x441084280860, 0x441084280860, 0x485084280860, 0x1021084280860, 0x411084280860, 0x441084280860, 0x1014210482521, 0x421084280860, 0x421084280860, 0x441084280860, 0x421084280860, 0x504084210860, 0x504084210860, 0x8000a00028040401008010200410000c010081a3, 0x80012000480404010080102004100014010083a3, 0x424084280860, 0x424084280860, 0x424084280860, 0x424084280860, 0x88b000222c0002d907aafc7981e60812afc3cc3db5d904097641e60812afc7980f31e607981e612d44, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x180006008004a010009102004008948201229a3, 0x88b000222c0004bf000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x80004000201e100000018400000041000000500004201e0004000400020200000020000800040008100f00040400000040009000080010201e0004080000010001200010004895726, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x806040002000100000018400000041000080480020000c000100020001020000002000404028000200010002040000004000508050002000020008080000004000a000100028f9c26, 0x821084280860, 0x421084280860, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e608118007b66001ed98001e612d44, 0x1014210482521, 0x1014210482521, 0x421084280860, 0x421084280860, 0x421084280860, 0x421084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_7 : (nb11_6.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_8 : (nb11_6.atMove 8).Valid :=
  SearchNode.check _ 4 [0x269a4d24d30c049a69a4920000924db6924e361269a69ac986026db69a6db0000934d30c20da4db4d00000024926920d26db69a4e381041809ac9a6804d26d26f300009249249241041249b4936820844d249349249049a69249248208269a4924920820920820006b208208001208269248209a4a34964c301a6b369d4820824926da4936984924d26924921924db6db6db4db8c378608389651b61349a022c9469841349a69ac9860249249349041049249a89a4920d34924d24924124a36db6db6db6c24924824d259200049a6b24980104924924124000126a269248041249049249049249249208001269ac9068041249249049008249a89a4920104924d2492412492492480, 0x202318c4418e1, 0x50318c4418e1, 0x21010884808e0, 0x1824088c809e0, 0x2014202442121, 0x201428a4129e1, 0x2014202442121, 0x2014202442121, 0x20442084821a1, 0x8850884808e0, 0xc630886808e0, 0x9040884108e0, 0x1824088c809e0, 0x20442084121a1, 0xc830886808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_9 : (nb11_6.atMove 9).Valid :=
  SearchNode.check _ 4 [0x14924924930020524924924904814d34924924100892520004124104120524904924904804924924920100524924924824814924924920820d34924d241040a4924934d041079c5924d600019349249241041a6924924c30810004824900920524900104824810492534d369349a4c24512824936d349a48120924a4924934d24904924924924920924924d249240a49249349249025049249249248124149144a248, 0x424084280860, 0x424084280860, 0x8c4098c809e0, 0x1084090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_10 : (nb11_6.atMove 10).Valid :=
  SearchNode.check _ 4 [0x24924d34d30c04924936920820a269b6da6e261a6928db49248249a6934db0c049269a4f66c301b6da69b6c00034d041a6024db4d04920804926920000d868256380209a00209a6804926db6db6180924924924104124936db49b4844d249349249049a69249248208269249249208209208260049269208001a082482482092493cd3cc301a49a6d248000269a6f34938b069269b6926180b2db2cd27b6c1269a8b3494ab04db71b6db6dc9036104b009359b61000280209469841349a69248000249249349041049269a8920821134924d249241249a6924824924900020024c04c00006b249240000001868240300001a69a6986034db4d24d000069249208001049249241240001a49248248041249049249049249269200008369341300001a6924824800020da69069800069a69a69a0d24db79240001a4924800804124924904900826924920820104924d249241249a692480, 0x21030886308e0, 0xd030886408e0, 0x28000a0040011008002100084002000080403a3, 0x28000a0040011008002100084002000080403a3, 0x8110884808e0, 0x8410884808e0, 0x8110884808e0, 0x814208482121, 0x8110884808e0, 0x814208482121, 0x8410884808e0, 0x8410884808e0, 0x8410884808e0, 0x8850884808e0, 0x8850884808e0, 0xc130886808e0, 0xc430886808e0, 0xc230886808e0, 0xc430886808e0, 0xc220884808e0, 0xc220884808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_11 : (nb11_6.atMove 11).Valid :=
  SearchNode.check _ 4 [0x149a4924930000524924924904014d34924924100892520004124104120504104924904804924924924100924924924104124924924934824924934924902924924924820824910824104924920400124924924810524934935030814924d24924d20536d249249248225128061269349a4c141249249249040249249349041049249249249209249249249240a48a25124149124a00049249249001049241241240001249249248041249049249029249145105041249249048041249049049049249249249209249241249240a48a251240] (by decide) (by decide +kernel)

private def nb11_6_12 : SearchNode := nb11_6.atMove 12

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_0 : (nb11_6_12.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_1 : (nb11_6_12.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_2 : (nb11_6_12.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_3 : (nb11_6_12.atMove 3).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_4 : (nb11_6_12.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_5 : (nb11_6_12.atMove 5).Valid :=
  SearchNode.check _ 3 [0x2492492692082092492492492483cf66d2496190493cf36dacb60c04926920934930900824920920920c3000692400412492482492480, 0x22118c4818e1, 0x401090880960, 0x401090880960, 0x1004090880960, 0x1004090880960, 0x2221084810a1, 0x2221084810a1, 0x1004090880960, 0x1004090880960, 0x1004090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_6 : (nb11_6_12.atMove 6).Valid :=
  SearchNode.check _ 3 [0x26d27134d249069a49289208211bd9b8dad9861249249a492482cd26d34d24904d46dc6e3cdc1005920920904924900824920920920c04806104d2412492482492480, 0x2021090880960, 0x421090880960, 0x1024090880960, 0x2010088040011008040101004100204000443a3, 0x425090a80960, 0x1025090880960, 0x1025090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_7 : (nb11_6_12.atMove 7).Valid :=
  SearchNode.check _ 3 [0x36de6da6a400069b4db69b0000db6dbc9a91b61a6d24d24d86036de6d249b1804936db6dac9b10069a49249269209a6936db49a4836d809b49b0000004820800920db6006926c0000002482402080, 0x421090880960, 0x2221084810a1, 0x1084090880960, 0x8410908809e0, 0x1084090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_8 : (nb11_6_12.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24924928920820924924a24924834927134d24904d46db71b4d30c04d34920904924900824920920920db6c06186db612492482492480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_9 : (nb11_6_12.atMove 9).Valid :=
  SearchNode.check _ 3 [0x36de4db69300069a4926920820db6934da6da61a69249a492483cde69b4db180493cdb6db49b0c04d000040008041008249209209201009040200201a492482492480, 0x1084090880960, 0x2421084810a1, 0x1084090880960, 0x1084090880960, 0x1084090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_10 : (nb11_6_12.atMove 10).Valid :=
  SearchNode.check _ 3 [0x35134d36d30c069a4928920820d34d44de6d34124924a2492483cdb6db4d30c04d249371b4d30c04900004000004100824920920920104d04000d3412492482492480, 0x10440908809e0, 0x8410908809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_11 : (nb11_6_12.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_12 : (nb11_6_12.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_13 : (nb11_6_12.atMove 13).Valid :=
  SearchNode.check _ 3 [0x249249269a6920000924d24d248001249249a4906036db6db6db0c0492492c92418092490, 0x481090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_14 : (nb11_6_12.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_12_15 : (nb11_6_12.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249675e6db6d80004926926930000924da6e268001249a49a4986036db6db6db0c069a4dbcb341809349a000693892134c209849a481249001a492680, 0x40201008100044001040801008040021000845a2, 0x140005010004c020009102004008548201229a3, 0x40201008100044001040801008040021000845a2, 0x40201008100044001040801008080022000845a2, 0x4a5090a80960, 0x4a1090880960, 0x1084090880960, 0x1084090880960] (by decide) (by decide +kernel)

private theorem vb11_6_12 : nb11_6_12.Valid :=
  SearchNode.cover16 nb11_6_12 (by decide) rfl
    vb11_6_12_0 vb11_6_12_1 vb11_6_12_2 vb11_6_12_3 vb11_6_12_4 vb11_6_12_5 vb11_6_12_6 vb11_6_12_7 vb11_6_12_8 vb11_6_12_9 vb11_6_12_10 vb11_6_12_11 vb11_6_12_12 vb11_6_12_13 vb11_6_12_14 vb11_6_12_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_13 : (nb11_6.atMove 13).Valid :=
  SearchNode.check _ 4 [0x14494d24924d300209249a6924820134924924984812524d3000c1ed920524900104964804494924924924100924d34924000124924924924824934d35920c049259251240001149240049249205249001049248104925a49249a48000249249249208049249249241005249249249040129120924a4934934900004924924924100924d24d348300a4924934920c0251241492c924d34e39135130944926da496582493493490410082c808900a20820924924124000128864c040000249649049009249249248201249249a6c30824926924926904924924924924924d20824824924826104126820c34820004924920d201249a49a4d060249249269349209249a4924924d249241249249a4d34c20824904104906000924d24124014d249249241009349349249648249249249249249249041241249241308209241041241000249249049004a49201249a012000082492492482010492492498402412492492410092cdb6006dbcdb090248, 0x4010100500044001000800100004020100805a2, 0x4010100500044001000800100004020100805a2, 0x411084280860, 0x2080082000104004100804400110802020080da2, 0x2080082000804020100804400100802020080da2, 0x1004000008010000040040000040100008000000820180004000100020200000020001000202008100600040400020000008000400004200c00040800000100010000100048a5726, 0x811084280860, 0x811084280860, 0x2080082000804020100804400110002400080da2, 0x1021084280860, 0x104308c6808e0, 0x2008080300044001004800100802020080805a2, 0x2010080500044001004800100802020080805a2, 0x4010100500044001000800100004020100805a2, 0x4010100500044001000800100004020100805a2, 0x4010100500044001000800100004024000805a2] (by decide) (by decide +kernel)

private def nb11_6_14 : SearchNode := nb11_6.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_0 : (nb11_6_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_1 : (nb11_6_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x34900024b34982d248008249241008049049041000009a092492002492412412400002682c820834900020d34d000009209a08208b4980020da6d0288, 0x10004401000804020108040201001002040088da2, 0x4400110100044001080802010080020100885a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_2 : (nb11_6_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_3 : (nb11_6_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24d800209249849a00041249209269048249a41a69000009248000049008040008209209249200309240201a6026926824924824d80024c34c028acd80020a24d8490, 0x80402010100044001080802010080022000885a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_4 : (nb11_6_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_5 : (nb11_6_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_6 : (nb11_6_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24db4da49000069a49249208209249249b41041249249a692483cda69ada00004924db6da490000490000400000410082492092092010412403012412492482692480, 0x1425090a80960, 0x425090a80960, 0x1024090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_7 : (nb11_6_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x249b6db6da6800024924934d000049269a69a0000d36924d341041a69269a89060249ac9a49a0000934d00034d24904920000c34d2410, 0x4a5090a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_8 : (nb11_6_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249249249208209249249a4924834d36d2c904104d36db6da6f00004d34920d20904100824920920920dc6006c3618612492482492480, 0x4410908809e0, 0x445090a809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_9 : (nb11_6_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x24924924980002924924924d241a69249a692483cda692cb00104934e36da4d0410488000410490410210090002492408, 0x4a5090a80960, 0x4a5090a80960, 0x1084090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_10 : (nb11_6_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x34d34d249000069a4924920820d34d44b261041249249a692483cdb6f3ce00004d34d36e24d000049000040008041008249209209a0104d0402012412492482692480, 0x445090a809e0, 0x846090c809e0, 0x10440908809e0, 0x445090a809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_11 : (nb11_6_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x24924da4900004924924920820924924924a261a49249a492483cd24b2ca80004934936da4f0000288080400080410082492092092002090402002002492482492480, 0x481090880960, 0x4a5090a80960, 0x8c6090c809e0, 0x1084090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_12 : (nb11_6_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_13 : (nb11_6_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x229249249349200049269a6920000924924d24d241a69269ac90602492c9249a00008a4900034924d02924800c2492408, 0x4a5090a80960, 0x8e7090e809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_14 : (nb11_6_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_14_15 : (nb11_6_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a49a49349a0004936926920820924924da4c20124d269a49248228a49800349a4d049200041249209a4904c24da6124d0000092480] (by decide) (by decide +kernel)

private theorem vb11_6_14 : nb11_6_14.Valid :=
  SearchNode.cover16 nb11_6_14 (by decide) rfl
    vb11_6_14_0 vb11_6_14_1 vb11_6_14_2 vb11_6_14_3 vb11_6_14_4 vb11_6_14_5 vb11_6_14_6 vb11_6_14_7 vb11_6_14_8 vb11_6_14_9 vb11_6_14_10 vb11_6_14_11 vb11_6_14_12 vb11_6_14_13 vb11_6_14_14 vb11_6_14_15

private def nb11_6_15 : SearchNode := nb11_6.atMove 15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_0 : (nb11_6_15.atMove 0).Valid :=
  SearchNode.check _ 3 [0x249200249249049200001249209248008249241249001849248148269208049201049249201240209a49a60268108249269009a04a492002492490248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_1 : (nb11_6_15.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_2 : (nb11_6_15.atMove 2).Valid :=
  SearchNode.check _ 3 [0x149200041249209249000009248041249248049048269a49049200009249241240209a69ac02682492002492490482c920804b209a68009249240a492002492490288, 0x28000a000804020100804400100802020080da2, 0x28000a000804020100804400100802020080da2, 0x4806020004020100880102004020800800825a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_3 : (nb11_6_15.atMove 3).Valid :=
  SearchNode.check _ 3 [0x249a4004924d209241349241000008249a6924820104d24924904024924930004934d20926d0012493480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_4 : (nb11_6_15.atMove 4).Valid :=
  SearchNode.check _ 3 [0x24924d349249208209a49a6924820136d2492492482492492000412492092490010492480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_5 : (nb11_6_15.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_6 : (nb11_6_15.atMove 6).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_7 : (nb11_6_15.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_8 : (nb11_6_15.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249249249208049249269208209249249249241249249a49248149144a69a092492080248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_9 : (nb11_6_15.atMove 9).Valid :=
  SearchNode.check _ 3 [0x24924924920804d34d369a00009249a4924820124924924964d2490402492092492080410400000012082012492400480, 0x441084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_10 : (nb11_6_15.atMove 10).Valid :=
  SearchNode.check _ 3 [0x149249269208209a492492482482492492492492080492692492482008412402480490200092692412408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_11 : (nb11_6_15.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_12 : (nb11_6_15.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249249a69a4930000924d24d248301249a49a6d860249249269a618092490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_13 : (nb11_6_15.atMove 13).Valid :=
  SearchNode.check _ 3 [0x14516de6db6dc0000924b249248200949249249241004a71c0004136d2052490010494480, 0xc620884808e0, 0x1c4409ce809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_14 : (nb11_6_15.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24924964934f000049ac9a69b00009359251341041249a6a2cd8602492c9a49a0000924d000249a4904924000c3592410, 0x80002010100044001080802010080022000885a2, 0x1024090880960, 0x104709ce809e0, 0x1084090880960, 0x10440908809e0, 0x1081090880960, 0x1084090880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_6_15_15 : (nb11_6_15.atMove 15).Valid :=
  SearchNode.check _ 3 [0x144949349249600009249a6924820124d2492490401252493000496592052690012496480, 0x2008080300044001002800080402020080807a2, 0x2010080500044001002800080402020080807a2, 0x4010100500044001004800100804020100805a2, 0x441084280860] (by decide) (by decide +kernel)

private theorem vb11_6_15 : nb11_6_15.Valid :=
  SearchNode.cover16 nb11_6_15 (by decide) rfl
    vb11_6_15_0 vb11_6_15_1 vb11_6_15_2 vb11_6_15_3 vb11_6_15_4 vb11_6_15_5 vb11_6_15_6 vb11_6_15_7 vb11_6_15_8 vb11_6_15_9 vb11_6_15_10 vb11_6_15_11 vb11_6_15_12 vb11_6_15_13 vb11_6_15_14 vb11_6_15_15

private theorem vb11_6 : nb11_6.Valid :=
  SearchNode.cover16 nb11_6 (by decide) rfl
    vb11_6_0 vb11_6_1 vb11_6_2 vb11_6_3 vb11_6_4 vb11_6_5 vb11_6_6 vb11_6_7 vb11_6_8 vb11_6_9 vb11_6_10 vb11_6_11 vb11_6_12 vb11_6_13 vb11_6_14 vb11_6_15

private theorem tv_b11_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_8 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_0 : (nb11_8.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_1 : (nb11_8.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_2 : (nb11_8.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_3 : (nb11_8.atMove 3).Valid :=
  SearchNode.check _ 4 [0x249249241208209249249349248240049241249209241341249241009208249241249209249249049248049261269200009249249849248261a49241208209269b49241208200001000001041201009209208208249248049248209249249249241249249b6db6db6db6c30926db4924904924814916180c000000300019e6de6c00186036d86030c00036de79b0c0cdb8f3cf3049248, 0x2101104210860, 0x2101104210860, 0x2101104210860, 0x2101104210860, 0x501104240860, 0x501104240860, 0x501104240860, 0xd031046408e0, 0x501104240860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_4 : (nb11_8.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_5 : (nb11_8.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_6 : (nb11_8.atMove 6).Valid :=
  SearchNode.check _ 4 [0x249249249208049249249208209a4924924820124924924924824924924924924906020920d34920c041049208209208001249248248049349a49a0000924d249248208249269b49249208209200008208208208209248248248209249a49248201249249a4820824924924924904924924924920924924924924d24924124134da49a69860249249249269209249b6d36d249a4824924824924920820924920900004924924820820924924924000124924924824924924904820824924c240209249a482482492492492490492492492492092492492410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_7 : (nb11_8.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_8 : (nb11_8.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_9 : (nb11_8.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_10 : (nb11_8.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_11 : (nb11_8.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_12 : (nb11_8.atMove 12).Valid :=
  SearchNode.check _ 4 [0x124924a6924d2cf241009249249209249249249049049249269208209249249249249249249209204a010092082082092492092492492490012492492492092490248, 0x1084110880960, 0x1084110880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_13 : (nb11_8.atMove 13).Valid :=
  SearchNode.check _ 4 [0x124924924a0104124920d2092492492030c1b6db6f3090248, 0x2014042408421, 0x2014058420421, 0x1e60f3445800097e000260733cde6003cc03ccf30088d22c1e607983cc8127307b660007983cc1e612ec4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_14 : (nb11_8.atMove 14).Valid :=
  SearchNode.check _ 4 [0x249228a4926da69a0804934926920820524924924924820900900920004924920820920d369b69a41241249249248248028a45249249a49a48201129249240249240920a49249249249249208049249249249241248249208049049249249241241024a69a69a49000049349249208209a89a69ac180124d249248248269a49249041028ac9ac9a49000069b4924920820520800924124920c36924924104020124804924804936f379b00009a49269b69269200009a49249a48208208068200008208249248208248208a4524b249249260041249249248208128920a08000009201008049208249209209a4020b24020124824824806024904124902880020980020900820920124820524924804924820800900924104300924104924102dbc9a618c9a40a4524c269241008241a492482082481212492402492409208, 0x3e2e6603db3000f6cc3cc03ccf3003cde600f4e607b6d9800204603cc7a7307b660007983cc1edaaec4, 0x1084120840960, 0x80402020080082002100404010080022000885a2, 0x1e60f3445800097e000222c03ccf3003cde600f300904800222c000408c7a7307b660007983cc1edaeb84, 0x1004110880960, 0x424104a80960, 0x1c2410ce809e0, 0x8c4118c809e0, 0x1084110880960, 0x4a4114a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_8_15 : (nb11_8.atMove 15).Valid :=
  SearchNode.check _ 4 [0x149228a4924924d24100936da4d240001249249249248148041241009205249249248248104a48a48a4924936904102524924904924812414b24924924924924104124924926924904034924124100924924004124124924920904900494934924924100d36d66934000124d24924924827126db4d349028a5947964d24000114104124924920504d249249248104a48a48e79e6dc798000251242400492480002090492493490482403492492410092c23cb069200009200049241b4d209049249349348048249241009209269249248248228a40041241249201041000200001209249249248143041241249205104a48a488412493092490252492490492481240, 0x2014050408421, 0x814058480421, 0x814058480421, 0x1014050480421, 0x421104280860, 0x421104280860, 0x421104280860, 0x421104280860, 0xc21104280860, 0x421104280860, 0x421104280860, 0xc24110e809e0, 0x840120080860] (by decide) (by decide +kernel)

private theorem vb11_8 : nb11_8.Valid :=
  SearchNode.cover16 nb11_8 (by decide) rfl
    vb11_8_0 vb11_8_1 vb11_8_2 vb11_8_3 vb11_8_4 vb11_8_5 vb11_8_6 vb11_8_7 vb11_8_8 vb11_8_9 vb11_8_10 vb11_8_11 vb11_8_12 vb11_8_13 vb11_8_14 vb11_8_15

private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_8

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_10 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_0 : (nb11_10.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_1 : (nb11_10.atMove 1).Valid :=
  SearchNode.check _ 4 [0x14924920804d205249249248348129e6924820124110004924904120504924924904820824124920904c349241009204849249a41009205249249248248149241049a4d24920106924d341241249249249248108049200249204904925245129249249248241a4936d348248120924a48861b6db6d86d825049249349248124124944a0824920924900824920100120924924924b2412492490490482492492690248, 0x2010850408421, 0x840120000860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_2 : (nb11_10.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_3 : (nb11_10.atMove 3).Valid :=
  SearchNode.check _ 4 [0x149a08000049205249241040248129e6920820124104120d04904c100040241241205041209049048208241a0920904c349041009204849249841009209249241049241249249048348249249001049008249b59241008001249649348208249a4d24100820924d3490400012496492481252482080092481052492480000481492492412012052c9209048040379840061a1802404120d04904812920804824824000024934900814924924d241201249201040248249041041249049249241209209249248241240a48801349b6920002400124934924812412c30db6c36db6000036c06db6c30c36db6db6d86186db61b0db0934b249a6104126904924804104900924904924924924920924924024924124934924810004804900d001041240249040001249048248041249001249049249125105041269049248041049009249049249249249209249240249240a48b2512420824920924900004824004c20820934924b2400012492483482492c92490248, 0x2101104210860, 0x2010850408421, 0x2101104230860, 0x1080042002200088300104004040801008051a3, 0x40081002002200088100104004040801008051a3, 0x20100804000104004100804000020020800805a2, 0x501104240860, 0xd031046408e0, 0x501104240860, 0x400810020024000881001040040808020100d1a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_4 : (nb11_10.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_5 : (nb11_10.atMove 5).Valid :=
  SearchNode.check _ 4 [0x149249249200205249249249048129e6924924820114d249249241004a00049249041205249249249048049249a4920100524924924924814924924924d208208901049a4920920524924924924810492524512824936d349a48120924a48a251241249449248, 0x840100080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_6 : (nb11_10.atMove 6).Valid :=
  SearchNode.check _ 4 [0x24924d24920c049249249208209a6b6c9a49a61a6924924824824d249a4da6920c049249369248301a69a69a48000040240208049041049208209200009349a40200001249a68248049449a49a0000924d249268208249269b49249208209200008208209208209248268248209249369268301249249a68208249249269269069249269a09209349a69b49a4a26124924926926904100900820124100024926904904134da69a48000249369a69208209249b6d36d249a48249248249249000240209248000049269a48200009348249240001249a6924824d24924904000900824d200209249a68248000249209249008249269a4920934924d2410, 0x841104280860, 0xc61104280860, 0x841104280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_7 : (nb11_10.atMove 7).Valid :=
  SearchNode.check _ 4 [0x149a49249300005249249249040129e6924924820114d349249241004a00041241041205061209049048049249a49241009249249241041249249248348249249399049049229249a69241041249249348208108049a4104920400124924824810524924935830814924924d24d2052c926924834c379b4da7986182512806238de7830c14124926944904024934d249041049249249249209249249a49240a48e25249249b49248124128944900049a49249001041248241240001249248248041249001249049229145105041269249048041041209049049249249249209249240249240a48e251240, 0x2101902310860, 0x1ebc1307983cc001023000f7439a0f379807d4c20bf8f303cc0f4e60079f98443b860f3079801e60f6a45, 0x411104280860, 0x411104280860, 0x840108080860, 0x840108080860, 0x840108080860, 0x485114a80960, 0x1004110880960, 0x840100080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_8 : (nb11_10.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_9 : (nb11_10.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_10 : (nb11_10.atMove 10).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_11 : (nb11_10.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_12 : (nb11_10.atMove 12).Valid :=
  SearchNode.check _ 4 [0x249349349a69369200009249249a4906020986db692000482693000092134da48208040124924984026802924924d24924924d248241240924b6db6db6db0c049a49bcd20000db6db6db6c301a49a4d249a69208209a6d249a4924830db49b6920c041249a0820920d86d249a48248069a49269a0820924926920924928924920920924924b24924824924924924924d249241240a08000009241001809208208208201360249041249001b49b69b0c00124926924920c36924d2492412490248, 0x1004110880960, 0x1084110880960, 0x1084120840960, 0x1084120840960, 0x1084120840960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_13 : (nb11_10.atMove 13).Valid :=
  SearchNode.check _ 4 [0x14492914d449249600205349249249048249249a4920804d309a08019205249249048648044949249249a4d24100926924d341041249249249248108248041009205249249248248104925245128249249249a41120924a48a2504924924924812412494f3ae3734a0001249a4924134da4924120366d249248341049249249209004a0924124920800924920100020924924924824124924924904824924124024924920920c3cd86db6f3090248, 0x304042408421, 0x804d400020001000000014000000050000804d0200000200800000801002000002000004402680010000200024000000040010804d0020000040080800000040002000100008ffc26, 0x411104280860, 0x415110a80960, 0x485104a80960, 0x485110a80960, 0x2008080204100104100804000802020080805a2, 0x2010080404100104100804000802020080805a2, 0x420104080860] (by decide) (by decide +kernel)

private def nb11_10_14 : SearchNode := nb11_10.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_0 : (nb11_10_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_1 : (nb11_10_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x34924d80804982d2492412412413492490412490490080400092400692492082092012492402492408080418092410288] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_2 : (nb11_10_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_3 : (nb11_10_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x4024100804800804920824920000934024020020124820824804024d80024902300db6180e360a080000092400082092012482092093402092412492480092482080000092418490, 0x80402020080102004100404010080020800885a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_4 : (nb11_10_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_5 : (nb11_10_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x24924d249200029249249249241249269a482082492492490410493cf2c9a69800049249249208208a0804d0492410292492402492408, 0x844118c809e0, 0x1004110880960, 0x1004110880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_6 : (nb11_10_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x36e37a3cd80004d24934db4934900004d34d24d24104104c34100004904134d2410412410, 0x424104a80960, 0x1c2410ce809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_7 : (nb11_10_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x34da4d249800069b4924920820db69349a41a61a6d249a6824834da4da4900002f36db6dbc0060bcda69a69800069b492492082090000000492410080092412492000093402092402012480092480, 0x1084110880960, 0x4e411ca809e0, 0x1084118880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_8 : (nb11_10_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_9 : (nb11_10_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_10 : (nb11_10_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_11 : (nb11_10_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x249249249a4d24900004924934924104104024d0000490492493410412410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_12 : (nb11_10_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_13 : (nb11_10_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x229249249a4da49200049249249249240a4824000804d0292492412412408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_14 : (nb11_10_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_14_15 : (nb11_10_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a2ca49a49a4920004934926920820924934924924124d24924924824824800804d049249208209209a4934124020124d2492482480] (by decide) (by decide +kernel)

private theorem vb11_10_14 : nb11_10_14.Valid :=
  SearchNode.cover16 nb11_10_14 (by decide) rfl
    vb11_10_14_0 vb11_10_14_1 vb11_10_14_2 vb11_10_14_3 vb11_10_14_4 vb11_10_14_5 vb11_10_14_6 vb11_10_14_7 vb11_10_14_8 vb11_10_14_9 vb11_10_14_10 vb11_10_14_11 vb11_10_14_12 vb11_10_14_13 vb11_10_14_14 vb11_10_14_15

private def nb11_10_15 : SearchNode := nb11_10.atMove 15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_0 : (nb11_10_15.atMove 0).Valid :=
  SearchNode.check _ 3 [0x24924d2080490492c9a082492092492482412412492498482481491492002010000048002492092490248, 0x294920940960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_1 : (nb11_10_15.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_2 : (nb11_10_15.atMove 2).Valid :=
  SearchNode.check _ 3 [0x14924920824920924924804824824924d208049049a69348201241041240269249041049269a49200009248249240861a4c2c92490288, 0x88b000222c0004bf000f33cc03ccf379801e603cc1e60f6cc001e61e60f301e63cc07987981e64f404] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_3 : (nb11_10_15.atMove 3).Valid :=
  SearchNode.check _ 3 [0x20924124920800804904104d208268049248241249249b49048241049208249a6104d20924904020c3d988f3d2b09240008251b4d2080012490493480, 0x3db3000f6cc001f53000f33cc03ccf379801e603cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x80004000201e100000018400000041000000500040201e0040000400200200000200000800040008100f00040400000040009000080010201e0004080000010001200010004895726, 0x3db3000f6cc001f53000f33cc03ccf379801e603cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x80004000201e100000008400000041000000100040201e0040000400200200000200000800040008100f00040400000040008000080010201e0004080000010001000010004895726] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_4 : (nb11_10_15.atMove 4).Valid :=
  SearchNode.check _ 3 [0x24924d2492080492c9a49208209249249249241249249a4924814914926da6d361804a248, 0x4a5110a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_5 : (nb11_10_15.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_6 : (nb11_10_15.atMove 6).Valid :=
  SearchNode.check _ 3 [0x149249249208209a49349248201a49249a4924824924d24920804924934924c2012488602402492490200092482492408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_7 : (nb11_10_15.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_8 : (nb11_10_15.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24924d24d34924d2082092492493492482492412092080492492002092092492490482480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_9 : (nb11_10_15.atMove 9).Valid :=
  SearchNode.check _ 3 [0x249a49259b4d36db0c30936d269649b4c36db6db6db0c059b4d30c30180966d2690480400, 0xa14120d409e0, 0xa14120d409e0, 0xc21104280860, 0xc24110e809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_10 : (nb11_10_15.atMove 10).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_11 : (nb11_10_15.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_12 : (nb11_10_15.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249249249a4936d2000092092493692490490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_13 : (nb11_10_15.atMove 13).Valid :=
  SearchNode.check _ 3 [0x1451d8949349351200004a09ad9289209011c69200251a042492490490480, 0x1014208482121, 0x1014210482521, 0x840120080860, 0x840120080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_14 : (nb11_10_15.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24924924d34f64900004924925924104124104000004904924d3410412410, 0x1004110880960, 0x1084110880960, 0x1084108880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_10_15_15 : (nb11_10_15.atMove 15).Valid :=
  SearchNode.check _ 3 [0x1449291493492592000052492496490402492492c92080493492000192052092490406480, 0x210920108860, 0x210920108860, 0x1014210482521, 0x421104280860, 0x421104280860] (by decide) (by decide +kernel)

private theorem vb11_10_15 : nb11_10_15.Valid :=
  SearchNode.cover16 nb11_10_15 (by decide) rfl
    vb11_10_15_0 vb11_10_15_1 vb11_10_15_2 vb11_10_15_3 vb11_10_15_4 vb11_10_15_5 vb11_10_15_6 vb11_10_15_7 vb11_10_15_8 vb11_10_15_9 vb11_10_15_10 vb11_10_15_11 vb11_10_15_12 vb11_10_15_13 vb11_10_15_14 vb11_10_15_15

private theorem vb11_10 : nb11_10.Valid :=
  SearchNode.cover16 nb11_10 (by decide) rfl
    vb11_10_0 vb11_10_1 vb11_10_2 vb11_10_3 vb11_10_4 vb11_10_5 vb11_10_6 vb11_10_7 vb11_10_8 vb11_10_9 vb11_10_10 vb11_10_11 vb11_10_12 vb11_10_13 vb11_10_14 vb11_10_15

private theorem tv_b11_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_10

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_12 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_0 : (nb11_12.atMove 0).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_1 : (nb11_12.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_2 : (nb11_12.atMove 2).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_3 : (nb11_12.atMove 3).Valid :=
  SearchNode.check _ 4 [0x249a41049249209249249241208209249249349248249249208241249209249249049248069a6186d24db09201208209200009249248249248269a61869249a00041041240001249261869249a09a4924984924820924924904924924904024924124924920934935920c049248161b61e61b00009249261b69b6f20000034d24d640001849acdac8000249209249249049a69a49860249241249249b6db6db6db6c30934934d30c04924814100120100000105800d259641049249a412482c104924d24924104b34e64b0c024924934924906920c3cc38f3cf30020820925924000330de6f3cc0002006492490049248, 0x500a04210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x500a04210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x212008480021, 0x212008480021, 0x242008480021, 0x242008480021, 0x10080022000820020800804020110002400080da2, 0x504204210860, 0x504204210860, 0x504204210860, 0x2211044810a1, 0x2221084810a1, 0x2211044810a1, 0x2211044810a1, 0x284202482121, 0x2211084810a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_4 : (nb11_12.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_5 : (nb11_12.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_12_6 : SearchNode := nb11_12.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_0 : (nb11_12_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x2490490080010092492082492092492412412412492482482482092492692092092492412412412492482482482082082c92490490002003492490490, 0x500a04210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_1 : (nb11_12_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x24820c301208209a6936da49a4820c36db0c36db09b6db6db6db6c2000cc379bcf309001201a49b6984000800924d2410, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_2 : (nb11_12_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x20820824904100924920824920824924924824820924926920920824924824824804124124924d8400080092492410013413c924d8490, 0x500a04210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_3 : (nb11_12_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920934920c0000c820820f30824924d26924120020806104820824c26da68301b6db6db6db6c20c3c826b2cf30924104104924920000c00db6db60001001a492480, 0x501204210860, 0x501204210860, 0x501204210860, 0x501204210860, 0x504210210860, 0x504210210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_4 : (nb11_12_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x24924924920c049249249208209249249249241249249a4924826924926924920924924d2492412492492492482492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_5 : (nb11_12_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_6 : (nb11_12_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x249249249208209249249249248269249269249209a492492492482490412412492490400080092492410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_7 : (nb11_12_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x26db6db6dc1030b249269061a61249b8988186205366da0000b04926f260003001649cc80, 0x501a02318860, 0x501a02310860, 0x501a02318860, 0x501204208860, 0x3db3000f6cc001f5304d5e6603cc1e60f30799357bab9f3003cc1e60f37980799e60079bcc01e6314c4, 0x501a02310860, 0x501a02318860, 0x3db3000f6cc001f5303e2e66001e7e60f30798f3099c6f3003cfcc00fa98007b660008118001e6314c4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_8 : (nb11_12_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24924936db6db6d8618492092493492490490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_9 : (nb11_12_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2c92c926dbc904104926b2c9b6d800059249279208209249249a49248209369bc920000924920020920c36db6f3618612492482482480, 0x812008480021, 0x812008480021, 0x421204280860, 0x425210a80960, 0x4e7208e809e0, 0x4a5210a80960, 0x421204280860, 0x4a5210a80960, 0x484220280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_10 : (nb11_12_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x24d34d36d8000492492490012493492490490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_11 : (nb11_12_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x24b2c92d9208209a49249a49248269a49269a49209a692492492482c90c12412492490400080092492410, 0x501204240860, 0x501204280860, 0x425210a80960, 0x4a5210a80960, 0x4a5210a80960, 0x4a5210a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_12 : (nb11_12_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_13 : (nb11_12_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x279d71b99b000092492c92cb26980184924936d648208209209348209009249249249208249249a492480, 0x421204280860, 0x4e7208e809e0, 0x4e7208e809e0, 0x4a5210a80960, 0x485204280860, 0x485210a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_14 : (nb11_12_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_6_15 : (nb11_12_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a49a6d20820924924934820826b28926900004924d369200009269a69a6980004924d34920000926936d249000209a69369200001241300009209a0820db6000100806c0402080, 0x424210280860] (by decide) (by decide +kernel)

private theorem vb11_12_6 : nb11_12_6.Valid :=
  SearchNode.cover16 nb11_12_6 (by decide) rfl
    vb11_12_6_0 vb11_12_6_1 vb11_12_6_2 vb11_12_6_3 vb11_12_6_4 vb11_12_6_5 vb11_12_6_6 vb11_12_6_7 vb11_12_6_8 vb11_12_6_9 vb11_12_6_10 vb11_12_6_11 vb11_12_6_12 vb11_12_6_13 vb11_12_6_14 vb11_12_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_7 : (nb11_12.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_8 : (nb11_12.atMove 8).Valid :=
  SearchNode.check _ 4 [0x124924ac9249a6db6180926926db6db6db0c30926920920924904904924d36da00009249e49249e4820824924924d241041349249349249069261b61a41809249241041241849249349049004a09201809a4820924920926926924900926b269a018092490248, 0x12008480021, 0x827204e809e0, 0x827210e809e0, 0x8c42184809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_9 : (nb11_12.atMove 9).Valid :=
  SearchNode.check _ 4 [0x124924959251379200009279b6db79b0c309649249e48208271e6db6db0000924924d241041349249349249061261b6124000124924104124186db6d86c30c049249049049004a012000092082092492c12cb2692000092490248, 0x812008480021, 0x812008480021, 0x814058480421, 0x1425210a80960, 0x421204280860, 0x1425210a80960, 0x421204280860, 0x1425210a80960, 0x421204280860, 0x424210280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_10 : (nb11_12.atMove 10).Valid :=
  SearchNode.check _ 4 [0x24924b269a49a6d20c06d24936920820924924b26934136d259a69248269a4820004d04d249308209209249249a6030136d259a68248028924b69a4b2cdb0000d24db6db6db6db0c06924d36920000e37b36f66f661ac9269a49060000000001200069248200009a0c36db6db6030020926984026804924936d200009a49e4924a668208271b6db6db6180924924d341043349249349249008201b0324000924924104124008db6db6c36c04924934904900d249659b6db6db6c301249249a482086c924926924920024066064800104924820824800db6db6d86d8c1249269209200b0c00c001b41009a0180824820d34030106d04124930d34db6d80000826b26b20000d34d66d6580012490248, 0x1e78ae079bcc00f31e6c571e61e601e60f3079b15d09c8f301e63cc079f98007b660008118001ead1ec4, 0x4111044810a1, 0x8121044810a1, 0x4111044810a1, 0x812008480021, 0x4006020004004000040040000040040000004200000002100000021000000021000800042022000002008000008020000020084040020200000010000200100040000102108fa726, 0x1e78ae07987980f31e6c571e61e601e60f3079b15d09c8f301e63cc079f98007b660008118001ead1ec4, 0x1e78ae07987980f31e6c571e61e601e60f3079b15d09c8f301e63cc079f98007b660008118001ead1ec4, 0x8e120c6809e0, 0x1e76c8079bcc00f31e6b641e61e601e60f30799e6102379801e7e60079f98007b660008118001ead1ec4, 0x8802084809e0, 0x20800808040201008100104004100024000865a2, 0x1e601e67980798f30100242661e601e60f3079b491c4810799e63cc079f98007b660008118001eaf04c4, 0x1e601e67980798f300fe641e61e601e60f30799e6102379801e7e60079f98007b660008118001eaf04c4, 0x827204e809e0, 0x827210e809e0, 0x861218c809e0, 0x6211024810a1, 0x1e76edff9bcc00f3007d5f1a6000f4e60f30798007a78b21e7e6003d39f98007b660008118001ead1ec4, 0x8c6218c809e0, 0x8e7204e809e0, 0x8842084809e0, 0x8842084809e0, 0x8c42184809e0, 0x8c42184809e0, 0x850a204209e0, 0x8612084809e0, 0x8c6204c809e0, 0x8422204809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_11 : (nb11_12.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_12 : (nb11_12.atMove 12).Valid :=
  SearchNode.check _ 4 [0x124924a4924936d200009249649249e4820824924924d241041b5936de68208249249249249069241b61a41809249241041241049249249049004a69241868249a0924926924b26b2018092490248, 0x8111044810a1, 0x12008480021, 0x1025204a80960, 0x1021210880960, 0x1025204a80960, 0x1025210880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_13 : (nb11_12.atMove 13).Valid :=
  SearchNode.check _ 4 [0x12492494934934d200009249649249650008249249249241041249249249249049241b41241009249241041241049249249049004a6924184924d20924926924b24920100926f3c006db6f3090248, 0x1018042408421, 0x1eace35b23cc0798f3025f81e61e601e679807980088d5f8222c0003cc812afc7b660007983cc1e612ec4, 0x1018050440421, 0x1012048480421, 0x421204280860, 0x1425210a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_14 : (nb11_12.atMove 14).Valid :=
  SearchNode.check _ 4 [0x124b28e59379e7b66d8000492492c920820724924b24924800900180920004924920820920f379e6f36060324924b248248028a4524db6db79b6c30124924b248208129249240249240920b2cb4d671e590000492c9a4e20820f37a46dc6006326928b349a486492ce34b20000524900024124920f301b6c379e6326900804924804924d3532482082cb6cdc6e66c00026a2c9ec9a40009249259241041a7926b6492082492496492490082c800000b2092492410412400002c8648000049249649049008a4624b2cdac800025924b249a48000128920a69b0830926d029249a4c2cb2408416000000590490c000024820824020024806020100004824837980060de780492082c12482052492480492482c960860925905902ca4524db6c31836db61a4b2c80402c81392492582492409208, 0x2181044090a1, 0x218050408421, 0x1084220810960, 0x1084220810960, 0x1084220810960, 0x4181044110a1, 0x80402020100204008100804010080022000885a2, 0x218002408021, 0x2181044090a1, 0x218008408021, 0x218002408021, 0x8010200500104004008100204008104004021a3, 0x6181024110a1, 0x6181024110a1, 0x4181044110a1, 0x14181504114a1, 0x80402020080202008100404010020020800885a2, 0x80402020080202008100404010080022000885a2, 0x80402020080202008100404010080022000885a2, 0x1018050440421, 0x1018042440421, 0x1084204880960, 0x4281044810a1, 0x1084208880960, 0x1084208880960, 0x1084208880960, 0x8004200100120004810040401010002200088da2, 0x1024220810960, 0x1024220810960, 0x4002200104020400810080401000402200088522, 0x4002200104020400810080401010002200088522, 0x1021210880960, 0x1025204a80960, 0x1021210880960, 0x1021210880960, 0x1021210880960, 0x1024210880960, 0x1024208880960, 0x1024210880960, 0x1025204a80960, 0x1025214a80960, 0x1025210880960, 0x1025210880960, 0x1024220880960, 0x1025210880960, 0x8040201100104004008100804080102004021a3, 0x2281024090a1, 0x2281024090a1, 0x2281024090a1, 0x10a5204a80960, 0x10a4204880960, 0x4281044810a1, 0x1084208880960, 0x1084208880960, 0x1084210880960, 0x1084210880960, 0x1084208880960, 0x1084210880960, 0x1084210880960, 0x1084210880960, 0x1081210880960, 0x1004210880960, 0x80402010001200048100404010100022000885a2, 0x1080a20840960, 0x1084220840960, 0x1084220810960, 0x1084220840960, 0x1084220840960, 0x1084220840960, 0x1081210880960, 0x1081210880960, 0x1081210880960, 0x1084210880960, 0x1084208880960, 0x1084210880960, 0x1084210880960, 0x1084210880960, 0x1084220880960, 0x1084220880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_12_15 : (nb11_12.atMove 15).Valid :=
  SearchNode.check _ 4 [0x124928a49249a4924924100924924d241041249249249248149a49041009205249249248248104a48a48a4924934904102524924904924812412db4d64d240000a7134945920c04924924924100e34d24d340001649249249a4837134944d30c05b259649240001148241049249205001001049248104a48a48ed9649349000025124249241249a4d0002090492493490482d90cf349a0000924d300041b4d209349249049348028a4824924100920926926904824824b24104124920024104000104126920904924814b241041249205104a48a488010490080410252492490492481240, 0x1018050408421, 0x1088210412121, 0x1012048480421, 0x1012048480421, 0x80012000480014000480102004100014000403a3, 0x1014050480421, 0x421204280860, 0x421204280860, 0x424204280860, 0x421204280860, 0x421204280860, 0x421204280860, 0x424204280860, 0x421204280860, 0x424204280860, 0x1021210880960, 0x1025210880960] (by decide) (by decide +kernel)

private theorem vb11_12 : nb11_12.Valid :=
  SearchNode.cover16 nb11_12 (by decide) rfl
    vb11_12_0 vb11_12_1 vb11_12_2 vb11_12_3 vb11_12_4 vb11_12_5 vb11_12_6 vb11_12_7 vb11_12_8 vb11_12_9 vb11_12_10 vb11_12_11 vb11_12_12 vb11_12_13 vb11_12_14 vb11_12_15

private theorem tv_b11_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_12

private def nb11_13 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_0 : (nb11_13.atMove 0).Valid :=
  SearchNode.check _ 4 [0x24924924920124d20920100030120820926a2cb20166b20904914924920124d209249261b6de6db0060124d36d2400012492091410003012002012492492c18410492496492690c13493692c18432692618cf38f3c3301048049218241b6f0cde6f0cc24920964920900494dbcb26136b209b69b60049241b6c30d86dc6c26da6db092490cb261b0c661b61e0186186000000136d861b0dbcd84b2048, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60008118001e616824, 0x1008210442121, 0x80040002200000001000200010000800018000402020000001080000004200000010000440020001000020001400000004000200040020000020010000200100000200100029fe326, 0x84000002200000001020000010080000018000402020000001080000004200000010000440020001000020001400000004000204000020002000010020000100020000100029fe326, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60008118001e616824, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60008118001e616824, 0x108821240a121, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60007980f31e616824, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60007980f31e616824, 0x20422084121a1, 0x2080a0240a121, 0x2080a0240a121, 0x2080a0240a121, 0x2080a0a422121, 0x2080a0a422121, 0x100004000002204008002100084002000088041a3, 0x2080a0240a121, 0x2080a0240a121, 0x20c0a064131a1, 0x2080a0a422121, 0x2080a0a422121, 0x100804000010200408010100404100204008041a3, 0x4121846808e0, 0x100804000020200808020100804100204008041a3, 0x414084280860, 0x414084280860, 0x80040002200000001000200010000800010004402000002001000020004000020010040042000100002000100400000400020080000020200000010800000102000000100108fe326, 0x8120884808e0, 0x28821040a121, 0x1008210442121, 0x1e600025f80003cc3cc16c83cc1e600081180020460f3000222c0003cc1e61e63cc07987980f31e616824, 0x1e600025f80003cc3cc16c83cc1e600081180020460f3000222c0003cc1e61e63cc07987980f31e616824] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_1 : (nb11_13.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_13_2 : SearchNode := nb11_13.atMove 2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_0 : (nb11_13_2.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_1 : (nb11_13_2.atMove 1).Valid :=
  SearchNode.check _ 3 [0x28980030d3cf06db0c361a69a09b6c30d869a6824920104db413610092490, 0x1088202442121, 0x1088202442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_2 : (nb11_13_2.atMove 2).Valid :=
  SearchNode.check _ 3 [0x38d801311b4d06db0c361269a0db6c30d849a6864d00000180000000c30db00000001a61b61e60001c6c30186de8c2590, 0x80040002000040002800400020000400028000402020000008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26, 0x1088210442121, 0x3cc01e6f30079bcc01e6f307983cc0000f3079803cc0000f307983cc25f8002046001ed98001e652644, 0x80040002000040002800400020000400028000402020000008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_3 : (nb11_13_2.atMove 3).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_4 : (nb11_13_2.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_5 : (nb11_13_2.atMove 5).Valid :=
  SearchNode.check _ 3 [0x208269309001849b4920c20806126d249348201849b4930c20030db6db6db60061b6db6db6c2492000400490412080010012490480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_6 : (nb11_13_2.atMove 6).Valid :=
  SearchNode.check _ 3 [0x1009001849b4960c20806126da4934800c24f3cb6cb001849b4960c2013493cda4f2c0081b8e3cdb6c34900c061c79e018000400490c02003093002002000010002090480, 0x1e600044580011160001e6222c00088bf300f33cc3cc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0x1e600044580011160001e6f6cc003db3f307983cc3cc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0x1e600025f800097e0f30000fa98004458000fa98003d3981024e6003d39803ea6003cc79803ea61029745, 0xc121846808e0, 0x211084280860, 0x211084280860, 0x811084280860, 0x4121846808e0, 0x211084280860, 0x211084280860, 0x2800080420200808020100804100204008043a3, 0x411084280860, 0x411084280860, 0x811084280860, 0x414084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_7 : (nb11_13_2.atMove 7).Valid :=
  SearchNode.check _ 3 [0x20826930900184c34920000804136d249040201849bcf60c20030db6db6db60061b6e36e3902492000410492412080412092490480, 0x4121884808e0, 0xc121884808e0, 0x8120884808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_8 : (nb11_13_2.atMove 8).Valid :=
  SearchNode.check _ 3 [0x38d80180006d86db0c301b0db0db6c30c06c36c64d00c671b8db1800dbcdb8f360001b79b6e67000046db8e48db6c3590, 0x84000002004000002840000020040000028000402020000008080000010200000040040042000040002000200420000200020080000020200000020800000102000000100128faf26, 0xc131886808e0, 0xc121884808e0, 0x4131886808e0, 0x4121884808e0, 0x644ac92b4c4fa767d90ba1afb864930e38cc41966d40388c7c8c9916550712d1039bbe2c04973b7a1a6f8d47d027c8b3246cab72999998077412b19341923ee4c0764d06ad44e13677dc3b94154077412b19341930716024a0c920d165f1341923f490b3c9b9dbd137c7308b86beaa01d6c3225632683310659b500c92262c32fcb58caf48bb6eb603228857cb58caf48bb6eb6191442be5ac657a45db75b0c8a215f2d632bd22edbad8064510af96b195e9176dd6cc8a215f2d632bd22edbad80191442be5ac657a45db75bc8a215f2d632bd22edbad80064510af96b195e9176dd6c0c8a215f2d632bd22edbad80c8a215f2d63879aefb15a40498d48a70ea8dad180d9fac64d096b503829de0d16f9f496081e3951858832cda806495e4c9d0d096b50343ef247d6536264d0648fa029f558cfe5758410abf0f8e70cc91f594d899341924011a0c9347d6eae546148fa01d8512b199863ea3513e8a666a72495e4c9d0d0648fa0367eb193425ad40dd8521e8e104aed1bc835983b53e9e532922ea8d7fa0c9e7d5c7720c91f72603b268646d33353924e14bb1ad0655835aa060c91f403ad8644de8a338b12c4b37f9cf3419ec7d93f50c93852ec6b419560d6a818324834597c4d07118f8e70cc951659dfe83279f571dc83247d027c8b1940a27cb1a8241f72603b268420cc3e34825ffe3ee35058f3152c35, 0x8120884808e0, 0x84000002004000002840000020040000028000402020000008080000010200000040040042000040002000200420000200020080000020200000020800000102000000100128faf26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_9 : (nb11_13_2.atMove 9).Valid :=
  SearchNode.check _ 3 [0x26980030d3cb06db0c30038db09b6c30d86db6c249a09249b493610093490, 0x1088208442121, 0x1088208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_10 : (nb11_13_2.atMove 10).Valid :=
  SearchNode.check _ 3 [0x36d80000d8c906db0c301b0e30db6c30c06c36c24d80c36e369800009269b69200001a4db6da600012490, 0x2010080500024000820800804002020080825a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_11 : (nb11_13_2.atMove 11).Valid :=
  SearchNode.check _ 3 [0x2698002093cb06db0c300269209b6c30d049a4824920d34db492410092490, 0x1088208442121, 0x1088208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_12 : (nb11_13_2.atMove 12).Valid :=
  SearchNode.check _ 3 [0x38d801b0e37986db0c361bcdb11b6c30d86db6c30f00030db0d840301b6c30186130dbce3cc363019b6d80030db6d8523c180c36f3610, 0x21821240a521, 0x29821244a521, 0x3b9b0d0e251cd651dcd662a05f20001dcd660c389473594773598a817cf7483818cca003ba9b0b2800eea6c2ca000ef599328003bb8976842771373597b9acaee6b2f73595dcd6c735941dcd6c735a2e6b2800eea6c2ca003ba9b0b280077712eca000ef599328000ef59b955ba1c8, 0x200001000800004002000010004000028000002020001000080000008020000090080040001000100000800000802000100080000004200000080800000042000000100809c5c26, 0x415290a80960, 0x415290a80960, 0x1e60004458000f6cc0025f83cc1e600118f8005b998f300f33cc03cc1e61e6003cfcc007a73001e9e2824, 0x21821240a521, 0x109821240a521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_13 : (nb11_13_2.atMove 13).Valid :=
  SearchNode.check _ 3 [0x36d80066decd86db0c361bcdb0db6c30d86db6c049e6dc69b00041349b71a4da6120f3cdbcdb0000f44980c469b71851349b7024da610, 0x4010100500024000804800100900024000805a2, 0x411084280860, 0x411084280860, 0x411084280860, 0x411084280860, 0x21821040a521, 0x1088210442121, 0x109821040a521, 0x1088210412121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_14 : (nb11_13_2.atMove 14).Valid :=
  SearchNode.check _ 3 [0x36d80030db7186db0c361bcdb0db6c30d86db6c040061b0030004134db6c00db6126f3cdb6c300009b4d800001b718514423c006f4610, 0x21820240a121, 0x4bac702061882a61172f474ca2a537dc3b94154075b0113cda185f6abd608330d6536264d06620cb36a019257932743425ad40d0fbc91f594d8cb597c4a6b2bd800ecf12b19341c463e39c33247d659a7113534f42fbd896c1912b199863ea350da3fa01d8512b19343236999a9c9257932d87edf70ee505501d6c03eaebbf023ee339a0678c313771860c5f84b5699e82563ef18b1170d7d5403ad8c898aef03efa264b7d8ecf12b25bd71ed88d07a594d899344b494b2dde247d00ebc44ad2d65f129acaf6003b3c4ac96f5c7b62341e900eb7912be1c9a5bdf4994f03ba0958fbc62c45c35f5500eb60065135bd9a0558bf5da6d8c8971dc525c60d4d6bbf6b30c41562b0fa980412a919b500e231f1ce199498411b7e25bc20b76d50648fa01d6cc895f0e4d2defa65ba336a0192a2cb3bfd0648fb9301d9341ab513208f1ab513208f192a2cb3bfd064c1c580928324834597c4d0648fd242cf26e76f434df1af3eae3b90648faca6c4c9a0cc41966d40324898a4429a0c91f4cc430c9a191b4ccd4e491f4cc430c9a70dcba50b3c8fa6621864d386e5d2859e47d3310c32684b5a81a1f7923e9988619373b7a1a6f8d47d3310c3268388c7c7386648fa66218650289f2c6a0907d3310c326833d8fb27ea1923e9988619344b494b2dde247d3310c3268646d333539247d3310c971782880b9aad2550009c5715434, 0x415290a80960, 0x415290a80960, 0x21820240a121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_2_15 : (nb11_13_2.atMove 15).Valid :=
  SearchNode.check _ 3 [0x26d80034d34d06db0c38366db09b6106c349b41b6c30c00dbcc00020030d24800db0830100da0000800c30004036c30c0c030c369a0c249b6900000000020820da6830926da41a68209879a483c9a082c366b2090, 0x21821040a521, 0x1088210442121, 0x4a82104529e1, 0x4a82104529e1, 0x1088210442121, 0x1088210442121, 0x86600002200000008002000008008000028000433020000004080000000200000040860043000080000000200400000800040004000020010000080020000100020000100228ffb26, 0x29821044a521, 0x1088210442121, 0x4a82104529e1] (by decide) (by decide +kernel)

private theorem vb11_13_2 : nb11_13_2.Valid :=
  SearchNode.cover16 nb11_13_2 (by decide) rfl
    vb11_13_2_0 vb11_13_2_1 vb11_13_2_2 vb11_13_2_3 vb11_13_2_4 vb11_13_2_5 vb11_13_2_6 vb11_13_2_7 vb11_13_2_8 vb11_13_2_9 vb11_13_2_10 vb11_13_2_11 vb11_13_2_12 vb11_13_2_13 vb11_13_2_14 vb11_13_2_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_3 : (nb11_13.atMove 3).Valid :=
  SearchNode.check _ 4 [0x16db0004164d30d2600082c9a61349a08209b69840008261a08001008209a6980984db6106838d86136d841a0e36987930004164d40dc6186c3cde6120534900c469a7986d26d34936de69a10049b48141079859300001a68208201a4130db6c26d860049251a69a69a6020124d2049c24ce06db0001826800da00001009a69a69b0805836930dbc18013492000ce36f3c1b0000800da18241008209269b0900496db0006036e411e6030006dc6236c061c0dc9436d86030db718c9a00000300000001861b6000000036c36c3cc0004da000301bd204b2050, 0x80044002000040002800440020000400028000402020001008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26, 0x121821244a521, 0x1218212442521, 0x121821244a521, 0x80604002000800002002040000008000028060403280081000000200000000800040000440028000400000001000080004000280000020200000080800000102000000100029fbb26, 0x80044002000040002800440020000400028000402020001008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26, 0x1018210442521, 0x100014000402204008002100084002000088043a3, 0x2010a0240a121, 0x2010a064131a1, 0x2010a0a422121, 0x2011000440201008040101004100014008043a3, 0x1014210482521, 0x80012000480204008080102004100014008043a3, 0x814218482521, 0x1014210482521, 0x1014210482521, 0x1014210482521, 0x40600000040800000404000000401000e050702808001000000500008080001000400070281000040002000000802000002080000020200000080800000102000000100018fbf26, 0x21821240a521, 0x21820240a121, 0x121821244a521, 0x121821240a521, 0x21820240a121, 0x121821244a521, 0x1218212442521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_4 : (nb11_13.atMove 4).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_5 : (nb11_13.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_13_6 : SearchNode := nb11_13.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_0 : (nb11_13_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x24d269209009a4930804120824926d24804824920824134904120824906d249048008249269249000009a086000090, 0x420860108860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_1 : (nb11_13_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_2 : (nb11_13_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x69a69a08048009a4830804120020924924020024926d24804820186a2086018000000080480400602c826c000008208269249008240349041201a682492482400000010090080082482c924980180a2086000090, 0x420860108860, 0x100014000402204008002100084002000088043a3, 0x4040501002090082100084002410020400817a2, 0x4209605208e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_3 : (nb11_13_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x209a0924920806134004000000984d04d34d840201049041041209a000ce36f3c1b092000480400412080412493498480, 0x2010a0240a121, 0x2030a064131e1, 0x2050a0a4221a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_4 : (nb11_13_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x269a69a49208049a4934930c209a4926d249b4826db49a6936d30924920000104004120924906d2490480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_5 : (nb11_13_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_6 : (nb11_13_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x269a69a49208049a49b4940c209a69249249a61a4926d249b482cdb6db6de0c309a49208269a49209000000040041209a6824924824124800d2490080, 0x4211886808e0, 0xc211886808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_7 : (nb11_13_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_8 : (nb11_13_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_9 : (nb11_13_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_10 : (nb11_13_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x36e6cf6cd80004d24de51251e69000049a6db7926184304024000000900db6db6db6db01a6db61061a410, 0x4221204808e0, 0x8221084808e0, 0x8221084808e0, 0x8221084808e0, 0x4221044808e0, 0x8221084808e0, 0x8221084808e0, 0x8221084808e0, 0x8221084808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_11 : (nb11_13_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_12 : (nb11_13_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249a6da69000049269a49249b4920820924926d249048209a69a6920804000000000120824926d2480480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_13 : (nb11_13_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_14 : (nb11_13_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249a79ac9000049269b6db69a61841a49269a69208049249b49208209a69249249a414cd251669048048269a0800904000000000120020924924020024824d2480080, 0x424084280860, 0x424084280860, 0x424084280860, 0x424084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_6_15 : (nb11_13_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x269a4924920804d34934dc00009a69249248241b6d24d34d86024d349b6db0000b38f38db8c0002cdbce36db000092082092492090000000400612082682492482400000010498080, 0x421084280860, 0x421084280860, 0x8221084808e0, 0x8221084808e0] (by decide) (by decide +kernel)

private theorem vb11_13_6 : nb11_13_6.Valid :=
  SearchNode.cover16 nb11_13_6 (by decide) rfl
    vb11_13_6_0 vb11_13_6_1 vb11_13_6_2 vb11_13_6_3 vb11_13_6_4 vb11_13_6_5 vb11_13_6_6 vb11_13_6_7 vb11_13_6_8 vb11_13_6_9 vb11_13_6_10 vb11_13_6_11 vb11_13_6_12 vb11_13_6_13 vb11_13_6_14 vb11_13_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_7 : (nb11_13.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_8 : (nb11_13.atMove 8).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_9 : (nb11_13.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_10 : (nb11_13.atMove 10).Valid :=
  SearchNode.check _ 4 [0x269acb24924926920806db5966db0000b24924924924124924820800800000000004820b249249241240000001049208049249a6924924d20000db69a6d341841a4924d348208269208000009209a4924c30824820524926924926934904036da69b4d061049249b49249209249261040248249249b4920920812494d34d46db00009b6db69a4104126db6da6904104d349a69a69240001369a49249208001341341241001a69040001241369a49208049004a09a0820900000004000000000986d061b6800024920134134d30100924900db4db0020820db4930104db49241001a79e7124000034d36d24904024920434d26d048208249249049679b490000492480, 0x241084280860, 0x241084280860, 0x241084280860, 0x241084280860, 0x8420204408e0, 0x8420104808e0, 0xc411886808e0, 0xc411886808e0, 0x8420204808e0, 0x8420204808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_11 : (nb11_13.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_12 : (nb11_13.atMove 12).Valid :=
  SearchNode.check _ 4 [0x14914914924d36d30020926db6db79b0030926de6db6dc0000924924d260041249249349209061261361240001249041001a41b6d86d87000c249249049069004a492492012c136920000926904db4db0000c301800001b79e61b6000036c36c36d8002492048, 0x41000000101000000110000000410000040001000100100008000010020001000004000200010000800010000080040000280000010200000010800000102000000100069f6326, 0x41000000101000000110000000410000040001000100100080000010000041000004000200010000800010400000040000280000010200000010800000102000000100069f6326, 0x282208482121, 0x485290a80960, 0x481284280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_13 : (nb11_13.atMove 13).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_13_14 : SearchNode := nb11_13.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_0 : (nb11_13_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_1 : (nb11_13_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x24924925920804904d24924824124124920020924904934b20000920924924824924126920c2092498690, 0x84220010860, 0x84220000860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_2 : (nb11_13_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x26da6d80006180000000dbcf36e300001b61e6db600012490, 0x408c001023000408c00f3f307d4c1e7e60f3003cc1e60f30811bcc025f8002046001ed98001e652644, 0x420000000840000002100000004200000401008381d8008060263008080004000004000200008100cc002000130004000048000000820000008080000008200000010004aedca6, 0x4200000008400000021000000042000004010082008000808026300800008400000400020000810040002040130004000048000000820000008080000008200000010004aedca6] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_3 : (nb11_13_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x369a0c20924984d369348249a41249a68009368248259208049008249200040201008648240201248009048008249a00209249069a0824144c209449048249a41249268009368249a0c20924986db6db0036db090, 0x2080082010200408100104004010800408051a3, 0x2100082010200408100104004020800808051a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_4 : (nb11_13_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x699b6f37a36f60c00e36f36db6dccc36dbda36d80006f6ce36eb0000dbcdc6db60001b8f31036246dc0e36f36d86dccc0, 0x108821040a121, 0x1088210422121, 0x1088210442121, 0x484284280860, 0x481284280860, 0x484284280860, 0x485284280860, 0x485280280860, 0x4823886809e0, 0x1080a10482121, 0x4833886809e0, 0x4813886809e0, 0x487388e809e0, 0x4823886809e0, 0x487388e809e0, 0x1088210482121, 0x1088210482121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_5 : (nb11_13_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x24924925924920804d24924924924124934b2492000092492002492690692492482492410, 0x84204080860, 0x84200080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_6 : (nb11_13_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24db6d34900004f3adb6f3a000136db6dbce00005924d34db49000049249269300209249a4da60041249a69a6900800004000006900924820800d2010402400002012482682683080, 0x3d398007a73001e9ccd613306b9800f4e60f31e60f5e098003ea6000fa98007b66001ed98001e631464, 0x481284280860, 0x485284280860, 0x485290a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_7 : (nb11_13_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x249b493cd249840249259249208049249249c0020d36964924124124934934904826a6cb349a00009249200249269049208240041209349048249a412490480090480, 0x485284280860, 0x481284280860, 0x484284280860, 0x84210080860, 0x84200080860, 0x84210080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_8 : (nb11_13_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_9 : (nb11_13_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x34926924924d249208089a49249518209249249249a418092402080090d2496400582009249249241a410, 0x4402110002420090004800100900024000805a2, 0x1281282980960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_10 : (nb11_13_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_11 : (nb11_13_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x24925924924d24920804924924931820934964924b241249249249648009240208009049249a083012093496492402012492492480480, 0x84220040860, 0x281282180860, 0x281282180860, 0x84210080860, 0x281282180860, 0x84220080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_12 : (nb11_13_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_13 : (nb11_13_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_14 : (nb11_13_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_14_15 : (nb11_13_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

private theorem vb11_13_14 : nb11_13_14.Valid :=
  SearchNode.cover16 nb11_13_14 (by decide) rfl
    vb11_13_14_0 vb11_13_14_1 vb11_13_14_2 vb11_13_14_3 vb11_13_14_4 vb11_13_14_5 vb11_13_14_6 vb11_13_14_7 vb11_13_14_8 vb11_13_14_9 vb11_13_14_10 vb11_13_14_11 vb11_13_14_12 vb11_13_14_13 vb11_13_14_14 vb11_13_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_13_15 : (nb11_13.atMove 15).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private theorem vb11_13 : nb11_13.Valid :=
  SearchNode.cover16 nb11_13 (by decide) rfl
    vb11_13_0 vb11_13_1 vb11_13_2 vb11_13_3 vb11_13_4 vb11_13_5 vb11_13_6 vb11_13_7 vb11_13_8 vb11_13_9 vb11_13_10 vb11_13_11 vb11_13_12 vb11_13_13 vb11_13_14 vb11_13_15

private theorem tv_b11_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_13

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125149249200241209249a4824020124924904804814100004125920564936d049648249208209249044845149249241009209249249048248249241041249201241240001041249249049248144904925249249209069044249209040248129249268249a41120924a492492412092088490410080410252492490492481241492692c9200049209a4b2480092482692000c120920d059340009241a4020b0482482490c9a00249209209249249248201a4124924920906904924820824824124d248000348249249209209009b4924120d20836c36c00db6c241a49a49249840268249249241209209a6904184926834134900004904924924124920820124984824824814924924100100934934924804024d24924104124165934800034834924904104904820820924924100020024924900824004d24d209204a4920024924904920824134d20924904824b2412492090493482092082010002092410482c9a41a482080400482082400492d92092690248, 88003949168736, 88038308907104, 36834851718177, 36834985935905, 9080097802336, 9080097802336, 
    732180864850997610578894849654733641819303216546, 5753614230702594312420318140803585265730857379, 283958013200736, 5798215891240839019172621309036185704626923939, 281758989945184, 290555082967392, 
    45639702684961, 45639702684961, 22925253537946277599546221193286166653685990818]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_14_3 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_0 : (nb11_14_3.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_1 : (nb11_14_3.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_2 : (nb11_14_3.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_3 : (nb11_14_3.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920024924904926904824b24124920984934824004004004c2092600082c92600010010483482d82c0049adb2092490, 0x501204210860, 0x500a04210860, 0x501204210860, 0x501204210860, 0x504204210860, 0x3db3000f6cc001f53000f4e6003d3987980f3003cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x218048408421, 0x218050408421] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_4 : (nb11_14_3.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2492002492490492082412492092490482492412492098492481092082012492092410482492402482080492481082c0069269a04a248, 0x501204210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_5 : (nb11_14_3.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_6 : (nb11_14_3.atMove 6).Valid :=
  SearchNode.check _ 3 [0x249200249249049208241248209249048249a41a492080092480412002492490092082012482000080092412402482080492082682c004924b2089210480092492408, 0x501204210860, 0x501204210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_7 : (nb11_14_3.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_8 : (nb11_14_3.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2482092080490082492082492092492492412412492480482481492492082492010492410492402092482092481000410692482048002002692490248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_9 : (nb11_14_3.atMove 9).Valid :=
  SearchNode.check _ 3 [0x249a0820920904824b241201009248248248241248248009008248249208009049249200001209249248240201249249048068249a0820920904100004100020924824824824100800000900820c34db00341a090, 0x404010080402010100004000080022000805a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_10 : (nb11_14_3.atMove 10).Valid :=
  SearchNode.check _ 3 [0x402402c9208049249208249200008008249a40209248008248249249208249201049241069a4020924820924804024124920804104106924820000800924924092d2492410492408, 0x3db3000f6cc001f53000f4e6003d3987980f3003cc1e60f6cc001e61e679801e7e60079bcc01e64f404] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_11 : (nb11_14_3.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_12 : (nb11_14_3.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2492002492490492082412492092490482492412492098492482092082012492092410482492402482080492482082c00692600092490, 0x501204240860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_13 : (nb11_14_3.atMove 13).Valid :=
  SearchNode.check _ 3 [0x169b4da4124d305249249049348100049a4124d309249a4824024090904c341001204a49a4920926904db6f30024da052492490493480, 0x218208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_14 : (nb11_14_3.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_3_15 : (nb11_14_3.atMove 15).Valid :=
  SearchNode.check _ 3 [0x12526d06104924c100049a000492092482482402012412490400481480000412492052490c1049248249a0820924904b3418412492048, 0x298250442521, 0x298248442521] (by decide) (by decide +kernel)

private theorem vb11_14_3 : nb11_14_3.Valid :=
  SearchNode.cover16 nb11_14_3 (by decide) rfl
    vb11_14_3_0 vb11_14_3_1 vb11_14_3_2 vb11_14_3_3 vb11_14_3_4 vb11_14_3_5 vb11_14_3_6 vb11_14_3_7 vb11_14_3_8 vb11_14_3_9 vb11_14_3_10 vb11_14_3_11 vb11_14_3_12 vb11_14_3_13 vb11_14_3_14 vb11_14_3_15

private theorem tv_b11_14_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_14_3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125149249249218209249a49a49241249249249348144a5900c341259205249249049348045149249249241009249249249248249259249240000949241049249205249249049248104925249249269269045249249249040129120924a49249249249208a4924934920c0251241492492c924920000924b2492482082493c9a4920820d37934924000124900000920920924820804824820924924924924820124924924926904924d249a48000269b4924d26d209248208248241b6c36c36c30c249249209209041249a49249a49060249249249249209a6d249a49248449b49349000048249041a482682692492412492081492492593c100934934924924824d249249241041649349b480003492492490410492183cc38dbce3082082092592410002002492490049248, 88003949168736, 88038308907104, 88038308907104, 88038309103712, 9079628499040, 22858351036505046087704026701463228968681382819, 
    72645146576992, 495270008195552, 290554680707424, 281758587685216, 290554680707424, 354395210910048, 
    81924626655713, 81924626655713, 1984440489929837483293235241291086758375741837860202614833627185401425533326208190765865034442555685500416473033491816736567212240531016896023039557550153891441492212176648998]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_14_6 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_0 : (nb11_14_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x4d0410000010092492082492013492410412402692482482482092492082492012492410412402492482092483cc361bcdb6d84900020034d2490490, 0x500a04210860, 0x21b37307983cc007a73086ce36507987983cfcc21b28f303cc0f4e6007980f736501023000799e60f6a45] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_1 : (nb11_14_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x248049008001008009200009209a0920024020124024804020824300324100820120820b36db6d87986de79b79b09041061a69a480002013c9a6900004006da49208001001b492480, 0x501204210860, 0x501a02310860, 0x501204210860, 0x3db3000408c001f53009066600799e6003db301e612097980f307980798f307980f31e607981e612d44, 0x3db3000408c001f5304d5e6607981e6003db30f309ab9f30f3079800798f307980f31e607981e612d44, 0x40400000101000000084000000410000d6d820000004080001080040000020200004006b6c01000002002000040002000010d6d80020000200080000800100024000100008ff926, 0x3ccf3003ccf301e67a46de6607981e6003db31e60f5e0983cc1e600081e5087980f31e61e601e612d44, 0x3d398003d39801e9ccc6de6607981e6003db31e60f5e0983cc1e600086e0c87980f31e6f3001e612d44] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_2 : (nb11_14_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x20820834904100924920824920824924924824820924920824920824924820924824134134934d84800820d2492410003423c9a4d8490, 0x500a04210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_3 : (nb11_14_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x208040008001041041069248208208000200201001801a49a082c9a483c936f040000000009260209801a4900020826836db4d048260069249a08209001a492680002403c924d849a69a0db6db610, 0x501204210860, 0x500a02210860, 0x501204210860, 0x504210210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_4 : (nb11_14_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x24d34d34900004924924920820d34924d241042269249a4924824924924920820924924d2410412492492482083492490] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_5 : (nb11_14_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x24924924920c049449269200009a69269249a6124d249b4a06024b26b2492620612492490, 0x44721ce809e0, 0x485214a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_6 : (nb11_14_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24924924920820924924924924824924924920820924924924820824904134124924904000800d24d2410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_7 : (nb11_14_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x24924da4920c049249249208209a69b49a4b2632c928b6c924824db6db692a0001a49269862b4924920030c36db8e36020100da49a680, 0x4a5210a80960, 0x425210a80960, 0x4a5210a80960, 0x4a5210a80960, 0x4a5210a80960, 0x411204280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_8 : (nb11_14_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249a4934904104924944d34d34d20004d34934d24924104104100c0410412493412412410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_9 : (nb11_14_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2ce2c934a0a18c9ac934e34934b20004924b26d24a261c6dc71b7040c040049008000012472541251a0124b26124020024936d8095480, 0x840020108040201010004400102002080080da2, 0x4e7208e809e0, 0x421204280860, 0x446220e809e0, 0x484220280860, 0x4e7208e809e0, 0x4a5210a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_10 : (nb11_14_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x249a4934d04104924924d24934d00004924924d34104104d24900004d0412492410413410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_11 : (nb11_14_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x2c9bcebcebcdcac24b3c90cda4b34dbc98c184105a479a0030b24d2cf260003001349ec80, 0x501a02318860, 0x501a02308860, 0x501a02318860, 0x501204208860, 0x501204210860, 0x1040000008100000040400000041000000400800180c040001000200000100200010000020180c0c0604000080000100008001000004008000040040000100040000100048a5726, 0x501a02308860, 0x501a02310860, 0x880022000240021000201008100202400080fa2, 0x501a02308860, 0x501204220860, 0x501204240860, 0x501204280860, 0x3db3000408c001f53009066600799e6003db301e612097980f3079808118007b66001ed98001e612d44, 0x4a5210a80960, 0x4a5210a80960, 0x4a5210a80960, 0x3db3000408c001f5304d5e6607981e6003db30f309ab9f30f30798008118007b66001ed98001e612d44] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_12 : (nb11_14_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_13 : (nb11_14_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x26db6db79c00309b6db6db7000c26db6db79c00309b6db6de7000c3cdbaeb6e000049e6db79e6c000209a0034820800b47454d34000826db0db4d0000, 0x411204280860, 0x421204280860, 0x4232086809e0, 0x425210a80960, 0x4a5210a80960, 0x445204280860, 0x445204280860, 0x485204280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_14 : (nb11_14_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_6_15 : (nb11_14_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x249a4d34d26c301b6f269a68000249349349b0c06db6db6db0c30926d24d28030126db69b4c00034904004034924d04104104926920000904c2692400010000092480, 0x424210280860] (by decide) (by decide +kernel)

private theorem vb11_14_6 : nb11_14_6.Valid :=
  SearchNode.cover16 nb11_14_6 (by decide) rfl
    vb11_14_6_0 vb11_14_6_1 vb11_14_6_2 vb11_14_6_3 vb11_14_6_4 vb11_14_6_5 vb11_14_6_6 vb11_14_6_7 vb11_14_6_8 vb11_14_6_9 vb11_14_6_10 vb11_14_6_11 vb11_14_6_12 vb11_14_6_13 vb11_14_6_14 vb11_14_6_15

private theorem tv_b11_14_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_14_6

private def nb11_14_7 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_0 : (nb11_14_7.atMove 0).Valid :=
  SearchNode.check _ 3 [0x249200249249069a082412492092490482492412492098492481092082412092092410482492402082090482481083600c9249a04a248, 0x701a02310860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_1 : (nb11_14_7.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_2 : (nb11_14_7.atMove 2).Valid :=
  SearchNode.check _ 3 [0x24920824124920820920800924804120024924900920824120920000800924124020820904824818b6c004924b208a288, 0x701a02310860, 0x701a02310860, 0x704202310860, 0x4000212220000000100000000800000000000010020000000000000008800000000000200020000000000000800800000000000010020000000000000008800000004000272a1000000010000000040000000000004000080000010000000010000000000001001000000000000002004000000000004000080000010000000001000000000000202000119500000008000000400000000012000000000000002080004244000000200000008000000000800000010000000012000000000000000200000200000020000000100000000800000004000000001000000080000000200000004000000020000000020000000080000004000000001000000100000000020000000080000013487ffd6bfc7d72e] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_3 : (nb11_14_7.atMove 3).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_4 : (nb11_14_7.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_5 : (nb11_14_7.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_6 : (nb11_14_7.atMove 6).Valid :=
  SearchNode.check _ 3 [0x34f66924924920820f38b249380001a6924924820824904364134964d0410410492c920000904f279a600010032492480, 0x500a04210860, 0x501204210860, 0x501204210860, 0x500a04210860, 0x501204210860, 0x501204210860, 0x501204240860, 0x1c46204e809e0, 0x484204280860, 0x501204280860, 0x504204280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_7 : (nb11_14_7.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_8 : (nb11_14_7.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249249289208069a49249208209249249241241249249b48248149249249208209249249241041a69249248208169a49249208204b4d2492090410248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_9 : (nb11_14_7.atMove 9).Valid :=
  SearchNode.check _ 3 [0x249a4b24920d30926934d24904024924924920804924924960c209249249249a6124924924936824d44db49b0020a38f36db7830c2492082092090410000000412092482482482612482480090080, 0x421204280860, 0x421204280860, 0xc4120c6809e0, 0x84210080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_10 : (nb11_14_7.atMove 10).Valid :=
  SearchNode.check _ 3 [0x249249249208209a69249c68248249249249208209249249261841a6924924820816924924920820d2492492410408412402082490200080092412408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_11 : (nb11_14_7.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_12 : (nb11_14_7.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_13 : (nb11_14_7.atMove 13).Valid :=
  SearchNode.check _ 3 [0x145149249a49a49a4094924d349241004a650] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_14 : (nb11_14_7.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_7_15 : (nb11_14_7.atMove 15).Valid :=
  SearchNode.check _ 3 [0x125149249a49600009249a49a49241249249249040144a490000496592052690412496480, 0x1e6b640f31e61116b6416c80f31e607987980f30004bf62bb15c0003cc3cc0f31e60799e600f31e619824, 0x4a82904529e1, 0x4a82904529e1, 0x441204280860] (by decide) (by decide +kernel)

private theorem vb11_14_7 : nb11_14_7.Valid :=
  SearchNode.cover16 nb11_14_7 (by decide) rfl
    vb11_14_7_0 vb11_14_7_1 vb11_14_7_2 vb11_14_7_3 vb11_14_7_4 vb11_14_7_5 vb11_14_7_6 vb11_14_7_7 vb11_14_7_8 vb11_14_7_9 vb11_14_7_10 vb11_14_7_11 vb11_14_7_12 vb11_14_7_13 vb11_14_7_14 vb11_14_7_15

private theorem tv_b11_14_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_14_7

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x34da4936db6db71b0c04934928920820934e249009249049024a5924d249249269a0821924924924924835930131920c049249208209209249249248248029249349249249a6820864d34804c649241240bcdc6e399b1004db7b6cf3cde0134d26d36d249069349a4920820db71bcda6d061a69249a4924834decdb79b00089269a4b20000d44d34d65830120900824124920106804c34d240201248049248049a6db6db00009269a6db69b69a4180924924d3410432cd26b6d926834924934924900000800000820924924104124000120a30c06004924934904901924946924db6934904d25b36de6c001a69269ac8060349e69b59600049240a0800c001a0104927b3c020a66104026d001049009049a00249201811bcc200500201248048248041e01b1800180920820024820104d04c600341a6924804924834d00c00124104d309b4004124102dbd9b6c4c060124936924db0904904d35806c600061ac92698c026834de09b1800d0413483400492412408, 182699551980117837340611440749834229193342723491, 182699551982448538466540463099196666210047500707, 182699551980117837340611440749838662424225916323, 145419543841248, 182699551980117837343087320828405060112153585059, 182699551982448538469016343177767497128858362275, 
    154353084533216, 91522607424831215789295322887996872250614125986, 154078197975520, 145419544037856, 182710702395252398517299516541892379303066740131, 182710702395252398519775396620463210221877601699, 
    182710702397583099645704418969825647238582378915, 91522617634299148217239147694625392063429514658, 91522607445766636584605418961174153757219919266, 91522607445766636584605418961174153757219919266, 91522608126331370426501688774824178982389847458, 91522607445766636584895561157881664759149401506, 
    182733003225355042218518944632370882091092812707, 149817322375648, 149679883422176, 154352614902240, 149817456593376, 149679749204448, 
    149679749204448, 61857131127637483263755009076775401996465851725186789839515489699136229627862977748692393910118788487737424678568120878452245891749452156503334872552486461830498486422847270, 143426220198368, 143426622851552, 143426220198368, 143426622851552, 
    143289114692064, 143426622851552, 182777604885893286925271247800603482529988879267, 154352950446560, 156620359731680, 154352950446560, 
    145281702693344, 145281702693344, 145281971128800, 5280026789543376283667659932019425984407506103603905942303596721776440011921292092560552725314331830863924708895930913205534653805505777613732711935507532796483233667006948613984246313940111459652418517429078326951635450021502118448224767438226572386570312668674072008052527024990600323271998482772785352385089021010705782297417669946364477942006233696035070558451760202054246699, 147412283296224, 147412283296224, 
    145281836911072, 154352950446560, 145281836911072, 145281836911072, 154352950446560, 154215503104480, 
    182866808206969776337537914097783303132881888163, 182866808207136254990932577630710914086997599651, 183045214849122755164547126770713704888466154403, 183045214849122755164619662596591743744591799203, 183045214849289233817941790303641315842581865891, 145419544300000]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125148959c4d35531420534936d349348248201209208059b4d300301205249249048348045148a49249249241009249249249248108249241009205249249248248104925245128248009248241920924a48a25049001049248124149249289a492c9200009a6924b248208208249200009209a69248208248209249249249249248201249249249269041049248201a41a49249249069041249249a69249a4906024924924924920820924984026826924924920920814d351269a0000d249249241041249249b6c30824924934924904d24924924104134d249249041049208048249249208001001249248204a492092692080492492410002092492492482412492490490482092082010002092492482000412492490400082180cc38dbce30920c0cc36db6f3090248, 25696044544229575384828505936284314909561849250, 25696044544229575384828496491551278801527244194, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269516135775280303522, 48532007628023395881663588269518246845658697122, 290417514383840, 
    435553049250272, 36567889741920, 72851506333792]) (b := [0]) (by decide) ?_
  decide +kernel

private def nb11_14_10 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_0 : (nb11_14_10.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_1 : (nb11_14_10.atMove 1).Valid :=
  SearchNode.check _ 3 [0x24924d80134d049249249000059049b49260049241049000009040049269a00009a01b4100025924100000c001a418490, 0x1e709c83cc0000f3079f981e61e603cc7980f3213a09c83cfcc000007a54a0079f9801e7e6001ee9de64, 0x8c6220c609e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_2 : (nb11_14_10.atMove 2).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_3 : (nb11_14_10.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24924000004004924824d80004d049069a00249209809240048200201248008248000000009040009208201248200341040219241a6924800924820800c001a418490, 0xf409c87983cc0f30007980f31e607987980f32139f30079c2720000f31e6004012800f4e6001ef901a4] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_4 : (nb11_14_10.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_5 : (nb11_14_10.atMove 5).Valid :=
  SearchNode.check _ 3 [0x249251b51041049249a6dac8000249249359000049b692692410413da3ce36d800049269a49a0000904900024924d041b010402412410, 0x8822084809e0, 0x8842184809e0, 0x8842184809e0, 0x8842084809e0, 0x8842104809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_6 : (nb11_14_10.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24934d34d34db49000049249269a0820d3d934da61041a49249a6924804d040000041049249208209a00019341860200249249a682480, 0x1e601e61e601e6f301022c52607981e69a03b31e61e58e184d0346003db2c347be80b1e61e601ee24544, 0x8242084809e0, 0x825210c809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_7 : (nb11_14_10.atMove 7).Valid :=
  SearchNode.check _ 3 [0x24924e36d80004924924db59000049269a49208209b69249241061a6d249a492483da3cdb6d800049269a4a2000090000002492410090082412692000010402012402012480092480, 0x8422084809e0, 0x8c6218c809e0, 0x8c42184809e0, 0x8842084809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_8 : (nb11_14_10.atMove 8).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_9 : (nb11_14_10.atMove 9).Valid :=
  SearchNode.check _ 3 [0x249249349249a49000049249269a0820db792c9a4104104904000004d051b6d2418412410, 0x8042084809e0, 0x8042084809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_10 : (nb11_14_10.atMove 10).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_11 : (nb11_14_10.atMove 11).Valid :=
  SearchNode.check _ 3 [0x24924934d249a4900004924926920820db79249a61041a69249a6924834d04000004d04924920820920db6d241860201a69249a682480, 0x8442084809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_12 : (nb11_14_10.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_13 : (nb11_14_10.atMove 13).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_14 : (nb11_14_10.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_10_15 : (nb11_14_10.atMove 15).Valid :=
  SearchNode.check _ 3 [0x24934d34934db69000049349269a0820d27934e24104134904c00004904d2793418412410, 0x8c6220c609e0, 0x8c42084809e0] (by decide) (by decide +kernel)

private theorem vb11_14_10 : nb11_14_10.Valid :=
  SearchNode.cover16 nb11_14_10 (by decide) rfl
    vb11_14_10_0 vb11_14_10_1 vb11_14_10_2 vb11_14_10_3 vb11_14_10_4 vb11_14_10_5 vb11_14_10_6 vb11_14_10_7 vb11_14_10_8 vb11_14_10_9 vb11_14_10_10 vb11_14_10_11 vb11_14_10_12 vb11_14_10_13 vb11_14_10_14 vb11_14_10_15

private theorem tv_b11_14_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_14_10

private def nb11_14_11 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_0 : (nb11_14_11.atMove 0).Valid :=
  SearchNode.check _ 3 [0x249241208049049249208249209249249241241249249a48248149249208249209249241049241a492482092481448002002492490248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_1 : (nb11_14_11.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_2 : (nb11_14_11.atMove 2).Valid :=
  SearchNode.check _ 3 [0x24924920824920a249249248248149249208249209a49248209248041241249249040008009249240841261ac92490288, 0x500a04210860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_3 : (nb11_14_11.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920924920804824824924824120824804104d208208268200001a692490400082186c82692ce309241040049b4d2080010012493480, 0x501204210860, 0x501204210860, 0x501204240860, 0x501204240860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_4 : (nb11_14_11.atMove 4).Valid :=
  SearchNode.check _ 3 [0x249249249208049249249208209249249249241249249a49248149249249208209249249241041a49249248208144a248] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_5 : (nb11_14_11.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_6 : (nb11_14_11.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24924924920820a249249249248169249249208209a492492482082488412412492490200080092492408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_7 : (nb11_14_11.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_8 : (nb11_14_11.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24924934d24934d20c04d24924d24924104124930c04d04d24924d2412410] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_9 : (nb11_14_11.atMove 9).Valid :=
  SearchNode.check _ 3 [0x2cb24924924926920804d26db4d30c20924b24924a241469c7124946804124920808904d011c0c30d20924b2492402012482492480080, 0x84220020860, 0x84208080860, 0x84220080860, 0x84220080860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_10 : (nb11_14_11.atMove 10).Valid :=
  SearchNode.check _ 3 [0x2492492492496490000492492592410412492490000490492492410412410, 0x8822084809e0, 0x8422084809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_11 : (nb11_14_11.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_12 : (nb11_14_11.atMove 12).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_13 : (nb11_14_11.atMove 13).Valid :=
  SearchNode.check _ 3 [0x145148944a092412492c9001853349259a042492492496480, 0x211202180860, 0x211202180860, 0x211202180860, 0x4000002004000002040000020040000024000600010001000020001000020010000850002000040002008000020000400020080007000200018000800010002000040002001fbf27] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_14 : (nb11_14_11.atMove 14).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_14_11_15 : (nb11_14_11.atMove 15).Valid :=
  SearchNode.check _ 3 [0x1251489492496592000052492d16490402492412c92080492493000192052092490406480, 0x210a20108860, 0x210a20108860, 0x200108004804020200a0102004100414010083a3, 0x421204280860, 0x421204280860, 0x421204280860, 0x8222084809e0] (by decide) (by decide +kernel)

private theorem vb11_14_11 : nb11_14_11.Valid :=
  SearchNode.cover16 nb11_14_11 (by decide) rfl
    vb11_14_11_0 vb11_14_11_1 vb11_14_11_2 vb11_14_11_3 vb11_14_11_4 vb11_14_11_5 vb11_14_11_6 vb11_14_11_7 vb11_14_11_8 vb11_14_11_9 vb11_14_11_10 vb11_14_11_11 vb11_14_11_12 vb11_14_11_13 vb11_14_11_14 vb11_14_11_15

private theorem tv_b11_14_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_14_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x22892d3592596d96d9a4860124924a26820834da4934924904100100020104134da490c9049040b4d369b49a8db0000dc6d24da68301a8da49b6d860369b4d369200009a6da49a4906036db09b0920c069b4820000920da6da09840268049269b8d200009b79b6f36c000249349b72368208269249251341042399c79b7040c249249249249068240081a41809249241041241049249249049009259a49249a682082492c934a2a906924926924921924924b2482082492492c924920924027824800104904020824830db61bcd80c0412400c9209200ac9e08669259089a40008249a0926c20da4934124820000920820d34001034d240269001a08268371b00369b0c008240089a018092780192480012490248, 368231298514733347026056182693119085570651866530, 368231298520050259009195846184734313811773244834, 36834985935905, 11440325949328794423484043742211855044299467171, 11440325949332688660983225334358238429414695331, 36833912161313, 
    368231298514816403810605272530975465712095085986, 368231298520050259009505332375142916719127315874, 989336701756513946551633305859901898115939610101432257544833080886329657572483162615939414065826290204338389686058779831571048314798289717672398024251824231730676669569019686, 281552563472736, 281552563472736, 8304780986568768591145375763158153178624701317834816914121106810927450699452556803786760229645133733, 
    290554680707424, 368231298520050259009505332375147279597909329314, 284026334611936, 283751586728288, 284026464635232, 284026464635232, 
    281758989879648, 91522433200238746533710073470342660892449184035, 281758721902944, 281758587685216, 281758453467488, 281758721902944, 
    281758721902944, 281758453467488, 281758721902944, 281758990338400]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124949249249249249a6c30c249248248249a41a4114934944d600009249349b71b6c30c249249249241841249249249269049240041241009249341041a41049249249069004a6924104924d209269300009a0d209248208249a402690412483482692400492010092490448, 72645146576992]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a28e493496536492000492492c920820d24925924924324924b24924834964000804d04924920820920f24934324020324924b248248028a5924d3d93d924800124924b248208249249649249021001000201340a492490c9049020a2cb59651e490000492c924920820d36924d24924326924b2492486492c9a4b20000934d00834924d04900824124920f30904c24924326924800924804924d24b2682082c9249ac9ec9200009249259241041a99a4b64820824924964d24904820800000820924924104124000024860804004924964d049008a493c9bc926000925925924000124924934924905926b269248000229240219249340a49249309249020a2926b3cc2cb2608416518080550490c92002492010092402402002012480482482490006092500492082c12482092692582492412492480092482c9608609259849028a4d25924020134134924900904904d20001824930126b2680002c8349249609249039278218249640a208, 36834751054881, 36834784613537, 36834851718177, 36834985935905, 72020230478049, 290555082901856, 
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
    290555083360608]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124949249a49249a4924100924924926004136d26924904864924924920904924804101920924904100324136d2692480402492492490c900924924934d34db6c000249249a482482013718c0009060249b4da4124100124924924924924980104924924924824124d06d0490402412410400c904924924924324014936de6db79b1804924db49241009a69349c8004164d24924804036da4d26900905b259b6934000124824004925920820000848b2410012090493482002000012c90052492712cdace0010cda4b369a4c2416d96d1a4d00004926d00020dac9049a4830824b24024924904004100000924820824b2612410010400402d90c0049a0000924920004035920926d041349e48049348258341009209acb36000b44166d2090480404622d9a0908904b240041249209a0000826804166d209049348679a1800126904b24184124931920526924924125120924d2490002c9049249248241a41241041209ac1049249248249a4126d0610492486480, 11429175534213704434447147910865753620647249826, 1038097623321096073894050850658663711185768498961356785832629030709583160251095483018018375990351908, 177064863992288, 11440325949348265611135223702923903730371266466, 291930273522977, 290829554164001, 
    290829688381729, 290829688381729, 290829688185121, 290829688185121, 102784483166724243191840649282227841814600652706, 141983570069984, 
    36567889512544, 177064863992288, 141983570069984, 423595994122720, 141983570069984, 283132872106273, 
    283133106988321, 730775907091549633261815119149685599387806368675, 730775907099525072225074284489359783405341934499, 730775907099525031660255077186018935510839362467, 283132972769569, 290829688381729, 
    290829688381729, 72713870248416, 72645146576992, 72645146576992, 72851305007200, 72645146576992, 
    143082679437792, 290829554426145, 213382706235872, 143082679437792, 11507206662084149730893739539316263617015842722, 11507228440155632670956610125722439897783469986, 
    11507228440155632670956610116499067860928694178, 72645146576992, 72851305007200, 72645146576992, 72851305007200, 732180853993946377667833355031080832218314080675, 
    283751586728288, 283957745158496, 39625906227296, 39625906227296, 22880651856306457963897681911005703819691034018, 39625906227296, 
    39625906227296, 11774838382283606478691962704686952809786509218, 74844169832544]) (b := [0]) (by decide) ?_
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

private def nb11_15 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_15_0 : SearchNode := nb11_15.atMove 0

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_0 : (nb11_15_0.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_1 : (nb11_15_0.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_2 : (nb11_15_0.atMove 2).Valid :=
  SearchNode.check _ 3 [0x679e4366200004104d3cdb000482016400602c000130f30c0002c864c000601a590400000c1a49a0d64c4602c9bc126b0800092c824f37840006de610, 0x28820240a121, 0x28820840a121, 0x28820240a121, 0x1008202442121, 0x1008208442121, 0xf300003cde600f3007981e61e607987980f300000f303cc3cc0000798001e60000000003ea60f33505, 0x1e76c80f31e611176c816c800097e0f39f78000799023b64f6cc000f303cc0f31e60799e600f31e619824, 0x1e76c80f31e611176c816c800097e0f39f78000799023bdddeec000f303cc0f31e60799e600f31e619824, 0x1e9e80080799e7e60079f981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a73088eb65, 0x4c820241a1a1, 0x3e80080799e601e679f981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a73088eb65, 0x1e6b640f31e61116b6416c800097e0f362b80007984bf62bb15c0003cc3cc0f31e60799e600f31e619824, 0x10008400204010080500814000402020080807a2, 0x810860108860, 0x1e60000f31e60f33cc00f33cc079bdb30003cc097e0f307983cc1e60003cc0f31e60799e600f31e619824, 0x1e60000f31e60f33cc00f33cc097e0f30003cc097e0f307983cc1e60003cc0f31e60799e600f31e619824, 0x810860108860, 0x210860108860, 0x214060108860, 0x210860108860, 0xf300f31e60f30f3016c800097e0f3079800097e0f307983cc1e60003cc0f31e60799e600f31e619824, 0x2008080300014000500804000402020080807a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_3 : (nb11_15_0.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24920034124d209a4906d049348208240040040209a4906d3498482000c1b49adb2092490, 0x2080a0240a121, 0x100004000002404010002100084002000090081a3, 0x2080a0240a121, 0x208220840a121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_4 : (nb11_15_0.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2491492000092082091410c3269261a04a6dbc300824b2048, 0x208202442121, 0x808208442121, 0x808208442121, 0x2002208442121, 0x2002208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_5 : (nb11_15_0.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_6 : (nb11_15_0.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24120024820804124800824924120820924924900820000920000924824924c241060009ac9a082000c1a4924b209a69801a49a681cf3000000482082082492492408, 0xf300f31e60f30f3016c8003ea600025f8003cc04c0e60222c0003cc3cc7981e63cc1e607981e619824, 0x1e600f31e60f31e6016c8003ea60004458003cc04bff30222c0003cc3cc7981e63cc1e607981e619824, 0x2080a0240a121, 0x2082208422121, 0x20412084121a1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_7 : (nb11_15_0.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_8 : (nb11_15_0.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249148269201009a09108241269041204a4920926920906c3cdb6000b2048, 0xa109605208e0, 0xa109605208e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_9 : (nb11_15_0.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_10 : (nb11_15_0.atMove 10).Valid :=
  SearchNode.check _ 3 [0x2412492080490492492682412412cb249a0004b20986924820124130e26a0602882082412492080082410690402012480092482402080400402081cf36c30004b2090492482012408, 0xa109605208e0, 0xf300f31e60f30f300f30f4e60088b0000f4e7e60fa9f9803cde60003cfcc01e7e601e63cc01e619824, 0xa109605208e0, 0x8121204208e0, 0x4000000400200001040000010002000010400020000400020004004000004000200800002002000100008000020020000080004000004004000010040000100040000100408e2726, 0x8121204208e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_11 : (nb11_15_0.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_12 : (nb11_15_0.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249149269b0004d209148201b01008204a492092092690448] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_13 : (nb11_15_0.atMove 13).Valid :=
  SearchNode.check _ 3 [0x24924920000920c2092410c3369261a0926dbc306036f2090, 0x208202442121, 0x808208442121, 0x808208442121, 0x2002208442121, 0x2002208442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_14 : (nb11_15_0.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24924125120804904926a30004d20924b6482432412492002092490082003000092092493482492412698600492681488, 0x1ea4583cc3cc03cc1e60f324120007d4c0010231e616eaa581e61e60007d4c007a730007b66001e612ec4, 0x2de3883cc3cc03cc1e61aa93dc710f6cc00088b1e616f23d80f31e60007d4c007a730007b66001e612ec4, 0x8000a0402104008101000840140400220008a522] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_0_15 : (nb11_15_0.atMove 15).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

private theorem vb11_15_0 : nb11_15_0.Valid :=
  SearchNode.cover16 nb11_15_0 (by decide) rfl
    vb11_15_0_0 vb11_15_0_1 vb11_15_0_2 vb11_15_0_3 vb11_15_0_4 vb11_15_0_5 vb11_15_0_6 vb11_15_0_7 vb11_15_0_8 vb11_15_0_9 vb11_15_0_10 vb11_15_0_11 vb11_15_0_12 vb11_15_0_13 vb11_15_0_14 vb11_15_0_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_1 : (nb11_15.atMove 1).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_15_2 : SearchNode := nb11_15.atMove 2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_0 : (nb11_15_2.atMove 0).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_1 : (nb11_15_2.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_2 : (nb11_15_2.atMove 2).Valid :=
  SearchNode.check _ 3 [0x67638c3000ceb81e4366180034104d3cdb0004820104036000000130f36c0002c8654000609b590400000c1a49a1924006026dbc126b0600092c824f37840006de610, 0x21820240a121, 0x21820840a121, 0x21820240a121, 0x1088202442121, 0x1088208442121, 0x4000100900404010020100004000400110081a3, 0x4a82104529e1, 0x1e9db5d907983ea6000fa981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a7308ad165, 0x43820241a1e1, 0x3db5d907983cc1e60fa981e61e603cc7980f3003ccf300799e601e679faef95c01e679807a7308ad165, 0x4a82104529e1, 0x10010400404010080500814000402020080807a2, 0x810860108860, 0x810860108860, 0x210860108860, 0x214060108860, 0x210860108860, 0x1088210442121, 0x2010080500014000500804000402020080807a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_3 : (nb11_15_2.atMove 3).Valid :=
  SearchNode.check _ 3 [0x24db00041349c19c6001837b66136d04104db4c20004134004800900104d34d84c2000c1b49adb3092498, 0x100014020001400050002100044002400090083a3, 0x100014020002404010002100084002000090083a3, 0x100014020002400090002100084002000090083a3, 0x100014020020400810020100804002400090083a3, 0x21821040a521, 0x21821040a521, 0x21821040a521, 0x4b821040ade1, 0x109821040a521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_4 : (nb11_15_2.atMove 4).Valid :=
  SearchNode.check _ 3 [0x67580064d35906e30004136a219d6001436d641b6d8018cda88269a0820924904d301808208209a6820826d24030c060000208208200249249041000069260208208009248240a6dbc180824b209a683092492408, 0x218202442121, 0x8482084421a1, 0x4282084421e1, 0x29821044a521, 0x1088210442121, 0x29821044a521, 0x4a82104529e1, 0x1088210442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_5 : (nb11_15_2.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1ce300061b6c009c68208275241b6d88208db7014c3410410092049400413492c9204a6dbc180c36b6050, 0x8482084121a1, 0x218202412121, 0x8482084121a1, 0x1000140204024000900061000840041001100a3a3, 0x1088210412121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_6 : (nb11_15_2.atMove 6).Valid :=
  SearchNode.check _ 3 [0x26d80024020006e300041368209b6001437104036c00000da0800020924824900c300009a0000000824920c240000069a49a082000c1a49a4b209b6c001a69a0810c30000004820000824920d2408, 0x10000c020001400050001100044001400050081a3, 0x1001040200204008100201008040204008100a1a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_7 : (nb11_15_2.atMove 7).Valid :=
  SearchNode.check _ 3 [0x14db00041b4d019b60018371d0136d04104db4810004124004120500104934d8481000c1b49a4a6052250, 0x1001040200204008100201008040084002100a1a3, 0x1001040200204008100201008040084002100a1a3, 0x4a82104129e1, 0x1088210412121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_8 : (nb11_15_2.atMove 8).Valid :=
  SearchNode.check _ 3 [0x26c34d300069a01861800001041b0db6d8c0288261a4d20804904c36a20000a209869e48201241200041269841208a0000126920106c3cc36180b2098693482012408, 0xa109605208e0, 0xa109605208e0, 0x8121204208e0, 0x775366fb830dd4d8594003b9acbdcd66dd4d85940007735b1dc8ec0dedaca01dcd82cd653b9b059aca10c38c89aca077360b35cf9aca07736826b2803b9e83aca07736826b28077394daca00ee8361ae132f143a5f7f44b3150300735947735b1cd65ee6b28ee6b2f94e7adff89] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_9 : (nb11_15_2.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1cc36db0006c409869a08201241b0db0e00036014c349241009204900041349241004a002092892090000000402402050010493490480, 0x2010080480012000500014000402020100807a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_10 : (nb11_15_2.atMove 10).Valid :=
  SearchNode.check _ 3 [0x261a4900004906c34d30006a20986130000124330db8d8602682cc349a0004b20d86db6000db6230da48001a8800024924920000004106904020000820920804030c0000002081cc36c30004b2098692600012408, 0xa109605208e0, 0xa109605208e0, 0x8121204208e0, 0x8121204208e0, 0x1814320c209e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_11 : (nb11_15_2.atMove 11).Valid :=
  SearchNode.check _ 3 [0x14c34db0004d20000000824800130d34d0403481cc349a00049e05100041349241005001049249048200249ac92490250, 0x100014020002400090022100084020400810083a3, 0x2121204208e0, 0x8121204208e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_12 : (nb11_15_2.atMove 12).Valid :=
  SearchNode.check _ 3 [0x355d8c30006e3a124d369b0004da19b0db6e0c036c20120da08049048200001000008048088201a00b6da1800126d0488, 0x218208442121, 0x3ca7047238146f73597b9acbdcf41d650430e237b9acbdcd65ee6b29dd11eaca0077447ab2801dcddc359401dd4d8594001dd4d85cf9aca07736826b281dcda09aca00ee7a0eb280ee6ee1aca00ee853bb9309dc5cb4195cd653b9acdb9acaee6b45cd653b9acbdcd65f0487576a09, 0x80040002000040002800400020000400028000600020000800080001000200004000800040022000000028000400220000000240000020040000020200000100200000100029faf26] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_13 : (nb11_15_2.atMove 13).Valid :=
  SearchNode.check _ 3 [0x16dc8c30006dbc194d34930000db04940041341009004a99a0920926906db4db0024920536d3490493480, 0x298210442521, 0x1088210442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_14 : (nb11_15_2.atMove 14).Valid :=
  SearchNode.check _ 3 [0x24db6c3000ce38124924180006d84d369b0004da19b89b60060341b0e38c00038c24800020926d808200000000009a01068249b4126988000936c14c8, 0x214220140860, 0x1088210442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_2_15 : (nb11_15_2.atMove 15).Valid :=
  SearchNode.check _ 3 [0x14db68200049a6114d34920004d20530d24904034814000004124d205269041049348259a082092490250, 0x298210442521] (by decide) (by decide +kernel)

private theorem vb11_15_2 : nb11_15_2.Valid :=
  SearchNode.cover16 nb11_15_2 (by decide) rfl
    vb11_15_2_0 vb11_15_2_1 vb11_15_2_2 vb11_15_2_3 vb11_15_2_4 vb11_15_2_5 vb11_15_2_6 vb11_15_2_7 vb11_15_2_8 vb11_15_2_9 vb11_15_2_10 vb11_15_2_11 vb11_15_2_12 vb11_15_2_13 vb11_15_2_14 vb11_15_2_15

private def nb11_15_3 : SearchNode := nb11_15.atMove 3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_0 : (nb11_15_3.atMove 0).Valid :=
  SearchNode.check _ 3 [0x249200041349309a4906d049248208240001040309a4906d3490482692cf30006f36a2090, 0x40101005004040100a2102084086412190083a3, 0x1018202442121, 0x1018202442121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_1 : (nb11_15_3.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_2 : (nb11_15_3.atMove 2).Valid :=
  SearchNode.check _ 3 [0x24da08269a4904a300041b4930b66824824da612ad0c000da4820c209a0824900804000004030900824824020120000d04000820c30000006820187830186dec1b6f06030d2c82cf30006db69a090, 0x1018210442521, 0x1018210442521, 0x218202442121, 0x818208442121, 0xa1820a412121, 0x218202412121, 0x818208412121, 0x818208442121, 0x1018210442521, 0x1018210442521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_3 : (nb11_15_3.atMove 3).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_4 : (nb11_15_3.atMove 4).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_5 : (nb11_15_3.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_6 : (nb11_15_3.atMove 6).Valid :=
  SearchNode.check _ 3 [0x60de4c2590000c1b4004930000836db11b6000000f36f2610086c1b6f36db0000da4d000651a596098003403490c1b0007021341826000c00f26d0080, 0x100014000420400090020100804008400210083a3, 0x2010a0240a121, 0x2010a0240a121, 0x100014000402404010002100084002000090083a3, 0x2010a0240a121, 0x2010a064131a1, 0x2010a0a422121, 0x812208482121, 0x1014210482521, 0x2012208482121, 0x8010200420402010020100804100404010083a3, 0x200108004804020900a0102004100414010083a3, 0x80012000480404010080102004100014010083a3, 0x4142144835a1, 0x814218482521, 0x1014210482521] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_7 : (nb11_15_3.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_8 : (nb11_15_3.atMove 8).Valid :=
  SearchNode.check _ 3 [0x24004000800000986d36d2498482c3349a413000092c300828d340309b0004020800130906d06d2498480, 0x2014202442121, 0x2014202442121, 0x1014202482121, 0x1014202482121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_9 : (nb11_15_3.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_10 : (nb11_15_3.atMove 10).Valid :=
  SearchNode.check _ 3 [0x209a49269a08041b40009800008269249a4820000d3cd2418482c1b49a49a0000a00030e30d80c2c1b69a49a00008269249a6820000f3692698c020024820820900004020804130800824924020100000d2480080, 0x214202482121, 0x814208482121, 0x1014210482521, 0x1014210482521, 0x814208482121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_11 : (nb11_15_3.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_12 : (nb11_15_3.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249a0004e34d20d24124984d30000984926d34904824934da0806136d30934926d0493480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_13 : (nb11_15_3.atMove 13).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_14 : (nb11_15_3.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249a00049acd20db6c30e36eb61b6e08230db8c241249a08208041049840000008009248240200001201040068200000049a01209248209a69a43369080209b68249a08269a6904e308061b4d30926924824b26136d280009b680, 0x21820240a121, 0x1218212442521, 0x21820240a121] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_3_15 : (nb11_15_3.atMove 15).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

private theorem vb11_15_3 : nb11_15_3.Valid :=
  SearchNode.cover16 nb11_15_3 (by decide) rfl
    vb11_15_3_0 vb11_15_3_1 vb11_15_3_2 vb11_15_3_3 vb11_15_3_4 vb11_15_3_5 vb11_15_3_6 vb11_15_3_7 vb11_15_3_8 vb11_15_3_9 vb11_15_3_10 vb11_15_3_11 vb11_15_3_12 vb11_15_3_13 vb11_15_3_14 vb11_15_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_4 : (nb11_15.atMove 4).Valid :=
  SearchNode.check _ 4 [0x14924924a34d341009a4d369b600436496cd34b64836db6dc79b0c029659c6db6000124934304d34d20934000db6d34364927104b648105248a6934da69801048a4d36de4920c02524d00036db4d02414924924924100d669a6d64000124924d249048259a4934924000136d249249840271c4d44d210039b69349640001349249249040359669b49318041048041041201e60201040000049001248048105351b6db59000048a79349349200048a250618000590000241cdacb269200019a49b4924004334d289e4c04c27166d6492010d9b69649340001a492000cb2692c1a0004804921824004d089e4304c20100164920100494924304924930d66000d249a41a490c1049b48241040041049201a40001861040049001048048061818061800020018000009641bcf0c0249bc8359618049359059e6000d24d24110535180c35936d048a6100c049241048a0c30d64924d02567980c35934d0240, 0x46001181002040100200830040c06001180c123, 0x1088210442121, 0x1088210442121, 0x1e61c7a7984459e601e600f4e6000f4e6007a733b538f303cc0f522c079faf39e9e61116003d3983cfa45, 0x488218472121, 0x1088210442121, 0x1088210442121, 0x288202442121, 0x888208442121, 0x888208442121, 0x1088210442121, 0x288202412121, 0x888208412121, 0x888208412121, 0x1088210412121, 0x80000010200000040800000102000000100040400020089000400014000001000002000100200000900440004000080004008000100010000800040004000100004000100048b5726, 0x1e61a947983cc1e601e60799e600799e603ccf320bf8f303cc0f4e6007a04eaa51e60f3001e67983cfa45, 0x1e9cc1ed98001e60f3081183cd11600025f800079889a300222c0003cfcc79807987980799e601e690384, 0x888208442121, 0x1088210442121, 0x888208442121, 0x100404010020402010020100804008400210081a3, 0x2080a0240a121, 0x2080a0240a121, 0x100004010002404010002100084002000090081a3, 0x2080a0240a121, 0x2080a0a422121, 0x2080a0a422121, 0xc221846808e0, 0x4220846808e0, 0x2082208482121, 0x424084280860, 0x424084280860, 0x421084280860, 0x421084280860, 0x424084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x84c50020200000010008000100008000100004420280010010000040040000040100040040020020000020200400000200000280000020200000010800000102000000100029fe726, 0x8221084808e0, 0x1c24388e809e0, 0x4000420088004000080010000100010000100800000904000004400000004020001004000008010004040040000040000088000000420000004080000010200000010000ca5726, 0x284202482121, 0xc211886808e0, 0xc211886808e0, 0xc211886808e0, 0xc211886808e0, 0x8221084808e0, 0x1c24388e809e0, 0x1c24388e809e0, 0x425210a80960, 0x28820240a121, 0x28820240a121, 0x28820240a121, 0x288212442121, 0x28820a422121, 0x425210a80960, 0x425210a80960, 0x825290c809e0, 0x4020100802400090080802000900024000805a2, 0x880a0a482121, 0x1425290a80960, 0x1c22390e809e0, 0x424210280860, 0x424210280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_5 : (nb11_15.atMove 5).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_15_6 : SearchNode := nb11_15.atMove 6

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_0 : (nb11_15_6.atMove 0).Valid :=
  SearchNode.check _ 3 [0x20000030920920000836d24c34100006c209208200218249209040001808248208008309250261208211a492490400002c9248208208349249240ac000200826a20800860924d2408, 0xf307981e9cc007a7307981e61e607987980f30f300f33cc03cc0f3079800f4e60025f800097e1026865, 0x2040041100014000201800040402020080807a2, 0x1e61e58e18465e46000798f4e6000f4e6007a733cb0df303cc0f532e37a72cad63d2f497183d3984d1d45, 0xf307981e9cc007a7307981e61e607987980f30f300f33cc03cc0f307987981e61e679803cde61026865] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_1 : (nb11_15_6.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1000c1b6980920820824924824104186da4da6814004104924100494104134924d304a4004184936d3050, 0x1001040040204008100011000441004008100a1a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_2 : (nb11_15_6.atMove 2).Valid :=
  SearchNode.check _ 3 [0x20000024125180000000000820800000826184100000000120800020020024800000000c30820000800800004000000036c000100000000048210000001049a01800000209ac82c00000692692088, 0x2040081100014000402800080402020080807a2, 0x4040101100014000402800080804020100805a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_3 : (nb11_15_6.atMove 3).Valid :=
  SearchNode.check _ 3 [0x14000004124000820826924824100104104904010004124924000504104924904c1252c0000069b69a050, 0x2040081100014000402800000402020080807a2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_4 : (nb11_15_6.atMove 4).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_5 : (nb11_15_6.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_6 : (nb11_15_6.atMove 6).Valid :=
  SearchNode.check _ 3 [0x64de4d2590000c9a4d24920020934924db6186124b36b2690086cdb4b249a0000d24d0006512596090082402490c120104c24f41826124800b2690080, 0x20422084121a1, 0x2010a0240a121, 0x2010a0240a121, 0x100014000402404010002100084002000090083a3, 0x2010a0240a121, 0x2030a064131e1, 0x2050a0a4221a1, 0xc221846808e0, 0x4220846808e0, 0x20422084821a1, 0x424084280860, 0x424084280860, 0x424084280860, 0x421084280860, 0x421084280860, 0x421084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_7 : (nb11_15_6.atMove 7).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_8 : (nb11_15_6.atMove 8).Valid :=
  SearchNode.check _ 3 [0x269a49349b0020db69649a49a61a4926e2498482c9a4d249208049a6a269a4000b369e4924c201248a0000000820000838834924c2008, 0x8221084808e0, 0x1027308e809e0, 0x1024308880960, 0x8221084808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_9 : (nb11_15_6.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1cdb6db6dc00309b6db6db6d86c14db49249241004944a4004184d3610050, 0x424084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_10 : (nb11_15_6.atMove 10).Valid :=
  SearchNode.check _ 3 [0x249249249000069a4934a300209a69269a6004324926e2898482c9a49a49a0000db6db6db600023cda49aa80001cdb49a4b200009b6924d240002b8f38da480000002402002090000010082000000082090002408, 0xc211886808e0, 0xc211886808e0, 0xc211886808e0, 0x8221084808e0, 0x8221084808e0, 0x1824308c809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_11 : (nb11_15_6.atMove 11).Valid :=
  SearchNode.check _ 3 [0x14924db4920000924934d2490401cdb49a49e000051252000400490412050412492490480, 0x4221084808e0, 0x8221084808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_12 : (nb11_15_6.atMove 12).Valid :=
  SearchNode.check _ 3 [0x26d671b59218049acb34b20000db49c6d6400012c9a6dac9060249269b4f30020db7b679b6c60126a38e2c988024926da49208049a6dbc9241809249e69248200a19311c5920c0482000600682088, 0x58b48795790815f65760000002b3fb0159fd8015a0033fb000159fd959fd800159fdd67f615a084fec0000568213fb000015a02e7f60000567f8b3fb00002b4263fb000002b4263fb46a4f2af4c3fb00000000acfec00002b4109fd80159fd80acff167f6000acfec0159fd80ad0173fb023527962606c00000002b3fb000000164cd6c0159fd82b3fb002b3fb0acfec00acfec0567f90a78ca42b, 0x20100880404010100401010041002040100c3a3, 0x1425290a80960, 0x425210a80960, 0x825290c809e0, 0x10080400201400050080102004100084010091a3, 0x1425290a80960, 0x1425290a80960, 0x1c22390e809e0, 0x1425290a80960, 0x825290c809e0, 0x1021210880960, 0x1025210880960, 0x1425290a80960, 0x1021210880960, 0x1025210880960, 0x1024210880960, 0x80402000201400050080102004100404010081a3, 0x1021210880960, 0x1024210880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_13 : (nb11_15_6.atMove 13).Valid :=
  SearchNode.check _ 3 [0x1692cdb69b00009249249248201249b6da4d86014d34936da0000494d34d349241004a09209249208001040061a0000524906d3490400, 0x1025294a80960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_14 : (nb11_15_6.atMove 14).Valid :=
  SearchNode.check _ 3 [0x2492c9b49200009249c6924c201269a8da6906024924da49000049269b4db00219369b69362041a6a36e268000149acdb49200009379b6d240001240000200269048200060069a082010080432408, 0x4040101100404010080802000802020080805a2, 0x1425290a80960, 0x425210a80960, 0x424210280860, 0x1024210880960] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_6_15 : (nb11_15_6.atMove 15).Valid :=
  SearchNode.check _ 3 [0x149acdb69b00009249a69248201249b6da6d86014d34924930000534d249249040125249a000413492052090410492480, 0x1024210880960] (by decide) (by decide +kernel)

private theorem vb11_15_6 : nb11_15_6.Valid :=
  SearchNode.cover16 nb11_15_6 (by decide) rfl
    vb11_15_6_0 vb11_15_6_1 vb11_15_6_2 vb11_15_6_3 vb11_15_6_4 vb11_15_6_5 vb11_15_6_6 vb11_15_6_7 vb11_15_6_8 vb11_15_6_9 vb11_15_6_10 vb11_15_6_11 vb11_15_6_12 vb11_15_6_13 vb11_15_6_14 vb11_15_6_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_7 : (nb11_15.atMove 7).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_8 : (nb11_15.atMove 8).Valid :=
  SearchNode.check _ 4 [0x149229249249a4924100924924924924824936db4920c049049a4100d20904db60001341249249248048105248a48a2524934924904824136d8000410241cb249ac9b6b2c9240009249259260041b6d26b25904824964d24921900806820100da09049241001a41c8d66825804024964d24907900514d349249241009249249249848239e6934924000124936db4d34930c041049249241201861040000001249049249048105248a69e59349318048a2506184100000002424db41b41a00209b6d06d2498482410480410412092000cb2692c230920004004804120936d06d24904804d34824100930db71860301b6030d30d24804836dc61b1807183986d86000964030c20804000036de61b0c07984104004924920800100124904806184100800004104005924921986d04000d041105248a69b4130804d048a25249049249048661b410000410240, 0x240860108860, 0x240860108860, 0x1e60079f9801e7e6003cc0222c00088b3cc0f3079bcc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0xa409605208e0, 0x8408604208e0, 0xa409605208e0, 0xa409605208e0, 0x20460f379800f307983cc0222cf307981e60f3097e16c87980799e601e63cc0079bcc007a73001ea5c384, 0x2080a0240a121, 0x2080a0a422121, 0x2080a0a422121, 0x204202482121, 0x8410884808e0, 0x8410884808e0, 0xc411886808e0, 0xc411886808e0, 0x2421204208e0, 0x2421204208e0, 0x8421204108e0, 0x8421204208e0, 0x1004202482121, 0x4421084808e0, 0x8421044808e0, 0x8421084808e0, 0x4421084808e0, 0x8421084808e0, 0x8421084808e0, 0x8421084808e0, 0x8421204808e0, 0x8421204808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_9 : (nb11_15.atMove 9).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_15_10 : SearchNode := nb11_15.atMove 10

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_0 : (nb11_15_10.atMove 0).Valid :=
  SearchNode.check _ 3 [0x269a4820004920924d040000341269a09800268249241208049049a8824180b209249048201261248a0000134d2010cdb88200008209a690482012408, 0x240860108860, 0xa409605208e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_1 : (nb11_15_10.atMove 1).Valid :=
  SearchNode.check _ 3 [0x1cdb69e00069209a6924820024134da6d84026814924924100d304944a002092492090000000412402050010493490480, 0x8421204408e0, 0x8421204408e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_2 : (nb11_15_10.atMove 2).Valid :=
  SearchNode.check _ 3 [0x249241000241869a4c300049a09249861000241269b0d0002681c926c30004b201b6104000036236db0c0003cc00020024924984000800920824034c2080000002002402c92498cdb682000682088, 0x240860108860, 0x1e600f379803cde6007980222c00088b3cc0f30f33cc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0xa409605208e0, 0xa409605208e0, 0xa409605208e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_3 : (nb11_15_10.atMove 3).Valid :=
  SearchNode.check _ 3 [0x149208000049a09a6920820024124924104024812500104d24904c10004134924920500104d249048200249ac92498cdb680000682050, 0x2100084002014000500814000402020080807a2, 0x100014020002400090002100084002000090083a3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_4 : (nb11_15_10.atMove 4).Valid :=
  SearchNode.check _ 3 [0x66db5964d000069a4da49a0000924da4d340001269b69ac9860249249249208049ac9a49a6300924924926c201b6e269b6d880248a0db09a00000009a693482482008, 0x214202482121, 0x8410884808e0, 0x8410908809e0, 0x441084280860, 0x441084280860, 0x441084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_5 : (nb11_15_10.atMove 5).Valid :=
  SearchNode.check _ 3 [0x1cdb69b69200009a69249a4820134da6da4986014924924d341004944a0db09e000000050, 0x841082180860, 0x8421104808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_6 : (nb11_15_10.atMove 6).Valid :=
  SearchNode.check _ 3 [0x24924d249000069a49a49a00009249349240041269a692698001c9249a49a00009249b4da69a6800000024d24920900db082000000000083492082408, 0xc411886808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_7 : (nb11_15_10.atMove 7).Valid :=
  SearchNode.check _ 3 [0x149249249a00009a69249a482012492492498401251452000412400412050010492490480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_8 : (nb11_15_10.atMove 8).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_9 : (nb11_15_10.atMove 9).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_10 : (nb11_15_10.atMove 10).Valid :=
  SearchNode.check _ 3 [0x64924d651a596490000492492c930020924da5924004124b2692490c804024100006904824920800d21124f4410c020124b2692483c80, 0x2421204208e0, 0x2421204208e0, 0x8421204108e0, 0x8421204208e0, 0x1084202482121, 0x4421084808e0, 0x8421084808e0, 0x4421084808e0, 0x8421084808e0, 0x8421084808e0, 0x8421084808e0, 0x8421204808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_11 : (nb11_15_10.atMove 11).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_12 : (nb11_15_10.atMove 12).Valid :=
  SearchNode.check _ 3 [0x249259248b01a79b4d20d04826db000082088, 0x214208482121, 0x8442204809e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_13 : (nb11_15_10.atMove 13).Valid :=
  SearchNode.check _ 3 [0x14914494d34d679b00004a09a492092090000000002402050010490490480, 0x441084280860, 0x4421084808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_14 : (nb11_15_10.atMove 14).Valid :=
  SearchNode.check _ 3 [0x249149249a4d249000049a69369240041249b6d26906004024d00006904826db00009a09a893610402408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_10_15 : (nb11_15_10.atMove 15).Valid :=
  SearchNode.check _ 3 [0x14912514924934920000524924d249040209a4920920804824930000920524924d0402480] (by decide) (by decide +kernel)

private theorem vb11_15_10 : nb11_15_10.Valid :=
  SearchNode.cover16 nb11_15_10 (by decide) rfl
    vb11_15_10_0 vb11_15_10_1 vb11_15_10_2 vb11_15_10_3 vb11_15_10_4 vb11_15_10_5 vb11_15_10_6 vb11_15_10_7 vb11_15_10_8 vb11_15_10_9 vb11_15_10_10 vb11_15_10_11 vb11_15_10_12 vb11_15_10_13 vb11_15_10_14 vb11_15_10_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_11 : (nb11_15.atMove 11).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_12 : (nb11_15.atMove 12).Valid :=
  SearchNode.check _ 4 [0x14912924924924924924100924926d241841249249249348349249b4d24904924904100d209b69a61841341249249248048105248a48a4924934906102524924904904826da6986104d024129249249249840249249249241009249249249b4824936d35930c04925934924000124004004924d20986180824d340249201049348105248a48a6965934900002526d861a0934d024249b4184924d20d249241b41300209a4926d349848201ac1b49a00009249a00041b4d20924926d049348029b6db6c00db6c24db4834100920824926d04804836db6db1986d84db41841249200001000001041a4926d04934834924980124904db41841249209105248a48a490410080410252492490493482240, 0x4200000004800000041000000041000866502020000400028000010000004000280004332a000000028000010020000040004000020010000080020000100020000100229fbf26, 0x282208482121, 0x481084280860, 0x481084280860, 0x481084280860, 0x4831886808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_13 : (nb11_15.atMove 13).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private def nb11_15_14 : SearchNode := nb11_15.atMove 14

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_0 : (nb11_15_14.atMove 0).Valid :=
  SearchNode.check _ 3 [0x24924d241241a08009049208201008209049048200240a4935100126d0488] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_1 : (nb11_15_14.atMove 1).Valid :=
  SearchNode.check _ 3 [0x14d144949a49341001004a6da492092890692410002512052490490493480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_2 : (nb11_15_14.atMove 2).Valid :=
  SearchNode.check _ 3 [0x14db6db6006db61261a4d80024984d449360040341b6db6c00c36c26980020924800000800000820d441068249a41a4924c00924824da0c2092498488] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_3 : (nb11_15_14.atMove 3).Valid :=
  SearchNode.check _ 3 [0x12db6c36c36e36136d04104924810804920004800526124904004c14a200041240005269041049348249a082092498650] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_4 : (nb11_15_14.atMove 4).Valid :=
  SearchNode.check _ 3 [0x24924db6db6e36db6c24d24e24920804daca369200009b49369248200a4db0c341269a088, 0x481084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_5 : (nb11_15_14.atMove 5).Valid :=
  SearchNode.check _ 3 [0x14d144949a49349201004a003000000000050] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_6 : (nb11_15_14.atMove 6).Valid :=
  SearchNode.check _ 3 [0x14d34924d34000124d24924980004d449249241841aa9b69a4800024b2c9a49a0000920000024926904c30c041269a01041008249a408, 0x481084280860, 0x485084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_7 : (nb11_15_14.atMove 7).Valid :=
  SearchNode.check _ 3 [0x12914924924920000526924934d84014a6c9b49a0000524900004004d2052690412493480, 0x481084280860, 0x484084280860] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_8 : (nb11_15_14.atMove 8).Valid :=
  SearchNode.check _ 3 [0x249249249249269a0c208a4934d20920d04db4d30c209a088] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_9 : (nb11_15_14.atMove 9).Valid :=
  SearchNode.check _ 3 [0x14d14494d44d349200004a01a4920926906926db0024da052493490490480] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_10 : (nb11_15_14.atMove 10).Valid :=
  SearchNode.check _ 3 [0x14924924d24924900004924936920c20d349249241841a4924da6924824d04000006904db4d30c209a0d3492410402408] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_11 : (nb11_15_14.atMove 11).Valid :=
  SearchNode.check _ 3 [0x129145149249349200005269649249040241209a0920804924c60000d2052692490403480, 0xa809605208e0, 0xc811886808e0] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_12 : (nb11_15_14.atMove 12).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_13 : (nb11_15_14.atMove 13).Valid :=
  SearchNode.check _ 3 [0x3] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_14 : (nb11_15_14.atMove 14).Valid :=
  SearchNode.check _ 3 [0x2] (by decide) (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_14_15 : (nb11_15_14.atMove 15).Valid :=
  SearchNode.check _ 3 [0x1] (by decide) (by decide +kernel)

private theorem vb11_15_14 : nb11_15_14.Valid :=
  SearchNode.cover16 nb11_15_14 (by decide) rfl
    vb11_15_14_0 vb11_15_14_1 vb11_15_14_2 vb11_15_14_3 vb11_15_14_4 vb11_15_14_5 vb11_15_14_6 vb11_15_14_7 vb11_15_14_8 vb11_15_14_9 vb11_15_14_10 vb11_15_14_11 vb11_15_14_12 vb11_15_14_13 vb11_15_14_14 vb11_15_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem vb11_15_15 : (nb11_15.atMove 15).Valid :=
  SearchNode.check _ 4 [0x1] (by decide) (by decide +kernel)

private theorem vb11_15 : nb11_15.Valid :=
  SearchNode.cover16 nb11_15 (by decide) rfl
    vb11_15_0 vb11_15_1 vb11_15_2 vb11_15_3 vb11_15_4 vb11_15_5 vb11_15_6 vb11_15_7 vb11_15_8 vb11_15_9 vb11_15_10 vb11_15_11 vb11_15_12 vb11_15_13 vb11_15_14 vb11_15_15

private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_15

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
    (q' : State) (hq' : q' ≠ 3)
    (hM10 : M 1 0 = some (some q', Stmt.write 1 Dir.left)) : False := by
  let m : Move := ⟨q', 1, true⟩
  have hm_cmd : M 1 0 = m.command := hM10
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
    exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    exact tv_b7 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · exact tv_b11 M hG hm1 rfl hv (by simp)
  · exact absurd rfl hq'

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := by
  intro M hFirst second hRun _hUsed hForm hMissing hLoop hHalts
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
  obtain ⟨q', hM10⟩ := second
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
    have hM10' : (reindex23 M) 1 0 = some (some 2, Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    exact solve_branch (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01)
      2 (by decide) hM10'
  · exact solve_branch M hG hm0 hv q' h3 hM10

end OMA.BB4H1

-- Adaptation by @ubuwaits.
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := OMA.BB4H1.h1_proof
