import OMAReductions.R_BusyBeaver_BB_3_R1

/-!
# The three-state Busy Beaver upper bound

The search branches only on the first unassigned transition seen in the first
21 steps. Nonhalting leaves use finite-automata reduction: a DFA summarizes
one half of the tape and an NFA recognizes a superset of configurations that
can reach an unassigned transition. The NFA excludes the entirely blank tape.
See Blanchard et al., *Determination of the fifth Busy Beaver value*, for the
finite-automata reduction method. Every certificate is checked by Lean.
-/

namespace BeaverBound

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev Key (n : ℕ) := Fin n × Symbol
abbrev MachineOf (n : ℕ) [NeZero n] := Machine Symbol (Fin n)

structure Move (n : ℕ) where
  state : Fin n
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Position (n : ℕ) where
  state : Fin n
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def start (n : ℕ) [NeZero n] : Position n := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  if a = 0 ∧ xs = [] then [] else a :: xs

def Position.move (c : Position n) (m : Move n) : Position n :=
  if m.left then ⟨m.state, c.ls.tail, c.ls.headI, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, c.rs.headI, c.rs.tail⟩

def Move.flip (m : Move n) : Move n := { m with left := !m.left }

def Position.flip (c : Position n) : Position n := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position n) (m : Move n) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with
  | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
  · exact (ListBlank.cons_mk a xs).symm

def Position.view [NeZero n] (c : Position n) : Cfg Symbol (Fin n) :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start (n : ℕ) [NeZero n] : (start n).view = Machine.init [] := rfl

def Move.command (m : Move n) : Option (Option (Fin n) × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def ongoing [NeZero n] (M : MachineOf n) (k : Key n) : Option (Move n) :=
  match M k.1 k.2 with
  | some (some q, ⟨b, .left⟩) => some ⟨q, b, true⟩
  | some (some q, ⟨b, .right⟩) => some ⟨q, b, false⟩
  | _ => none

theorem ongoing_command [NeZero n] (M : MachineOf n) (k : Key n) (m : Move n)
    (h : ongoing M k = some m) : M k.1 k.2 = m.command := by
  rcases m with ⟨q, a, d⟩
  unfold ongoing at h
  split at h <;> simp_all [Move.command, Move.mk.injEq]

theorem step_move [NeZero n] (M : MachineOf n) (c : Position n) (m : Move n)
    (h : ongoing M (c.state, c.head) = some m) :
    M.step c.view = some (c.move m).view := by
  have he := ongoing_command M (c.state, c.head) m h
  change M c.state c.head = m.command at he
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push]

theorem step_stop [NeZero n] (M : MachineOf n) (c : Position n)
    (h : ongoing M (c.state, c.head) = none) : M.HaltsAfter c.view 1 := by
  unfold ongoing at h
  split at h
  all_goals try contradiction
  cases hc : M c.state c.head with
  | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
  | some pair =>
    obtain ⟨q, b, d⟩ := pair
    cases q with
    | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
    | some q => cases d <;> simp_all

theorem multi_succ_front [NeZero n] (M : MachineOf n) (c : Cfg Symbol (Fin n)) (k : ℕ) :
    M.multiStep c (k+1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

abbrev Program (n : ℕ) := List (Key n × Move n)

def Program.get : Program n → Key n → Option (Move n)
  | [], _ => none
  | (a, m) :: rest, k => if k = a then some m else Program.get rest k

def Program.flip (tb : Program n) : Program n := tb.map fun (k, m) => (k, m.flip)

theorem get_flip (tb : Program n) (k : Key n) : tb.flip.get k = (tb.get k).map Move.flip := by
  induction tb with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', m⟩ := x
    by_cases h : k = k' <;> simp [Program.flip, Program.get, h] at ih ⊢
    exact ih

inductive CanStop (tb : Program n) : Position n → Prop
  | missing {c} : tb.get (c.state, c.head) = none → CanStop tb c
  | move {c m} : tb.get (c.state, c.head) = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Program n} {c : Position n} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get (c.state, c.head) = some m.flip
      simp [get_flip, h]
    · rwa [← flip_move]

def Matches [NeZero n] (M : MachineOf n) (tb : Program n) : Prop :=
  ∀ k m, tb.get k = some m → ongoing M k = some m

theorem matches_empty [NeZero n] (M : MachineOf n) : Matches M [] := by
  intro k m h
  contradiction

theorem matches_add [NeZero n] {M : MachineOf n} {tb : Program n} {k : Key n} {m : Move n}
    (hm : Matches M tb) (h : ongoing M k = some m) : Matches M ((k, m) :: tb) := by
  intro k' m' hh
  by_cases e : k' = k
  · subst k'
    simp [Program.get] at hh
    simpa [← hh] using h
  · apply hm k' m'
    simpa [Program.get, e] using hh

theorem cannot_stop_run [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (c : Position n) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get (c.state, c.head) with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move M c m (hm _ _ h), Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

end BeaverBound


namespace BeaverBound

open Turing Turing.BusyBeaver

-- A DFA reads a left half-tape from the far end toward the head. Its initial
-- state is fixed by the blank symbol, so appending blank cells changes nothing.
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
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact D.blank.symm
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

-- Each NFA state records a control state and a left DFA state. The extra state
-- is accepting. The NFA reads the other half of the tape, starting at the head.
structure Certificate (n : ℕ) where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate n) := Option (Fin n × Fin cert.dfa.size)

def nodeId (cert : Certificate n) : Node cert → ℕ
  | none => n * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edge (cert : Certificate n) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  match p with
  | none => q.isNone
  | some _ => cert.edges.testBit ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1) + nodeId cert q)

def Certificate.onBlank (cert : Certificate n) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (n val : ℕ) : Certificate n :=
  let extra := val / 2 % 8
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 16 / dfaBase
  let width := n * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 16 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate n) : List (Node cert) :=
  none :: (List.finRange n).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate n} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩
  · simp [nodes]
  · simp [nodes]

def checkBlank (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all (fun p => if cert.onBlank p then
      (nodes cert).all fun q => !cert.edge p 0 q || cert.onBlank q
    else true)

def checkAt (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  match tb.get (q, a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state, l')) a' s then
            (nodes cert).all fun t => !cert.edge s m.write t || cert.edge p a t
          else true
        else true
    else cert.edge p a (some (m.state, cert.dfa.next m.write l))

def checkMachine (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate n) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate n} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate n} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, rfl, .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank [NeZero n] {cert : Certificate n} (hb : checkBlank cert = true) :
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
      have he0 : cert.edge p 0 q = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Program n} {cert : Certificate n} (hchk : checkMachine tb cert = true)
    {c : Position n} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    rw [checkAt, hh] at h
    exact Reads.push h (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    rw [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      simp only [TapeDFA.read_pop, if_true] at h'
      have h'' := allNodes h' s
      simp only [he, if_true] at h''
      have h''' := allNodes h'' t
      simp [hf] at h'''
      exact Reads.push h''' ht

def checkCertificate [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  let C := unpack n val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound [NeZero n] {tb : Program n} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb (start n) := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, start, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [start, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

def firstMissing (tb : Program n) : ℕ → Position n → Option (Key n)
  | 0, _ => none
  | fuel + 1, c =>
    match tb.get (c.state, c.head) with
    | none => some (c.state, c.head)
    | some m => firstMissing tb fuel (c.move m)

theorem firstMissing_stops [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (fuel : ℕ) (c : Position n) {k : Key n}
    (h : firstMissing tb fuel c = some k) (halt : ongoing M k = none) : M.HaltsAfter c.view fuel := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases ht : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, ht] at h
      subst k
      exact Machine.multiStep_eq_none_mono (step_stop M c halt) (by omega)
    | some m =>
      have htail : firstMissing tb fuel (c.move m) = some k := by
        simpa [firstMissing, ht] using h
      unfold Machine.HaltsAfter
      rw [multi_succ_front, step_move M c m (hm _ _ ht), Option.bind_some]
      exact ih _ htail

def holes (tb : Program n) : Finset (Key n) :=
  Finset.univ.filter fun k => tb.get k = none

theorem missing_is_hole {tb : Program n} {c : Position n} {k : Key n} {fuel : ℕ}
    (h : firstMissing tb fuel c = some k) : k ∈ holes tb := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases he : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, he] at h
      subst k
      simp [holes, he]
    | some m =>
      exact ih (by simpa [firstMissing, he] using h)

theorem holes_add (tb : Program n) (k : Key n) (m : Move n) :
    holes ((k, m) :: tb) = (holes tb).erase k := by
  ext k'
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [Program.get]
  by_cases e : k' = k <;> simp [e]

theorem no_holes_cannot_stop {tb : Program n} (h : (holes tb).card = 0) {c : Position n} :
    ¬ CanStop tb c := by
  intro hs
  induction hs with
  | @missing c hm =>
    have he : (c.state, c.head) ∈ holes tb := by simp [holes, hm]
    have := Finset.card_pos.mpr ⟨_, he⟩
    omega
  | move _ _ ih => exact ih

def moves (n : ℕ) : List (Move n) := (List.finRange n).flatMap fun q =>
  (List.finRange 2).flatMap fun a => [⟨q, a, false⟩, ⟨q, a, true⟩]

theorem mem_moves (m : Move n) : m ∈ moves n := by
  obtain ⟨q, a, d⟩ := m
  rw [moves, List.mem_flatMap]
  refine ⟨q, by simp, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, by simp, ?_⟩
  cases d <;> simp

def checkTree [NeZero n] (limit : ℕ) : ℕ → Program n → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | fuel + 1, tb, certs =>
    match firstMissing tb limit (start n) with
    | none => match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | some k => (moves n).foldlM (fun rest m => checkTree limit fuel ((k, m) :: tb) rest) certs

theorem succeeds_each {α β : Type*} {items : List α} {f : β → α → Option β}
    {a b : β} (h : items.foldlM f a = some b) {i : α} (hi : i ∈ items) :
    ∃ x y, f x i = some y := by
  induction items generalizing a with
  | nil => simp at hi
  | cons head tail ih =>
    rw [List.foldlM_cons] at h
    cases hh : f a head with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hi with rfl | ht
      · exact ⟨_, _, hh⟩
      · exact ih h ht

def Upper [NeZero n] (M : MachineOf n) (limit : ℕ) : Prop :=
  M.HaltsAfter (Machine.init []) limit ∨ ¬ M.IsHalting

theorem upper_cannot_stop [NeZero n] {M : MachineOf n} {tb : Program n} {limit : ℕ}
    (hm : Matches M tb) (h : ¬ CanStop tb (start n)) : Upper M limit := by
  right
  intro halts
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  apply cannot_stop_run hm (start n) h (k + 1)
  rwa [view_start]

abbrev TreeBound [NeZero n] (limit : ℕ) (tb : Program n) : Prop :=
  ∀ M : MachineOf n, Matches M tb → Upper M limit

theorem branch_bound [NeZero n] {limit : ℕ} {tb : Program n} {k : Key n}
    (h : firstMissing tb limit (start n) = some k)
    (children : ∀ m, TreeBound limit ((k, m) :: tb)) : TreeBound limit tb := by
  intro M hm
  cases hs : ongoing M k with
  | none =>
    left
    simpa only [view_start] using firstMissing_stops hm limit (start n) h hs
  | some m => exact children m M (matches_add hm hs)

theorem subtree_bound [NeZero n] {limit fuel : ℕ} {tb : Program n} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkTree limit fuel tb a = some b) :
    TreeBound limit tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    rw [checkTree.eq_def] at h
    cases hFirst : firstMissing tb limit (start n) with
    | none =>
      simp only [hFirst] at h
      intro M hm
      cases a with
      | nil => contradiction
      | cons v rest =>
        by_cases hc : checkCertificate tb v = true
        · exact upper_cannot_stop hm (certificate_sound hc)
        · simp [hc] at h
    | some k =>
      simp only [hFirst] at h
      apply branch_bound hFirst
      intro m
      obtain ⟨x, y, hy⟩ := succeeds_each h (mem_moves m)
      refine ih ?_ hy
      rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
      omega

end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

section Symmetry

variable {n : ℕ} [NeZero n]

def orient (mirror : Bool) (d : Dir) : Dir :=
  if mirror then match d with
  | .left => .right
  | .right => .left
  else d

def orientTape (mirror : Bool) (t : Tape Symbol) : Tape Symbol :=
  if mirror then ⟨t.head, t.right, t.left⟩ else t

def orientCfg (e : Fin n ≃ Fin n) (mirror : Bool) (c : Cfg Symbol (Fin n)) : Cfg Symbol (Fin n) :=
  ⟨c.q.map e, orientTape mirror c.tape⟩

def reindex (M : MachineOf n) (e : Fin n ≃ Fin n) (mirror : Bool) : MachineOf n :=
  fun q a => (M (e.symm q) a).map fun (s, b) => (s.map e, ⟨b.symbol, orient mirror b.dir⟩)

theorem reindex_step (M : MachineOf n) (e : Fin n ≃ Fin n) (mirror : Bool)
    (c : Cfg Symbol (Fin n)) : (reindex M e mirror).step (orientCfg e mirror c) =
      (M.step c).map (orientCfg e mirror) := by
  obtain ⟨q, ⟨a, l, r⟩⟩ := c
  cases q with
  | none => rfl
  | some p =>
    cases mirror <;>
      simp only [Machine.step, orientCfg, orientTape, Bool.false_eq_true, if_false, if_true,
        Option.map_some, reindex, Equiv.symm_apply_apply]
    all_goals
      cases h : M p a with
      | none => rfl
      | some entry =>
        rcases entry with ⟨p', b, d⟩
        cases d <;> rfl

theorem reindex_init (e : Fin n ≃ Fin n) (h0 : e 0 = 0) (mirror : Bool) :
    orientCfg e mirror (Machine.init []) = Machine.init [] := by
  cases mirror <;> simpa [orientCfg, orientTape, Machine.init, Tape.mk₁, Tape.mk₂, Tape.mk']
    using h0

theorem reindex_multi (M : MachineOf n) (e : Fin n ≃ Fin n) (mirror : Bool)
    (c : Cfg Symbol (Fin n)) (k : ℕ) :
    (reindex M e mirror).multiStep (orientCfg e mirror c) k =
      (M.multiStep c k).map (orientCfg e mirror) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases he : M.multiStep c k with
    | none => rfl
    | some c' => exact reindex_step M e mirror c'

theorem reindex_haltsAfter (M : MachineOf n) (e : Fin n ≃ Fin n) (h0 : e 0 = 0)
    (mirror : Bool) (k : ℕ) : (reindex M e mirror).HaltsAfter (Machine.init []) k ↔
      M.HaltsAfter (Machine.init []) k := by
  unfold Machine.HaltsAfter
  conv_lhs => rw [← reindex_init e h0 mirror, reindex_multi]
  exact Option.map_eq_none_iff

theorem upper_of_reindex {M : MachineOf n} (e : Fin n ≃ Fin n) (h0 : e 0 = 0)
    (mirror : Bool) {limit : ℕ} (h : Upper (reindex M e mirror) limit) : Upper M limit := by
  rcases h with h | h
  · exact Or.inl ((reindex_haltsAfter M e h0 mirror limit).mp h)
  · right
    intro hs
    obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hs
    exact h ((Machine.isHalting_iff_exists_haltsAt _).mpr
      ⟨k, (reindex_haltsAfter M e h0 mirror k).mpr hk⟩)

omit [NeZero n] in
theorem orient_command (m : Move n) (e : Fin n ≃ Fin n) :
    m.command.map (fun (q, b) => (q.map e, ⟨b.symbol, orient m.left b.dir⟩)) =
      (Move.mk (e m.state) m.write false).command := by
  rcases m with ⟨q, b, d⟩
  cases d <;> rfl

theorem first_reindex {M : MachineOf n} (e : Fin n ≃ Fin n) (h0 : e 0 = 0) (m : Move n)
    (h : ongoing M (0, 0) = some m) :
    ongoing (reindex M e m.left) (0, 0) = some ⟨e m.state, m.write, false⟩ := by
  have he : e.symm 0 = (0 : Fin n) := e.symm_apply_eq.mpr h0.symm
  have hcmd := ongoing_command M (0, 0) m h
  change M 0 0 = m.command at hcmd
  have hr : reindex M e m.left 0 0 = (Move.mk (e m.state) m.write false).command := by
    unfold reindex
    rw [he, hcmd, orient_command]
  simp [ongoing, hr, Move.command]

end Symmetry

theorem canonical_start {n : ℕ} (hn : 1 < n) [NeZero n] {limit : ℕ} (hl : 1 ≤ limit)
    (same : ∀ a, TreeBound (n := n) limit [((0, 0), ⟨0, a, false⟩)])
    (other : ∀ a, TreeBound (n := n) limit [((0, 0), ⟨1, a, false⟩)]) :
    TreeBound (n := n) limit [] := by
  intro M _
  cases h : ongoing M (0, 0) with
  | none =>
    left
    rw [← view_start n]
    exact Machine.multiStep_eq_none_mono (step_stop M (start n) h) (by omega)
  | some m =>
    by_cases hs : m.state = 0
    · apply upper_of_reindex (Equiv.refl (Fin n)) rfl m.left
      apply same m.write
      apply matches_add (matches_empty _)
      simpa [hs] using first_reindex (Equiv.refl (Fin n)) rfl m h
    · let e := Equiv.swap m.state (1 : Fin n)
      have h1 : (0 : Fin n) ≠ 1 := by
        intro he
        have hval := congrArg Fin.val he
        change 0 = 1 % n at hval
        rw [Nat.mod_eq_of_lt hn] at hval
        omega
      have h0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hs) h1
      have he : e m.state = 1 := Equiv.swap_apply_left _ _
      apply upper_of_reindex e h0 m.left
      apply other m.write
      apply matches_add (matches_empty _)
      simpa [he] using first_reindex e h0 m h

end BeaverBound

namespace BeaverBound

-- Each integer packs one DFA, an NFA edge set, and its states reachable on blank input.
-- They follow the enumeration order of `moves` within each checked subtree.

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound0 : TreeBound (n := 3) 21 [((0, 0), ⟨0, 0, false⟩)] := by
  refine subtree_bound (fuel := 5) (b := []) (a := List.flatten [
    [2290647312]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound2 : TreeBound (n := 3) 21 [((0, 0), ⟨0, 1, false⟩)] := by
  refine subtree_bound (fuel := 5) (b := []) (a := List.flatten [
    [2290647312]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_0 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_1 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [159704012627178225784091378386]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_2 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_0 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012046070326013221470930]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_1 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282848273]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_2 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012055294265398076179410]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_3 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282848273]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_4 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281799697]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_5 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283897105]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_6 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283999792, 2283938352, 2283999792, 2283938352, 2283938352, 2283938352, 2283938352, 2283938352, 404963888, 159695549625865372387489416914, 404963888, 673333808],
    [673333808, 673333808, 673333808, 673333808, 3050680171447260652985726214423479955031365085804317754492676, 3053839722287363361602897585282638441664996641959855193033316, 3050697627545928250880797138877184920351970549054258958272260, 3053839722287363361602897585282638441664996641959855193033316, 3053839722287363276929755659611678701146566325498107600013924, 3050860551133492522597953663223605947787070200094719071455940, 3053653526920307254404740393435843253237768957088922679610052, 3053653526920307254404740393435843253237768957088922679610052],
    [404963888, 404963888, 673333808, 673333808, 673333808, 673333808, 673333808, 3050680171447260652985726214346470181067500149663360419858180, 3053839722287363276929755659611678701146566325498107600013924, 3053653526920307254404740393435843253237768957088922679610052, 3053653526920307254404740393435843253237768957088922679610052]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_7 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283897105]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_8 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485340580985765381026155218, 159703955516031622350299531986, 158504684574691220165232757714, 159703955516031622350299531986, 158543372562102129733645961938, 159703936776445486471682525938, 2185564784, 2185564784, 2185503344, 2185503344, 2185503344, 3050860551133492523756725887911399053310083377520570729715396],
    [6247881234161990097237510898, 303136785, 14895868032962298724213722925458677432849742225741416521508, 303136785, 34701329, 571572241, 571572241, 303136785, 1110540561, 154751949788890356886012115, 1110540561, 158775500486567587144125188818],
    [159703936776445486471682525938, 159085004385854863691430828754, 159703936776445486471682525938]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_9 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485341023700814974056202962, 2168553745, 158504685017406269758262805202, 2168553745, 2151776273, 2185331249, 158620748975097665830317523666, 158620748975025040853917827794, 158620748975170290806717219794, 158620748975025040853917827794, 158620748975025040991365169874, 159703941344464539276651070419],
    [159703946066831022284817434067, 159703955511563988301150161107, 2185331249, 158775500929289444913154427602, 2218886225, 159085004828585799028458984146, 2218886225]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_10 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485340728568795538701488850, 2269450864, 158466034366221248922889818770, 2269450864, 3053653524079148749976080743356061908917308212314373924727812, 2219057776, 158466034509183515494071734994, 2219057776, 159085004533437892199738053330, 3055143109744870393947697063814042181976210286003047097053028, 158466034513795202612077859538, 158504684722274250322908091346],
    [2235896432, 2235896432, 2219057776, 158466034509183515494071734994, 2219057776, 3055143109744870393947697063814042181976210286003047097053028, 158543372709685159891321295570, 158466072292727066668818305746, 2185564784, 158543377284477688109638685330, 2185564784, 2185503344],
    [2185503344, 2185503344, 2495451045645141610984444626, 4990826233648808773636133842, 33652753, 570523665, 570523665, 1111589425, 33652753, 1111589425, 158775500634150617301800524498, 2553445247829643006442541778],
    [3053653524077069854995521669952512700416178443489035628194820, 5029476442127855384887628498, 3053653524077069854995521669952512700416178443489035628194820, 67207185, 606175505, 606175505, 1145144401, 1145144401, 67207185, 1145144401, 159085004533437893849106158290, 67207185],
    [606175505, 20427267097470966395471729362, 606175505, 1145144401, 1145144401, 67207185, 1145144401]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_3_11 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2151743505, 2151747601, 2151743505, 2151747601, 2151743505, 2168529169, 2168529169, 158485341023707621500687289042, 2151759889, 158485341023716699618475578066, 2151759889, 2168553745],
    [2151743505, 2168525073, 2151743505, 2168525073, 2151743505, 159085042307902051980327522515, 159085042307902052117774864595, 158504685017413076284893891538, 158504685017422154402682180562, 2168553745, 2151776273, 2185331249],
    [2495449860585818121020915923, 4990823867997864566529753555, 10058876731448176006091834066, 9981571882821957457547428819, 19963001508641025519872180946, 19963067912470143239582778835, 154751954255326492311487186, 2185331249, 2785535688493554851114975954, 272728081, 5261566882792334577559995346, 272728081],
    [4292625, 557941009, 557941009, 4292625, 1078034449, 4292625, 1078034449, 2218886225, 3095039587780831398420611794, 5571070782079611124865631186, 4292625, 641828465],
    [641828465, 4292625, 1145144401, 4292625, 1145144401, 2218886225]
  ]) (by decide) ?_
  decide +kernel

theorem bound4_3 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (1, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_3_0
  · exact bound4_3_1
  · exact bound4_3_2
  · exact bound4_3_3
  · exact bound4_3_4
  · exact bound4_3_5
  · exact bound4_3_6
  · exact bound4_3_7
  · exact bound4_3_8
  · exact bound4_3_9
  · exact bound4_3_10
  · exact bound4_3_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_4 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_5 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [159704012622854787750107874003]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_6 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_7 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [159704012623143035718445696211]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_8 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2172945008, 159703955955321737203272452818, 2172945008, 159703937665339522273186482898, 159703955955294715605508229842, 159703938855155077977405983698, 159703937065819776927672634066, 159703941234786189385844984530, 159703936475523966568966982354, 159703945994048412202722987730, 3713973005624580752996895442, 287342609],
    [6190005380514976798806707154, 287342609, 18907153, 555778065, 555778065, 555778065, 18907153, 1092714769, 1092714769, 159703955512572857836478991058, 159703937066972698433353222898, 2235830896],
    [2235830896, 2219057776, 2219057776, 3055143109744870393945113044898275107605770863286671532751716, 159703937066972698433353222898, 2189722224, 159703937065855805724691598034, 2189722224, 3713973005660046600062438098, 159696702400404049428224215762, 6190005380549879695918828498, 159694417374510057068435671762],
    [303071249, 159694569680053064601302010834, 303071249, 302022673, 304119825, 302022673, 304119825, 302022673, 306348593, 306348593, 11142070130329545887631608530, 159694265659298888691293948626],
    [21046199629888878271057170130, 159694265659298888691293948626, 40854458629007543037908290258, 39771251649323373637511808211, 1528316348414892512998655757759130083550712739943293937383428, 1528316347704602717255836939511838435421052844983710234310660, 1176797808, 1145340528, 1176797808, 1145340528, 1145340528, 1145340528],
    [1145340528, 1145340528, 79387750758094771692633195731, 2223276656, 159703937067008727230372186866, 2223276656, 159703937067008727230372186866]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_9 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [158485341023734591971261481682, 158485341020275880250105151699, 158504685017440046755468083922, 159742623304825734934271427314, 2165604625, 2165575953, 2165575953, 2164523281, 2165575953, 2165575953, 8958981238197476326177311459650582757774936292054758434283186835648059974856032567611673620261429556119, 158504684445556075649097073362],
    [3050697627529280836437818341828927773679386267588896812271493, 3053676798866273260618420510516936884203303227905978818533220, 2165604625, 2165604625, 2166654289, 158495013017092578828009636307, 5981623143433830939434399677984267768645028962894905719013, 23856668179054075492061040271873456372226058572569417201893, 3050694718196161159420863503080851207770698652064827901065445, 556041553, 17072401, 556041553],
    [38687988563903640921735635, 1095008529, 1095008529, 2166654289, 160322925685554108087712942834, 2168750353, 158485377326908916866400453330, 158466034513795060775010763474, 158504720140022755365604099026, 159085004533437891787396027090, 3050697627545928253359196942881244284563626915295265019495653, 159085004533437891924843369170],
    [3050697627545928253359196942881357091957288309608350933157093, 3050697627545928253359196942881507501815503501767119111567589, 2168750353, 158543373004850938731695243986, 158543373001392244602725010131, 310542896, 3713973005660046616168513747, 310542896, 26835839488300807337387739821800008747893408452382855642181, 6190004799441975526465503699, 6190004808665910512736829907, 3714124711648405889229029779],
    [321161073, 26812567553433089599985534414923663508030319675784564422885, 321161073, 4952064750932660264221311443, 289702161, 289702161, 578847280, 11142070130329545903737735891, 578847280, 21046199629888878287163362515, 1115849264, 41976368],
    [1115849264, 1529805933370324362550148102619764485567804507535465817552357, 572555824, 33587760, 572555824, 33587760, 1111654960, 33587760, 1111654960, 33587760, 158620748976214063739551485139, 158775500929316466510918650578],
    [158775500925857702013204433107, 159085004828603813426968466130, 159085004825144978560510333139]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2256802416, 2223260272, 2256802416, 2249462384, 3053653524079148751297805313372474709249493474381092719832068, 2249462384, 2214855280, 2216960624, 158466034216323438925423121106, 2216960624, 3053653524789438544725343222521133569106038278788715618642948, 158466034806619249284128772818],
    [3053653524079148749974788732512002587267006733596985914174468, 2223252080, 158504683837424884884342637299, 2223252080, 8937519721047441111971469767762683617669072291103255702532, 2495375778912002547126502611, 26812564756667685664598110361647171917663440230908156587012, 4971406973210214925571589331, 50645958803416650955381406986689559728533564889996737784836, 19344584037329416377860307, 39635843693961648976106375379, 79252342803885968535834874067],
    [2223260272, 158504683839154320740859265267, 2223260272, 9846900276336116950148240501331878857130117043231548705533727530623256423716594224680430843978036118, 1149518448, 28488331583649437303561323983938858658879263065636955106980, 4971406974939703560282063059, 195135768378416116076839798094529310940389706175228257644388, 1149518448, 1149518448, 1149518448, 75760240]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485416578139674352271037074, 6703141183623034106236804573401788395184386084808455758308, 4911852627085829982982802, 6004914966423947491604479631023558303322416986378669547172, 9747555905544346681807506, 9981572178996813231684653714, 9982176641906620546272006802, 79852044387687036165094970066, 158485417758731295069684437650, 2165576304, 2165576304, 2147746416],
    [2183406192, 2147746416, 2183406192, 158465997027687386326967063250, 158465997027687386326967063250, 2165580400, 2219057776, 2165580400, 2147754608, 2183406192, 2147754608, 2183406192],
    [2219057776, 158465997027687386464414405330, 2219057776, 158465997027687386464414405330, 3050685990146816524957035741105552240037675442821619309476677, 2165580400, 2219057776, 2165580400, 2147754608, 2183406192, 2147754608, 2183406192],
    [2219057776, 2219057776, 8937519682205500062692281747914145115459207741252656049156, 2514719772617457331333104851, 4990750966915669709778191571, 2495451337352295025658106514, 159080206901951373208849552082, 2514946446785201638511547282, 9981576901363296513613173394, 158456401179030224554701165266, 19963068209797920929536349906, 40238000908333808271088489106],
    [3053653524084697215598282447022820993802056430741563221355956, 3055143109744870396591147469271473556869211477811479234621284, 3053676798866273260616966998471390246091270498546184472120772, 3053653524079148073912669908004195146242993267863691595754932, 3050685990146816522353472506177019747911097295210500449690533, 3053653524079148073912672431460468394169290773666312462675812, 3055143109744870393945113045822392688941124263332657622822756, 3053653524079148073912672431460468394169290773666312462675812, 2495451337352295025691660946, 14621038115866370298155666, 2495603633671367571749802642, 9747555905544896437621394],
    [9981576901363296513646727826, 9982186086639586697879294610, 79852044387687036165094970066, 3053653524084697215598282447022820993802056430741530606448052, 3053653524079148073912669908004195146242993267863691595754932, 3053653524123541225919820016393724369953905202612443582180788, 3050685990146816522352826501371067691545800928382299783908261, 3053653524079148073912672431460468394169290773666312462675812, 3053653524079148073912672431460468394169290773666312462675812]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2182382192, 158620743685565862469043224819, 2182382192, 3053653524079150783453214052931180090758955840472215494470660, 2216985200, 2147779184, 2216985200, 8937519721049515603948648703874471186427708029829922040836, 26812564756669760156575289297773060397182061004316365171716, 606372464, 295536, 606372464],
    [295536, 1078231664, 295536, 1078231664, 295536, 2151973488, 158620743964437261619044616947, 2151973488, 3050720902477331076633197446979553959497762221606235925484357]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485415997031770183354618514, 159085079801900869558976189074, 158504759990737224967563318162, 158485415997031770183354618514, 158543447978148134639059931794, 158466072004479237006831981266, 158620814509389909678650103506, 159085079801900869009220375186, 8937519682202795814222030629832515730812891305469258116100, 26812564734470473330785098339685802925671854852607958739140, 34701329, 571572241],
    [571572241, 154751958867579857664999635, 1108705905, 1108705905, 158485415997032333133308039826, 158466109782258741271968420498, 158485417177623953850721440402, 158466074364510119749566403218, 158543447978148697589013353106, 158543447978148697589147570834, 158543452700515180458666955410, 158466072003326878314873819794],
    [159085042033345863093229523666, 3053653524079150783453214052931180090758955840472215494470660, 158543448005819941661194654354, 158466071995255304081742303954, 158543452728188676330653553298, 572818032, 295536, 572818032, 295536, 1145340528, 295536, 1145340528],
    [295536, 289702512, 159080206459202495491424195282, 289702512, 574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528, 4489840],
    [5981640212585498775733989137177765717007814094657655022004, 11928334078434182738169146862625978366252259656396696331972, 574915184, 295536, 574915184, 295536, 1145340528, 295536, 1145340528, 295536, 289702512, 289702512],
    [574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528, 4489840, 570720880, 295536, 570720880, 295536],
    [1145340528, 295536, 1145340528, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [377782896, 5570900777065241520885465331, 377782896, 3053653524120775462334439288950172144301665225462974566509572, 3053653524077069856317248763425198748674591171376970424265732, 3053653524120780881431026662020312097588409885301707904003076, 3053653524076376213938593666922402782834346021927087435033604, 3053653524786710037110519972444903836539136328760239806360580, 3053653524076373504398052045451691086244680955156669423038356, 4578989245775683749876456372929704170396626396564694831607652, 3053653524076373504398049521995417838318453489302055756377956, 3053653524077069854994229659108453378765876964771647617641476],
    [3053653524076373504398049521995417838318453489302055756377956, 612663920, 20426634596104519066130121459, 612663920, 605258545, 605258545, 606372464, 295536, 606372464, 295536, 4489840, 295536],
    [4489840, 295536, 1082425968, 8684144, 1082425968, 8684144]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_10_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293868144, 3095040764949288688940028562, 293868144, 2553483318468658965935886994, 2476031786936037480968819410, 2630849849710434005526058706, 2495375780641492265177518802, 360989296, 2476031786936035419384517330, 360989296, 277086832, 50645958138172289331884133953976609518745399023436710161412],
    [1149518448, 50645958138172289331884133953976609532193088277878676532228, 1149510256, 3095039583492839557606424787, 1149510256, 3095039583781070071205594323, 1149518448, 1149518448, 1149518448, 1149518448, 293868144, 2476221861034049280625676946],
    [293868144, 2553634434196110794582725266, 2553639156562593664236327570, 360989296, 2553673393719594469357064850, 360989296, 277086832, 3053653524076376213938593666922402782834346021927087435033604, 3053653524120812718553062887806151880744552504466398593821700, 3053653524076373504398052045451691086244680955156669423038356, 4580478831796550630410757798047428647346881850614839273192292, 3053653524076373504398049521995417838318453489302055756377956],
    [3053653524076373504398049521995417838318453489302055756377956, 9923544339139029641445053074, 68190225, 9942888332845047375605076882, 68190225, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048],
    [537166448, 3053653524076373504398052045454097641681051734411073320529812, 9924148802048836956032406162, 9924149982641020623397130898, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448],
    [605258545, 605258545, 572818032, 295536, 572818032, 295536, 4489840, 295536, 4489840, 295536, 1149534832, 8684144],
    [1149534832, 8684144]
  ]) (by decide) ?_
  decide +kernel

theorem bound4_10 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_10_0
  · exact bound4_10_1
  · exact bound4_10_2
  · exact bound4_10_3
  · exact bound4_10_4
  · exact bound4_10_5
  · exact bound4_10_6
  · exact bound4_10_7
  · exact bound4_10_8
  · exact bound4_10_9
  · exact bound4_10_10
  · exact bound4_10_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485341023734576612326310610, 158485341023734572179917963986, 158485341023734581044734657490, 2147749905, 2148798481, 2148798481, 2148798481, 2147749905, 2216957009, 2216957009, 158485340580985765380925491922, 2151944209],
    [158485340728568795538634379986, 2151944209, 158485341023734589909551350482, 159085080384161694286474645715, 293741104, 293741104, 3241364592738876689668717491911948658807399956551759338900068, 1099309680, 1099309680, 159085080384161694423921987795, 158485341023734643098451512018, 158485341023734591971135652562],
    [158485341023734714016985060050, 158485341023734574378941219538]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485341021428872123456176339]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158504685017440031396532912850, 158504685017440026964124566226, 158504685017440035828941259730, 2165575953, 2165575953, 2165575953, 2165575953, 2165575953, 158504760019561951474470654419, 158504760056457691421703442899, 2168721681, 2168721681],
    [158504685017440044693757952722, 158504684436332140524975751890, 2199135089, 2147754001, 2199135089, 2147754001, 158543448006972861111607562963, 158620824018690420195666826451, 158504684574691156462286210002, 158504684722274116251217363922, 159085042310063911742860693715, 293741104],
    [293741104, 1099309680, 1099309680, 159085042310063911880308035795, 2199135089, 2147754001, 2199135089, 2147754001, 158543448006972861249054905043, 158620824018690420333114168531, 159085042310063911880308035795, 158504685017440097882658114514],
    [293741104, 38688577742748725220016850, 293741104, 9942813359547284257427751634, 9981572180149735164680934099, 19963068209797920945642542291, 1099379312, 39293045264242058234757842, 1099379312, 38688577742748725220016850, 158504685017440168801191662546, 293601840],
    [25166384, 293601840, 9981572180149735714470302419, 19963068209797921495431910611, 1099186800, 1099186800, 25166384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2165575953, 2165575953, 2165571857, 2165575953, 2165575953, 2169774353, 2169774353, 159742623306555168868127542002, 2165588241, 2165588241, 2165604625, 2165575953],
    [2165575953, 2164523281, 2165575953, 2165575953, 8960074863559867832139023426366177812645257346669697714717288355231900294110884692019169045496073813910, 3050697627545928250714127742383317692580689674579078557161285, 2165604625, 2165604625, 2166654289, 38990221171799171566436819, 556041553, 17072401],
    [556041553, 38687989716895514272760275, 1095008529, 1095008529, 2166654289, 6808840521175695003635221234, 286556433, 286556433, 286556433, 559186193, 38687989716895514272760275, 559186193],
    [286556433, 1091862801, 1091862801, 2168750353, 6703161066186141738249088944619590669939822565119492541316, 190690421844868311049895619043389048692922716731969920784197, 1525360451171382217996144957516649557037403372106078913517381, 2168750353]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158543372423743038960825336530, 2148827153, 158543372432966978345680045010, 2148827153, 2147778577, 2216985681, 572686896, 572686896, 572686896, 572686896, 1109820016, 572686896],
    [1109820016, 572686896, 2216985681, 158543372562102129733645961938, 2151972881, 158543372709685159891321295570, 2151972881]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158543373002545236476076036819]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158620748398564858097651745490, 158620748426236674087420232402, 158620748389340916513639563986, 158620748426236674121782067922, 158620748389340916513639563986, 158620748389340916651086906066, 158543443256934573274021565139, 158620814509389909679723910355, 159085042024121928113937977555, 158620748407788797482506453970, 158620748398564292982902686418, 158620748389340916513639563986],
    [158620748407787669452165809106, 158620748389340916513639563986, 158620748389340916651086906066, 158543443266158508259756020435, 158620748389340916788534248146, 158620814518613844664384623827, 159085042033345863092156240083, 158620748426236676252215870162, 158543443284606380303672480467, 572686896, 572686896, 572686896],
    [572686896, 1109820016, 572686896, 1109820016, 572686896, 158620814573957456518086530259, 2476032377195819041715912915, 4952064752085652137572303059, 574915184, 574915184, 574915184, 38044272],
    [1111786096, 1648788080, 1111786096, 1111786096, 2630783185483073407380685522, 289702161, 5106814379781285785825772242, 289702161, 570458672, 33587760, 570458672, 33587760],
    [1114014320, 33587760, 1114014320, 33587760, 574915184, 574915184, 574915184, 38044272, 1111786096, 1648788080, 1111786096, 1111786096],
    [289702161, 289702161, 570458672, 33587760, 570458672, 33587760, 1111786096, 33587760, 1111786096, 33587760]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158620748977367055612902511827]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2785535688529020698180518610, 158765829522759479108776821458, 5261566882827237474672116690, 158765980057379031166553752274, 269778961, 158766131182330422380055299026, 269778961, 268730385, 337937489, 337937489, 268730385, 272924689],
    [158770664930872158785101699794, 272924689, 10213629271423671027655312082, 10523133168405227727156154579, 605258288, 605258288, 606241328, 606241328, 606241328, 604144176, 608600688, 610697840],
    [608600688, 606241328, 20427257945598077240936501459, 1149534832, 1149534832, 1149534832, 75530800]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158775500927010693886555457747]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3095039587816297245486154450, 10523133170710945410165310162, 75498032, 10523133170710945444527145682, 75506224, 2553478597255097617003647699, 75506224, 2630849849710434021632251091, 1149518448, 1149518448, 1149518448, 75498032],
    [5571070782114514021977752530, 3104559878717817879479255762, 628679800074995303234732754, 5580439957360640455723779026, 5029509791553309995448734419, 5106881044008646400077337811, 628679800074996402813469394, 5571073140992043305509851347, 10523133170710947574960947922, 10523132585063414981655069394, 9923543159700330427835236563, 10523132594359407562501194450],
    [9942885982038099481170313683, 69239344, 67142192, 69239344, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 605258288, 605258288, 606241328],
    [606241328, 606241328, 604144176, 608600688, 610697840, 608600688, 606241328, 19827667936893179941615583443, 19847010759230948994950660563, 606241328, 67142192, 606241328],
    [67142192, 71336496, 71336496, 71336496, 67142192, 1149534832, 1149534832, 1149534832, 75530800]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound4_11_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159085004826297970433861357779]
  ]) (by decide) ?_
  decide +kernel

theorem bound4_11 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_11_0
  · exact bound4_11_1
  · exact bound4_11_2
  · exact bound4_11_3
  · exact bound4_11_4
  · exact bound4_11_5
  · exact bound4_11_6
  · exact bound4_11_7
  · exact bound4_11_8
  · exact bound4_11_9
  · exact bound4_11_10
  · exact bound4_11_11

theorem bound4 : TreeBound (n := 3) 21 [((0, 0), ⟨1, 0, false⟩)] := by
  apply branch_bound (k := (1, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound4_0
  · exact bound4_1
  · exact bound4_2
  · exact bound4_3
  · exact bound4_4
  · exact bound4_5
  · exact bound4_6
  · exact bound4_7
  · exact bound4_8
  · exact bound4_9
  · exact bound4_10
  · exact bound4_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_0 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_0 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290225712]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_1 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290090544]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_2 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290225712]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_3 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282885680, 2281701936, 2282885680, 2281701936, 2283807280, 2281701936, 2283807280, 2281701936, 3050680171447260653151103602391104359050785815225183591271812, 3053653526920307593262523983266054800177665146928097255283076, 3053676798855174985203251820166199406119649137545884728933445, 3050720902344151741915306614679859080966393333050435801037029],
    [3050860551133492522763169550138948990291477808980796552056196, 3050860551133492525075874010309498803531237039049965431273701, 3051046749519280431214590571108404223805932255246521692379524, 3052163939834006696499129736453561393949115814161347068024196, 406917393, 406917393, 406917393, 406917393, 11142140374377984502169470162, 675353393, 406917393, 675353393],
    [3050680171447260654143367930628964205911867817586758941216132, 3050674352747707494190838330374004476076953080235359090838916, 3051046749519280432206854899346264070667014257608097042323844, 3052163939834006697491394065307500020059065638360099082485124, 406917393, 406917393, 406917393, 406917393, 675353393, 406917393, 675353393]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_4 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290098736]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_5 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638599712144425683]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_6 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2290098736]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_7 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638599849591833811]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_8 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172731952, 2155889200, 2172731952, 159703937664258590743625598162, 159703936474370973047321658578, 159703938854146208439929538002, 159703941233921443832537417426, 159703936474370973047321658578, 159703945993471914617753175250, 159703936474370973047321658578, 159703955512572856188184693970, 2189574704],
    [159703937064702812203046274258, 2189574704, 159703937064702812203046274258, 2223260272, 158775500924776772131837184211, 2223260272, 159085004824064048679176638675]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_9 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703937064846932362546907379, 158485341019194948719470708947, 293610032, 25174576, 293610032, 562045488, 21277704200969723526223497971, 562045488, 98312744943595374206582834682876832815157605422334307799301, 1099051568, 562045488, 1099051568],
    [38688577742748726302213330, 2165392465, 2165392465, 2165392465, 2166441585, 2166441585, 3050697627545928254681911970428238736502707025953204924057765, 159703955954240805688744085715, 158543373000311313072090516179, 159703955954240805688744085715, 158620748975133132208916925651, 159703937064846932362546907379],
    [158775500924776770482569742547, 159703937064846932362546907379, 159085004824064047029875382483]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_10 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, false⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172731952, 2155889200, 2172731952, 2495451336271576250657670290, 9747554752764129319191698, 2495603632590657592808834194, 9747554752764129319191698, 9981572178131999921073686226, 19963068208068433670372984018, 79852044387687036166168777938, 2189574704, 2182234672],
    [2147500592, 2182234672, 2149597744, 2147500592, 2149597744, 2147500592, 2151694896, 158543372557562435354564496083, 2151694896, 158543372705145395143529468627, 2189574704, 159085079803054071988803998866],
    [2147500592, 159085042033345863094303331538, 2183283248, 2147500592, 2183283248, 2147500592, 158620748532384254491390905555, 158620748679967214280355878099, 2223260272, 310526512, 8405552, 310526512],
    [545276464, 10213629266884029425106617043, 545276464, 20117754044076878938895418579, 1082147376, 8405552, 1082147376, 8405552, 2223260272, 361054832, 8405552, 361054832],
    [10523133166171305972412252883, 20427257943364155486201054419, 1149518448, 8405552, 1149518448, 8405552]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_1_11 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, true⟩), ((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158466072583353220399377158355, 158485341019194949269260341459, 293601840, 25166384, 293601840, 9981576900282296829498364627, 19963077652296965480105120979, 1098990128, 1098990128, 25166384, 2165392465, 2165392465],
    [2165392465, 158485341618696116716555473043, 2166441585, 2166441585, 158466034214089518269310963923, 2215724113, 2215724113, 158466034214107532135244501139, 2267104881, 3050720902344151739437224766392480634509776588870658433027460, 2267104881, 3055143109744870396589878169538084353328948577882149753435621],
    [159085004381315168212871549139, 158466034509255437864353140947, 158543373000311313621880148691, 158466034214089518269310963923, 2215724113, 2215724113, 2250327665, 2250327665, 3050860551133492522763169550138948990291477808980796552056196, 158620748975133132758706558163, 344068656, 75498032],
    [344068656, 3053653524077069856315961799500303366233626267695849314693765, 9923507140234069519716847827, 191039543818220493865641880016996731203948573947588456025476, 19827631917426919033497194707, 1149518448, 1149518448, 1149518448, 75498032, 158775500924776771032359377107, 344068656, 75498032],
    [344068656, 5571073138758121550892241107, 1149518448, 1149518448, 1149518448, 75498032, 159085004824064047579665010899]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_1 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (0, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_1_0
  · exact bound6_1_1
  · exact bound6_1_2
  · exact bound6_1_3
  · exact bound6_1_4
  · exact bound6_1_5
  · exact bound6_1_6
  · exact bound6_1_7
  · exact bound6_1_8
  · exact bound6_1_9
  · exact bound6_1_10
  · exact bound6_1_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_2 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290188848]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_0 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638881067929568402]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_1 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622566819042557035730]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_2 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012622638885465978176658]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_3 : TreeBound (n := 3) 21 [((0, 1), ⟨0, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2281701936, 2282820144, 2281701936, 2283938352, 2281701936, 2283938352, 2281701936, 3714046939102406354848056466, 159694340773260811536166946002, 6190078133472676362764551634, 50645960934288067702270132775058176271842256058990942443333],
    [11142744985411254203554333842, 1238015744732136348005303442, 406917393, 406917393, 406917393, 406917393, 11142140374377984502169470162, 675353393, 406917393, 675353393, 3714046939111554291658261650, 2982083519608544361364165071237751952113568976558764133764],
    [6190078281055706520473437650, 1242851595593625023486756050, 193646184843609242816871928697544259382146097094117896818724, 1238015744741284284815508626, 406917393, 406917393, 406917393, 406917393, 675353393, 406917393, 675353393]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_4 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282824240, 2281710128, 2282824240, 2281710128, 2283938352, 2281710128, 2283938352, 2281710128, 2168726128, 2219057776, 2168726128, 2219057776],
    [2185503344, 2151948912, 2185503344, 2219057776, 3053653526920307255560928599207870456310515923087768599715140, 2219057776, 3053653526920307255560928599207870456310515923087768599715140, 158485341019668103329900266706, 158485340576518130829466026195, 158504685013373558114106868946, 158620748975025322467415688402, 158775500925830889444930096338],
    [158775500482099953107961383123, 159085004826280094696097322194, 159085004381387230205023097043, 2168726128, 2219057776, 2168726128, 2219057776, 2185503344, 2151948912, 2185503344, 2219057776, 2219057776],
    [158485340724101090618397180115, 158543373000203503330589279442, 158775500629682912896892537043, 159085004528970189993954250963]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_5 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282824240, 2281701936, 2282824240, 2281701936, 2283938352, 2281701936, 2283938352, 2281701936, 3050680171463908070237534855127966848221798391072609941652276, 158465996582668622380308497618, 158485341758262743438360448914, 2185503344],
    [2151940720, 2185503344, 3050860551133492525075889151061591729225656968251996996285029, 943792945, 406922033, 406922033, 159694340773404865286857884627, 675357233, 675357233, 675357233, 3050680171463908070567642680100586080790606774499848280148036, 158465996730251652537983829202],
    [158504684720112520372427036114, 158466034509183515495145538770, 2185503344, 2151940720, 2185503344, 943792945, 406922033, 406922033, 675357233, 675357233, 675357233]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_6 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282824240, 2281710128, 2282824240, 2281710128, 2283938352, 2281710128, 2283938352, 2281710128, 2168726128, 2219057776, 2168726128, 2219057776],
    [2185503344, 2151948912, 2185503344, 2219057776, 2219057776, 138477585, 406917393, 138477585, 406917393, 11142140374377984777064154322, 675357233, 138477585],
    [675357233, 2168726128, 2219057776, 2168726128, 2219057776, 2185503344, 2151948912, 2185503344, 2219057776, 2219057776, 138477585, 406917393],
    [138477585, 406917393, 675357233, 138477585, 675357233]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_7 : TreeBound (n := 3) 21 [((0, 1), ⟨1, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282816048, 2281701936, 2282816048, 2281701936, 2283938352, 2281701936, 2283938352, 2281701936, 3714046939102410752863110290, 1238015744732136349045490898, 6190078133472676362735191506, 50645960934288067702270132775058176397476592401260280954181],
    [1238015744732136347971749010, 943792945, 406922033, 2240838367556492501896381855999333348508688525187246944494725967475524644551345373947010017753974674327, 406922033, 159694340773404865424305292755, 675357233, 675357233, 675357233, 3714046939111558689606206610, 1238015892315166506720822482, 6190078281055706520410523090],
    [1242851595593625023419647186, 1238015744741284284714845330, 943792945, 406922033, 406922033, 675357233, 675357233, 675357233]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_8 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047381851501741316637842, 159694341216009902558948754642, 6190078576221767316826883538, 403784240, 403784240, 134234672, 673333808, 134234672, 673333808, 134234672, 1238015597185135538178491602, 1238015597185135538178491602],
    [672350768, 672350768, 673333808, 673333808, 673333808, 673333808, 671236656, 11142140374666215428110550738, 940786224, 940786224, 134234672, 673333808],
    [134234672, 673333808, 134234672, 11142140522069039546030392275, 11142140669651999334961546195, 11142745428160380135830324370, 134234672, 673333808, 134234672, 673333808, 134234672, 1238015744732136897761117330],
    [21046265299261889060884481491, 1238015744741284834504213650, 21046265446844848849815635411, 39635843693961965894243585170, 39926003599543717289672182994, 39655187687667350310779751890, 39693880397444813116508605586, 39926003599543787657342618770, 39616499700256511110036982930, 39926022489009719135923477650, 39926003599543787657342618770, 19827594138999770930007377042],
    [590332121182638310610, 19846938132705190530915632338, 154752539975759456291128530, 39926003599543787657342618770, 590332121181564568722, 119159020708858498992868301970, 590332121181564568722, 39638261546754187025944024210, 79852006608755313396706055378, 39638262727345807743355327634, 40238000909487011250672112786, 79387750759824398575747601618],
    [39928421452336008789043059858, 39618917553048732241737421970, 39928440341801940267623914642, 39928459231267871746204769426, 39635843693961965894243585170, 590332121182638310610, 39655187687667350310779751890, 309504489619397728870204562, 590332121181564568722, 309523379085329207451059346, 590332121181564568722]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_9 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 0, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2147566673, 2148615249, 2148615249, 158465996435229716754444060883, 2166441585, 2166441585, 3050680171447260653151103602694328283060544615446357663078788, 3050680171447260654143367931856306298794928350562915253501316, 158485341019267010711555147987, 3050697627545928250720587794141561799217665625125530817596804, 3050697627545928250756764097808947515791386119966734515275524, 3050720905140920519588508636574096929886316642676684558294165],
    [3050767454692974321003925460658965437770720457645961315628981, 2165392465, 2165392465, 2165392465, 158504684422640626322857265619, 2166441585, 2166441585, 158465996435229716754444060883, 2215724113, 2215724113, 158465996435229716754444060883, 2267104881],
    [2267104881, 3050720902477331075981383050796752914712605895658469551481877, 2182169713, 2182169713, 158543372410051535891270470611, 2183218801, 2183218801, 3050720902344151741915321755431942606304663471879524309040741, 3050720902344151741915321755431933205697490148255880468266597, 159703955954312867680828524755, 158543377206138004017739336851, 2182169713],
    [2182169713, 158620748384873355028096880083, 2183218801, 2183218801, 6330745116786011110111460158360959248875857103055500414340, 39923585746751566526715921618, 191039543818220493865641880094006505167811389737709303827844, 39926003599543787657342618770, 39926003599543787657342618770, 39928421452336008789043059858, 309504489619397179114390674, 158775500924848832474654181587],
    [7447935431512276394650625195478739767625505100075300097412, 79852006608755313946495423698, 39926022489009719685746400402, 119159020708858500092447038610, 39928440342954861772297870482, 309523379085328657762354322, 159085004824136109021959821523]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_10 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, false⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047381851501741350192274, 2505047184964767369731900562, 9747554752764129319191698, 2505350597011300540529902738, 9747554752764129319191698, 19963002094937919785944614098, 39935675006100704690773822610, 590332121732427678930, 39940529598845235423541861522, 590332121732427678930, 3714198497578957968043541650, 1247687594038144404218315922],
    [672350768, 672350768, 673333808, 673333808, 673333808, 673333808, 671236656, 11142140374666215977899919058, 940786224, 11142140383710014725653807315, 940786224, 134234672],
    [673333808, 134234672, 673333808, 134234672, 21046265742443387701514339538, 21046265160902864239434154195, 134234672, 673333808, 134234672, 673333808, 134234672, 1238015744732136897794671762],
    [1238015744741284834537768082, 39635843693961965894277139602, 39616518589722372770736770258, 39655187687667350860569120210, 381335387939751254045730649098717286831813751948078489547428, 39693880397444813116542160018, 39926003599543787657376173202, 39616499700256511110070537362, 39926022489009719135957032082, 39926003599543787657376173202, 20553509857225779351520402, 590332121732427678930],
    [39897503562645930015589586, 154752539975760006080496850, 39926003599543787657376173202, 590332121181598123154, 119159020708858498992901856402, 590332121181598123154, 39638261545601265521370729618, 79233036589112623809045861586, 79271686797591670420297356754, 79852044387687176903657133266, 39696298249084112743635750034, 39928421451183087284469763218],
    [39618917551895810737164127378, 39928440340649018763050622098, 39928459230114950241631476882, 24180287316175219991905426, 590332121732427678930, 43524281021489817539708114, 309504489619397728903758994, 590332121181598123154, 309523379085329207484613778, 590332121181598123154]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_3_11 : TreeBound (n := 3) 21 [((0, 1), ⟨2, 1, true⟩), ((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158466072583425282391461597395, 158485341019267011261344780499, 2495376958927408511838192786, 38688577743030201262146770, 2495528074654860340485031058, 39655187687667350310779751890, 79271686797591670420297356754, 19345764629196133393106066, 2165392465, 2165392465, 2165392465, 158504684422640626872646898131],
    [2166441585, 2166441585, 158465996435229717304233693395, 2215724113, 2215724113, 158465996435229717304233693395, 2267104881, 2267104881, 158466072288259362813599289555, 3050720902477331075971052139101201520806305513100681058824613, 2182169713, 2182169713],
    [158543372410051536441060103123, 2183218801, 2183218801, 3050720902344151741915321755431942607165315584965354898580069, 3050720902344151741915321755431933206558142260540167081157221, 158466034214161580261395402963, 2215724113, 2215724113, 158466034214161580261395402963, 2250327665, 2250327665, 158620748458665961382996350419],
    [2182169713, 2182169713, 158620748384873355577886512595, 2183218801, 2183218801, 2785535683989671583972197522, 309504489619397180154578130, 2785686799645061386176955538, 39926003599543787657342618770, 39926003599543787657342618770, 39928421451183087284469763218, 309504489619397179080836242],
    [158775500924848833024443816147, 2785554573455603062553052306, 619008388906673727460213970, 5571070777503098484354581714, 5571073138830183542976680147, 39926022489009719135923477650, 119159020708858500092447038610, 39928440342954861772297870482, 309523379085328657661691026, 159085004824136109571749449939]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_3 : TreeBound (n := 3) 21 [((1, 0), ⟨0, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (0, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_3_0
  · exact bound6_3_1
  · exact bound6_3_2
  · exact bound6_3_3
  · exact bound6_3_4
  · exact bound6_3_5
  · exact bound6_3_6
  · exact bound6_3_7
  · exact bound6_3_8
  · exact bound6_3_9
  · exact bound6_3_10
  · exact bound6_3_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_4 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_0 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282914352]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_1 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012041746883581191405779]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_2 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282914352]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_3 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282885680, 2281701936, 2282885680, 2281701936, 2281710128, 2281701936, 2281710128, 2281701936, 403849776, 159694340625677781928247428306, 403849776, 134234672],
    [673202736, 134234672, 673202736, 134234672, 2232567121, 2165458257, 2165458257, 2266121585, 2182235505, 2232567121, 2182235505, 2215789905],
    [2215789905, 403849776, 403849776, 134234672, 673202736, 134234672, 673202736, 134234672, 2232567121, 2165458257, 2165458257, 2266121585],
    [2182235505, 2232567121, 2182235505, 2215789905, 2215789905]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_4 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283831856]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_5 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_6 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283831856]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_7 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_8 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2168685104, 159703936621953934485620917458, 2168685104, 159703955512572857837552798930, 2185396784, 2151711280, 2185396784, 159703936621953934485620917458, 2219082352, 158775500924965936510426941651, 2219082352, 159085004824262220256987582675]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_9 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703936770104365443409250547, 158485340576662256978298669267, 287343152, 6228538414707034985794373875, 287343152, 14895870863023203636724822465415516833833146301576077639589, 555778608, 18907696, 555778608, 555778608, 1093829168, 555778608],
    [1093829168, 158495315395265698369758300627, 289572177, 158495013163810794711927753171, 289572177, 826443633, 558007921, 1094878289, 558007921, 1363314001, 1094878289, 1094878289],
    [158543372557778621330918476499, 158543372557778621330918476499, 159703955511708113947572046035, 158620748532600440467744886483, 159703936770104365443409250547, 158775500482244078741397702867, 159703936770104365443409250547, 159085004381531355288703342803]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_10 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, false⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2168685104, 2185368112, 2151678512, 2185368112, 2151686704, 2151678512, 2151686704, 158485341019379609223437616851, 2151694896, 158485341019384113097959803091, 2151694896, 158485341019393120847004176595],
    [2168685104, 2236027504, 158466034509183374757657183442, 2236027504, 2219057776, 158466034509183374757657183442, 2219057776, 158504685013085064007644219091, 2185396784, 2151711280, 2185396784, 2495469782997742764150621330],
    [2495661038840466110549197970, 642155120, 4227632, 642155120, 4227632, 1145340528, 4227632, 1145340528, 4227632, 2219082352, 306348592, 2785535684170112419084910803],
    [306348592, 541098544, 4227632, 541098544, 4227632, 1077969456, 4227632, 1077969456, 4227632, 2219082352, 3095039583457388966390546643, 642155120],
    [4227632, 642155120, 4227632, 1145340528, 4227632, 1145340528, 4227632]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_5_11 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, true⟩), ((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3050680171447260655466387035017309366917712952587962725240196, 159085080086978038827162538195, 158543448263225304972463182547, 158543448263225304972463182547, 3050680171447260655466387034940370024204363855661037184159108, 158543448263225305109910524627, 3050680171447260655466387034945408827825090956377162699836804, 3050680171447260655466387034940370026355994136371099505331588, 3050680171447260655466387034945709648115289416068249034755460, 158466072288403486797768167635, 158485340724245216767230087379, 3050697627545928253361457959471014332238318415837903929019780],
    [158485415101517319799346565331, 3053653524789440577871762131356844169746096376764577295610501, 159085042308046175973086335187, 159085042308046176110533677267, 289572177, 289572177, 826443633, 558007921, 1094878289, 558007921, 1363314001, 1094878289],
    [1094878289, 158466001452906244852668698835, 158543372705361581119849894611, 356681041, 356681041, 570458672, 33587760, 570458672, 33587760, 1111654960, 33587760, 1111654960],
    [33587760, 158620748680183400256676304595, 6330745116786011110111460228155842872809948816612982066564, 356681041, 356681041, 606110256, 67142192, 606110256, 67142192, 1145340528, 1145340528, 1145340528],
    [67142192, 158775500629827038530329123027, 7447935431512276394650625265273623391559596812850023959940, 606110256, 67142192, 606110256, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 159085004529114315077634756819]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_5 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (1, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_5_0
  · exact bound6_5_1
  · exact bound6_5_2
  · exact bound6_5_3
  · exact bound6_5_4
  · exact bound6_5_5
  · exact bound6_5_6
  · exact bound6_5_7
  · exact bound6_5_8
  · exact bound6_5_9
  · exact bound6_5_10
  · exact bound6_5_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_6 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 4) (b := []) (a := List.flatten [
    [2290254384]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_0 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2282750512, 2282820144, 2282820144, 2282955312, 2282959408, 2282955312, 2282750512, 158485340439168255890691329170, 158775500344750007286119926994, 158504684432873640307227495890, 159703937665339731731124718802],
    [3050860551133492480117807994571865640212432359593726417393348, 3053839722376149501254033306076292117418657836772279641496900, 158543377142651103112956349586, 3055143110100014613131624137065505016141868154727990501104964, 158775500344750077653790362770, 3053653526920307254261165687619582816065788156735969295392068, 158775519234216009132371221650, 3053653526920307254261165687619582816065788156735969295392068, 2147631121, 158485340438591478482260213971, 158504684432296939311616623826, 3050697627545928254702722924305732624764213948041325465681061],
    [2183283249, 2183283249, 2147631121, 2183283249, 158775500344750008935387368658, 158775500482568353857386318035, 159085004245190206987333407954, 159085004529438590193623371987, 158485340440321247764075910290, 158466109783411381851354436754, 158485341620912868481487213714, 158620823954123157167845545106],
    [158620748396259291066863326418, 159085079803054071988803998866, 158775500345903069527174945938, 158775519235369001005755800722, 2147631121, 158485340438591479036344549587, 3050697627545928250733669406400786088668768382396205956761413, 2183283249, 2183283249, 2147631121, 2183283249, 158775500482568354407175686355],
    [159085004529438590743412740307]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_1 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 0, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159704012042035131549529161939]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_2 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2282750512, 2282820144, 2282820144, 2282955312, 2282959408, 2282955312, 2282750512, 158485340439168818840644750482, 158775500353973942272928124114, 158504684442097575294035693010, 159703938855155287435344219602],
    [3050674352792100689780055372476457497012233473547822249554596, 158543377142651666062909770898, 158775500344750640603743784082, 158775519234216572082324642962, 3714046801248598590230758546, 3714046801256757244758868179, 134365201, 3089403582894860268654979616333930439850698684467683359789092, 673333809, 673333809, 134365201, 673333809],
    [158485340439168889209422482578, 158466034234771450737180415186, 158504684443250497348431910354, 158620823963346951967994942674, 158543377142651736431687502994, 159085042033346003831791686866, 158775500344750710972521516178, 158775519234216642451102375058, 3714046801265764998097944787, 134365201, 673333809, 673333809],
    [134365201, 673333809]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_3 : TreeBound (n := 3) 21 [((1, 1), ⟨0, 1, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2282820144, 2281701936, 2282820144, 2281701936, 2281710128, 2281701936, 2281710128, 2281701936, 159694340625677781928247428306, 134234672, 673333808, 134234672],
    [673333808, 134234672, 2232567121, 2165458257, 2165458257, 2266121585, 2182235505, 2232567121, 2182235505, 2215789905, 2215789905, 134234672],
    [673333808, 134234672, 673333808, 134234672, 2232567121, 2165458257, 2165458257, 2266121585, 2182235505, 2232567121, 2182235505, 2215789905],
    [2215789905]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_4 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283962928]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_5 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 0, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_6 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2283962928]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_7 : TreeBound (n := 3) 21 [((1, 1), ⟨1, 1, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2281734704]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_8 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714046939102624023891281042, 159694340773260743366546687186, 6190078133472889599401526738, 158478087022609313093231185106, 285376529, 158497431016314767877437787602, 285376529, 304251441, 304251441, 268599313, 304251441, 268599313],
    [25322980467132183595974528010338260430220991896746311924901, 159077750827478411403635858642, 3339653974736134392066391622741197425733489178507940861938085, 159694340773260743366546687186, 11142744985411291312172434578, 138445360, 1095008880, 16941073, 1095008880, 16941073, 1111786096, 1078231664],
    [1111786096, 1145340528, 1145340528, 1078231664, 1145340528, 1145340528, 19827593696250682106349487250, 39635843112277285979149058259, 19846937689956136891629831378, 1525360451171035398149375644282763618585577632026218903223461, 37782064, 4227632],
    [37782064, 4227632, 1145340528, 4227632, 1145340528, 4227632, 1095008880, 1095008880, 1111786096, 1078231664, 1111786096, 1145340528],
    [1145340528, 1078231664, 1145340528, 1145340528, 79252342221048684034270445779, 1111786096, 4227632, 1111786096, 4227632, 71336496, 4227632, 71336496],
    [4227632]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_9 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 0, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [287474224, 3713990271208982056957905107, 287474224, 6190004937224504391913179603, 555909680, 555909680, 555909680, 555909680, 381340112793018967416409982496059334923998523380472388324740, 555909680, 1525342995072714618784514980504666586123638071527203287141764, 158485340576950504946636425427],
    [287474224, 287474224, 555909680, 555909680, 555909680, 555909680, 555909680, 158495315395553946338096056787, 289572177, 158495013164099042680265509331, 289572177, 826443633],
    [558007921, 1094878289, 558007921, 1363314001, 1094878289, 1094878289, 158620748532888688436082642131, 158543372558066869299256233683, 159703955511996361915909802195, 158620748532888688436082642131, 2785535168034813225392538770, 356681041],
    [5261566362400579599321925074, 356681041, 610697840, 1145340528, 610697840, 71336496, 1145340528, 1145340528, 1145340528, 71336496, 158775500482532326709735459027, 2785554057518759102482875538],
    [5571070261696863345882301906, 610697840, 1145340528, 610697840, 71336496, 1145340528, 1145340528, 1145340528, 71336496, 159085004381819603257041098963]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_10 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, false⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714046939111631223146022034, 21048683151342567804173943954, 138412592, 21046265447277361539680699602, 138420784, 3714046828953331603408488147, 138420784, 138412592, 3714198054839087449839371410, 3721300494029246464654443666, 1242851595593484285931291858, 3721451609756707089396401298],
    [1242851595593484285998400722, 6190078023251543981853574867, 1242851595593484285931291858, 1245269299658972609586005138, 558269040, 558269040, 575046256, 642155120, 575046256, 642155120, 608600688, 642155120],
    [608600688, 642155120, 2506255668044617033818702994, 2514417097918803623926695058, 1648788080, 4227632, 1648788080, 4227632, 1145340528, 4227632, 1145340528, 4227632],
    [21046265447277363670114501842, 138445360, 1095008880, 40854458333841623461119790290, 1095008880, 1111786096, 1078231664, 1111786096, 1145340528, 1145340528, 1078231664, 1145340528],
    [1145340528, 20553067117144154914817170, 39635843250663332383331453139, 39897208396445976755307730, 37782064, 4227632, 37782064, 4227632, 1145340528, 4227632, 1145340528, 4227632],
    [1095008880, 1095008880, 1111786096, 1078231664, 1111786096, 1145340528, 1145340528, 1078231664, 1145340528, 1145340528, 79252342507008683032424485075, 1525360451171382217995014448028097136498787916814435503540037],
    [1111786096, 4227632, 1111786096, 4227632, 71336496, 4227632, 71336496, 4227632]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_7_11 : TreeBound (n := 3) 21 [((1, 1), ⟨2, 1, true⟩), ((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3050680171447260655466387034945112634974486254716418584808836, 159085080087266286795500294355, 158620824238335372215074690259, 158620824238335372077627348179, 158620824238335372215074690259, 158466072288691734766105923795, 158485340724533464735567843539, 3050697627545928253361457959398817600295091717966359788588420, 158485415101805567767684321491, 159085042308334423941424091347, 159085042308334424078871433427, 289572177],
    [289572177, 826443633, 558007921, 1094878289, 558007921, 1363314001, 1094878289, 1094878289, 158466006175560975690651668691, 158543372705649829088187651795, 356681041, 356681041],
    [570458672, 33587760, 570458672, 33587760, 1111786096, 33587760, 1111786096, 33587760, 158620748680471648225014060243, 356681041, 356681041, 606241328],
    [67142192, 606241328, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 158775500630115286498666879187, 606241328, 67142192, 606241328, 67142192],
    [1145340528, 1145340528, 1145340528, 67142192, 159085004529402563045972512979]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_7 : TreeBound (n := 3) 21 [((1, 0), ⟨1, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (1, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_7_0
  · exact bound6_7_1
  · exact bound6_7_2
  · exact bound6_7_3
  · exact bound6_7_4
  · exact bound6_7_5
  · exact bound6_7_6
  · exact bound6_7_7
  · exact bound6_7_8
  · exact bound6_7_9
  · exact bound6_7_10
  · exact bound6_7_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703955955321737204346260690]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703937665339522274260290770, 2271482480, 159703936475532971570171612370, 2271482480, 158465996436247591295238933714, 2219057776, 158465996436247591295238933714, 2219057776, 159703936475532972119927426258, 159703938855155077978479791570, 2165576304, 3050685990146816522321192305670836906169419086196381981660485],
    [2165576304, 2147746416, 2147754608, 2147746416, 2147754608, 159703941234786189386918792914, 159703936475523966570040790226, 159703945994048412203796794578, 287474225, 287474225, 555909681, 555909681],
    [555909681, 555909681, 555909681, 381347022497701097954203413620138719625946245755484725126821, 762680225586037934900085284412493028978467872274802761606821, 159703955512572857837552798930, 3713980753301564758402665682, 6190011947599777136847752402, 11142083854716143927866559698, 558270065, 21004305, 558270065],
    [21004305, 381347022497701098202512693778088580272892563535328485572517, 762680225586037935148717566973418917951503981792365679987621, 2235830896, 3196670516267870255641817316123211488780077153222683550690177866299871605311105132983022479246368166216601152696020082725300094572204421373799563906059861384, 2235830896, 2219057776, 2219057776, 558270065, 21004305, 558270065, 21004305],
    [381347022497701098534235530770401359185551538123660383694757, 762680225586037935479471396756803611885893581167540868467621]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [159703937065855805725765405906]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3713973005660046601136245970, 159696702400404049429298023634, 6190005380549879696992636370, 159694417374510057069509479634, 159694569680053064602375818706, 302022673, 304251441, 302022673, 304251441, 302022673, 11142070130329545888705416914, 159694265659298888692367756498],
    [21046199629888878272130976978, 159694265659298888692367756498, 40854458629007543038982098130, 39771251068215469468595273939, 1713668720, 295536, 1713668720, 295536, 4489840, 295536, 4489840, 295536],
    [1528316348414892512998655757759130083550817800015594265276804, 1176797808, 1145340528, 1176797808, 1145340528, 1145340528, 1145340528, 1145340528, 1145340528, 79387750176986867523716661459, 572818032, 295536],
    [572818032, 295536, 4489840, 295536, 4489840, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [377782896, 5570900779443208095371641075, 377782896, 25322979401697488662465686780352235770949017422079880444997, 3245810257499029785290995738963484330334359086422313617631508, 5261566325067744196555803603, 5261566362251714521014109651, 4578990700449532252358724005833974182230632789828419791923476, 3053653524076373504398049521379339352838559833919961573927188, 3053653524076373504398049521379339352838559833919961573927188, 612663920, 10213629267964959306499033811],
    [612663920, 20117754044004887315672597715, 1082425968, 8684144, 1082425968, 8684144]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_8_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293868144, 2785536865661941533412297938, 293868144, 2476031785783045608691600594, 2495375779488500392900299986, 360989296, 2476031785783043684546251986, 360989296, 277086832, 1149518448, 1149510256, 1149510256],
    [1149518448, 1149518448, 1149518448, 1149518448, 293868144, 4952062980081255788146986194, 293868144, 360989296, 360989296, 277086832, 3244506869420019775541995498850776017261091994690211150080276, 5571070224355091112605619155],
    [5571070261539061437063923155, 25322980467132518960184781459053075927175640947248778664229, 25322980467132519621694333608100358565595974630745662773541, 10213633990304420563347705554, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448],
    [10523133168405227727155696339, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448, 20427257943292234231722411219, 1149534832, 8684144],
    [1149534832, 8684144]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_8 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_8_0
  · exact bound6_8_1
  · exact bound6_8_2
  · exact bound6_8_3
  · exact bound6_8_4
  · exact bound6_8_5
  · exact bound6_8_6
  · exact bound6_8_7
  · exact bound6_8_8
  · exact bound6_8_9
  · exact bound6_8_10
  · exact bound6_8_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_0 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047382355937335275816082]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_1 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047382932151813080629459]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_2 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [6190078576654114530422555858]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_3 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3053653526917540813351374026051298829286143145577562686426500, 403968273, 403968273, 403964177, 403968273, 403968273, 403968273, 403968273, 402915601, 403968273, 6190078004770143286604203218, 14895865180707536320100220772649332108947871097035704349461],
    [403968273, 6190077986903026693985829331, 6190078004770143698946229458, 26812567553435787265341296884023604864340513647875111631941, 1238317847628623149139100882, 403968273, 403968273, 403964177, 403968273, 1238015597149387802720470162, 403968273, 1238015597149388215062496402],
    [1238015597149388215096050834, 6190002429034799104297828819, 268730641, 308578161, 308578161, 4952062389749418829398704595, 340033809, 3052163939831275479343764865522696393889518228355009314831748, 340033809, 6190026077762953400830430163, 287605617, 287605617],
    [337937265, 304382833, 321160049, 304382833, 388268913, 337937265, 4577501116205084522286448166769511201869141302019872704446740, 337937265, 403968273, 403968273, 403964177, 403968273],
    [3714197908328888169706586515, 403968273, 3714197908328888169710780819, 3714197908328888169706586515, 6190030837025176218782174675, 287605617, 6051455972803725903336310861904762067253054184442383683989, 287605617, 337937265, 304382833, 321160049, 304382833],
    [388268913, 337937265, 337937265, 3050680171444832904825810764633421933317062213400334560988548, 4990750377160328397811909075, 4952062389749418829398704595, 23879942977277564048486154265445906055099569483002915961061, 4952064750932660264221311443, 24019591766618347209053549895085628619943275482532546197733, 4952062389749418829398704595, 24205790152406255660474570633511319916072288559316436891877, 3052163939831578948173836898695879486901237224806849729254788],
    [407142673, 3050680171445873369386057737624573270649872897715550175432068, 3050720902342764455837556289704273150049441855573021567059716, 3050674352746320209433528137369615822114648170963838738173316, 3051046749517893147449544706341873066552916017497461060852100, 3052163939832619412734083872303109015944967398249463101013380, 407142673]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_4 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [562201136, 158475820729446415045354340563, 562201136, 3074528088847707462967693677046457630913928352280340273413189, 1361348465, 1361348465, 38990220018807298215412179, 289702161, 289702161, 578847280, 158534306057745134883914713811, 578847280],
    [158612286495476761335328541907, 612663920, 545292848, 612663920, 159080169121866520043811508435]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_5 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [21664574632507648356070263539, 9923469362383137543400000211, 554861104, 21084271958333783458980104947, 554861104, 555909680, 555909680, 555909680, 553812528, 826442288, 555909680, 826442288],
    [95356802862998964324652723126112312503505643256689973690389, 95356802862998964324652723125811493073959295849889486503957, 556040817, 556040817, 556040817, 560236145, 558137969, 558137969, 11142065407963063034092522195, 9981501343499501896019806931, 11142070130329545903737735891, 10058877318321321032846216915],
    [10213610378499027827918179027, 10213629267964959306499033811, 21045585723399026740039846643, 10523133167252235853804673747]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_6 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [11142745427583885848522917010]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_7 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3074530998178057981448111594249870519529508400893255547162852, 555909680, 555909680, 555909680, 16941616, 11198724912381733234208504991015173626633666466719937770324774263474055308012544380897048238805020554134, 555909680, 4576030439895460561447472679691151727880171620381320320716836, 21046208779455924433559096531, 19827594139575987057180413139, 555909680, 555909680],
    [555909680, 16941616, 281608534987662527204225561660183690354085399917623927016366189331861402123343156587084360282603519895, 555909680, 4957364370303900827244264334129722651006775923228157145845796, 190690421844868315018951669339265217116155129040851057048389, 556040817, 556040817, 556040817, 560236145, 558137969, 558137969],
    [21046190185155912547872935123, 19885626120692351409800220371, 21046199629888878287163362515, 19963002095514170546626628819, 20117735155691877341698591955, 20117754045157808820279446739, 606372464, 71598704, 606372464, 67404400, 71598704, 71598704],
    [71598704, 67404400, 20427257944445085367585086675]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_8 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [1099137584, 40854439738388901162026927314, 1099137584, 40854440337944710488931828946, 40854441527832323787189257682, 1898219377, 17072145, 1898219377, 17072145, 21266449, 21266449, 1115849264],
    [49597395989361092636554037971, 1115849264, 59578292278465953972573441235, 1149534832, 1082163760, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_9 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [562201136, 39635843693961686084741236947, 562201136, 762691499316427424353437265552478624070510809230310624200341, 1092912753, 1095009361, 1092912753, 1525360451171035399473523996359924491303025654071942194661541, 1095009361, 1095009361, 41976368, 39693875675078050437361044179],
    [41976368, 39771251649899869574187453651, 1149534832, 8421936, 1149534832, 8421936]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_10 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, false⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [1099137584, 1115820592, 1082130992, 1115820592, 1082139184, 158476274076628768469584775891, 1082139184, 158476878539538575921619537107, 1082147376, 1082130992, 1082147376, 1082147376],
    [1099137584, 39638337102384025854594385042, 79233074365738642657415136466, 39638338282975668562240341138, 40238000909487011250672112786, 79852044387687317641145488594, 1115849264, 1108509232, 158533852129454875229057728723, 1108509232, 1075872304, 1073775152],
    [1075872304, 1073775152, 1077969456, 1073775152, 1077969456, 1077969456, 1115849264, 158611228104276694365884137683, 1109557808, 1073775152, 1109557808, 1073775152],
    [1145340528, 1073775152, 1145340528, 1145340528, 1149534832, 1082163760, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_9_11 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, true⟩), ((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293737008, 19344584037329126450922706, 293737008, 3050680171444529438600432592542318709441793890788376249699716, 19344584037331325474178258, 3050680171444572791249098535996696081021832497097754886868356, 1099121200, 3050680171444572791249098535996696083173460589058398305979780, 1099121200, 25297456, 79252342802733084139862888659, 293737008],
    [38688577742783910657524946, 293737008, 1099121200, 38688577742783910674302162, 1099121200, 25297456, 1092912753, 1095009361, 1092912753, 1095009361, 39638262283488692694277427347, 1095009361],
    [3050720902341382588843478278738707754385595343051625369243012, 77376565117631696837149906, 572555824, 33587760, 572555824, 33587760, 1111654960, 33587760, 1111654960, 33587760, 79310374783849448492482697939, 3050860551130723372004045674368349900544475921478992991686020],
    [572555824, 33587760, 572555824, 33587760, 1111654960, 33587760, 1111654960, 33587760, 79387750758671267629309107411, 75793008, 8421936, 75793008],
    [8421936]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_9 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 0, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_9_0
  · exact bound6_9_1
  · exact bound6_9_2
  · exact bound6_9_3
  · exact bound6_9_4
  · exact bound6_9_5
  · exact bound6_9_6
  · exact bound6_9_7
  · exact bound6_9_8
  · exact bound6_9_9
  · exact bound6_9_10
  · exact bound6_9_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_0 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_1 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2256802416, 2223260272, 2256802416, 2249462384, 158466034216341453325006410962, 2249462384, 2214855280, 2216960624, 158466034216323438926496928978, 2216960624, 2223252080, 2215928432],
    [2219065968, 2215928432, 158466034216323438926496928978, 2216968816, 2219065968, 2216968816, 2219065968, 158504683542249958113668237555, 2219065968, 2223252080, 3050674355588866337149433838934229584919333325384930377347940, 3052163941254586965203233381279575090865069781697582274985348],
    [3050680171463908070236323598576306104203130230312476601173317, 2223260272, 344220272, 1149518448, 344220272, 612647536, 19846332495544620234957720307, 612647536, 1149518448, 1149518448, 1149518448, 75776624],
    [2223260272, 8976479243995738434221747945572191143695106096254864433826004051742056694371039969015121177117552279447, 1149518448, 5958368544084219916759560057038244512163563365893895107428, 1149518448, 1149518448, 1149518448, 75760240]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_2 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2172945008]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_3 : TreeBound (n := 3) 21 [((2, 0), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485415398700975140540388562, 3050674355588866678483840699300769757647858741731417508298116, 158504758211814809241697523154, 2165576304, 158465996437409590367844701394, 2165576304, 2147746416, 2183406192, 2147746416, 2183406192, 2165580400, 2219057776],
    [2165580400, 2147754608, 2183406192, 2147754608, 2183406192, 2219057776, 2219057776, 2199138928, 158465996437409590367844701394, 2199138928, 2147746416, 2147746416],
    [158466034511489358504359236818, 2165580400, 2219057776, 2165580400, 2147754608, 2183406192, 2147754608, 2183406192, 2219057776, 2219057776, 3050674355588864003345959512628401736880097727908012344750948, 3050767454870544272082579388422615936249309217780766036736116],
    [2495450157913595813927458002, 159080206901951373209923359954, 4990824165325642259167843794, 9981572180149735149648615122, 158456401179030224555774973138, 19963068209797920930610156754, 79852044387687035616379409618, 2514719773193953542903185619, 95426766652087800869908845714594561133594905198798231582836, 2495450157913596363716826322, 4911853780008435175265490, 4990824165325642808957212114],
    [9747557058466951874090194, 9981572180149735699437983442, 19963068209797921480399525074, 79852044387687036166168777938, 2514719774346945966043578579, 5958368233332772971844029757818719029585152158513072190308, 43524281021349095083606227]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_4 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_5 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2182382192, 2221150832, 2151957104, 2221150832, 158465996437409590367844701394, 2151948912, 2151940720, 2151948912, 2151957104, 158620743685565861382316100339, 2151957104, 3050720902477331075976214995089292665720284084977112028123973],
    [2182382192, 2182353520, 2182353520, 2147746416, 2147754608, 2147746416, 2147754608, 3050720902477331075981388070592204551718720859346202310728997, 3050720902477331075981388070592204552005604075459076290097573, 2216985200, 2147779184, 2216985200],
    [606372464, 295536, 606372464, 295536, 1078231664, 295536, 1078231664, 295536, 2151973488, 342131312, 5106658802220642324386431219, 342131312],
    [11963246420047014787289113748876545194554073242903741313957, 541360752, 295536, 541360752, 295536, 1074037360, 295536, 1074037360, 295536, 2151973488, 23926492573724476335729394688670643639273831091527272847653, 537166448],
    [295536, 537166448, 295536, 1078231664, 295536, 1078231664, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_6 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2189722224]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_7 : TreeBound (n := 3) 21 [((2, 0), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [158485414817593070971623970002, 159085042024121928107495134418, 158504757630706905072781104594, 158485414817593070971623970002, 158543443256934573275095373522, 158466072004479237145344742610, 158620814509389909679723910354, 159085042024121928107495134418, 3050767454781760587808661725011655760599445181950743713428324, 3050674355588866675837802490666075740112244938893569946303876, 3050767454870546727603695232882178122940923949722476094437492, 3050674355588866675837156485860725909857036343493426130204788],
    [158485414826817005958432167122, 158466072013703171857342141650, 158504757639930840059589301714, 158466072013703171857279227090, 158543443266158508261903570642, 158620814518613844666532107474, 158620814518613844666532107474, 158466072013703171857409250514, 159085042033345863094303331538, 158485414817593070971623970002, 158504757639930840059589301714, 158466071995255301883658638546],
    [158466071995255302021105980626, 158466071995255301883658638546, 158466071995255302158553322706, 158543443284606380297230096082, 158466071995255304082816111826, 158620814573957456511644079314, 572818032, 295536, 572818032, 295536, 1145340528, 295536],
    [1145340528, 295536, 289702512, 159080206459202495492498003154, 289702512, 574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528],
    [4489840, 2650127212600856972351376530, 6051464585059370953769962072229801402343681223589638231365, 5145492957033487100647970258, 12009807336737590716048650547151867179360927523889048933397, 574915184, 295536, 574915184, 295536, 1145340528, 295536, 1145340528],
    [295536, 289702512, 289702512, 574915184, 4489840, 574915184, 4489840, 1145340528, 4489840, 1145340528, 4489840, 24019591766618345888297979386924336306856353877950532376869],
    [570720880, 295536, 570720880, 295536, 1145340528, 295536, 1145340528, 295536]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_8 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_9 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [377782896, 1686377072, 1082409584, 1686377072, 1082401392, 5570900773318244708789584627, 1082401392, 6330763229175802549412353217562028028872720004381192030277, 1082409584, 1082393200, 1082409584, 1082409584],
    [377782896, 6051450382042092237139893166481568660146550663206986855268, 5261566878287606901593096403, 12009810180665418064600152787845459722691670887751573321844, 24578186923981564524306070349476917500443034662719991710309, 5571051890486853647880163571, 5261566878215549273197510867, 5571051890486853647913718003, 612663920, 1679065712, 20426634019824473696144212211, 1679065712],
    [1076134512, 295536, 1076134512, 295536, 4489840, 295536, 4489840, 295536, 612663920, 606372464, 295536, 606372464],
    [295536, 4489840, 295536, 4489840, 295536, 1082425968, 8684144, 1082425968, 8684144]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_10 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2223276656]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_10_11 : TreeBound (n := 3) 21 [((2, 0), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293868144, 3095040766102210194620683474, 293868144, 2553478597255097601971328722, 2476031786936037482042627282, 2630849849710434006599865554, 2495375780641492266251326674, 360989296, 2476031786936035557897278674, 360989296, 277086832, 1149518448],
    [1149510256, 1149510256, 12661490943856396230913749971292803827762396416742874807637, 1149518448, 1149518448, 1149518448, 1149518448, 293868144, 4952062981234247661531567314, 293868144, 5029509791553309980416415442, 5106881044008646385044952274],
    [360989296, 5106881044008646385229501650, 360989296, 277086832, 5964169888702695070800756618251055938215223236947234009956, 5571070777574883448898732243, 5964186952310660819686175666728088162550910824221775770468, 25322980467132520944854747935501767717796997974465105756773, 5571070779952785126461018355, 5571070777502825820503146707, 5571070779952785126494572787, 9923543159700330429714404562],
    [10523137890753696183259108562, 9942885982038099483317900754, 572818032, 537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448, 95339395066863525084979466683675516354712972430286983541604, 48411716680474964979107380331806027923422600861781065520453],
    [47672744697544709981703335207538864894926525626620600660836, 1143243376, 295536, 1143243376, 295536, 4489840, 295536, 4489840, 295536, 19827667936893179943494751442, 19847010759230948997098247634, 572818032],
    [537166448, 572818032, 572818032, 642024048, 644121200, 642024048, 537166448, 572818032, 295536, 572818032, 295536, 4489840],
    [295536, 4489840, 295536, 1149534832, 8684144, 1149534832, 8684144]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_10 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, false⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_10_0
  · exact bound6_10_1
  · exact bound6_10_2
  · exact bound6_10_3
  · exact bound6_10_4
  · exact bound6_10_5
  · exact bound6_10_6
  · exact bound6_10_7
  · exact bound6_10_8
  · exact bound6_10_9
  · exact bound6_10_10
  · exact bound6_10_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_0 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047381851501225889105042, 3714047381779439200516572370, 3714047381923554457316099538, 134483985, 403968273, 403968273, 403968273, 134483985, 138678289, 138678289, 293741104, 293741104],
    [26998765761642865433472607683609724540827674766069486947012, 26812567553427659937182068519810961975017997962724179282628, 344138288, 27045312561323708304122321767469953969340097199870852303556, 344138288, 26998762964876794696123510836083336534130581276985574394564, 2495375778335508519547176146, 79257329622891984296849445075, 79315814951190704135409767123, 79393795388922330586823529683, 2785535684493795433012921554, 79549756264385583489651054803],
    [3095039583781071980318557394, 2476031784630053735340573906, 3714047382355935273574073490, 2495375778335508519547176146, 79257329622891984434296787155, 79315814951190704272857109203, 79393795388922330724270871763, 2785535683917334680692720850, 79549756264385583627098396883, 3095039583204611227998356690, 2476031784630053735340573906, 293880432],
    [361054832, 293880432, 4766861965204298491260230226870033601817665767180175577527221, 2553412482971627439832304786, 5624862490316554192632487700110934242001872362384161005414581, 344277616, 2630802624892899583640865938, 344277616, 361054832, 293741104, 2476031784630051811195225298, 293741104],
    [9995403991578060355511849683, 2630783734273971559824753874, 19976300280682921691531318483, 344416880, 2630783734850467495443301522, 344416880, 2476031784630051811195225298, 293880432, 361054832, 293880432, 2495451338505498005275284626, 2630783736579815393739281618],
    [344277616, 2630821515511822935606301842, 344277616, 361054832, 293601840, 276824624, 293601840, 9995403991578060905301218003, 19976300280682922241320686803, 344003120, 39935675007253415655010207955, 344003120],
    [276824624]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_1 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714047384085143686431654099]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_2 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3714198497578953054535943314, 6190078576077651578961659090, 3714198497578957452584551570, 403968273, 403968273, 403968273, 403968273, 403968273, 6190078133472887468997084626, 407114001, 6190078281055847257961792978, 407114001],
    [293741104, 293741104, 344138288, 344138288, 3714197916975483070877664402, 3714651265887044754286330067, 134488081, 134488081, 6190078576654112606159766738, 3715255728796852207394767059, 134488081, 134488081],
    [6190078133472887469101942226, 3714198054839089683228656786, 293880432, 361054832, 293880432, 5958351186377675146453408650871028796373409292499898086052, 2553563598699079268479143058, 5964169880384416194426599063045866549657311448739927044772, 344277616, 5106824374458080253171600594, 344277616, 361054832],
    [6190078576654112606277207250, 293880432, 361054832, 293880432, 4990824165325924283933922770, 2553563598699149637256875154, 344277616, 5106852709809899525439100114, 344277616, 361054832, 3714198497506891028223886482]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_3 : TreeBound (n := 3) 21 [((2, 1), ⟨0, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [403968273, 403968273, 403964177, 403968273, 26812567553435786572824766835303159881456076441870669141829, 403968273, 26812567553435787234334318994277483802487388693861774874437, 403968273, 403968273, 403964177, 403968273, 403968273],
    [403968273, 403968273, 402915601, 403968273, 8937528200139326381353512890937661662001271039743281966741, 403968273, 6190077988056018567336853971, 403968273, 403968273, 403964177, 403968273, 1238015597149387802720470162],
    [403968273, 1238015597149388215062496402, 1238015597149388215096050834, 23856668179054072846991839771436902166429966843811682539333, 268730641, 308578161, 4952064752085652137572336083, 308578161, 4952062390902410702749729235, 340033809, 340033809, 287605617],
    [287605617, 337937265, 304382833, 321160049, 304382833, 388268913, 337937265, 337937265, 403968273, 403968273, 403964177, 403968273],
    [21046265225903027478123906258, 3387320716039226996432094761647662448157004470584527494647844, 403968273, 26812567553435785911315372392345914170959499063112970229573, 21046265225903027890465932498, 1239224597336944041869313234, 3339653974736134389381635985114435297598727361690633964949540, 287605617, 287605617, 337937265, 304382833, 321160049],
    [304382833, 388268913, 337937265, 337937265, 3050680171444832904825810764936650195009330188705618910566788, 4990750378313320271162933715, 4952062390902410702749729235, 4952064752085652137572336083, 4952062390902410702749729235, 3052163939831578948173836898387841566121674145662708665000324, 407142673, 3718731674236583939106014418],
    [1242851595593765760908002514, 6194611752879402117304026578, 1242851595593765760975111378, 1242851595593766860486739154, 26812567553435787234334318995461961310420264593785493870405, 407142673]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_4 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [11142140383638236357103584402, 11142140964638049737990341842, 11142140392934224540976940498, 11142140383638234192307946642, 11142140374342237180127216850, 11142140392934222410543138258, 11142140374342237179053474962, 11142140374342237316500817042, 11142140374342237316509205650, 19495111739455525846253779, 23274798245143713767128784335561698238321430241283676805, 572686896],
    [572686896, 572686896, 572686896, 606241328, 572686896, 606241328, 572686896, 1361348465, 1361348465, 570458672, 536904240, 570458672],
    [536904240, 606241328, 536904240, 606241328, 536904240, 11142140411816727061932934290, 1361348465, 1361348465, 570458672, 536904240, 570458672, 536904240],
    [604144176, 536904240, 604144176, 536904240, 9923468919634539635477187730, 11142083854680343829266173138, 9942812913339924052013354450, 11142083854680343829266173138, 574915184, 541360752, 574915184, 574915184],
    [608600688, 642155120, 608600688, 642155120, 9923469361775362684905194706, 289702161, 9942813355480817469111796946, 289702161, 570458672, 536904240, 570458672, 536904240],
    [610697840, 536904240, 610697840, 536904240, 9923468920796538708082955410, 9923470101388159425494258834, 574915184, 541360752, 574915184, 574915184, 608600688, 642155120],
    [608600688, 642155120, 289702161, 289702161, 570458672, 536904240, 570458672, 536904240, 606241328, 536904240, 606241328, 536904240]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_5 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [9981609959081597606415110867, 10523208726268951579768984275, 50645958803419360495923028457401256320509953184225930652677, 10523208726268951717216326355, 3050685990138498230204608971532253211271426398098566889397044, 3241364592738876689668717491911948661102469930529761260277988, 3074530998178057984074608153116174570782092893558111080851684, 9904238706626262404450816723, 9923469363536129416751026899, 9923543740808232448867504851, 9981572180149735164680934099, 9981572180149735714470302419],
    [47690061559906354628882494289925388070943640672149707843781, 556040817, 556040817, 556040817, 560236145, 558137969, 558137969, 571572784, 9981500763544589600454415059, 571572784, 572686896, 33587760],
    [572686896, 33587760, 574915184, 33587760, 574915184, 33587760, 9981501344652493769370833619, 571572784, 571572784, 572686896, 33587760, 572686896],
    [33587760, 574915184, 33587760, 574915184, 33587760, 10058877319474312906197243603, 10523133168405227727155696339, 10213629269117951179850062547, 3266661457265239350896238748742409759318342333766329611129156, 9923543159700330444746724051, 69239344, 67142192],
    [69239344, 67142192, 1145340528, 1145340528, 1145340528, 67142192, 10523133168405227727155696339]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_6 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [11142744846548043671690937490, 135528465, 403968273, 135528465, 403968273, 135528465, 11142744846548611019690869906, 135528465, 403968273, 135528465, 403968273, 11142744837252044631088170130],
    [135528465, 11142744911620020874571285650, 21046265225903028440255300818, 572686896, 572686896, 572686896, 572686896, 606241328, 572686896, 606241328, 572686896, 556040817],
    [556040817, 570458672, 536904240, 570458672, 536904240, 606241328, 536904240, 606241328, 536904240, 134512657, 556040817, 556040817],
    [570458672, 536904240, 570458672, 536904240, 604144176, 536904240, 604144176, 536904240, 9924073382544346950064540818, 17072145, 19846937690532773565793701330, 17072145],
    [574915184, 541360752, 574915184, 574915184, 608600688, 642155120, 608600688, 642155120, 138706961, 9924073382553424518063459474, 19846937839268654859331704274, 574915184],
    [541360752, 574915184, 574915184, 608600688, 642155120, 608600688, 642155120, 138706961]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_7 : TreeBound (n := 3) 21 [((2, 1), ⟨1, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [3050685990138498230204608971229026936545071587670209451593524, 19963105988729783387376719059, 20427333503461801093549397203, 20427333503461801230996739283, 190667149887808093589879386696347370767757092491394359570565, 19808363483819111918231229651, 19827594140728978930531439827, 8958980170203942451378438371230576586463937519737542918754372455819887482953553981280303346341198048790, 19827668518001081962647917779, 190853348273594393251603819686537992213710092796017659949189, 19963068209797920945642542291, 19963068209797921495431910611],
    [190690421844868311049895619041001294470898584190491166338373, 556040817, 556040817, 556040817, 560236145, 558137969, 190690421844868311049895619043389048692922716731970033380677, 558137969, 19963001515559258251061236947, 572686896, 33587760, 572686896],
    [33587760, 38044272, 33587760, 38044272, 33587760, 19885626121845343283151247059, 572686896, 33587760, 572686896, 33587760, 38044272, 33587760],
    [38044272, 33587760, 19963002096667162419977655507, 20427257945598077240936109267, 20117754046310800693630475475, 19827667936893179958527136979, 606241328, 67142192, 606241328, 67142192, 71336496, 71336496],
    [71336496, 67142192, 20427257945598077240936109267]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_8 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [39635843693961967543611690130, 40854458629007824513958808786, 39655187687667351960147856850, 40854440339025539215128661202, 40854441528841094919348162002, 1898219377, 17072145, 1898219377, 17072145, 21266449, 21266449, 1108705904],
    [39693875675051028824564305618, 1108705904, 1109820016, 1114014320, 1109820016, 1111786096, 1111786096, 1114014320, 1111786096, 1111786096, 89213895099285482565026779859, 39693880397444814765876710546],
    [99194791388390343901046248659, 1149534832, 1082425968, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_9 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 0, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [2496433007392106219233739922, 2496433007392669169187161234, 19827593622459378134818096338, 5964525030904571325770831472769842246857346121116232503140, 20552919529856688216736914, 5965616036030832295400902383005862802703293340508929930084, 20552919561381885608330386, 39635843695114677958092261587, 23274798396877987973963681169308252236506596492603886980, 23274798396878003478093824325200977665588409803373228100, 19846937616164832919024698578, 23274798396878313560696687640468236887015161731577208292],
    [39896913235311473497081042, 23274798396879305825025849617602664348251213620806836292, 39896913266836670888674514, 4479491637030051514652572078315991732613671510815318696150802286185773801912467708050301776918708475799, 1092912753, 1095009361, 1092912753, 1095009361, 1095009361, 77376565117631696837149906, 572686896, 33587760],
    [572686896, 33587760, 1648788080, 33587760, 1648788080, 33587760, 39693875676231042310712072915, 154752539975761105659233490, 39771251651052861447538482387, 1149534832, 8421936, 1149534832],
    [8421936]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_10 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, false⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [39638261545601267170705280146, 79387779094023436015679706322, 1149518448, 79387779094023436050041541842, 1149510256, 1149510256, 1149518448, 1149518448, 1149518448, 1149518448, 79271686797591671519876093394, 79252417181158324165832479954],
    [79852044387687317641145488594, 79271759994272162665036125650, 79852044387687317091356120274, 79852044387687317641145488594, 43524283327192104297300179, 1108705904, 79310374784984425952291460818, 1108705904, 1109820016, 1114014320, 1109820016, 1111786096],
    [1111786096, 1114014320, 1111786096, 1111786096, 1108705904, 1108705904, 1143243376, 1074037360, 1143243376, 1078231664, 1078231664, 1074037360],
    [1078231664, 1078231664, 39696298249084114392970300562, 1176928880, 1145340528, 1176928880, 1145340528, 1145340528, 1145340528, 1145340528, 1145340528, 1149534832],
    [1082425968, 1149534832, 1149534832]
  ]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem bound6_11_11 : TreeBound (n := 3) 21 [((2, 1), ⟨2, 1, true⟩), ((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  refine subtree_bound (fuel := 3) (b := []) (a := List.flatten [
    [293671472, 25166384, 293671472, 19344584037296141102089426, 19344584037296141102089426, 1099186800, 1099186800, 25166384, 79252342803886076013213913299, 293671472, 25166384, 293671472],
    [1099186800, 38688577742748726302213330, 1099186800, 25166384, 1525360451171382216673125853197516432906647522963927027648325, 1092912753, 1095009361, 1092912753, 1095009361, 1525360451171382217996144957516649557038506501813206556575557, 1095009361, 77376565117631696837149906],
    [572686896, 33587760, 572686896, 33587760, 1111786096, 33587760, 1111786096, 33587760, 79310374785002440365833720531, 572686896, 33587760, 572686896],
    [33587760, 1111786096, 33587760, 1111786096, 33587760, 79387750759824259502660130003, 75530800, 8421936, 75530800, 8421936]
  ]) (by decide) ?_
  decide +kernel

theorem bound6_11 : TreeBound (n := 3) 21 [((1, 0), ⟨2, 1, true⟩), ((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (2, 1)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_11_0
  · exact bound6_11_1
  · exact bound6_11_2
  · exact bound6_11_3
  · exact bound6_11_4
  · exact bound6_11_5
  · exact bound6_11_6
  · exact bound6_11_7
  · exact bound6_11_8
  · exact bound6_11_9
  · exact bound6_11_10
  · exact bound6_11_11

theorem bound6 : TreeBound (n := 3) 21 [((0, 0), ⟨1, 1, false⟩)] := by
  apply branch_bound (k := (1, 0)) (by rfl)
  rintro ⟨q, s, d⟩
  fin_cases q <;> fin_cases s <;> cases d
  · exact bound6_0
  · exact bound6_1
  · exact bound6_2
  · exact bound6_3
  · exact bound6_4
  · exact bound6_5
  · exact bound6_6
  · exact bound6_7
  · exact bound6_8
  · exact bound6_9
  · exact bound6_10
  · exact bound6_11

theorem initialBound : TreeBound (n := 3) 21 [] := by
  apply canonical_start (by decide) (by decide)
  · intro a
    fin_cases a
    · exact bound0
    · exact bound2
  · intro a
    fin_cases a
    · exact bound4
    · exact bound6

end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver BusyBeaver

-- The relabeling argument is from @steveDOTdigital's four-state reduction.
theorem normalize (n : ℕ) [NeZero n] (C : Candidate n) :
    ∃ M : Machine (Fin 2) (Fin n), M.IsHalting ∧ M.haltingNumber = C.M.haltingNumber := by
  classical
  let a := (Fintype.equivFinOfCardEq C.Γ_card).setValue default (default : Fin 2)
  let b := (Fintype.equivFinOfCardEq C.Λ_card).setValue default (default : Fin n)
  let f : PointedMap C.Γ (Fin 2) := ⟨a,by simp [a]⟩
  let conf (s : Cfg C.Γ C.Λ) : Cfg (Fin 2) (Fin n) := ⟨s.q.map b,s.tape.map f⟩
  let M : Machine (Fin 2) (Fin n) := fun q t =>
    (C.M (b.symm q) (a.symm t)).map (fun (q',cmd) => (q'.map b, Stmt.write (f cmd.symbol) cmd.dir))
  have step (s : Cfg C.Γ C.Λ) : M.step (conf s) = (C.M.step s).map conf := by
    obtain ⟨q,T⟩ := s
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step,conf,Option.map_some,Tape.map_fst,M]
      change ((C.M (b.symm (b q)) (a.symm (a T.head))).map _).map _ = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      cases h : C.M q T.head with
      | none => rfl
      | some z =>
        obtain ⟨q',⟨t,d⟩⟩ := z
        simp [Tape.map_move,Tape.map_write]
  have start : conf (Machine.init []) = Machine.init [] := by
    simp [conf,Machine.init,Tape.map_mk₁,b]
  have trace (k : ℕ) : M.multiStep (Machine.init []) k = (C.M.multiStep (Machine.init []) k).map conf := by
    induction k with
    | zero => simp [start]
    | succ k ih =>
      rw [Machine.multiStep_succ,Machine.multiStep_succ,ih]
      cases he : C.M.multiStep (Machine.init []) k with
      | none => rfl
      | some s => exact step s
  have stops (k : ℕ) : M.HaltsAfter (Machine.init []) k ↔ C.M.HaltsAfter (Machine.init []) k := by
    simp only [Machine.HaltsAfter,trace,Option.map_eq_none_iff]
  refine ⟨M,?_,?_⟩
  · obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt _).mp C.M_isHalting
    exact (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k,(stops k).mpr hk⟩
  · unfold Machine.haltingNumber
    congr 1
    ext e
    constructor <;> rintro ⟨k,hk,rfl⟩
    · exact ⟨k,(stops k).mp hk,rfl⟩
    · exact ⟨k,(stops k).mpr hk,rfl⟩

end BeaverBound

open Turing Turing.BusyBeaver in
theorem OMA.solution : OMA.R_BusyBeaver_BB_3_R1.H2 := by
  intro C k hk
  obtain ⟨M, hM, hEq⟩ := BeaverBound.normalize 3 C
  rcases BeaverBound.initialBound M (BeaverBound.matches_empty M) with h | h
  · have hle : M.haltingNumber ≤ (21 : ℕ) := sInf_le ⟨21, h, rfl⟩
    rw [hEq, hk] at hle
    exact_mod_cast hle
  · exact (h hM).elim
