/- Standalone proof component for the zero/one-write Busy Beaver family
with return state one. This file proves only that fixed-return-state case. -/
import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1

/-!

New certificate construction and assembly: Hanan Beer (@hananzlt).
The generic finite-automata verifier is reused from James Halldon (@Halldon),
merged PR1292. The tape-reader soundness lemmas and target reduction are by
@marcusbuffett (PR4876 and PR4509). Their attribution is retained.
The untrusted certificate search follows the direct FAR and n-gram CPS methods
from bbchallenge. Every resulting certificate is checked by Lean.

The following verifier originally established the three-state upper bound.

That original search branches on the first unassigned transition in 21 steps.
The present four-state application uses the first unassigned transition in
106 steps. The new bit-mask tests imply the original verifier checks. Nonhalting leaves use finite-automata reduction: a DFA summarizes
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

def forceNat {α : Type} (v : ℕ) (f : ℕ → α) : α :=
  match v with
  | 0 => f 0
  | k + 1 => f (k + 1)

theorem forceNat_eq {α : Type} (v : ℕ) (f : ℕ → α) : forceNat v f = f v := by
  cases v <;> rfl

/-- Normalize packed fields once before the kernel checks repeated edge lookups. -/
def checkCertificateFast [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  forceNat (val / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (val / 16 % dfaBase) fun dfaCode =>
  forceNat (val / 16 / dfaBase) fun payload =>
  forceNat (2 ^ (n * size + 1)) fun initialBase =>
  forceNat (payload / initialBase) fun edges =>
  forceNat (payload % initialBase) fun blankReach =>
  let C : Certificate n := ⟨val % 2 == 1, ⟨extra,dfaCode⟩, edges,blankReach⟩
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem checkCertificateFast_eq [NeZero n] (tb : Program n) (val : ℕ) :
    checkCertificateFast tb val = checkCertificate tb val := by
  simp only [checkCertificateFast, forceNat_eq]
  rfl
end BeaverBound
namespace BeaverBound

def Certificate.row (cert : Certificate n) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (n * cert.dfa.size)
  | some _ => (cert.edges >>> ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1))) % 2 ^ (n * cert.dfa.size + 1)

theorem state_nodeId_lt (cert : Certificate n) (q : Fin n) (l : Fin cert.dfa.size) :
    nodeId cert (some (q,l)) < n * cert.dfa.size := by
  have hh := Nat.mul_le_mul_right cert.dfa.size (Nat.succ_le_of_lt q.isLt)
  simp only [Nat.succ_mul] at hh
  have hl := l.isLt
  simp only [nodeId]
  omega

theorem nodeId_lt (cert : Certificate n) (p : Node cert) :
    nodeId cert p < n * cert.dfa.size + 1 := by
  rcases p with _ | ⟨q,l⟩
  · simp [nodeId]
  · exact Nat.lt_succ_of_lt (state_nodeId_lt cert q l)

theorem row_bit (cert : Certificate n) (p q : Node cert) (a : Symbol) :
    (cert.row p a).testBit (nodeId cert q) = cert.edge p a q := by
  cases p with
  | none =>
    cases q with
    | none => simp [Certificate.row,Certificate.edge,nodeId]
    | some q =>
      have hh := state_nodeId_lt cert q.1 q.2
      simp [Certificate.row,Certificate.edge,ne_of_gt hh]
  | some p =>
    have hq := nodeId_lt cert q
    simp only [Certificate.row,Certificate.edge,Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight,hq,decide_true,Bool.true_and]

def rowsIncluded (a b : ℕ) : Bool := decide (a &&& b = a)

theorem rowsIncluded_bit {a b i : ℕ} (h : rowsIncluded a b = true)
    (ha : a.testBit i = true) : b.testBit i = true := by
  have he : a &&& b = a := of_decide_eq_true h
  have hh := congrArg (fun v => v.testBit i) he
  simpa only [Nat.testBit_and,ha,Bool.true_and] using hh

def checkAtBits (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q,l)
  match tb.get (q,a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      forceNat (cert.row p a) fun target =>
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state,l')) a' s then
            rowsIncluded (cert.row s m.write) target
          else true
        else true
    else cert.edge p a (some (m.state,cert.dfa.next m.write l))

theorem checkAtBits_sound {tb : Program n} {cert : Certificate n} {q : Fin n}
    {a : Symbol} {l : Fin cert.dfa.size} (h : checkAtBits tb cert q a l = true) :
    checkAt tb cert q a l = true := by
  unfold checkAtBits checkAt at *
  cases hg : tb.get (q,a) with
  | none => simpa [hg] using h
  | some m =>
    simp only [hg] at h ⊢
    cases hd : m.left with
    | false => simpa [hd] using h
    | true =>
      simp only [hd,if_true,forceNat_eq] at h ⊢
      apply List.all_eq_true.mpr
      intro l' _
      apply List.all_eq_true.mpr
      intro a' _
      have hh := allFin (allFin h l') a'
      by_cases he : cert.dfa.next a' l' = l
      · simp only [he,if_true] at hh ⊢
        apply List.all_eq_true.mpr
        intro s _
        have hs := allNodes hh s
        by_cases hed : cert.edge (some (m.state,l')) a' s = true
        · simp only [hed,if_true] at hs ⊢
          apply List.all_eq_true.mpr
          intro t _
          by_cases het : cert.edge s m.write t = true
          · have hrow : (cert.row s m.write).testBit (nodeId cert t) = true := by
              rwa [row_bit]
            have ht := rowsIncluded_bit hs hrow
            rw [row_bit] at ht
            simp only [het,ht,Bool.not_true,Bool.false_or]
          · simp [het]
        · simp [hed]
      · simp [he]

def checkMachineBits (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAtBits tb cert q a l

theorem checkMachineBits_sound {tb : Program n} {cert : Certificate n}
    (h : checkMachineBits tb cert = true) : checkMachine tb cert = true := by
  unfold checkMachineBits at h
  unfold checkMachine
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro l _
  exact checkAtBits_sound (allFin (allFin (allFin h q) a) l)

end BeaverBound

namespace BeaverBound

def checkBlankBits (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0,0)) && !cert.onBlank none &&
    (nodes cert).all fun p => if cert.onBlank p then
      rowsIncluded (cert.row p 0) cert.blankReach
    else true

theorem checkBlankBits_sound {cert : Certificate n} [NeZero n]
    (h : checkBlankBits cert = true) : checkBlank cert = true := by
  simp only [checkBlankBits,Bool.and_eq_true_iff] at h
  unfold checkBlank
  apply Bool.and_eq_true_iff.mpr
  refine ⟨Bool.and_eq_true_iff.mpr h.1,?_⟩
  apply List.all_eq_true.mpr
  intro p _
  have hp := allNodes h.2 p
  by_cases hb : cert.onBlank p = true
  · simp only [hb,if_true] at hp ⊢
    apply List.all_eq_true.mpr
    intro q _
    by_cases he : cert.edge p 0 q = true
    · have hrow : (cert.row p 0).testBit (nodeId cert q) = true := by rwa [row_bit]
      have hq := rowsIncluded_bit hp hrow
      change cert.onBlank q = true at hq
      simp only [he,hq,Bool.not_true,Bool.false_or]
    · simp [he]
  · simp [hb]

def checkCertificateBits [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  forceNat (val / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (val / 16 % dfaBase) fun dfaCode =>
  forceNat (val / 16 / dfaBase) fun payload =>
  forceNat (2 ^ (n * size + 1)) fun initialBase =>
  forceNat (payload / initialBase) fun edges =>
  forceNat (payload % initialBase) fun blankReach =>
  let C : Certificate n := ⟨val % 2 == 1, ⟨extra,dfaCode⟩, edges,blankReach⟩
  checkBlankBits C && checkMachineBits (if C.mirror then tb.flip else tb) C

theorem checkCertificateBits_sound [NeZero n] {tb : Program n} {val : ℕ}
    (h : checkCertificateBits tb val = true) : ¬ CanStop tb (start n) := by
  apply certificate_sound (val := val)
  rw [← checkCertificateFast_eq]
  unfold checkCertificateBits at h
  unfold checkCertificateFast
  simp only [forceNat_eq] at h ⊢
  exact Bool.and_eq_true_iff.mpr ⟨checkBlankBits_sound (Bool.and_eq_true_iff.mp h).1,
    checkMachineBits_sound (Bool.and_eq_true_iff.mp h).2⟩

end BeaverBound
namespace BeaverBound

/- The constructor is an untrusted finite calculation following direct FAR
saturation from bbchallenge. Its output must pass `checkCertificateFast`, whose
soundness is inherited from James Halldon's verifier. -/

def nfaRow (size edges p : ℕ) (a : Fin 2) : ℕ :=
  let width := 4 * size + 1
  if p = 4 * size then 1 <<< (4 * size)
  else (edges >>> ((2 * p + a.val) * width)) % (2 ^ width)

def nfaInsert (size edges p : ℕ) (a : Fin 2) (row : ℕ) : ℕ :=
  edges ||| (row <<< ((2 * p + a.val) * (4 * size + 1)))

def nfaInitial (tb : Program 4) (D : TapeDFA) : ℕ :=
  (List.finRange 4).foldl (fun e q =>
    (List.finRange 2).foldl (fun e a =>
      (List.finRange D.size).foldl (fun e l =>
        match tb.get (q,a) with
        | none => nfaInsert D.size e (q.val * D.size + l.val) a (1 <<< (4 * D.size))
        | some cmd => if cmd.left then e else
            nfaInsert D.size e (q.val * D.size + l.val) a
              (1 <<< (cmd.state.val * D.size + (D.next cmd.write l).val))) e) e) 0

def nfaCompose (size edges mask : ℕ) (a : Fin 2) : ℕ :=
  forceNat mask fun mask =>
  (List.range (4 * size + 1)).foldl (fun out p =>
    if mask.testBit p then out ||| nfaRow size edges p a else out) 0

def nfaIteration (tb : Program 4) (D : TapeDFA) (edges : ℕ) : ℕ :=
  (List.finRange 4).foldl (fun out q =>
    (List.finRange 2).foldl (fun out a =>
      match tb.get (q,a) with
      | none => out
      | some cmd => if cmd.left then
          (List.finRange D.size).foldl (fun out l =>
            (List.finRange 2).foldl (fun out b =>
              nfaInsert D.size out (q.val * D.size + (D.next b l).val) a
                (nfaCompose D.size edges (nfaRow D.size edges
                  (cmd.state.val * D.size + l.val) b) cmd.write)) out) out
        else out) out) edges

def nfaSaturate (tb : Program 4) (D : TapeDFA) : ℕ → ℕ → ℕ
  | 0, edges => edges
  | fuel + 1, edges => forceNat (nfaIteration tb D edges) fun next =>
      if next = edges then next else nfaSaturate tb D fuel next

def nfaBlankStep (size edges reach : ℕ) : ℕ :=
  reach ||| nfaCompose size edges reach 0

def nfaBlankReach (size edges : ℕ) : ℕ → ℕ → ℕ
  | 0, reach => reach
  | fuel + 1, reach => forceNat (nfaBlankStep size edges reach) fun next =>
      if next = reach then next else nfaBlankReach size edges fuel next

def constructCertificate (tb : Program 4) (choice : ℕ) : ℕ :=
  forceNat (choice / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (choice / 16 % dfaBase) fun code =>
  let D : TapeDFA := ⟨extra,code⟩
  let oriented := if choice % 2 == 1 then tb.flip else tb
  forceNat (nfaInitial oriented D) fun initial =>
  forceNat (nfaSaturate oriented D (2 * (4 * size + 1) ^ 2) initial) fun edges =>
  forceNat (nfaBlankReach size edges (4 * size + 1) 1) fun reach =>
  choice % 2 + 2 * extra + 16 * (code + dfaBase * (reach + 2^(4 * size + 1) * edges))

def checkChoice (tb : Program 4) (choice : ℕ) : Bool :=
  forceNat (constructCertificate tb choice) fun cert => checkCertificateBits tb cert

theorem choice_sound {tb : Program 4} {choice : ℕ}
    (h : checkChoice tb choice = true) : ¬ CanStop tb (start 4) := by
  apply checkCertificateBits_sound (val := constructCertificate tb choice)
  simpa only [checkChoice, forceNat_eq] using h

end BeaverBound
namespace BeaverBound

def chunkBytes : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, data => forceNat (data / 256) fun next =>
      data % 256 :: chunkBytes fuel next

def varints : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | b :: rest, acc, shift =>
    let next := acc + (b % 128) * 2^shift
    if b < 128 then next :: varints rest 0 0 else varints rest next (shift+7)

def decodeTokens (chunks : List (ℕ × ℕ)) : List ℕ :=
  varints (chunks.flatMap fun (count,data) => chunkBytes count data) 0 0

def checkGenerated (special : ℕ → Program 4 → Bool) :
    ℕ → Program 4 → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | _ + 1, _, [] => none
  | fuel + 1, tb, v :: rest =>
    if v = 0 then
      match firstMissing tb 106 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkGenerated special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkChoice tb (v-17) then some rest else none

theorem generated_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 106 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkGenerated special fuel tb a = some b) :
    TreeBound 106 tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    cases a with
    | nil => simp [checkGenerated] at h
    | cons v rest =>
      by_cases hv : v = 0
      · simp only [checkGenerated, hv, if_true] at h
        cases hFirst : firstMissing tb 106 (start 4) with
        | none => simp [hFirst] at h
        | some k =>
          simp only [hFirst] at h
          apply branch_bound hFirst
          intro m
          obtain ⟨x,y,hy⟩ := succeeds_each h (mem_moves m)
          refine ih ?_ hy
          rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
          omega
      · simp only [checkGenerated, hv, if_false] at h
        by_cases small : v < 17
        · simp only [small,if_true] at h
          by_cases hs : special v tb = true
          · exact hspecial v tb hs
          · simp [hs] at h
        · simp only [small,if_false] at h
          by_cases hc : checkChoice tb (v-17) = true
          · intro M hm
            exact upper_cannot_stop hm (choice_sound hc)
          · simp [hc] at h
end BeaverBound

namespace BeaverBound

/- This is only a data preparation pass. The result is checked again by
`checkPrepared`, including every branch and every certificate. No correctness
assumption about this pass is used by the soundness theorem. -/
def prepareCertificates : ℕ → Program 4 → List ℕ → List ℕ →
    Option (List ℕ × List ℕ)
  | 0, _, rest, acc => some (rest, acc)
  | _ + 1, _, [], _ => none
  | fuel + 1, tb, v :: rest, acc =>
    if v = 0 then
      match firstMissing tb 106 (start 4) with
      | none => none
      | some k => (moves 4).foldlM
          (fun st m => prepareCertificates fuel ((k,m)::tb) st.1 st.2)
          (rest, 0 :: acc)
    else if v < 17 then some (rest, v :: acc)
    else forceNat (constructCertificate tb (v-17)) fun cert =>
      some (rest, (cert+17) :: acc)

def preparedTokens (fuel : ℕ) (tb : Program 4) (xs : List ℕ) : List ℕ :=
  match prepareCertificates fuel tb xs [] with
  | some ([], acc) => acc.reverse
  | _ => []

def checkPrepared (special : ℕ → Program 4 → Bool) :
    ℕ → Program 4 → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | _ + 1, _, [] => none
  | fuel + 1, tb, v :: rest =>
    if v = 0 then
      match firstMissing tb 106 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkPrepared special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkCertificateBits tb (v-17) then some rest else none

theorem prepared_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 106 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkPrepared special fuel tb a = some b) :
    TreeBound 106 tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    cases a with
    | nil => simp [checkPrepared] at h
    | cons v rest =>
      by_cases hv : v = 0
      · simp only [checkPrepared, hv, if_true] at h
        cases hFirst : firstMissing tb 106 (start 4) with
        | none => simp [hFirst] at h
        | some k =>
          simp only [hFirst] at h
          apply branch_bound hFirst
          intro m
          obtain ⟨x,y,hy⟩ := succeeds_each h (mem_moves m)
          refine ih ?_ hy
          rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
          omega
      · simp only [checkPrepared, hv, if_false] at h
        by_cases small : v < 17
        · simp only [small,if_true] at h
          by_cases hs : special v tb = true
          · exact hspecial v tb hs
          · simp [hs] at h
        · simp only [small,if_false] at h
          by_cases hc : checkCertificateBits tb (v-17) = true
          · intro M hm
            exact upper_cannot_stop hm (checkCertificateBits_sound hc)
          · simp [hc] at h
end BeaverBound

namespace BeaverBound

/-- This decoder supplies data only; every decoded program is checked by the proof. -/
private def decodeProgram : ℕ → ℕ → Program 4
  | 0, _ => []
  | fuel+1, data => if data = 0 then [] else
      let v := data % 256 - 1
      ((⟨v/32%4, Nat.mod_lt _ (by decide)⟩, ⟨v/16%2, Nat.mod_lt _ (by decide)⟩),
        ⟨⟨v/4%4, Nat.mod_lt _ (by decide)⟩,
          ⟨v/2%2, Nat.mod_lt _ (by decide)⟩, v%2 == 1⟩) ::
        decodeProgram fuel (data/256)

private def programCode (data : ℕ) : Program 4 := decodeProgram 8 data

private theorem branchFour {tb : Program 4} {k : Key 4}
    (h : firstMissing tb 106 (start 4) = some k)
    (p0 : TreeBound (n := 4) 106 ((k,⟨0,0,false⟩)::tb))
    (p1 : TreeBound (n := 4) 106 ((k,⟨0,0,true⟩)::tb))
    (p2 : TreeBound (n := 4) 106 ((k,⟨0,1,false⟩)::tb))
    (p3 : TreeBound (n := 4) 106 ((k,⟨0,1,true⟩)::tb))
    (p4 : TreeBound (n := 4) 106 ((k,⟨1,0,false⟩)::tb))
    (p5 : TreeBound (n := 4) 106 ((k,⟨1,0,true⟩)::tb))
    (p6 : TreeBound (n := 4) 106 ((k,⟨1,1,false⟩)::tb))
    (p7 : TreeBound (n := 4) 106 ((k,⟨1,1,true⟩)::tb))
    (p8 : TreeBound (n := 4) 106 ((k,⟨2,0,false⟩)::tb))
    (p9 : TreeBound (n := 4) 106 ((k,⟨2,0,true⟩)::tb))
    (p10 : TreeBound (n := 4) 106 ((k,⟨2,1,false⟩)::tb))
    (p11 : TreeBound (n := 4) 106 ((k,⟨2,1,true⟩)::tb))
    (p12 : TreeBound (n := 4) 106 ((k,⟨3,0,false⟩)::tb))
    (p13 : TreeBound (n := 4) 106 ((k,⟨3,0,true⟩)::tb))
    (p14 : TreeBound (n := 4) 106 ((k,⟨3,1,false⟩)::tb))
    (p15 : TreeBound (n := 4) 106 ((k,⟨3,1,true⟩)::tb))
    : TreeBound (n := 4) 106 tb := by
  apply branch_bound h
  rintro ⟨q,a,b⟩
  fin_cases q <;> fin_cases a <;> cases b
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1 : TreeBound (n := 4) 106 (programCode 0x48290751) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x80402010000c0002018004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2 : TreeBound (n := 4) 106 (programCode 0x48290752) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201008040020108004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3 : TreeBound (n := 4) 106 (programCode 0x48290753) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201000140004028004200108002200080de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5 : TreeBound (n := 4) 106 (programCode 0x4829075431) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201008040002010084002108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6 : TreeBound (n := 4) 106 (programCode 0x4829075432) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce6204481,0x1081084210481,0x1081ce6204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x8000600018010402010084020102002080080ce3,0x8004200108004020100804020102002080080ce3,0x8000a00028010804020104020102002080080de3,0x8040200008000000000004020102002080080ce3,0x8001200048005008040204020102002080080ee3,0x8000200008000000000004020102002080080ce3,0x8002200088002010080404020102002080080ce3,0x8000200008000000000004020102002080080ce3,0x8004200108004020100804020102002080080ce3,0x8040200008000000000004020102002080080ce3,0xf30079bcc01e6f3003cfcc1e60f3003cc1e60f307981e61e607983cc1e679803cde600f379801e6c7195,0x8040200008000000000004020102002080080ce3,0x8010200408050080402004020102002080082ce3,0x0,0x8020200808060100804004020102002080084ce3,0x0,0x0,0x16c800111600016c803cc1e7023811c08e04603cc1ea08c1e60f301e9cc001e60f30408fcc1e7037c5],
[0xc00030001020040800900024020100800100e4,0x400010001020040800900024020100800000e4,0x0,0x0,0x0,0x20400010001020040800900024020100800000e4,0x0,0x0,0x0,0x20400030001020040800900024020100800100e4,0x0,0x0,0x0,0x0,0x0,0x0,0x8000600018020402010084020104002100080ce3,0x8000200108000000000004020104002100080ce3,0x8000a00028020804020104020104002100080de3,0x0,0x8001200048005008040204020104002100080ee3,0x8000200008000000000004020104002100080ce3,0x8002200088002010080404020104002100080ce3,0x8000200008000000000004020104002100080ce3,0x8004200108004020100804020104002100080ce3,0x0,0x0,0x0,0x8010200408050080402004020104002100082ce3,0x0,0x8020200808060100804004020104002100084ce3,0x0],
[0x0,0x0,0xc00030001020040800a00028040201000100e4,0x400010001020040800a00028040201000000e4,0x0,0x402010001020040800a00028040201000000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_87 : TreeBound (n := 4) 106 (programCode 0x4829075433) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201008040004020104004108002200080de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_88 : TreeBound (n := 4) 106 (programCode 0x4829075434) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080000210481,0x1080421204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0xc0003000090002010084002102002080080ce3,0x8040021000804020100804020102002080080ce3,0x140005000110004020104004102002080080de3,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x0],
[0xc00030001020040801100044020100800100e4,0x400010001020040801100044020100800000e4,0x0,0x0,0x0,0x20400010001020040801100044020100800000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc00030000a0002010084002104002100080ce3,0x0,0x140005000120004020104004104002100080de3,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0xc00030001020040801200048040201000100e4,0x400010001020040801200048040201000000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_169 : TreeBound (n := 4) 106 (programCode 0x4829075435) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080440040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_170 : TreeBound (n := 4) 106 (programCode 0x4829075436) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080442140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_171 : TreeBound (n := 4) 106 (programCode 0x4829075437) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080440040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_172 : TreeBound (n := 4) 106 (programCode 0x4829075438) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080442140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_173 : TreeBound (n := 4) 106 (programCode 0x4829075439) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080440040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_174 : TreeBound (n := 4) 106 (programCode 0x482907543a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce7204481,0x1080000210481,0x1081ce7204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0xc0003000086030180c04030102002080080ce3,0x8040021000800000000004000102002080080ce3,0x140005000106030180c04030102002080080ce3,0x80000220481,0x2818c6220481,0x80000220481,0x2818c6220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x8000a000201020040808008200220008804021e4],
[0x80006000101020040808008200220008804020e4,0xf303cc3cc1e60f30798000799e601e67980799e63cc00f6cc003cfcc00fa98f30798000fa98f30799556,0x8000a000201020040808008200220008804021e4,0x80022000201020040808008200220008804021e4,0x80012000401020040808008200220008804023e4,0x8000a004001020040808008200220008804020e4,0x80022000801020040808008200220008804025e4,0x8000a000201020040808008200220008804021e4,0x8004200100102004080800820022000880402de4,0x8010200100102004080800820022000880402de4,0x80082002001020040808008200220008804035e4,0x0,0x80102004001020040808008200220008804020e4,0x0,0x80202008001020040808008200220008804060e4,0x0,0xc0003000086030180c04030104002100080ce3,0x0,0x140005000106030180c04030104002100080ce3,0x80000220481,0x2818c6220481,0x80000220481,0x2818c6220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x80002000201020040808008200240009008040e4,0x80006000101020040808008200240009008040e4,0x0,0x8000a000201020040808008200240009008041e4,0x80022000201020040808008200240009008045e4,0x80012000401020040808008200240009008043e4,0x8000a008001020040808008200240009008041e4,0x80022000801020040808008200240009008045e4,0x8000a000201020040808008200240009008041e4,0x8004200100102004080800820024000900804de4,0x80202001001020040808008200240009008040e4,0x80082002001020040808008200240009008055e4,0x0,0x80102004001020040808008200240009008060e4,0x0,0x80202008001020040808008200240009008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_255 : TreeBound (n := 4) 106 (programCode 0x482907543b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10814a4204481,0x1081084210481,0x10814a4204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x1814a4220481,0x8040021000804040201004040102002080081ce3,0x1814a4220481,0x481084220481,0x2818c4220481,0x481084220481,0x2818c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x80400010001020040820000800020000800000e4],
[0x0,0x80448020022,0x0,0x80400010001020040820000800020000800000e4,0x0,0x80448020022,0x0,0x80448020022,0x840021000102004082004080102004080020de4,0x0,0x10400410001020040820080802020080800215e4,0x0,0x0,0x0,0x0,0x0,0x1814a4220481,0x0,0x1814a4220481,0x481084220481,0x2818c4220481,0x481084220481,0x2818c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x80448020022,0x0,0x0,0x0,0x80448020022,0x0,0x80448020022,0x840021000102004084004100104004100020de4,0x0,0x10400410001020040840081002040081000215e4,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_336 : TreeBound (n := 4) 106 (programCode 0x482907543c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080000210481,0x1080421204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x0,0x8040021000800000000004000102002080080ce3,0x0,0x80000220481,0x280840220481,0x80000220481,0x280840220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x8000a000201020040810008400220008804021e4],
[0x80006000101020040810008400220008804020e4,0xf303cc3cc1e60f30798000799e601e67980799e679800f4e6003d39800fa98f30798000fa98f30799556,0x8000a000201020040810008400220008804021e4,0x80022000201020040810008400220008804021e4,0x80012000401020040810008400220008804023e4,0x8000a004001020040810008400220008804020e4,0x80022000801020040810008400220008804025e4,0x8000a000201020040810008400220008804021e4,0x8004200100102004081000840022000880402de4,0x80102002001020040810008400220008804035e4,0x80082002001020040810008400220008804035e4,0x0,0x80102004001020040810008400220008804020e4,0x0,0x80202008001020040810008400220008804060e4,0x0,0x0,0x0,0x0,0x80000220481,0x280840220481,0x80000220481,0x280840220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x80002000201020040810008400240009008040e4,0x80006000101020040810008400240009008040e4,0x0,0x8000a000201020040810008400240009008041e4,0x80022000201020040810008400240009008045e4,0x80012000401020040810008400240009008043e4,0x8000a008001020040810008400240009008041e4,0x80022000801020040810008400240009008045e4,0x8000a000201020040810008400240009008041e4,0x8004200100102004081000840024000900804de4,0x80202002001020040810008400240009008040e4,0x80082002001020040810008400240009008055e4,0x0,0x80102004001020040810008400240009008060e4,0x0,0x80202008001020040810008400240009008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_417 : TreeBound (n := 4) 106 (programCode 0x482907543d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040080402004080108002200082ce3,0x8040200108040080402004080108002200082ce3,0x8000a00028040080402004080108002200082de3,0x8040200408040080402004080108002200082ce3,0x8001200048040080402004080108002200082ee3,0x8010200408040080402004080108002200082ce3,0x8002200088040080402004080108002200082ce3,0x8040200408040080402004080108002200082ce3,0x8004200108040080402004080108002200082ce3,0x0,0xc2002088000480402004080108002200082ce3,0x120442140442,0x142004088000880402004080108002200082ce3,0x120442140442,0x220442140442,0x220442140442,0x220442140442,0x220442140442,0x220442140442,0x420442140442,0x1048040208008080402004080108002200083ce3,0x420442140442,0x220442140442,0x7980799e601e61e601e600f33cc03ccf300799e711e2389f307980f31e9cc208f17001e9cc0003d0fbb6,0x7987981e600003cc0003cc0798f301e607983cc1e601e67980799e601e9cc003db3000f6cc001e833995,0x100000800800002001000008002000008000010008000080040000100080000200100100008100480820401000080000200200400000811000080044000008010000000401226baa8,0x0,0x88002208000480402004080108002200083ce3,0x8008020208004080402004080108002200083ce3,0x108004208000880402004080108002200083de3,0x8008080208010080402004080108002200083ce3],
[0x208008208001080402004080108002200083ee3,0x1008080208010080402004080108002200083ce3,0x408010208002080402004080108002200083ce3,0x2008080208010080402004080108002200083ce3,0x808020208004080402004080108002200083ce3,0x9008040208008080402004080108002200083ce3,0x1008040208008080402004080108002200083ce3,0x8008000208000080402004080108002200083ce3,0x2008080208010080402004080108002200083ce3,0x8000208000080402004080108002200083ce3,0x4008100208020080402004080108002200087ce3,0x0,0x0,0x0,0x120442140442,0x0,0x120442140442,0x220442140442,0x220442140442,0x220442140442,0x220442140442,0x220442140442,0x420442140442,0x0,0x420442140442,0x220442140442,0x100001000400004001000008001000010000020010000080040000100080000200100200010100880840600800110000400440400001011000084064000011010000040402227baa8,0x0,0x200001000800004001000008002000010000020010000080040000100080000200100200010100880840401000110000400440400001011000084044000011010000040402227baa8,0x8010200408040080402004080108002200082ce3,0x0,0x82002508000480402004080108002200082ce3],
[0x0,0x102004508000880402004080108002200082ce3,0x0,0x8404484410a2,0x24044a5414c2,0x40448040022,0x24044a5414c2,0x40448040022,0x8100204001020040804060801880062000a0de4,0x1008040208008080402004080108002200083ce3,0x101004040010200408040a08028800a2000a15e4,0x8404484410a2,0x8404484410a2,0x40448040022,0x8404484410a2,0x8020200808040080402004080108002200086ce3,0x0,0x0,0x0,0x0,0x0,0x8404484410a2,0x24044a5414c2,0x40448040022,0x24044a5414c2,0x40448040022,0x8200208001020040804061001880062000a0de4,0x0,0x102004080010200408040a10028800a2000a15e4,0x8404484410a2,0x8404484410a2,0x40448040022],
[0x8404484410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_514 : TreeBound (n := 4) 106 (programCode 0x482907543e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc0003008042010080404200108002200080ce3,0x0,0x180448084222,0x180448084222,0x180448080222,0x180448084222,0x840021008040000000004200100202008080ce3,0xc00030001020040820004800102004080402e4,0x180448084222,0xc00030001020040820004800104004100804e4,0x180448084222,0x180448290a82,0x0,0x180448290a82,0x0,0x0,0x0,0x0,0x140005008042010080404200108002200080ce3,0x0,0x180448084222,0x180448084222,0x180448080222,0x180448084222,0x0,0x1400050001020040820008800202008080403e4,0x180448084222,0x1400050001020040820008800204008100805e4,0x180448084222,0x180448290a82,0x40001000040000000004200101002040080ce3],
[0x180448290a82,0x40001000040000000004200102002080080ce3,0x0,0x40001000040000000004200104002100080ce3,0x0,0x240009008044020100804200108002200080ce3,0x0,0x800400018000000000004010108002200080ce3,0x2084485414c2,0x800800028000000000004010108002200080ce3,0x2084485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2,0x220448541502,0x8000208000000000004000108002200080ce3,0x220448541502,0x2504485414c2,0x2404485414c2,0x2504485414c2,0x2404485414c2,0x80448040022,0x0,0x400018000000000004010108002200080ce3,0x2084485414c2,0x800028000000000004010108002200080ce3,0x2084485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2],
[0x2104485414c2,0x2504485414c2,0x220448541502,0x8000208000000000004000108002200080ce3,0x220448541502,0x2504485414c2,0x2404485414c2,0x2504485414c2,0x2404485414c2,0x80448040022,0x840021000102004082004080108004200020de4,0x0,0x1000440018000000000004010108002200080ce3,0x80004800101020040820100804080102004020e4,0x1000840028000000000004010108002200080ce3,0x80008800201020040820100804080102004021e4,0x1001040048000000000004020108002200080ce3,0x1000040008000000000004000108002200080ce3,0x1002040088000000000004020108002200080ce3,0x1000040008000000000004000108002200080ce3,0x1004040108000000000004000108002200080ce3,0x8004080100102004082010080408010200402ce4,0x1008040208000000000004000108002200080ce3,0x80080802001020040820100804080102004034e4,0x0,0x1000040008000000000004000108002200080ce3,0x0,0x80200808001020040820100804080102004060e4,0x10400410001020040820080802080082000215e4,0x0,0x2000480018040402010084010108002200080ce3,0x8448040022],
[0x2000880028040804020104010108002200080de3,0x8448040022,0x448040022,0x10448040022,0x448040022,0x10448040022,0x448040022,0x404010100081004082002080488002200482ca4,0x0,0x4080102001020040820020800880022004034e4,0x448040022,0x8404484410a2,0x448040022,0x8404484410a2,0x0,0x800410018004020100804010108002200080ce3,0x8084484410a2,0x800810028004020100804010108002200080ce3,0x8084484410a2,0x8004484410a2,0x8104484410c2,0x8404484410a2,0x8104484410c2,0x8404484410a2,0x820448441102,0x8000208000000000004000108002200080ce3,0x820448441102,0x8004484410a2,0x8404484410a2,0x8404484410a2,0x8404484410a2,0x0],
[0x4000500018040402010084010108002200080ce3,0x0,0x4000900028040804020104010108002200080de3,0x0,0x448040022,0x8104484410c2,0x448040022,0x8104484410c2,0x448040022,0x0,0x0,0x0,0x448040022,0x40448040022,0x448040022,0x40448040022,0x0,0x0,0x8084484410a2,0x0,0x8084484410a2,0x8004484410a2,0x8104484410c2,0x8404484410a2,0x8104484410c2,0x8404484410a2,0x820448441102,0x0,0x820448441102,0x8004484410a2,0x8404484410a2,0x8404484410a2],
[0x8404484410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_675 : TreeBound (n := 4) 106 (programCode 0x482907543f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040100804004100108002200084ce3,0x0,0x80022001000c0100804004100100082002084ce3,0x802020010c040100804004100104002020084ce3,0x8002200100140100804004100100102004084ce3,0x0,0x8004200104040100804004100100202008084ce3,0x8000200108040100804004100100002100084ce3,0x8004200104040100804004100100402010084ce3,0x0,0x8020200104040100804004100100802020084ce3,0x400031001000002004000000010000020060003000020001000000020000200010002000010008000040008000080020000080620000101000000400000000400000001009087fda7,0x0,0x0,0x8004200108040100804004100102002080084ce3,0x0,0x8000200108040100804004100104002100084ce3,0x0,0x8000a00028040100804004100108002200084de3,0x0,0x80006008000c0100804004100100082002084ce3,0x1dcd6500000773597b9acbdcd6577359b73595dcd66dcd653b9aca00003b9acbdcd65ee6b2bb9acbdcd65ee6b36e6b29dcd65ee6b36e6b280ee6ee1aca03b9ae7cd6503b9ca6d6503b9ae7cd6503b9aca0000077359400001dcd6c735940ef59932800ee6b9f35940ef5b77aabfd99,0x8000a00800140100804004100100102004084de3,0x0,0x8020200804040100804004100100202008084ce3,0x0,0x8020200804040100804004100100402010084ce3,0x0,0x8020200804040100804004100100802020084ce3,0x400030001000010004000000010000100060003000020001000000020000200010002000010008000040008000080020000080600000101000000400000000400000001009087fda7,0x8000200800040100804004100101002040084ce3],
[0x0,0x0,0x0,0x0,0x0,0x8001200048040100804004100108002200084ee3,0x8000200808040100804004100108002200084ce3,0x8002200088040100804004100108002200084ce3,0x0,0x80402808000500804004100108002200084ce3,0x0,0x100804808000900804004100108002200084de3,0x0,0x10440040022,0x210440040022,0x10440040022,0x210440040022,0x10440040022,0x0,0x1008040808008100804004100108002200085ce3,0x0,0x10440040022,0x8104484410c2,0x10440040022,0x8104484410c2,0x8004200108040100804004100108002200084ce3,0x0,0x80022010800c0100804004100100082002084ce3,0x0,0x8002201080140100804004100100102004084ce3,0x0,0x8000201004040100804004100100202008084ce3],
[0x0,0x8000201004040100804004100100402010084ce3,0x0,0x8000201004040100804004100100802020084ce3,0x400020001000080004000000010000000060003000020001000000020000200010002000010008000040008000080020000080400000101000000400000000400000001009087fda7,0x8000201000040100804004100101002040084ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x88002208000500804004100108002200085ce3,0x0,0x108004208000900804004100108002200085de3,0x0,0x208008208001100804004100108002200085ee3,0x1008100208008100804004100108002200085ce3,0x408010208002100804004100108002200085ce3,0x8100208000100804004100108002200085ce3,0x808020208004100804004100108002200085ce3,0x0,0x1008040208008100804004100108002200085ce3,0x0,0x2008080208010100804004100108002200087ce3,0x8000208000100804004100108002200085ce3,0x4008100208020100804004100108002200085ce3,0x0,0x0,0xf30000b641e60f307980005b200016c81e60f3079801e7e60079bcc01e6003cfcc00f3f3003cdede5995,0x0,0xf3000222c1e60f3079800111600044581e60f3079801e7e60079bcc01e600f33cc03ccf300799ee07c55],
[0x0,0x0,0x0,0x0,0x0,0x0,0x4000004010000020040000080100000100000080040000400200001000800002001000012180d000486034000010000004040001002180c08008603010001000010000010208daea8,0xf300003cc1e60f307980001e600007981e60f3079801e7e60079bcc01e63cc03ccf300f31e601ede5995,0x0,0x0,0x0,0x0,0x0,0x8010200408040100804004100108002200086ce3,0x0,0x82002988000500804004100108002200084ce3,0x0,0x102004988000900804004100108002200084ce3,0x0,0x40440040022,0x240442140442,0x40440040022,0x240442140442,0x40440040022,0x0,0x1008040208008100804004100108002200085ce3,0x0,0x8404484410a2,0x8404484410a2,0x40440040022,0x8404484410a2,0x8020200808040100804004100108002200084ce3],
[0x0,0x0,0x0,0x0,0x0,0x40440040022,0x240442140442,0x40440040022,0x240442140442,0x40440040022,0x0,0x0,0x0,0x8404484410a2,0x8404484410a2,0x40440040022,0x8404484410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_820 : TreeBound (n := 4) 106 (programCode 0x4829075440) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80448000022,0x80448004022,0x80448000022,0x80448004022,0xc0003008040008040204200100202008080ee3,0x80448008022,0x80448000022,0x80448008022,0x80448000022,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x180448084222,0x180448084222,0x180448080222,0x180448084222,0x840021008040000000004200100202008080ce3,0xc00030001020040840005000102004080402e4,0x180448084222,0xc00030001020040840005000104004100804e4,0x180448084222,0x180448290a82,0x0,0x180448290a82,0x0],
[0x0,0x0,0x0,0x0,0x80448000022,0x180448084222,0x80448000022,0x180448084222,0x140005008040008040204200100202008080ee3,0x0,0x80448000022,0x0,0x80448000022,0x580448290a82,0x80448020022,0x580448290a82,0x0,0x80448020022,0x0,0x80448020022,0x0,0x180448084222,0x180448084222,0x180448080222,0x180448084222,0x0,0x1400050001020040840009000202008080403e4,0x180448084222,0x1400050001020040840009000204008100805e4,0x180448084222,0x180448290a82,0x40001000040000000004200101002040080ce3],
[0x180448290a82,0x40001000040000000004200102002080080ce3,0x0,0x40001000040000000004200104002100080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x448040022,0xa104485414c2,0x448040022,0xa104485414c2,0x448040022,0x804010100102004084004100108004200020de4,0x0,0x10080102001020040840081002080082000215e4,0x448040022,0x8404484410a2,0x448040022,0x8404484410a2,0x0,0x0,0x2084485414c2,0x0,0x2084485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2],
[0x220448541502,0x0,0x220448541502,0x2504485414c2,0x2404485414c2,0x2504485414c2,0x2404485414c2,0x80448040022,0x0,0x0,0x2084485414c2,0x0,0x2084485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2,0x2104485414c2,0x2504485414c2,0x220448541502,0x0,0x220448541502,0x2504485414c2,0x2404485414c2,0x2504485414c2,0x2404485414c2,0x80448040022,0x840021000102004084004100108004200020de4,0x0,0x10400410000c0402010084200100082002080ce3,0x1040041000040000000004200100002020080ce3,0x1040041000140804020104200100102004080de3,0x1040041000040000000004200100002000080ce3],
[0x0,0x0,0x1040041000040000000004200100402010080ce3,0x0,0x1040041000040000000004200100802020080ce3,0x840101000102004084004100100804020020de4,0x1040041000040000000004200101002040080ce3,0x10401010001020040840081002010080400215e4,0x0,0x0,0x401010001020040840001000000002000000e4,0x0,0x10400410001020040840081002080082000215e4,0x0,0x2000480018050080402004200108002200082ce3,0x8448040022,0x2000880028050080402004200108002200082de3,0x8448040022,0x448040022,0x10448040022,0x448040022,0x10448040022,0x448040022,0x4010100081004082000100488000200482ca4,0x0,0x80102001020040840001000080002000000e4,0x448040022,0x8404484410a2,0x448040022,0x8404484410a2,0x0,0x800410018040000000004200108002200080ce3],
[0x8084484410a2,0x800810028040000000004200108002200080ce3,0x8084484410a2,0x8004484410a2,0x8104484410c2,0x8404484410a2,0x8104484410c2,0x8404484410a2,0x820448441102,0x0,0x820448441102,0x8004484410a2,0x8404484410a2,0x8404484410a2,0x8404484410a2,0x0,0x4000500018060100804004200108002200084ce3,0x0,0x4000900028060100804004200108002200084de3,0x0,0x448040022,0x8104484410c2,0x448040022,0x8104484410c2,0x448040022,0x0,0x7980799e601e63cc03cfcc0f30f307981e60f3079801e7e6007a73001e9cc003db3000f6cc001eed8995,0x0,0x448040022,0x40448040022,0x448040022,0x40448040022],
[0x0,0x0,0x8084484410a2,0x0,0x8084484410a2,0x8004484410a2,0x8104484410c2,0x8404484410a2,0x8104484410c2,0x8404484410a2,0x820448441102,0x0,0x820448441102,0x8004484410a2,0x8404484410a2,0x8404484410a2,0x8404484410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4 : TreeBound (n := 4) 106 (programCode 0x48290754) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part011_5 part011_6 part011_87 part011_88 part011_169 part011_170 part011_171 part011_172 part011_173 part011_174 part011_255 part011_336 part011_417 part011_514 part011_675 part011_820

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1029 : TreeBound (n := 4) 106 (programCode 0x48290755) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201000240008048004200108002200080ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1030 : TreeBound (n := 4) 106 (programCode 0x48290756) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201008040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1031 : TreeBound (n := 4) 106 (programCode 0x48290757) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201000440010088004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1032 : TreeBound (n := 4) 106 (programCode 0x48290758) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201008040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1033 : TreeBound (n := 4) 106 (programCode 0x48290759) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201000840020108004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1035 : TreeBound (n := 4) 106 (programCode 0x4829075a31) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce1204481,0x1081081210481,0x1081ce1204481,0x1081ce1204481,0x10818c1208481,0x10818c1218481,0x10818c1208481,0x1080001200481,0x1081081210481,0x1080001200481,0x1081081210481,0x1080001200481,0x0,0x100bde1220501,0x1023181220501,0x100bde1220501,0x8040200010c90032190084002102002080080ce3,0x10139c1220501,0x10739c1220501,0x10139c1220501,0x1042101220501,0x1023181220501,0x1000101220501,0x1023181220501,0xf307983cc1e60f300003cc35280000f30000000003d398007a73000f4e7e6003cfcc00f379801e870925,0x1042101220501,0xf307983cc1e60f300003cc35280000f30000000003d398007a73000f4e7e6003cfcc00f379801e870925,0x1042101220501,0xf307983cc1e60f300003cc35280000f30000000003d398007a73000f4e7e6003cfcc00f379801e870925,0x0,0x1001040120022],
[0x80006000108010200800822820820500804120a4,0x8000a00020802020100084002108002010080ce3,0xf3000222c00088b0000f6cc03ccf300f30f301fccdb2f300799e600007b662d9bdd80000798003cc3cb6,0x1011042120442,0x1011042120442,0x1001040120022,0x1011042120442,0x1011042120442,0x1021046120c82,0x1031046120c82,0x1021046120c82,0x8010200402010080400084002108002080082ce3,0x80102004008020200820022800820400804020e4,0x8020200804020100800084002108002100084ce3,0x80202008008020200840023000820400808040e4,0x0,0x100bde1220501,0x1023181220501,0x100bde1220501,0x0,0x10139c1220501,0x10739c1220501,0x10139c1220501,0x1042101220501,0x1023181220501,0x1000101220501,0x1023181220501,0x8000201000020000800084002102001100084ca3,0x1042101220501,0x0,0x1042101220501,0x0],
[0x0,0x1001040120022,0x80006000108010200800823020820601008140a4,0x0,0x80006000208010200800823060820701008140a4,0x1011042120442,0x1011042120442,0x1001040120022,0x1011042120442,0x1011042120442,0x1021046120c82,0x1031046120c82,0x1021046120c82,0x0,0x80102004008020200820022800840401004020e4,0x0,0x80202008008020200840023000840401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1116 : TreeBound (n := 4) 106 (programCode 0x4829075a32) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010008020200800820020880402000100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1117 : TreeBound (n := 4) 106 (programCode 0x4829075a33) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce1204481,0x1081081210481,0x1081ce1204481,0x1081ce1204481,0x10818c1208481,0x10818c1218481,0x10818c1208481,0x1080001200481,0x1081081210481,0x1080001200481,0x1081081210481,0x1080001200481,0x0,0x100bde1220501,0x1023181220501,0x100bde1220501,0x8040200020d100341a0104004102002080080de3,0x10139c1220501,0x10739c1220501,0x10139c1220501,0x1042101220501,0x1023181220501,0x1000101220501,0x1023181220501,0x0,0x1042101220501,0x0,0x1042101220501,0x0,0x0,0xc0003000802020100104004100402200080ce3],
[0xc00030008020200800820820820104800100e4,0x81040120022,0x4002a0000000a800040002000000018000436421b2004000200400000041000080000002010000008020000004080000020080402400101000000400008000210000001001087f8a7,0x281042120442,0x281042120442,0x81040120022,0x281042120442,0x281042120442,0x481044120882,0x481044120882,0x481044120882,0x0,0x0,0x0,0x0,0x0,0x100bde1220501,0x1023181220501,0x100bde1220501,0x0,0x10139c1220501,0x10739c1220501,0x10139c1220501,0x1042101220501,0x1023181220501,0x1000101220501,0x1023181220501,0x8000201000020000000104004104002100080ce3,0x1042101220501,0x0,0x1042101220501,0x0],
[0x0,0x0,0xc00030008020200800821020840205000100e4,0x81040120022,0x0,0x281042120442,0x281042120442,0x81040120022,0x281042120442,0x281042120442,0x481044120882,0x481044120882,0x481044120882,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1198 : TreeBound (n := 4) 106 (programCode 0x4829075a34) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce1204481,0x1080000210481,0x1081ce1204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x0,0x8040021000000000000804020102002080080ce3,0x0,0x80000220481,0x2818c2220481,0x80000220481,0x2818c2220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x10490411212a2],
[0x10090411212a2,0x0,0x10090411212a2,0x10590411212c2,0x10110411212c2,0x10490411212a2,0x10110411212c2,0x10110411212c2,0x1021041121302,0x1029041121302,0x1021041121302,0x0,0x10410411212a2,0x0,0x10410411212a2,0x0,0x0,0x0,0x0,0x80000220481,0x2818c2220481,0x80000220481,0x2818c2220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x10490411212a2,0x10090411212a2,0x0,0x10090411212a2,0x10590411212c2,0x10110411212c2,0x10490411212a2,0x10110411212c2,0x10110411212c2,0x1021041121302,0x1029041121302,0x1021041121302,0x0,0x10410411212a2,0x0,0x10410411212a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1279 : TreeBound (n := 4) 106 (programCode 0x4829075a35) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10818c2240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1280 : TreeBound (n := 4) 106 (programCode 0x4829075a36) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1281 : TreeBound (n := 4) 106 (programCode 0x4829075a37) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10818c2240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1282 : TreeBound (n := 4) 106 (programCode 0x4829075a38) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1283 : TreeBound (n := 4) 106 (programCode 0x4829075a39) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1284 : TreeBound (n := 4) 106 (programCode 0x4829075a3a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1285 : TreeBound (n := 4) 106 (programCode 0x4829075a3b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1286 : TreeBound (n := 4) 106 (programCode 0x4829075a3c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1287 : TreeBound (n := 4) 106 (programCode 0x4829075a3d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x181ce8240481,0x8040021000004000002004080108002200080ce3,0x181ce8240481,0x0,0x8000480010c90032192004080108002200080ce3,0x109040140022,0x8000880020d100341a2004080108002200080de3,0x109040140022,0x111042140442,0x111042140442,0x101040140022,0x111042140442,0x111042140442,0x121042140442,0x131042140442,0x121042140442,0x101040140022,0x16c87985b200003cc0003cc2d900001e600000007980798f300f31e601e9cc003db3000f6cc001ea56925,0x8020080804010100802004080108002200084ce3,0x0,0x2818c8240481,0x8040001000000000002004080108002200080ce3,0x2818c8240481,0x80008240481,0x481088240481,0x80008240481,0x481088240481,0x80008240481,0x0,0x80bde8240501,0x9040140022],
[0x80bde8240501,0x9040140022,0x8139c8240501,0x842108240501,0x8139c8240501,0x842108240501,0x823188240501,0x800108240501,0x823188240501,0x842108240501,0x842108240501,0x800108240501,0x842108240501,0x842108240501,0x0,0x6098c8240481,0x20004800108020200800820020880402000100e4,0x6098c8240481,0x7980020460007b66000f6cc03ccf300f30f301f535b2f300799e600007d4c1e6c5700003cc0003cc3cb6,0x411088240481,0x8240481,0x411088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0],
[0x80bde8240501,0x0,0x80bde8240501,0x0,0x8139c8240501,0x842108240501,0x8139c8240501,0x842108240501,0x823188240501,0x800108240501,0x823188240501,0x842108240501,0x842108240501,0x800108240501,0x842108240501,0x842108240501,0x0,0x0,0x40005000108020200800820020880402000100e4,0x0,0x0,0x8139c8240501,0x8240481,0x8139c8240501,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40008240481,0x8240481,0x40008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1384 : TreeBound (n := 4) 106 (programCode 0x4829075a3e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1098c2240481,0xc00024008020200820020800880006004020e4,0x1098c2240481,0x140004020802020082002080088000a004021e4,0x2098c6240481,0x6098c6240481,0x2098c6240481,0x6098c6240481,0x4098c6240481,0x6098c6240481,0x4098c6240481,0x6098c6240481,0x798001ed98002046000bbca4e422bf007aafc97e232698003d3980f31e9cc003db3000f6cc001e64dcf5,0x6098c6240481,0x798002046000222c000bbc68223cbf007aafc97e223398003d3980f31e9cc003db3000f6cc001e64dcf5,0x0,0x80006000108020200820020800880402004020e4,0x0,0x1098c2240481,0x0,0x1098c2240481,0x0,0x2098c6240481,0x6098c6240481,0x2098c6240481,0x6098c6240481,0x4098c6240481,0x6098c6240481,0x4098c6240481,0x6098c6240481],
[0x0,0x6098c6240481,0x0,0x0,0x0,0x8000804020802020082002080088000a004021e4,0x1090481412a2,0x80008000208020200820020800880002004021e4,0x1090481412a2,0x3090481416c2,0x2090481414c2,0x8090481410a2,0x2090481414c2,0x2090481414c2,0x409048141902,0xc09048141902,0x409048141902,0x9090481412a2,0x8090481410a2,0x0,0x8090481410a2,0x80022000808020200820020800880402004024e4,0x80012000408020200820020800880402004026e4,0x80402004008020200820020800880402004020e4,0x80022000808020200820020800880402004024e4,0x80022000808020200820020800880402004024e4,0x8004200100802020082002080088040200402ce4,0x80042004008020200820020800880402004020e4,0x80082002008020200820020800880402004034e4,0x0,0x143dea240501,0x1490481412a2],
[0x143dea240501,0x1490481412a2,0x2418cc240481,0x842108240501,0x2418cc240481,0x40008240481,0x44108c240481,0x40008240481,0x44108c240481,0x40008240481,0x842108240501,0x842108240501,0x842108240501,0x40008240481,0x80102004008020200820020800880402004020e4,0x0,0x143dea240501,0x0,0x143dea240501,0x0,0x2418cc240481,0x842108240501,0x2418cc240481,0x40008240481,0x44108c240481,0x40008240481,0x44108c240481,0x40008240481,0x842108240501,0x842108240501,0x842108240501,0x40008240481],
[0x80202008008020200820020800880402004060e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1481 : TreeBound (n := 4) 106 (programCode 0x4829075a3f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x181ce8240481,0x0,0x6818c8204481,0x481088210481,0x6818c8204481,0x0,0x481088208481,0xc00030008020200802022000802400080406e4,0x481088208481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x0,0x0,0x0,0x0,0x181ce8240481,0x0,0xc0101000c00430184004100100082002080ce3,0x40101000000000004004100100002020080ce3,0x140101000c00830184004100100102004080ce3,0x40101000000000004004100100002100080ce3,0x0,0x1400050008020200802022000802400080406e4,0x0,0x40101000000000004004100100002000080ce3,0x40101000000000004004100100802020080ce3,0x40101000000000004004100100002000080ce3,0x40101000000000004004100101002040080ce3],
[0x40101000000000004004100100002000080ce3,0x0,0x0,0x40101000000000004004100104002100080ce3,0x0,0x2818c8240481,0x0,0x709ce8240481,0x0,0x709ce8240481,0x0,0x6118c8240481,0x8240481,0x6118c8240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x2818c8240481,0x80008240481,0x481088240481,0x80008240481,0x481088240481,0x80008240481,0x0,0x80bde8240501,0x2040080100810020104004100108002200080ce3],
[0x80bde8240501,0x0,0x8139c8240501,0x842108240501,0x8139c8240501,0x842108240501,0x823188240501,0x800108240501,0x823188240501,0x842108240501,0x842108240501,0x800108240501,0x842108240501,0x842108240501,0x0,0x6098c8240481,0x20004800108010200820022800880502004020a4,0x6098c8240481,0x0,0x411088240481,0x8240481,0x411088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0],
[0x80bde8240501,0x0,0x80bde8240501,0x0,0x8139c8240501,0x842108240501,0x8139c8240501,0x842108240501,0x823188240501,0x800108240501,0x823188240501,0x842108240501,0x842108240501,0x800108240501,0x842108240501,0x842108240501,0x0,0x0,0x2000500010801020082002300088050200c060a4,0x0,0x7980020460007d4c000f3f303cc3cc0f30f301ed98007b66001f530007d4c0f30f307983cc0f3079d756,0x8139c8240501,0x8240481,0x8139c8240501,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40008240481,0x8240481,0x40008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1610 : TreeBound (n := 4) 106 (programCode 0x4829075a40) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf3000222c0002d90000bbc68223cbf007aafc98d33d39bcc0079800f4e600f33cc00f3f3003cde64dcf5,0x80202018008020200840021000800c00028040e4,0x0,0x0,0x80022010808020200840021000804400108044e4,0x80022010808020200840021000802400088044e4,0x0,0x80022010808020200840021000804400108044e4,0x80022010808020200840021000804400108044e4,0x80022010808020200840021000808400208044e4,0x80022010808020200840021000808401008044e4,0x80022010808020200840021000810400408044e4,0x0,0x0,0x0,0x80002010008020200840021000840401008040e4,0x80006000108020200840021000880402008040e4,0x0,0x400000005000000024000000090000000140002000101208000404800012012000900002410010000040040000020000090080000200040000800200000400800001001000485ee27,0x80006010008020200840021000800c00028040e4,0x0,0x0,0x0,0x80202010008020200840021000802400088040e4,0x0,0x80202010008020200840021000804400108040e4,0x80202010008020200840021000804400108040e4,0x8004201000802020084002100080840020804ce4,0xf3001e9cc1eda73079800f301e63cc0f30f301e9cc007b66001e9cc00798f4e6003d3982d90f307e5486,0x8004201000802020084002100081040040804ce4],
[0x0,0x0,0x0,0x0,0x0,0x0,0x1090481412a2,0x0,0x1090481412a2,0x3090481416c2,0x2090481414c2,0x8090481410a2,0x2090481414c2,0x2090481414c2,0x409048141902,0xc09048141902,0x409048141902,0x9090481412a2,0x8090481410a2,0x0,0x8090481410a2,0x80002000808020200840021000880402008040e4,0x80012000408020200840021000880402008046e4,0x0,0x0,0x1490481412a2,0x0,0x1490481412a2,0x210000240481,0x10000240481,0x210000240481,0x10000240481],
[0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x8139c8240501,0x410000240481,0x8139c8240501,0x10000240481,0x80022000808020200840021000880402008044e4,0x80022000808020200840021000880402008044e4,0x8004200100802020084002100088040200804ce4,0x8004200800802020084002100088040200804ce4,0x80082002008020200840021000880402008054e4,0x0,0x0,0x1490481412a2,0x0,0x1490481412a2,0x2418c2240481,0x40000240481,0x2418c2240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x80102004008020200840021000880402008060e4,0x0],
[0x0,0x0,0x0,0x0,0x2418c2240481,0x40000240481,0x2418c2240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x80202008008020200840021000880402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1034 : TreeBound (n := 4) 106 (programCode 0x4829075a) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part011_1035 part011_1116 part011_1117 part011_1198 part011_1279 part011_1280 part011_1281 part011_1282 part011_1283 part011_1284 part011_1285 part011_1286 part011_1287 part011_1384 part011_1481 part011_1610

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1724 : TreeBound (n := 4) 106 (programCode 0x4829075b31) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10810a1204481,0x1081081210481,0x10810a1204481,0x10810a1204481,0x10810c1208481,0x10810c1218481,0x10810c1208481,0x1081081210481,0x1081081210481,0x1081081210481,0x1081081210481,0x1081081210481,0x0,0x1009181220501,0x1021181220501,0x1009181220501,0x8040200011010040200084002102002080083ce3,0x1011181220501,0x1071181220501,0x1011181220501,0x1061181220501,0x1021181220501,0x1061181220501,0x1021181220501,0xf307983cc00f3f3003cc1e60f30798f301e60f3000f4e600f4e6000f4e679801ed980079f9801e963055,0x1041181220501,0x0,0x1041181220501,0x0,0x0,0x1000040020022],
[0xf3000222c00088b0000dc4affcde600f3003cdf5358495f83cc00000001e6315c7980000798000001e56,0x8000a00021002040200084002108002010081ce3,0xf3000222c00088b00014e2f33d39800f300799f534825e6079800000001e62d907980000798000001e56,0x1000040020022,0x1010842020442,0x1000040020022,0x1010842020442,0x1000040020022,0x1021846120c82,0x1000040020022,0x1021846120c82,0x8010200401010040200084002108002080083ce3,0x0,0x8020200801020040200084002108002100085ce3,0x0,0x0,0x1009181220501,0x1021181220501,0x1009181220501,0x0,0x1011181220501,0x1071181220501,0x1011181220501,0x1061181220501,0x1021181220501,0x1061181220501,0x1021181220501,0x8004201300820040a00084002102001100085ca3,0x1041181220501,0x0,0x1041181220501,0x0],
[0x0,0x1000040020022,0x400021401000002004000210010000020000800100008000400008021400020001000001008000001008000010080000010080400000041020000404000000400800001003085b1a7,0x0,0x0,0x1000040020022,0x1010842020442,0x1000040020022,0x1010842020442,0x1000040020022,0x1021846120c82,0x1000040020022,0x1021846120c82,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1805 : TreeBound (n := 4) 106 (programCode 0x4829075b32) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079803cde600f303cc1e60f3f3001e9cc007983cc1e9cc003db3000f6cc001e6c7195]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1806 : TreeBound (n := 4) 106 (programCode 0x4829075b33) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10810a1204481,0x1081081210481,0x10810a1204481,0x10810a1204481,0x10810c1208481,0x10810c1218481,0x10810c1208481,0x1081081210481,0x1081081210481,0x1081081210481,0x1081081210481,0x1081081210481,0x0,0x1009181220501,0x1021181220501,0x1009181220501,0x8040200021010040200104004102002080083de3,0x1011181220501,0x1071181220501,0x1011181220501,0x1061181220501,0x1021181220501,0x1061181220501,0x1021181220501,0x0,0x1041181220501,0x0,0x1041181220501,0x0,0x0,0xc0003001002040200104004100402200081ce3],
[0x79f983cc1e6003d39801e7e600f303cc1e60f3001e7e600f379801e7e9cc001e67980f6cc001e6c6c85,0x80040020022,0x62b83cc1e600062b801e7e600f3016c9e60f3001e7e600f379801e7e9cc001e62d90f6cc001e6e5285,0x80040020022,0x280842020442,0x80040020022,0x280842020442,0x80040020022,0x481044120882,0x80040020022,0x481044120882,0x0,0x0,0x0,0x0,0x0,0x1009181220501,0x1021181220501,0x1009181220501,0x0,0x1011181220501,0x1071181220501,0x1011181220501,0x1061181220501,0x1021181220501,0x1061181220501,0x1021181220501,0x8008201201020040200104004104002100085ce3,0x1041181220501,0x0,0x1041181220501,0x0],
[0x0,0x0,0x109cf983cc1e6003d39803ce0460f303cc1e60f3003cde600f379801e7ea08c03cc7980f6cc001e6c7195,0x80040020022,0x0,0x80040020022,0x280842020442,0x80040020022,0x280842020442,0x80040020022,0x481044120882,0x80040020022,0x481044120882,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1887 : TreeBound (n := 4) 106 (programCode 0x4829075b34) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10810a1204481,0x1081084210481,0x10810a1204481,0x1081080200481,0x1081080208481,0x1081084210481,0x1081080208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x0,0x8040021001008040200804020102002080081ce3,0x0,0x81080220481,0x2810c2220481,0x481084220481,0x2810c2220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x0],
[0x614f4c000000afb2bb000000164cd6c0000001853d30000000614f4c000000081bf10000000567f6ad0427f759fdab3fb002b3fb2b42ba7acc1f3ab4517f60000159fd8002b3fb159fd800676442453d30159fd8000000164cd6c00000019d910914f4c0afb2bb0000000b7ceac0159fd80000002b3fb040df880567f602b3fb00567f62df3b1164ebd80acfec0159fd80000567f602d24fa84ac,0x200000000800040002000100008000000100040000200103000000800004001000009800000028000000118000000260000400200008000400010000800010000000000051ea8,0x0,0x0,0x0,0x0,0x0,0x77447ab2801dd11eaca0077447ab28077394daca0077447ab2803b9ad8e6b2f7368624d4bdcd65ee6b2bb9bbe01aaf3b9acbdcf42c4bb2bb9ad8e6b28ee6b639aca3ba24c3ff2bb9cab7e67cbb9acdb9aca0ee729b5941dd4d8594007735a2e6b28eee25d94000ee747fc7aac59,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81080220481,0x2810c2220481,0x481084220481,0x2810c2220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x614f4c000000afb2bb0000000614f4c0000001853d30000000614f4c000000081bf10000000567f6ad0427f600002b3fb002b3fb2b40067fcc1f3ab4517f60000159fd8002b3fb159fd80061fc4c453d30159fd8000000164cd6c000000187f13114f4c0afb2bb0000000b7ceac0159fd80000000567f602b3fb0567f602b3fb00567f62df3b117a8bb0159fd802b3fb00000567f602d24f6b8ac,0x200000000800000002000100008000000100040000200101800000800004001000008c0000002800000010c000000230000800200002000100010000800020000000000051ea8,0x0,0x0,0x0,0x0,0x0,0x77447ab2801dd11eaca0077447ab28077394daca0077447ab280ee6b2bb9acbdce54599345cd662a05f5b9bb959932bb9acbdcf458ffca3b9ad8e6b28ee6b639aca3ba23d59403b9caa8ffca3b9acdb9aca3b9b501c46877ad052eca7735a2e6b28eee25d94000ee747fd31c759,0x0,0x20000000880002000200000008800000000010000080010200000100000800100002200000002c000000210000000240002000100002000800020001000020000000000079ba8,0x7736826b281dcda09aca00ee7a0eb280ee6ee1aca00ee7a0eb28000000077360b35941dcd650b2d06cf59932800ee6b283b9ad8e6b29dcd82cd6507aef40a000051f6b296503d77a050000430e237b9acbdcd65ee6b2f735947735d0897139ff97b9aca773594ee6b2faf2d2193a,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1968 : TreeBound (n := 4) 106 (programCode 0x4829075b35) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10810c2240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1969 : TreeBound (n := 4) 106 (programCode 0x4829075b36) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081084240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1970 : TreeBound (n := 4) 106 (programCode 0x4829075b37) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10810c2240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1971 : TreeBound (n := 4) 106 (programCode 0x4829075b38) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081084240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1972 : TreeBound (n := 4) 106 (programCode 0x4829075b39) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081084240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1973 : TreeBound (n := 4) 106 (programCode 0x4829075b3a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081084240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1974 : TreeBound (n := 4) 106 (programCode 0x4829075b3b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081084240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1975 : TreeBound (n := 4) 106 (programCode 0x4829075b3c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081084240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1976 : TreeBound (n := 4) 106 (programCode 0x4829075b3d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1810a8240481,0x8040021001004040202004080108002200081ce3,0x1810a8240481,0x0,0x8000480011010040202004080108002200083ce3,0x108040040022,0x8000880021010040202004080108002200083de3,0x108040040022,0x100040040022,0x110040040022,0x100040040022,0x110040040022,0x100040040022,0x120842040442,0x100040040022,0x120842040442,0x100040040022,0x0,0x8020080801010040202004080108002200087ce3,0x0,0x2810c8240481,0x8040041001008040202004080108002200081ce3,0x2810c8240481,0x481088240481,0x481088240481,0x481088240481,0x481088240481,0x481088240481,0x0,0x809188240501,0x8040040022],
[0x809188240501,0x8040040022,0x811188240501,0x861188240501,0x811188240501,0x861188240501,0x821188240501,0x861188240501,0x821188240501,0x861188240501,0x841188240501,0x801188240501,0x841188240501,0x841188240501,0x0,0x6090c8240481,0x7980020460007b66000b64f33db3000f3003cdf5344580003cc00000003cc1e60f300003cc0000001e56,0x6090c8240481,0x7980020460007b660012fcf33db3000f300799f53445800079800000003cc1e60f300003cc0000001e56,0x411088240481,0x421088240481,0x411088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x841188240501,0x1088240481,0x841188240501,0x1088240481,0x0],
[0x809188240501,0x0,0x809188240501,0x0,0x811188240501,0x861188240501,0x811188240501,0x861188240501,0x821188240501,0x861188240501,0x821188240501,0x861188240501,0x841188240501,0x801188240501,0x841188240501,0x841188240501,0x0,0x0,0x400020001000002004080200000800020000800100008000400008021000020001001000008001000008010000080010000080400000041000000404000000410000001003085b1a7,0x0,0x0,0x811188240501,0x421088240481,0x811188240501,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x41088240481,0x1088240481,0x41088240481],
[0x1088240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2073 : TreeBound (n := 4) 106 (programCode 0x4829075b3e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1090c2240481,0xf30000b640001e9cc007d4e0460f303cc1e60f3f3001e61e607980f31e9cc003db3000f6cc001e6c7195,0x1090c2240481,0x0,0x2090c6240481,0x6090c6240481,0x2090c6240481,0x6090c6240481,0x4090c6240481,0x6090c6240481,0x4090c6240481,0x6090c6240481,0x1e600081180020460007d4de600f30007b660f3000f4e6003d3980f31e9cc003db3000f6cc001e6c7195,0x6090c6240481,0x79800097e000222c0007d4de600f30007b660f3000f4e6003d3980f31e9cc003db3000f6cc001e6c7195,0x0,0x0,0x40000004100000080400000041000002d00040010000800040000402160002008100400000200040000804000008010f00008000004002000010040000100020000100100308430a7,0x400001001000002004000010010000020000800000008000400008020400020001004000008000000008040000080008000080020000040040000400200000400400001003085b1a7,0x40000002100000200400000041000002900040010000800040000802160002008100400000200040000804000008010f00008000004002000080040000080040000200100308431a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x1dcd6500000773597c4d9c3ad6501dcddc359400001dcd6500ee6b36e6b2800003b9bba47fe6dcd65ee6b2bb9acbdcd653b9acbdcf41d6500ee72c80d57f7359400001dcddc359403b9ad1735943ba23d594003bb94a355e0ee6b28000077536165000ee6d04d6500ee747fd5e1ee9,0x40000000100000080400000001000002800040000000800040000402020002008100400000200000000804000008010a00008004000002080000040040000020200000100308430a7,0x1dcd6500000773597c4d9c3ad6501dcddc359400001dcd6500ee6b36e6b2800003b9bba47fe6dcd65ee6b2bb9acbdcd653b9acbdcf41d6500ee72c80d57f7359400001dcddc359403b9ad1735943ba23d594003bb94a355e0ee6b28000077536165000ee6d04d6500ee747fd5e1ee9,0x0,0x1090c2240481,0x0,0x1090c2240481,0x0,0x2090c6240481,0x6090c6240481,0x2090c6240481,0x6090c6240481,0x4090c6240481,0x6090c6240481,0x4090c6240481,0x6090c6240481,0x1e6001ed98007b66000f6cde600f3000f4e60f3001e7e60079f981e61e9cc003db3000f6cc001e6e75f5,0x6090c6240481,0x7980020460007d4c000f6cde600f3001e7e60f3003cde600f37981e61e9cc003db3000f6cc001e6e9455,0x0,0x0,0x0,0x1dcd6500773d07597c3eb588565f0fad6215940ee6d04d65f047fe5ee6b2800003b9bbafacecbcd65ee6b287744a3aceb1b9e8589941d6501dcddd7d675e7359400001dcddc359403b9cabf59d5fba24112eca3bb8e959d5cee6b45cd6577360b359401dcddc35940ee747fd712d09,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0xf3000408c0010230003cfcde600f303cc1e60f3f3001e9cc007983cc1e9cc003db3000f6cc001e6c7195,0xf30811bcc0000f3003cc3ce0460f300001e60f4023079bcc007980001e9cc003db3000f6cc001e6c74f5,0xf3000f6cc003db300079bcde600f303cc1e60f3f3001e9cc007983cc1e9cc003db3000f6cc001e6c7195,0xf30811bcc0000f3003cc3ce0460f300001e60f4023079bcc007980001e9cc003db3000f6cc001e6c74f5,0x0,0x1210c6240481,0x400000201000000804000002000100008002002000008000200010000800020001004000002010000008000800020002000080400000101000000404000000810000001001c873227,0x1210c6240481,0x0,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x821084240481,0x421084240481,0x821084240481,0x421084240481,0xf30811bcc0000f3000003ce0460f300001e60f4023079bcc007980001e9cc003db3000f6cc001e6c74f5,0x0,0x1210c6240481,0x0,0x1210c6240481,0x220000000220000002000040002200040000010040000010000080100400000101000200044000a0011000080001000200040000000500008001400000005000000010000f9ba8],
[0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x821084240481,0x421084240481,0x821084240481,0x421084240481,0x0,0x1310c6240481,0x0,0x1310c6240481,0x20100000020100000201000000201004000001004000001000008010040000010100020004400081011000004001000010040000000500008001400000005000000010000f9ba8,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x821084240481,0x421084240481,0x821084240481,0x421084240481,0x0,0x1411ea240501,0xf300f33cc03cc03ccf303ce0460f301e61e60f3f3001e61e60799e601e9cc003db3000f6cc001e6c7195],
[0x1411ea240501,0x0,0x2410cc240481,0xc4118c240501,0x2410cc240481,0x44108c240481,0x44108c240481,0x44108c240481,0x44108c240481,0x44108c240481,0x841188240501,0x841188240501,0x841188240501,0x41088240481,0x0,0x1310c6240481,0x1dcd65f04805d2402e91ff97b9aca0007823ff36e6b29dcd6500000ee6b2800003b9bba47fe6dcd65ee6b2bb9acbdcd653b9acbdcf458ffcbdcddd23ff2f73594000007735b1cd653b9aca000003ba23d594003bb89765000eee25d940077536165000eee25d94000ee747fd712219,0x1310c6240481,0x400020001000080004000000000000000002002100008000000010000800020001004000010010000040000000040000000080400000101000000404000000810000001001887fe67,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x801080240481,0x1080240481,0x801080240481,0x1080240481,0x0],
[0x1411ea240501,0x0,0x1411ea240501,0x0,0x2410cc240481,0xc4118c240501,0x2410cc240481,0x44108c240481,0x44108c240481,0x44108c240481,0x44108c240481,0x44108c240481,0x841188240501,0x841188240501,0x841188240501,0x41088240481,0x0,0x0,0x1dcd6501dcddd2402e91ff97b9acbdcddc35940ee6b29dcd6500000ee6b2800003b9bba47fe6dcd65ee6b2bb9aca000003b9acbdcf458ffcbdcddd23ff2f7359400001dcd66dcd653b9aca000003ba23d594003bb89765000eee25d940077536165000eee25d94000ee747fd7131b9,0x0,0x400020001000080004000000000000000002002100008000000010000800020001004000010010000040000000040000000080400000101000000404000000810000001001887fe67,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x841188240501,0x1080240481,0x841188240501],
[0x1080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2266 : TreeBound (n := 4) 106 (programCode 0x4829075b3f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1810a8240481,0x0,0x6810c8204481,0x481088210481,0x6810c8204481,0x0,0x481088208481,0xf307980001e6003d39803cde600f300001e60f379801e7e60079bcc01e9cc003db3000f31e601e6c7195,0x481088208481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x0,0x0,0x0,0x0,0x1810a8240481,0x0,0xc0101001000440204004100100082002081ce3,0x1040101001008040204004100101002020081ce3,0x140101001000840204004100100102004081de3,0x40101001000040204004100100002100081ce3,0x0,0x0,0x0,0x1040101001008040204004100101002040081ce3,0x1040101001008040204004100100802020081ce3,0x40101001000040204004100100002000081ce3,0x1040101001008040204004100101002040081ce3],
[0x1040101001008040204004100101002040081ce3,0x0,0x0,0x40101001000040204004100104002100081ce3,0x0,0x2810c8240481,0x0,0x5090a8240481,0x0,0x5090a8240481,0x0,0x6110c8240481,0x421088240481,0x6110c8240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0xc41188240501,0x421088240481,0xc41188240501,0x421088240481,0x2810c8240481,0x481088240481,0x481088240481,0x481088240481,0x481088240481,0x481088240481,0x0,0x809188240501,0x2040080101010040204004100108002200083ce3],
[0x809188240501,0x0,0x811188240501,0x861188240501,0x811188240501,0x861188240501,0x821188240501,0x861188240501,0x821188240501,0x861188240501,0x841188240501,0x801188240501,0x841188240501,0x841188240501,0x0,0x6090c8240481,0x0,0x6090c8240481,0x0,0x411088240481,0x421088240481,0x411088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x841188240501,0x1088240481,0x841188240501,0x1088240481,0x0],
[0x809188240501,0x0,0x809188240501,0x0,0x811188240501,0x861188240501,0x811188240501,0x861188240501,0x821188240501,0x861188240501,0x821188240501,0x861188240501,0x841188240501,0x801188240501,0x841188240501,0x841188240501,0x0,0x0,0x0,0x0,0x0,0x811188240501,0x421088240481,0x811188240501,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x421088240481,0x41088240481,0x1088240481,0x41088240481],
[0x1088240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2395 : TreeBound (n := 4) 106 (programCode 0x4829075b40) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf30000b640002d900007d4de600f30007b660f3f3001e9cc0079800f4e6003cfcc00f3f3003cde6c7195,0xf30000b640002d900007d4de600f303cc1e60f3f3001e9cc007983cc1e61e603cc7980f30f301e6c7195,0xf30000b640002d900007d4de600f3001e7e60f3f3001e9cc0079801e7e600f33cc03ccf300799e6e9455,0x0,0xf30000b640002d900007d4de600f3003cde60f3f3001e9cc007980799e601e63cc0798f301e61e6ceb15,0x0,0x0,0x0,0xf30000b640002d900007d4de600f303cc1e60f3f3001e9cc007983cc1e60f303cc3cc0f30f301e6c7195,0xf3000222c0002d900007d4e0460f300001e60f4023079bcc007980001ea08c03cc0000f300001e6c74f5,0x0,0x0,0x0,0x0,0x0,0xf30000b640002d900007d4de600f300001e60f3f3001e9cc007980001e9cc003db3000f300001e6c7195,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x1dcd6500000773597c4d9c3ad6501dcddc359400001dcd6500ee6b36e6b2800003b9bba47fe6dcd65ee6b2bb9acbdcd653b9acbdcf41d6500ee72c80d57f7359400001dcddc359403b9ad1735943ba23d594003bb94a355e0ee6b28000077536165000ee6d04d6500ee747fd5e1ee9,0x40000000100000080400000001000002800040000000800040000402020002008100400000200000000804000008010a00008004000002080000040040000020200000100308430a7,0x1dcd6500000773597c4d9c3ad6501dcddc359400001dcd6500ee6b36e6b2800003b9bba47fe6dcd65ee6b2bb9acbdcd653b9acbdcf41d6500ee72c80d57f7359400001dcddc359403b9ad1735943ba23d594003bb94a355e0ee6b28000077536165000ee6d04d6500ee747fd5e1ee9,0x0,0xf3000222c00088b0000f6cde600f30007b660f3f3001e9cc0079800f4e6003cfcc00f3f3003cde6c7195,0x1dcd6500007ea8ed40001faa3b50000f5de8140001faa3b500001ddc4bb2800003b9bb86b281dcd65ee6b2bb9acbdcd653b9acbdcf41d6500ee729b59403b9aca000003ba23d59403b9ad1735943b9ae7cd6503b9aca00000ee6b9f359477360b35940ee6b9f35940ee747fd5d4429,0xf3000222c00088b0000f6cde600f3001e7e60f3f3001e9cc0079803cde600f33cc03ccf300799e6e9455,0x0,0xf3000222c00088b0000f6cde600f3003cde60f3f3001e9cc007980799e601e63cc0798f301e61e6ceb15,0x0,0x0,0x0,0xf3000222c00088b0000f6cde600f303cc1e60f3f3001e9cc007983cc1e60f303cc3cc0f30f301e6c7195,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40000000300008000c00000003000080008040000020800040000402000202008100400000200000100804000008010001008000004002000010040000100020000100100308430a7,0x0,0x40000000300008001c00000003000080018040000020800040000402000602008100400000200000200804000008010003008000004002000080040000040020000200100308430a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0xf3000408c0010230003cfcde600f300001e60f3f3001e9cc007980001e9cc003db3000f6cc001e6c7195,0x0,0x0,0x0,0x0,0x1e449b8624dc1359400001e449a95dcddc35940000000000007735b1cda189352f7359400000ee6b2f73597b9acdb9aca3b9acbdcf4949a97b9b43126a53b9aca00003b9aca000003b9acdb9aca3ba23d5940077536165001dd4d8594003bb89765000eee25d94000ee70c631c9099,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x86118c240501,0x421084240481,0x86118c240501,0x421084240481,0x0,0x0,0x0,0x0,0x0,0x211080240481,0x411084240481,0x211080240481,0x411084240481],
[0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x811188240501,0x411084240481,0x811188240501,0x11080240481,0x0,0x0,0x0,0x0,0x0,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x86118c240501,0x421084240481,0x86118c240501,0x421084240481,0x0,0x0,0x400000201000000804000002000100008002002000008000200010000800020001004000002010000008000800020002000080400000101000000404000000810000001001c873227,0x0,0x0,0x221084240481,0x421084240481],
[0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x82118c240501,0x421084240481,0x82118c240501,0x421084240481,0xf30811bcc0000f3000003ce0460f300001e60f4023079bcc007980001e9cc003db3000f6cc001e6c74f5,0x0,0x0,0x0,0x0,0x0,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x82118c240501,0x421084240481,0x82118c240501,0x421084240481,0x0,0x0,0x0,0x0],
[0x0,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x86118c240501,0x421084240481,0x86118c240501,0x421084240481,0x0,0x0,0xf300f33cc03cc03ccf303ce0460f303cc1e60f3f3001e61e607983cc1e9cc003db3000f6cc001e6c7195,0x0,0x0,0x2410c2240481,0x441084240481,0x2410c2240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x841188240501,0x841188240501,0x841188240501,0x41080240481,0x0,0x0],
[0x0,0x0,0x400020001000080004000000000000000002002100008000000010000800020001004000010010000040000000040000000080400000101000000404000000810000001001887fe67,0x221084240481,0x421084240481,0x221084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x801188240501,0x1080240481,0x801188240501,0x1080240481,0x0,0x0,0x0,0x0,0x0,0x2410c2240481,0x441084240481,0x2410c2240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x841188240501,0x841188240501,0x841188240501,0x41080240481],
[0x0,0x0,0x0,0x0,0x400020001000080004000000000000000002002100008000000010000800020001004000010010000040000000040000000080400000101000000404000000810000001001887fe67,0x201080240481,0x421084240481,0x201080240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x421084240481,0x841188240501,0x1080240481,0x841188240501,0x1080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_1723 : TreeBound (n := 4) 106 (programCode 0x4829075b) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part011_1724 part011_1805 part011_1806 part011_1887 part011_1968 part011_1969 part011_1970 part011_1971 part011_1972 part011_1973 part011_1974 part011_1975 part011_1976 part011_2073 part011_2266 part011_2395

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2637 : TreeBound (n := 4) 106 (programCode 0x4829075c31) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080081210481,0x1080421204481,0x1080421204481,0x1080c61208481,0x1080c6120c481,0x1080c61208481,0x1080001200481,0x1080081210481,0x1080001200481,0x1080081210481,0x1080001200481,0x0,0x16c800111600016c80003cc2047023079c08de60f4e600f4e6000f4e679800fa98003d39801e7032b5,0x8040021000810020100084002102002080080ce3,0x16c800097e00025f80007984640e832604941b20f4e600f4e6000f4e679800fa980079f9801e7051a5,0x16c80014e200053880012fc99cace307ab3957e0f4e600f4e6000f4e679801ed98003d39801e707485,0x20200000080800000102000000108000242652132001000080000020000000000000020100000080400000100800000100802000001008000004010000010010000010014c7ffa7,0x440001000010000000084002102002080080ce3,0x8118002046000fa98003cc1e7f90b307e42f1f80f4e600f4e6000f4e679800fa98003d39801e7032b5,0x2040001000010000000084002102002080080ce3,0x840021000810020100084002102002080080ce3,0xf307980001e6000079800000000000f30000000000f4e600f4e6000f4e679801ed980079f9801e703855,0x0,0x40001000010000000084002102002080080ce3,0x0,0x0,0x0,0x0,0x0,0x1001040120022],
[0x80006000110020400800820020820100800100e4,0x8000a00020482012090084002108002010080ce3,0x1dcd650000f5de817b9acbdcd650000f5de817b9adac388d0000430e2558712ac390c975c21aca1dcd660c390ba8f101201925d71751da9dd11eaca077447ab28001dd11eaca01dd11eaca001dd11f23d594000f047fe5000eee25f70d65f047fe5000ee6b29dcd65ee6d0ce58cd19,0x1011042120442,0x1011042120442,0x1001040120022,0x1011042120442,0x1011042120442,0x1021046120c82,0x1031046120c82,0x1021046120c82,0x0,0x80102004010020400820022800820400804020e4,0x0,0x80202008010020400840023000820400808040e4,0x0,0x16c800111600016c8000f307d4fea60f3fa9f980f4e600f4e6000f4e6f3001e7e6003db3001e707485,0x0,0x16c80005b200025f80003cc2414f7616d41a9b20f4e600f4e6000f4e679800f4e6003db3001e7032b5,0x40003000020000000084002104002100080ce3,0x4200000080800000102000000108000000200010004000200812440002059182c80004020000080400000100800000100800800000401000000804000002020000010031a50ca7,0xfa98003ea605ce008003cc1ebcda561736d5b0e0f4e600f4e6000f4e679800f4e6003db3001e7032b5,0x8118003ea6000fa98003cc1e7f929907e4a89f80f4e600f4e6000f4e679800f6cc007a73001e703345,0x0,0x840021000820020100084002104002100080ce3,0x40201000020000000084002104002100080ce3,0x0,0x40001000020000000084002104002100080ce3,0x0,0x0,0x0,0x0],
[0x0,0x1001040120022,0x80006000110020400800820020840201000100e4,0x0,0xf3000222c00088b0000f6cc03ccf300f31e601e603ccf300f33e2cbccf4e60f30798b640f3000811d756,0x1011042120442,0x1011042120442,0x1001040120022,0x1011042120442,0x1011042120442,0x1021046120c82,0x1031046120c82,0x1021046120c82,0x0,0x80102004010020400820022800840401004020e4,0x0,0x80202008010020400840023000840401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2718 : TreeBound (n := 4) 106 (programCode 0x4829075c32) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010010020400800820020880402000100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2719 : TreeBound (n := 4) 106 (programCode 0x4829075c33) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080081210481,0x1080421204481,0x1080421204481,0x1080c61208481,0x1080c6120c481,0x1080c61208481,0x1080001200481,0x1080081210481,0x1080001200481,0x1080081210481,0x1080001200481,0x0,0x16c800111600016c80003cc20472fc079c08de60f4e6003ea6001e7e679800fa98003d39801e7032b5,0x8040021000810020100104004102002080080ce3,0x16c80005b200025f80003cc27e115c2604941b20f4e6003ea6001e7e679800fa98003d39801e7032b5,0x25f800097e00025f8000798445a22c1e68c7fcc0f4e6007b66001e7e679800fa980079f9801e7051a5,0x0,0x440001000010000000104004102002080080ce3,0xfa98002046000fa98003cc1e7f65fc07d8cac461e7e6003ea6001e7e679801ed98003d39801e7037c5,0x2040001000010000000104004102002080080ce3,0x840021000810020100104004102002080080ce3,0x0,0x0,0x40001000010000000104004102002080080ce3,0x0,0x0,0x0,0x0,0x0,0xc00030005020140a0104004100402200080de3],
[0xc00030010020400800820820820104800100e4,0x81040120022,0x4002a00000002800040002000000018000402ee017600010000c00000041000080000002010000008040000004080000020080402400101000000400008000210000001001087fca7,0x281042120442,0x281042120442,0x81040120022,0x281042120442,0x281042120442,0x481044120882,0x481044120882,0x481044120882,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c80003cc2416ce316dbb2d7e0f4e6003ea6001e7e679800f4e6003db3001e7032b5,0x0,0x16c800097e00025f8000798408e0460f3811bcc0f4e6007b66001e7e679800f6cc007a73001e7051a5,0x40005000020000000104004104002100080ce3,0x4200000080800000102000000108000000040002004000200810440002041102080004020000010400000080800000200800400000201000000808000004020000010031840da7,0xfa98003ea603dd8f8003cc1e9dd3460f74d3a2c0f4e6007b66001e7e679800f6cc007a73001e703345,0x8118002046000fa98003cc1ebcbb03172f3d7420f4e6003ea6001e7e679800f4e6003db3001e7032b5,0x0,0x840021000820020100104004104002100080ce3,0x40201000020000000104004104002100080ce3,0x0,0x40001000020000000104004104002100080ce3,0x0,0x0,0x0,0x0],
[0x0,0x0,0xc00030010020400800821020840205000100e4,0x81040120022,0x0,0x281042120442,0x281042120442,0x81040120022,0x281042120442,0x281042120442,0x481044120882,0x481044120882,0x481044120882,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2800 : TreeBound (n := 4) 106 (programCode 0x4829075c34) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080000210481,0x1080421204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x16c800111600016c80003cc2047023079c08de60f4e6003ea6000f4e679800fa98003d39801e7032b5,0x8040021000000000000804020102002080080ce3,0x16c800097e00025f8000b6464a124f2604941b22dae600b826002dae679800fa980079f9801e7051a5,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x10490411212a2],
[0x10090411212a2,0x0,0x10090411212a2,0x10590411212c2,0x10110411212c2,0x10490411212a2,0x10110411212c2,0x10110411212c2,0x1021041121302,0x1029041121302,0x1021041121302,0x0,0x10410411212a2,0x0,0x10410411212a2,0x0,0x16c800111600016c8000f307d4fea60f3fa9f984c0e600f4e6004c0e6f3001e7e6003db3001e707485,0x0,0x16c800097e00025f8000798408e0460f3811bcc1e7e6007b66001e7e679800f6cc007a73001e7051a5,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x10490411212a2,0x10090411212a2,0x0,0x10090411212a2,0x10590411212c2,0x10110411212c2,0x10490411212a2,0x10110411212c2,0x10110411212c2,0x1021041121302,0x1029041121302,0x1021041121302,0x0,0x10410411212a2,0x0,0x10410411212a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2881 : TreeBound (n := 4) 106 (programCode 0x4829075c35) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2882 : TreeBound (n := 4) 106 (programCode 0x4829075c36) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2883 : TreeBound (n := 4) 106 (programCode 0x4829075c37) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2884 : TreeBound (n := 4) 106 (programCode 0x4829075c38) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2885 : TreeBound (n := 4) 106 (programCode 0x4829075c39) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2886 : TreeBound (n := 4) 106 (programCode 0x4829075c3a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2887 : TreeBound (n := 4) 106 (programCode 0x4829075c3b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2888 : TreeBound (n := 4) 106 (programCode 0x4829075c3c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2889 : TreeBound (n := 4) 106 (programCode 0x4829075c3d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x180428204481,0xc0003000800420102004080100802020080ce3,0x180428204481,0x0,0x2200000008800000012000000018000242652132001000080000000020000000020000100080000400100000800100000800020001000080004000100010000100010014c7ffa7,0xc0003000000400002004080108002000080ce3,0x16c800111600016c8003cc1eda8230982181064601e7e601e61e601e601e60f307983cc3cc1e7032b5,0x180428204481,0x1810a8210481,0x445800097e00016c870d65a96a000079800007980798f300f31e601ed0d2d7cc0f30f300001e68a925,0x1810a8210481,0x180028200481,0x0,0x0,0x0,0x0,0x8040021000004000002004080108002200080ce3,0x0,0x180428204481,0x140005000000800002004080100002020080ce3,0x180428204481,0xc0005000100804022004080100101084080fa3,0x0,0x0,0x16c800097e00025f8003cc1eda82318b2181430601e7e601e61e601e601e60f30f307983cc1e703345,0x180428204481,0x1810a8210481,0xc0005000000800022004080100001008080fa3,0x1810a8210481,0x180028200481],
[0x0,0x25f800097e00025f8003cc1eda916111a54d24a601e7e601e61e601e9cc001e60f307d4c001e703855,0x0,0xc0005000000800022004080100001200080fa3,0x0,0x8000480012010080402004080108002200082ce3,0x109040140022,0x8000880022010080402004080108002200082de3,0x109040140022,0x111042140442,0x111042140442,0x101040140022,0x111042140442,0x111042140442,0x121042140442,0x131042140442,0x121042140442,0x101040140022,0x0,0x8020080802010080402004080108002200086ce3,0x0,0x0,0x20a948240501,0x209042140442,0x20a948240501,0x209042140442,0x212948240501,0x252948240501,0x212948240501,0x252948240501,0x222948240501,0x222948240501],
[0x222948240501,0x252948240501,0x242948240501,0x272948240501,0x242948240501,0x252948240501,0x8040001000000000002004080108002200080ce3,0x0,0x20a948240501,0x9040140022,0x20a948240501,0x9040140022,0x212948240501,0x252948240501,0x212948240501,0x252948240501,0x222948240501,0x222948240501,0x222948240501,0x252948240501,0x242948240501,0x272948240501,0x242948240501,0x252948240501,0x80008240481,0x480088240481,0x80008240481,0x480088240481,0x80008240481,0x0,0x80a108240501,0x9040140022],
[0x80a108240501,0x9040140022,0x812108240501,0x842108240501,0x812108240501,0x842108240501,0x822108240501,0x802108240501,0x822108240501,0x842108240501,0x842108240501,0x802108240501,0x842108240501,0x842108240501,0x0,0x880490012412090482004080108001200082ca3,0x20004800110020400800820020880402000100e4,0x9004980226130984c2004080108001200082fa3,0x0,0x410088240481,0x8240481,0x410088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0],
[0x80a108240501,0x0,0x80a108240501,0x0,0x812108240501,0x842108240501,0x812108240501,0x842108240501,0x822108240501,0x802108240501,0x822108240501,0x842108240501,0x842108240501,0x802108240501,0x842108240501,0x842108240501,0x0,0x0,0x40005000110020400800820020880402000100e4,0x0,0x0,0x812108240501,0x8240481,0x812108240501,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40008240481,0x8240481,0x40008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3050 : TreeBound (n := 4) 106 (programCode 0x4829075c3e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108842240481,0xc00024010020400820020800880006004020e4,0x108842240481,0x140004021002040082002080088000a004021e4,0x2098c6240481,0x6098c6240481,0x2098c6240481,0x6098c6240481,0x408842240481,0x408842240481,0x408842240481,0x6098c6240481,0x0,0x6098c6240481,0x0,0x0,0x80006000110020400820020800880402004020e4,0x0,0x108842240481,0x0,0x108842240481,0x0,0x2098c6240481,0x6098c6240481,0x2098c6240481,0x6098c6240481,0x408842240481,0x408842240481,0x408842240481,0x6098c6240481],
[0x0,0x6098c6240481,0x0,0x0,0x0,0x8000804021002040082002080088000a004021e4,0x1090481412a2,0x80008000210020400820020800880002004021e4,0x1090481412a2,0x3090481416c2,0x2090481414c2,0x8090481410a2,0x2090481414c2,0x2090481414c2,0x409048141902,0xc09048141902,0x409048141902,0x9090481412a2,0x8090481410a2,0x0,0x8090481410a2,0x80022000810020400820020800880402004024e4,0x80012000410020400820020800880402004026e4,0x80402004010020400820020800880402004020e4,0x80022000810020400820020800880402004024e4,0x80022000810020400820020800880402004024e4,0x8004200101002040082002080088040200402ce4,0x80082004010020400820020800880402004020e4,0x80082002010020400820020800880402004034e4,0x0,0x0,0x1490481412a2],
[0x0,0x1490481412a2,0x2439cc240501,0x842108240501,0x2439cc240501,0x40008240481,0x44008c240481,0x40008240481,0x44008c240481,0x40008240481,0x842108240501,0x842108240501,0x842108240501,0x40008240481,0x80102004010020400820020800880402004020e4,0x0,0x0,0x0,0x0,0x0,0x2439cc240501,0x842108240501,0x2439cc240501,0x40008240481,0x44008c240481,0x40008240481,0x44008c240481,0x40008240481,0x842108240501,0x842108240501,0x842108240501,0x40008240481],
[0x80202008010020400820020800880402004060e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3147 : TreeBound (n := 4) 106 (programCode 0x4829075c3f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x180428204481,0xc0003000800420104004100100802020080ce3,0x180428204481,0x0,0x2cb41780007aef40a0000fd51da8000218711a00002cb41780000773597c89352f735940773597b9d97633949cc4e22d3ed2a8179d283b9b059acaee6b36e6b29dcd68b9aca3b9ae7cd6503b9aca0ee6b2f735cf9aca1dcd6c735947735a2e6b29dcd65ee6b36e749d8e4dfc9,0xc0003000000400004004100108002000080ce3,0x16c800111600016c8003cc1e7f6231edd8cac82c01e67981e63cc01e603cc1e607983cc3cc1e7037c5,0x180428204481,0x1810a8210481,0x16c800111600016c8003cc1f8192322e66cf282c01e67981e63cc01e603cc1f6323040cc8c1e7037c5,0x1810a8210481,0x180028200481,0x0,0x0,0x0,0x0,0x0,0x0,0x480088210481,0x0,0x0,0x480088208481,0xc00030010020400802022000802400080406e4,0x480088208481,0x480088210481,0x480088210481,0x480088210481,0x480088210481,0x480088200481,0x0],
[0x0,0x0,0x0,0x0,0x180428204481,0x140005000000800004004100100002020080ce3,0x180428204481,0x140005000100804024004100100102100080de3,0x0,0x0,0x16c80005b200025f8003cc1ebcba1090af3d760601e67981e63cc01e601e60f307983cc3cc1e7032b5,0x180428204481,0x1810a8210481,0x140005000000800004004100100002010080ce3,0x1810a8210481,0x180028200481,0x0,0x16c800097e00025f8003cc1e9dd1610274d3a4a601e6f301e63cc01e9cc000f30f307d4fcc1e703345,0x0,0x140005000000800004004100100002200080ce3,0x0,0xc0101000080402014004100100082002080ce3,0x40101000000000004004100100002020080ce3,0x140101000100804024004100100102004080de3,0x40101000000000004004100100002100080ce3,0x0,0x1400050010020400802022000802400080406e4,0x0,0x40101000000000004004100100002000080ce3,0x40101000000000004004100100802020080ce3,0x40101000000000004004100100002000080ce3,0x40101000000000004004100101002040080ce3],
[0x40101000000000004004100100002000080ce3,0x0,0x0,0x40101000000000004004100104002100080ce3,0x0,0x0,0x20a948240501,0x0,0x20a948240501,0x0,0x212948240501,0x252948240501,0x212948240501,0x252948240501,0x222948240501,0x222948240501,0x222948240501,0x252948240501,0x242948240501,0x272948240501,0x242948240501,0x252948240501,0x0,0x0,0x0,0x0,0x0,0xa12948240501,0x8240481,0xa12948240501,0x8240481,0x420088240481],
[0x8240481,0x420088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0,0x20a948240501,0x0,0x20a948240501,0x0,0x212948240501,0x252948240501,0x212948240501,0x252948240501,0x222948240501,0x222948240501,0x222948240501,0x252948240501,0x242948240501,0x272948240501,0x242948240501,0x252948240501,0x80008240481,0x480088240481,0x80008240481,0x480088240481,0x80008240481,0x0,0x80a108240501,0x2040080102010080404004100108002200082ce3],
[0x80a108240501,0x0,0x812108240501,0x842108240501,0x812108240501,0x842108240501,0x822108240501,0x802108240501,0x822108240501,0x842108240501,0x842108240501,0x802108240501,0x842108240501,0x842108240501,0x0,0x800410010004000004004100108002200080ce3,0x20004800110020400820022000880502004020e4,0x800810020004000004004100108002200080ce3,0x0,0x410088240481,0x8240481,0x410088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0],
[0x80a108240501,0x0,0x80a108240501,0x0,0x812108240501,0x842108240501,0x812108240501,0x842108240501,0x822108240501,0x802108240501,0x822108240501,0x842108240501,0x842108240501,0x802108240501,0x842108240501,0x842108240501,0x0,0x0,0x40005000110020400840022000880602008040e4,0x0,0x7980020460007d4c000f6cc03ccf300f31e601ed9800f4e6003db3000f6cc0f30f307983cc0f3079d756,0x812108240501,0x8240481,0x812108240501,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40008240481,0x8240481,0x40008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3340 : TreeBound (n := 4) 106 (programCode 0x4829075c40) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf3000222c0002d90000b654e297e0f307983cc2d93d39bcc0079800f4e600f33cc00f3f3003cde64dcf5,0x80202018010020400840021000800c00028040e4,0x0,0x0,0x80022010810020400840021000804400108044e4,0x80022010810020400840021000802400088044e4,0x0,0x80022010810020400840021000804400108044e4,0x80022010810020400840021000804400108044e4,0x80022010810020400840021000808400208044e4,0x80022010810020400840021000810401008044e4,0x80022010810020400840021000810400408044e4,0x0,0x0,0x0,0x80002010010020400840021000840401008040e4,0x80006000110020400840021000880402008040e4,0x0,0xf307983cc0000f3079803cc03cc7980799e601ed98016d73001e9cc007d4c352800079800007983cddc6,0x80006010010020400840021000800c00028040e4,0x0,0x0,0x0,0x80202010010020400840021000802400088040e4,0x0,0x80202010010020400840021000804400108040e4,0x80202010010020400840021000804400108040e4,0x80082010010020400840021000808400208054e4,0xf30079bcc1e60f3079803cc03ccf300f31e601ed9800f4e6003cfcc00f33cde600f37981e60f308ab096,0x80082010010020400840021000810400408054e4],
[0x0,0x0,0x0,0x0,0x0,0x0,0x1090481412a2,0x0,0x1090481412a2,0x3090481416c2,0x2090481414c2,0x8090481410a2,0x2090481414c2,0x2090481414c2,0x409048141902,0xc09048141902,0x409048141902,0x9090481412a2,0x8090481410a2,0x0,0x8090481410a2,0x80002000810020400840021000880402008040e4,0x80012000410020400840021000880402008046e4,0x0,0x0,0x1490481412a2,0x0,0x1490481412a2,0x210000240481,0x10000240481,0x210000240481,0x10000240481],
[0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x812108240501,0x410000240481,0x812108240501,0x10000240481,0x80022000810020400840021000880402008044e4,0x80022000810020400840021000880402008044e4,0x8004200101002040084002100088040200804ce4,0x80082008010020400840021000880402008054e4,0x80082002010020400840021000880402008054e4,0x0,0x0,0x1490481412a2,0x0,0x1490481412a2,0x240842240481,0x40000240481,0x240842240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x80102004010020400840021000880402008060e4,0x0],
[0x0,0x0,0x0,0x0,0x240842240481,0x40000240481,0x240842240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x80202008010020400840021000880402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_2636 : TreeBound (n := 4) 106 (programCode 0x4829075c) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part011_2637 part011_2718 part011_2719 part011_2800 part011_2881 part011_2882 part011_2883 part011_2884 part011_2885 part011_2886 part011_2887 part011_2888 part011_2889 part011_3050 part011_3147 part011_3340

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3454 : TreeBound (n := 4) 106 (programCode 0x4829075d61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000600012040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3455 : TreeBound (n := 4) 106 (programCode 0x4829075d62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040200102040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3456 : TreeBound (n := 4) 106 (programCode 0x4829075d63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000a00022040080408004200108002200082de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3457 : TreeBound (n := 4) 106 (programCode 0x4829075d64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8040200012040080400084002108002200082ce3,0x0,0x103a1c6204501,0x8050200402050080402004020102002020082ce3,0x103a1c6204501,0x8000200002010080400004020100002000082ce3,0x1022104208501,0x8040200002010080400004020102002080082ce3,0x1022104208501,0x8040200002010080400004020102002080082ce3,0x8010200402050080402004020100802020082ce3,0x8000200002010080400004020100002000082ce3,0x40000800100008000400008001000008001000200001000080010000200010000800400000800040000800400008000400008002000010002000010020000100020000100508793a7,0x0,0x8040200002010080400004020102002080082ce3,0x4000000090000000440000000900000001400000081400000404000000801000001000012001000048004000100004000100011000080004000a0001000020001000200010026baa8,0x0,0x4000000110000000440000000900000001400000101800000404000000802000001000012001000048004000100008000100022000100008000c0001000040002000400020027baa8,0x8040200022040080400104004108002200082de3,0x0,0x100a121204501,0x4000100010000c8004000320010000c800040022000800040001000200001000880020000020190000400640000801900000802040000200400004064000004195000010210843da7,0x100a121204501,0x1002100200501,0x1002100208501,0x0,0x1002100208501,0x0,0x8010200402040080402004080100802020082ce3,0x1002100200501,0x8010200402040080402004080101002040082ce3],
[0x0,0x0,0x400020001000080004000000010000000020003000020001000100028000100008004000010010000010000000080000000080400000100000000104000001000000001009087d7a7,0x0,0x400020001000080004000000010000000020003000020001000100028000100008004000010010000010000000080000000080400000100000000104000001000000001009087d7a7,0x8040200042001080400204008108002200082ee3,0x8040200002040080400004080108002200082ce3,0x8040200082002080400404010108002200082ce3,0x0,0x12000000018000000120000000100009000200001000080010000000210000800400000800100000800000408001000008040000010100000010400000101000000100508793a7,0x108842040442,0x22000000028000000220000000200011000200001000080010000000410000800400000800100000800000808001000008040000010100000010400000101000000100528f93a7,0x108842040442,0x8842040442,0x208842040442,0x208842040442,0x208842040442,0x8842040442,0x408842040442,0x208842040442,0x408842040442,0x208842040442,0x808c42140442,0x0,0x808c42140442,0x8040200102010080400804020108002200082ce3,0x8040200002000080400004000108002200082ce3,0x8040200202010080401004040108002200083ce3,0x0,0xc0002012040080400084202108002200082ce3,0x108044040022,0x140004022040080400104204108002200082de3],
[0x108044040022,0x208044040022,0x208044040022,0x8044040022,0x208044040022,0x8044040022,0x408844040442,0x408844040442,0x408844040442,0x8044040022,0x0,0x0,0x0,0x8040200402040080402004080108002200082ce3,0x0,0xc0002082052080400404220108002200082ce3,0x808020200020020820000800080006000000e4,0x140004082052080400404220108002200082ce3,0x0,0x240008102051080400804280108002200082ce3,0x208848040442,0x8048040022,0x208848040442,0x8048040022,0x800820020402020082002080088004200402de4,0x0,0x10008400204020400820020800880082004035e4,0x8048040022,0x0,0x0,0x0,0x0],
[0x8000600802040080404004100100082002086ce3,0x0,0x8000a00802040080404004100100102004086de3,0x0,0x8020200802040080404004100100202008086ce3,0x0,0x8020200802040080404004100100402010086ce3,0x0,0x8010200802040080404004100100802020086ce3,0x0,0x8010200802040080404004100101002040086ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x808020200020020840001000080006000000e4,0x0,0x0,0x0,0x208848040442,0x8048040022,0x208848040442,0x8048040022,0x800820020402020084002100088004200804de4,0x1040040402058080402004240108002200082ce3,0x10008400204020400840021000880082008055e4,0x8048040022,0x0,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3586 : TreeBound (n := 4) 106 (programCode 0x4829075d65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8001200042040080408004200108002200082ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3587 : TreeBound (n := 4) 106 (programCode 0x4829075d66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040200402040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3588 : TreeBound (n := 4) 106 (programCode 0x4829075d67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8002200082040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3589 : TreeBound (n := 4) 106 (programCode 0x4829075d68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040200402040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3590 : TreeBound (n := 4) 106 (programCode 0x4829075d69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8004200102040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3591 : TreeBound (n := 4) 106 (programCode 0x4829075d6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3000007983cc79879807983ccf3001e9cc01e6f3001e9cc001f530007d4c001e8e9855]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3592 : TreeBound (n := 4) 106 (programCode 0x4829075d6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1022121204501,0x1022181230501,0x1022121204501,0x1022121204501,0x1022141208501,0x1022141228501,0x1022141208501,0x1022101220501,0x1022181210501,0x1022181230501,0x1022181210501,0x0,0x1022101220501,0x8008200202000080400084002108002000083ce3,0x1022101220501,0x8008200202010080400084002108002080083ce3,0xf30079bcc01e6f3003cc799e601e60f307983ccf3001e9cc007983cc1e9cc003db3000f6cc001e8ad195,0x0,0x1022121204501,0x1022181230501,0x1022121204501,0x1022121204501,0x1022141208501,0x1022141228501,0x1022141208501,0x1022101220501,0x1022181210501,0x1022181230501,0x1022181210501,0x0],
[0x1022101220501,0x0,0x1022101220501,0x0,0x0,0x1022121204501,0x0,0x1022121204501,0x1022100200501,0x1022100208501,0x0,0x1022100208501,0x0,0x0,0x0,0x0,0x0,0x0,0x400000009000080024000200010000000260000008100000020400000080800000100001200080004800200010000800020002200030000800040001000080001000400020016eea8,0x0,0x0,0x1022142240501,0x0,0xfa98003ea6000f6cc79a32104600081183cc2ac64e61e60799e601e9cc003db3000f6cc001e8ad195,0x110842040442,0x3d39800f4e6001e9cc79a3d92a6000fa983cc2bc87e61e60799e601e9cc003db3000f6cc001e8cd5f5,0x110842040442,0x2221ce240501,0xc2218c240501,0x2221ce240501,0x82210c240501,0x42218c240501],
[0xc2218c240501,0x42218c240501,0x2210c240501,0x82210c240501,0xc2218c240501,0x82210c240501,0x82210c240501,0x1022142240501,0x0,0xfa98003ea6000f6cc799e601e600081183ccf3001e6003d399e601e9cc003db3000f6cc001e8ad195,0x110842040442,0x3d39800f4e6001e9cc799e601e6000fa983ccf3001e60079f99e601e9cc003db3000f6cc001e8cd5f5,0x110842040442,0x22214a240501,0xc2218c240501,0x22214a240501,0x822108240501,0x42218c240501,0xc2218c240501,0x42218c240501,0x22108240501,0x822108240501,0xc2218c240501,0x822108240501,0x822108240501,0x1022104240501,0x1022104240501,0x1022104240501,0x0,0x0,0x120844040442,0x0],
[0x120844040442,0x222142240501,0xc2218c240501,0x222142240501,0x822108240501,0x422104240501,0x422104240501,0x422104240501,0x22100240501,0x822108240501,0xc2218c240501,0x822108240501,0x822108240501,0x0,0x122128240501,0x100040040022,0x122128240501,0x100040040022,0x222148240501,0xc22188240501,0x222148240501,0x822108240501,0x422188240501,0xc22188240501,0x422188240501,0x22108240501,0x822108240501,0xc22188240501,0x822108240501,0x822108240501,0x0,0x88002202002080400404010108002200083ce3],
[0x2c432e406fc40ae58bd8000000614f4c00000056aa9fb000000567f60acfec0059335b206fc80df8d67fb67f6000159fd800159fd95a53ff60000159fd800159fd95a02e7f6000015aaa7ec10e4e2c9b03b043938b1d4afd8000000159fd80000000159fd80acfec0159fd82b3fb159fd80acfee0c64360000000159fd8000000b266b60000002c99ad80000001037e20000002b3fb01853b672ac,0x108004202002080400404010108002200083ce3,0x220010000820000002000100002200000020010140080040000080100400000101000280144000a00510000800010002000400000011000080044000000050000000400027bba8,0x2221ce240501,0xc2218c240501,0x2221ce240501,0x82210c240501,0x42218c240501,0xc2218c240501,0x42218c240501,0x22108240501,0x82210c240501,0xc2218c240501,0x82210c240501,0x82210c240501,0x0,0x122128240501,0x0,0x122128240501,0x0,0x222148240501,0xc22188240501,0x222148240501,0x822108240501,0x422188240501,0xc22188240501,0x422188240501,0x22108240501,0x822108240501,0xc22188240501,0x822108240501,0x822108240501],
[0x0,0xfa98003ea6000f6cc799e601e600081183ccf3001e9cc00799e601e9cc003db3000f6cc001e8ad195,0x800028000020000840001000080006000000e4,0x3d39800f4e6001e9cc799e601e6000fa983ccf3001e9cc00799e601e9cc003db3000f6cc001e8cd5f5,0x0,0x222148240501,0xc2218c240501,0x222148240501,0x822108240501,0x422188240501,0xc2218c240501,0x422188240501,0x22108240501,0x822108240501,0xc2218c240501,0x822108240501,0x822108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3769 : TreeBound (n := 4) 106 (programCode 0x4829075d6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x25f8f30f3097e16c97bb0798798b64079a22cf3003cfcc01e6f3001e9cc001f53000408c001ead3635,0x880022000020100880002000080402000000e4,0x25f80007983cc1e60fa983cc79879807983ccf3001e9cc01e6f3001e9cc001f530007d4c001e8eb6b5,0x0,0x44583cc0007983cc1ed983cc79879807983cc000f4e600f4e6000f4e9cc001f530007d4c001e8ed515,0x0,0x25f83cc0003cc1e60fa983cc79879807983cc001e7e6007b66001e7e9cc001f530007d4c001e8eb6b5,0x0,0x120840040022,0x120842040442,0x120840040022,0x120842040442,0x120840040022,0x120844040442,0x120840040022,0x120844040442,0x120842040442,0x0,0x3cc7983cc07983cc1e607983cc79879807983cc3cc01e6f301e63cc01e9cc001f530007d4c001ecb5855,0x0,0x8118007980f307983d3983cc79879807983ccf3001e9cc01e6f3001e9cc001f530007d4c001e92ddd5,0x2080082000020100880002000080402000000e4,0xfa98003cc1e60f3079f983cc79879807983ccf3001e9cc01e6f3001e9cc001f530007d4c001e8e9855,0x4080102000020100880002000080402000000e4,0x80002000020100880002000080402000000e4,0x8080202004020100880002000080402000000e4,0x0,0x0,0x880022000020100800800020080402000000e4,0x0,0x0],
[0x432142240501,0x46218c240501,0x432142240501,0x46218c240501,0x422104240501,0x422104240501,0x422104240501,0x422104240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x10080402004020100880002000080402000000e4,0x80102000020100880002000080402000000e4,0x0,0x0,0x20080802010020100800820020880402000100e4,0x0,0x0,0xe72142240501,0x2108240501,0xe72142240501,0x2108240501,0x2104240501,0x2100240501,0x2104240501,0x2100240501,0x2108240501,0x2100240501,0x2108240501,0x2100240501,0x80002000020100880002000080402000000e4],
[0x0,0x0,0x40081002010020100800820020880402000100e4,0x0,0x0,0x212142240501,0x2108240501,0x212142240501,0x2108240501,0x2104240501,0x2100240501,0x2104240501,0x2100240501,0x2108240501,0x2100240501,0x2108240501,0x2100240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3850 : TreeBound (n := 4) 106 (programCode 0x4829075d6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8010200402040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3851 : TreeBound (n := 4) 106 (programCode 0x4829075d6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x82002502040080408004200108002200082ce3,0x408c00102300010235b32ffcc00f3f379801f530b669c403ccf300f33cc1e6a7107983cc0001e61e56,0x102004502040080408004200108002200082ce3,0x0,0x408c0010230001f535b36cbcc0000f379801f53668715c03cc0000f33cc1e6c5700003cc0003cc3cb6,0x0,0x0,0x0,0xf4f52c713a4dfb0f3001e60f8b5cc1e9d3983cc01e679803ccf300799e9cc003db3000f6cc001ec80ea5,0x9000440020108c0802110084480012000623a4,0x0,0x900044002010940802110104480012000a27a4,0x1023e3d408cb640798001e616c83cc2d907983cc0f307981e60f303cc1e9cc003db3000f6cc001ec3c925,0x1100044020020800808100204080102000221e4,0x0,0x900044000010840808100404080002004221a4,0x16c87985b200003cc0001e62d903cc1e607983cc7980798f300f31e601e9cc003db3000f6cc001ea56925,0xf307983cc00000000001e62d903cc1e607983ccf3007980000f300001e9cc003db3000f6cc001ea56925,0x0,0xf307983cc00000000001e62d903cc1e607983ccf3007980000f300001e9cc003db3000f6cc001ea56925,0x204008402040080408004200108002200082ce3,0x2100084020020800880102004080402000422e4,0x404010402040080408004200108002200082ce3,0x4100104020020800880102004080402000824e4,0x810020002040080408004200108002200082ce3,0x810020400402080088010200408040200102ce4,0x0,0x0,0xf3b6403cc7980798001e62d903cc1e607983cd023079c08c0f307981e9cc003db3000f6cc001ea56925,0x0,0x0],
[0x472142240501,0x46218c240501,0x472142240501,0x46218c240501,0x442104240501,0x46218c240501,0x442104240501,0x442104240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x10100404004020800880102004080402002034e4,0x2000080002040080408004200108002200082ce3,0x2040080408004200108002200082ce3,0x4000100002040080408004200108002200082ce3,0x2040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3900 : TreeBound (n := 4) 106 (programCode 0x4829075d6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8020200802040080408004200108002200086ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3901 : TreeBound (n := 4) 106 (programCode 0x4829075d70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80402012040080408004200100082002082ce3,0x84002512040080408004200102c82020082ce3,0x80802022040080408004200100102004082de3,0x0,0x0,0x90002412040080408004200108002080082ce3,0x0,0x90002412040080408004200108002080082ce3,0x84002512040080408004200100802020082ce3,0x220000000100000001000000001000020003000010000800100020000100008004000010010000008040000080100000080400000101000000100000001000000001005087d3a7,0x400100008200000010040000012984840002000800040001000200001000880040000020100000400400000801000000800080000400100000800400002002000010210a50ca7,0x1ab29cc003d3983cc1e66a5003cfcc007a73001f530d4a3cc0798f301e603cf583279f9801e601e9dd0c6,0x90002412040080408004200102002080082ce3,0x80002002040080408004200100402000082ce3,0xa0002812040080408004200104002100086ce3,0x80002002040080408004200100002000082ce3,0x440000008200000004800000011000100000040000800200002000804000001040000000100000000400008001000020004000000010000800040002000100000004000252e28,0x0,0x100404012040080408004200100082002082ce3,0x900000002000100009000000024001040002000800040001000200001000080040000020100000400400000801000000800100000400400001020000004004000010210851da7,0x100804022040080408004200100102004082de3,0x0,0x0,0x0,0x0,0x0,0x104004522040080408004200100802020082de3,0x100004002040080408004200100002200082ce3,0x400020001200000008040000022100840002000800040001000200001000880040000020100000400400000801000000800040000200100000800800004002000010210840da7,0x100804022040080408004200100102204082de3],
[0x110004422040080408004200102002080082de3,0x0,0x120004822040080408004200104002100086de3,0x100004002040080408004200100002000082ce3,0x0,0x0,0x0,0x0,0x0,0xf4eda76d3981e60f3001e60f8b5cc1e9d3983cc01e679803ccf300799e9cc003db3000f6cc001ec80ea5,0x1200048002021000802200088080012000243e4,0x0,0x1200048004021000804200108080022000245e4,0x210000000840000001080000002100000000010000080040000200080c000001000000000000000000200010000800040004000000010000000440000001100000004000273228,0x1200048040021000808200208080202000241e4,0x0,0x1200048000021000810200408080002000201e4,0x0,0xf307983cc00000000001e62d903cc1e607983ccf3007980000f300001e9cc003db3000f6cc001ea56925,0x0,0xf307983cc00000000001e62d903cc1e607983ccf3007980000f300001e9cc003db3000f6cc001ea56925,0x0,0x0,0x204008542050080408004020108002200082ee3,0x0,0x0,0x212142240501,0x2721ce240501,0x212142240501,0x25214a240501,0x272104240501,0x202100240501],
[0x272104240501,0x212142240501,0x252148240501,0x2721ce240501,0x252148240501,0x202100240501,0x2200088040021000880202008080402000442e4,0x0,0x0,0x0,0x0,0x0,0x212142240501,0x2721ce240501,0x212142240501,0x25214a240501,0x272104240501,0x202100240501,0x272104240501,0x212142240501,0x252148240501,0x2721ce240501,0x252148240501,0x202100240501,0x4200108040021000880202008080402000844e4,0x810020502040080408004200108002200082ce3,0x820020800402100088020200808040200104ce4,0x0,0x0,0x200028000021000800a00028080402000000e4,0x0,0x0],
[0x462142240501,0x46218c240501,0x462142240501,0x46218c240501,0x462104240501,0x46218c240501,0x462104240501,0x462104240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x10200408004021000880202008080402002054e4,0x2010080402040080408004200108002200082ce3,0x2040080408004200108002200082ce3,0x4020100802040080408004200108002200086ce3,0x2040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_3453 : TreeBound (n := 4) 106 (programCode 0x4829075d) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part011_3454 part011_3455 part011_3456 part011_3457 part011_3586 part011_3587 part011_3588 part011_3589 part011_3590 part011_3591 part011_3592 part011_3769 part011_3850 part011_3851 part011_3900 part011_3901

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4015 : TreeBound (n := 4) 106 (programCode 0x4829075e61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000600018040010088004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4016 : TreeBound (n := 4) 106 (programCode 0x4829075e62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8002200108040020108004200100082002080ce3,0x8000200108040000008004200100002020080ce3,0x8002200108040020108004200100102004080ce3,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a042084642,0x100a041084222,0x100a042084642,0x100a041084222,0x100a0440852a2,0x0,0x100a0440852a2,0x0,0x0,0x0,0x0,0x8004200108040000008004200100202008080ce3,0x80006000120020800880006000102400080402e4,0x8004200108040000008004200100402010080ce3,0x80006000120020800880006000104400100804e4,0x8000200108040000008004200100802020080ce3,0x8000600012002080088000600010840020100ce4,0x0,0x8008200108008040200084002101002040081ce3,0x8000200108000000000004020101002040080ce3,0x8008200108008040200104004101002040081ce3,0x0],
[0x8001200108001020100204008101002040080ce3,0x8000200108000000000004000101002040080ce3,0x8002200108002020100404010101002040080ce3,0x8000200108000000000004000101002040080ce3,0x8000200108000000000804020101002040080ce3,0x8000600012002080080800420018010020100ce4,0x0,0x80006000120020800810004400180100402014e4,0x0,0x80006000120020800820004800180400804020e4,0x0,0x80006000120020800840005000180401008040e4,0x80006000120020800880006000110400402014e4,0x8004200108040000008004200102002080080ce3,0x80006000120020800880006000120400804020e4,0x8000200108040000008004200104002100080ce3,0x80006000120020800880006000140401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4065 : TreeBound (n := 4) 106 (programCode 0x4829075e63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000a00028040010088004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4066 : TreeBound (n := 4) 106 (programCode 0x4829075e64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d9079879bcc1f5307983cfea7f53001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5,0x8000a00022002080088000a000200c00020100e4,0xf307983cc0002d90798f33cc1f5307983ce047023001e9cc01e6f3001e6003ccf300f33cc0799e7032b5,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a042084642,0x100a041084222,0x100a042084642,0x100a041084222,0x100a0440852a2,0x0,0x100a0440852a2,0x0,0x0,0x0,0x0,0x0,0x100a040080022,0x100a041080022,0x100a040080022,0x100a041080022,0x100a040080022,0x100a04208c642,0x100a040080022,0x100a04208c642,0x100a041080022,0x100a0440a94c2],
[0x0,0x100a0440a94c2,0x8010200408040080402004080100202008082ce3,0x0,0x8020200808040100804004100100202008084ce3,0x0,0x0,0x100a041088442,0x100a041088442,0x100a040088442,0x100a041088442,0x100a043088642,0x100a042088442,0x100a042088442,0x100a042088442,0x100a041088442,0x100a0440894c2,0x0,0x100a0440894c2,0x0,0x0,0x8000200808040000004004100100002000080ce3,0x0,0x0,0x100a040080022,0x100a041080022,0x100a040080022,0x100a041080022,0x100a040080022,0x100a042088442,0x100a040080022,0x100a042088442],
[0x100a041080022,0x100a0440a10a2,0x0,0x100a0440a10a2,0x8010200408040080402004080100402010082ce3,0x0,0x8020200808040100804004100100402010084ce3,0x0,0x0,0x100a041088442,0x100a041088442,0x100a040088442,0x100a041088442,0x100a043088642,0x100a042088442,0x100a042088442,0x100a042088442,0x100a041088442,0x100a0440894c2,0x0,0x100a0440894c2,0x0,0x0,0x0,0x0,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a042084642],
[0x100a041084222,0x100a042084642,0x100a041084222,0x100a0440852a2,0x0,0x100a0440852a2,0x8010200408040080402004080100802020082ce3,0x0,0x8000200808040000004004100100802020080ce3,0x0,0x0,0x8000600022001080080400814020806020180da4,0x100a041090882,0x0,0x100a041090882,0x8000600022001080080000800020800020100da4,0x100a042090c82,0xf3000222c00088b0000fa9803cde600f379801f530000fa98003cfcc00f3f4e6003ccf300f3079a357f6,0x100a042090c82,0x100a041090882,0x100a044091902,0x0,0x100a044091902,0x0,0x0,0xf3000222c00088b0000fa9803cde600f379801f5300012fc0003cfcc00f3f4e6003ccf300f3079a357f6,0x0,0x0,0x16c8000f31e60176b47cc1e600fa9841dc2ee03001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x80802022002080088000a000200c02000100e4,0x16c8000799e6026791bcc1e600fa9840cac6553001e9cc01e6f3001e60f300f37980799e601e703345,0x0],
[0x0,0x0,0x8000800022002080088000a000200402000000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800022002080088000a000200402000000e4,0x0,0x0,0x8000a0002200208008040081402100a0402015e4,0x100a041090882,0x0,0x100a041090882,0x8000600022001080080000800020800040100da4,0x100a042090c82,0xf3000222c00088b0000fa9803cde600f379801f530000fa98003db3000f6cde600f30f301e61e62faef6,0x100a042090c82,0x100a041090882,0x100a044091902,0x0,0x100a044091902,0x0,0x0,0xf3000222c00088b0000fa9803cde600f379801f5300012fc0003db3000f6cde600f30f301e61e62faef6,0x0,0x0,0x16c8000f301e616c879bcc1e60fa983d1d08e83001e9cc01e6f3001e679800fa98003d39801e7032b5,0x80802022002080088000a000200402000000e4],
[0x16c80007985b225f8f33cc1e60fa983cfea7f53001e9cc01e6f3001e679800fa980079f9801e703345,0x0,0x0,0x0,0x8118001e61e60faa367cc1e60f379841810c073001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800022002080088000a000200402000000e4,0x0,0x0,0x100a0410a10a2,0x100a0410a10a2,0x0,0x100a0410a10a2,0x80006000220010800800008000220000804021a4,0x100a0420a14c2,0x0,0x100a0420a14c2,0x100a0410a10a2,0x100a0440a10a2,0x0,0x100a0440a10a2,0x0,0x0,0x0,0x0,0x0],
[0x16c8000f3079816c879bcc1e60fa983cfea7f53001e9cc01e6f3001e6f3001e7e6003db3001e7037c5,0x80802022002080088000a000200400000000e4,0x16c80003cc1e625f8f33cc1e6081183d1d08e83001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x100804022002080088000a000200400000000e4,0x0,0x0,0x8118003cc1e60fa9f9bcc1e60f379841810c073001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x100804022002080088000a000200400000000e4,0x0,0x0,0x0,0x0,0x0,0x800022002080088000a000200400000000e4,0x0,0x0,0x100a0410a10a2,0x100a0410a10a2,0x0,0x100a0410a10a2,0x80006000220010800800008000220001004021a4,0x100a0420a14c2,0x0,0x100a0420a14c2,0x100a0410a10a2,0x100a0440a10a2,0x0,0x100a0440a10a2,0x0,0x0,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4291 : TreeBound (n := 4) 106 (programCode 0x4829075e65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8001200048040020108004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4292 : TreeBound (n := 4) 106 (programCode 0x4829075e66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8002200108040020100084002108002200080ce3,0x80012000420020800800810020480402000100e4,0x8002200108040020100104004108002200080ce3,0x0,0x1012041104222,0x1012041104222,0x1012041100222,0x1012041104222,0x101204110c642,0x1012041108642,0x1012041104222,0x1012041108642,0x1012041108642,0x1012041110a82,0x0,0x1012041110a82,0x0,0x10120411212c2,0x0,0x10120411212c2,0x1012042140442,0x1012042140442,0x1012040140022,0x1012042140442,0x1012042140442,0x1012044141902,0x0,0x1318c4240481,0x810020420020800800810020480402000100e4,0x1318c4240481,0x0],
[0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x800004240481,0x4240481,0x800004240481,0x4240481,0x1012044141902,0x8000200008040000002004080108002200080ce3,0x80012000420020800820010800480402004022e4,0x8000200008040000004004100108002200080ce3,0x80012000420020800840011000480402008042e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4341 : TreeBound (n := 4) 106 (programCode 0x4829075e67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8002200088040020108004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4342 : TreeBound (n := 4) 106 (programCode 0x4829075e68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1012040100022,0x1012040104022,0x1012040100022,0x1012040104022,0x1012042108442,0x1012042108442,0x1012040100022,0x1012042108442,0x1012042108442,0x1012042110442,0x8008200208008040200084002101002040081ce3,0x1012042110442,0x8010200008010000000084002102002080080ce3,0x1012042120442,0x8020200808020100800084002104002100084ce3,0x1012042120442,0x80022000820020800800820020880402000100e4,0x0,0x1012040100022,0x1012041104222,0x1012040100022,0x1012041104222,0x1012040108022,0x1012040108022,0x1012040100022,0x1012040108022,0x1012040108022,0x80022000820020800820022000808400204024e4,0x8008200208008040200104004101002040081ce3,0x80022000820020800820022000810400404024e4],
[0x8010200008010000000104004102002080080ce3,0x0,0x8020200808020100800104004104002100084ce3,0x0,0x0,0x1012041104222,0x1012041104222,0x1012041100222,0x1012041104222,0x101204110c642,0x1012041108642,0x1012041104222,0x1012041108642,0x1012041108642,0x1012041110a82,0x0,0x1012041110a82,0x0,0x10120411212c2,0x0,0x10120411212c2,0x1012042140442,0x1012042140442,0x1012040140022,0x1012042140442,0x1012042140442,0x1012044141902,0x0,0x1318c4240481,0x820020820020800800820020880402000100e4,0x1318c4240481,0x0],
[0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x800004240481,0x4240481,0x800004240481,0x4240481,0x1012044141902,0x0,0x139ce8240481,0x112042140442,0x139ce8240481,0x112042140442,0x2318c8240481,0x8240481,0x2318c8240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x80022000820020800820020800880402004024e4,0x0],
[0x139ce8240481,0x0,0x139ce8240481,0x0,0x2318c8240481,0x8240481,0x2318c8240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x80022000820020800840021000880402008044e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4455 : TreeBound (n := 4) 106 (programCode 0x4829075e69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8004200108040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4456 : TreeBound (n := 4) 106 (programCode 0x4829075e6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8004200102002080088004200108040200402ce4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4457 : TreeBound (n := 4) 106 (programCode 0x4829075e6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x8008200208000402010084002100082002080ce3,0x8008200208004020100084002100802020080ce3,0x8008200208000804020084002100102004080de3,0x8008200208000402010084002100082002080ce3,0x8008200208001008040084002100202008080ee3,0x8008200208000000000084002100402000080ce3,0x8008200208002010080084002100402010080ce3,0x8008200208000000000084002100002000080ce3,0x8008200208004020100084002100802020080ce3,0x8008200208000000000084002108002000080ce3,0x8008200208008040200084002101002040081ce3,0x8008200208000000000084002108002000080ce3,0x8008200208010080400084002102002080083ce3,0x8008200208000000000084002108002000080ce3,0x8008200208020100800084002104002100085ce3,0x0,0x0,0x8008200208002010080404020100082002080ce3,0x8008200208000000000004020100002020080ce3,0x8008200208002010080404020100102004080ce3,0x8008200208000000000004020100002000080ce3,0x8008200208000000000804020100202008080ce3,0x8008200208000000000004020100002000080ce3,0x8008200208000000000804020100402010080ce3,0x8008200208000000000004020100002000080ce3,0x8008200208000000000004020100802020080ce3,0x8040200012002080080080402010804020100ce4,0x8008200208000000000004020101002040080ce3,0x80402000120020800800804020110080402014e4,0x0],
[0x80402000120020800800804020120100804020e4,0x0,0x0,0x0,0x8008200208000402010104004100082002080ce3,0x8008200208000000000104004100002020080ce3,0x8008200208000804020104004100102004080de3,0x8008200208000000000104004100002004080ce3,0x8008200208001008040104004100202008080ee3,0x8008200208002010080104004100402010080ce3,0x8008200208002010080104004100402010080ce3,0x8008200208000000000104004100002000080ce3,0x8008200208004020100104004100802020080ce3,0x0,0x8008200208008040200104004101002040081ce3,0x0,0x8008200208010080400104004102002080083ce3,0x0,0x8008200208020100800104004104002100085ce3,0x0,0x0,0x8008200208000402010084002100082002080ce3,0x8008200208000000000004000100002020080ce3,0x8008200208000804020104004100102004080de3,0x8008200208000000000004000100002000080ce3,0x8008200208000000000004000100202008080ce3,0x8008200208000000000004000100002000080ce3,0x8008200208000000000004000100402010080ce3,0x8008200208000000000004000100002000080ce3,0x8008200208000000000004000100802020080ce3,0x8040200022002080080100804020804020100de4,0x0],
[0x80402000220020800801008040210080402015e4,0x0,0x80402000220020800801008040220100804021e4,0x0,0x0,0x8008200208001008040204008108002200080ee3,0x8008200208000000000004000108002200080ce3,0x8008200208002010080404010108002200080ce3,0x8008200208000000000004000108002200080ce3,0x8008200208000000000804020108002200080ce3,0x8040200102002080080804020108010200402ce4,0x0,0x120844240481,0x0,0x120844240481,0x0,0x221084240481,0x20004240481,0x221084240481,0x20004240481,0x420004240481,0x20004240481,0x420004240481,0x20004240481,0x821084240481,0x20004240481,0x821084240481,0x20004240481,0x80402002020020800810080402080102004034e4,0x0,0x120c68240481,0x8008020208804020102004080108002200080ce3],
[0x120c68240481,0x8008080209010080402004080108002200083ce3,0x2218c8240481,0x421088240481,0x2218c8240481,0x20008240481,0x421088240481,0x20008240481,0x421088240481,0x20008240481,0x823188240501,0x20008240481,0x823188240501,0x20008240481,0x0,0x120842240481,0x804024020020800820100804080006000100e4,0x120842240481,0x100804402002080082010080408000a000201e4,0x221084240481,0x20000240481,0x221084240481,0x20000240481,0x420000240481,0x20000240481,0x420000240481,0x20000240481,0x821084240481,0x20000240481,0x821084240481,0x20000240481,0x0],
[0x120c68240481,0x0,0x120c68240481,0x0,0x2218c8240481,0x421088240481,0x2218c8240481,0x20008240481,0x421088240481,0x20008240481,0x421088240481,0x20008240481,0x823188240501,0x20008240481,0x823188240501,0x20008240481,0x0,0x0,0x804028020020800840201008080006000100e4,0x0,0x100804802002080084020100808000a000201e4,0x221084240481,0x20000240481,0x221084240481,0x20000240481,0x420000240481,0x20000240481,0x420000240481,0x20000240481,0x82318c240501,0x20000240481,0x82318c240501],
[0x20000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4618 : TreeBound (n := 4) 106 (programCode 0x4829075e6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80082002020020800880082002080402004034e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4619 : TreeBound (n := 4) 106 (programCode 0x4829075e6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8010200408040080408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4620 : TreeBound (n := 4) 106 (programCode 0x4829075e6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x82002100440020108004200108002200080ce3,0x900024020020800880102004080402000100e4,0x102004100440020108004200108002200080ce3,0x0,0x408c0010230001f531e6003d39800f379801f535eec3cc03cc0000f33cc1e6c5700003cc0003cc3cb6,0x0,0x0,0x0,0x142048440222,0x1420424406c2,0x0,0x1420424406c2,0x142048440222,0x1420444412a2,0x0,0x1420444412a2,0x16c87985b200003cc0003cc2d900001e600000007980798f300f31e601e9cc003db3000f6cc001ea56925,0x142048440222,0x0,0x142048440222,0x204008000840000008004200108002200080ce3,0x2100084020020800880102004080402000422e4,0x404010000840000008004200108002200080ce3,0x4100104020020800880102004080402000824e4,0x800020000040000008004200108002200080ce3,0x810020402002080088010200408040200102ce4,0x0,0x0,0x900024020020800800900024080402000100e4,0x0,0x0],
[0x4318c2240481,0x400000240481,0x4318c2240481,0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x421088240481,0x400000240481,0x421088240481,0x400000240481,0x10100404020020800880102004080402002034e4,0x2000080000040000008004200108002200080ce3,0x40000008004200108002200080ce3,0x4000100000040000008004200108002200080ce3,0x40000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4669 : TreeBound (n := 4) 106 (programCode 0x4829075e6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8020200808040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4670 : TreeBound (n := 4) 106 (programCode 0x4829075e70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80402010440010088004200100082002080ce3,0x84002000440000008004200100002020080ce3,0x80802020440010088004200100102004080ce3,0x0,0xf303cc1e60f316c81e6079803cde600f379801f5301e63cc0798f301e63cc1e60f307981e60f30799a96,0x80002000440000008004200108002000080ce3,0x16c8000f31e6016d367cc1e600fa9841dc2ee03001e9cc01e6f3001e601e60f307983cc3cc1e7032b5,0x80002000440000008004200108002000080ce3,0x84002000440000008004200100802020080ce3,0x4203008020020800880202008008400200844e4,0x0,0x4203008020020800880202008010400400844e4,0x90002410440092498004200102002080082ce3,0x80002000440000008004200100402000080ce3,0xa0002810440110888004200104002100084ce3,0x80002000440000008004200100002000080ce3,0xa00028020020800880202008080402000100e4,0x0,0x100404010440010088004200100082002080ce3,0x100004000440000008004200100002020080ce3,0x100804020440010088004200100102004080ce3,0x0,0x0,0x0,0x16c8000799e6025ff9bcc1e600fa9840cac6553001e9cc01e6f3001e601e60f30f307983cc1e703345,0x0,0x104004000440000008004200100802020080ce3,0x104004000440000008004200100802200080ce3,0x0,0x20202008020020800880202008010400404060e4],
[0x1100044204400944a8004200102002080082de3,0x16c8000799e6026791bcc1e600fa9840cac6553001e9cc01e6f3001e63cc00f30f307d8c8c1e703345,0x120004820440110888004200104002100084ce3,0x100004000440000008004200100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x142048440222,0x1420424406c2,0x0,0x1420424406c2,0x142048440222,0x1420444412a2,0x0,0x1420444412a2,0x0,0x142048440222,0x0,0x142048440222,0x0,0x81180079801e6811879bcc1e63d3983df1af7e00f4e600f4e6000f4e9cc001023000408c001e7032b5,0x204008000840000008004020108002200080ce3,0x81180079805b28118f33cc1e63d3983df1af7e00f4e6007b66001e7e9cc0010230007d4c001e703345,0x0,0x2110c2240481,0x221084240481,0x2110c2240481,0x221084240481,0x221084240481,0x221084240481],
[0x221084240481,0x221084240481,0x2539c8240501,0x221084240481,0x2539c8240501,0x201080240481,0x2200088020020800880202008080402000442e4,0x0,0xfa98001e60798fa9879bcc1e6f37983df1af7e00f4e600f4e6000f4e9cc001f53000408c001e7037c5,0x0,0x8118001e601e6fa98f33cc1e6f37983dd34e8b00f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0x2110c2240481,0x221084240481,0x2110c2240481,0x221084240481,0x221084240481,0x221084240481,0x221084240481,0x221084240481,0x2539c8240501,0x221084240481,0x2539c8240501,0x201080240481,0x4200108020020800880202008080402000844e4,0x800020000040000008004200108002200080ce3,0x820020802002080088020200808040200104ce4,0x0,0x0,0xa00028020020800800a00028080402000100e4,0x0,0x0],
[0x4318c2240481,0x400000240481,0x4318c2240481,0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x421088240481,0x400000240481,0x421088240481,0x400000240481,0x10200408020020800880202008080402002054e4,0x2010080402040080408004200108002200082ce3,0x40000008004200108002200080ce3,0x4020100804040100808004200108002200084ce3,0x40000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4014 : TreeBound (n := 4) 106 (programCode 0x4829075e) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part011_4015 part011_4016 part011_4065 part011_4066 part011_4291 part011_4292 part011_4341 part011_4342 part011_4455 part011_4456 part011_4457 part011_4618 part011_4619 part011_4620 part011_4669 part011_4670

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4784 : TreeBound (n := 4) 106 (programCode 0x4829075f61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000600014040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4785 : TreeBound (n := 4) 106 (programCode 0x4829075f62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8002200104040100808004200100082002084ce3,0x8020200104040100808004200104002020084ce3,0x8002200104040100808004200100102004084ce3,0x0,0x1032121204501,0x8000200104020100800004020100002000084ce3,0x1032121204501,0x1022100200501,0x1022142208501,0x8000200104040100800004100100002000084ce3,0x1022142208501,0x0,0xf3097e3cc0798f3001e7e607987981e60f3079803cc1e60f307983cc1e9cc003cfcc00f30f301ea19995,0x8000200104000100800004000100002000084ce3,0x0,0x0,0xf307983cc007a73001e7e61e607987980f307981e601e67980799e601e9cc003db3000f379801ea19995,0x0,0x0,0x0,0x8004200104040100808004200100202008084ce3,0xf307983cc0000f3001e7e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea19995,0x8004200104040100808004200100402010084ce3,0xf307983cc0000f3001e7e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea19995,0x8020200104040100808004200100802020084ce3,0x0,0x1062181230501,0x8000200104020100800004020100002000084ce3,0x1062181230501,0x8000200104000100800004000100002000084ce3,0x1072142238501],
[0x0,0x1072142238501,0x0,0x1062104230501,0x8000200104000100800004000100002000084ce3,0x1062104230501,0x0,0x0,0x0,0x0,0x0,0x0,0x1062181210501,0xf307983cc0798f3001e7e61e607981e60f30798f3001e6f3007983cc1e63cc03ccf300f31e601ea19995,0x1062181210501,0x0,0x1072142210501,0x0,0x1072142210501,0x0,0x1062104210501,0x8000200104000100800004000101002040084ce3,0x1062104210501,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x40000080100000080400020a01000082800400000208000400004000002020001010000400200008000800004008000020008040000002000200040400000021003000102108430a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8004200104040100808004200102002080084ce3,0xf3000222c00088b0000d4a003db3000f379801f53079a22c0002d9000097e315c79879807983cc1e7e56,0x8000200104040100808004200104002100084ce3,0x400021001000004004000008010000020020003000020001000200030000200010004000010010000010040000080100000080600000100200000106000001002000001009087d7a7]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4866 : TreeBound (n := 4) 106 (programCode 0x4829075f63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000a00024040100808004200108002200084de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4867 : TreeBound (n := 4) 106 (programCode 0x4829075f64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8000601004040100808004200100082002084ce3,0xf307983cc0798f307981e61e607987980f30798f3001e9cc007a73001e6f3003cfcc00f30f301ea19995,0x8000a01004040100808004200100102004084de3,0x0,0x100a121204501,0x8000200004020100800004020100002000084ce3,0x100a121204501,0x1002100200501,0x1012142208501,0x8000200004040100800004100100002000084ce3,0x1012142208501,0x0,0xf307983cc0798f3001e7e607987981e60f3079803cc1e60f307983cc1e9cc003cfcc00f30f301ea19995,0x1002100200501,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a141208501,0x1022104208501,0x100a141208501,0x1002100208501,0x1012142208501,0x8020200804040100804004100100202008084ce3,0x1012142208501,0x8020201004040100808004100100202008084ce3,0x1022104208501,0x1002100208501],
[0x1022104208501,0x0,0x8010200404040100802004080100202008086ce3,0x0,0x8020200804040100804004100100202008084ce3,0x0,0x0,0x16c80003cc1e616c81e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea19995,0x808020202020080880002000002400080000e4,0x4458000f3079825f81e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea3bc55,0x1008040202020080880002000002400080000e4,0x8118001e60f3081181e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea21315,0x0,0x1ed98007983cc0fa981e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea37f95,0x0,0x8000200020080880002000002400080000e4,0x8008200202020080880002000002400080000e4,0x0,0x10008400200020080880002000002400080000e4,0x0,0x0,0x0,0x0,0x0,0x100a141208501,0x1022104208501,0x100a141208501,0x1002100208501,0x1012142208501,0x8000200802040100800004100100201010084ca3,0x1012142208501,0x0],
[0x1022104208501,0x1002100208501,0x1022104208501,0x0,0x8010200404040100802004080100402010086ce3,0x0,0x8020200804040100804004100100402010084ce3,0x0,0x0,0x16c80003cc1e616c81e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea19995,0x808020204020100880002000004400100000e4,0x4458000f3079825f81e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea3bc55,0x1008040204020100880002000004400100000e4,0x8118001e60f3081181e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea21315,0x0,0x1ed98007983cc0fa981e61e607987980f30798f3001e9cc007a73001e9cc003db3000f3f3001ea37f95,0x0,0x8000200020100880002000004400100000e4,0x8008200204020100880002000004400100000e4,0x0,0x10008400200020100880002000004400100000e4,0x0,0x0,0x0,0x0,0x8020201004040100808004200100802020084ce3,0x0,0x8000200014000100800084002100002000084ce3,0x8000200004020100800004020100002000084ce3,0x8000200024000100800104004100002000084ce3,0x1002100200501,0x1dcd650ee6b9f3598a853809765000eee25d9400001dcd6500077536165003ba23d597ba9b46c2cbdcd65773594001dd4d8597b9aca01dcd82cd65077360b35941dcd82cd6503b9b059aca03b9b059b41359403bc2250c305ee6b45cd6577359400000ee6b2800000ef79450ad31b9],
[0x0,0xf30007d4c224b5300fa9f983cc3cc007a7307b660799e603cde600f31e63cc010425307e060c1e8e9345,0x0,0x8000200104020100800804020100002000084ce3,0x1002100200501,0x8000200204020100801004040100002000084ce3,0x0,0x0,0x0,0x0,0x0,0x8020201004040100808004200101002040084ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf30007d4c1e7f5300079f983cc3cc007a7307b660799e603cde600f31e603cc10230007d4fcc1e8e9345,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80403004040100808004200102002080084ce3,0x8004021004040100808004200102002080084ce3],
[0x100805004040100808004200102002080084de3,0x0,0x201009004040100808004200102002080084ee3,0x8020101004040100808004200102002080084ce3,0x402011004040100808004200102002080084ce3,0x8020101004040100808004200102002080084ce3,0x804021004040100808004200102002080084ce3,0x8008200204020100880002000004402000000e4,0x0,0x10008400200020100880002000004402000000e4,0x0,0x0,0x4020101004040100808004200102002080084ce3,0x0,0x0,0x400020011000000044000000090000000220003014020001000200030140200010000002010000002010000010080000010080402000100002000104020001000020001009097d7a7,0x400021801000086004000000010000000020003400020001000200014000200010004300010000800040000000080004000080680000100000000104000001000000001009087dfa7,0x0,0x400020001000080004000000010000000020003000020001000200030000200010004000010010000010000000080000000080400000100000000104000001000000001009087d7a7,0x0,0x400030001000080004000000010000000020003000040000000100020000200010006000010000000040000000020020000080600000101000000204000000800000001008487ee27,0x0,0x0,0x0,0x400020001000080004000000010000000020003000020001000200030000200010004000010010000010000000080000000080400000100000000104000001000000001009087d7a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x80403004040100808004200104002100084ce3,0x21004040100808004200104002100084ce3,0x100805004040100808004200104002100084de3,0x201004040100808004200104002100084ce3,0x201009004040100808004200104002100084ee3,0x0,0x402011004040100808004200104002100084ce3,0x0,0x804021004040100808004200104002100084ce3,0x201004040100808004200104002100084ce3,0x0,0x201004040100808004200104002100084ce3,0x0,0x0,0x4020101004040100808004200104002100084ce3,0x0,0x0,0x400020011000000044000000090000000220003000020001000200030000200010000002010000002010000010080000010080400000100000000104000001000000001009097d7a7,0x400021801000086004000000010000000020003400020001000200014000200010004300010000800040000000080004000080680000100000000104000001000000001009087dfa7,0x0,0x400020001000080004000000010000000020003000020001000200030000200010004000010010000010000000080000000080400000100000000104000001000000001009087d7a7,0xf307983cc002e83000b826000fa983cfdb3079800f33cc01e67980799e9cc003db3000f301e61ea214c5,0x400030001000080004000000010000000020003000040000000100020000200010006000010000000040000000020020000080400000101000000204000000800000001008487ee27,0x0,0x0,0x0,0x400020001000080004000000010000000020003000020001000200030000200010004000010010000010000000080000000080400000100000000104000001000000001009087d7a7,0x0,0x0,0x0,0x0,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5060 : TreeBound (n := 4) 106 (programCode 0x4829075f65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8001200044040100808004200108002200084ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5061 : TreeBound (n := 4) 106 (programCode 0x4829075f66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8002200804040100800084002108002200084ce3,0xf307983cc0798f301e61e61e607981e60f30798f3001e9cc007983cc1e9cc003db3000f6cc001ea19995,0x8002200804040100800104004108002200084ce3,0x0,0x105a121204501,0x0,0x105a121204501,0x1042100200501,0x1042100208501,0x0,0x1042100208501,0x0,0x8000200804040100804004100100802020084ce3,0x8000200804000100800004000100002000084ce3,0x8000200804040100804004100101002040084ce3,0x0,0x0,0x0,0x0,0x0,0x1072142240501,0x8000200802040100800004100108001200084ca3,0x1072142240501,0xf307983cc0000f301e61e61e607987980f30798f3001e9cc0079bcc01e9cc003db3000f6cc001ea19995,0x1042104240501,0x8000200804000100800004000108002200084ce3,0x1042104240501,0x0,0x0,0x0,0x0],
[0x0,0x272142240501,0x842108240501,0x272142240501,0x842108240501,0x442104240501,0x842108240501,0x442104240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501,0x8020200804040100802004080108002200084ce3,0xf30b643cc0000f301e61e62d907980000f307996c8079bcc007980001e9cc003db3000f6cc001ea19cf5,0x8000200804040100804004100108002200084ce3,0x0,0x0,0x0,0x0,0x0,0x27214a240501,0x842108240501,0x27214a240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501],
[0x42100240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5126 : TreeBound (n := 4) 106 (programCode 0x4829075f67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8002200084040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5127 : TreeBound (n := 4) 106 (programCode 0x4829075f68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x104a121204501,0x1062181230501,0x104a121204501,0x104a121204501,0x1052141208501,0x1052141228501,0x1052141208501,0x1042101220501,0x1062181210501,0x1042101220501,0x1062181210501,0x0,0x1042101220501,0x8000200804000100800084002108002000084ce3,0x1042101220501,0x0,0xf307983cc0798f301e61e61e607981e60f30798f3001e9cc007983cc1e9cc003db3000f6cc001ea19995,0x0,0x104a121204501,0x1062181230501,0x104a121204501,0x104a121204501,0x1052141208501,0x1052141228501,0x1052141208501,0x1042101220501,0x1062181210501,0x1042101220501,0x1062181210501,0x0],
[0x1042101220501,0x0,0x1042101220501,0x0,0x0,0x104a121204501,0x0,0x104a121204501,0x1042100200501,0x1042100208501,0x0,0x1042100208501,0x0,0x0,0x8000200804000100800004000100002000084ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x1052142240501,0x0,0x18ae0003d3b6611160f325f879801ee8b07983db31e60f6d39bcc01e9cc001f53000f6cc001ea19485,0x0,0x27de000f3811820460f325f879802055307983db31e6102379bcc01e9cc001f53000f6cc001ea1d145,0x0,0x2721ce240501,0x842108240501,0x2721ce240501,0x842108240501,0x46218c240501],
[0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1052142240501,0x0,0x16c80003cc1e611161e61e6079800088b0798f3001e6003d39bcc01e9cc003db3000f6cc001ea19995,0x0,0x4458000f3079820461e61e60798001f530798f3001e600f379bcc01e9cc003db3000f6cc001ea3bc55,0x0,0x25214a240501,0x842108240501,0x25214a240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1042104240501,0x8000200804000100800004000108002200084ce3,0x1042104240501,0x0,0x0,0x0,0x0],
[0x0,0x252142240501,0x842108240501,0x252142240501,0x842108240501,0x442104240501,0x842108240501,0x442104240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501,0x0,0x14a128240501,0x8004020804004100802004080108002200084ce3,0x14a128240501,0x8010080804010100802004080108002200086ce3,0x252148240501,0x842108240501,0x252148240501,0x842108240501,0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0xf30b643cc0000f301e61e62d907980000f307996c8079bcc007980001e9cc003db3000f6cc001ea19cf5,0x0],
[0x14a128240501,0x0,0x14a128240501,0x0,0x252148240501,0x842108240501,0x252148240501,0x842108240501,0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x0,0x0,0x0,0x0,0x0,0x252142240501,0x842108240501,0x252142240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501],
[0x42100240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5288 : TreeBound (n := 4) 106 (programCode 0x4829075f69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8004200104040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5289 : TreeBound (n := 4) 106 (programCode 0x4829075f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8000201004040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5290 : TreeBound (n := 4) 106 (programCode 0x4829075f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1022121204501,0x1022181230501,0x1022121204501,0x1022121204501,0x1022141208501,0x1022141228501,0x1022141208501,0x1022101220501,0x1022181210501,0x1022181230501,0x1022181210501,0x0,0x1022101220501,0x8008200204000100800084002108002000085ce3,0x1022101220501,0x8008200204020100800084002108002100085ce3,0x0,0x10221c6204501,0x0,0x10221c6204501,0x8008200204020100800004020100002000085ce3,0x1022104208501,0x1022104220501,0x1022104208501,0x1022104220501,0x0,0xf30079bcc01e6f3003cde600007981e60f3079800001e600007983cc1e63cc03ccf300f33cc01eb0c995,0x0,0x0,0x1022104220501],
[0x0,0x1022104220501,0x0,0x0,0x1022121204501,0x1022181230501,0x1022121204501,0x1022121204501,0x1022141208501,0x1022141228501,0x1022141208501,0x1022101220501,0x1022181210501,0x1022181230501,0x1022181210501,0x0,0x1022101220501,0x0,0x1022101220501,0x0,0x0,0x1022121204501,0x0,0x1022121204501,0x1022100200501,0x1022100208501,0x0,0x1022100208501,0x0,0x0,0x0,0x0],
[0x0,0x0,0x400000009000080024000200010000000260000008100000020400000080800000100001200080004800200010000800020002200030000800040001000080001000400020016eea8,0x0,0x0,0x1022142240501,0x8004200202040100800804100108001200084ca3,0x1022142240501,0x0,0x0,0x0,0x0,0x0,0x22214a240501,0xc2218c240501,0x22214a240501,0x822108240501,0x42218c240501,0xc2218c240501,0x42218c240501,0x22108240501,0x822108240501,0xc2218c240501,0x822108240501,0x822108240501,0x1022104240501,0x1022104240501,0x1022104240501,0x0,0x0,0x0,0x0],
[0x0,0x222142240501,0xc2218c240501,0x222142240501,0x822108240501,0x422104240501,0x422104240501,0x422104240501,0x22100240501,0x822108240501,0xc2218c240501,0x822108240501,0x822108240501,0x0,0x122128240501,0x8008020204004100802004080108002200085ce3,0x122128240501,0x8008080204010100802004080108002200087ce3,0x222148240501,0xc22188240501,0x222148240501,0x822108240501,0x422188240501,0xc22188240501,0x422188240501,0x22108240501,0x822108240501,0xc22188240501,0x822108240501,0x822108240501,0x0,0x84002202042500880404312108001200084ca3],
[0x0,0x108004204002100800404010108002200085ce3,0x0,0x2221ce240501,0xc2218c240501,0x2221ce240501,0x82210c240501,0x42218c240501,0xc2218c240501,0x42218c240501,0x22108240501,0x82210c240501,0xc2218c240501,0x82210c240501,0x82210c240501,0x0,0x122128240501,0x0,0x122128240501,0x0,0x222148240501,0xc22188240501,0x222148240501,0x822108240501,0x422188240501,0xc22188240501,0x422188240501,0x22108240501,0x822108240501,0xc22188240501,0x822108240501,0x822108240501],
[0x0,0x0,0x0,0x0,0x0,0x222148240501,0xc2218c240501,0x222148240501,0x822108240501,0x422188240501,0xc2218c240501,0x422188240501,0x22108240501,0x822108240501,0xc2218c240501,0x822108240501,0x822108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5467 : TreeBound (n := 4) 106 (programCode 0x4829075f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80403014040100808004200108002200084ce3,0x0,0x402021084040100808004200100082002084ce3,0x4020021804040100808004200104002020084ce3,0x402021084040100808004200100102004084ce3,0x0,0x804021104040100808004200100202008084ce3,0x880022002020080880002000002400080000e4,0x804021104040100808004200100402010084ce3,0x880022004020100880002000004400100000e4,0x4020021804040100808004200100802020084ce3,0x0,0x0,0x0,0x880022004020100880002000000400100000e4,0x880022020020800880082002020400804034e4,0x21004040100808004200104002100084ce3,0x880022040021000880082002040401008054e4,0x100805024040100808004200108002200084de3,0x0,0x80601014040100808004200100082002084ce3,0x4020201804040100808004200104002020084ce3,0x100a01024040100808004200100102004084de3,0x0,0x0,0x1080042002020080880002000002400080000e4,0x0,0x1080042004020100880002000004400100000e4,0x4020201804040100808004200100802020084ce3,0x0,0x4020201804040100808004200101002040084ce3],
[0x0,0x0,0x1080042020020800880082002020400804034e4,0x201004040100808004200104002100084ce3,0x1080042040021000880082002040401008054e4,0x201009044040100808004200108002200084ee3,0x0,0x402101084040100800084002108002200084ce3,0x2080082000820020800800020080402000000e4,0x402101084040100800104004108002200084ce3,0x0,0xe72142240501,0x842108240501,0xe72142240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x402011084040100808004200108002200084ce3,0x0,0x0,0x4080102000820020800800020080402000000e4,0x0,0x0,0xa52142240501,0x842108240501,0xa52142240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x804021104040100808004200108002200084ce3,0x201004040100808004200108002200084ce3,0x0,0x0,0x0,0x0,0x0,0x432142240501,0x46218c240501,0x432142240501,0x46218c240501,0x422104240501,0x422104240501,0x422104240501,0x422104240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x201004040100808004200108002200084ce3,0x0,0x0,0x80102000820020800800020080402000000e4],
[0x0,0x0,0x852142240501,0x842108240501,0x852142240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x20080802020020800880082002080402004034e4,0x4020101804040100808004200108002200084ce3,0x40081002040021000880082002080402008054e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5580 : TreeBound (n := 4) 106 (programCode 0x4829075f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8010200404040100808004200108002200086ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5581 : TreeBound (n := 4) 106 (programCode 0x4829075f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x82002984040100808004200108002200084ce3,0xf307983cc079803d57e1e61e607987980f30798f3001e9cc007a73001e9cc003db3000f6cc001ea19995,0x102004984040100808004200108002200084ce3,0x0,0xf307983cc001e6018d41661e607987980f30798000f4e6003d39800f4e9cc003db3000f6cc001ea19995,0x0,0xf307983cc003cc0466bae61e607987980f30798003cde600f379801e7e9cc003db3000f6cc001ea37f95,0x0,0xf307983cc007980831c7e6000fa98003db3079800799e601e67980799e9cc003db3000f6cc001ea19995,0xf307983cc00000007981e600007987980f3079800001e6000079bcc01e9cc003db3000f6cc001ea19995,0xf307983cc007981ef9c7e6003d39800f3f3079801e61e607987980f31e9cc003db3000f6cc001ea19995,0x0,0xf307983cc079803d57e1e607987981e60f3079803cc1e60f307983cc1e9cc003db3000f6cc001ea19995,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x204008904040100808004200108002200084ce3,0xf307983cc00003cc7981e61e607987980f30798f3001e9cc007a73001e9cc003db3000f6cc001ea19995,0x404010904040100808004200108002200084ce3,0xf307983cc00003cc7981e61e607987980f30798f3001e9cc007a73001e9cc003db3000f6cc001ea19995,0x820020804040100808004200108002200084ce3,0x0,0x0,0x8100204008020200800820020880402000100e4,0x0,0x0,0xe72142240501],
[0x2108240501,0xe72142240501,0x2108240501,0x2104240501,0x2100240501,0x2104240501,0x2100240501,0x2108240501,0x2100240501,0x2108240501,0x2100240501,0x0,0x0,0xf379803cc79807a17e1e61e607981e60f30798f3001e9cc007983cc1e9cc003db3000f6cc001ea19995,0x0,0x0,0x472142240501,0x46218c240501,0x472142240501,0x46218c240501,0x442104240501,0x46218c240501,0x442104240501,0x442104240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x0,0x0,0x10100404000020400800820020880402000100e4,0x0],
[0x0,0x272142240501,0x2108240501,0x272142240501,0x2108240501,0x2104240501,0x2100240501,0x2104240501,0x2100240501,0x2108240501,0x2100240501,0x2108240501,0x2100240501,0x2000080004040100808004200108002200084ce3,0x4040100808004200108002200084ce3,0x4000100004040100808004200108002200084ce3,0x4040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5662 : TreeBound (n := 4) 106 (programCode 0x4829075f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8020200804040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5663 : TreeBound (n := 4) 106 (programCode 0x4829075f70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80402014040100808004200100082002084ce3,0x84002914040100808004200104802020084ce3,0x80802024040100808004200100102004084de3,0x0,0x81003004040100808004200100202008084ee3,0xa0002814040100808004200108002100084ce3,0x82003004040100808004200100402010084ce3,0xa0002814040100808004200108002100084ce3,0x84002914040100808004200100802020084ce3,0xf4e9cc003db300001e63d3983cc0000f303cc1f5307983cc0000f3000003cde600f379800f3000001e56,0x0,0x1000080002800280012000a0001800284002000080004000040022000200090004000008010000010040000080100000080000100021000100400001000210005001021294b4a7,0x90002414040100808004200102002080086ce3,0x80002004040100808004200100402000084ce3,0xa0002814040100808004200104002100084ce3,0x80002004040100808004200100002000084ce3,0xf307983cc079803d3981e61e607987980f30798f3001e9cc007a73001e9cc003db3000f6cc001ea19995,0x0,0x100404014040100808004200100082002084ce3,0x120004824040100808004200104002020084ce3,0x100804024040100808004200100102004084de3,0x0,0x101005004040100808004200100202008084ee3,0x0,0x102005004040100808004200100402010084ce3,0x0,0x104004924040100808004200100802020084ce3,0x100004004040100808004200100002200084ce3,0x0,0x100804024040100808004200100102204084de3],
[0x110004424040100808004200102002080086de3,0x102005004040100808004200100402220084ce3,0x120004824040100808004200104002100084ce3,0x100004004040100808004200100002000084ce3,0x0,0x0,0x0,0x0,0x0,0xf307983cc000f30811bea6000fa98003db3079800799e601e67980799e9cc003db3000f6cc001ea21315,0xf307983cc00000007981e600007987980f3079800001e6000079bcc01e9cc003db3000f6cc001ea19995,0xf307983cc003cc1eda74e6003d39800f3f3079801e61e607987980f31e9cc003db3000f6cc001ea37f95,0x0,0xf307983cc079803d3981e607987981e60f3079803cc1e60f307983cc1e9cc003db3000f6cc001ea19995,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200409004040100800084002108002200084ce3,0x204008944060100808004020108002200084ce3,0x200809004040100800104004108002200084de3,0x0,0x212142240501,0x2721ce240501,0x212142240501,0x25214a240501,0x272104240501,0x202100240501],
[0x272104240501,0x212142240501,0x252148240501,0x2721ce240501,0x252148240501,0x202100240501,0x0,0x402501014040100800084002108002200084ce3,0x2200088000820080800800020080402000000e4,0x402901024040100800104004108002200084de3,0x0,0xe72142240501,0x842108240501,0xe72142240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x0,0x400411004040100800084002108002200084ce3,0x0,0x400811004040100800104004108002200084de3,0x0,0x212142240501,0x2721ce240501,0x212142240501,0x25214a240501],
[0x272104240501,0x202100240501,0x272104240501,0x212142240501,0x252148240501,0x2721ce240501,0x252148240501,0x202100240501,0x0,0x0,0x4200108000820100800800020080402000000e4,0x0,0x0,0xa52142240501,0x842108240501,0xa52142240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x820020904040100808004200108002200084ce3,0x0,0x0,0x8200208008020200800820020880402000100e4,0x0,0x0,0xc62142240501],
[0x2108240501,0xc62142240501,0x2108240501,0x2104240501,0x2100240501,0x2104240501,0x2100240501,0x2108240501,0x2100240501,0x2108240501,0x2100240501,0x1020040a04040100808004200108002200084ce3,0x0,0x0,0x10200408000020400800820020880402000100e4,0x0,0x0,0x212142240501,0x2108240501,0x212142240501,0x2108240501,0x2104240501,0x2100240501,0x2104240501,0x2100240501,0x2108240501,0x2100240501,0x2108240501,0x2100240501,0x2010080404040100808004200108002200086ce3,0x4040100808004200108002200084ce3,0x4020100804040100808004200108002200084ce3],
[0x4040100808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_4783 : TreeBound (n := 4) 106 (programCode 0x4829075f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part011_4784 part011_4785 part011_4866 part011_4867 part011_5060 part011_5061 part011_5126 part011_5127 part011_5288 part011_5289 part011_5290 part011_5467 part011_5580 part011_5581 part011_5662 part011_5663

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5825 : TreeBound (n := 4) 106 (programCode 0x4829076061) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040002018004200100082002080ce3,0x8000600018040020108004200100802020080ce3,0x8000600018040004028004200100102004080de3,0x0,0x1002040004022,0x100a041084222,0x100a041084222,0x100a041084222,0x1002040004022,0x1012042104442,0x1002040004022,0x1012042104442,0x1002040004022,0x0,0x0,0x0,0x8000600018040080402004080108002080082ce3,0x0,0x8000600018040100804004100108002100084ce3,0x0,0x8000600018040008048004200100202008080ee3,0x8000600018040000008004200108002000080ce3,0x8000600018040010088004200100402010080ce3,0x8000600018040000008004200108002000080ce3,0x8000600018040020108004200100802020080ce3,0x0,0x1012042110442,0x80022000940021000800820020808040200100e4,0x80022010840021000840022000808400208044e4,0x8002200184002100080102004080804020020de4,0x1012042110442],
[0x1012042110442,0x1012040110022,0x1012042110442,0x1012042110442,0x1012044111902,0x0,0x1012044111902,0x0,0x0,0x0,0x80022010840021000840021000808400208044e4,0x0,0x8000600018008040200084002101002040081ce3,0xf30000b640002d90000b641e60f3003cc1e60f3f3001e61e607983cc1e63cc03ccf300f31e601e6c7195,0x8000600018008040200104004101002040081ce3,0x0,0x8000600018001040200204008101002040081ee3,0x0,0x8000600018002040200404010101002040081ce3,0x0,0x8000600018008040200804020101002040081ce3,0xf3000222c0002d90000ba0e046f3000001e60f4023079800007980001e63cc03ccf300f31e601e6c74f5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1012042110442,0x80022000940021000800820020810080400100e4,0x80022010840021000840022000810400408044e4],
[0x80022002840021000801020040810080400215e4,0x1012042110442,0x1012042110442,0x1012040110022,0x1012042110442,0x1012042110442,0x1012044111902,0x0,0x1012044111902,0x0,0x0,0x0,0x80022010840021000840021000810400408044e4,0x8000600018040080408004200102002080082ce3,0x8000600018040010088004200108002010080ce3,0x8000600018040100808004200104002100084ce3,0x8000600018040000008004200108002000080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5906 : TreeBound (n := 4) 106 (programCode 0x4829076062) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x100a040080022,0x100a041080022,0x100a040080022,0x100a041080022,0x100a040080022,0x100a04208c642,0x100a040080022,0x100a04208c642,0x100a041080022,0x100a0440a52a2,0x0,0x100a0440a52a2,0x8002200108040080402004080100082002082ce3,0x0,0x8002200108040100804004100100082002084ce3,0x0,0x8000200108040000008004200100002020080ce3,0x0,0x100a040080022,0x100a041080022,0x100a040080022,0x100a041080022,0x100a040080022,0x100a042088442,0x100a040080022,0x100a042088442,0x100a041080022,0x0,0x0,0x0],
[0x8002200108040080402004080100102004082ce3,0x0,0x8002200108040100804004100100102004084ce3,0x0,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a042084642,0x100a041084222,0x100a042084642,0x100a041084222,0x100a0440852a2,0x0,0x100a0440852a2,0x0,0x0,0x0,0x0,0x8004200108040000008004200100202008080ce3,0x80006000140021000880006000102400080402e4,0x8004200108040000008004200100402010080ce3,0x80006000140021000880006000104400100804e4,0x8000200108040000008004200100802020080ce3,0x8000600014002100088000600010840020100ce4,0x0,0x0,0x8000200108000000000004020101002040080ce3,0x0,0x0],
[0x8001200108001008040204008101002040080ee3,0x8000200108000000000004000101002040080ce3,0x8002200108002010080404010101002040080ce3,0x8000200108000000000004000101002040080ce3,0x8000200108000000000804020101002040080ce3,0x8000600014002100080800420018020020100ce4,0x0,0x80006000140021000810004400180200402014e4,0x0,0x80006000140021000820004800180400804020e4,0x0,0x80006000140021000840005000180401008040e4,0x80006000140021000880006000110400402014e4,0x8004200108040000008004200102002080080ce3,0x80006000140021000880006000120400804020e4,0x8000200108040000008004200104002100080ce3,0x80006000140021000880006000140401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5987 : TreeBound (n := 4) 106 (programCode 0x4829076063) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8000a00028040002018004200100082002080ce3,0x8000a00028040000008004200100002020080ce3,0x8000a00028040004028004200100102004080de3,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x101a042184642,0x100a041084222,0x101a042184642,0x100a041084222,0x8000a010240021000808008200201200040241e4,0x0,0x8000a010240021000810008400201200040241e4,0x0,0x0,0x0,0x0,0x8000a00028040008048004200100202008080ee3,0x0,0x1002040008022,0x100a041088442,0x1002040008022,0x100a041088442,0x1002040008022,0x1012042108442,0x1002040008022,0x1012042108442,0x1002040008022],
[0x8004201004002100080804020100220008804ce4,0x0,0x80082010040021000810080402002200088054e4,0x8000a00028040004022004080100102004080de3,0x0,0x8000a00028040004024004100100102004080de3,0x0,0x8000a00028040010088004200100402010080ce3,0x0,0x1002040008022,0x100a041088442,0x1002040008022,0x100a041088442,0x1002040008022,0x1012042108442,0x1002040008022,0x1012042108442,0x1002040008022,0x8004201004002100080804020100420010804ce4,0x0,0x80082010040021000810080402004200108054e4,0x0,0x0,0x0,0x0,0x8000a00028040020108004200100802020080ce3,0x0,0x4203010040021000880202008008400200844e4,0xa00031040021000880202008008400200100e4,0x100804020040000008004200100002200080ce3,0x0,0x0],
[0x2200090040021000880202008008400200442e4,0x0,0x4200110040021000880202008008400200844e4,0x800820020040000008004200100002200080ce3,0x820021804002100088020200800840020104ce4,0x1000840020040000008004200100002200080ce3,0x10200418040021000880202008008400202054e4,0x20008800220400341a8004200100d02234080de3,0x0,0x40009000240400341a8004200100d02234080de3,0x800020040000008004200100002200080ce3,0x0,0x8000a00028008040200084002101002040081ce3,0x0,0x8000a00028008040200104004101002040081ce3,0x0,0x8000a00028001040200204008101002040081ee3,0xf3000222c00088b00012fc0000f3079803cc1e600001e60000798f301e63cc03ccf300f31e601e740995,0x8000a00028002040200404010101002040081ce3,0x0,0x8000a00028008040200804020101002040081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4203010040021000880202008010400400844e4,0xa00032040021000880202008010400400100e4,0x100804020040000008004200100002200080ce3],
[0x0,0x0,0x2200090040021000880202008010400400442e4,0x0,0x4200110040021000880202008010400400844e4,0x800820020040000008004200100002200080ce3,0x820021804002100088020200801040040104ce4,0x1000840020040000008004200100002200080ce3,0x10200418040021000880202008010400402054e4,0x2000880022040080408004200102002280082de3,0x0,0x4000900024040100808004200104002300084de3,0x800020040000008004200100002200080ce3,0x8000a00028040080408004200102002080082de3,0x0,0x80802020440010088004200100402010080ce3,0x800820020040000008004200100002010080ce3,0x100804020440010088004200100402010080ce3,0x0,0x200808028040020108004200100802010080ce3,0x0,0x400810028040020108004200100802010080ce3,0x0,0x800820020040000008004200100002010080ce3,0x804021104002100088004200102040080804ce4,0x0,0x10080412040021000880082002020400808054e4,0x2000880022040004028004200100102010080de3,0x800810028840020108004200100802010080ce3,0x4000900024040004028004200100102010080de3,0x800020040000008004200100002010080ce3,0x8000a00028040100808004200104002100084de3],
[0x0,0x80802020040000008004200100002000080ce3,0x820020040000008004200100002000080ce3,0x100804020040000008004200100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x800820020040000008004200100002000080ce3,0x804021104002100088004200104040100804ce4,0x1000840020040000008004200100002000080ce3,0x10080412040021000880082002040401008054e4,0x2000880022040080408004200102002080082de3,0x1e67981e60f301e60f30f3001e9cc007a73001f5303cc3cc0f30f303cc0f303cc3cc7980f303cc1e7556,0x4000900024040100808004200104002100084de3,0x800020040000008004200100002000080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6132 : TreeBound (n := 4) 106 (programCode 0x4829076064) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d907987983cc2d907983cc5b22d9001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5,0x8000a00024002100088000a000200c00020100e4,0xf307983cc0004bf0798f307984bf07983cc97e4bf001e9cc01e6f3001e6003ccf301e67980799e7051a5,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a042084642,0x100a041084222,0x100a042084642,0x100a041084222,0x100a0440852a2,0x0,0x100a0440852a2,0x0,0x0,0x0,0x0,0x0,0x100a040080022,0x100a041080022,0x100a040080022,0x100a041080022,0x100a040080022,0x100a04208c642,0x100a040080022,0x100a04208c642,0x100a041080022,0x100a0440a94c2],
[0x0,0x100a0440a94c2,0x0,0x0,0x0,0x0,0x0,0x100a041088442,0x100a041088442,0x100a040088442,0x100a041088442,0x100a043088642,0x100a042088442,0x100a042088442,0x100a042088442,0x100a041088442,0x100a0440894c2,0x0,0x100a0440894c2,0x0,0x0,0x0,0x0,0x0,0x100a040080022,0x100a041080022,0x100a040080022,0x100a041080022,0x100a040080022,0x100a042088442,0x100a040080022,0x100a042088442],
[0x100a041080022,0x100a0440a10a2,0x0,0x100a0440a10a2,0x0,0x0,0x0,0x0,0x0,0x100a041088442,0x100a041088442,0x100a040088442,0x100a041088442,0x100a043088642,0x100a042088442,0x100a042088442,0x100a042088442,0x100a041088442,0x100a0440894c2,0x0,0x100a0440894c2,0x0,0x0,0x0,0x0,0x0,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a041084222,0x100a042084642],
[0x100a041084222,0x100a042084642,0x100a041084222,0x100a0440852a2,0x0,0x100a0440852a2,0x0,0x0,0x0,0x0,0x0,0x8000600022001100080400412030806020180ca4,0x100a041090882,0x0,0x100a041090882,0x8000a00024002100080000800020800020100de4,0x100a042090c82,0x0,0x100a042090c82,0x100a041090882,0x100a044091902,0x0,0x100a044091902,0x0,0x0,0x0,0x0,0x0,0x0,0x80802024002100088000a000200c02000100e4,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0xa00024002100088000a000200402000000e4,0x0,0x0,0x0,0x800024002100088000a000200402000000e4,0x0,0x0,0x8000a0002400210008040081402100a0402015e4,0x100a041090882,0x0,0x100a041090882,0x8000a000240021000800008000210000402015e4,0x100a042090c82,0x0,0x100a042090c82,0x100a041090882,0x100a044091902,0x0,0x100a044091902,0x0,0x0,0x0,0x0,0x0,0x0,0x80802024002100088000a000200402000000e4],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3d39800f30f3079ff320000000007983cc1e60f3001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x0,0x0,0x800024002100088000a000200402000000e4,0x0,0x0,0x100a0410a10a2,0x100a0410a10a2,0x0,0x100a0410a10a2,0x8000a000240021000800008000220000804021e4,0x100a0420a14c2,0x0,0x100a0420a14c2,0x100a0410a10a2,0x100a0440a10a2,0x0,0x100a0440a10a2,0x0,0x0,0x0,0x0,0x0],
[0x16c8000f3079816c888b07983cc7984bf25f8f3001e9cc01e6f3001e6f3001e7e6003db3001ead3485,0x80802024002100088000a000200400000000e4,0x16c80003cc1e625f902307981e6798538a9c4f3001e9cc01e6f3001e679800f4e6003db3001eacf2b5,0x100804024002100088000a000200400000000e4,0x0,0x0,0x0,0x0,0x100804024002100088000a000200400000000e4,0x0,0x3d39801e60f3079fd4c0000000007983cc1e60f3001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x0,0x0,0x800024002100088000a000200400000000e4,0x0,0x0,0x100a0410a10a2,0x100a0410a10a2,0x0,0x100a0410a10a2,0x8000a000240021000800008000240001008041e4,0x100a0420a14c2,0x0,0x100a0420a14c2,0x100a0410a10a2,0x100a0440a10a2,0x0,0x100a0440a10a2,0x0,0x0,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6357 : TreeBound (n := 4) 106 (programCode 0x4829076065) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8001200048040002010084002108002200080ce3,0x8001200048044020108004020108002200080ce3,0x8001200048040004020104004108002200080de3,0x0,0x1002041000022,0x100a041084222,0x1002041000022,0x100a041084222,0x1002041000022,0x101a041188642,0x1002041000022,0x101a041188642,0x1002041000022,0x8004200084002100080104004100804020804ce4,0x0,0x80082000840021000801080042010080408054e4,0x0,0x0,0x0,0x0,0x1002040040022,0x1002042040442,0x1002040040022,0x1002042040442,0x1002040040022,0x1012044141902,0x0,0x0,0x800020040021000800800020080402000000e4,0x0,0x0],
[0x211084240481,0x411084240481,0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x813184240501,0x411084240481,0x813184240501,0x411084240481,0x1012044141902,0x8001200048040080402004080108002200082ee3,0x8001200048044020108004020108002200080ce3,0x8001200048040100804004100108002200084ee3,0x8001200048040000008004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6406 : TreeBound (n := 4) 106 (programCode 0x4829076066) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000222c001f5307a17e0f3088b07983cd1167980f4e600f4e6000f4e9cc001f53000408c001e707485,0x80012000440021000800810020480402000100e4,0xf300012fc001f5307a08b07984bf07983cc97e3cc0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0x1012041104222,0x1012041104222,0x1012041100222,0x1012041104222,0x101204110c642,0x1012041108642,0x1012041104222,0x1012041108642,0x1012041108642,0x1012041110a82,0x0,0x1012041110a82,0x0,0x10120411212c2,0x0,0x10120411212c2,0x1012042140442,0x1012042140442,0x1012040140022,0x1012042140442,0x1012042140442,0x1012044141902,0x0,0x0,0x810020440021000800810020480402000100e4,0x0,0x0],
[0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x1012044141902,0x8000200008040000002004080108002200080ce3,0x80012000440021000820010800480402004022e4,0x8000200008040000004004100108002200080ce3,0x80012000440021000840011000480402008042e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6455 : TreeBound (n := 4) 106 (programCode 0x4829076067) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8002200088040002010084002108002200080ce3,0x0,0x1002041000022,0x100a041084222,0x1002041000022,0x100a041084222,0x1002041000022,0x101a041188642,0x1002041000022,0x101a041188642,0x1002041000022,0x8004200804002100080084002100804020804ce4,0x8002200088000000000004020101002040080ce3,0x80082008040021000800880022010080408054e4,0x8002200088002010080404020102002080080ce3,0x0,0x8002200088002010080404020104002100080ce3,0x0,0x8002200088040004020104004108002200080de3,0x0,0x1002041000022,0x100a041084222,0x1002041000022,0x100a041084222,0x1002041000022,0x101a041188642,0x1002041000022,0x101a041188642,0x1002041000022,0x8004200804002100080104004100804020804ce4,0x0],
[0x80082008040021000801080042010080408054e4,0x0,0x0,0x0,0x0,0x1002040040022,0x1012042140442,0x1002040040022,0x1012042140442,0x1002040040022,0x0,0x0,0xa00020140021000808200208080202000100e4,0x0,0x1200040240021000808200208080202000241e4,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x8139ce240501,0x410000240481,0x8139ce240501,0x10000240481,0x0,0x0,0x0,0x0,0x0],
[0x211084240481,0x411084240481,0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x813184240501,0x411084240481,0x813184240501,0x411084240481,0x0,0x0,0xa00020140021000810200408080202000100e4,0x0,0x1200040240021000810200408080202000241e4,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x812108240501,0x410000240481,0x812108240501,0x10000240481,0x8002200088040080402004080108002200082ce3,0x0,0x82002088002010080404020108002200080ce3],
[0x0,0x102004088002010080404020108002200080ce3,0x0,0x211084240481,0x411084240481,0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x8139c6240501,0x411084240481,0x8139c6240501,0x411084240481,0x8002200088040100804004100108002200084ce3,0x0,0x0,0x0,0x0,0x0,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x812108240501,0x410000240481,0x812108240501],
[0x10000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6584 : TreeBound (n := 4) 106 (programCode 0x4829076068) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1012040100022,0x1012040104022,0x1012040100022,0x1012040104022,0x1012042108442,0x1012042108442,0x1012040100022,0x1012042108442,0x1012042108442,0x1012042110442,0x0,0x1012042110442,0x0,0x1012042120442,0x0,0x1012042120442,0x80022000840021000800820020880402000100e4,0x0,0x1012040100022,0x1012041104222,0x1012040100022,0x1012041104222,0x1012040108022,0x1012040108022,0x1012040100022,0x1012040108022,0x1012040108022,0x80022000840021000840022000808400208044e4,0x0,0x80022000840021000840022000810400408044e4],
[0x0,0x0,0x0,0x0,0x0,0x1012041104222,0x1012041104222,0x1012041100222,0x1012041104222,0x101204110c642,0x1012041108642,0x1012041104222,0x1012041108642,0x1012041108642,0x1012041110a82,0x0,0x1012041110a82,0x0,0x10120411212c2,0x0,0x10120411212c2,0x1012042140442,0x1012042140442,0x1012040140022,0x1012042140442,0x1012042140442,0x1012044141902,0x0,0x0,0x820020840021000800820020880402000100e4,0x0,0x0],
[0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x1012044141902,0x0,0x0,0x112042140442,0x0,0x112042140442,0x252948240501,0x8240481,0x252948240501,0x8240481,0x420088240481,0x8240481,0x420088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x80022000840021000820020800880402004024e4,0x0],
[0x0,0x0,0x0,0x0,0x252948240501,0x8240481,0x252948240501,0x8240481,0x420088240481,0x8240481,0x420088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x80022000840021000840021000880402008044e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6697 : TreeBound (n := 4) 106 (programCode 0x4829076069) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8004200108040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6698 : TreeBound (n := 4) 106 (programCode 0x482907606a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8004200104002100088004200108040200804ce4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6699 : TreeBound (n := 4) 106 (programCode 0x482907606b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x880022000c0002018004200100082002080ce3,0x88002200840020108004200100802020080ce3,0x88002200140004028004200100102004080de3,0x0,0x88002200240008048004200100202008080ee3,0x88002200040000008004200108002000080ce3,0x88002200440010088004200100402010080ce3,0x88002200040000008004200108002000080ce3,0x88002200840020108004200100802020080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x88002200040000008004200100002000080ce3,0x0,0x0,0x8020200040000008004200100002020080ce3,0x0,0x0,0x808020200040000008004200100202008080ce3,0x804030040021000880006000102400080402e4,0x808020200040000008004200100402010080ce3,0x804030040021000880006000104400100804e4,0x8020200040000008004200100802020080ce3,0x80403004002100088000600010840020100ce4,0x0,0x804030040021000880006000110400402014e4,0x1008020200040000008004200102002080080ce3],
[0x0,0x1008020200040000008004200104002100080ce3,0x8020200040000008004200100002000080ce3,0x0,0x1080042000c0002018004200100082002080ce3,0x108004200040000008004200100002020080ce3,0x108004200140004028004200100102004080de3,0x0,0x108004200240008048004200100202008080ee3,0x0,0x108004200440010088004200100402010080ce3,0x0,0x108004200840020108004200100802020080ce3,0x108004200040000008004200100002200080ce3,0x0,0x108004200040000008004200100002200080ce3,0x0,0x108004200440010088004200100402200080ce3,0x0,0x108004200040000008004200100002000080ce3,0x0,0x4459e607983cc25f81e6003cfcc007a73001f53079b15c0004bf00012fc1e600007980000000001dc6,0x100805004002100088000a000200c00020100e4,0x4459e607983cc25f81e6003cfcc007a73001f53079b15c0004bf00012fc1e600007980000000001dc6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x100805004002100088000a000200402000000e4,0x0,0x0,0x2080082000c0002010084002108002200080ce3,0x208008200844020108004020108002200080ce3,0x208008200140004020104004108002200080de3,0x0,0x220842240481,0x220000240481,0x220842240481,0x220000240481,0x221084240481,0x220000240481,0x221084240481,0x220000240481,0x222148240501,0x221084240481,0x222148240501,0x220000240481,0x0,0x80020000040100000801001002401000001200000004000240012000100048002000040200000100800001008000001008040000002100000010400000101000000100109413a7,0x2010080140021000800810020480402000100e4,0x40020000010080002001001002a010000006000000010000c00220001000a8005000040200000100800002008000002008040000002100000008400000101000000100108403a7,0x0,0x620842240481,0x20000240481,0x620842240481,0x20000240481,0x20004240481],
[0x20000240481,0x20004240481,0x20000240481,0x420088240481,0x20000240481,0x420088240481,0x20000240481,0x0,0x4080102000c0002010084002108002200080ce3,0x0,0x408010200140004020104004108002200080de3,0x0,0x220842240481,0x220000240481,0x220842240481,0x220000240481,0x221084240481,0x220000240481,0x221084240481,0x220000240481,0x222148240501,0x221084240481,0x222148240501,0x220000240481,0x0,0x0,0x4020100140021000800820020880402000100e4,0x0,0x0,0x220842240481,0x20000240481,0x220842240481],
[0x20000240481,0x20004240481,0x20000240481,0x20004240481,0x20000240481,0x20008240481,0x20000240481,0x20008240481,0x20000240481,0x808020200040000008004200108002200080ce3,0x804021004002100088004200108040200804ce4,0x1008040200040000008004200108002200080ce3,0x10080410040021000880082002080402008054e4,0x0,0x0,0x140021000800800020080402000000e4,0x0,0x0,0x822142240501,0x82210c240501,0x822142240501,0x822108240501,0x822104240501,0x822104240501,0x822104240501,0x822108240501,0x822108240501,0x82210c240501,0x822108240501,0x822108240501,0x0,0x0],
[0x20100800140021000800900024080402004020e4,0x0,0x0,0x620842240481,0x20000240481,0x620842240481,0x20000240481,0x20004240481,0x20000240481,0x20004240481,0x20000240481,0x20008240481,0x20000240481,0x20008240481,0x20000240481,0x0,0x0,0x0,0x0,0x0,0x822142240501,0x82210c240501,0x822142240501,0x822108240501,0x822104240501,0x822104240501,0x822104240501,0x822108240501,0x822108240501,0x82210c240501,0x822108240501,0x822108240501],
[0x8000200040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6892 : TreeBound (n := 4) 106 (programCode 0x482907606c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80082002040021000880082002080402008054e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6893 : TreeBound (n := 4) 106 (programCode 0x482907606d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x90002408040002018004200108002200080ce3,0x8010020408840020108004200108002200080ce3,0x110004408040004028004200108002200080de3,0x0,0x8010002408040002010084002108002200080ce3,0x0,0x8010004408040004020104004108002200080de3,0x0,0x102040040022,0x112042140442,0x102040040022,0x112042140442,0x102040040022,0x1200048040021000808200208080202000241e4,0x0,0x1200048040021000810200408080202000241e4,0x102040040022,0x0,0x8010100408040100804004100108002200086ce3,0x0,0x210008408040008048004200108002200080ee3,0x8010000408040000008004200108002200080ce3,0x410010408040010088004200108002200080ce3,0x8010000408040000008004200108002200080ce3,0x810020400840020108004200108002200080ce3,0x0,0x0,0x8020200840021000800820020880402000100e4,0x0,0x0,0x6418c2240481],
[0x40000240481,0x6418c2240481,0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x40008240481,0x40008240481,0x40008240481,0x40000240481,0x0,0x0,0x20040021000800800020080402000000e4,0x0,0x0,0x4410c2240481,0x441084240481,0x4410c2240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x441088240481,0x44108c240481,0x441088240481,0x441084240481,0x0,0x0,0x10020400840021000800820020880402000100e4,0x0],
[0x0,0x240842240481,0x40000240481,0x240842240481,0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x40008240481,0x40008240481,0x40008240481,0x40000240481,0x2010080402040080408004200108002200082ce3,0x2010080402040080408004200108002200082ce3,0x4010100404040100808004200108002200086ce3,0x10000400040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_6974 : TreeBound (n := 4) 106 (programCode 0x482907606e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xfa9800f31e600fb2fe0f3088b07983cd1167980f4e600f4e6000f4e9cc001f53000408c001e707485,0x0,0xfa9800f31e60176cb083cc2d907983ccd4a5b20f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0x82002148001008040204008108002200080ee3,0x82002108000000000004000108002200080ce3,0x82002188002010080404010108002200080ce3,0x82002108000000000004000108002200080ce3,0x82002108004020100804020108002200080ce3,0x80100804040021000808100204080202004020e4,0x0,0x80100804040021000810100404080202004020e4,0xfa9800f31e601c2adbe0f30f30000dc3ee1e04601e7e601e61e601e9cc001023000408c001ee9b2b5,0x82002188002010080404030108002200080ce3,0xfa9800f31e6010a41f983ccf300022a5deee22c01e67981e63cc01e9cc001f53000408c001e8e97c5,0x0,0x900024040021000880102004080402000100e4,0x0,0xf4e6003ccf30269da383cc2d907983cd4e297e0f4e600f4e6000f4e9cc001023000408c001e7032b5,0x0,0xfa9800799e601ee20b07984bf07983cc97e3cc0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0x102004148001008040204008108002200080ee3,0x102004108000000000004000108002200080ce3,0x102004188002010080404010108002200080ce3,0x102004108000000000004000108002200080ce3,0x102004108004020100804020108002200080ce3,0x0,0x0,0x0],
[0xfa9800799e6022ad3660f30f30001c7a6a55d0601e7e601e61e601e9cc0010230007d4c001ee9b345,0x102004188002010080404030108002200080ce3,0xfa9800799e6020c72730798f300013ef9f7bea601e6f301e63cc01e9cc0010230007d4c001eacf345,0x0,0x0,0x40002000000010200400000040000582124000200000004000240002000100048002000040200000100800001008000001008040000010100000010400000101000000100109713a7,0x0,0x0,0x0,0x142048440222,0x1420424406c2,0x0,0x1420424406c2,0x142048440222,0x1420444412a2,0x0,0x1420444412a2,0x3db3000f6cc001f531e6003d39800f3f3001f5300f30007d4c1e60f33cc1e60f300012fc0003cc38f6,0x142048440222,0x0,0x142048440222,0x204008008040000008004200108002200080ce3,0x2100084040021000880102004080402000422e4,0x404010008040000008004200108002200080ce3,0x4100104040021000880102004080402000824e4,0x800020000040000008004200108002200080ce3,0x810020404002100088010200408040200102ce4,0x0,0x0,0x100024040021000800900024080402000100e4,0x0,0x0],
[0x430842240481,0x400000240481,0x430842240481,0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x420088240481,0x400000240481,0x420088240481,0x400000240481,0x10100404040021000880102004080402002034e4,0x2000080002040000008004200108002200080ce3,0x40000008004200108002200080ce3,0x4000100004040000008004200108002200080ce3,0x40000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_7055 : TreeBound (n := 4) 106 (programCode 0x482907606f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xa0002808040002018004200108002200080ce3,0x0,0x420020808440010088004200100082002080ce3,0x20020800040000008004200100002020080ce3,0x420020808440010088004200100102004080ce3,0x0,0x820020800840020108004200100202008080ce3,0x0,0x820020800840020108004200100402010080ce3,0x0,0x20020800040000008004200100802020080ce3,0x84002914002100088004200100840020804ce4,0x0,0x88002a140021000880082002010400408054e4,0x4020020804040100808004200102002080084ce3,0x4020020804040100808004200104002100084ce3,0x4020020804040100808004200104002100084ce3,0x20020800040000008004200100002000080ce3,0x120004808040004028004200108002200080de3,0x0,0xa02008080c0002018004200100082002080ce3,0x20200808040000008004200100002020080ce3,0x120200808140004028004200100102004080de3,0x0,0x0,0x0,0x0,0x0,0x20200808040000008004200100802020080ce3,0x104004924002100088004200100840020804ce4,0x0],
[0x108004a240021000880082002010400408054e4,0x0,0x0,0x20200808040000008004200104002100080ce3,0x0,0x220008808040008048004200108002200080ee3,0x0,0x4200108000c0010080084002108002200080ce3,0x0,0x420010800140010080104004108002200080ce3,0x0,0x6418c2240481,0x40000240481,0x6418c2240481,0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x420010808040010088004200108002200080ce3,0x0,0x0,0x0,0x0,0x0,0x240842240481,0x40000240481,0x240842240481],
[0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x40008240481,0x40008240481,0x40008240481,0x40000240481,0x820020800840020108004200108002200080ce3,0x820020904002100088020200808040200104ce4,0x0,0x0,0x0,0x0,0x0,0x4410c2240481,0x441084240481,0x4410c2240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x441084240481,0x441088240481,0x44108c240481,0x441088240481,0x441084240481,0x1020040a040021000880202008080402002054e4,0x2020080802040080408004200108002200086ce3,0x4020100804040100808004200108002200084ce3,0x4020100804040100808004200108002200084ce3],
[0x20000800040000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_7152 : TreeBound (n := 4) 106 (programCode 0x4829076070) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x804020100c0002018004200100082002080ce3,0x84002000840000008004200100002020080ce3,0x80802020140004028004200100102004080de3,0x0,0x0,0x80002000040000008004200108002000080ce3,0x0,0x80002000040000008004200108002000080ce3,0x84002000840000008004200100802020080ce3,0x4203008040021000880202008008400200844e4,0x0,0x4203008040021000880202008010400400844e4,0x90002412040082418004200102002080082ce3,0x80002000040000008004200100402000080ce3,0xa0002814040102818004200104002100084ce3,0x80002000040000008004200100002000080ce3,0xa00028040021000880202008080402000100e4,0x0,0x1004040100c0002018004200100082002080ce3,0x100004000040000008004200100002020080ce3,0x100804020140004028004200100102004080de3,0x0,0x0,0x0,0x0,0x0,0x104004000840000008004200100802020080ce3,0x100004000040000008004200100002200080ce3,0x0,0x100004000040000008004200100002200080ce3],
[0x110004422040084428004200102002080082de3,0x0,0x120004824040104828004200104002100084de3,0x100004000040000008004200100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x142048440222,0x1420424406c2,0x0,0x1420424406c2,0x142048440222,0x1420444412a2,0x0,0x1420444412a2,0x0,0x142048440222,0x0,0x142048440222,0x0,0x0,0x204008000840000008004020108002200080ce3,0x0,0x0,0x210842240481,0x200000240481,0x210842240481,0x200000240481,0x221084240481,0x200000240481],
[0x221084240481,0x200000240481,0x252948240501,0x221084240481,0x252948240501,0x200000240481,0x2200088040021000880202008080402000442e4,0x0,0x0,0x0,0x0,0x0,0x210842240481,0x200000240481,0x210842240481,0x200000240481,0x221084240481,0x200000240481,0x221084240481,0x200000240481,0x252948240501,0x221084240481,0x252948240501,0x200000240481,0x4200108040021000880202008080402000844e4,0x800020000040000008004200108002200080ce3,0x820020804002100088020200808040200104ce4,0x1000040000040000008004200108002200080ce3,0x10200408040021000880202008080402002054e4,0x2010080402040080408004200108002200082ce3,0x40000008004200108002200080ce3,0x4020100804040100808004200108002200084ce3],
[0x40000008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_5824 : TreeBound (n := 4) 106 (programCode 0x48290760) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part011_5825 part011_5906 part011_5987 part011_6132 part011_6357 part011_6406 part011_6455 part011_6584 part011_6697 part011_6698 part011_6699 part011_6892 part011_6893 part011_6974 part011_7055 part011_7152

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part011_0 : TreeBound (n := 4) 106 (programCode 0x482907) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part011_1 part011_2 part011_3 part011_4 part011_1029 part011_1030 part011_1031 part011_1032 part011_1033 part011_1034 part011_1723 part011_2636 part011_3453 part011_4014 part011_4783 part011_5824

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned011 : TreeBound (n := 4) 106 [((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨1,1,true⟩)] := part011_0
open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem zero_one_return_one_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 1, Stmt.write 1 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 106 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,0,false⟩),((2,0), ⟨1,1,true⟩)] := by
    intro k m h
    simp only [Program.get] at h
    split at h
    next hk =>
      subst k
      cases Option.some.inj h
      simp [ongoing,h0]
    next =>
      split at h
      next hk =>
        subst k
        cases Option.some.inj h
        simp [ongoing,h1]
      next =>
        split at h
        next hk =>
          subst k
          cases Option.some.inj h
          simp [ongoing,h2]
        next => contradiction
  rcases partitioned011 M hm with h | h
  · exact h
  · exact (h halts).elim

end BeaverBound



/- Exact residual adapter: Hanan Beer (@hananzlt).
Residual specification and freeze reduction: @pageman, PR6963, adapting
@henry10101001. All existing verifier and certificate attribution above is retained.
This proves only the named auxiliary return-state branch. -/
open Turing Turing.BusyBeaver
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1.H2 := by
  intro M h0 h1 h2 hRun _hUsed _hForm _hMissing _hLoop hHalts
  have stopped := BeaverBound.zero_one_return_one_machine M h0 h1 h2 hHalts
  change M.multiStep (Machine.init []) 107 = none at stopped
  obtain ⟨q,t,live⟩ := hRun
  rw [live] at stopped
  contradiction
