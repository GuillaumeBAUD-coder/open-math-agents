/- Standalone proof component for the one/zero-write Busy Beaver family.
This proves only return states 1, 2. -/
import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1

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
107 steps. The new bit-mask tests imply the original verifier checks. Nonhalting leaves use finite-automata reduction: a DFA summarizes
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
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkGenerated special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkChoice tb (v-17) then some rest else none

theorem generated_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 107 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkGenerated special fuel tb a = some b) :
    TreeBound 107 tb := by
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
        cases hFirst : firstMissing tb 107 (start 4) with
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
      match firstMissing tb 107 (start 4) with
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
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkPrepared special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkCertificateBits tb (v-17) then some rest else none

theorem prepared_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 107 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkPrepared special fuel tb a = some b) :
    TreeBound 107 tb := by
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
        cases hFirst : firstMissing tb 107 (start 4) with
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
    (h : firstMissing tb 107 (start 4) = some k)
    (p0 : TreeBound (n := 4) 107 ((k,⟨0,0,false⟩)::tb))
    (p1 : TreeBound (n := 4) 107 ((k,⟨0,0,true⟩)::tb))
    (p2 : TreeBound (n := 4) 107 ((k,⟨0,1,false⟩)::tb))
    (p3 : TreeBound (n := 4) 107 ((k,⟨0,1,true⟩)::tb))
    (p4 : TreeBound (n := 4) 107 ((k,⟨1,0,false⟩)::tb))
    (p5 : TreeBound (n := 4) 107 ((k,⟨1,0,true⟩)::tb))
    (p6 : TreeBound (n := 4) 107 ((k,⟨1,1,false⟩)::tb))
    (p7 : TreeBound (n := 4) 107 ((k,⟨1,1,true⟩)::tb))
    (p8 : TreeBound (n := 4) 107 ((k,⟨2,0,false⟩)::tb))
    (p9 : TreeBound (n := 4) 107 ((k,⟨2,0,true⟩)::tb))
    (p10 : TreeBound (n := 4) 107 ((k,⟨2,1,false⟩)::tb))
    (p11 : TreeBound (n := 4) 107 ((k,⟨2,1,true⟩)::tb))
    (p12 : TreeBound (n := 4) 107 ((k,⟨3,0,false⟩)::tb))
    (p13 : TreeBound (n := 4) 107 ((k,⟨3,0,true⟩)::tb))
    (p14 : TreeBound (n := 4) 107 ((k,⟨3,1,false⟩)::tb))
    (p15 : TreeBound (n := 4) 107 ((k,⟨3,1,true⟩)::tb))
    : TreeBound (n := 4) 107 tb := by
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
private theorem part101_1 : TreeBound (n := 4) 107 (programCode 0x462b0731) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084041240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3 : TreeBound (n := 4) 107 (programCode 0x462b073211) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084086204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4 : TreeBound (n := 4) 107 (programCode 0x462b073212) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084004210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5 : TreeBound (n := 4) 107 (programCode 0x462b073213) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084086204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6 : TreeBound (n := 4) 107 (programCode 0x462b073214) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010080002000000080402000020000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_7 : TreeBound (n := 4) 107 (programCode 0x462b073215) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084004208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_8 : TreeBound (n := 4) 107 (programCode 0x462b073216) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084004200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_9 : TreeBound (n := 4) 107 (programCode 0x462b073217) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084004208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_10 : TreeBound (n := 4) 107 (programCode 0x462b073218) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x108048621c481,0x1081004210481,0x108048621c481,0x1081004210481,0x1080804208481,0x1080004200481,0x1080804208481,0x1080004200481,0x1081004210481,0x1080004200481,0x1081004210481,0x1080004200481,0x0,0x100a045220481,0x1022004220481,0x100a045220481,0x80402000020000800000080402020020800814e3,0x1012086238481,0x1002004220481,0x1012086238481,0xf3000f6cc003db30007d548b3db3000f300000f304469160f300000f3079fb6a459e607983cc1e611156,0x1022004220481,0x1002004220481,0x1022004220481,0x80402000020000800000080402020020800814e3,0xf307983cc1e60f300003cc003db3000f300000f304459e60f300000f3079fb69cc1e607983cc1e611156,0x0,0xf307983cc1e60f300003cc003db3000f300000f304459e60f300000f3079fb69cc1e607983cc1e611156,0x0,0x0,0x182041088442],
[0x182041088442,0x182041088442,0x182041088442,0x382041188642,0x282041188642,0x382041188642,0x282041188642,0x8400210000002000000080402000020000814e3,0x3d39803cde6003d398079800fa9800f379800f300f30798f379800f3079bcfcc00f307983cc1e654dd6,0x182041088442,0x79f9801e7e60079f98079800fa9800f379800f300f30798f3f3000f3079bdb3000f307983cc1e6a8656,0x0,0x0,0x0,0x0,0x0,0x100a045220481,0x1022004220481,0x100a045220481,0x0,0x1012086238481,0x1002004220481,0x1012086238481,0xf300003cc0f30f303cc1e600007980000f3000000007980001e60f303cc00003d39800f4e6001e703d95,0x1022004220481,0x1002004220481,0x1022004220481,0x0,0xf307983cc1e60f300003cc003db3000f300000f304459e60f300000f3079fb69cc1e607983cc1e611156,0x0,0xf307983cc1e60f300003cc003db3000f300000f304459e60f300000f3079fb69cc1e607983cc1e611156,0x0],
[0x0,0x182041088442,0x182041088442,0x182041088442,0x182041088442,0x382041188642,0x282041188642,0x382041188642,0x282041188642,0x0,0x3d39803cde6003d3980f3000f6cc00f3f3000f300f30798f4e6000f3079bd39800f307983cc1e70b1d6,0x182041088442,0x79f9801e7e60079f980f3000f6cc00f3f3000f300f30798f3f3000f3079bd39800f307983cc1e6a8656,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_91 : TreeBound (n := 4) 107 (programCode 0x462b073219) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084004210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_92 : TreeBound (n := 4) 107 (programCode 0x462b07321a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x804020100800220004014080201104c020100b04]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_93 : TreeBound (n := 4) 107 (programCode 0x462b07321b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084004210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_94 : TreeBound (n := 4) 107 (programCode 0x462b07321c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc001023000f6cc000f300f307991160000f307b67e6007983cc1e60f3099356]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_95 : TreeBound (n := 4) 107 (programCode 0x462b07321d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x100c045220481,0x1024004220481,0x100c045220481,0x80402000080002000000080402020020800814e3,0x1014086220481,0x1004004220481,0x1014086220481,0x0,0x80106000100820020800880402020020800814e3,0x1021004220481,0x8010a000201020040801080402020020800814e3,0x0,0x1030886220481,0x1000004220481,0x1030886220481,0x1000004220481,0x1021004220481,0x1000004220481,0x1021004220481,0x1000004220481,0x80502004020100804020080402020020800834e3,0x0,0x0,0x0,0x1024004220481,0x80402000080002000000080402020020800814e3,0x1024004220481,0x80402000080002000000080402020020800814e3,0x104410c220501,0x802020040800220004014080201c070080402104,0x104410c220501],
[0x802020080800220004014080201c060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_128 : TreeBound (n := 4) 107 (programCode 0x462b07321e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8040200008002200040140802014070080402104,0x8000a00018002200040140802014070080402104,0x0,0x10c004208481,0x40c004208481,0x10c004208481,0x40c004208481,0x20c004218481,0xc004208481,0x20c004218481,0x0,0x40c004208481,0x104c020108002200040140802014070080402b04,0x40c004208481,0x80200000200010000800040002000100400000021000000404000000810000000800004000200080004000120000000100008400020008000800010001200010000800049251da8,0x80c08620c481,0x60c004218481,0x80c08620c481,0x8000280002000010080402000020100814e3,0xf300012fc0004bf00012fc001023000f6cc000f300f307991160000f308119e607980f307983cc1e93b6,0x8070200408002200040140802014070080402104,0x8002200048002200040140802014070080402304,0x8070200408002200040140802014070080402104,0x0,0x10108410a10c2,0xf30007d4c001f5300079803ccf303ccf3003ccf300f30798f6cc000f308119e607980f307983cc1f6856,0x0,0xf30007d4c001f530007980798f301e6f300798f300f307990230000f308119e607980f307983cc98e856,0x0,0x10108410a10c2,0x0],
[0x10108410a10c2,0xf3000f6cc003db30007fb7d73cde600f3003ccf304825e60f6cc000f3097e2d907980f307983cc1f7156,0x10110412a1902,0xf3000f6cc003db30007f32f33cde600f3003ccf304825e60f6cc000f3097e2d907980f307983cc1f7156,0x10110412a1902,0xf3000f6cc003db30007f32f33db3000f300000f304825e60f300000f3097e2d907980f307983cc1f7156,0x0,0x4000000010000a000400008001000040001000000004000a000200000000200000004000008014400020000000100008000100400000081400000204000001000000001002086aba7,0x0,0x8040a00018002200040140802014070080402104,0x8008200108002200040140802014070080402b04,0x8040a00018002200040140802014070080402104,0xf3003cfcc00f3f3003cfcc001023000f6cc000f300f307991160000f308119e607980f307983cc27f356,0x8040200008002200040140802014070080402104,0x8020200408002200040140802014070080402104,0x8040200008002200040140802014070080402104,0x8020200808002200040140802014070080406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_177 : TreeBound (n := 4) 107 (programCode 0x462b07321f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x100c045220481,0x1024004220481,0x100c045220481,0x0,0x12c045220481,0x424004220481,0x12c045220481,0x424004220481,0x234086220481,0x24004220481,0x234086220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0x86418c220501,0x24004220481,0x86418c220501,0x80002000000080402040021000814e3,0x1014086220481,0x1004004220481,0x1014086220481,0x0,0x40002000100001000400000003000000008000600020001001000006004200018010c00001000200004000000408000c0001002000001008000004010000008020000010010873227,0x1021004220481,0x0,0x0,0x1030886220481,0x1000004220481,0x1030886220481],
[0x1000004220481,0x1021004220481,0x1000004220481,0x1021004220481,0x1000004220481,0x40002000100008000400002001000008000400200001000080004002200010008800400001001000004000400008000c0001002000001008000004010000008020000010050873227,0x0,0x0,0x0,0x1024004220481,0x0,0x1030486220481,0x1001004220481,0x1030486220481,0xf3001e9cc01e6f3001e600798f301e6f300798f300f307991160000f3079897e0f30000f307983cc33b6,0x1020804220481,0x1000004220481,0x1020804220481,0x1000004220481,0x1001004220481,0x1000004220481,0x1001004220481,0x1000004220481,0x1002004220481,0x800820010400208004014080201c070080402b04,0x1002004220481,0xf3001e9cc01e6f3001e6f3000f6cc00f3f3000f300f307991160000f3088b1e60f301e60f307984c7ed6,0x1024004220481,0x0,0x80202010000a00028040080402040021000854e3,0x1021004220481,0x80202010001200048040080402040021000854e3],
[0xf3003cfcc00f3f3003cc00798f301e6f300798f300f307991160000f3079897e0f30000f307983cc33b6,0x1020804220481,0x1000004220481,0x1020804220481,0x1000004220481,0x1021004220481,0x1000004220481,0x1021004220481,0x1000004220481,0x0,0xf3003cfcc00f3f3003cc79800fa9800f379800f300f307991160000f3097e1e60f303cc1e60f30831356,0x0,0xf3003cfcc00f3f3003ccf3000f6cc00f3f3000f300f307991160000f3088b1e60f301e60f30798465356,0x104410c220501,0x0,0x134086220481,0x404004220481,0x134086220481,0x404004220481,0x224004220481,0x4004220481,0x224004220481,0x0,0x404004220481,0x102002040800220004014080201904c020100b04,0x404004220481,0x798f301e6f300798f33cc001023000f6cc000f300f307991160000f307b67e60f3003cc1e60f3099356,0x804004220481,0x4004220481,0x804004220481,0x4004220481,0x104410c220501],
[0x0,0x14c16d220501,0x0,0x14c16d220501,0x80002000000080402040021000814e3,0x2080090080002000010080402040021000814e3,0x4004220481,0x4000100080002000000080402040021000814e3,0x0,0x0,0x3cde603cc79803cde63cc001023000f6cc000f300f307991160000f307d4de60f3007983cc1e60fbed6,0x0,0x799e601e67980799e63cc001023000f6cc000f300f307991160000f307b67e60f3003cc1e60f3099356,0x84410c220501,0x4004220481,0x84410c220501,0x4004220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_290 : TreeBound (n := 4) 107 (programCode 0x462b073220) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf300003cc0000f307983cc001023000f6cc000f300f307991160000f3088b1e603cc1e60f307983cd556,0x0,0x0,0x0,0x0,0x0,0x0,0x10088410a10a2,0x0,0x10088410a10a2,0x0,0x10090412a1902,0x0,0x10090412a1902,0x0,0x0,0x0,0x0,0x0,0x10c004200481,0x0,0x10c004200481,0x8000280002000000080402000020000814e3,0x20c004210481,0xc004200481,0x20c004210481,0x0,0x0,0x3cc7983cc1e603d411bcc001023000f6cc000f300f307991160000f3088b1e603cc1e60f307984c7ed6,0x0,0x7983cc1e60f3079fd4fcc001023000f6cc000f300f307991160000f3088b1e603cc1e60f30798465356],
[0x80c045220481,0x1e63cc1e60f301e6b643cc001023000f6cc000f300f307991160000f3088b1e603cc1e60f30798b65556,0x80c045220481,0xc004200481,0xf3000222c00088b00012fc001f530007d4c000f3025f800097e3cc0f3097e0f30798d4a0f30798b69936,0xf30b643cc0798f301e63cc003db3000f6cc000f304459e611160000f3097e2d907981e60f307983cde56,0xf3000408c003db3000408c001023000f6cc000f300f307991160000f3088b1e603cc1e60f307983ebb56,0xf307983cc0798f301e63cc001023000f6cc000f300f307991160000f3088b1e603cc1e60f307983cd556,0x0,0x10108410a10c2,0xf3000f6cc003db30007980799e601e679803ccf30222c000811bcc0f3097e0f30798d4a0f30798b84276,0x0,0xf30007d4c003db30007980799e603cc7980798f30204600088b3cc0f3088b0f30798d4a0f307983ebd66,0x0,0x10108410a10c2,0x0,0x10108410a10c2,0x0,0x10110412a1902,0x0,0x10110412a1902,0x0,0x0,0x0,0x0,0x0,0x80002000100010000400800020140201008040e4,0xf30b6622c0798f30000798f33cc03ccf3003ccf30408de60fa98000f3097e2d907981e60f307983cde56,0x0,0xf30000b640798f30000798798f301e6f300798f300f30798fa98000f3088b1e603cc1e60f307983cd556,0xf3079a22c0000f30000d4a003cfcc00f3f3000f304459e611160000f3097e2d907981e60f307983cde56,0x10088410a10a2],
[0xf3079a22c0000f30000d4a003cfcc00f3f3000f304459e611160000f3097e2d907981e60f307983cde56,0x10088410a10a2,0xf30000b640798f300007983ccf6cc00f3003ccf300f3079918f8000f3088b1e603cc1e60f307983cd556,0x10390412a1902,0xf30d4c22c0798f30000d4af33cfcc00f3003ccf304825e60fa98000f3097e2d907981e60f307983cde56,0x10390412a1902,0xf3079a22c0000f30000d4a003db3000f3f3000f304459e611160000f3097e2d907981e60f307983cde56,0xf30000b640002d90000811800fa9800f379800f300f307991160000f3088b1e603cc1e60f307983cd556,0xf3079a22c0000f30000d4a003db3000f3f3000f304459e611160000f3097e2d907981e60f307983cde56,0xf30000b640000f3000088b000f6cc00f3f3000f300f307991160000f3088b1e603cc1e60f307983cd556,0xf3001e9cc01e6f3001e9cc001023000f6cc000f300f307991160000f3088b1e603cc1e60f307984c7ed6,0x0,0x80002000100010000400800020140201008040e4,0xf30000b640798f300007983ccf303ccf3003ccf300f30798fa98000f3088b1e603cc1e60f307983cd556,0x0,0xf30000b640798f30000798798f301e6f300798f300f30798fa98000f3088b1e603cc1e60f307983cd556,0x0,0x10088410a10a2,0x0,0x10088410a10a2,0xf30b6622c0798f30000e3df33cfcc00f3003ccf304825e60fa98000f3097e2d907981e60f307983cde56,0x10290412a1902,0xf30b6622c0798f30000d4af33cfcc00f3003ccf304825e60fa98000f3097e2d907981e60f307983cde56,0x10290412a1902,0x0,0x0,0x0,0x0,0xf3003cfcc00f3f3003cfcc001023000f6cc000f300f307991160000f3088b1e603cc1e60f30798465356,0x0,0x144086204481,0x4a0a0008118000f303cc003db30007d4c000f304459e6097e3cc0f3097e2d90798d4a0f307983cde26],
[0x144086204481,0x100004080002000000080402000020000814e3,0x244004218481,0x44004200481,0x244004218481,0x0,0xf34a0a3cc8118000f303cc003db30007d4c000f304459e6097e3cc0f3097e2d90798d4a0f307983cde26,0xf3d67e8667a919cc003cc003db30007d4c000f304459e6097e3cc0f3097e2d90798d4a0f307983d57a6,0xf34a0a3cc8118000f303cc003db30007d4c000f304459e6097e3cc0f3097e2d90798d4a0f307983cde26,0x798007b6603cc799f5e64001023000f6cc000f300f307991160000f3088b1e603cc1e60f307983ebb56,0x84410c220501,0x84410c220501,0x84410c220501,0x44004200481,0x8020200408002200040140802014060100804104,0x0,0x144086204481,0xf31e60fa9800111822c001023000f6cc000f300f307991160000f3088b1e603cc1e60f307983cd556,0x144086204481,0x200008080002000000080402000020000814e3,0x244004218481,0x44004200481,0x244004218481,0x0,0xf3482622c0798000f303cc003db3000f6cc000f304459e611160000f3097e2d907981e60f307983cde56,0x0,0xf3482622c0798000f303cc003db3000f6cc000f304459e611160000f3097e2d907981e60f307983cde56,0x0,0x84410c220501,0x84410c220501,0x84410c220501,0x44004200481],
[0x8020200808002200040140802014060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2 : TreeBound (n := 4) 107 (programCode 0x462b0732) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part101_3 part101_4 part101_5 part101_6 part101_7 part101_8 part101_9 part101_10 part101_91 part101_92 part101_93 part101_94 part101_95 part101_128 part101_177 part101_290

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_419 : TreeBound (n := 4) 107 (programCode 0x462b0733) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084041240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_421 : TreeBound (n := 4) 107 (programCode 0x462b073411) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084041204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_422 : TreeBound (n := 4) 107 (programCode 0x462b073412) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441218481,0x1081004210481,0x1080441218481,0x1080000210481,0x1080882210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1081004210481,0x1080000210481,0x1081004210481,0x1080000210481,0x0,0x100a0ef21c481,0x1022088210481,0x100a0ef21c481,0x4000000010000000040001000100004000040000000800000000400000001000000000000040000000200200000800800001000100000400000002000000008004000010010852e27,0x1012048218481,0x1002008210481,0x1012048218481,0x400020001000080004000200010000080004002000010000800040022000100088004000010010000040004000080110000100440000101100000404400000800c000010050873227,0x1022088210481,0x1002008210481,0x1022088210481,0x80402000020000800020080802000020400814e3,0x400002001000008004000020010000080004002000010000800040022000100088004000010010000040004000080110000100440000101100000404400000800c000010050873227,0x0,0x400010001000040004000080010000100004002000010001000040024000100090004000010010000040004000080110000100600000101400000404800000800c000010390873227,0x0,0x0,0x182041084222],
[0x182041084222,0x182041084222,0x182041084222,0x182041084222,0x282041184222,0x182041084222,0x282041184222,0x8400210000002000000080002000020400814e3,0x0,0x182041084222,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0ef21c481,0x1022088210481,0x100a0ef21c481,0xf300003cc0f30f303cc1e600007980000f300000000799e601e679803cc00003cc0000f33cc01e703d95,0x1012048218481,0x1002008210481,0x1012048218481,0x400000001000080004000200010000600020000000080000000100000000200000000000010000000040020000080080000100000000100000000400000000800c000010010873227,0x1022088210481,0x1002008210481,0x1022088210481,0x0,0x400002001000008004000020010000080020002000080000800100022000200088004000010010000040020000080180000100440000101100000404400000800c000010050873227,0x0,0x4000100010000400040000800100001000200020000800040001000300002000c0004000010010000040020000080180000100600000101800000406000000800c000010210873227,0x0],
[0x0,0x182041084222,0x182041084222,0x182041084222,0x182041084222,0x182041084222,0x282041184222,0x182041084222,0x282041184222,0x0,0x0,0x182041084222,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_503 : TreeBound (n := 4) 107 (programCode 0x462b073413) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084041204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_504 : TreeBound (n := 4) 107 (programCode 0x462b073414) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_505 : TreeBound (n := 4) 107 (programCode 0x462b073415) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_506 : TreeBound (n := 4) 107 (programCode 0x462b073416) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_507 : TreeBound (n := 4) 107 (programCode 0x462b073417) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_508 : TreeBound (n := 4) 107 (programCode 0x462b073418) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441204481,0x1081004210481,0x1080441204481,0x1080000200481,0x1080800208481,0x1080000200481,0x1080800208481,0x1080000200481,0x1081004210481,0x1080000200481,0x1081004210481,0x1080000200481,0x0,0x182041220481,0x80400410020000800010080402020020800814e3,0x182041220481,0x82000220481,0x282082228481,0x82000220481,0x282082228481,0x0,0x482004220481,0x80400010020000800000080002000020800814e3,0x482004220481,0x82000220481,0x0,0x0,0x0,0x0,0x0,0x182041088442],
[0x182041088442,0x182041088442,0x182041088442,0x382041188642,0x282041188642,0x382041188642,0x282041188642,0x8400210000002000000080002000020000814e3,0xf307983cc1e600007983cc1e600000003cc0000f30079800007980003cfcc003cc00003cc0001e64dc35,0x182041088442,0xf307983cc1e600007983cc1e600000003cc0000f30079800007980003cfcc003cc00003cc0001e64dc35,0x0,0x0,0x0,0x0,0x0,0x182041220481,0x7983cc1e600f37981e600007980000f3000000007980001e600003cc00003cc0000f4e6001e703d95,0x182041220481,0x82000220481,0x282082228481,0x82000220481,0x282082228481,0x401010040001000000080002000021000814e3,0x482004220481,0x0,0x482004220481,0x82000220481,0x0,0x0,0x0,0x0],
[0x0,0x182041088442,0x182041088442,0x182041088442,0x182041088442,0x382041188642,0x282041188642,0x382041188642,0x282041188642,0x0,0xf307983cc1e600007983cc1e600000003cc0000f30079800007980003cfcc003cc00003cc0001e64dc35,0x182041088442,0xf307983cc1e600007983cc1e600000003cc0000f30079800007980003cfcc003cc00003cc0001e64dc35,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_589 : TreeBound (n := 4) 107 (programCode 0x462b073419) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441210481,0x1081004210481,0x1080441210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1081004210481,0x1080000210481,0x1081004210481,0x1080000210481,0x0,0x100a028210481,0x1022088210481,0x100a028210481,0x1042108210501,0x1012048210481,0x1002008210481,0x1012048210481,0x80402004020100804020080802008020200834e3,0x1022088210481,0x1002008210481,0x1022088210481,0x80402000020000800020080802008020200814e3,0x1042108210501,0xf303cc3cc0f30f300f35b2003db3000f379800f304459e611160001e614e32097b660f30007d4c1e7e56,0x1042108210501,0xf303cc3cc0f30f301e65b2003db3000f4e6000f304459e611160001e614e320981183cc00088b0799e56,0x0,0x80006000180080102004080102008020200814e3],
[0x80002002080000000000080002008020200814e3,0x8000a000280080102004080102008020200814e3,0x80002000080000000000080002008020200814e3,0x80012000480000400010080402008020200814e3,0x80002000080000000000080002008020200814e3,0x80022000880000400010080402008020200814e3,0x0,0x80042001080000000000080002008020200814e3,0xf3001e9cc01e6f3001e679800fa9800f379800f301e60f3097e0001e60f3097e003cc1e60079f9847936,0x80082002080000000000080002008020200814e3,0xf3003cfcc00f3f3003cc79800fa9800f379800f301e60f3097e0001e60f3097e007983cc007a7309b1b6,0x80102004080100804020080802008020200834e3,0xf300f33cc0f30f300f3079800fa9800f379800f301e60f3097e0001e60f3097e01e60f30007d4c1e7556,0x80202008080201008040081002008020200854e3,0xf301e63cc0798f301e6079800fa9800f379800f301e60f3097e0001e60f3097e03cc1e600081183cd556,0x0,0x100a028210481,0x1022088210481,0x100a028210481,0x1042108210501,0x1012048210481,0x1002008210481,0x1012048210481,0x0,0x1022088210481,0x1002008210481,0x1022088210481,0x0,0x1042108210501,0x0,0x1042108210501,0x0],
[0x0,0x80006000180000200008080202008020200814e3,0x0,0x8000a000280000200008080202008020200814e3,0x80002000080000000000080002008020200814e3,0x80012000480000000000080002008020200814e3,0x80002000080000000000080002008020200814e3,0x80022000880000000000080002008020200814e3,0x0,0x80042001080000000000080002008020200814e3,0xf3001e9cc01e6f3001e6f3000f6cc00f3f3000f301e60f3097e0001e60f3097e00f30798007b660fdd36,0x0,0xf3003cfcc00f3f3003ccf3000f6cc00f3f3000f301e60f3097e0001e60f3097e007983cc007a7309b1b6,0x0,0xf300f33cc0f30f300f30f3000f6cc00f3f3000f301e60f3097e0001e60f3097e07983cc00088b097f556,0x0,0xf301e63cc0798f301e60f3000f6cc00f3f3000f301e60f3097e0001e60f3097e03cc1e600081183cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_670 : TreeBound (n := 4) 107 (programCode 0x462b07341a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc001023000f6cc000f301e60f3097e0001e60f3f4e600f307980f31e60fdd36]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_671 : TreeBound (n := 4) 107 (programCode 0x462b07341b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441210481,0x1081004210481,0x1080441210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1081004210481,0x1080000210481,0x1081004210481,0x1080000210481,0x0,0x100a028210481,0x1022088210481,0x100a028210481,0x1042108210501,0x1012048210481,0x1002008210481,0x1012048210481,0x80402004020100804020080802010020400834e3,0x1022088210481,0x1002008210481,0x1022088210481,0x80402000020000800020080802010020400814e3,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x182041084222],
[0x182041084222,0x182041084222,0x182041084222,0x182041084222,0x28204118c642,0x182041084222,0x28204118c642,0x8400210000002000000080002010020400814e3,0x3d39803cde6003d398079800fa9800f379800f301e60f3079f9801e60f307d4c03cc1e60079f9847936,0x182041084222,0x79f9803cde60079f980f3001e9cc0079f9800f301ed9800f5e0981e60f6cc1e617075e2607c60b00f26,0x0,0x0,0x0,0x0,0x0,0x100a028210481,0x1022088210481,0x100a028210481,0x1042108210501,0x1012048210481,0x1002008210481,0x1012048210481,0x0,0x1022088210481,0x1002008210481,0x1022088210481,0x0,0x1042108210501,0x0,0x1042108210501,0x0],
[0x0,0x182041084222,0x182041084222,0x182041084222,0x182041084222,0x182041084222,0x28204118c642,0x182041084222,0x28204118c642,0x0,0x79f9801e7e6003d3980f3001ed98007a73000f301e9cc00f3fa981e60f4e60f307d8caa607a7aa0df26,0x182041084222,0x79f9803cde60079f980f3001ed98007a73000f301e9cc00f4ed981e60f4e60f30f732a2607b6db00f26,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_752 : TreeBound (n := 4) 107 (programCode 0x462b07341c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc001023000f6cc000f301e60f3097e0001e60f4e7e6007983cc1e60f309b1b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_753 : TreeBound (n := 4) 107 (programCode 0x462b07341d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x184041220481,0x80400410080002000010080402020020800814e3,0x184041220481,0x84000220481,0x284082220481,0x84000220481,0x284082220481,0x0,0x20400030000820020800880022020020800814e3,0x0,0x20400050001020040801080042020020800814e3,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x400010000002000000080002020020800814e3,0x0,0x400010000002000000080002020020800814e3,0x484004220481,0x80400010080002000000080002020020800814e3,0x484004220481,0x80400010080002000000080002020020800814e3,0x0,0x80c028220481,0x824088220481],
[0x80c028220481,0x844108220501,0x814048220481,0x804008220481,0x814048220481,0x0,0x824088220481,0x20400800080002000020080802020020800814e3,0x824088220481,0x20400800080002000020080802020020800814e3,0x844108220501,0x804008220481,0x844108220501,0x844108220501,0x0,0x60c086220481,0x24000220481,0x60c086220481,0x4000220481,0x414004220481,0x4000220481,0x414004220481,0x0,0x24000220481,0x1e601e7e601e61e601e9cc001023000f6cc000f301e60f3097e0001e60f32046003cc1e601e679847936,0x24000220481,0x1e603cde600f31e603cfcc001023000f6cc000f301e60f3097e0001e60f37b66007983cc0798f309b1b6,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x0],
[0x80c028220481,0x824088220481,0x80c028220481,0x844108220501,0x814048220481,0x804008220481,0x814048220481,0x40201010080202008040081002020020800854e3,0x824088220481,0x0,0x824088220481,0x0,0x844108220501,0x804008220481,0x844108220501,0x844108220501,0x0,0x80c028220481,0x0,0x80c028220481,0x4000220481,0x14000220481,0x4000220481,0x14000220481,0x0,0x0,0x3cc01e6f301e63cc01e9cc001023000f6cc000f301e60f3097e0001e60f3204600f3079801e7e60fdd36,0x0,0x3cc03ccf300f33cc03cfcc001023000f6cc000f301e60f3097e0001e60f37b66007983cc0798f309b1b6,0x44000220481,0x4000220481,0x44000220481],
[0x4000220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_850 : TreeBound (n := 4) 107 (programCode 0x462b07341e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf300003cc1e60f307983cc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f30799556,0xf30000b6400088b0000b64001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f30799556,0x0,0x10c000208481,0x40c000208481,0x10c000208481,0xc000208481,0x0,0xc000208481,0x0,0x0,0x40c000208481,0x3cc1e63cc07983d3b69cc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f307df936,0x40c000208481,0x7983cc1e60f3079fd4fcc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f308331b6,0x80c0c320c481,0x0,0x80c0c320c481,0x8000280002000000080002000020100814e3,0xf300012fc00088b00012fc001f530007d4c000f3025f80011167981e6102307983cc97e07987983d1426,0x0,0x4000000210000000840000002100000008000060000000100100000600400001801040000100100000400000040801000101004000001010000004040000008002000010010873227,0xf303cc3cc0f30f303cc0003ccf303ccf3003ccf301e60f307d4c001e60fa99e607983cc0798f30799556,0x0,0xf300003cc0f30f303cc000798f301e6f300798f301e60f3088b0001e60fa99e607983cc0798f30799556,0x0,0x10408410a10a2,0x0,0x10408410a10a2,0x40000002100000008400000081000000080040200000100000001002000001008000404001001000004000100008010500010040000010108000040400000080020000100108732a7,0x10710412a1902],
[0x4000000210000000840000002100000008020020000080000000100200000200800040000100100000400010000801040001004000001010000004040000008002000010010873227,0x10710412a1902,0x400030001000000004000080010000200060000010000000008400000080000000080002200100002000100020000000020001200030000100000001000080001000200010007d3a8,0x0,0x0,0x0,0xf3000408c003db3000408c001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f307a2d36,0x0,0x400000101000000404000000810000001000006000000010010000060040000180104000010010000040000004080100010100400000101000000404000000800c000010010873227,0x0,0x0,0x0,0x0,0x10408410a10a2,0x0,0x10408410a10a2,0x0,0x10610412a1902,0x0,0x10610412a1902,0x400000101000000404000000810000001004002000010000010040020040100080104000010010000040004000080110000100400000101000000404000000800c000010010873227,0x0,0x0,0x0,0x0,0x10108410a10c2,0xf30007d4c003db30007980799e601e679803ccf302046000fe6b981e6102307983cc97e07987983ebd66,0x0,0xf30007d4c003db30007980799e603cc7980798f302046000fa9f981e6102307983cc97e07987983ebd66,0x0,0x10108410a10c2,0x0],
[0x10108410a10c2,0x400021001000004004000000010000020002002000008000000010000000010000004000010010000040000000080000000100400000101000000404000000800000001001087fea7,0x10110412a1902,0x400021001000004004000000010000020002002000008000000010000000020000004000010010000040000000080000000100400000101000000404000000800000001001087fea7,0x10110412a1902,0x0,0x0,0x4000000010000a0004000000010000400010000000040008000200000000200000004000008010000020000000100000000100400000081400000204000001000000001002086aba7,0x0,0xf300012fc1e60f300012fc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f3079b3b6,0xf3001e9cc01e6f3001e9cc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f307df936,0xf300012fc1e60f300012fc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f3079b3b6,0xf3003cfcc00f3f3003cfcc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f308331b6,0x0,0x144041228481,0xc4410c220501,0x144041228481,0x44000220481,0x2010000008040000010080000010080040002100100000100400000401000001004020010010000040000040080000100100220000100880000400080000801000001001887fea7,0x44000220481,0x16c87986a500003cc0003cc003db30007d4c000f304459e611167981e611162d903ccd4a07987983cde26,0x0,0x444004220481,0x3cc00f6cc00f33cfcd2fc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f3079b3b6,0x444004220481,0x79800f4e603cc79bcd2fc001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f3079b3b6,0x844108220501,0x844108220501,0x844108220501,0x44000220481,0x8020200408002200040140804024060080804104,0x0],
[0x144041228481,0xc4410c220501,0x144041228481,0x44000220481,0x0,0x44000220481,0x0,0xf6cc003cc03ccf6d4c7c001023000f6cc000f301e60f3097e0001e60fa99e607983cc0798f30799556,0x444004220481,0x0,0x444004220481,0x0,0x844108220501,0x844108220501,0x844108220501,0x44000220481,0x8020200808002200040140804024060080804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_963 : TreeBound (n := 4) 107 (programCode 0x462b07341f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x184041220481,0x0,0x50c045220481,0x424004220481,0x50c045220481,0x424004220481,0x614086220481,0x404004220481,0x614086220481,0x410080002000000080002040021000814e3,0x424004220481,0x0,0x424004220481,0x0,0xc4410c220501,0x404004220481,0xc4410c220501,0x0,0x184041220481,0x84000220481,0x284082220481,0x84000220481,0x284082220481,0x402010080002000000080002040021000814e3,0x484004220481,0x0,0x680486220481,0x3d39803cde6003d3980003ccf303ccf3003ccf301e60f3097e0001e612fc1e60000f30b640001e61556,0x680486220481,0x80000220481,0x480804220481],
[0x80000220481,0x480804220481,0x80000220481,0x81000220481,0x80000220481,0x81000220481,0x80000220481,0x0,0x0,0x0,0x0,0x484004220481,0x0,0x0,0x0,0x0,0x80000220481,0x80800220481,0x80000220481,0x80800220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x82000220481,0x0,0x82000220481,0x0,0x0,0x80c028220481,0x824088220481],
[0x80c028220481,0x844108220501,0x814048220481,0x804008220481,0x814048220481,0x0,0x824088220481,0x20400800080002000020080802040021000814e3,0x824088220481,0x20400800080002000020080802040021000814e3,0x844108220501,0x804008220481,0x844108220501,0x844108220501,0x0,0x60c086220481,0x24000220481,0x60c086220481,0x4000220481,0x414004220481,0x4000220481,0x414004220481,0x0,0x24000220481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cde6003cfcc007a73001e68a8c5,0x24000220481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cde6003cfcc007a73001e68a8c5,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x0],
[0x80c028220481,0x824088220481,0x80c028220481,0x844108220501,0x814048220481,0x804008220481,0x814048220481,0x40201010080202008040081002040021000854e3,0x824088220481,0x0,0x824088220481,0x0,0x844108220501,0x804008220481,0x844108220501,0x844108220501,0x0,0x80c028220481,0x0,0x80c028220481,0x4000220481,0x14000220481,0x4000220481,0x14000220481,0x0,0x0,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cde6003cfcc007a73001e68a8c5,0x0,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cde6003cfcc007a73001e68a8c5,0x44000220481,0x4000220481,0x44000220481],
[0x4000220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1092 : TreeBound (n := 4) 107 (programCode 0x462b073420) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf300003cc1e60f300003cc001f530007d4c000f3025f80011167981e610230798798d4a0f30f30799766,0x0,0x0,0x0,0x0,0x0,0x0,0x10088410a10a2,0x0,0x10088410a10a2,0x0,0x10090412a1902,0x0,0x10090412a1902,0x0,0x0,0x0,0x0,0x0,0x10c000200481,0x0,0x10c000200481,0xc000200481,0x20c000200481,0xc000200481,0x20c000200481,0x0,0x0,0x3cc7983cc1e603d411bcc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307984c9d36,0x0,0x7983cc1e60f3079fd4fcc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307984671b6],
[0x80c028220481,0x1e63cc1e60f301e6b643cc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f30798b65556,0x80c028220481,0xc000200481,0xf3000222c00088b00012fc001f530007d4c000f3044580011167981e611160f30798b640f30f3079d936,0xf303cc3cc2d90f30b643cc001f530007d4c000f3044580011167981e611160f30798b640f30f30799c76,0xf3000408c003db3000408c001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307983ed9b6,0xf303cc3cc2d90f303cc3cc001f530007d4c000f3044580011167981e611160f30798b640f30f30799c76,0x0,0x10108410a10c2,0xf30007d4c003db30007980799e601e679803ccf30222c00109cf981e610230798798d4a0f30f30b96d26,0x0,0xf30007d4c003db30007980799e603cc7980798f3020460010237981e610230798798d4a0f30f30b96d26,0x0,0x10108410a10c2,0x0,0x10108410a10c2,0x40000008100000010400000101000000100010000800002000820000008000020008000120000000200010002100000002000110000800020009000200010000200040002010e93a8,0x10110412a1902,0x0,0x10110412a1902,0x0,0x0,0x0,0x0,0x0,0x80002000200010000401000040240201008040e4,0x0,0x0,0xf303cc3cc2d988b0000f30f31e603cc7980798f30408c0010237981e611160f30798b640f30f30799c76,0xf3079a22c0000f300014e2003cfcc00f3f3000f304459e6097e0001e611162d903cc1e60f307983cddc6,0x10088410a10a2],
[0xf3079a22c0000f300014e2003cfcc00f3f3000f304459e6097e0001e611162d903cc1e60f307983cddc6,0x10088410a10a2,0xf300012fc0798f30000f30798f6cc00f300798f301e60f309f78001e610231e603cc1e60f307983cd556,0x10390412a1902,0x4000002010000008040000020100000080020020000080000000100200000200800040000100100000400010000801040001004000001010000004040000008002000010010873227,0x10390412a1902,0x0,0xf300012fc0004bf0000fa9800fa9800f379800f301e60f3097e0001e610231e603cc1e60f307983cf3b6,0x0,0xf300003cc1e688b0001023001ed98007a73000f3025f80011167981e610230798798d4a0f30f30799766,0xf3001e9cc01e6f3001e9cc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307984c9d36,0x0,0x80002000200010000401000040240201008040e4,0xf303cc3cc16d08b0000f30799e601e679803ccf30222c00109cf981e610230798798d4a0f30f30799766,0x0,0xf301e63cc0f388b0000f30799e603cc7980798f3020460010237981e610230798798d4a0f30f30b69426,0x0,0x10088410a10a2,0x0,0x10088410a10a2,0x0,0x10290412a1902,0x0,0x10290412a1902,0x0,0x0,0x0,0x0,0xf3003cfcc00f3f3003cfcc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307984671b6,0x0,0x144041204481,0x0],
[0x144041204481,0x44000200481,0x244000208481,0x44000200481,0x244000208481,0x0,0x0,0x3cc00f6cc00f33cdeafbc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307983d6d36,0x0,0x79800f4e603cc799f65fc001023000f6cc000f301e60f3097e0001e610231e603cc1e60f307983ed9b6,0x844108220501,0x844108220501,0x844108220501,0x44000200481,0x8020200408002200040140804024060100804104,0x0,0x144041204481,0x222c000904bcc0f303cc001f530007d4c000f3025f80011167981e610230798798d4a0f30f30799766,0x144041204481,0x44000200481,0x244000208481,0x44000200481,0x244000208481,0x1e601e67a77458f3003cc001f530007d4c000f3044580011167981e611160f30798b640f30f3079d936,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44000200481],
[0x8020200808002200040140804024060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_420 : TreeBound (n := 4) 107 (programCode 0x462b0734) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part101_421 part101_422 part101_503 part101_504 part101_505 part101_506 part101_507 part101_508 part101_589 part101_670 part101_671 part101_752 part101_753 part101_850 part101_963 part101_1092

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1221 : TreeBound (n := 4) 107 (programCode 0x462b0735) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084082240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1222 : TreeBound (n := 4) 107 (programCode 0x462b0736) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1223 : TreeBound (n := 4) 107 (programCode 0x462b0737) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084082240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1225 : TreeBound (n := 4) 107 (programCode 0x462b073851) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441204481,0x10804c7218481,0x1080441204481,0x1080441204481,0x10804c3208481,0x10804c7218481,0x10804c3208481,0x1080441204481,0x1080445210481,0x10804c7218481,0x1080445210481,0x1080441204481,0x0,0x40000000300000000c00000003000000008000600000001000080004004000018010c0000100100000400040000800000101000400001001000004004000008010000010010873227,0x4000000110000000440000000300000000c0200010100000040000000020000000080020201000080000000100000000200010402020101000000404000000800040002000107fe28,0x0,0x400000009000000024000000110000000140000008100400020000000080000000080010000000040802000200000000200010400000081004080204000001000080004000206aba8,0x4000000210000000840000002100000008000060000000100080000400400001801840000100100000400040000800000101000400001001000004004000008010000010018c73227,0x400000101000000404000000210000000840200010100000040000000020000000080020201000080000000100000000200010402020101000000404000000800020002000107fe28,0x4000001010000004040000008100000010000060000000100100000400400001801040000100100000400040000800000101000400001001000004004000008010000010010873227,0x40002000100008000400002001000000008000600000001000080004004000018010c0000100100000400040000800000101000400001001000004004000008010000010010873227,0x400020101000000004000000010000001040200010100000040000000020000000080020201000080000000100000000200010402020101000000404000000800000002000107fe28,0x400000801000002004000008010000008040000008100c00020000800080008000080010001000040802000200008000200010400000081004080204000001000010004000206aba8,0x4000010010000040040000080100000100000060000000101000000400400001811040000100100000400040000800000101000400001001000004004000008010000010018873227,0x1dcd6665a1b1de81400001dcd66a13c7bde8141dcd82cd6665a1aa6b2fccc91df40bf332477d02bb9aca00000773770d6500773d0a24835511eaca0077447ad04d73ea6c2e7cd6503b9aca00773d0794daca0077447ab2801dcf41d650077394daca0077394daca00ee6d0c85434e9,0x4000020010000080040000200100000800000060000000108000000400400001881040000100100000400040000800000101000400001001000004004000008010000010050873227,0x0,0x4000100010000400040000800100001000000060000000110000000400400001901040000100100000400040000800000101000400001001000004004000008010000010390873227,0x0,0x0,0x1010842120442],
[0x40000000900000000c00000009000000008000400811000000800004008110000008000802000002000100020220000020001010000004010008000100000100100000400420593a8,0x8000a0002008a0022804080022080020100814e3,0x40000000500000001400000011000000010000800814000000800008008140000008000808000002000100020280000020001010000004010008000100000100100000401020d93a8,0x1010842120442,0x1010842120442,0x1010842120442,0x1010842120442,0x1010842120442,0x1021842320c82,0x1010842120442,0x1021842320c82,0x4000020010000080040000200100000800000060000000108000000400400001881040000100100000400040000800000101004000001010000004040000008010000010050873227,0x0,0x4000100010000400040000800100001000000060000000140000000400400001c010400001001000004003000008000001010040000010100000040400000080c0000010210873227,0x0,0x0,0x40000000300000000c00000003000000008000600000001000080004004000018010c0000100100000400080000800000101002000001008000004010000008020000010010873227,0x4000000010000000040000000100000600000060000000100000000400400001801040000100100000400080000800000101002000001008000004010000008020000010010873227,0x0,0x0,0x4000000210000000840000002100000008000060000000100080000400400001801840000100100000400080000800000101002000001008000004010000008020000010018c73227,0x4000200010000001040000004100008010000060000000100100000400400001801040000100100000400080000800000101002000001008000004010000008020000010010873227,0x0,0x4000200010000800040000400100000000800060000000110000000400400001901040000100100000400080000800000101002000001008000004010000008020000010090873227,0x400020101000000004000000010000001040200010100000040000000020000000080020201000080000000100000000200010402020101000000404000000800040002000107fe28,0x4000000410000001040000004100008200000060000000100100000400400001801040000100100000400080000800000101002000001008000004010000008020000010010873227,0x4000010010000040040000080100000100000060000000102000000400400001821040000100100000400080000800000101002000001008000004010000008020000010010873227,0x4000040010000100040000400100009000000060000000110000000400400001901040000100100000400080000800000101002000001008000004010000008020000010090873227,0x4000020010000080040000200100000800000060000000108000000400400001881040000100100000400080000800000101002000001008000004010000008020000010050873227,0x0,0x4000100010000400040000800100001000000060000000120000000400400001a01040000100100000400080000800000101002000001008000004010000008020000010310873227,0x0],
[0x0,0x1010842120442,0x0,0x0,0x40000001100000001400000011000000010002000808000000800020008180000008002010000002000100020200000020001020000010020008000200000100200000402022793a8,0x1010842120442,0x1010842120442,0x1010842120442,0x1010842120442,0x1010842120442,0x1021842320c82,0x1010842120442,0x1021842320c82,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1306 : TreeBound (n := 4) 107 (programCode 0x462b073852) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081886204481,0x1081004210481,0x1081886204481,0x1081004210481,0x1081004208481,0x1081004200481,0x1081004208481,0x1081004210481,0x1081004210481,0x1081004200481,0x1081004210481,0x1081004210481,0x0,0x40000000300000000c0000000300000000800060000000100008000400400c008010c0000100100000400040000800000101000400001001000004004000008010000010010873227,0x1021004220481,0x0,0x80402000000000400000080002020020800814e3,0x1011886220481,0x1001004220481,0x1011886220481,0x1021004220481,0x1021004220481,0x1001004220481,0x1021004220481,0x1021004220481,0x0,0xf300f33cc0f30f300f30003ccf303ccf3003ccf30f307983cfcc00f3079f99e60f300079f9801e7f6856,0x0,0xf301e63cc0798f301e60003ccf303ccf3003ccf30f307983d39800f307a731e60f30007a73001e9dc856,0x0,0x0],
[0xf30000b6400088b00007983ccf303ccf3003ccf30f307983cfcc00f3079f99e607980079f9801e7f6856,0x0,0xf3000222c00088b0000f30799e601e679803ccf31e7e60079c08c0f307a73003cfcc7a7379803cfeff36,0x8032200c80102002040432010084042080086504,0x8002200040102002040432010084042080086704,0xf307983cc001f5300079803ccf303ccf3003ccf30f307983cfcc00f3079f99e607980079f9801e7f6856,0x8002200080102002040432010084042080086504,0xf307a76cc0409b30007980799e601e679803ccf31e7e60079c08c0f307a73003cfcc7a7379803d1e1576,0x8008200100102002040432010084042080087f04,0x8032200080102002040432010084042080086504,0x8008200200102002040432010084042080087504,0x0,0x8020200400102002040432010084042080086504,0x0,0x8020200800102002040432010084042080086504,0x0,0x40000000300000000c0000000300000000800060000000100008000400400c008010c0000100100000400080000800000101002000001008000004010000008020000010010873227,0x1021004220481,0x0,0x0,0x1011886220481,0x1001004220481,0x1011886220481,0x1021004220481,0x1021004220481,0x1001004220481,0x1021004220481,0x1021004220481,0x0,0x0,0x0,0x0],
[0x0,0xf300003cc3565b303cc000799e601e679803ccf30f6cc007af04c0f307a73001ed987aed73003d3b7d66,0x0,0x0,0xf3000222c00088b0000f30799e601e679803ccf31e9cc0079fd4c0f307b66003d3987a73f3003d3bbf36,0x8022200880102002040422010084042100084504,0x8002200040102002040422010084042100084504,0xf3000f6cc1e9db3000f300799e601e679803ccf31e9cc0079fd4c0f307b66003d3987a73f3003d3b8276,0x8002200080102002040422010084042100084504,0x400001001000004004000008010000008042002000108000000000000000040000004200010010800040000000080000000100420000101080000404000000800400001001087fea7,0x8008200100102002040422010084042100085504,0x8022200080102002040422010084042100084504,0x8008200200102002040422010084042100085504,0x0,0x8020200400102002040422010084042100084504,0x0,0x8020200800102002040422010084042100084504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1387 : TreeBound (n := 4) 107 (programCode 0x462b073853) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441204481,0x10804c7218481,0x1080441204481,0x1080441204481,0x10804c3208481,0x10804c7218481,0x10804c3208481,0x1080441204481,0x1080445210481,0x10804c7218481,0x1080445210481,0x1080441204481,0x0,0x40000000300000000c00000003000000008002200000008000080010010000028040c0000100100000400040000800000c01000400001001000004004000008010000010010873227,0x0,0x0,0x0,0x0,0x0,0x4000001010000004040000008100000010000220000000800100001001000002805040000100100000400040000800000c01000400001001000004004000008010000010010873227,0x0,0x0,0x400000801000002004000008010000008040000008100400020000800080004000080010001000040802000200008000200010400000081004080204000001000010004000206aba8,0x0,0x1dcd6665a1b1de81400001dcd66a13c7bde8147735b1cd6665a1aa6b2fccc91df40bf332477d02f7359400000773770d6500ee729e24835511eaca0077447ad04d82d11eae7cd6503b9aca00773d0794daca0077447ab2801dcf41d650077394daca0077394daca00ee6d0c85434e9,0x4000020010000080040000200100000800000220000000808000001001000002884040000100100000400040000800000c01000400001001000004004000008010000010050873227,0x0,0x4000100010000400040000800100001000000220000000810000001001000002904040000100100000400040000800000c01000400001001000004004000008010000010390873227,0x0,0x0,0xc000300010a0042804080042004022000814e3],
[0x0,0x280842120442,0x0,0x280842120442,0x280842120442,0x280842120442,0x280842120442,0x280842120442,0x481842320c82,0x280842120442,0x481842320c82,0x0,0x0,0x0,0x0,0x0,0x40000000300000000c00000003000000008002200000008000080010010000028040c0000100100000400200000800000c01002000001008000004010000008020000010010873227,0x4000000010000000040000000100000600000220000000800000001001000002804040000100100000400200000800000c01002000001008000004010000008020000010010873227,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000100010000400040000800100008000000220000000840000001001000002c04040000100100000400200000800000c01002000001008000004010000008020000010210873227,0x4000020010000080040000200100000800000220000000808000001001000002884040000100100000400200000800000c01002000001008000004010000008020000010050873227,0x0,0x4000100010000400040000800100001000000220000000840000001001000002c04040000100100000400200000800000c01002000001008000004010000008020000010210873227,0x0],
[0x0,0x0,0x0,0x280842120442,0x0,0x280842120442,0x280842120442,0x280842120442,0x280842120442,0x280842120442,0x481842320c82,0x280842120442,0x481842320c82,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1468 : TreeBound (n := 4) 107 (programCode 0x462b073854) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441204481,0x1080000210481,0x1080441204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x0,0x80400410010000400010080402020020800814e3,0x0,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0xf303cc3cc2d90f30b64000798f301e6f300798f30f307983db3000f3079f99e607980079f9801eda8856],
[0xf30000b6400088b0000798798f301e6f300798f30f307983db3000f3079f99e607980079f9801eda8856,0xf30007d4c1e60f3079f980798f301e6f300798f30f307983db3000f3079f99e607980079f9801eda8856,0xf300012fc00088b0000f30799e603cc7980798f30f4e60079fd4c0f307a73001e9cc7aecf9803cffed26,0x8022200880102004040422010084042080084504,0x8002200040102004040422010084042080084504,0x0,0x8002200080102004040422010084042080084504,0xf30007d4c001f530007980798f301e6f300798f30f307983db3000f3079f99e607980079f9801eda8856,0x8008200100102004040422010084042080085504,0x8022200080102004040422010084042080084504,0x8008200200102004040422010084042080085504,0x0,0x8020200400102004040422010084042080084504,0x0,0x8020200800102004040422010084042080084504,0x0,0x0,0x0,0x0,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0xf300003cc2d90f303cc000f31e603cc7980798f31e9cc007a76cc0f307b66003d3987a73f3003d3b8276,0x0,0x0,0xf3000222c00088b0000f30f31e603cc7980798f31e9cc007a76cc0f307b66003d3987a73f3003d3bbf36,0x8022200880102004040422010084042100084504,0x8002200040102004040422010084042100084504,0xf3000f6cc1e9db3000f300f31e603cc7980798f31e9cc007a76cc0f307b66003d3987a73f3003d3b8276,0x8002200080102004040422010084042100084504,0xf3000f6cc2dcdb30007980f31e603cc7980798f31e9cc007a76cc0f307b66003d3987a73f3003d3b8276,0x8008200100102004040422010084042100085504,0x8022200080102004040422010084042100084504,0x8008200200102004040422010084042100085504,0x0,0x8020200400102004040422010084042100084504,0x0,0x8020200800102004040422010084042100084504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1549 : TreeBound (n := 4) 107 (programCode 0x462b073855) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080882240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1550 : TreeBound (n := 4) 107 (programCode 0x462b073856) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1551 : TreeBound (n := 4) 107 (programCode 0x462b073857) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080882240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1552 : TreeBound (n := 4) 107 (programCode 0x462b073858) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1553 : TreeBound (n := 4) 107 (programCode 0x462b073859) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1554 : TreeBound (n := 4) 107 (programCode 0x462b07385a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1555 : TreeBound (n := 4) 107 (programCode 0x462b07385b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1556 : TreeBound (n := 4) 107 (programCode 0x462b07385c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1557 : TreeBound (n := 4) 107 (programCode 0x462b07385d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x600000001800000006000000018000040020000100000100400200001000801040000100100000400000040800100001004000001010000004040000008100000010010873227,0x0,0x80004400120004800130080802080022000814e3,0x108842140442,0x80008400220008800230080802080022000815e3,0x108842140442,0x110842140442,0x110842140442,0x110842140442,0x110842140442,0x110842140442,0x120842140442,0x110842140442,0x120842140442,0x110842140442,0x0,0x80200408020200808030080802080022000854e3,0x0,0x0,0x445800111600025f8079805b3e67980799ebb200fa98007b661e603cc003cfcc00f3f3003cde722395,0x2becaec0000002df3ab0000002becaec00000059335b0000000b7ceac0000000d83e700159fd80000000567f62b3fb00159fd8000159fed9fd80005680b9fd8acfec00159fdab3fb000000000159fd800005680b9fd8000000159fd8567f6002b3fb000015a02e7f6567f6000567f600000000567f600000000567f8b3fb000567f6acfec000acfec02b3fb0159fdab3fb00015a00e45d4cde6bab,0x445800111600025f8079803cde67980799e9cc03d398007b661e603cc00f33cc03ccf300799e722395,0x445800111600025f8079803cde67980799e9cc000798007b661e603cc00003cc0000f300799e722395,0x0,0x0,0x445800111600025f80798222de6798079a082c1e6798007b661e603cc07983cc1e60f303cc1e722395,0x445800111600025f8079803cde67980799e9cc01ed98007b661e603cc0079bcc01e6f379801e722395,0x12000000028000000220000000280000400001001000004010002000010008040010000800100001000000810005000010000400008001000010010000100010000100328613a7,0x0,0xa00000008800000012000000028000040000080100000200400200001000802004000040004000400000080800100001000080000400800004001000008002000010031853227,0x445800111600025f8079803cde67980799e9cc01ed98007b661e603cc0079bcc01e6f6cc799e722395],
[0x0,0x445800111600025f80798222de6798079a082c1e6798007b661e603cc07983cc1e60f6cc001e722395,0x0,0x445800111600025f8079803cde67980799e9cc000798007b661e603cc00003cc0000f6cc001e722395,0xf307983cc1e6000079807980001e67980799e6000003cc0001e61e603cfcc001f53000f6cc001e703885,0x0,0x20a0aa240481,0x208842140442,0x20a0aa240481,0x208842140442,0x2120ca240481,0x22208a240481,0x2120ca240481,0x2521ca240501,0x22208a240481,0x22208a240481,0x22208a240481,0x2521ca240501,0x24218a240501,0x22208a240481,0x24218a240501,0x2521ca240501,0x400020000000080004000200010000800020002000080000000100020000100080006000010008000040000000080040000100400000101000000404000000810000001001087fea7,0x8118007b66000fa9807981e61e6811879a04600f31e603cde61f533cfcc001023000f6cc001e703375,0x0,0x80a028240481,0x208842140442,0x80a028240481,0x208842140442,0x812048240481,0x802008240481,0x812048240481],
[0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x40a02c240481,0x208842140442,0x40a02c240481,0x208842140442,0x41204c240481,0x40200c240481,0x41204c240481,0x46218c240501,0x42208c240481,0x40200c240481,0x42208c240481,0x46218c240501,0x44210c240501,0x40200c240481,0x44210c240501,0x46218c240501,0x0,0x400020001000080004000204200000840000802100002000400000021000020085080100014200400010800800100001004000001010000004040000008100000010010873227,0x408842140442,0x800040002000400008000800400001040000000100004000400000041000040100000040000000400001000800100001004000000410000004040000008100000010030853227,0x408842140442,0x6120ce240481],
[0x2008240481,0x6120ce240481,0x842108240501,0x42208c240481,0x2008240481,0x42208c240481,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0,0x40a02c240481,0x208842140442,0x40a02c240481,0x208842140442,0x41204c240481,0x40200c240481,0x41204c240481,0x46218c240501,0x42208c240481,0x40200c240481,0x42208c240481,0x46218c240501,0x44210c240501,0x40200c240481,0x44210c240501,0x46218c240501,0x0,0x0,0x408842140442,0x0],
[0x408842140442,0x812048240481,0x2008240481,0x812048240481,0x42108240501,0x822088240481,0x2008240481,0x822088240481,0x2008240481,0x42108240501,0x2008240481,0x42108240501,0x2008240481,0x0,0x80a028240481,0x208842140442,0x80a028240481,0x208842140442,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x14804100120084802104080802080022000814e3],
[0x0,0x15008100220088802204080802080022000815e3,0x0,0x6120ce240481,0x2008240481,0x6120ce240481,0x842108240501,0x42208c240481,0x2008240481,0x42208c240481,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0,0x80a028240481,0x0,0x80a028240481,0x0,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501],
[0x0,0x0,0x0,0x0,0x0,0x812048240481,0x2008240481,0x812048240481,0x42108240501,0x822088240481,0x2008240481,0x822088240481,0x2008240481,0x42108240501,0x2008240481,0x42108240501,0x2008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1766 : TreeBound (n := 4) 107 (programCode 0x462b07385e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030004082002000080102080022000814e3,0x16c800111600016c8079800fa9800f379800f30f307983cc01e6f307d4c1e60f30007d4c001e610856,0x1400050004082002000080102080022000814e3,0x445800111600025f80f3001e9cc0079f9800f31e601e6798408cf307d4c003db307a76cc003cc23f36,0x282042140442,0x282042140442,0x282042140442,0x282042140442,0x8400210000002000000080002080022000814e3,0x104002100400208004040e010088032200081f04,0x282042140442,0x104004100400208004040a010088022200081504,0x0,0x0,0x20a042140442,0x0,0x20a042140442,0x811886240481,0x800000240481,0x811886240481,0x800000240481,0x821004240481,0x800000240481,0x821004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x0,0x609886240481],
[0x80a0425414c2,0x609886240481,0x80a0425414c2,0x411004240481,0x240481,0x411004240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x0,0x0,0x0,0x0,0x811886240481,0x800000240481,0x811886240481,0x800000240481,0x821004240481,0x800000240481,0x821004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501],
[0x0,0x0,0x80a0425414c2,0x0,0x80a0425414c2,0x411004240481,0x240481,0x411004240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x42108240501,0x240481,0x42108240501,0x240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1847 : TreeBound (n := 4) 107 (programCode 0x462b07385f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x600000001800000006000000018000200020000800000101000200002000801040000100100000400000040800c00001004000001010000004040000008100000010010873227,0x0,0xfa98003ea6016cf980f301e67988118f3204600f33cc03cde6b6403cc003cde600f3f3003cde703885,0x7980001e600f37981e600007987980f31e6000007980001e679803cc00003cc0000f33cc01e703d95,0x1ed98007b6600f37981e601e67987980f3204600007980799e679803cc00f33cc03ccf300799e703d95,0x7980001e6016cf980f300007987980f31e6000003cc0001e6b6403cc00001e60000f300001e703885,0x0,0x0,0x0,0x7983cc1e600f37981e600007987980f31e6000007980001e679803cc00003cc0000f4e6001e703d95,0x2000008008000400020000080080002000000002000000020002000020008000000001000800001000000010008000010001000010001000010010000100010000100208793a7,0x0,0x7983cc1e600f37981e600007987980f31e6000007980001e679803cc3cc03ccf300f31e601e703d95,0x0,0x0,0x2000106008000400020000080080000800000004000800020002000020008000000000401e6000200000001000800001004000000410000002000000010100000010020852ba7,0x0,0x0,0x0,0x445800111600025f81e6005b9987980f31ebb200fa9800f4e679803cc003cfcc00f3f3003cde722395,0x2200000008800000012000000028000200000000800000401000200002000804000000100000000400000200800c0000100000000100080000400020000800c000010032873227,0x445800111600025f81e6003d3987980f31e9cc03d39800f4e679803cc00f33cc03ccf300799e722395,0x445800111600025f81e6003d3987980f31e9cc00079800f4e679803cc00003cc0000f300f31e722395,0x6000000048000000220000000280000400000404000837820002000020008100000400200704e020000004100080000100001000020004000200010001000010001002084aba7,0x2200000008800000012000000028000200000000800000401000200002000804000000100000000400000200800c00001000000001000080004040000008100800010032873227,0x445800111600025f81e602233987980f32082c1e679800f4e679803cc07983cc1e60f303cc1e722395,0x445800111600025f81e6003d3987980f31e9cc00079800f4e679803cc00003cc03ccf4e6001e722395,0x0,0x0,0x22000000018000000120000000280002000201a010000010100020080200080202a43010001200008001004080040020100020000100010000080100000800200001001087cea7,0x445800111600025f81e6003d3987980f31e9cc03d39800f4e679803cc00f33cc03ccf6ccf31e722395],
[0x0,0x445800111600025f81e602233987980f32082c1e679800f4e679803cc07983cc1e60f6cc001e722395,0x0,0x445800111600025f81e6003d3987980f31e9cc00079800f4e679803cc00003cc0000f6cc001e722395,0x0,0x16c80005b200016c80f3001ed9879fa731e7e600f6cc003ea6b6403cc003cde600f3f3003cde703885,0x7981e61e600007981e600007987980f31e6000007980001e679803cc00003cc0000f33cc01e703d95,0x445800111600044581e6003d3987980f31e9cc03d39800f4e679803cc00f33cc03ccf300799e722395,0x7980001e600007980f300007987980f31e6000003cc0001e6b6403cc00001e60000f300001e703885,0x0,0x0,0x7980001e600007980f300007987980f31e6000003cc0001e6b6403cc03cc1e61e60f303cc1e703885,0x7980001e600007980f300007987980f31e6000003cc0001e6b6403cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x0,0x7980001e600007980f300007987980f31e6000003cc0001e6b6403cc79801e7e600f379801e703885,0x200016000800040002000000008000080000000400080002000200002000800000000040160000200000001000800001004000000410000002000000010100000010020852ba7,0x7980001e600007980f300007987980f31e6000003cc0001e6b6403ccf3001ed9800f3f3001e703885,0x200016000800040002000000008000080000000400080002000200002000800000000040160000200000001000800001004000000416000002000000010100000010020852ba7,0x0,0x20a0aa240481,0x0,0x20a0aa240481,0x0,0x2120ca240481,0x22208a240481,0x2120ca240481,0x2521ca240501,0x22208a240481,0x22208a240481],
[0x22208a240481,0x2521ca240501,0x24218a240501,0x22208a240481,0x24218a240501,0x2521ca240501,0x7983cc1e60f307981e600007987980f31e6000007980001e679803cfcc003db3000f6cc001e703d95,0x1ed98007b66000fa981e601e67987980f3204600007980799e679803cfcc003db3000f6cc001e703d95,0x7980001e60b647980f300007987980f31e6000003cc0001e6b6403cfcc001f53000f6cc001e703885,0x0,0x40a02c240481,0x0,0x40a02c240481,0x0,0x41204c240481,0x40200c240481,0x41204c240481,0x46218c240501,0x42208c240481,0x40200c240481,0x42208c240481,0x46218c240501,0x44210c240501,0x40200c240481,0x44210c240501,0x46218c240501,0x0,0x400020001000080004000304200000a000200008000001010000000220008010c0000100100000400000040800c00001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x6120ce240481],
[0x2008240481,0x6120ce240481,0x842108240501,0x42208c240481,0x2008240481,0x42208c240481,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0,0x40a02c240481,0x0,0x40a02c240481,0x0,0x41204c240481,0x40200c240481,0x41204c240481,0x46218c240501,0x42208c240481,0x40200c240481,0x42208c240481,0x46218c240501,0x44210c240501,0x40200c240481,0x44210c240501,0x46218c240501,0x7980001e60f307980f300007987980f31e6000003cc0001e6b6403cfcc001f53000f6cc001e703885,0x0,0x80a028240481,0x1e67980799e601e60799e601e67987980f320461e607987981e679803cfcc003db3000f6cc001e703d95],
[0x80a028240481,0x1e67980799e601e60f30f303cc79888b0f3222c1e603cc7981e6b6403cfcc001f53000f6cc001e8e9885,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x7d4c001e6f30088b000079800088b000222c03cc3cc1e6b6403cfcc001f53000f6cc001e703885,0x200010e008700000020000000004000800000004000870020002000020008000000000401ee00020000000100080000100400000041000000204000001010000001002085aba7,0x1e9cc00799e6011160000798001f53000798007980001e679803cfcc003db3000f6cc001e703d95,0x20001e000f000000020000000000000800000004000f00020002000020008000000000401e000020000000100080000100400000041000000204000001010000001002085aba7,0x6120ce240481,0x2008240481,0x6120ce240481,0x842108240501,0x42208c240481,0x2008240481,0x42208c240481,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0],
[0x80a028240481,0x0,0x80a028240481,0x0,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x0,0x20001e0008700000020000200004000800000004000870020002000020008000000000401e000020000000100080000100400000041000000204000001010000001002085aba7,0x0,0x200010000f000000020000000000000800000004000f00020002000020008000000000401e000020000000100080000100400000041000000204000001010000001002085aba7,0x812048240481,0x2008240481,0x812048240481,0x42108240501,0x822088240481,0x2008240481,0x822088240481,0x2008240481,0x42108240501,0x2008240481,0x42108240501],
[0x2008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2040 : TreeBound (n := 4) 107 (programCode 0x462b073860) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x282042108442,0x282042104442,0x282042108442,0x282042104442,0x282042108442,0x282042108442,0x282042108442,0x282042108442,0x0,0x282042110442,0x282042108442,0x282042110442,0x16c80005b200016c8079801e7e67983cc1e7e7e603cc003ea61e603cc79801e7e600f379801e703885,0x0,0x16c80005b200016c80f3001e9cc7983cc1e7e9cc03cc003ea63cc03ccf3001ed9800f3f3001e703885,0x0,0x0,0x18204218c642,0x182042184642,0x182042188442,0x182042184642,0x18204218c642,0x182042188442,0x182042188442,0x182042188442,0x400410000002000000080002008020200814e3,0x182042190c82,0x18204218c642,0x182042190c82,0x0],
[0x0,0x0,0x0,0x0,0x282042108442,0x382042184642,0x282042108442,0x382042184642,0x282042108442,0x282042108442,0x282042108442,0x282042108442,0x0,0x0,0x282042108442,0x0,0x0,0x282042120442,0x0,0x282042120442,0x445800111600025f81e6001ed98007a73000f31e601e67984458f307d4c003db307a76cc003cc23f36,0x282042140442,0x282042140442,0x282042140442,0x282042140442,0x0,0x0,0x0,0x0,0x3cc1e688b0798f301116001ed98007a73000f31e601e67984458f307d4c003db307a76cc003cc23f36,0x410000240481,0x400000240481],
[0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x441004240481,0x400000240481,0x441004240481,0x400000240481,0x104002100400210004040a010088022200081504,0x282042140442,0x104004100400210004040a010088022200081504,0x0,0x20004800120006000120080802080022000814e3,0x20a042140442,0x2000880022000a000220080802080022000815e3,0x20a042140442,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x10004100100002000000080002080022000814e3],
[0x80a0425414c2,0x10008100200002000000080002080022000814e3,0x80a0425414c2,0x410000240481,0x240481,0x410000240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x40005000140006000140081002080022000814e3,0x0,0x4000900024000a000240081002080022000815e3,0x0,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501],
[0x0,0x0,0x80a0425414c2,0x0,0x80a0425414c2,0x10000240481,0x240481,0x10000240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40000240481,0x240481,0x40000240481,0x240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_1224 : TreeBound (n := 4) 107 (programCode 0x462b0738) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part101_1225 part101_1306 part101_1387 part101_1468 part101_1549 part101_1550 part101_1551 part101_1552 part101_1553 part101_1554 part101_1555 part101_1556 part101_1557 part101_1766 part101_1847 part101_2040

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2185 : TreeBound (n := 4) 107 (programCode 0x462b0739) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2186 : TreeBound (n := 4) 107 (programCode 0x462b073a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x1080486240481,0x8040201000102002041048020108040e00010104,0x1080486240481,0xf307983cc1e60f30798000798f301e6f300798f33cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0x1080804240481,0x1080000240481,0x1080804240481,0x1080000240481,0x1081000240481,0x1080000240481,0x1081000240481,0x1080000240481,0x0,0x100a045240481,0x80402002020000800010080002080022000814e3,0x100a045240481,0x80402000020000800000080002080022000814e3,0x1012086240481,0x1002000240481,0x1012086240481,0x80402004020100804020080802080022000834e3,0x1022004240481,0x1002000240481,0x1022004240481,0x80402000020000800000080002080022000814e3,0x1042108240501,0x802020040c002080041048020108070200402104,0x1042108240501,0x802020080c002100041048020108060200804104,0x0,0x8040200004002080041048020108070200402104],
[0x8000a00014002080041048020108070200402104,0x0,0x108804240481,0x140c02014002080041008c20108070200402104,0x108804240481,0x445ad911160001e61116003d39800f379800f3f307b69cc003cfcc1e9cc2d90f300f33cc03cc1e9cb6,0x209804240481,0x8804240481,0x209804240481,0x609804240481,0x408804240481,0x408804240481,0x408804240481,0x408804240481,0x808c86240481,0x609804240481,0x808c86240481,0x0,0xf300012fc0004bf0000fa9800fa9800f379800f33cc1e63cde6003cc1e9cc1e60f300f33cc03cc1e93b6,0x8043200044002080041048020108070200402b04,0x8002200044002080041048020108070200402b04,0x8070200404002080041048020108070200402104,0x0,0x131804240481,0x1e6f30079bcc00f37a73001e9cc0079f9800f379800f4e60f4e9cc1e9cc0798f30a713cc03cc270776,0x131804240481,0x1e67980799e601e679f9800fa9800f379800f33cc1e63cc003cfcc1e9cc1e60f300f33cc03cc1f86b6,0x221000240481,0x240481,0x221000240481,0x240481,0x400000240481],
[0x240481,0x400000240481,0x240481,0x800000240481,0x240481,0x800000240481,0x240481,0x804c200104002080041048020108070200402b04,0x8008200104002080041048020108070200402b04,0x8048200104002080041048020108070200402b04,0xf3003cfcc00f3f3003cc79800fa9800f379800f33cc1e63cde6003cc1e9cc1e60f300f33cc03cc2c38d6,0x8040200004002080041048020108070200402104,0x8020200404002080041048020108070200402104,0x8040200004002080041048020108070200402104,0x8020200804002080041048020108070200406104,0x0,0x100a045240481,0x0,0x1032086204481,0x1022004210481,0x1032086204481,0x80002002040001000000080002000020000814e3,0x1022004208481,0x1022004200481,0x1022004208481,0x1022004220481,0x1022004210481,0x1022004210481,0x1022004210481,0xf30000b6400088b00007b6601023000f31e600f33cc1e63cde6003cc1e61e7e6007983cc1e60f30dd8d6,0x1022004220481,0x8000a0001c002080041048020104070080402104],
[0x1022004220481,0x0,0x100a045240481,0x0,0x102a045204481,0xf300003cc0f30f303cc1e600007980000f300000000799e601e600003cc00003cc0000f33cc01e703d95,0x102a045204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481,0x0,0x1042108210501,0x1002000200481,0x1042108210501,0xf300012fc0004bf0000f4e601023000f31e600f33cc1e63cde6003cc1e61e7e6007983cc1e60f30dd8d6,0x0,0xf300012fc0004bf0001116001023000f4e6000f33cc1e63cde6003cc1e6799e607983cc0798f3079b3b6,0x0,0xf300012fc0004bf0001023001023000f3f3000f33cc1e63cde6003cc1e6f31e603cc1e60f307983cf3b6,0x1012086240481,0x1002000240481,0x1012086240481,0x80002008040001000000080002080022000814e3,0x1022004240481,0x1002000240481,0x1022004240481,0x0,0x12a045240481,0x0,0x12a045240481,0x0],
[0x2721ce240501,0x2000240481,0x2721ce240501,0x842108240501,0x422004240481,0x2000240481,0x422004240481,0x2000240481,0x842108240501,0x2000240481,0x842108240501,0x2000240481,0x1042108240501,0x0,0x132086240481,0x120002408102002041048020108040e00010104,0x132086240481,0x1f5300088b0001f53000799023000f300798f33cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0x222004240481,0x2000240481,0x222004240481,0x802000240481,0x402000240481,0x2000240481,0x402000240481,0x2000240481,0x802000240481,0x2000240481,0x802000240481,0x2000240481,0x1042108240501,0x0],
[0x0,0x0,0x0,0x20460008118002046000799023000f300798f33cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0x202000240481,0x2000240481,0x202000240481,0x842108240501,0x46218c240501,0x2000240481,0x46218c240501,0x2000240481,0x842108240501,0x2000240481,0x842108240501,0x2000240481,0x0,0x0,0xf307983cc0000f300001e6003cfcc00f3f3000f3f381183cde6003cc1e9cc2d900005b200007983cddc6,0xf30d4a3cc0798f301e61e6003d39800f3f3000f3f381183cde6003cc1e6012090003ea600044583cde56,0x0,0xf301e63cc0798f3097e0f3000f6cc00f3f3000f33cc1e63cde6003cc1e60097e000204600081183cd556,0xf308301cc007a73001e7e6003d39800f3f3000f3f381183cde6003cc1e9d3c590007b66001ed984123d6,0xf3001e9cc007a7307b66f3000f6cc00f3f3000f33cc1e63cde6003cc1e602046001e7e6001ed98411ad6,0xf307983cc0000f300001e6003d39800f3f3000f3f381183cde6003cc1ebb22d903cc1e60f307983cde56,0x0,0xf3002268c0089a307ba3b3000f6cc00f3f3000f33cc1e63cde6003cc1e60f4e6004476600f3798411ad6,0xf3000408c001023079bdb3000f6cc00f3f3000f33cc1e63cde6003cc1e60f4e600f31e600f3798411ad6,0xf307ab38c0010230003ea6003d39800f3f3000f3f381183cde6003cc1ea08ed90f301e600f37984123d6,0xf3000f6cc003db307a73f3000f6cc00f3f3000f33cc1e63cde6003cc1e61e7e600799e601e67984300d6,0xf307983cc0000f300001e6003d39800f3f3000f3f381183cde6003cc1e9cc2d90f301e600007983cde56,0xf307983cc0000f300001e6003d39800f3f3000f3f381183cde6003cc1e7e62d907981e607987983cde56],
[0xf307983cc0000f300001e6003d39800f3f3000f3f381183cde6003cc1e9cc2d90f301e600007983cde56,0xf300003cc0000f307980f3000f6cc00f3f3000f33cc1e63cde6003cc1e6f31e603cc1e60f307983cd556,0x0,0x0,0x0,0x0,0x0,0x60a044341902,0x20a044341902,0x80a0446410a2,0x20a044341902,0x0,0x40a0442410a2,0x40a0442410a2,0x40a0442410a2,0x0,0x80a0446410a2,0x0,0x80a0446410a2,0x0,0xf307983cc0000f307981e6003cfcc00f3f3000f3f381183cde6003cc1e9cc2d900005b200007983cddc6,0xf307983cc0002d907980f3000f6cc00f3f3000f33cc1e63cde6003cc1e6005b20003ea600044583cd556,0x0,0xf307983cc0004bf07980f3000f6cc00f3f3000f33cc1e63cde6003cc1e60097e000204600081183cf3b6,0xf308301cc007a7307981e6003d39800f3f3000f3f381183cde6003cc1e9d3c590007b66001ed984123d6,0xf307983cc007a7307980f3000f6cc00f3f3000f33cc1e63cde6003cc1e602046001e7e6001ed98411ad6,0x0,0xf307983cc01e6f307980f3000f6cc00f3f3000f33cc1e63cde6003cc1e603ea6000f4e6003d398504ad6,0xf30b643cc0798f307981e6003d39800f3f3000f3f381183cde6003cc1ebeeed903cc1e600f37983cde56,0xf307983cc0798f307980f3000f6cc00f3f3000f33cc1e63cde6003cc1e60f4e600f31e600f37983cd556,0xf30b643cc0798f307981e6003d39800f3f3000f3f381183cde6003cc1ea08ed90f301e600f37983cde56,0xf307983cc0798f307980f3000f6cc00f3f3000f33cc1e63cde6003cc1e61e7e600799e601e67983cd556],
[0x0,0x0,0x0,0x0,0xf3000222c00088b0001116001ed98007a73000f379f9801e7f5303cc1e9cc0f30f30d4a3cc0798b69936,0xf307983cc0010230003db3000f6cc00f3f3000f33cc1e63cde6003cc1e9cc1e60f301e63cc0798411ad6,0xf3000408c003db30003db3000f6cc00f3f3000f33cc1e63cde6003cc1e9cc1e60f301e63cc07984300d6,0xf307983cc0798f301e60f3000f6cc00f3f3000f33cc1e63cde6003cc1e9cc1e60f301e63cc07983cd556,0x0,0x0,0x0,0x0,0x3ccf300f33cc01e67b66001ed98007a73000f379801e7e60fa9bcc1e9cc0f30f30d4a3cc0798b87f36,0x200000240481,0x240481,0x200000240481,0x240481,0x400000240481,0x240481,0x400000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0xf3001e9cc0000f3001e6f3000f6cc00f3f3000f33cc1e63cde6003cc1e9cc1e60f301e63cc07983cd556,0xf3001e9cc01e6f3001e6f3000f6cc00f3f3000f33cc1e63cde6003cc1e9cc1e60f301e63cc0798504ad6,0x0,0x0,0x0,0x0,0x3cc1e60f3fa981e7e7e6001ed98007a73000f379801e7e60fa9bcc1e9cc0f30f30d4a3cc0798bf2436],
[0x220000240481,0x20000240481,0x220000240481,0x20000240481,0x420000240481,0x20000240481,0x420000240481,0x20000240481,0x822004240481,0x20000240481,0x822004240481,0x20000240481,0xf3003cfcc00f3f3003ccf3000f6cc00f3f3000f33cc1e63cde6003cc1e9cc1e60f301e63cc07984a98d6,0x0,0xf307983cc00000000001e6003d398007a73000f3f381181e7f5303cc1e9cc2d90f30d4a3cc07983cde26,0x4a0a0008118000f301e6003d398007a73000f3f307b67e60f6cfcc1e9cc2d90f30d4a3cc07983cde26,0x0,0x204600081180020460f3000f6cc00f3f3000f33cc1e63cc003cfcc1e9cc1e60f301e63cc07983cd556,0x241804240481,0x40000240481,0x241804240481,0x40000240481,0x441000240481,0x40000240481,0x441000240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x8020200404002100041048020108060200804104,0x0],
[0xf307983cc00000000001e6003d398007a73000f3f381181e7f5303cc1e9cc2d90f30d4a3cc07983cde26,0x0,0x0,0x0,0x241804240481,0x40000240481,0x241804240481,0x40000240481,0x441000240481,0x40000240481,0x441000240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x8020200804002100041048020108060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2491 : TreeBound (n := 4) 107 (programCode 0x462b073b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2493 : TreeBound (n := 4) 107 (programCode 0x462b073c51) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441204481,0x1080404210481,0x1080441204481,0x1080400200481,0x10804c3208481,0x1080400200481,0x10804c3208481,0x1080441204481,0x1080404210481,0x10804c7218481,0x1080404210481,0x1080400200481,0x0,0x1008428220481,0x10204c9220481,0x1008428220481,0xf307983cc1e60f300f3000408c0017bb0005eec1e603cc7981e6f3003cc79801e7e600f379801e8e9885,0x1010448220481,0x1000408220481,0x1010448220481,0x80402000100804020120080802020020800814e3,0x10204c9220481,0x10304c9220481,0x10204c9220481,0x80102000000800020020080002020020800814e3,0xf300f33cc03ccf300f3000408c0017bb0005eec1e601e67981e711603cc79800f4e600f379801e8e9375,0xf303cc3cc0f30f300f362b803cde600f379800f3f381183cde6007983d1b2315cf300f307983cc1e7e56,0xf300f33cc0f30f301e600044580018ae00062b81e601e67981e711603cc79800f4e600f379801f44d375,0xf303cc3cc0f30f301e65b2003d39800f4e6000f3f381183cde6007983d1b22d90f303cc1e60f30799e56,0x0,0x1000044220022],
[0xf30000b6400088b00007983ccf300f3f6cc3ccf37983cc1e822c07983cc799e607980008118001e61556,0x8000a0002008a0022804080122080020100814e3,0xf300012fc0004bf0000f30798f301e6f6cc798f37983cc1e8d9007983cc799e60798000fa98003cc33b6,0x1031844320c82,0x1011844320c82,0x1000044220022,0x1011844320c82,0x1031844320c82,0x1021844320c82,0x1031844320c82,0x1021844320c82,0xf300f33cc03ccf300f3000408c0017bb0005eec1e603cc7981e6f3003cfcc001f53000f379801e8e9885,0xf300f33cc0f30f300f3079800f4e600f745800f37983cc1e7e6007983cc799e607980f307983cc1e7556,0xf301e63cc0f30f301e60005388001c7a00071e8b6403ced901e6f3003cfcc001f53000f5d9001f267885,0xf301e63cc0798f301e60f3000f6cc00f7bf000f37983cc1e7e6007983cc799e607981e607987983cd556,0x0,0x1008428220481,0x10204c9220481,0x1008428220481,0x0,0x1010448220481,0x1000408220481,0x1010448220481,0xf307983cc0000f300007983cc0000f300003cc03cc0798f301e600003cde6003d39800f3f3001e703d95,0x10204c9220481,0x10304c9220481,0x10204c9220481,0xf301e63cc0798f3097e00044580018ae00062b83cc01e6f301e72fc03cc79800fa9800f3f3001eacf375,0xf300f33cc03ccf300f3000408c0017bb0005eec3cc01e6f301e72fc03cc79800fa9800f3f3001e8e9375,0x0,0xf300f33cc0f30f301e60004bf0001a940006a503cc01e6f301e72fc03cc79800fa9800f3f3001f44d375,0x0],
[0x0,0x1000044220022,0x40000001100000000c0000000900000000c0020010000000008000100080000000080200350000200010002000000002000100200020010200000002000000082000000200017d3a8,0x0,0xf300012fc0004bf0000f30798f301e6f6cc798f37983cc1e85f807983ccf31e603cc0010230003cc33b6,0x1031844320c82,0x1011844320c82,0x1000044220022,0x1011844320c82,0x1031844320c82,0x1021844320c82,0x1031844320c82,0x1021844320c82,0x0,0xf300f33cc0f30f300f3079800fa9800f745800f37983cc1e7e6007983ccf31e603cc3cc0f30f3097f556,0x0,0xf301e63cc0798f301e60f3000f6cc00f7bf000f37983cc1e7e6007983ccf31e603cc1e60f307983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2574 : TreeBound (n := 4) 107 (programCode 0x462b073c52) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081886204481,0x1081004210481,0x1081886204481,0x1081004210481,0x1081004208481,0x1081004200481,0x1081004208481,0x1081004210481,0x1081004210481,0x1081004200481,0x1081004210481,0x1081004210481,0x0,0x100946d220481,0x1021004220481,0x100946d220481,0x80402000000000400000080002020020800814e3,0x1011886220481,0x1001004220481,0x1011886220481,0x1021004220481,0x1021004220481,0x1001004220481,0x1021004220481,0x1021004220481,0x4000020010000080040000200100000800040020000100008000400200000c00880040000100100000400040000801000001000400001001000004004000008010000010050873227,0x0,0x4000100010000400040000800100001000080020000200020000800200000c00a00040000100100000400080000801000001000400001001000004004000008010000010310873227,0x0,0x0,0x80400030000810020410100402020004800100e4],
[0x180444620222,0x0,0x180444620222,0xf30798007b66001ed980003ccf303ccf3003ccf37983cc1e63cc07983cc79803d398001ed98007a1d016,0x2400090000810020410100402020004800512e4,0x180444620222,0x0,0x10c00410000810020410100402020004802112e4,0x840021000081002041010040202000480111ae4,0x20400410000810020410100402020004802112e4,0x10400410000810020410100402020004802112e4,0x0,0x0,0x0,0x0,0x0,0x100946d220481,0x1021004220481,0x100946d220481,0x0,0x1011886220481,0x1001004220481,0x1011886220481,0x1021004220481,0x1021004220481,0x1001004220481,0x1021004220481,0x1021004220481,0x4000020010000080040000200100000800040020000100008000400200000c00880040000100100000400040000801000001002000001008000004010000008020000010050873227,0x0,0x4000100010000400040000800100001000200020000800040001000200000c00c00040000100100000400200000801000001002000001008000004010000008020000010210873227,0x0],
[0x0,0x0,0x180444620222,0x40101000081002040820040a020005000100a4,0x180444620222,0x2402090000810020410200402040005000512e4,0x2400090000810020410200402040005000512e4,0x180444620222,0x0,0xc0143000081002040820040a020005000100a4,0x840021000081002041020040204000500111ae4,0x0,0x10400410000810020410200402040005002112e4,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2655 : TreeBound (n := 4) 107 (programCode 0x462b073c53) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080441204481,0x1080404210481,0x1080441204481,0x1080400200481,0x10804c3208481,0x1080400200481,0x10804c3208481,0x1080441204481,0x1080404210481,0x10804c7218481,0x1080404210481,0x1080400200481,0x0,0x1008428220481,0x10204c9220481,0x1008428220481,0xf307983cc1e60f300f30007d4c00454b0009bac1e603cc7981e6f3003cc79801e7e600f379801e8e9885,0x1010448220481,0x1000408220481,0x1010448220481,0x80402000201008040220080802020020800815e3,0x10204c9220481,0x10304c9220481,0x10204c9220481,0x80102000001000040020080002020020800814e3,0xf300f33cc03ccf300f3000408c00454b0009bac1e601e67981e711603cc79800f4e600f379801e8e9375,0x0,0xf300f33cc0f30f301e6000445800463e0009f781e601e67981e711603cc79800f4e600f379801f44d375,0x0,0x0,0xc000300010a0042804080142004022000814e3],
[0x16c800111600016c8079800f300f3f379bccf37983cc1e63cded983cc7983ce5f80008118001e61556,0x80044220022,0x25f800097e00025f81e6000f301e6f4e6798f37983cc1e6f33d3983cc798f34458000fa98003cc33b6,0x681844320c82,0x281844320c82,0x80044220022,0x281844320c82,0x681844320c82,0x481044220882,0x481044220882,0x481044220882,0x0,0x0,0x0,0x0,0x0,0x1008428220481,0x10204c9220481,0x1008428220481,0x0,0x1010448220481,0x1000408220481,0x1010448220481,0x0,0x10204c9220481,0x10304c9220481,0x10204c9220481,0xf301e63cc0f30f307980008118004824000aea83cc03cde601e6f3003ccf3001ed9800f3f3001f267885,0xf300f33cc03ccf300f3000408c00454b0009bac1e601e7e601e72fc03cc79800fa9800f3f3001e8e9375,0x0,0xf300f33cc0f30f301e6000408c004824000b2741e601e7e601e72fc03cc79800fa9800f3f3001f44d375,0x0],
[0x0,0x0,0x0,0x80044220022,0x25f800097e00025f80f3000f301e6f3f3798f37983cc1e679bd3983ccf3079c08c0010230003cc33b6,0x681844320c82,0x281844320c82,0x80044220022,0x281844320c82,0x681844320c82,0x481044220882,0x481044220882,0x481044220882,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2736 : TreeBound (n := 4) 107 (programCode 0x462b073c54) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f30798000f31e603cc7980798f3f379803ce04607983cfcc00088b079a22c0007985936]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2737 : TreeBound (n := 4) 107 (programCode 0x462b073c55) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2738 : TreeBound (n := 4) 107 (programCode 0x462b073c56) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2739 : TreeBound (n := 4) 107 (programCode 0x462b073c57) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2740 : TreeBound (n := 4) 107 (programCode 0x462b073c58) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2741 : TreeBound (n := 4) 107 (programCode 0x462b073c59) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2742 : TreeBound (n := 4) 107 (programCode 0x462b073c5a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2743 : TreeBound (n := 4) 107 (programCode 0x462b073c5b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2744 : TreeBound (n := 4) 107 (programCode 0x462b073c5c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2745 : TreeBound (n := 4) 107 (programCode 0x462b073c5d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x182041240481,0x80400410020000800010080002080022000814e3,0x182041240481,0x80400010020000800000080002080022000814e3,0x2020000008080000010200000010800020002100080000100100000000100000007020010000080040000040080000000100400000101000000404000000810000001001887fea7,0x82000240481,0x8118007b66000fa9807981e61e6811879a04600f31e603cde712533cfcc001023000f6cc001e703375,0x0,0x1e6000bdd800204600081180020467988119e6204601e67981e711603cfcc001023000f6cc001e703375,0x209044240882,0x1e600222c0007b66000fa98003ea67980799e63ea607987981e6f3003cfcc003db3000f6cc001e7241f5,0x209044240882,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x482004240481,0x80400010020000800000080002080022000814e3,0x482004240481,0x82000240481,0x0,0x1e6000811800204600081180020467988119e6204601e67981e711603cfcc001023000f6cc001e703375,0x8044240022],
[0x1e6001ed98007b66000fa98003ea67980799e63ea607987981e6f3003cfcc003db3000f6cc001e7241f5,0x8044240022,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0xf30007d4c001f6230081181e61e6812011a047f6231e6408de721833cfcc001023000f6cc001e703375,0x1e600097e0007b66000b64000f300f3f3003ccf37983cc1e7e6007983cfcc1e60f30000b640001e61556,0xf3001e9cc00799e600fa981e61e6798fa9a049cde67980799e711603cfcc003db3000f6cc001e703d95,0x1e60011160003ea6000f30798f301e6f300798f37983cc1e7e6007983cfcc1e60f300012fc0003cc33b6,0x412004240481,0x2000240481,0x412004240481,0x842108240501,0x22000240481,0x2000240481,0x22000240481,0x2000240481,0x842108240501,0x2000240481,0x842108240501,0x2000240481,0x0],
[0x1e600097e000222c00081180020467988119e6222c01e6f301e72fc03cfcc001023000f6cc001e703375,0x0,0x3cc0011160007d4c000fa98007b66799ed99e67d4c03ccf301e6f3003cfcc001f53000f6cc001e707545,0x0,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x0,0x0,0x0,0x7980020460007d4c000f30f31e603cc7d4cf30f3f379803ce04607983cfcc00088b079a22c0007985936,0x12000240481,0x2000240481,0x12000240481,0x42000240481,0x822088240481,0x2000240481,0x822088240481,0x2000240481,0x42000240481,0x2000240481,0x42000240481],
[0x2000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2842 : TreeBound (n := 4) 107 (programCode 0x462b073c5e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf300003cc1e60f30798079800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f30799556,0xf30000b6400088b0000811800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f30799556,0x0,0x108800240481,0xf3079911600016c8811800fa9800f379800f37983cc1e6001ed983cfcc1e60f303cc3cc0f30799556,0x108800240481,0x1e60f3097e00025f8fa9800fa9800f379800f37983cc1e6003d3983cfcc1e60f303cc3cc0f3079b3b6,0x209886240481,0x8800240481,0x209886240481,0x609886240481,0x408800240481,0x408800240481,0x408800240481,0x8800240481,0x0,0x609886240481,0x0,0x0,0xf300012fc00088b0001023001e9cc0079f9800f379f9803ce04607983cfcc0798f3097e3cc07983d1426,0x0,0x111886240481,0x12fc000f33cc00f3f379800fa9800f379800f37983cc1e6001ed983cfcc1e60f303cc3cc0f30799556,0x111886240481,0x222c00079bcc01e6f379800fa9800f379800f37983cc1e6003d3983cfcc1e60f303cc3cc0f30799556,0x211004240481,0x11004240481,0x211004240481,0x411004240481,0x411004240481,0x11004240481],
[0x411004240481,0x411004240481,0x811886240481,0x411004240481,0x811886240481,0x411004240481,0xf3000408c003db30003d39800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f30838cd6,0x0,0x111886240481,0x0,0x111886240481,0x0,0x211004240481,0x11004240481,0x211004240481,0x411004240481,0x411004240481,0x11004240481,0x411004240481,0x411004240481,0x811886240481,0x411004240481,0x811886240481,0x411004240481,0x0,0x131886240481,0xf37980f31e600f379f9800fa9800f379800f37983cc1e6001ed983cfcc1e60f303cc3cc0f307a8856,0x131886240481,0x1e67980f33cc01e67a73001e9cc0079f9800f379801e9cc1f16b983cfcc0798f3097e3cc07983efa26,0x221004240481,0x240481,0x221004240481],
[0x240481,0x400000240481,0x240481,0x400000240481,0x240481,0x800000240481,0x240481,0x800000240481,0x240481,0xf3003cfcc00f3f3003cc79800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f30831356,0xf3001e9cc01e6f3001e679800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f308758d6,0xf3003cfcc1e60f3003cc79800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f30831356,0xf3003cfcc00f3f3003cc79800fa9800f379800f37983cc1e7e6007983cfcc1e60f303cc3cc0f30831356,0x0,0x142841240481,0x4a0a0008118000f301e6003cfcc0079f9800f3f307c5ccc1e7ed983cfcc2d90f30d4a3cc07983cde26,0x142841240481,0x1e6000088b0001e60079800fa9800f379800f37983cc1e6003d3983cfcc1e60f303cc3cc0f30799556,0x24318e240501,0x42000240481,0x24318e240501,0x842108240501,0x442004240481,0x842108240501,0x442004240481,0x42000240481,0x842108240501,0x842108240501,0x842108240501,0x42000240481,0x8020200404002080041048040208060200804104,0x0],
[0x142841240481,0x0,0x142841240481,0x0,0x24318e240501,0x42000240481,0x24318e240501,0x842108240501,0x442004240481,0x842108240501,0x442004240481,0x42000240481,0x842108240501,0x842108240501,0x842108240501,0x42000240481,0x8020200804002080041048040208060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2955 : TreeBound (n := 4) 107 (programCode 0x462b073c5f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x182041240481,0x0,0xfa98003ea601b8e9807981e67988118f3204600f31e603cde72ce73cc003ccf300f3f3003cde703375,0x482004210481,0x1ed98007b6600f37981e601e67987980f3204601e67980799e76c803cc00f33cc03ccf300799e703d95,0x400410040001000000080002000020000814e3,0x482004208481,0x482004200481,0x482004208481,0x0,0x482004210481,0x16c800111600016c83cc000f33cc0f6cc000f37983cc1e7e6007983cc0f4e600f301e60f30798dd8d6,0x482004210481,0x482004210481,0x0,0x0,0x0,0x0,0x182041240481,0x0,0x182041204481,0x0,0x182041204481,0x82000200481,0x82000208481,0x82000200481,0x82000208481,0x82000220481,0x0,0x25f800097e00025f83cc000f3f300f6cc000f37983cc1e7e6007983cc0f4e600f307980f31e6193cd6,0x0],
[0x82000200481,0x82000220481,0x0,0x82000220481,0x0,0x1020001004080000010200000040800042000008100000020020000081000000080080200000800040000802100002000100400021001000084004000010010000040002105b9a8,0x82000240481,0x1ed98007b66000fa981e601e67987980f3204601e67980799e76c803cfcc003db3000f6cc001e703d95,0x401010040001000000080002080022000814e3,0x482004240481,0x0,0x50a045240481,0x0,0x50a045240481,0x0,0x6120ce240481,0x2000240481,0x6120ce240481,0x842108240501,0x422004240481,0x2000240481,0x422004240481,0x2000240481,0x842108240501,0x2000240481,0x842108240501,0x2000240481,0x482004240481,0x82000240481,0x0,0x1e6000811800204600081180025f879888b1e6204601e67981e711603cfcc001023000f6cc001e703375,0x1e67980799e601e60799e601e67987980f320461e607987981e76c803cfcc003db3000f6cc001e703d95],
[0x1e6001ed98007b6600111600044587980f31e63ea607987981e6f3003cfcc003db3000f6cc001e7241f5,0x20400804040101004020080802080022000834e3,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x10004100140001000010080002080022000814e3,0xf3084e4001e6000003cde61e603cc0000f30000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x10008100240001000010080002080022000814e3,0xf307980001e600000001e61e603cc0000f30000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x412004240481,0x2000240481,0x412004240481,0x842108240501,0x22000240481,0x2000240481,0x22000240481,0x2000240481,0x842108240501,0x2000240481,0x842108240501,0x2000240481,0x0],
[0x1e600097e000222c00081180025f879888b1e6204601e7e601e72fc03cfcc001023000f6cc001e703375,0x0,0x1e600097e0007d4c000fa980025f8799f531e6d68601e7e601e72fc03cfcc001023000f6cc001e703375,0x0,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x0,0x1a9484e4001e603cc03cde621393cc0000f30001a9407980000f300003cfcc003db30007d4c001e68a8c5,0x0,0xf307980001e600000001e61e603cc0000f30000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x12000240481,0x2000240481,0x12000240481,0x42000240481,0x822088240481,0x2000240481,0x822088240481,0x2000240481,0x42000240481,0x2000240481,0x42000240481],
[0x2000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3084 : TreeBound (n := 4) 107 (programCode 0x462b073c60) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf307983cc0000f300001e6003cfcc00f3f3000f3f381181e7e6007983cfcc2d900001e600007983cddc6,0x0,0x0,0xf303cc3cc2d90f303cc1e6001ed98007a73000f3f379803ce04607983cc01023000482400088b0799c76,0x4000000110000000440000000300000000c0202000100000000400000000001000004000010010000040000000080000000100002000100008000400004000800010001001087fe27,0xf3003cfcc00f3f307d4cf3000f6cc00f3f3000f37983cc1e7e6007983cc02046001e7e6001ed98465356,0xf307983cc0000f300001e6003cfcc00f3f3000f3f381181e7e6007983d1b22d903cc1e60f307983cddc6,0x0,0xf3004c2cc0130b307e3ff3000f6cc00f3f3000f37983cc1e7e6007983cc1e7e60097fe601e6798465356,0xf3000408c001023079bdb3000f6cc00f3f3000f37983cc1e7e6007983cc0f4e600f31e600f379846ccd6,0x0,0xf3000f6cc003db307a73f3000f6cc00f3f3000f37983cc1e7e6007983cc1e7e600799e601e6798465356,0x0,0x40000000300000000c0000000300000000c00020001000000004000200000020800040000100100000400000000801000001004000001010000004040000008000200010010873227,0x0,0xf300003cc1e60f300000f3001ed98007a73000f379f9803ce04607983ccf30798798d4a0f30f30799766,0x0,0x0,0x0,0x0,0x0,0x60a044341902,0x20a044341902,0x80a0446410a2,0x20a044341902,0x0,0x40a0442410a2,0x40a0442410a2,0x40a0442410a2,0x200000003400400020000400088000000088000002040000020200000080200000080080100000400a202020000002020001004000040010000a00240001000100004000200052ba8],
[0x80a0446410a2,0x0,0x80a0446410a2,0x0,0xf307983cc0000f307981e6003cfcc00f3f3000f3f381181e7e6007983cfcc2d900001e600007983cddc6,0xf307983cc0002d907980f3000f6cc00f3f3000f37983cc1e7e6007983cc005b20003ea600044583cd556,0x0,0xf3000222c1e688b07981e6001ed98007a73000f3f379803ce04607983cc01023000482400088b079d936,0x400000011000000044000000090000000140202000100000000402000000002000004000010010000040000000080000000100002000100008000400008000800010001001087fe67,0xf307983cc00f3f307980f3000f6cc00f3f3000f37983cc1e7e6007983cc02046001e7e6001ed98465356,0x0,0xf307983cc00f3f307980f3000f6cc00f3f3000f37983cc1e7e6007983cc03ea6000f4e6003d398465356,0x0,0xf303cc3cc3528f307980f3001ed98007a73000f379f9803ce04607983cc1e679807a54a00f3f30799766,0x0,0xf303cc3cc2d90f307981e6001ed98007a73000f3f379803ce04607983cc3ccf300f3b6401e6f30799c76,0x0,0x0,0x0,0x0,0xf3000222c00088b0001116001ed98007a73000f3f379803ce04607983cfcc0f30f30b643cc0f3079d936,0xf307983cc003db3000f3f3000f6cc00f3f3000f37983cc1e7e6007983cfcc1e60f301e63cc0798465356,0xf3000408c003db30003db3000f6cc00f3f3000f37983cc1e7e6007983cfcc1e60f301e63cc0798465356,0xf303cc3cc2d90f303cc1e6001ed98007a73000f3f379803ce04607983cfcc0f30f30b643cc0f30799c76,0x0,0x0,0x0,0x0,0x3ccf300f33cc01e67b66001ed98007a73000f3f3001e9cc1ed9f983cfcc0f30f30b643cc0f307bbf36,0x200000240481,0x240481,0x200000240481],
[0x240481,0x400000240481,0x240481,0x400000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0xf300003cc2046f3003ccf3001ed98007a73000f379f9803ce04607983cfcc0798f30d4a3cc0f30799766,0xf3001e9cc01e6f3001e6f3000f6cc00f3f3000f37983cc1e7e6007983cfcc1e60f301e63cc079855fcd6,0x0,0x0,0x0,0x0,0x3cc1e60f4ed981e9cde6001ed98007a73000f3f3001e9cc1ed9f983cfcc0f30f30b643cc0f3079d936,0x220000240481,0x20000240481,0x220000240481,0x20000240481,0x420000240481,0x20000240481,0x420000240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0xf3003cfcc00f3f3003ccf3000f6cc00f3f3000f37983cc1e7e6007983cfcc1e60f301e63cc0798465356,0x0,0x0,0x0],
[0x0,0x408c0012090001e601e6001ed98007a73000f3f3001e9cc1ed9f983cfcc0f30f30b643cc0f30799c76,0x240800240481,0x40000240481,0x240800240481,0x40000240481,0x441004240481,0x40000240481,0x441004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x8020200404002100041048040208060200804104,0x0,0x0,0x0,0x0,0x0,0x240800240481,0x40000240481,0x240800240481,0x40000240481,0x441004240481,0x40000240481,0x441004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481],
[0x8020200804002100041048040208060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_2492 : TreeBound (n := 4) 107 (programCode 0x462b073c) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part101_2493 part101_2574 part101_2655 part101_2736 part101_2737 part101_2738 part101_2739 part101_2740 part101_2741 part101_2742 part101_2743 part101_2744 part101_2745 part101_2842 part101_2955 part101_3084

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3213 : TreeBound (n := 4) 107 (programCode 0x462b073d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x100c028240481,0x80402002080082002020080802080022000814e3,0x100c028240481,0x80402004080102004020080802080022000834e3,0x1014048240481,0x1004008240481,0x1014048240481,0x0,0x80402000100804020120080802080022000814e3,0x0,0x80402000804020400820080802000820020814e3,0x80402000000000400020080802000020400814e3,0x80402000804020400820080802001020040814e3,0x0,0x80402002010080402020080802002020080814e3,0x80402000000000400020080802000020000814e3,0x80402002010080402020080802004020100814e3,0x0,0x80402000000000400020080802008020200814e3,0x80402000000000400020080802000020000814e3,0x80402000000000400020080802010020400814e3,0x80402000000000400020080802000020000814e3,0x80402000000000400020080802020020800814e3,0x0,0x0,0x0,0x80402000201008040220080802080022000815e3,0x0,0x80402000100804800120080802000820020814e3,0x80402000000000800020080802000020400814e3,0x80402000201008800220080802001020040815e3],
[0x0,0x80402004020100804020080802002020080834e3,0x80402000000000800020080802000020000814e3,0x80402004020100804020080802004020100834e3,0x0,0x80402004020100804020080802008020200834e3,0x80402000000000800020080802000020000814e3,0x80402000000000800020080802010020400814e3,0x0,0x0,0x0,0x0,0x0,0x80402000402010080420080802080022000816e3,0x80402000000000000020080802080022000814e3,0x80402000804020100820080802080022000814e3,0x0,0x108428240481,0x110840040022,0x108428240481,0x110840040022,0x210848240481,0x8240481,0x210848240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501],
[0x8240481,0x8040200100804020102008080208002200081ce3,0x80402000000000000020080802080022000814e3,0x80402002010080402020080802080022000814e3,0x80402000000000000020080802080022000814e3,0x80402004020100804020080802080022000834e3,0x0,0x139ce8240481,0x0,0x139ce8240481,0x0,0x2318c8240481,0x8240481,0x2318c8240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0,0x14a128240501,0x80080408040201008020080802080022000854e3,0x14a128240501,0x80100808040201008020080802080022000874e3,0x252148240501,0x842108240501,0x252148240501,0x842108240501],
[0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x0,0x0,0x0,0x0,0x0,0x252948240501,0x8240481,0x252948240501,0x8240481,0x420088240481,0x8240481,0x420088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x1024088240481,0x80402000080002000020080802080022000814e3,0x1024088240481,0x80402000080002000020080802080022000814e3,0x1044108240501,0x0,0x1340c8240481],
[0x12000240800220004c1e0c80408040e00010104,0x1340c8240481,0x408c0010230001f533cc003db3000f6cc00109cc825e6097e01e60f33cc1e688b00012fc0003cc3cb6,0x224088240481,0x4008240481,0x224088240481,0x0,0x1304c8240481,0x0,0x1304c8240481,0x0,0x220888240481,0x8240481,0x220888240481,0x8240481,0x401008240481,0x8240481,0x401008240481,0x8240481,0x802008240481,0x8240481,0x802008240481,0x8240481,0x404008240481,0x102002040800220004466308040807f200102b04,0x404008240481,0x798f301e6f300798f33cc001023000f6cc000f4e60f3007b6601e60f33cc1e60f3012ffcc00f327f356,0x804008240481,0x4008240481,0x804008240481,0x4008240481,0x1044108240501],
[0x0,0x0,0x10c028204481,0x0,0x10c028204481,0x14c128224501,0x15c168208501,0x104008200481,0x15c168208501,0x0,0x0,0x800020080002000020080802080020000814e3,0x0,0x800020080002000020080802080020000814e3,0x14c128220501,0x800020080002000020080802004020000814e3,0x14c128220501,0x104008200481,0x0,0x0,0x0,0x0,0x0,0x0,0xa00028002010080400a01008080406000100e4,0x0,0x0,0x0,0xa0002800801020040884100808044600114ae4,0x0,0xa00028010010400410881008080486002152e4,0x0],
[0x0,0x0,0x0,0x0,0x10c028204481,0x1000040080002000020080802000020400814e3,0x10c028204481,0x14c128224501,0x15c168208501,0x104008200481,0x15c168208501,0x100804028000a000220080802001022000815e3,0x0,0x0,0x0,0x0,0x14c128220501,0x1020044a8012a004a20080802004020d40835e3,0x14c128220501,0x104008200481,0x0,0x94c128204501,0x1e449a9400079126a500003c893528003c8935280003c89359f3594001deb326500077acc99400079126a500077acc9940007735942cb4178000218711aee6b2f735940007aef40a773597b9aca0001dcd653b9ad173597b9acab2d05e00007735a2e6b287735cf9acc15ece9a,0x94c128204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x1e449a9400079126a500003c893528003c8935280003c89359f3594001deb326500077acc99400079126a500077acc9940007735940ee6b2800eea6c2caee6b2f735940007aef40a773597b9aca00ee6b2800003b9acbdcd651e08ffca001dcd650ee6b45cd653b9acc15ece9a,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x254148240501,0x4008240481,0x254148240501,0x0,0x0,0x0,0x0,0x0,0x250948240501,0x8240481,0x250948240501,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0,0x0,0x0,0x0,0x810020508014080502008080208002200083ce3,0x4709c8240501,0x400008240481],
[0x4709c8240501,0x421088240481,0x421088240481,0x400008240481,0x421088240481,0x400008240481,0x462188240501,0x400008240481,0x462188240501,0x400008240481,0x3cde603cc79803cde63cc001023000f6cc000f6cc1e600204603cc1e63cc1e60f3025fbcc01e64c7ed6,0x0,0x0,0x0,0x0,0x0,0x4709c8240501,0x400008240481,0x4709c8240501,0x421088240481,0x421088240481,0x400008240481,0x421088240481,0x400008240481,0x462188240501,0x400008240481,0x462188240501,0x400008240481,0x799e601e67980799e63cc001023000f6cc000f6cc1e6007b6603cc1e63cc1e60f30222fcc00f3465356,0x844108240501,0x4008240481,0x844108240501],
[0x4008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3503 : TreeBound (n := 4) 107 (programCode 0x462b073e71) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008002200044060080408040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3504 : TreeBound (n := 4) 107 (programCode 0x462b073e72) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x140003008002200044060080408040e00010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3505 : TreeBound (n := 4) 107 (programCode 0x462b073e73) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008002200044060080408040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3506 : TreeBound (n := 4) 107 (programCode 0x462b073e74) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x25f800097e00025f83cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f300012fc0003cc33b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3507 : TreeBound (n := 4) 107 (programCode 0x462b073e75) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x20c086240481,0x8180802018002200044060080408040e00010104,0x20c086240481,0xf33cc1e607987981e612fc003db3000f6cc000fa98b641e61e601e60f33cc1e688b00012fc0003cc3cb6,0x214004240481,0x204004240481,0x214004240481,0x0,0x238486240481,0x0,0x238486240481,0x0,0x210804240481,0x200004240481,0x210804240481,0x200004240481,0x221004240481,0x200004240481,0x221004240481,0x200004240481,0x2721ce240501,0x221004240481,0x2721ce240501,0x221004240481,0x224004240481,0x980802010800220004406008040804c200102b04,0x224004240481,0xf3003cc1e60f307983cfcc001023000f6cc000f4e60f31e61e601e60f33cc1e60f307d4fcc00f327f356,0x24410c240501,0x224004240481,0x24410c240501],
[0x2000080080002000010080002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3540 : TreeBound (n := 4) 107 (programCode 0x462b073e76) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40c086240481,0x400808018002200044060080408043200042304,0x40c086240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x14004240481,0x4000240481,0x14004240481,0x0,0x438486240481,0x0,0x438486240481,0x0,0x10804240481,0x240481,0x10804240481,0x240481,0x21000240481,0x240481,0x21000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x24000240481,0x408008108002200044060080408043200042b04,0x24000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x844108240501,0x4000240481,0x844108240501],
[0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3573 : TreeBound (n := 4) 107 (programCode 0x462b073e77) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008002200044060080408040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3574 : TreeBound (n := 4) 107 (programCode 0x462b073e78) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1039c83cc1e600016c80003ea60016c80005d06f3003cc408de6f3003cfcc001f53000f6cc001e703885,0x0,0x2400110000810020420000804000020000804a4,0x2400110000810020420004804100820020904a4,0x0,0x2400110000810020420008804200820040905a4,0x0,0x0,0xfa98002046000fa980003ccf303ccf3003ccf4e60f31e6001e7e64bf1e60f3000f307983cc1e6107c6,0xfa98003ea6000fa980003ccf303ccf3003ccf4e60f31e6001e7e60f3003db3000f307983cc1e610856,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20200000020800000202000000208000500800080400000404000000804000000810002804080004000100000040100008004000001410000a01040000014100000010000879fa8,0x0,0x2400110000810040420000804000020000804a4,0x2400110000810040420004804100820020904a4,0x4200000020800000042000000208000000040020000200400000400800002000804000200080004000100000040100028000008000205000200000080006050000010000841ca8,0x2400110000810040420004804200820040b05a4,0x0,0x0,0xfa98003ea6000fa98000798f301e6f300798f4e60f31e6001e7e60f31e60f3000f307983cc1e610856,0xfa98003ea6000fa98000798f301e6f300798f4e60f31e6001e7e60f3003db3000f307983cc1e610856,0xfa98003ea6000fa98000798f301e6f300798f4e60f31e6001e7e60f30798f3000f3079f9801e610856,0x0,0x2400110000810040420000804000020800804a4],
[0x0,0x4400110001010040420000804000022000804e4,0x0,0x0,0x0,0x0,0x608886240481,0x0,0x608886240481,0x0,0x210804240481,0x200804240481,0x210804240481,0x210804240481,0x220804240481,0x220804240481,0x220804240481,0x220804240481,0x24090c240501,0x220804240481,0x24090c240501,0x230804240481,0x0,0x609086240481,0x2088484404c2,0x609086240481,0x2088484404c2,0x10004240481,0x240481,0x10004240481,0x240481,0x20000240481],
[0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x608886240481,0x2088484404c2,0x608886240481,0x2088484404c2,0x210804240481,0x200804240481,0x210804240481,0x210804240481,0x220804240481,0x220804240481,0x220804240481,0x220804240481,0x24090c240501,0x220804240481,0x24090c240501,0x230804240481,0x0,0x609886240481,0x2088484404c2,0x609886240481,0x2088484404c2,0x10004240481,0x240481,0x10004240481],
[0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40108240501,0x240481,0x40108240501,0x240481,0x1ed98007b66000fa985b9983db3000f379800fa98b734e6001e7e60f33cc2dcdb30007d4c001e611156,0x0,0x609086240481,0x209048640d02,0x609086240481,0x209048640d02,0x10004240481,0x240481,0x10004240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0xfa98002046000fa98079800f30f30f55f800f4e60f31e6001e7e64bf3cc0f30f30007d4c001e6107c6,0x0,0x608086240481,0x209048640d02,0x608086240481],
[0x209048640d02,0x10004240481,0x240481,0x10004240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40108240501,0x240481,0x40108240501,0x240481,0x0,0x1f173303ea6000f3005b9983cc0000f300000fa98b734e600001e60f33cc2dcdb3001704c001e6110c6,0x20a8485414c2,0x0,0x20a8485414c2,0xe12086240481,0x802000240481,0xe12086240481,0x842108240501,0x822004240481,0x802000240481,0x822004240481,0x842108240501,0x842108240501,0x802000240481,0x842108240501,0x842108240501,0xfa98003ea6000fa98079800fa9800f379800f4e60f31e6001e7e60f33cc0f30f30007d4c001e610856,0x0],
[0x1f173307b66000f3005b9983d39800f300000fa98b734e600001e60f33cc2dcdb30007d4c001e611156,0x0,0x10100000040e0200010200000020200060100008180400040100000080004000081000080008000c02010001000010000800400030081000000204000000410000001020086aea8,0x0,0xe12086240481,0x802000240481,0xe12086240481,0x842108240501,0x822004240481,0x802000240481,0x822004240481,0x842108240501,0x842108240501,0x802000240481,0x842108240501,0x842108240501,0xfa98003ea6000fa980f3000f6cc00f3f3000f4e60f31e6001e7e60f33cc0f30f30007d4c001e610856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3751 : TreeBound (n := 4) 107 (programCode 0x462b073e79) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40c086240481,0xc000880018002200044060080408070200402104,0x40c086240481,0x1e60012fc0003ea60012fc001023000f6cc000f4e60f31e61e601e60f33cc1e60f300f33cc03cc1e93b6,0x414004240481,0x404000240481,0x414004240481,0x0,0x438486240481,0x0,0x438486240481,0x0,0x410804240481,0x400000240481,0x410804240481,0x400000240481,0x421000240481,0x400000240481,0x421000240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481,0x424000240481,0xc008080108002200044060080408070200402b04,0x424000240481,0x1e603cfcc00f31e603cfcc001023000f6cc000f4e60f31e61e601e60f33cc1e60f300f33cc03cc27f356,0x444108240501,0x404000240481,0x444108240501],
[0xc020080808002200044060080408070200406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3784 : TreeBound (n := 4) 107 (programCode 0x462b073e7a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x104302004800220004406008040804c200102b04,0x100082001800220004406008040804c200102b04,0x0,0x608486240481,0x1040c2001010200204406008040804c200102b04,0x608486240481,0xf379adccde6003cc00f30f33cc03ccf300798fa98b641e61e601e60f33cc2046f3001e9cc0079a2e236,0x408886240481,0x409086240481,0x408886240481,0x409886240481,0x409086240481,0x409086240481,0x409086240481,0x408086240481,0x50a086240481,0x409886240481,0x50a086240481,0x0,0x3cc00f6cc003cfcc012fc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3001e9cc0079a2d936,0x104002000800220004406008040804c200102b04,0x100202004800220004406008040804c200102b04,0x104c02010800220004406008040804c200102b04,0x0,0x638486240481,0x0,0x638486240481,0x0,0x410804240481,0x240481,0x410804240481],
[0x240481,0x21000240481,0x240481,0x21000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x106002040800220004406008040804c200102b04,0x100802010800220004406008040804c200102b04,0x106002040800220004406008040804c200102b04,0x3cc3cc3cc0f303cc3cfcc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3001e9cc0079ac38d6,0x107302000800220004406008040804c200102b04,0x102002040800220004406008040804c200102b04,0x104002000800220004406008040804c200102b04,0x102002080800220004406008040804c200106b04]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3833 : TreeBound (n := 4) 107 (programCode 0x462b073e7b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40c086240481,0xc000880018002200044060080408070200402104,0x40c086240481,0xf379801e7e600798003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x414004240481,0x404000240481,0x414004240481,0x0,0x438486240481,0x0,0x438486240481,0x0,0x410804240481,0x400000240481,0x410804240481,0x400000240481,0x421000240481,0x400000240481,0x421000240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481,0x424000240481,0xc008080108002200044060080408070200402b04,0x424000240481,0xf379801e7e600798003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x444108240501,0x404000240481,0x444108240501],
[0xc020080808002200044060080408070200406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3866 : TreeBound (n := 4) 107 (programCode 0x462b073e7c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf37aaffcde600798040957e3db30003cc1e60fa98c5707983cc1e60f33cc2139f3003cfcc00f3268f76,0x0,0x0,0x0,0x608886240481,0x409086240481,0x608886240481,0x609886240481,0x409086240481,0x409086240481,0x409086240481,0x8082240481,0xf0a0c7240481,0x609886240481,0xf0a0c7240481,0x0,0x798007b660079f9800b64001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x0,0x0,0x0,0x0,0x0,0x608886240481,0x409086240481,0x608886240481,0x609886240481,0x409086240481,0x409086240481,0x409086240481,0x8082240481],
[0xf0a0c7240481,0x609886240481,0xf0a0c7240481,0x80004000200100000802000002001000080000020200000400800000802000000804000200080004000100000400100008004000004010000100040000040100000100209051da8,0x79800f4e6003d398012fc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f32811b6,0x79f9801e7e600798003cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x79803cde603cc7980408c001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f3286cd6,0x79f9801e60f307983cfcc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x0,0xf300f33cc03cc79807d557e3db30003cc1e60fa98c5707983cc1e60f33cc2139f3003cfcc00f3278276,0x0,0x0,0x0,0x410804240481,0x240481,0x410804240481,0x240481,0x421000240481,0x240481,0x421000240481,0x240481,0x42108240501,0x240481,0x42108240501,0x240481,0x798f301e7e600798f33cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x7981e61e61e607981e9cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f32c38d6,0x798f301e7e600798f33cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x7983cc1e60f307983cfcc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x798f301e603cc798003cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x798f301e6f300798f33cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f327f356,0x0],
[0x0,0x0,0x0,0x0,0x840908240501,0x42108240501,0x840908240501,0x40108240501,0x441108240501,0x42108240501,0x441108240501,0x40108240501,0x42108240501,0x42108240501,0x42108240501,0x40108240501,0x799e601e67980799e63cc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3003cfcc00f364b356]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3947 : TreeBound (n := 4) 107 (programCode 0x462b073e7d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80c0c3240481,0x8000800018002200044060080408040200000104,0x80c0c3240481,0x1e67980799e601e60003cc0000f307983cc1e6000003cc0001e6f3003cfcc001f53000f6cc001e703885,0x814086240481,0x804000240481,0x814086240481,0x0,0x1e67980799e620460007983cde6017491805d24600f6cc003ea6f3f33cfcc001f53000f6cc001e703885,0x0,0x1e67980799e67b66001e60f33cc044d18009a02c03d39800f4e6f4e63cfcc003db3000f6cc001e722395,0x0,0x830886240481,0x800000240481,0x830886240481,0x800000240481,0x821004240481,0x800000240481,0x821004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x824004240481,0xfe0800810800220004406008040807f200042b04,0x824004240481,0x1e63cc9f78f301e63cfcc001023000f6cc000f4e60f31e61e601e60f33cc1e60f3000f6cc003ce7f356,0x844108240501,0x804000240481,0x844108240501],
[0x844108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3980 : TreeBound (n := 4) 107 (programCode 0x462b073e7e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x60c086240481,0x4000880018002200044060080408070200402104,0x60c086240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x414004240481,0x4000240481,0x414004240481,0x0,0x638486240481,0x0,0x638486240481,0x0,0x410804240481,0x240481,0x410804240481,0x240481,0x21000240481,0x240481,0x21000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x24000240481,0x4008080108002200044060080408070200402b04,0x24000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x844108240501,0x4000240481,0x844108240501],
[0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4013 : TreeBound (n := 4) 107 (programCode 0x462b073e7f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80c0c3240481,0x0,0x834086204481,0x824004210481,0x834086204481,0x40001002080002000000080002000020000814e3,0x824004208481,0x824004200481,0x824004208481,0x0,0x824004210481,0x900082001800220004406008040104c020102b04,0x824004210481,0x79800b6400079f9800b64001023000f6cc000f4e60f31e61e601e60f301e7e6007983cc1e60f327f356,0x824004220481,0x824004210481,0x824004220481,0x0,0x80c0c3240481,0x0,0x83c0c7204481,0x0,0x83c0c7204481,0x804000200481,0x804000208481,0x804000200481,0x804000208481,0x0,0x0,0xf30012fc0003db30012fc001023000f6cc000f4e60f31e61e601e60f300f4e600f307980f31e62e3d36,0x0],
[0x798012fc0003d398012fc001023000f6cc000f4e60f31e61e601e60f301e7e6007983cc1e60f32811b6,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x814086240481,0x804000240481,0x814086240481,0x0,0x40001000100880022000080102080022000814e3,0x0,0x40001000201080042000080102080022000814e3,0x0,0x830886240481,0x800000240481,0x830886240481,0x800000240481,0x821004240481,0x800000240481,0x821004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x824004240481,0x0,0x830486240481,0x8108002100102002044060080408040e00010104,0x830486240481,0x1e7e9cc01e6001e7e600798f301e6f300798f4e60f31e61e601e60f33cc1e60f300012fc0003cc33b6,0x820804240481],
[0x800000240481,0x820804240481,0x800000240481,0x801000240481,0x800000240481,0x801000240481,0x800000240481,0x802000240481,0x800000240481,0x802000240481,0x802000240481,0x824004240481,0x0,0x0,0x0,0x0,0x1e9cfcc00f3001e9cc00798f301e6f300798f4e60f31e61e601e60f33cc1e60f300012fc0003cc33b6,0x800800240481,0x800000240481,0x800800240481,0x800000240481,0x821004240481,0x800000240481,0x821004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x844108240501,0x804000240481,0x844108240501],
[0x844108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4110 : TreeBound (n := 4) 107 (programCode 0x462b073e80) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c082204481,0x798d4a1e607983cc1e63cc003db3000f6cc000fa98b641e61e601e60f30012090003ea600044583cde56,0x10c082204481,0x4000180082002000080102000020000814e3,0x7987981e600003cc0003cc003db3000f6cc000fa98b641e61e601e60f33cc2d900001e600007983cde56,0x798c571e603cc3cc0f33cc003db3000f6cc000fa98b641e61e601e60f3007c59001e7e6001ed985b3e56,0x7987981e600003cc0003cc003db3000f6cc000fa98b641e61e601e60f35b22d903cc1e60f307983cde56,0x0,0x7987981e600003cc0003cc003db3000f6cc000fa98b641e61e601e60f35b22d90f301e607987983cde56,0x7980001e60000b640000f30079bcc01e600003cc0001e600f33cfcc001f53000f300001e703885,0x7987981e600003cc0003cc003db3000f6cc000fa98b641e61e601e60f35b22d90f301e607987983cde56,0x0,0x80c0c3220481,0x7987981e600003cc0003cc003db3000f6cc000fa98b641e61e601e60f31e62d907981e607987983cde56,0x80c0c3220481,0xc082200481,0x0,0x0,0x0,0x0,0x0,0x0,0x8088484410a2,0x80a0484410a2,0x8088484410a2,0x0,0x809048641902,0x80a0484410a2,0x809048641902,0x0],
[0x80a0484410a2,0x0,0x80a0484410a2,0x0,0x10c082204481,0x1e6000079800012fc0000f30079bcc01e600007980001e601e63cc00003cc0000f33cc01e703d95,0x10c082204481,0x8000280082002000080102000020000814e3,0xee6b2800003b9ad8e6b281dce536b281dcd73e6b282540be400001dcd6503b9b4135940ee6d04d6503b9b4135940ee6b2800003b9acbdcd65ee6b283b9ad173597b9ad1735941dcd6c735943b9ad173594ee6b45cd650ee6b36e6b36e6b36e6b28ee6b36e765cb24fd99,0x0,0x1e60000799e6012fc0000f30079bcc01e600007983cc1e601e63cc07983cc1e60f303cc1e703d95,0x8000280082002000080102000022000814e3,0x798b641e607983cc3cc3cc003db3000f6cc000fa98b641e61e601e60f35b22d90f301e607987983cde56,0x0,0x798b641e607983cc3cc3cc003db3000f6cc000fa98b641e61e601e60f35b22d90f301e607987983cde56,0x0,0x80c0c3220481,0x8000280082002000080102000020100814e3,0x80c0c3220481,0xc082200481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x7987981e600003cc0003cc003db3000f6cc000fa98b641e61e601e60f33cc2d90f301e63cc07983cde56,0x4000240481,0x20000880002000000080402080022000814e3,0x0,0x0,0x0,0x0,0x0,0x610804240481,0x240481,0x610804240481],
[0x240481,0x421000240481,0x240481,0x421000240481,0x240481,0x42108240501,0x240481,0x42108240501,0x240481,0x0,0x798b641e600003cc0f35b2003db30003cc0000fa98b6407980001e60f33cc3528f301e63cc07983cddf6,0x798b641e607983cc0f3000f33cc03ccf3003ccfa98b641e61e601e60f33cc2d90f301e63cc07983cde56,0x0,0x40001080000000000080002080022000814e3,0x620804240481,0x20000240481,0x620804240481,0x20000240481,0x421000240481,0x20000240481,0x421000240481,0x20000240481,0x822004240481,0x20000240481,0x822004240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x0,0x798b641e600003cc0f35b2003db30003cc0000fa98b6407980001e60f33cc3528f301e63cc07983cddf6,0x0,0x0,0x0],
[0x620804240481,0x20000240481,0x620804240481,0x20000240481,0x421000240481,0x20000240481,0x421000240481,0x20000240481,0x822004240481,0x20000240481,0x822004240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x44108240501,0x4000240481,0x44108240501,0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_3502 : TreeBound (n := 4) 107 (programCode 0x462b073e) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part101_3503 part101_3504 part101_3505 part101_3506 part101_3507 part101_3540 part101_3573 part101_3574 part101_3751 part101_3784 part101_3833 part101_3866 part101_3947 part101_3980 part101_4013 part101_4110

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4224 : TreeBound (n := 4) 107 (programCode 0x462b073f61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100c028240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4225 : TreeBound (n := 4) 107 (programCode 0x462b073f62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10340c8204481,0x1024088210481,0x10340c8204481,0x0,0x1340c8224481,0x402080002000040081002000021000814e3,0x1340c8224481,0x824088220481,0x224088228481,0x2080002000040081002000021000814e3,0x224088228481,0x2002080002000040081002000021000814e3,0x0,0x0,0x0,0x0,0x824088220481,0x2080002000040081002000021000814e3,0x824088220481,0x0,0x1024088208481,0x1024088210481,0x1024088208481,0x0,0xf379805b3e60100c74c001f53079fd4c21d0fe601e7e601e63cc03cc003ccf300f3f6cc3cde703375,0x0,0x1e67981119cc01f167cc001f5307a76cc1ebb5cc03cde601e63cc03cc00799e603ccf6cc001e703885,0x0,0x0,0x0,0x1e679807b66000f379bcc01e6f307983cc20467980799e601e63cc03cc07983cc1e60f6cc001e703d95],
[0x1e60f300d4dcc0000f307983cc21b29e601e7e601e63cc03cc00000f30000f6cc001e703375,0xf4e60222c000798f300b64003db3000f6cc001024eda73001e6000f307987b69cc1e600003cc00001e56,0x0,0x3cc0003cde6007a06cdcc0000f307983cc21b29e601e7e601e63cc03cc0f300f3f300f6ea601e703375,0x0,0x1e60798799e601e6079bcc01e6f307983cc20467980799e601e63cc03cc79803cde600f6cc001e703d95,0x1e600097e0007b66000b64001023000f6cc000f30f3079f99e6000f307983ea6000f3f3003cfcc1e7556,0x1e60001e61e603cc0d4dcc0000f307983cc21b29e601e7e601e63cc03cc79800fa9800f7bf001e703375,0x0,0x1024088210481,0x0,0x1020488218481,0x1021088210481,0x1020488218481,0x1022088210481,0x1020888210481,0x1021088210481,0x1020888210481,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1020088210481,0x1022088210481,0x8000a00014002080049048020101070020402104,0x1022088210481,0x0,0x1024088210481,0x0,0x10304c8224481,0x1021088210481,0x10304c8224481],
[0x0,0x1020888228481,0x1021088210481,0x1020888228481,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1020088200481,0x0,0xf30000b6400088b0000811800fa9800f379800f37983cfcc1e6007983cc1e7e6007a36401e6f30799556,0x0,0x0,0x1024088220481,0x0,0x124088218481,0x424088210481,0x124088218481,0x1002080002000040081002000020000814e3,0x224088210481,0x424088210481,0x224088210481,0x0,0x424088210481,0x100082001800220004c06008040404c080102b04,0x424088210481,0x798007b660079f9800b64001023000f6cc000f4e60f33cc1e601e60f30799e607987d4c7980f327f356,0x824088210481,0x424088210481,0x824088210481,0x0,0x1024088220481],
[0x0,0x0,0x0,0xf300011160001f34dcc0000f307983cc21b29e601e7e601e63cc03cc00000f30000f6cc001e703375,0x3cc0f30f303cc1e60b64001f530007d4c000fa987981e62d903cc1e61e60008118799f530007985936,0x0,0x0,0x7980007b66000f3d4dcc0000f307983cc21b29e601e7e601e63cc03cc79800fa9800f7bf001e703375,0x0,0x0,0x0,0x0,0x0,0x1e60798799e601e6079bcc01e6f307983cc20467980799e601e63cc03cc79803cde600f6cc001e703d95,0x1e600097e0007b66000b64001023000f6cc000f6cc1e60799e603cc1e60f31e603cc4bf0f30f30799556,0x1e60001e61e603cc0d4dcc0000f307983cc21b29e601e7e601e63cc03cc79800fa9800f7bf001e703375,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4338 : TreeBound (n := 4) 107 (programCode 0x462b073f63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100c028240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4339 : TreeBound (n := 4) 107 (programCode 0x462b073f64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x104c128204501,0xf300003cc1e60f303cc3cc0000f307983cc1e607980799e601e63cc03cc00003cc0000f33cc01e703d95,0x104c128204501,0x0,0x14c128224501,0x408080002000040081002000021000814e3,0x14c128224501,0x844108220501,0x254148228501,0x844108220501,0x254148228501,0x2008080002000040081002000021000814e3,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x1044108208501,0x80002008080002000040081002000020000814e3,0x1044108208501,0x0,0x0,0x0,0xf307991167982c9e2fc0002d9079a22c390168601e7e601e63cc03cc003ccf303ccf6cc799e703375,0x0,0x0,0x0,0x1e9cc007b66000f6cc3cc0f30f307983cc2d907980799e601e63cc03cc07983cc1e60f6cc001ee9bd95],
[0x1e60f306a53cc0000f307983cc38f41e601e7e601e63cc03cc00000f30000f6cc001e703375,0x0,0x0,0x0,0x0,0x1e60f30799e601e63cc3cc03ccf307983cc222c7980799e601e63cc03cc79803cde600f6cc001f081d95,0x1e60011160003ea60012fc001023000f6cc000f30f3079f99e6000f307983ea6000f3f3003cfcc1e93b6,0x7983cc1e61e603cc3cc3cc0f30f307983cc2d907980799e601e63cc03cde6003d39800f6cc001ee9bd95,0x7980020460007d4c0012fc001f530007d4c000fa987981edc5ccc1e60f307a73001f164003db3079d936,0x0,0x1048528210501,0x1063188210501,0x1048528210501,0x1042108210501,0x1050948210501,0x1042108210501,0x1050948210501,0x0,0x1061188210501,0x1042108210501,0x1061188210501,0x80002008000000000040081002008020200814e3,0x1042108210501,0x80002008080000000040081002008020200814e3,0x1042108210501,0x0,0x0,0xf303cc3cc2d90f306a50004bf0001a9400075b41e601e7e601e63cc03cc03cc0f30f30fa224c1ee9b375,0x80002008000000400040081002000020000814e3,0xf303cc3cc1e60f303cc0010230004458000a7107980799e601e63cc03cc07983cc1e60f8b2001ee9bd95,0x80002008000001000040081002000020000814e3,0x80012008002010080440081002010020400816e3],
[0x80002008000000000040081002000020000814e3,0x80022008004020100840081002010020400814e3,0x0,0x80002008008000200040081002000020000814e3,0x80002008000000000040081002000020000814e3,0x80002008010000400040081002000020000814e3,0x80002008000000000040081002000020000814e3,0x0,0x4000000010000a000400028001000040004000000014000a0004000280000000a00010000080040000200200001000200001004000000814000002000000010140000010020866ba7,0x80002008040001000040081002000020000814e3,0x0,0x0,0x1048528210501,0x1063188210501,0x1048528210501,0x1042108210501,0x1050948210501,0x1042108210501,0x1050948210501,0x0,0x1061188210501,0x1042108210501,0x1061188210501,0x80002008000000000040081002010020400814e3,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x80002008000800020040081002000020000814e3,0x80002008000000400040081002000020000814e3,0x80002008001000040040081002000020000814e3],
[0x0,0x0,0x80002008000000000040081002000020000814e3,0x0,0x0,0x8004200800804020104008100200802020081ce3,0x80002008000000000040081002000020000814e3,0x80082008010080402040081002010020400814e3,0x80002008000000000040081002000020000814e3,0x0,0x4000000010000a000400028001000040004000000014000a0004000280000000a00010000080040000200200001000200001004000000810000002000000010100000010020866ba7,0x0,0x0,0x0,0x14c128220501,0xc64188220501,0x14c128220501,0x844108220501,0x254148220501,0x844108220501,0x254148220501,0x0,0x464188220501,0x80000008080002000040081002020020800814e3,0x464188220501,0x80000008080002000040081002020020800814e3,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x12fc00077ba4615d53cc0f30f30ebece43afa64601e7e601e63cc03cc03cc0f30f30fa5f48dee9b375],
[0x408080002000040081002000020000814e3,0x408c001023798222c3cc0f30f303ce22c0f381180799e601e63cc03cc07983cc1e60f4ed981ee9bd95,0x844108220501,0x0,0x844108220501,0x0,0x0,0x8000208080002000040081002000020000814e3,0x4000000014000a000400000000000040004000000010000a000400000001000000001000008004000020020000100020000100400000081400000200000001000000001002086aba7,0x10000408080002000040081002000020000814e3,0x4000000010000a000400000000000040004000000010000a000400000001000000001000008004000020020000100020000100400000081400000200000001000000001002086aba7,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x14c128220501,0xc64188220501,0x14c128220501,0x844108220501,0x254148220501,0x844108220501,0x254148220501,0x2008080002000040081002040021000814e3,0x464188220501,0x0,0x464188220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501],
[0x0,0x14c128204501,0x0,0x14c128204501,0x844108220501,0x254148228501,0x844108220501,0x254148228501,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108200501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4516 : TreeBound (n := 4) 107 (programCode 0x462b073f65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1014048240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4517 : TreeBound (n := 4) 107 (programCode 0x462b073f66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1004008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4518 : TreeBound (n := 4) 107 (programCode 0x462b073f67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1014048240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4519 : TreeBound (n := 4) 107 (programCode 0x462b073f68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x804030080006000140081002080022000814e3,0x0,0x4020410080022000840081002000820020814e3,0x410080002000040081002000020400814e3,0x4020410080022000840081002001020040814e3,0x410080002000040081002000021000814e3,0x10080410080082002040081002002020080814e3,0x410080002000040081002000020000814e3,0x10080410080082002040081002004020100814e3,0x0,0x410080002000040081002008020200814e3,0x0,0x410080002000040081002010020400814e3,0x0,0x0,0xf37980f31e600f37d4c001023000f6cc000f4e60f30799e601e60f30799e607980008118001e61556,0x410080002000040081002040021000814e3,0x0,0x100805008000a000240081002080022000815e3,0x0,0x805010080006000140081002000820020814e3,0x3cc1e607987983cc0000f307983cc1e607980799e601e63cc03cc00003cc0000f33cc01e703d95,0x100901008000a000240081002001020040815e3,0x1010080002000040081002000021000814e3,0x40201010080202008040081002002020080854e3,0x1010080002000040081002000020000814e3,0x40201010080202008040081002004020100854e3,0x0,0x0,0x0,0x0],
[0x0,0x40201010080202008040081002020020800854e3,0x1e67980f33cc01e67d4c001f530007d4c000f6cc7980f325f83cc1e60f30007d4c799ed98007985426,0x1010080002000040081002040021000814e3,0x3ccf300f33cc01e67d4c001f530007d4c000fa987981e62d907983cc1e60008118799f530007985936,0x2010090080012000440081002080022000816e3,0x10080002000040081002080022000814e3,0x4020110080022000840081002080022000814e3,0x2010080002000040081002080022000814e3,0x804021008004200104008100208002200081ce3,0x0,0x7384e8240481,0x0,0x7384e8240481,0x0,0x6308c8240481,0x8240481,0x6308c8240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x10080410080082002040081002080022000814e3,0x0,0x0,0x0,0x0],
[0x0,0x850948240501,0x8240481,0x850948240501,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x42108240501,0x8240481,0x42108240501,0x8240481,0x0,0x848528240501,0x0,0x848528240501,0x0,0x850948240501,0x842108240501,0x850948240501,0x842108240501,0x861188240501,0x842108240501,0x861188240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x0,0x7384e8240481],
[0x0,0x7384e8240481,0x0,0x6308c8240481,0x8240481,0x6308c8240481,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x40201010080202008040081002080022000854e3,0x0,0x0,0x0,0x0,0x0,0x850948240501,0x8240481,0x850948240501,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x42108240501,0x8240481,0x42108240501],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4648 : TreeBound (n := 4) 107 (programCode 0x462b073f69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024088240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4649 : TreeBound (n := 4) 107 (programCode 0x462b073f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10304c8240481,0x0,0x1021888204481,0x1001008210481,0x1021888204481,0xf30079bcc01e6f3001e600f33cc03ccf3003cd023445a22c0003cc0f307991167983cc0f307983cc3cb6,0x1001008208481,0x1001008200481,0x1001008208481,0xf3001e9cc01e6f3001e6003ccf303ccf3003ccf300f30b64001e600f3079bea6000fa9f983cc1e610856,0x1001008210481,0x1001008200481,0x1001008210481,0x1001008210481,0x1001008220481,0x8008200100102002048170802014070080402b04,0x1001008220481,0xf3001e9cc01e6f3001e6003ccf303ccf3003ccf300f30b640798000f3088b1e603cc97e0f307984c7ed6,0x10304c8240481,0x0,0x10324c8204481,0x1002008210481,0x10324c8204481,0x0,0x1002008208481,0x1002008200481,0x1002008208481,0xf3003cfcc00f3f3001e600f31e603cc7980799023000f6cd11a4581e60f37b69cc1eda7303cc3cc20276,0x1002008210481,0x1002008200481,0x1002008210481],
[0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080020000100400000100000000404000000800000001001087fea7,0x0,0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x0,0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x1020888240481,0x1000008240481,0x1020888240481,0x0,0x1304c8240481,0x0,0x1304c8240481,0x0,0x220888240481,0x8240481,0x220888240481,0x8240481,0x401008240481,0x8240481,0x401008240481,0x8240481,0x802008240481,0x8240481,0x802008240481,0x8240481,0x1001008240481,0x1000008240481,0x1001008240481,0x1000008240481,0x1002008240481,0x0,0x121888240481],
[0x10800210400208004c060c80408040e00010104,0x121888240481,0x3d39800f4e6001e7e7e6003d39800f37980109c8b6622c0003ea60f33cc1e688b00012fc0003cc3cb6,0x201008240481,0x8240481,0x201008240481,0x8240481,0x400008240481,0x8240481,0x400008240481,0x8240481,0x800008240481,0x8240481,0x800008240481,0x8240481,0x1002008240481,0x0,0x0,0x0,0x0,0x0,0x202008240481,0x8240481,0x202008240481,0x8240481,0x400008240481,0x8240481,0x400008240481,0x8240481,0x802008240481,0x8240481,0x802008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4746 : TreeBound (n := 4) 107 (programCode 0x462b073f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024088240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4747 : TreeBound (n := 4) 107 (programCode 0x462b073f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1008428204481,0x80082000100880022040081002010020400814e3,0x1008428204481,0x80202010000a00028040081002080021000854e3,0x80012008000810020440081002002020080816e3,0x1000408200481,0x80022008000820020840081002004020100814e3,0x80006000100804020140081002080020020814e3,0x10284a8210481,0x80002000000800020040081002004020000814e3,0x10284a8210481,0x1000408200481,0x0,0x80002000000800020040081002080020000814e3,0x80202010000a00028040081002040021000854e3,0x80002000000800020040081002080020000814e3,0x0,0x80222018004220408840081002000820020854e3,0x1021088210481,0x80222018004220408840081002001020040854e3,0x400000001000082004000200010000800040000000104008200000020000080080001000008004000020020000100020000100400000081400000204000001008000001002086aba7,0x1021088208481,0x1021088210481,0x1021088208481,0xf3003cfcc01e6f3003cc00799e601e679803cd023000f6cc983eec1e60f33ea9cc1eda8233cc3cc1fd66,0x1021088210481,0x1021088210481,0x1021088210481,0x1021088210481,0x1021088220481],
[0x0,0x1021088220481,0x0,0x0,0x1008428204481,0x80002000001000040040081002000020400814e3,0x1008428204481,0x0,0x80012008001010040440081002002020080816e3,0x1000408200481,0x80022008001020040840081002004020100814e3,0x0,0x10284a8210481,0x80022008001020040840081002004020400814e3,0x10284a8210481,0x1000408200481,0x0,0x0,0x80202010001200048040081002040021000854e3,0x0,0x0,0xf30000b641e62d907987983cc1e616c8aeadb2204601e7e601e63cc03cc003ccf300f3f3003cde703375,0x80082002001010040480004040200c04020100e4,0xf30000b641e688b079b5283cc1e6445a1b317ed68601e7e601e63cc03cc003ccf303ccf300799e703375,0x0,0x0,0x0,0x0,0xf30079bcc01e6f3003cc00f31e603cc7980799023000f6cd11a4583cc1e67b69cc1eda7303cc3cc20276,0x0,0x0,0x80082002001010040480000040200400040000e4],
[0x0,0x0,0x0,0x0,0x0,0x80202010002200088040081002080022000854e3,0x1000008240481,0x80202010004200108040081002080022000854e3,0x0,0x0,0x0,0x0,0x0,0x250948240501,0x8240481,0x250948240501,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x1021088240481,0x1000008240481,0x1021088240481,0x1000008240481,0x0,0x804030020004800140081002080022000814e3,0x80080404020080802040081002080022000814e3],
[0x1008050020008800240081002080022000815e3,0x80201010020200808040081002080022000854e3,0x252148240501,0x2008240481,0x252148240501,0x842108240501,0x462188240501,0x2008240481,0x462188240501,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0,0x12fc0006a51e61a9479bdb3000fe64d4df99204601e7e601e63cc03cfcc001023000f6cc001ee9b375,0xf6cc00f3f3000f6cc79800fa9800f379800fa983cc3cc00025f83cc3cc1e60f30798b640001e61556,0x408c00120979825f9e67a73001f166419c5981180799e601e63cc03cfcc003db3000f6cc001ee9bd95,0x600020001000000006000000004000000040002000100000000000000000000000002000010008000040010000080020000100400000101000000404000000810000001001087fe67,0x221088240481,0x8240481,0x221088240481,0x8240481,0x400008240481,0x8240481,0x400008240481,0x8240481,0x800008240481,0x8240481,0x800008240481,0x8240481,0x0],
[0x804030040005000140081002080022000814e3,0x0,0x1008050040009000240081002080022000815e3,0x0,0x252148240501,0x2008240481,0x252148240501,0x842108240501,0x462188240501,0x2008240481,0x462188240501,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0,0x0,0x0,0x0,0x0,0x252948240501,0x8240481,0x252948240501,0x8240481,0x400008240481,0x8240481,0x400008240481,0x8240481,0x842108240501,0x8240481,0x842108240501],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4908 : TreeBound (n := 4) 107 (programCode 0x462b073f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1044108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4909 : TreeBound (n := 4) 107 (programCode 0x462b073f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1340c8240481,0x0,0x624088204481,0x404008210481,0x624088204481,0x400080002000040081002000021000814e3,0x404008208481,0x404008200481,0x404008208481,0x0,0x404008210481,0x12000240800220004194c80201104c020100b04,0x404008210481,0x102300102300010233cc001023000f6cc000f300f307b67e60000f307b67e60079fd4c1e60f3099356,0x404008220481,0x404008200481,0x404008220481,0x120002408002200044160802014060900804104,0x1340c8240481,0x0,0x9340c8204481,0x0,0x9340c8204481,0x804008220481,0x804008208481,0x804008200481,0x804008208481,0x0,0x0,0x600020001800000000000000004000000040002000100000000400000001000000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x0],
[0x600020001800000000000000004000000040002000100000000400000001000000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x804008220481,0x804008200481,0x804008220481,0x804008220481,0x224088240481,0x4008240481,0x224088240481,0x1e60f307983cc0000f307983cc1e601e601e7e601e63cc03cfcc001023000f6cc001e703375,0x404008240481,0x0,0x620488240481,0x10200204001020020411c8c20108040e00010104,0x620488240481,0xf33cc03ccf3003ccf3000f33cc03ccf300798f3f74d366097e003cc1e9cc1e688b00012fc0003cc3cb6,0x400808240481,0x8240481,0x400808240481,0x8240481,0x1008240481,0x8240481,0x1008240481,0x8240481,0x2008240481,0x8240481,0x2008240481,0x8240481,0x404008240481,0x0,0x0,0x0,0x0],
[0x0,0x800808240481,0x8240481,0x800808240481,0x8240481,0x401008240481,0x8240481,0x401008240481,0x8240481,0x2008240481,0x8240481,0x2008240481,0x8240481,0x804008240481,0x4008240481,0x804008240481,0x4008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4990 : TreeBound (n := 4) 107 (programCode 0x462b073f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1044108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4991 : TreeBound (n := 4) 107 (programCode 0x462b073f70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c028204481,0x880030080082002040081002010020400814e3,0x10c028204481,0x14c128224501,0x15c168208501,0x104008200481,0x15c168208501,0x0,0x84003008004200104008100200802020081ce3,0x800020080002000040081002080020000814e3,0x880030080082002040081002010020400814e3,0x800020080002000040081002080020000814e3,0x14c128220501,0x800020080002000040081002004020000814e3,0x14c128220501,0x104008200481,0x0,0xf6cc003f9901b926bd4c0f30f30b643cc2dae7e601e7e601e63cc03cc003ccf300f3f3003cdee9b375,0x1e600f37983cc0000f307983cc1e607980799e601e63cc03cc00003cc0000f33cc01e703d95,0x1e9cc007b6600f3b736cc0f30f307983cc2d907980799e601e63cc03cc00f33cc03ccf300799ee9bd95,0x1e600f37983cc0000f307983cc1e607980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x222c00088b00011163cc001f530007d4c000fa987981e6a713cc1e614e288b4458b651160f30799c76],
[0x120002808002200046170804024060c80804104,0x0,0x120002808002200044160804024060900804104,0x0,0x10c028204481,0x1000040080002000040081002000020400814e3,0x10c028204481,0x14c128224501,0x15c168208501,0x104008200481,0x15c168208501,0x100804028000a000240081002001022000815e3,0x104005008004200104008100200802020081ce3,0x0,0x1080050080082002040081002010020400814e3,0x0,0x14c128220501,0x1020048a80022000840081002004020500814e3,0x14c128220501,0x104008200481,0x0,0x94c128204501,0x0,0x94c128204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x0,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x254148240501,0x4008240481,0x254148240501,0x1e60f307983cc0000f307983cc1e601e601e7e601e63cc03cfcc001023000f6cc001e703375,0x0,0x8004210000804020140081002080022000814e3,0x8080210080080402040081002080022000814e3,0x8008210001008040240081002080022000815e3,0x8200209080201008040081002080022000854e3,0x4709c8240501,0x400008240481,0x4709c8240501,0x421088240481,0x421088240481,0x400008240481,0x421088240481,0x400008240481,0x462188240501,0x400008240481,0x462188240501,0x400008240481,0x0,0xf6cc003f9b1c2ae6b9804bf0001a9c1186a7064601e7e601e63cc03cfcc001023000f6cc001ee9b375,0x3cde603cc79803cde60003ccf303ccf3003ccf3f30798005b200f3079bcc1e60f30798b640001e61556,0x1e9cc007a774e2a173301023000409d16088f4d180799e601e63cc03cfcc003db3000f6cc001ee9bd95,0x400020001000000000000000000000000060002000100000000600000000400000002000010008000040010000080020000100400000101000000404000000810000001001087fe67,0xe709c8240501],
[0x8240481,0xe709c8240501,0x8240481,0x1008240481,0x8240481,0x1008240481,0x8240481,0x2008240481,0x8240481,0x2008240481,0x8240481,0x0,0x10004410000804020140081002080022000814e3,0x0,0x10008410001008040240081002080022000815e3,0x0,0x4709c8240501,0x400008240481,0x4709c8240501,0x421088240481,0x421088240481,0x400008240481,0x421088240481,0x400008240481,0x462188240501,0x400008240481,0x462188240501,0x400008240481,0x0,0x0,0x0,0x0],
[0x0,0x840908240501,0x8240481,0x840908240501,0x8240481,0x421088240481,0x8240481,0x421088240481,0x8240481,0x2008240481,0x8240481,0x2008240481,0x8240481,0x844108240501,0x4008240481,0x844108240501,0x4008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_4223 : TreeBound (n := 4) 107 (programCode 0x462b073f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part101_4224 part101_4225 part101_4338 part101_4339 part101_4516 part101_4517 part101_4518 part101_4519 part101_4648 part101_4649 part101_4746 part101_4747 part101_4908 part101_4909 part101_4990 part101_4991

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5137 : TreeBound (n := 4) 107 (programCode 0x462b074071) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c83cc001f53079fd4c1e7e600f4e6003ea6f30f6cc003ccf300f3f3003cde703375,0x16c80005b200016c83cc0000f307983cc1e600f307983cc1e6f3003cc00003cc0000f33cc01e703d95,0x16c80005b200016c83cc003db307983cc1e9cc01ed98007b66f3003cc00f33cc03ccf300799e722395,0x16c80005b200016c83cc0000f307983cc1e6000003cc0001e6f3003cc00001e60000f300001e703885,0x0,0x10c082208481,0x0,0x10c082208481,0x114082208481,0x114082208481,0x221000000801000001000000001000040002100100000100400000001000000004020010000080040000040080000000100002000100008000400010000800010001001887fea7,0x114082208481,0x0,0x0,0x221000000880000001200000001000040002100100000100400000001000000004020010010080040000040080000000100002000100008000400010000800010001001887fea7,0x0,0x220000000880000001200000001000040002100100000100400000001000000004020010010080040000040080000000100002000100008000400010000800010001001887fea7,0x1440c3208481,0x16c83cc1e60f307980f33cc003db3000f6cc000fa98b640f31e603cc1e65b22d907983cc1e60f30799dc6,0x1440c3208481,0x114082208481,0x0,0x10c000200481,0x0,0x10c000200481,0x104000200481,0x114000200481,0x104000200481,0x114000200481,0x0,0x0],
[0xf301e6f301e702301e9cc001023000f6cc000f6cc1e60f31e603cc1e6002046001e7e6001ed984c7ed6,0x0,0x7983ccf300f3fa983cfcc001023000f6cc000f6cc1e60f31e603cc1e6002046001e7e6001ed98465356,0x1440c7218481,0x7980f30f30f316c80f33cc001023000f6cc000f6cc1e60f31e603cc1e6002046001e7e6001ed98d4b556,0x1440c7218481,0x104000200481,0x16c80005b200016c83cc01e6f30811bcc204600f31e603cde6f3f33cc01e60f31e60f303cc1e703375,0x0,0x400010000010000440001008004000100000e4,0xfa98003ea60f3fa980003ccf303ccf3003ccf6cc1e60f3001e9cc1e6003d39800f307983cc1e610856,0x400010040010000440001008004000100000e4,0xfa98003ea60f3fa98000798f301e6f300798f6cc1e60f3001e9cc1e6003d39800f307983cc1e610856,0x0,0x0,0x400010000010000440001008004000100000e4,0x0,0x16c800111600016c800f30000f379800f4e60f6cc3cc3cc1e6f3003cc0f301f56cc0f33cc01e7038e5,0x0,0x400010000011000440001008004000100000e4,0x0,0x0,0x400010020010800440001008004000100000e4,0x0,0x400010040011000440001008004000100000e4,0x0,0x10c004210481,0x0,0x10c004210481,0x0,0x114004210481,0x104004210481],
[0x114004210481,0x0,0x0,0x220000000880000001200000001000040002000100000000400000001000000004200010010800040000400080000000100020000100080000400100000800100001001087fea7,0x0,0x220000000880000001200000001000040002000100000000400000001000000004200010010800040000400080000000100020000100080000400100000800100001001087fea7,0x144045210481,0x16c83cc1e60f307980f33cc003db3000f6cc000fa98b641e61e603cc1e65b22d90f303cc0f30f30799e56,0x144045210481,0x16c83cc1e60f307981e63cc003db3000f6cc000fa98b641e61e603cc1e65b22d90f303cc0f30f30799e56,0x0,0x804020180002000000080002080020000814e3,0x0,0x0,0x3cc000f31e604fbc0012fc001023000f6cc000f6cc1e60f31e603cc1e600f4e600f3003ccf300f6d6d36,0x810020480002000000080002080020000814e3,0x800020080002000000080002080020000814e3,0x820020880002000000080002080020000814e3,0x0,0x0,0x3cc01e601e7e72fc01e9cc001023000f6cc000f6cc1e60f31e603cc1e600f4e600f3003ccf300f7c7ed6,0x0,0x3cc03cc01e6f42fc03cfcc001023000f6cc000f6cc1e60f31e603cc1e600f4e600f3003ccf300f76ccd6,0x900024080022000810080022080020400814e3,0x3cc0f3001f5312fc0f33cc001023000f6cc000f6cc1e60f31e603cc1e600f4e600f3003ccf3010052ed6,0xa00028080022000810080022080020400814e3,0x800020080002000000080002080020000814e3,0x0,0x10c004210481,0x0,0x10c004210481,0x0],
[0x114004210481,0x104004210481,0x114004210481,0x0,0x0,0x220000000880000001200000001000040002000100000000400000001000000004200010010800040000800080000000100020000100080000400100000800200001001087fea7,0x0,0x220000000880000001200000001000040002000100000000400000001000000004200010010800040000800080000000100020000100080000400100000800200001001087fea7,0x144045210481,0x16c83cc1e60f307980f33cc003db3000f6cc000fa98b641e61e603cc1e65b22d90f303cc0f30f30799e56,0x144045210481,0x16c83cc1e60f307981e63cc003db3000f6cc000fa98b641e61e603cc1e65b22d90f303cc0f30f30799e56,0x0,0x804020180002000000080002080020000814e3,0x0,0x0,0x3cc000f379804fbc0012fc001023000f6cc000f6cc1e60f31e603cc1e601e7e6007980f31e603cfed9b6,0x810020480002000000080002080020000814e3,0x800020080002000000080002080020000814e3,0x820020880002000000080002080020000814e3,0x0,0x0,0x3cc01e60799e72fc01e9cc001023000f6cc000f6cc1e60f31e603cc1e601e7e6007980f31e603d0e64d6,0x0,0x3cc03cc0798f42fc03cfcc001023000f6cc000f6cc1e60f31e603cc1e601e7e6007980f31e603d065356,0x900024080022000800080022080020000814e3,0x3cc0f3007a7312fc0f33cc001023000f6cc000f6cc1e60f31e603cc1e601e7e6007980f31e603d969b56,0xa00028080022000800080022080020000814e3,0x800020080002000000080002080020000814e3,0x0,0x10c028220481,0xfa98003ea6000fa9bcc01e6f307983cc20461e607987981e6f3003cc79803cde600f379801e703d95],
[0x10c028220481,0x14c169220501,0x114048220481,0x104008220481,0x114048220481,0x0,0x0,0x220000000880000001200000001000040002000100000000400000001000000006000010018000040004000080000000100200000100800000401000000801000001001087fea7,0x0,0x220000000880000001200000001000040002000100000000400000001000000006000010018000040004000080000000100200000100800000401000000801000001001087fea7,0x144149220501,0xf379803cde600fb154c020553081954c20647e601e67981e711603cc79800f4e600f379801e703375,0x144149220501,0x14c169220501,0x0,0x10c082208481,0xfa98003cc0000fa9bcc0000f307983cc1e6000007980001e6f3003cc03cc3cc0f30f300001e703d95,0x10c082208481,0x800020080002000000080002004020000814e3,0x114086218481,0x800020080002000000080002004020000814e3,0x114086218481,0x0,0x0,0x799e60f31e6f3799e9cc001023000f6cc000f6cc1e60f31e603cc1e60799e6079801e6798079d04ad6,0x0,0x1e63cc1e60f3f4e63cfcc001023000f6cc000f6cc1e60f31e603cc1e60799e6079803cc7980f3465356,0x1441cb228501,0xf379803cde600fb154c01e6f30811bcc204610231e6408de703233cc03cc0f30f30f3408c1e703375,0x1441cb228501,0x800020080002000000080002004020000814e3,0x0],
[0x10c028220481,0xf300003cc0001004dcc0000f307983cc1e603cc01e6f301e72fc03cc79800fa9800f3f3001e703375,0x10c028220481,0x14c169220501,0x114048220481,0x104008220481,0x114048220481,0x0,0xf4e600f4e6000f4e9cc01e6f30811bcc20c091601e6f301e72fc03cc79800fa9800f3f3001e7033d5,0x0,0xf4e6003ea6000f6cfcc01e6f30811bcc20463cc01e6f301e72fc03cc79800fa9800f3f3001e703375,0x0,0x144149220501,0xf379803cde600fb154c001f53079fd4c1e7e9cc01e6f301e72fc03cc79800fa9800f3f3001e703375,0x144149220501,0x14c169220501,0x0,0x10c000200481,0x0,0x10c000200481,0x104000200481,0x114000200481,0x104000200481,0x114000200481,0x0,0x0,0x799e63cc1e6f3799e9cc001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc0798f301e64c7ed6,0x0,0x1e63cc1e60f3f4e63cfcc001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc03ccf300f3465356,0x144041204481,0x1e60f31e60f311160f33cc001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc3cc0f30f3097f556,0x144041204481],
[0x104000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5330 : TreeBound (n := 4) 107 (programCode 0x462b074072) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x400020001000080004000200000c008000000060000000100100000600000001801040000100100000400000040801000001004000001010000004040000008100000010010873227,0x0,0x180448484222,0x180448484222,0x180448400222,0x180448484222,0x0,0x0,0x180448484222,0x0,0xc00030000810020440201008000805000100e4,0x180448610222,0x180448420222,0x180448610222,0x0,0x180448420222,0x0,0x180448420222,0x0,0x180448484222,0x180448484222,0x180048400222,0x180448484222,0x79f9801e7e600f3798000f33cc04458000981cc03d39800f4e6f3003cc01e63cc0798f301e61e722395,0x44580005b200016c82e0983cfcc003cc1e60fa983ce7de07983cc1e60079853887980799e601e61df6,0x180448484222,0x0,0x0,0x600000008800000012000000018000000000020080000400200000800800000808000400020001000080000000200010000040000080800000001000000801000002000151da8,0x0,0xc00030000010400420001008008004400100a4],
[0x0,0x0,0x0,0x0,0x0,0x180448484222,0x180448484222,0x180448400222,0x180448484222,0x0,0x0,0x180448484222,0x0,0x0,0x180448610222,0x180448420222,0x180448610222,0x0,0x180448420222,0x0,0x180448420222,0x0,0x0,0x0,0x0,0x0,0x100048440222,0x110848440222,0x0,0x110848440222,0x800028000010000440001008080006000100e4,0xf4e600f4e6000f4e600000f3f300f33cc00f6cc1e60f300003cc1e63cc0000f3000222c0007985216],
[0x800028000010000440001008080006000100e4,0x880022010010480440281008080006002152e4,0x0,0x0,0x0,0x0,0x180848440222,0x0,0x180448484222,0x180448484222,0x180448400222,0x180448484222,0x79f9801e7e600f379800799e601ed98003ec4601e67980799e6f3003cc01e63cc0798f301e61e703d95,0x0,0x180448484222,0x0,0xc00030000810020440201008000805000100e4,0x180448610222,0x180448420222,0x180448610222,0x0,0x180448420222,0x0,0x180448420222,0x180848440222,0x0,0x44580005b200016c85b32ffdb30003db3000fa98b667de000222c1e63cd4e297e0f307983cc1e61df6,0x44580005b200016c85b2f33db30003db3000fa98b66046000222c1e60011167980f307983cc1e61df6,0x44580005b200016c85b2f33db30003db3000fa98b66046000222c1e63cc1e679800007980001e61df6,0x44580005b200016c85b2f33db30003db3000fa98b66046000222c1e60011167983cc07987985b23c56,0x4020000050080000080200000a0080000100000000100000001002000001008000010000801010000800100010010100010000100008000100008001000100001000100208683a7,0x0],
[0x44580005b200016c85b2f33db30003db3000fa98b66046000222c1e63cd1167980f307983cc1e61df6,0x44580005b200016c85ba8b3db30003db3000fa98b75346000222c1e6007c5d459e60079bcc204710f6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x109048640b02,0x0,0x109048640b02,0x111048640b02,0x111048640b02,0x129048640b02,0x111048640b02,0x171048640b02,0x121048640b02,0x161048640b02,0x121048640b02,0x179048640b02,0x141048640b02,0x0,0x141048640b02,0x0,0x182448484222,0x182448484222,0x182448480222,0x182448484222],
[0x79f9801e7e600f379803cc0000f379801e7e600f307983cc1e6f3003cc01e63cc0798f301e61e703d95,0x0,0x182448484222,0x44580005b200016c81f2573cc00f33db3000fa983e4cc6000222c1e6007a77459e60079bcc204710f6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x109048640b02,0x0,0x109048640b02,0x111048640b02,0x111048640b02,0x129048640b02,0x111048640b02,0x171048640b02,0x121048640b02,0x161048640b02,0x121048640b02,0x179048640b02,0x141048640b02,0x0,0x141048640b02,0x0,0x40000000300000000c000000020c0000008400200001000000084002000010008000c0000100100000400040000801000001004000001010000004040000008100000010010873227,0x0],
[0x0,0x0,0x44580003cc0000f303cd2ffcc00f33cc0000fa98b641e600003cc1e63cc1e688b0000b640001e61df6,0x0,0x400000101000000404000000800c000010040020000100000100400200401000801040000100100000400040000801100001004000001010000004040000008100000010010873227,0x400020001000006004000238000c0008000400200001000080004002200010008800400001001000004000400008011c0001004000001010000004040000008100000010050873227,0x48265f83cc00011165b32ffcc00f33cc0000fa98b6604600003cc1e63cc1e688b0000b640001e61df6,0x3d398003d39800f4e9d4c7fcc00f33cc1e60fa98b641e607983cc1e63cc1e688b0000b640001e61df6,0x4825e603cc00011165b32ffcc00f33cc0000fa98b6604600003cc1e63cc1e688b0000b640001e61df6,0x404000008020000004080000010100002000021000100400000400200090000808000400040008000100004000200010004000200010000000440000000300000000800052e28,0x400002001000008004000020000c0008000400200001000080004002200010008800400001001000004000400008000c0001004000001010000004040000008100000010050873227,0x0,0x400010001000040004000080000c001000040020000100010000400200001000900040000100100000400040000801000001004000001010000004040000008100000010390873227,0x0,0x0,0x182048484222,0x182048484222,0x182048480222,0x182048484222,0x0,0x0,0x182048484222,0xc00030020010800420005008102004100904a4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x40000000300000000c000000020c000000a000200008000000090002000020008000c0000100100000400200000801000001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x44580003cc0000f303cc003db30003cc0000fa98b641e600003cc1e63cc1e688b0000b640001e61df6,0x0,0x0,0x0,0x0,0x3d398003d39800f4e9cc003db30003cc0000fa98b641e600003cc1e63cc1e688b0000b640001e61df6,0x0,0x0,0x400002001000008004000020000c0008002000200008000080010002200020008800400001001000004002000008000c0001004000001010000004040000008100000010050873227,0x0,0x400010001000040004000080000c001000200020000800040001000200002000c00040000100100000400200000801000001004000001010000004040000008100000010210873227,0x0,0x0,0x182048484222,0x182048484222,0x182048480222,0x182048484222,0x79f9801e7e6016cf9800000000007983cc1e6000003cc0001e6f3003cc01e61e60798f301e61e703885,0x0,0x182048484222,0xc00030020011000420005008102004100904a4,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5555 : TreeBound (n := 4) 107 (programCode 0x462b074073) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600025f83cc001f53079fd4c1e7e600f4e6003ea6f30f6cc003ccf300f3f3003cde703375,0x445800111600025f83cc0000f307983cc1e6000007980001e6f3003cc00003cc0000f33cc01e703d95,0x25f800111600025f83cc001f5307a76cc1ebb201e9cc00f4e6f3003cc00799e603ccf300799e703885,0x25f800111600025f83cc0000f307983cc1e6000003cc0001e6f3003cc00001e60000f300001e703885,0x0,0x10c082208481,0x0,0x10c082208481,0x114082208481,0x114082208481,0x6000000818000002020000008180000008400000081000000204000000810000000808002000080004000080020000200010000010300010040c0000010100000040400020105b9a8,0x114082208481,0x0,0x0,0x0,0x0,0x0,0x1440c3208481,0x221500000201000000800400002000040002140100000100400000401000001004020010000040010000100040000000100002000100008000100010000400010001000887dda7,0x1440c3208481,0x114082208481,0x0,0x10c000200481,0x0,0x10c000200481,0x104000200481,0x114000200481,0x104000200481,0x114000200481,0x0,0x0],
[0x445800097e0001e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x0,0x445800097e0001e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x1440c7218481,0x451d700799e601e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x1440c7218481,0x104000200481,0x445800111600025f83cc01e6f307983cc204601e67980799e6f3003cc07983cc1e60f303cc1e703d95,0x0,0x0,0x0,0x1008040280002000000080002000022000814e3,0x445800097e0001e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007d4c001e68a8c5,0x1010040480002000000080002000022000814e3,0x1000040080002000000080002000022000814e3,0x1020040880002000000080002000022000814e3,0x0,0x0,0x445800097e0001e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007d4c001e68a8c5,0x0,0x445800097e0001e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007d4c001e68a8c5,0x1100044080022000800080042000022000814e3,0x451d700799e601e603cc1e60f300003cc0000f3007980000f300003cfcc003cc00007d4c001e68a8c5,0x1200048080022000800080042000022000814e3,0x1000040080002000000080002000022000814e3,0x16c800111600025f83cc0000f307983cc1e60f6cc1e63cc1e6f6cc3cc0f300f3f300f30f301e7033d5,0x0,0x400010002010000440201008008000200000e4,0xc00210000810020440041008008004200100e4,0x80048410022,0x1400210001010040440041008008008200201e4,0x0],
[0x0,0x80048410022,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16c800111600025f83cc0000f307983cc1e6003cc1e63cc1e6fa983cc0f300f3f300f31e601e703375,0x0,0x0,0xc00410000810020440081008010004400100e4,0x80048410022,0x1400410001010040440081008010008400201e4,0x0,0x0,0x80048410022,0x0,0x0,0x0,0x400010000011000440001008010000400000e4,0x0,0x445800111600025f8079803cde67980799e9cc01ed98007b66f3003cc0079bcc01e6f6cc799e722395,0x0,0x25f800111600025f80f3001ed987a73f31ebb201e9cc00f4e6f3003cc00799e603ccf6cd6c9e703885,0x0,0x0,0x10c028220481,0x3d39800f4e6001ed9bcc01e6f307983cc20461e607987981e6f3003cc79803cde600f379801e703d95],
[0x10c028220481,0x14c169220501,0x114048220481,0x104008220481,0x114048220481,0x0,0x0,0x220000000800000000a00000002000040002000100000000400000001000000006000010010000040010000040000000100200000100800000401000000401000001000887fda7,0x0,0x220000000800000000a00000002000040002000100000000400000001000000006000010010000040010000040000000100200000100800000401000000401000001000887fda7,0x144149220501,0x3ccf300f33cc01ed9bcc01e6f30811bcc20461e607987981e711603cc79803cde600f379801e703d95,0x144149220501,0x14c169220501,0x445800111600025f83cc01e6f307983cc204601e67980799e6f3003cc07983cc1e60f6cc001e703d95,0x0,0x10c028220481,0xf30000f300001f34dcc0000f307983cc21b29e601e7e601e72fc03cc79800fa9800f3f3001e703375,0x10c028220481,0x14c169220501,0x114048220481,0x104008220481,0x114048220481,0xf30799116d4a25f92fc0002d9079b8f41e6d68601e7e601e7c7a03cc79800fa9800f3f3001e703375,0xf30b640001e600001e63cc003db3000f6cc000fa98b640f31e603cc1e63cc1e600000000000000001dc6,0x0,0x3d39800f4e6001e9cfcc01e6f307983cc20467980799e601e6f3003cde6003d39800f3f3001e703d95,0x0,0x144149220501,0x1e67980f33cc026c544c001f5307af04c1ebb5cc03cde601e7a9403ccf3001ed9800f3f3001e703885,0x144149220501,0x14c169220501],
[0x16c800111600025f83cc0000f307983cc1e6000001e60001e6f3003cc00000f30000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5684 : TreeBound (n := 4) 107 (programCode 0x462b074074) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x445800111600025f83cc001f530007d4c000fa987981e62d903cc1e63cc00088b079a22c0007985936]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5685 : TreeBound (n := 4) 107 (programCode 0x462b074075) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x20c041204481,0x20c004210481,0x20c041204481,0x20c000200481,0x20c082208481,0x20c000200481,0x20c082208481,0x0,0x20c004210481,0x2004080180002000000080002080020000814e3,0x20c004210481,0x2004080180002000000080002080020000814e3,0x20c028220481,0x20c086218481,0x20c028220481,0x20c000200481,0x0,0x4002000100000000080010000800040000c0020010000000008400000080000000082000300002000100020000000020001000400020011000000004000000090000000200017d3a8,0x0,0x0,0x0,0x0,0x108848440222,0x0,0x108848440222,0x0,0x309048640f02,0x0,0x309048640f02,0x0],
[0x0,0x0,0x0,0x0,0x20c041204481,0x20c004210481,0x20c041204481,0x20c000200481,0x20c082208481,0x20c000200481,0x20c082208481,0x2008080280002000000080002000022000814e3,0x20c004210481,0x0,0x20c004210481,0x0,0x20c028220481,0x20c086218481,0x20c028220481,0x20c000200481,0xf30000f307983cc1e612fc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f300012fc0003cc33b6,0x214000240481,0x204000240481,0x214000240481,0x0,0x0,0x0,0x0,0x0,0x210800240481,0x200000240481,0x210800240481],
[0x200000240481,0x221004240481,0x200000240481,0x221004240481,0x200000240481,0x252082240481,0x221004240481,0x252082240481,0x200000240481,0x0,0x220441240481,0x2040081080000400010080402080022000814e3,0x220441240481,0x2040081080000000000080002080022000814e3,0x220882240481,0x220000240481,0x220882240481,0x220000240481,0x221004240481,0x220000240481,0x221004240481,0x220000240481,0x222088240481,0x221004240481,0x222088240481,0x220000240481,0xf3001e63cc1e60f301e9cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x0,0x220441240481,0x0,0x220441240481,0x0],
[0x220882240481,0x220000240481,0x220882240481,0x220000240481,0x221004240481,0x220000240481,0x221004240481,0x220000240481,0x222088240481,0x221004240481,0x222088240481,0x220000240481,0xf3003cc1e60f307983cfcc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x244082240481,0xf300f31e60f307980f33cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f303cc3cc0f3097f556,0x244082240481,0x204000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5798 : TreeBound (n := 4) 107 (programCode 0x462b074076) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x20c041204481,0xc004210481,0x20c041204481,0xc000200481,0x0,0xc000200481,0x0,0x0,0xc004210481,0x4000180002000000080002080020000814e3,0xc004210481,0x4000180002000000080002080020000814e3,0x10c028220481,0x0,0x10c028220481,0xc000200481,0x0,0x20000100080000400100000800100000e8330010020000040400000080200000082000341802000100020000008020001000400034181000010004000000810000002008117dfa8,0x0,0xf5e14e403ea6000f33cc0111bb201e67980799f535b9980000f3001e9cfcc003db30007d4c001e68a8c5,0x0,0x0,0x2088484404c2,0x2088484404c2,0x2088484404c2,0x1e601e61e601e67980e47adfcc00f33db3000fa98d5d1a6000f6cc1e63cc3574e3000408c07a76d5776,0x209048640d02,0x20a8485414c2,0x209048640d02,0x20a8485414c2],
[0x20a0485414c2,0x0,0x20a0485414c2,0x0,0x20c041204481,0xc004210481,0x20c041204481,0xc000200481,0x0,0xc000200481,0x0,0x8000280002000000080002000022000814e3,0xc004210481,0x0,0xc004210481,0x0,0x10c028220481,0x8000280002000000080002000020100814e3,0x10c028220481,0xc000200481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x14000240481,0x4000240481,0x14000240481,0x0,0x0,0x0,0x0,0x0,0x10800240481,0x240481,0x10800240481],
[0x240481,0x21004240481,0x240481,0x21004240481,0x240481,0x42000240481,0x240481,0x42000240481,0x240481,0x0,0x220441240481,0x40001080000400000080402080022000814e3,0x220441240481,0x40001080000000000080002080022000814e3,0x420882240481,0x20000240481,0x420882240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422088240481,0x20000240481,0x422088240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x0,0x220441240481,0x0,0x220441240481,0x0],
[0x420882240481,0x20000240481,0x420882240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422088240481,0x20000240481,0x422088240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x44000240481,0x4000240481,0x44000240481,0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5911 : TreeBound (n := 4) 107 (programCode 0x462b074077) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8118007b66000fa983cc0000f307983cc1e6000001e60001e6f3003cfcc001023000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5912 : TreeBound (n := 4) 107 (programCode 0x462b074078) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x4400110000010000440001008000020000804e4,0x0,0x0,0x0,0x0,0x400220000000880004000200000004800000022000000080000000120000000180004000010010000040000000080100000100400000100000000404000000810000001001087fea7,0x4400110000010000440001008004020100804e4,0x4400110000010000440001008004020100804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4400110000810020440001008000020000804e4,0x4400110000810020440005008000820020904e4,0x0,0x4400110000810020440009008001020040a05e4,0x0,0x0,0x0,0xfa98007b66000fa98000799e601e679803ccf6cc00f4e60f8b5cc1e6003cc1e61ebc8c83cc3cc1fd66,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x16c83cc1e600062b8000799e60445800097ff53003cc003ea6f3003cc003cde600f3f3003cde703885,0x20001000e800040002000000088000000080000000480000002200000002800040000040106000200000001001000001000000000410600002000000010008000010020852ba7,0x0,0x1ed98003ea6000fa982e5d0bcc01e6f3f3000fa985cbb03002268c1e60010a2e841e67980799e612f26,0x0,0x400220000000880004000200000004800000022000000080000000120000000280004000010010000040000000080100000100400000100000000404000000810000001001087fea7,0x1ed98003ea6000fa982e4643cfcc00f3f3000fa985c8d73001e9cc1e62e47b2320f307983cc1e6110c6,0x1ed98003ea6000fa982e4643cfcc00f3f3000fa985c8d73001e9cc1e6007af2320f307983cc1e6110c6,0x0,0x8200010eee80004000200000008800000008100000048770000220000000280004000004010eee0200000801001000001000008000410ee0002000200010108000010020852ba7,0x0,0x7983cc1e600062b8000798000445800097e0f3003cc0001e6f3003cc00001e60000f6cc001e703885,0x0,0x0,0x0,0x0,0x0,0x4400110001010040440001008000020000804e4,0x4400110001010040440005008000820020904e4,0x0,0x4400110001010040440009008001020040a05e4,0x0,0x0,0x1ed98007b66000fa98000f31e603cc7980798fa9800f4e60f6cfcc1e6007983d3b69db307983cc20276,0x1ed98007b66000fa98000f31e603cc7980798fa9800f4e60f6cfcc1e6007983cc1e9db303cc3cc20276,0x1ed98007b66000fa98000f31e603cc7980798fa9800f4e60f6cfcc1e6007983d3b69db3f3003cc20276,0x0,0x4400110001010040440001008000021000804e4],
[0x0,0x4400110001010040440001008000022000804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x210800240481,0x200800240481,0x210800240481,0x210800240481,0x220882240481,0x220882240481,0x220882240481,0x200800240481,0x240882240481,0x220882240481,0x240882240481,0x200800240481,0x0,0x0,0x2088484404c2,0x0,0x2088484404c2,0x10000240481,0x240481,0x10000240481,0x240481,0x20000240481],
[0x240481,0x20000240481,0x240481,0x40000240481,0x240481,0x40000240481,0x240481,0x0,0x0,0x2088484404c2,0x0,0x2088484404c2,0x210800240481,0x200800240481,0x210800240481,0x210800240481,0x220882240481,0x220882240481,0x220882240481,0x200800240481,0x240882240481,0x220882240481,0x240882240481,0x200800240481,0x0,0x0,0x2088484404c2,0x0,0x2088484404c2,0x10000240481,0x240481,0x10000240481],
[0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40000240481,0x240481,0x40000240481,0x240481,0x0,0x0,0x0,0x0,0x0,0x411004240481,0x401004240481,0x411004240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441004240481,0x401004240481,0x441004240481,0x421004240481,0x0,0x0,0x209048640d02,0x0,0x209048640d02,0x10000240481],
[0x240481,0x10000240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40000240481,0x240481,0x40000240481,0x240481,0x0,0x0,0x20a8485414c2,0x0,0x20a8485414c2,0x411004240481,0x401004240481,0x411004240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441004240481,0x401004240481,0x441004240481,0x421004240481,0x0,0x0,0x209048640d02,0x0],
[0x209048640d02,0x10000240481,0x240481,0x10000240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40000240481,0x240481,0x40000240481,0x240481,0x0,0x1e6000b64000204600081180020467980799e62d9003cc7981e6f3003cfcc001f53000f6cc001e703885,0x20a8485414c2,0x0,0x20a8485414c2,0x812048240481,0x802008240481,0x812048240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0xfa98007b66000fa980f3001e9cc0079f9800f6cc00f4e60f8b5cc1e63cc001f5305c904c003cc1fd66,0x200016000800040002000080008000080000000400080002000200002000800040000040160000200000001001000001004000000410000002040000010100000010020852ba7],
[0x1ed98007b66000fa981e6001ed98007a73000fa9800f4e60f6cfcc1e63cc003db303db6cc003cc20276]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6137 : TreeBound (n := 4) 107 (programCode 0x462b074079) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x3d39800f4e6003d3980003cde6016cf9805b3e600f4e6003ea6f30f6cfcc001023000f6cc001e703375,0x3d39800f4e6003d3983cc0000f3079803cde600f307983cc1e6f3003cfcc003db3000f6cc001e703d95,0x3d39800f4e6003d398000f33cc04458000981cc01ed98007b66f3003cfcc003db3000f6cc001e722395,0x3d39800f4e6003d3983cc0000f307980001e6000003cc0001e6f3003cfcc001f53000f6cc001e703885,0x0,0x0,0x0,0x0,0x16c8001e60000408c0012fcf33cc01e6f300798fa98b640f31e603cc1e63cc2d90f300003cc0000001dc6,0x410882240481,0x420882240481,0x410882240481,0x410882240481,0x420882240481,0x420882240481,0x420882240481,0x410882240481,0x440886240481,0x420882240481,0x440886240481,0x410882240481,0x0,0x0,0x8088484410a2,0x0,0x8088484410a2,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481],
[0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x401010000010000440001008080002000000e4,0x0,0x0,0x8088484410a2,0x0,0x8088484410a2,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x0,0x0,0x0,0x0,0x3cc2046f307d4c000f30f31ed9bcc7a73000fa9879a0460f37d4c1e63cc00088b0b6622c0f3811d936,0x411004240481,0x401004240481],
[0x411004240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441004240481,0x401004240481,0x441004240481,0x421004240481,0x0,0x0,0xe09048641d02,0x0,0xe09048641d02,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x0,0x0,0x0,0x0,0x20021000080084000100200000100010002002000008000000010000000020000004200010010800040000800080004000100400000101000000404000000810000001001087fea7],
[0x411004240481,0x401004240481,0x411004240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441004240481,0x401004240481,0x441004240481,0x421004240481,0x0,0x0,0xe09048641d02,0x0,0xe09048641d02,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x0,0x3cc007a73001e9cc0081180020467988119e6204601e67981e711603cfcc001023000f6cc001e703375,0x3d39800f4e6003cc7987981e61e6811879a0461e607987981e711603cfcc003db3000f6cc001e703d95],
[0x3cc01e6f30079bcc00fa98003ea67980799e63ea607987981e6f3003cfcc003db3000f6cc001e7241f5,0x3d39800f4e6003ccf307983cc1e688b079a22c1e603cc7981e6f6cc3cfcc001f53000f6cc001e8e9885,0x412048240481,0x402008240481,0x412048240481,0x46218c240501,0x422088240481,0x402008240481,0x422088240481,0x46218c240501,0x44210c240501,0x402008240481,0x44210c240501,0x46218c240501,0x0,0x401000020010800440201008080002000000e4,0x805000120010800440201008080006000100e4,0x401000020010800440201008080002000000e4,0x100900022001080044020100808000a000201e4,0x411004240481,0x400000240481,0x411004240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x44210c240501,0x400000240481,0x44210c240501,0x400000240481,0x0],
[0x3cc007a73001e9cc0081180025f879888b1e6222c01e6f301e72fc03cfcc001023000f6cc001e703375,0x0,0x3cc00f3f30079bcc010230008118799f531e67d4c03ccf301e6f3003cfcc001f53000f6cc001e707545,0x0,0x412048240481,0x402008240481,0x412048240481,0x46218c240501,0x422088240481,0x402008240481,0x422088240481,0x46218c240501,0x44210c240501,0x402008240481,0x44210c240501,0x46218c240501,0x0,0x0,0x0,0x0,0x3cc2046f307d4c001116001ed98007a73000fa980020460f37d4c1e63cc00088b0b6622c0f3811d936,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x441004240481,0x400000240481,0x441004240481],
[0x400000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6330 : TreeBound (n := 4) 107 (programCode 0x462b07407a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x4000000110000000440000000800000000c0002000100000000400000001000000004200010010800040000000080004000100420000100080000400000000800400001001087fea7,0x0,0x3cc03cfcc1e603d39c08c001023000f6cc000f6cc1e60f31e603cc1e600097e0001ed98007b664c7ed6,0x0,0x3cc03cfcc79803d39c08c001023000f6cc000f6cc1e60f31e603cc1e6002046001e679801e7e64c7ed6,0x4200000110000000440000000200000000c0002100100000000400000801000002004020010010000040000000080000200100002000100008000400010000800020001001087fe27,0x0,0x4000000110000000440000000200000000c0002000100000000400000001000000004200010010000040000000080001000100020000100080000400040000800100001001087fe27,0x3cc03cfcc00f33d39c08c001023000f6cc000f6cc1e60f31e603cc1e600f4e600f307980f31e64c7ed6,0x4000000110000000440000000200000000c0002000100000000400000001000000004200010010000040000000080002000100020000100080000400100000800200001001087fe27,0x3cc03cfcc03cc3d39c08c001023000f6cc000f6cc1e60f31e603cc1e601e7e6007987981e61e64e64d6,0x4020000110000000440000000200200000c000200110000000040000000300000000e000010010000040000000080010000100200000100800000400400000801000001001087fe27,0x4200000110000000440000000200000000c0002100100000000400000801000002004220010010000040000000080000200100422000101000000400000000800020001001087fe27,0x4020000110000000440000000200200000c000200110000000040000000300000000e000010010000040000000080020000100200000100800000401000000802000001001087fe27,0x3cc03cfcc00003d39c08c001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc0798f301e64c7ed6,0x0,0xf3001e6f3001e9cc00b6b983db30003cc1e60fa98b641e607983cc1e63cc2046f3001e9cc0079c12376,0x0,0x10bb64e403ea6007983cc0111bb201e67980799f535b998007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x0,0x408848440902,0x409048640902,0x408848440902,0x79800f3f3001e9cc00e6d2c5edd5b33db3000fa98da5b7e0fa9bcc1e63cc00f3f30da5d640904c8b9c6,0x409048640902,0x40b048641902,0x409048640902,0x40b848741d02],
[0x40a048641902,0x0,0x40a048641902,0x0,0x0,0x3d39803cc001e9d3983cc001023000f6cc000f6cc1e60f31e603cc1e60005b20003d398003ea64c7ed6,0x0,0x3d39803cc003cfd3983cc001023000f6cc000f6cc1e60f31e603cc1e600097e0001ed98007b664c9d36,0x0,0x3d39803cc79803d3983cc001023000f6cc000f6cc1e60f31e603cc1e6002046001e679801e7e64c7ed6,0x0,0x3d39803cc79803d3983cc001023000f6cc000f6cc1e60f31e603cc1e6003ea6000f379803cde64c7ed6,0x400000011000000044000000080000000140002000100000000400000001000000004200010010800040000000080004000100020000100080000400100000800100001001087fea7,0x0,0x400000011000000044000000080000000140002000100000000400000001000000004200010010800040000000080004000100020000100080000400100000800200001001087fea7,0x0,0x0,0x3d39803cc07983d3983cc001023000f6cc000f6cc1e60f31e603cc1e60799e6079807987981e6504ad6,0x0,0x3d39803cc1e603d3983cc001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc0798f301e64c7ed6,0x3cc00f6cc003cfcc012fc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c9d36,0x3d39803cc00003cc003cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x3cc03cfcc03cc3cc0408c001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64e64d6,0x3d39803cc1e603cc79bcc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x240481,0x410882240481],
[0x240481,0x21004240481,0x240481,0x21004240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x620441240481,0x400001001000004000000008000000008042002000108000000400000000040000004200010010800040000000080004000100400000101000000404000000810000001001087fea7,0x620441240481,0x3cde603cc1e603cde6000798f301e6f300798f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x420882240481,0x20000240481,0x420882240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422088240481,0x20000240481,0x422088240481,0x20000240481,0x3cc1e63cc1e603cc1e9cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x0,0x620441240481,0x0,0x620441240481,0x0],
[0x420882240481,0x20000240481,0x420882240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422088240481,0x20000240481,0x422088240481,0x20000240481,0x3cc3cc3cc0f303cc3cfcc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e655fcd6,0x3cde603cc00f33cdea08c001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x3ccf303ccf3003ccf33cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e6e45ed6,0x0,0x6404c7240481,0x3d39803cc001e9d3980003ccf303ccf3003ccf6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6,0x6404c7240481,0x3d39803cc003cfd398000798f301e6f300798f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c9d36,0x440886240481,0x40000240481,0x440886240481,0x40000240481,0x41000240481,0x40000240481,0x41000240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481],
[0x3cde603cc79803cde63cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f30079bcc01e64c7ed6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6459 : TreeBound (n := 4) 107 (programCode 0x462b07407b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x3d39803cde60079f980003cde6016cf9805b3e600f4e6003ea6f30f6cfcc001023000f6cc001e703375,0x0,0x401010000810020440001008000000000000e4,0xc01010000810020440005008000804020100e4,0x401010000810020440001008000000000000e4,0x1401010000810020440009008001008040201e4,0x0,0x0,0x401010000810020440001008000000000000e4,0x3cc798003ea603cc7980003ccf303ccf3003ccf6cc1e60f3001e9cc1e6003d39800f307983cc1e610856,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x79f9803cde60079f98000799e604467300983b201e9cc00f4e6f3003cfcc001f53000f6cc001e703885,0x0,0x401010001010040440001008000000000000e4,0xc01010001010040440005008000804020100e4,0x401010001010040440001008000000000000e4,0x1401010001010040440009008001008040201e4,0x0,0x0,0x401010001010040440001008000000000000e4,0x3cc798003ea603cc798000798f301e6f300798f6cc1e60f3001e9cc1e6003d39800f307983cc1e610856,0x401010001010040440001008000001000000e4,0x0,0x401010001010040440001008000001000000e4],
[0x0,0x0,0x0,0x401010001010040440001008000002000000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x420882240481,0x410882240481,0x410882240481,0x420882240481,0x420882240481,0x420882240481,0x410882240481,0x440886240481,0x420882240481,0x440886240481,0x410882240481,0x0,0x0,0x8088484410a2,0x0,0x8088484410a2,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481],
[0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x401010000010000440001008080002000000e4,0x0,0x0,0x8088484410a2,0x0,0x8088484410a2,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x3d39803cde60079f9800f30000f379800f4e60f6cc1e63cc1e6f6cc3cfcc001023000f6cc001e7033d5,0x0,0x0,0xc09048641902,0x0,0xc09048641902,0x410000240481],
[0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x401010000011000440001008080002000000e4,0x0,0x0,0xc09048641902,0x0,0xc09048641902,0x410000240481,0x400000240481,0x410000240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x440004240481,0x400000240481,0x440004240481,0x400000240481,0x0,0x3cc007d4c001ed980081180020467988119e6204601e67981e711603cfcc001023000f6cc001e703375,0xf379803cde6007987987981e61e6811879a0461e607987981e711603cfcc003db3000f6cc001e703d95],
[0xf3001e9cc0079f9800fa98003ea67980799e63ea607987981e6f3003cfcc003db3000f6cc001e7241f5,0x79f9803cde600798f307983cc1e688b079a22c1e603cc7981e6fa983cfcc001f53000f6cc001e8e9885,0x412048240481,0x402008240481,0x412048240481,0x46218c240501,0x422088240481,0x402008240481,0x422088240481,0x46218c240501,0x44210c240501,0x402008240481,0x44210c240501,0x46218c240501,0x0,0x0,0x80a0484410a2,0x0,0x80a0484410a2,0x411004240481,0x400000240481,0x411004240481,0x400000240481,0x420000240481,0x400000240481,0x420000240481,0x400000240481,0x44210c240501,0x400000240481,0x44210c240501,0x400000240481,0x0],
[0x3cc007d4c001ed980081180025f879888b1e6204601e7e601e72fc03cfcc001023000f6cc001e703375,0x0,0x3cc007d4c0079f9800fa980025f8799f531e6d68601e7e601e72fc03cfcc001023000f6cc001e703375,0x0,0x412048240481,0x402008240481,0x412048240481,0x46218c240501,0x422088240481,0x402008240481,0x422088240481,0x46218c240501,0x44210c240501,0x402008240481,0x44210c240501,0x46218c240501,0x401010040011000440001008080002000000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6636 : TreeBound (n := 4) 107 (programCode 0x462b07407c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x4002000110000000440000000200000000c0002010100000000400000041000000104002010010000040000000080000010100000200100000800400000400800001001001087fe27,0x4000000110000000440000000800000000c0002000100000000400000001000000004200010010800040000000080004000100420000100080000400000000800400001001087fea7,0x0,0x7980f31e60f3079fa76cc001023000f6cc000f6cc1e60f31e603cc1e600097e0001e9cc007a73465356,0x0,0x7980f31e6798079fa76cc001023000f6cc000f6cc1e60f31e603cc1e6002046001e63cc01e6f3465356,0x0,0x0,0x4000000110000000440000000200000000c0002000100000000400000001000000004200010010000040000000080001000100020000100080000400040000800100001001087fe27,0x7980f31e600f379fa76cc001023000f6cc000f6cc1e60f31e603cc1e600f4e600f303cc0f30f346ccd6,0x4000000110000000440000000200000000c0002000100000000400000001000000004200010010000040000000080002000100020000100080000400100000800200001001087fe27,0x7980f31e603cc79fa76cc001023000f6cc000f6cc1e60f31e603cc1e601e7e6007983cc1e60f3465356,0x6400000110000000440000000210000000c0002001300000000c0000000300000000e400010010000040004000080010000100200000100800000400400000801000001001087fe27,0x0,0x0,0x7980f31e6000079fa76cc001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc03ccf300f3465356,0x0,0x3cc007b660079f980079f981023000f6d3980f4e60f30f3222c3cc2d93cc1f53f3003cfcc00f327ee46,0x0,0x0,0x0,0x0,0x408848440902,0x409048640902,0x408848440902,0x80000020200000401000000202000000880000020240000400020400202000000808000400020009000100004800200010004000208010000010040000080100001200092051e28,0x409048640902,0x40b048641902,0x409048640902,0x40b848741d02],
[0x40a048641902,0x0,0x40a048641902,0x0,0x8010000080080000080304000200800040000008100000008400000081000000080800200008000400008002000020001000200000400004080006000004010040010020905b1a8,0x79f9801e6001ed9f983cc001023000f6cc000f6cc1e60f31e603cc1e60005b20003cfcc003db3465356,0x0,0x79f9801e6003d39f983cc001023000f6cc000f6cc1e60f31e603cc1e600097e0001e9cc007a734671b6,0x0,0x79f9801e6798079f983cc001023000f6cc000f6cc1e60f31e603cc1e6002046001e63cc01e6f3465356,0x0,0x79f9801e6798079f983cc001023000f6cc000f6cc1e60f31e603cc1e6003ea6000f33cc03ccf3465356,0x400000011000000044000000080000000140002000100000000400000001000000004200010010800040000000080004000100020000100080000400100000800100001001087fea7,0x0,0x400000011000000044000000080000000140002000100000000400000001000000004200010010800040000000080004000100020000100080000400100000800200001001087fea7,0x0,0x0,0x79f9801e60f3079f983cc001023000f6cc000f6cc1e60f31e603cc1e60799e6079803cc7980f3465356,0x0,0x79f9801e60f3079f983cc001023000f6cc000f6cc1e60f31e603cc1e60f31e603cc03ccf300f3465356,0x79800f4e6003d398012fc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f34671b6,0x79f9801e60000798003cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x79803cde603cc7980408c001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x79f9801e60f307983cfcc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x0,0x0,0x0,0x0,0x0,0x10800240481,0x240481,0x10800240481],
[0x240481,0x421004240481,0x240481,0x421004240481,0x240481,0x42000240481,0x240481,0x42000240481,0x240481,0x0,0x400201001000004004000002000000008000022010000080000000040040000100104002010010000040000000080000010100400000101000000404000000810000001001087fe27,0x420001001000004004200008000000008042002000108000000400000000040000004200010010800040000000080004000100400000101000000404000000810000001001087fea7,0x0,0x799e601e60f30799e6000798f301e6f300798f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x7981e61e61e607981e9cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f355fcd6,0x0,0x80040000400b0000100040000200100000200008100800040400000020008000080800040004000b00010000400020001000400020801000002004000008010000020009205ae28,0x0,0x0,0x0],
[0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x7983cc1e60f307983cfcc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x799e601e603cc799f56cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356,0x798f301e6f300798f33cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3de3356,0x0,0x0,0x0,0x0,0x79f9801e6003d39f98000798f301e6f300798f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f34671b6,0x40800240481,0x40000240481,0x40800240481,0x40000240481,0x441004240481,0x40000240481,0x441004240481,0x40000240481,0x42000240481,0x42000240481,0x42000240481,0x40000240481],
[0x799e601e67980799e63cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3003cfcc00f3465356]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6765 : TreeBound (n := 4) 107 (programCode 0x462b07407d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1e60008118002046000b640002d90798b641e6204601e67981e711603cfcc001023000f6cc001e703375,0x1e67980799e601e6079bcc01e6f307983cc20461e607987981e6f3003cfcc003db3000f6cc001e703d95,0x1e6001ed98007b660012fc0004bf07983cc1e63ea607987981e6f3003cfcc003db3000f6cc001e7241f5,0x1e67980799e601e60f33cc03ccf3088b3cc222c1e603cc7981e711603cfcc001f53000f6cc001e8e9885,0x814048240481,0x804008240481,0x814048240481,0x0,0x1e60f3079a22c1e60f3798408de617bb7985eee04601e67981e711603cfcc001023000f6cc001e8e9375,0x0,0x1e60f3079a22c1e6001e60f307984459e6097e7b6607987981e711603cfcc003db3000f6cc001e726055,0x0,0x850948240501,0x842108240501,0x850948240501,0x842108240501,0x86118c240501,0x842108240501,0x86118c240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x0,0x8204c9240481,0x2004080108004040102008040208002200081ce3,0x8204c9240481,0x2004080108004080102008080208002200081ce3,0x82088a240481,0x82108c240481],
[0x82088a240481,0x822088240481,0x82108c240481,0x82108c240481,0x82108c240481,0x820088240481,0x822088240481,0x82108c240481,0x822088240481,0x822088240481,0x799e731a7e600799e9cc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f3026388c098d7c7ed6,0x0,0x8204c9240481,0x0,0x8204c9240481,0x0,0x82088a240481,0x82108c240481,0x82088a240481,0x822088240481,0x82108c240481,0x82108c240481,0x82108c240481,0x820088240481,0x822088240481,0x82108c240481,0x822088240481,0x822088240481,0x1e63cd18f8f301e63cfcc001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f302322cc08c8065356,0x844108240501,0x804008240481,0x844108240501],
[0x844108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6830 : TreeBound (n := 4) 107 (programCode 0x462b07407e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x7d4c001e6f300b640000f307983cc1e60f3001e60001e6f3003cfcc001023000f6cc001e703375,0x1e600097e0007b66000b64001023000f6cc000f6cc1e60f31e603cc1e63cc1e60f303cc3cc0f30799556,0x0,0x102301e9cc00799e600f303cde6016c80005b3e600fa98003ea6f3003cfcc003db3000f6cc001e703d95,0x0,0x111601e9cc00799e600f30f33cc04458000981cc03d39800f4e6f3003cfcc003db3000f6cc001e722395,0x0,0x0,0x20400804002010080440201008080102004020e4,0x20400804020010800440101008080102004020e4,0x20400804004010100440201008080102004020e4,0x798b640799e601e60f35b2003db30003db3000fa98b641e603cc3cc1e63cc2d90f300f33cc03cc1e7df6,0x0,0x20400804020011000440101008080102004020e4,0x0,0x1dcd6501dcd65ee6b658247ec69e1bc77e17801dcd8a40be41e08ffca0007823ff28001ebbd0639ae095a698e6b283b9b059ad3502f9007735cf9acaee6d4f57cc8ee6b639aca773770d6500773d07594000f047fe5001dd4d8594001deb3265000eee25d94000ee767aa6f6a79,0x20400804020010800440101008080102004020e4,0x168f63350ae39c0b4784930288f8e868f08fa4ff08f915893b9e74a674930e51ea49bc830168f0abc13b3720d7f7f98875700000b47847d27f84a9a820fac6e7000b4a565d929ce002d20e3d2efeec130be07f304bae847c74e8f09260512a6a083eb1ba1a3c23e39c00002d1e135abe8f8e75a3c254c8c8f8e7b4786ff5fffb5b834785e5640f8e75a3c3a72a4f8e705a3c7e1fbfe39c02d1f7ae25d8e70168f63350ae39c02d1f7ae25d8e7005a41c7a5da39c005a52b2ec94e7002d23b5b40c39c002d1e2b6b0ccd9a7c52ad,0x20400804040011000440101008080102004020e4,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x0,0x610441240481,0x0,0x610441240481,0x0,0x410882240481,0x410000240481,0x410882240481,0x410000240481,0x411004240481,0x410000240481],
[0x411004240481,0x410000240481,0x612048240481,0x411004240481,0x612048240481,0x410000240481,0x4000240481,0x0,0x610441240481,0x0,0x610441240481,0x0,0x410882240481,0x410000240481,0x410882240481,0x410000240481,0x411004240481,0x410000240481,0x411004240481,0x410000240481,0x612048240481,0x411004240481,0x612048240481,0x410000240481,0x0,0x0,0x0,0x79800f379803cde6007f32003db30003d39800fa98b641e603cc3cc1e63cc2d90f300f33cc03cc1f70f6,0x0,0x410882240481,0x240481,0x410882240481],
[0x240481,0x21004240481,0x240481,0x21004240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x620441240481,0x40001080000400000080402080022000814e3,0x620441240481,0x40001080000000000080002080022000814e3,0x420882240481,0x20000240481,0x420882240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422088240481,0x20000240481,0x422088240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x0,0x620441240481,0x0,0x620441240481,0x0],
[0x420882240481,0x20000240481,0x420882240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422088240481,0x20000240481,0x422088240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x844108240501,0x4000240481,0x844108240501,0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_6943 : TreeBound (n := 4) 107 (programCode 0x462b07407f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1e600097e000222c000b640002d90798b641e6204601e7e601e72fc03cfcc001023000f6cc001e703375,0x0,0x1e6007b66001e9cc0dc74c001f53079fd4c21d0fe601e7e601e7a9403cc003ccf300f3f3003cde703375,0x7980001e600003cc079bcc0000f307983cc1e607980799e601e6f3003cc00003cc0000f33cc01e703d95,0x3cc007b66003cfcc0b67cc001f5307af04c1ebb5cc03cde601e7a9403cc00799e603ccf300799e703885,0x3cc0001e600003cc0b67cc0000f307983cc1e603cc03cde601e6f3003ced9001f16400f5d9001e703885,0x0,0x0,0x7980799e601e63cc079bcc01e6f307983cc20467980799e601e6f3003cc07983cc1e60f303cc1e703d95,0x0,0x3cc0007980007d4c000b64001023000f6cc000f6cc1e60f31e603cc1e60f31e60f300000f30000001556,0x0,0x1e60001e61e603cc86cdcc0000f307983cc21b29e601e7e601e72fc03cc0f300f3f300f31e601e703375,0x0,0x7980799e601e63cc079bcc01e6f307983cc20467980799e601e6f3003cc79803cde600f379801e703d95,0x7980001e600003cc079bcc0000f307983cc1e607980799e601e6f3003cc00003cc0000f300001e703d95,0x800018002200044060100800040000000104,0x1e60001e61e603cc0d4dcc0000f307983cc21b29e601e7e601e72fc03cc79800fa9800f7bf001e703375,0x1e600097e0007d4c0012fc0002d9079a22c1e6d68601e7e601e72fc03cfcc001023000f6cc001e703375,0x0,0x84c169204501,0x7980001e61e603cc3cc3cc0000f307983cc1e607980799e601e76c803cc00003cc0000f33cc01e703d95,0x84c169204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0xf3010230003ccf3012fc001023000f6cc000f6cc1e60f31e603cc1e6003ea6000f4e6003d3983cf3b6,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x814048240481,0x804008240481,0x814048240481,0x7983cc1e62d903cc7983cc0f30f30b643cc2d907980799e601e76c803cfcc003db3000f6cc001ee9bd95,0xf30b640001e600001e63cc003db3000f6cc000fa98b640f31e603cc1e63cc1e60f300003cc0000001dc6,0x0,0x8304c9240481,0x0,0x8304c9240481,0x0,0x82088a240481,0x800008240481,0x82088a240481,0x802008240481,0x801008240481,0x800008240481,0x801008240481,0x800008240481,0x802008240481,0x800008240481,0x802008240481,0x802008240481,0x7980799e601e63cc03cfcc01e6f307983cc20467980799e601e6f3003cfcc003db3000f6cc001e703d95,0x0,0x0,0x0,0x0],
[0x0,0x840908240501,0x800008240481,0x840908240501,0x842108240501,0x82108c240481,0x800008240481,0x82108c240481,0x800008240481,0x842108240501,0x800008240481,0x842108240501,0x842108240501,0x844108240501,0x804008240481,0x844108240501,0x844108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_7024 : TreeBound (n := 4) 107 (programCode 0x462b074080) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c041204481,0x0,0x10c041204481,0xc000200481,0x20c082208481,0xc000200481,0x20c082208481,0x0,0x0,0x4000180002000000080002080020000814e3,0x0,0x4000180002000000080002080020000814e3,0x80c028220481,0x410018004200100004010200801010080ca3,0x80c028220481,0xc000200481,0x0,0x0,0x0,0x0,0x0,0x0,0x8088484410a2,0x80a0484410a2,0x8088484410a2,0x0,0x809048641902,0x80a0484410a2,0x809048641902,0x0],
[0x80a0484410a2,0x3cc00097e0007d4c000c57000fa9800f6cc000f6cc1e61e62d903cc1e63cc25f8f303cc3cc0f307995e6,0x80a0484410a2,0x0,0x10c041204481,0x8000280002000000080002000020400814e3,0x10c041204481,0xc000200481,0x20c082208481,0xc000200481,0x20c082208481,0x8000280002000000080002000022000814e3,0x0,0x0,0x0,0x0,0x80c028220481,0x8000280002000000080002000020100814e3,0x80c028220481,0xc000200481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x14000240481,0x4000240481,0x14000240481,0x0,0x0,0x0,0x0,0x0,0x10800240481,0x240481,0x10800240481],
[0x240481,0x421004240481,0x240481,0x421004240481,0x240481,0x42000240481,0x240481,0x42000240481,0x240481,0x0,0x0,0x0,0x0,0x40001080000000000080002080022000814e3,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x0,0x0,0x0,0x0,0x0],
[0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x44000240481,0x4000240481,0x44000240481,0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_5136 : TreeBound (n := 4) 107 (programCode 0x462b0740) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part101_5137 part101_5330 part101_5555 part101_5684 part101_5685 part101_5798 part101_5911 part101_5912 part101_6137 part101_6330 part101_6459 part101_6636 part101_6765 part101_6830 part101_6943 part101_7024

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part101_0 : TreeBound (n := 4) 107 (programCode 0x462b07) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part101_1 part101_2 part101_419 part101_420 part101_1221 part101_1222 part101_1223 part101_1224 part101_2185 part101_2186 part101_2491 part101_2492 part101_3213 part101_3502 part101_4223 part101_5136

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned101 : TreeBound (n := 4) 107 [((0,0),⟨1,1,false⟩),((1,0),⟨2,1,false⟩),((2,0),⟨1,0,true⟩)] := part101_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1 : TreeBound (n := 4) 107 (programCode 0x4a2b0751) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10804d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3 : TreeBound (n := 4) 107 (programCode 0x4a2b075211) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081890204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4 : TreeBound (n := 4) 107 (programCode 0x4a2b075212) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5 : TreeBound (n := 4) 107 (programCode 0x4a2b075213) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081890204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_6 : TreeBound (n := 4) 107 (programCode 0x4a2b075214) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081881204481,0x1081004210481,0x1081881204481,0x1081000200481,0x1081002208481,0x1081000200481,0x1081002208481,0x1081004210481,0x1081004210481,0x1081000200481,0x1081004210481,0x1081004210481,0x0,0xf3079a22c0000f30000000f4e6003d398003d3a733cc222c0003cc00007991167983cc00007983cc3cb6,0x0,0x0,0xf3000222c00088b0000f30f4e6003d398003d3a733cc222c0003cc00007991167983cc00007983cc3cb6,0xf3079a22c0000f30000f30f4e6003d398003d3a733cc222c0003cc00007991167983cc00007983cc3cb6,0xf3000f6cc003db30003cc0f4e6003d398003d3a733cc222c0003cc0f307991167983cc0f307983cc3cb6,0xf3079a22c0000f30000f30f4e6003d398003d3a733cc222c0003cc00007991167983cc00007983cc3cb6,0x0,0xf3081495c0004bf001e600f4e6003d398003d3a829a5222c0003cfcc00799116b643cc07987983cc3cb6,0xf30079bcc01e6f3001e600f4e6003d398003d3a82300222c0003cfcc007991167983cc07987983cc3cb6,0x0,0x400021001000000004000210010000000042002000108000000000000000040000002000010004000040010000080010000100600000101c00000404000000804000001001087faa7,0xf307983cc1e60f30000000f4e6003d398003d3a73000222c0003cc00007991167983cc00007983cc3cb6,0x0,0xf307983cc1e60f30000000f4e6003d398003d3a73000222c0003cc00007991167983cc00007983cc3cb6,0x0,0x0,0x180488084222],
[0x180488084222,0x180488084222,0x180488084222,0x2400090000000400010082002000020400814e3,0x280488084642,0x180488084222,0x280488084642,0x580488084a62,0x480488084a62,0x180488084222,0x480488084a62,0x0,0x0,0x0,0x0,0x0,0xf3079a22c0000f30000000f4e6003d398003d3a733cc222c0003cc00007991167983cc00007983cc3cb6,0x0,0x0,0x0,0x0,0xf3000f6cc003db30003cc0f4e6003d398003d3a73000222c0003cc00007991167983cc00007983cc3cb6,0x0,0x0,0xf30813a2c0004bf001e600f4e6003d398003d3a733cc222c0003cc0f307991167983cc0f307983cc3cb6,0xf30079bcc01e6f3001e600f4e6003d398003d3a733cc222c0003cc0f307991167983cc0f307983cc3cb6,0x0,0x400021001000000004000210010000000042002000108000000000000000040000002000010008000040010000080020000100600000101800000404000000804000001001087faa7,0xf307983cc1e60f30000000f4e6003d398003d3a73000222c0003cc00007991167983cc00007983cc3cb6,0x0,0xf307983cc1e60f30000000f4e6003d398003d3a73000222c0003cc00007991167983cc00007983cc3cb6,0x0],
[0x0,0x180488084222,0x180488084222,0x180488084222,0x180488084222,0x0,0x280488084642,0x180488084222,0x280488084642,0x580488084a62,0x480488084a62,0x180488084222,0x480488084a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_87 : TreeBound (n := 4) 107 (programCode 0x4a2b075215) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_88 : TreeBound (n := 4) 107 (programCode 0x4a2b075216) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201000108002108003a00010442008040304]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_89 : TreeBound (n := 4) 107 (programCode 0x4a2b075217) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_90 : TreeBound (n := 4) 107 (programCode 0x4a2b075218) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307980003d39803d398003d3a730000b64001f53000079bea6000fa98003cc1e610856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_91 : TreeBound (n := 4) 107 (programCode 0x4a2b075219) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_92 : TreeBound (n := 4) 107 (programCode 0x4a2b07521a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_93 : TreeBound (n := 4) 107 (programCode 0x4a2b07521b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_94 : TreeBound (n := 4) 107 (programCode 0x4a2b07521c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081010210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_95 : TreeBound (n := 4) 107 (programCode 0x4a2b07521d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10094d0220481,0x1021010220481,0x10094d0220481,0x0,0x80402000100820402800880022020020800814e3,0x80402000000000400000080402020020800814e3,0x80402000201020402801080042020020800814e3,0x0,0x80402000402080402002080082020020800814e3,0x80402000000000400000080002020020800814e3,0x80402000804080402004080102020020800814e3,0x80402000000000400000080002020020800814e3,0x80402001008000400008080202020020800814e3,0x80402000000000400000080002020020800814e3,0x80402002010000400010080402020020800814e3,0x80402000000000400000080002020020800814e3,0x80402004020100404020080802020020800834e3,0x0,0x0,0x0,0x1011890220481,0x80402000000000400080082002020020800814e3,0x1011890220481,0x80402000000000400080082002020020800814e3,0x1021010220481,0x1001010220481,0x1021010220481,0x1021010220481,0x1043110220501,0x8020200400108002108070a0001c060080402104,0x1043110220501],
[0x8020200800108002108060a0001c060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_128 : TreeBound (n := 4) 107 (programCode 0x4a2b07521e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8040200000108002108030a00014060080402104,0x8000a00010108002108030a00014060080402104,0x0,0x109010208481,0x409010208481,0x109010208481,0x0,0x209010218481,0x443008040108002108030a00014063080402304,0x209010218481,0x1eda7307981e60f307980f4e6003d398003d3a7303ce22c03ccf3000097e2deb99879807983cc1f7156,0x409010208481,0x9010208481,0x409010208481,0x409010208481,0x80989020c481,0x609010218481,0x80989020c481,0x8000210000400080082002000020100814e3,0x0,0x400000011000000014000000090000000100020100000080400000100800000100804002900100002400400029200000020000a000380008000e000100008000100008001400fdea8,0xf300012fc0004bf0000f303d39803d398003d39800f30798f6cc000f308119e607980f307983cc1e93b6,0x0,0xf300012fc0004bf0000f303d39803d398003d39801e607987d4c001e608119e607983cc07983cc9813b6,0x0,0xf300012fc0004bf0000f303d39803d398003d3980798079f9bcc0079808119e60798003d3983cc1f0d36,0x0,0xf300012fc0004bf0000f303d39803d398003d3980f30079bcfcc00f3008119e607980079f983cc1f86b6,0xf3000222c00088b0000f30f4e6003d398003d3afbf08ded983cc03cc0097e2d9811800081183cc1e9cb6,0xf300012fc0004bf0000f303d39803d398003d3983cc007d4c3cc03cc008119e6079800081183cc1e93b6,0xf3000222c00088b0000f30f4e6003d398003d39f9c08ded983cc000f3097e2d907980f307983cc1e9cb6],
[0x0,0xf3000222c00088b0000f30f4e6003d398003d3aec83ce22c03cc00000097e2d9079800007983cc1e9cb6,0x0,0x0,0x0,0x8070200400108002108030a00014060080402104,0x8002200040108002108030a00014060080402304,0x8060200400108002108030a00014060080402104,0xf30007d4c001f5300079803d39803d398003d3a730000b6403ccf300008119e6079879807983cc1f6856,0x8078200100108002108030a00014060080402904,0x8008200100108002108030a00014060080402904,0x8030a00010108002108030a00014060080402104,0x8008200200108002108030a00014060080403104,0x8040200000108002108030a00014060080402104,0x8020200400108002108030a00014060080402104,0x8040200000108002108030a00014060080402104,0x8020200800108002108030a00014060080406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_177 : TreeBound (n := 4) 107 (programCode 0x4a2b07521f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10094d0220481,0x1021010220481,0x10094d0220481,0x0,0x804030000820402880082002040021000814e3,0x410000000400080082002040021000814e3,0x1008050001020402880082002040021000814e3,0x2010000000400080082002040021000814e3,0x2010090002080402080082002040021000814e3,0x0,0x4020110004080402080082002040021000814e3,0x0,0x8040210008000400080082002040021000814e3,0x10000000400080082002040021000814e3,0x10080410010000400080082002040021000814e3,0x10000000400080082002040021000814e3,0x0,0x0,0x40201010040200408080082002040021000854e3,0x0,0x1011890220481,0x0,0x1031881220481,0x1001004220481,0x1031881220481,0x0,0x1021002220481,0x1001000220481,0x1021002220481,0x1001004220481,0x1001004220481],
[0x1001000220481,0x1001004220481,0x1001004220481,0x1001008220481,0x800220004010800210407088001c060080402304,0x1001008220481,0xf3000408c003db30003cc03d39803d398003d39bcc00088b07983cc00088b1e60f307980f307983ebb56,0x1011890220481,0x0,0x1063181220501,0x1021004220481,0x1063181220501,0x0,0x1031882220481,0x1021000220481,0x1031882220481,0x1021004220481,0x1021004220481,0x1021000220481,0x1021004220481,0x1021004220481,0x0,0xf30007d4c001f5300079803d39803d398003d399e600097e0f301e600097e1e60f307981e60f307a8856,0x0,0xf30007d4c001f5300079803d39803d398003d39bcc00088b07983cc00088b1e60f307980f307983dc856,0x1021010220481,0x1001010220481,0x1021010220481,0x1021010220481,0x1043110220501,0x0,0x131890220481],
[0x401010220481,0x131890220481,0x0,0x221010220481,0x420008400108002108043a00018442008040304,0x221010220481,0xf3f3003db3000f3f30003d39803d398003d3a730000b64001f53000079bea60f30798003cc1e610856,0x401010220481,0x1010220481,0x401010220481,0x401010220481,0x801010220481,0x1010220481,0x801010220481,0x1010220481,0x1043110220501,0x0,0x14b5f0220501,0x421010220481,0x14b5f0220501,0x0,0x0,0x7b660079f98007b660003d39803d398003d3a730000b64003db3000079fb660f30798007983cc1fb56,0x0,0xf4e6003d39800f4e60003d39803d398003d3a730000b64001f53000079bea60f30798003cc1e610856,0x421010220481,0x1010220481,0x421010220481,0x421010220481,0x843110220501,0x1010220481,0x843110220501],
[0x1010220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_274 : TreeBound (n := 4) 107 (programCode 0x4a2b075220) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0000f307980003d39803d398003d3a730000b640798f3000088b1e603cc7980f307983cd556,0x0,0x121010210481,0x421010210481,0x121010210481,0x0,0x0,0x2004080100840021080202000140401008442e4,0x0,0x4004100100840021080202000140401008844e4,0x421010210481,0x21010210481,0x421010210481,0x421010210481,0x821010230481,0x21010210481,0x821010230481,0x421010210481,0x0,0x109010200481,0x409010210481,0x109010200481,0x0,0x0,0x2010090400840021080202000140401008442e4,0x0,0x4020110800840021080202000140401008844e4,0x409010210481,0x9010200481,0x409010210481,0x409010210481],
[0x8094d0220481,0x0,0x8094d0220481,0x9010200481,0x0,0xf3000222c0004bf0000f30f4e6003d398003d3a735eede609048001e6097e35283cc1e60f307983cfc26,0xf3000222c00088b0000f307a73001e9cc003d3980222c000811bcc0f3097e0f30798d4a0f30798b69936,0x0,0xf300012fc00088b0000f307a73001e9cc003d3980222c00109cbcc1e6088b0798798b640f307983d1426,0x40000000500000002400000011000000010001008000004020000010080000010080080008001600c200200020c000200000008800040004000b0002000200002000100008025aba8,0xf300012fc0004bf0000f303d39803d398003d3980798079f9f9800798088b1e603cc003db307983d6d36,0x0,0xf3000222c00088b0000f307a73001e9cc003d3981e9cc0079f9bccf30097e003d398b733f30798b87f36,0x0,0xf300012fc0004bf0000f303d39803d398003d3983cc007d4c79803cc0088b1e603cc00088b07983cf3b6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf30b643cc0000f301e6000f4e6003d398003d3aec83cde6016c800000097e2d903cc0000f307983cddc6,0xf30d4a3cc0798f301e6000f4e6003d398003d3980408de60fa98000f3097e2d907981e60f307983cde56,0x0,0xf301e63cc0798f301e60003d39803d398003d39801e607988118001e6088b1e603cc1e60f307983cd556,0xf300003cc0000f301e60003d39803d398003d3980000079807983cc00088b1e603cc7980f307983cd556,0xf30000b640002d901e60003d39803d398003d3980798079f9f9800798088b1e603cc003db307983cd556,0xf30b643cc0000f301e6000f4e6003d398003d3aec83ce22c07983cc00097e2d907987980f307983cde56,0xf301e63cc0798f301e60003d39803d398003d3980f30079bd39800f30088b1e603cc007a7307983cd556,0xf30bfe02c007a7301e6000f4e6003d398003d3afbf08df53079803cc0097e2d9811800088b079840aa56,0xf3001e9cc007a7301e60003d39803d398003d3983cc007d4c79803cc0088b1e603cc00088b079840a156],
[0xf301e63cc0798f301e60003d39803d398003d39800f3088b0798000f3088b1e603cc97e0f307983cd556,0xf30079bcc01e6f301e60003d39803d398003d398798007b6679807980088b1e603cc001f5307984fd156,0xf30b643cc0000f301e6000f4e6003d398003d3aec83ce22c079800000097e2d907980000f307983cde56,0xf301e63cc0798f301e60003d39803d398003d399e600097e07981e600088b1e603cc7980f307983cd556,0x0,0xf300003cc0000f301e60003d39803d398003d39bcc00088b07983cc00088b1e603cc7980f307983cd556,0xf3000408c003db30003cc03d39803d398003d3a730000b640798f3000088b1e603cc7980f307983ebb56,0x0,0xf30b643cc0000f301e6000f4e6003d398003d3aec83cde6016c800000097e2d903cc0000f307983cddc6,0xf307983cc0798f301e60003d39803d398003d39800f30798fa98000f3088b1e603cc1e60f307983cd556,0x0,0xf307983cc0798f301e60003d39803d398003d39801e607988118001e6088b1e603cc1e60f307983cd556,0x0,0xf307983cc00102301e60003d39803d398003d3980798079f9f9800798088b1e603cc003db307983d4ed6,0x0,0xf307983cc001f5301e60003d39803d398003d3980f30079bd39800f30088b1e603cc007a7307983dc856,0xf30b6622c0002d901e6000f4e6003d398003d3afbf08df53079803cc0097e2d9811800088b07983cde56,0xf307983cc0002d901e60003d39803d398003d3983cc007d4c79803cc0088b1e603cc00088b07983cd556,0xf30b643cc0798f301e6000f4e6003d398003d39f9c08df530798000f3097e2d907981e60f307983cde56,0x0,0xf30b643cc0000f301e6000f4e6003d398003d3aec83ce22c079800000097e2d907980000f307983cde56,0x0,0x0,0x0,0xf3000f6cc003db300079807a73001e9cc003d3a7303cc3cc079cbf000097e1e60798b640f30798b84276,0xf30b643cc088bf3001e6007a73001e9cc003d3a7303cc3cc079cbf000097e1e60798b640f30798447476,0x8008200100108002108020a00014060100805104,0xf30000b640798f300007983d39803d398003d3a730000b640798f3000088b1e603cc7980f307983cd556,0x8008200200108002108020a00014060100805104,0x0,0x141890204481,0x441010210481],
[0x141890204481,0x0,0x16c87985b200003cc000000f4e6001e9cc003d3a7303ce22c079cbf000097e2d90798b640f307983cde26,0x2004088500840021080202000140401008442e4,0x16c87985b200003cc000000f4e6001e9cc003d3a7303ce22c079cbf000097e2d90798b640f307983cde26,0x4200108000840021080202000140401008844e4,0x441010210481,0x41010200481,0x441010210481,0x441010210481,0x843110220501,0x843110220501,0x843110220501,0x41010200481,0x8020200400108002108020a00014060100804104,0x0,0x141890204481,0x441010210481,0x141890204481,0xf303cc00003ccf301e64273e600007983db3000f30079bcc007a73003cfcc003db30003cc0001e64dc35,0x0,0x0,0x0,0x0,0x441010210481,0x41010200481,0x441010210481,0x441010210481,0x843110220501,0x843110220501,0x843110220501,0x41010200481],
[0x8020200800108002108020a00014060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2 : TreeBound (n := 4) 107 (programCode 0x4a2b0752) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part102_3 part102_4 part102_5 part102_6 part102_87 part102_88 part102_89 part102_90 part102_91 part102_92 part102_93 part102_94 part102_95 part102_128 part102_177 part102_274

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_403 : TreeBound (n := 4) 107 (programCode 0x4a2b0753) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10804d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_405 : TreeBound (n := 4) 107 (programCode 0x4a2b075411) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307980003cde6016cfd4c5d2553001e9cc01e6f3003cc003ccf300f3f3003cde703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_406 : TreeBound (n := 4) 107 (programCode 0x4a2b075412) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010001040041080006000200c00020100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_407 : TreeBound (n := 4) 107 (programCode 0x4a2b075413) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f30798000799e6044676cc219513003cfcc01e6f3003cc00799e603ccf300799e703885]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_408 : TreeBound (n := 4) 107 (programCode 0x4a2b075414) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081004210481,0x10804c1204481,0x1080000200481,0x1080882208481,0x1080000200481,0x1080882208481,0x1080000200481,0x1081004210481,0x1080000200481,0x1081004210481,0x1080000200481,0x0,0x16c80005b200016c8079801e6016c8079a0647e603cc7981e61e603cc79801e600f3f379801e703885,0x7983cc1e600f379800000000f37980799e601e607987981e61e603cc00003ccf300f379801e703d95,0x445800111600025f800079bcc025f8079a082de607987981e61e603cc0079bcc01e6f379801e722395,0x0,0x0,0x81180020460008118000f379803cde60079f9801e61e6079888b0000f30f3079844580007987985756,0xfa98007b66000fa9807981e600fa98079a0461e603cc7981e61e603cc79801e60f30f379801e703885,0x7980001e6000079800000000007980799e601e603cc7981e61e603cc00001e60000f379801e703885,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x180488084222],
[0x180488084222,0x180488084222,0x180488084222,0x2400090000000400010082002000020400814e3,0x280488084642,0x180488084222,0x280488084642,0x580488084a62,0x480488084a62,0x180488084222,0x480488084a62,0x0,0x0,0x0,0x0,0x0,0x16c80005b200016c82d9001e6016c82d920649cc03cde601e63cc03ced9001e600f3f5d9001e703885,0x7983cc1e600f379800000000007981e61e607980799e601e63cc03cc00003cc0000f4e6001e703d95,0x445800111600025f8000003cc044581e620833980799e601e63cc03cc00003cc03ccf4e6001e722395,0x7980001e60b6479800000000007982d91e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x1ed98002046000fa982e29f3900fa980798079f980798798079bcc03cee27e3cc0f303d39801e64dc35,0x7980001e6000079800000000007982d91e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0xf379803cde6003d398315de6003d39807980007980798798079bcc03cf15c03cc3cc03d39801e64dc35,0x7983cc1e60f3079800000000007981e61e607980799e601e63cc03cc00003cc0000f4e6001e703d95,0xf379803cde60079f9800000000f37981e61e607980799e601e63cc03cc00003ccf300f4e6001e703d95,0x7980001e60f3079800000000007982d91e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x0],
[0x0,0x180488084222,0x180488084222,0x180488084222,0x180488084222,0x0,0x280488084642,0x180488084222,0x280488084642,0x580488084a62,0x480488084a62,0x180488084222,0x480488084a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_489 : TreeBound (n := 4) 107 (programCode 0x4a2b075415) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1208481,0x1081004208481,0x10804c1208481,0x1080000208481,0x1080882208481,0x1080000208481,0x1080882208481,0x1080000208481,0x1081004208481,0x1080000208481,0x1081004208481,0x1080000208481,0x0,0x100a0e8208481,0x1022088208481,0x100a0e8208481,0x1042108208501,0x10120c8208481,0x1002008208481,0x10120c8208481,0x80402004020100804020080802002020080834e3,0x1022088208481,0x1002008208481,0x1022088208481,0x80402000020000800020080802002020080814e3,0x1042108208501,0xf303cc3cc0f30f300f3000f4e6003d3980079faec8c5922c03cc1e600155bb15c1e67983cc03cc1e7e56,0x1042108208501,0xf303cc3cc0f30f301e6000f4e6003d3980079faec8b6622c0f307980014e22d907987983cc0f30799e56,0x0,0xf30000b640002d9000079bcde600fb11bcc2046f3003cfcc01e600f33cc01e61e60798f301e61e703885],
[0xf30000b6400088b000079879f9801ed980079f99e60011160002046000f305b200016c83cc0001e61556,0xf3000222c00088b0000f3799e601ed983cc2046f30079bcc01e601e63cc01e63cc0798f301e61e703d95,0x0,0x0,0x0,0x80402000001040041020000800200402000000e4,0x80022000801040041020020800204402104824e4,0xf3001e9cc1e60f3001e60079f9801ed980079f99e600111600799e6000f3f3003cfd3983cc007983e156,0xf3001e9cc01e6f3001e60079f9801ed980079f99e600111600799e6000f3f3003cfd3983cc007983e156,0x0,0xf3003cfcc00f3f3003cc0079f9801ed980079f99e600111600f31e6000f6cc003d39f983cc00f31aa956,0xf300f33cc03ccf300f307983cc1e688b3cc222cf3003cfcc01e61e603cc01e61e60798f301e61e8e9885,0xf300f33cc0f30f300f300079f9801ed980079f99e600111603cc1e6000fa99e601e67983cc03cc1e7556,0xf301e63cc0f30f301e62d916c8b64d4a3cc3528f3003cfcc01e6b6403cc01e61e60798f301e61f267885,0xf301e63cc0798f301e600079f9801ed980079f99e600111607981e60010231e603cc7983cc07983cd556,0x0,0x100a0e8208481,0x1022088208481,0x100a0e8208481,0x1042108208501,0x10120c8208481,0x1002008208481,0x10120c8208481,0x0,0x1022088208481,0x1002008208481,0x1022088208481,0x0,0x1042108208501,0x0,0x1042108208501,0x0],
[0x0,0x0,0xf3003cfcc00f3f300b640000000007983cc1e60f3003cfcc01e600003cc01e61e60798f301e61e703885,0x0,0x0,0x80002010001040041040001000200402000000e4,0x0,0x0,0x80022000801040041040021000204402108844e4,0x0,0xf3001e9cc01e6f3001e60079f9801ed980079f9bcc00102301e63cc000f3f3003db37983cc01e6131156,0x80002000201040041040001000200402000000e4,0xf3003cfcc00f3f3003cc0079f9801ed980079f9bcc00102300f33cc000f6cc003d39f983cc00f31aa956,0x0,0xf300f33cc0f30f300f300079f9801ed980079f9bcc0010230f303cc000fa99e607987983cc0f3097f556,0x0,0xf301e63cc0798f301e600079f9801ed980079f9bcc00102307983cc0010231e603cc7983cc07983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_570 : TreeBound (n := 4) 107 (programCode 0x4a2b075416) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1218481,0x1081004200481,0x10804c1218481,0x1080000200481,0x1080882210481,0x1080000200481,0x1080882210481,0x1080000200481,0x1081004200481,0x1080000200481,0x1081004200481,0x1080000200481,0x0,0x100bce821c481,0x1022088210481,0x100bce821c481,0x0,0x10120c8218481,0x1002008200481,0x10120c8218481,0x80402000000000800020080802000020000814e3,0x1022088210481,0x1002008200481,0x1022088210481,0x8040200000000080002004080200001000080ca3,0x0,0x0,0x0,0x0,0x0,0x0],
[0x16c800111600016c800079f9801ed980079f99e6001116003cde6000f31e9cc01e600799e63cc219b6,0x4a817c80003f5476a0001ebbd028000218711a00004a817c800003b9acbdcfb9fd1a70eb59400000000000430e2352a4299028d077360b3d07d0760b35943b9b059aca03b9b059ca6d6500773597b9aca0f04d94d2f0ee6d04d65077537f326507737ac711a0ee6d0c6e53af9,0x25f800111600025f80007a73003cfcc0079f9bcc007a730026166000f33cc0798f4f0711e61e614726,0x25f83cc1e600025f800079f9801ed980079f99e6001116003cde6000f31e9cc01e600f31e63cc219b6,0xfa98003ea600081180007a73003cfcc0079f9bcc007a730026166000f33cc1e60f4f1641e61e614726,0x2020000008080000010200000020800042002000108000000000000000040000004200010010800040001000080100000100400000101000000404000000800000001001087faa7,0xfa98007b66000fa980007a73003cfcc0079f9bcc007a730026166000f33cc3cc0f4fcc81e61e632d26,0x3d39800f4e6003d39800079f9801ed980079f99e6001116003cde6000f31e9cc01e61e601e63cc5e5b6,0x79f9801e7e6003d3980007a73003cfcc0079f9bcc007a730026166000f33ccf300f548b81e61e68df26,0xfa98004dd600025f80007a73003cfcc0079f9bcc007a730026166000f33cc25f8f4f0711e61e614726,0x79f9803cde60079f980007a73003cfcc0079f9bcc007a730026166000f33cde600f5a3d81e61e780f26,0x0,0x0,0x0,0x0,0x0,0x100bce821c481,0x1022088210481,0x100bce821c481,0x80002008000001000040081002000020000814e3,0x10120c8218481,0x1002008200481,0x10120c8218481,0x0,0x1022088210481,0x1002008200481,0x1022088210481,0x400020001000000004000200010000000060002000180000000000000000400000002000010008000040010000080020000100400000101000000404000000800000001001087faa7,0x0,0x0,0x0,0x0],
[0x0,0x137585b756e00137580007a73003cfcc0079f9bcc007b66002634c000f33cc25f8fe6e711e61e614726,0x0,0x0,0x445800111600025f8000f3f3003cfcc0079f9f98007b66002634c000f33cc0798f6d57e1e61e614c36,0x0,0xfa98003ea600081180007a73003cfcc0079f9bcc007b66002634c000f33cc1e60f6d3981e61e614726,0x7981e9ea6000fa980007a73003cfcc0079f9bcc007b66002634c000f33cc0000f6d3981e61e614726,0xfa98007b66000fa980007a73003cfcc0079f9bcc007b66002634c000f33cc1e60f6e2c81e61e614726,0x7982084a6003d3980007a73003cfcc0079f9bcc007b66002634c000f33cc0000f710581e61e614726,0x79f9801e7e6003d3980007a73003cfcc0079f9bcc007b66002634c000f33ccf300f710581e61e68df26,0xfa98004dd600025f80007a73003cfcc0079f9bcc007b66002634c000f33cc1e60f6d57e1e61e614726,0x79f9803cde60079f980007a73003cfcc0079f9bcc007b66002634c000f33ccf300f74d181e61e68df26,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_651 : TreeBound (n := 4) 107 (programCode 0x4a2b075417) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1208481,0x1081004208481,0x10804c1208481,0x1080000208481,0x1080882208481,0x1080000208481,0x1080882208481,0x1080000208481,0x1081004208481,0x1080000208481,0x1081004208481,0x1080000208481,0x0,0x100a0e8208481,0x1022088208481,0x100a0e8208481,0x1042108208501,0x10120c8208481,0x1002008208481,0x10120c8208481,0x80402004020100804020080802004020100834e3,0x1022088208481,0x1002008208481,0x1022088208481,0x80402000020000800020080802004020100814e3,0x1042108208501,0x0,0x1042108208501,0x0,0x0,0x80488080022],
[0x180488084222,0x80488080022,0x180488084222,0x2400090010000400010082002004020100814e3,0x8118007b66000811800079f9801ed980079f99e6001116000f4e6000fa983cc007983cc1e60f30ad36,0x80488080022,0xf307983cc1e600007983cc1e600007983cc0000f30079800007a73003cc07983cc07983cc3cc1e64dc35,0x580488294a62,0x480488294a62,0x180488084222,0x480488294a62,0x0,0x0,0x0,0x0,0x0,0x100a0e8208481,0x1022088208481,0x100a0e8208481,0x1042108208501,0x10120c8208481,0x1002008208481,0x10120c8208481,0x0,0x1022088208481,0x1002008208481,0x1022088208481,0x0,0x1042108208501,0x0,0x1042108208501,0x0],
[0x0,0x80488080022,0x180488084222,0x80488080022,0x180488084222,0x0,0x8118007b66000811800079f9801ed980079f9bcc001023003cfcc001023079801e60f307983cc219b6,0x80488080022,0xf307983cc1e600007983cc1e600007983cc0000f30079800007a73003cc07983cc07983cc3cc1e64dc35,0x580488294a62,0x480488294a62,0x180488084222,0x480488294a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_732 : TreeBound (n := 4) 107 (programCode 0x4a2b075418) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f30798000f3f3003cfcc0079fa73000f6cc00454b0000f37b66001eda7303cc3cc20276]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_733 : TreeBound (n := 4) 107 (programCode 0x4a2b075419) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1210481,0x1081004210481,0x10804c1210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1080882210481,0x1080000210481,0x1081004210481,0x1080000210481,0x1081004210481,0x1080000210481,0x0,0x100a0e8210481,0x1022088210481,0x100a0e8210481,0x1042108210501,0x10120c8210481,0x1002008210481,0x10120c8210481,0x80402004020100804020080802008020200834e3,0x1022088210481,0x1002008210481,0x1022088210481,0x80402000020000800020080802008020200814e3,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x580488294a62],
[0x180488294a62,0x580488294a62,0x180488294a62,0x2400090010000400010082002008020200814e3,0x8118007b66000811800079f9801ed980079f99e6001116000f4e6000f3f33cc007983ccf300f30ad36,0x580488294a62,0xfa98003ea6000fa9800079f9801ed980079f99e6001116001e7e6000f3f3f3000f30798f301e610856,0x580488294a62,0x480488294a62,0x580488294a62,0x480488294a62,0x0,0x0,0x0,0x0,0x0,0x100a0e8210481,0x1022088210481,0x100a0e8210481,0x1042108210501,0x10120c8210481,0x1002008210481,0x10120c8210481,0x0,0x1022088210481,0x1002008210481,0x1022088210481,0x0,0x1042108210501,0x0,0x1042108210501,0x0],
[0x0,0x580488294a62,0x180488294a62,0x580488294a62,0x180488294a62,0x0,0x8118007b66000811800079f9801ed980079f9bcc001023003cfcc000f3f379801e60f30f303cc219b6,0x580488294a62,0xfa98003ea6000fa9800079f9801ed980079f9bcc001023001e9cc000f3f379800f30798f301e610856,0x580488294a62,0x480488294a62,0x580488294a62,0x480488294a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_814 : TreeBound (n := 4) 107 (programCode 0x4a2b07541a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201000108004108008a00021048820201104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_815 : TreeBound (n := 4) 107 (programCode 0x4a2b07541b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010001040041080002000200400040000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_816 : TreeBound (n := 4) 107 (programCode 0x4a2b07541c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201000108004108008a00021048840201104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_817 : TreeBound (n := 4) 107 (programCode 0x4a2b07541d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c80003cde6016cfd4c5d2553001e9cc01e6f3003cc79800f4e600f379801e703375,0xc00030001040041080002000200402000000e4,0x445800111600025f800079bcc025f83cc2083b30079bcc01e6f3003cc79803cde600f379801e722395,0x0,0x1804c1220481,0x0,0x1804c1220481,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x400010000000000000082002020020800814e3,0x0,0x400010000000000000082002020020800814e3,0x0,0x280cc1220481,0x0,0x280cc1220481,0x280882220481,0x280882220481,0x281884220481,0x280882220481,0x280882220481,0x281884220481,0x281884220481],
[0x281884220481,0x280882220481,0x0,0x2400090002080402010082002020020800814e3,0x0,0x0,0x0,0x681cc1220481,0x0,0x681cc1220481,0x80000220481,0x481882220481,0x80000220481,0x481882220481,0x80000220481,0x81004220481,0x80000220481,0x81004220481,0x80000220481,0x0,0x2400090001040041020008800201012000203e4,0x0,0x2400090001040041040009000201012000203e4,0x8118007b66000fa98003cde600fb11bcfec46f3001e9cc01e6f3003cc79800f4e600f379801e703375,0x4400110001040041080002000200402000000e4,0xf379803cde6003d398408de6003d398408c000f30079bcc007a73003cde6003d398003d39801e64dc35,0xf307983cc1e600007983cc1e600007983cc0000f30079bcc007a73003cde6003d398003d39801e64dc35,0x0,0x4814c1220481,0x0,0x4814c1220481,0x481004220481],
[0x481882220481,0x481000220481,0x481882220481,0x481004220481,0x481004220481,0x481000220481,0x481004220481,0x481004220481,0x0,0x10400410010000000000082002020020800814e3,0x0,0x10400410010000400010082002020020800814e3,0xf307983cc1e600007983cc1e600007983cc0000f30079bcc007a73003cde6003d398003d39801e64dc35,0x0,0x1e600081180020460008118002046798bdda06739001e9cc01e6f3003cc79800f4e600f379801e703375,0x4000101040041080002000200400000000e4,0x1e6001ed98007b66000fa98003ea67983cc20877f0079bcc01e6f3003cc79803cde600f379801e7241f5,0x0,0x0,0x0,0x1e6003d39803cde60079f9801e7e679fdc5a06553001e9cc01e6f3003cc79800f4e600f379801e703375,0x20000801040041080002000200400000000e4,0x7980799e601e61e601ebb220461e6811db2007a730079bcc007a73003cde6003d398003d39801e64dc35,0x180802010010800410800ca0002184c820301904,0x0,0x1008040200108004108008a00021048840201104,0x1040041080002000200400000000e4,0x20100804001040041080102000220400804020e4,0x1040041080002000200400000000e4,0x40201008001040041080202000240401008040e4,0x0,0xf30007d4c001f623007d88de6102b11c0cac46f3001e9cc01e6f3003cc79800f4e600f379801e703375],
[0x20004800101040041080006000200c00020100e4,0xf3001e9cc00799e600f3799e601ed983cc2046f30079bcc01e6f3003cc79803cde600f379801e703d95,0x0,0x0,0x0,0x20400800001040041080002000200402000000e4,0x1e6007b66001e7e600798079f9801ed980079fa7300012fc001f530000f33ea6000fa98003cc1e610856,0xf3007980001e600001e9cc1e600007983cc0000f30079bcc007a73003cde6003d398003d39801e64dc35,0x400808010010800410800ca0002184c820301904,0x0,0x4008080200108004108008a00021048840201104,0x20000800001040041080002000200400000000e4,0x20100804001040041080102000220400804020e4,0x20100804001040041080102000220400804020e4,0x2020080800104004108020200024040100c060e4,0x0,0x1e600097e000222c00088b000222c798c57206739001e9cc01e6f3003cc79800f4e600f379801e703375,0x4000101040041080002000200400000000e4,0x3cc0011160007d4c0010230007d4c79a22c206ceb003cfcc01e6f3003cc79801e7e600f379801e707545,0x8000201040041080002000200402000000e4,0x0,0x0,0x79800f4e6003cfcc007a73003cfcc7983cc2083b30079bcc01e6f3003cc79803cde600f379801e722395,0x0,0x0,0x0,0x201040041080002000200402000000e4,0x0,0x1040041080002000200400000000e4,0x100004001040041080002000200400800000e4,0x1040041080002000200400000000e4,0x200008001040041080002000200401000000e4],
[0x0,0x1e600081180020460008118002046798bdda06739001e9cc01e6f3003cc79800f4e600f379801e703375,0x40005000101040041080006000200c00020100e4,0x1e6001ed98007b66000fa98003ea67983cc20877f0079bcc01e6f3003cc79803cde600f379801e7241f5,0x0,0x0,0x0,0x0,0x79800f4e6003cfcc007980f3f3003cfcc0079fa73000f6cc00454b0000f37b66001eda73088b3cc20276,0x0,0x4008100100108004108008a00021048820201104,0x40001000201040041080002000200402000000e4,0x4008100200108004108008a00021048840201104,0x40001000001040041080002000200400000000e4,0x4010100400104004108010200022040080c060e4,0x40201008001040041080202000240401008040e4,0x40201008001040041080202000240401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_962 : TreeBound (n := 4) 107 (programCode 0x4a2b07541e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x40000000300000000c0000000300000000c00020001000000100000400400001821000004100000010400000040800000101004000001010000004040000008000200010010873227,0x40000000300000000c0000000300000000c000200010000000001002000104008000400001001000004000100008000c0001004000001010000004040000008000200010010873227,0x0,0xf300003cc1e60f3079800079f9801ed980079f9801e60f3088b0001e60fa99e607983cc0798f30799556,0xf300003cc1e60f3079800079f9801ed980079f9800000f300f30000000fa99e607980000798f30799556,0xf300012fc1e64bf0798f3079f9801ed980079f9807980f37a730007980fa99e60798003d398f307a2d36,0x0,0xf303cc3cc2d90f30b6400079f9801ed980079f980f300f33db3000f300fa99e607980079f98f30799556,0x4000000110000000240000000300000000c2002000108000000004000000050000000200010000400040000400080001000100402000101008000404000000800020001001087fa27,0xf300012fc1e64bf0798f3079f9801ed980079f983cc00f6ccf3003cc00fa99e60798000fa98f3079b3b6,0x40000000300000000c0000000300000000c00020001000000000100200000c00800002000100008000400010000800020001004000001010000004040000008000200010010873227,0xf300012fc1e64bf0798f3079f9801ed980079f9879800f4e6f30079800fa99e60798000fa98f3079b3b6,0x40000000300000000c0000000300000000c00020001000000008400000021000821084000100010000400040000800100001004000001010000004040000008000200010010873227,0x0,0x40000000300000000c0000000300000000c0002000100000000900000002c0008210a0000100080000400100000800200001004000001010000004040000008000200010010873227,0x0,0xf30000b6400088b000079879f9801ed980079fa7300012fc0f30f30000fa99e607987980798f30799556,0x0,0x4000000110000000440000000900000001400020001000000100000400400001821000004100000010400000040800000101004000001010000004040000008000c00010010873227,0x0,0x0,0x0,0xf300003cc1e60f3079800079f9801ed980079f9800000f300f30000000fa99e607980000798f30799556,0xf3000408c1e60f3079800079f9801ed980079f9807980f37a730007980fa99e60798003d398f307a2d36,0x0,0xf30007d4c1e60f3079800079f9801ed980079f980f300f33db3000f300fa99e607980079f98f307a8856,0x400000011000000044000000090000000142002000108000000010000000020000000200010000400040000800080001000100402000101008000404020000800040001001087fa67,0xf303cc3cc1e60f3079800079f9801ed980079f983cc00f6ccf3003cc00fa99e60798000fa98f30799556,0x0,0xf303cc3cc1e60f3079800079f9801ed980079f9879800f4e6f30079800fa99e60798000fa98f30799556],
[0x0,0x0,0x0,0x0,0x0,0x4000000110000000140000000900000001000201000000204000001008000002008040029001000024001000288000000200012000380008000e000100008000100020001000fdea8,0xf300012fc00088b0000f307a73003cfcc0079f9802046000811f980f3102307983cca7107987983d1426,0x0,0xf300012fc00088b0000f307a73003cfcc0079f9802046000fa9f981e6102307983cc97e07987983d1426,0x400000005000000044000000050000000100008080000080080000080800000200801000080000008000450020800140000001100008000100080001000280001000200010025b1a8,0xf300012fc00088b0000f307a73003cfcc0079f980f4e6003d39f987981023001e9cc9896b987983e0726,0x0,0xf300012fc00088b0000f307a73003cfcc0079f980f4e60079f9f98f301023001e9cc98d37987983e0726,0x400021001000084004000000010000028042002000108000000000000000050000000200010000400040000400080001000100400000101000000404000000800000001001087fa27,0xf300012fc00088b0000f307a73003cfcc0079f98799e601e679f9bcc010230007d4c980e0987983d1426,0x400021001000084004000000010000020042002000108000000000000000040000000200010000800040001000080002000100400000101000000404000000800000001001087faa7,0xf3000222c00088b0000f30f3f3003cfcc0079f98f31e603cc79f9f98010230007d4c97fed987983d1936,0x0,0x0,0x0,0x0,0xf300003cc1e60f3079800079f9801ed980079fa7300012fc0f30f30000fa99e607987980798f30799556,0x0,0x0,0xf30007d4c001f530003cc07a73003cfcc0079f9802046000811f980f3102307983cca7107987983e0726,0x0,0xf30007d4c001f530003cc07a73003cfcc0079f9802046000fa9f981e6102307983cc97e07987983e0726,0xf3000f6cc003db30003cc07b66003d3980079f981e9cd11688b001e6011162d9079800f3798f307b9da6,0xf30007d4c001f530003cc07a73003cfcc0079f980f4e6003d39f987981023001e9cc9896b987983e0726,0x0,0xf30007d4c001f530003cc07a73003cfcc0079f980f4e60079f9f98f301023001e9cc98d37987983e0726,0x400020001000080004000000010000000042002000108000000000000000050000000200010000400040000400080001000100400000101000000404000000800000001001087fa27],
[0xf30007d4c001f530003cc07a73003cfcc0079f98799e601e679f9bcc010230007d4c980e0987983e0726,0x400020001000080004000000010000000042002000108000000000000000040000000200010000800040001000080002000100400000101000000404000000800000001001087faa7,0xf30007d4c001f530003cc0f3f3003cfcc0079f98f31e603cc79f9f98010230007d4c97fed987983e0c36,0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080010000100400000101000000404000000800000001001087fea7,0x0,0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x0,0x0,0x0,0xc00024101040041080102000220400804120e4,0x0,0x0,0x7987981e63cc0798798000000007983cc1e60f3003cfcc01e6f3003cc1e601e67980f35b201e703885,0x0,0x80400804001040041080102000220400804020e4,0x4400104801040041080102000220400804824e4,0x80400205001040041080102000220400805028e4,0x8400205001040041080102000220400805028e4,0x0,0x10400406001040041080102000220400806038e4,0x0,0x20400804001040041080102000220400804020e4,0x0,0x0,0xf30007d4c003db300079807a73003cfcc0079fa7301e63cc07a08b00010231e603cc97e07987983ebd66,0xf3001e9cc1e60f3001e60079f9801ed980079fa7300012fc0f30f30000fa99e607987980798f307d6156,0x8008200100108004108020a00024060080805104,0x0,0x4000100110000000140000801100000001000201000000201000002008000002008060029001000020001700288010000200012000380002000c000100008000100020001000fd7a8,0xf301e63cc07a08b0000f307a73003cfcc0079f9802046000811f980f3102307983cca7107987983d1426,0x0,0xf301e63cc07a08b0000f307a73003cfcc0079f9802046000fa9f981e6102307983cc97e07987983d1426],
[0x400008001000000044000080010000000100008080000080080000080800000200801000080000008000450020800140000001100008000100080001000280001000200010025b1a8,0xf301e63cc07a08b0000f307a73003cfcc0079f980f4e6003d39f987981023001e9cc9896b987983e0726,0x0,0xf301e63cc07a08b0000f307a73003cfcc0079f980f4e60079f9f98f301023001e9cc98d37987983e0726,0x400001001000004004000008010000010042002000108000000000000000050000000200010000400040000400080001000100400000101000000404000000800000001001087fa27,0xf301e63cc07a08b0000f307a73003cfcc0079f98799e601e679f9bcc010230007d4c980e0987983d1426,0x400001001000004004000008010000010042002000108000000000000000040000000200010000800040001000080002000100400000101000000404000000800000001001087faa7,0xf301e63cc07a08b0000f30f3f3003cfcc0079f98f31e603cc79f9f98010230007d4c97fed987983d1936,0x400008001000000044000080010000000100008080000080080000080800000200804000080000008000440000800140000001100008000100080001000200001000200010025b1a8,0x0,0x0,0x0,0x8008200200108004108020a00024060080805104,0x0,0xf307983cc0000000000000f4e6003cfcc0079fa7303ce22c07a08b00011162d903ccb6407987983cde26,0x904024101040041080102000220400804120e4,0x0,0x0,0x0,0x0,0x7a730079bcc00f3f300001e600fa983cc2046f3001e9cc01e6f3003cc0f300f3f300f397e01e703375,0x4100100001040041080102000220400804824e4,0x17bb811bcc007983cc1e600f4e6003cde60079fa7303ce22c03ccf300011162f761e67980798445a249f6,0x8040201001040041080102000220400805028e4,0x0,0x10040401001040041080102000220400806038e4,0x1040041080102000220400804020e4,0x20000800001040041080102000220400804020e4,0x1040041080102000220400804020e4,0x4000100000104004108010200022040080c060e4,0x8020200400108004108020a00024060080804104,0x0],
[0xf307983cc0000000000000f4e6003cfcc0079fa7303ce22c07a08b00011162d903ccb6407987983cde26,0x900024101040041080102000220400804120e4,0x0,0x0,0x0,0x0,0x1e9cc007a73000f4e600001e601ed983cc2046f30079bcc01e6f3003cc3cc03ccf300f4e6001e703d95,0x0,0x20002000040020000100100000100100040000000105008000020020001040080004000002010000020040000100100000100480000021500000204000001008000001002084eba7,0x3cfcc03cc003cfcfeb53079f9801ed980079fa7300012fc0f30f30000fa98079f987980798f30799556,0x0,0x79bcc01e6003d39c09b3079f9801ed980079fa7300012fc0f30f30000fa980f37987980798f30799556,0x1040041080102000220400804020e4,0x20100804001040041080102000220400804020e4,0x1040041080102000220400804020e4,0x4020100800104004108010200022040080c060e4,0x8020200800108004108020a00024060080804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1107 : TreeBound (n := 4) 107 (programCode 0x4a2b07541f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c80003cde6016cfd4c5d2553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x0,0xf307983cc200a3307983cde6017495b6ad2553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x804020101040041080002000200400000000e4,0x1e60f30f307aec800f30799e6044676cc219513003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x808020201040041080002000200400000000e4,0x0,0x0,0x1e60f307983ccf300798799e601ed983cc2046f30079bcc01e6f3003cde6003d39800f3f3001e703d95,0x0,0x0,0x0,0x800020201040041080002000200400000000e4,0x0,0x800020001040041080002000200400000000e4,0x900024001040041080006000200c00020100e4,0x800020001040041080002000200400000000e4,0xa00028001040041080006000200c00020100e4,0x25f800111600025f8000799e6044676cc219513003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x1400050001040041080002000200402000000e4,0x0,0x280cc1220481,0x0,0x280cc1220481,0x280882220481,0x280882220481,0x281884220481,0x280882220481,0x280882220481,0x281884220481,0x281884220481],
[0x281884220481,0x280882220481,0x0,0x2400090002080402010082002040021000814e3,0x0,0x0,0x0,0x681cc1220481,0x8118007b66000811800079f9801ed980079f9800f30f30f301e60f312fc1e600016c83cc0001e61556,0x681cc1220481,0x80000220481,0x481882220481,0x80000220481,0x481882220481,0x80000220481,0x81004220481,0x80000220481,0x81004220481,0x80000220481,0x0,0x0,0x0,0x0,0x1ed98007b66000fa9800799e601ed983cc2046f30079bcc01e6f3003cde6003d39800f3f3001e703d95,0x0,0x0,0x0,0x0,0x80000220481,0x280882220481,0x80000220481,0x280882220481],
[0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x4400110001040041000002000200402000000e4,0x0,0x4400110001040041000002000200402000000e4,0x0,0x0,0x4814c1220481,0x0,0x4814c1220481,0x481004220481,0x481882220481,0x481000220481,0x481882220481,0x481004220481,0x481004220481,0x481000220481,0x481004220481,0x481004220481,0x0,0x8400210008000000000082002040021000814e3,0x0,0x8400210008000000000082002040021000814e3,0x0,0x681cc1220481,0x0,0x681cc1220481,0x80000220481,0x481882220481],
[0x80000220481,0x481882220481,0x80000220481,0x81004220481,0x80000220481,0x81004220481,0x80000220481,0x0,0x400010000000000000082002040021000814e3,0x0,0x400010000000000000082002040021000814e3,0x400050001040041080002000200402000000e4,0x0,0x0,0x0,0x0,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x400010000000000000082002040021000814e3,0x7980001e60f3079800000000007982d91e603cc03cde601e63cc03ccf3001ed9800f3f3001e703885,0x400010000000000000082002040021000814e3,0x0,0x1e600081180020460008118002046798bdda06739001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x4000101040041080002000200400000000e4],
[0x1e6001ed98007b66000fa98003ea67983cc20877f0079bcc01e6f3003cde6003d39800f3f3001e7241f5,0x0,0x0,0xf33ccf6cc000f301e63cc0f4e6003cde60079fa73079a22c0000f300012fc1e600007983cc0000001df6,0x1e6003d39803cde60079f9801e7e679fdc5a06553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x20000801040041080002000200402000000e4,0x0,0x0,0x0,0x0,0x1040041080002000200400000000e4,0x20100804001040041080102000220400804020e4,0x1040041080002000200400000000e4,0x40201008001040041080202000240401008040e4,0x0,0x7d4c001e6f30079800000f3811bcfea60f3001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x20004800101040041080102000220400004020e4,0x1e9cc00799e600f3000000f37983cc1e60f30079bcc01e6f3003cde6003d39800f3f3001e703d95,0x0,0x0,0x0,0x20400804001040041080102000220402804020e4,0x20020800801040041080102000220402004024e4,0x20400801001040041080102000220402044028e4,0x20040801001040041080102000220400044028e4,0x0,0x20080802001040041080102000220400044038e4,0x20000800001040041080102000220400004020e4,0x20100804001040041080102000220400804020e4,0x20100804001040041080102000220400804020e4,0x20200808001040041080102000220400804060e4,0x0],
[0x1e600097e000222c00081180025f8798c57206739001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x4000101040041080002000200400000000e4,0x1e600097e0007d4c000fa980025f879a31f222b0d001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x8000201040041080002000200400000000e4,0x0,0x0,0x3cc007b66003cfcc007a73001ed987a76cc219513003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x0,0x1e60799e60079bcc01ea4581e67987b6abf1eda73001e9cc01e6f3003cc79800fa9800f3f3001e7036d5,0x40041001040041080002000200400040000e4,0x201040041080002000200400000000e4,0x80042001040041080002000200400040000e4,0x1040041080002000200400000000e4,0x100004001040041080002000200400000000e4,0x1040041080002000200400000000e4,0x200008001040041080002000200400000000e4,0x0,0x798000222c0007980000000798c57206553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x40005000101040041080202000240400008040e4,0xf3000084e4000f3000000007983cc1e60f3003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x0,0x0,0x0,0x0,0x40021000801040041080202000240402008044e4,0x0,0x40041001001040041080202000240400048048e4,0x40201000201040041080202000240401008040e4,0x40081002001040041080202000240400048058e4,0x40001000001040041080202000240400008040e4,0x40101004001040041080202000240401008060e4,0x40201008001040041080202000240401008040e4],
[0x40201008001040041080202000240401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1300 : TreeBound (n := 4) 107 (programCode 0x4a2b075420) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf300003cc1e60f300000007a73003cfcc0079fa7301e63cc0f388b00010231e6079897e0f30f30799766,0x0,0x807020101040041080202000240401008140e4,0x804020101040041080202000240401008140e4,0x6000101040041080202000240401008040e4,0x0,0x0,0x0,0x0,0x4004100101040041080202000240401008844e4,0x0,0x8004200101040041080202000240401009048e4,0x40004040101040041080202000240401008040e4,0x1000440010104004108020200024040100a058e4,0x40805020101040041080202000240401008140e4,0x2000480010104004108020200024040100c060e4,0x5000101040041080202000240401008040e4,0x40005000101040041080202000240401008040e4,0x0,0x2010001040041080202000240401008040e4,0x804038101040041080202000240401008140e4,0x2010001040041080202000240401008040e4,0x0,0x0,0x0,0x0,0x4020110801040041080202000240401008844e4,0x0,0x8040211201040041080202000240401009048e4,0x40200058001040041080202000240401008040e4,0x1008041220104004108020200024040100a058e4],
[0x1e6001ed98007b66000fa98003ea67983cc20877f0079bcc01e6f3003cc79803cde600f379801e7241f5,0x0,0x7980020460007d4c00111600081187983cc208b4b0079bcc01e6f3003cde6003d39800f4e6001e726055,0x40201018001040041080202000240401008040e4,0x0,0xf3000222c0004bf0000f30f4e6001ed980079fa735eede608118001e6111635283cc1e60f307983cfc26,0xf3000222c00088b0000f30f3f3003cfcc0079f980222c00088b7980f311160f30798d4a0f30f3079d936,0x0,0xf3000222c00088b0000f30f3f3003cfcc0079f980408c0010237981e611160f30798b640f30f3079d936,0xf3000222c0004bf0000f30f4e6001ed980079fb299eede60079800000111635283cc0000f307983cfc26,0xf3000222c00088b0000f30f3f3003cfcc0079f980f6cc003db37987981116001ed98b67db30f307acc36,0x0,0xf3000222c00088b0000f30f3f3003cfcc0079f981e9cc007a73798f301116003d398b733f30f307bbf36,0x0,0xf3000222c00088b0000f30f3f3003cfcc0079f9879bcc01e6f379bcc011160008118b650230f3079d936,0x0,0xf3000222c00088b0000f30f3f3003cfcc0079f98f33cc03ccf379f98011160008118b65f530f3079d936,0x0,0x0,0x0,0x0,0x0,0xf30b643cc0000f30000000f4e6001ed980079faec83cde6007980000011162d903cc0000f307983cddc6,0x0,0x0,0xf303cc3cc2d90f30b64000f3f3003cfcc0079f980408c0010237981e611160f30798b640f30f30799c76,0xf300003cc0000f3000000079f9801ed980079f9800000f3007980000010231e603cc0000f307983cd556,0xf303ce22c0f5ab709896407a73003cfcc0079f980f4e6003db37987981023001ed989897330f307ac726,0x0,0xf301e63cc16eeeb098d3007a73003cfcc0079f980f4e6007a73798f301023001ed9898d3f30f30b78726,0x400000101000000204000000210000000842002000108000000014000000050000000200010000400040000400080001000100420000101040000404000000800100001001087fa27,0xf3003cfcc01750b0980d907a73003cfcc0079f98799e601e6f379bcc010230008118980e830f30812f66],
[0x4000000210000000840000002100000008400020001000000000000200000c00800002000100008000400010000800020001004000001010000004040000008002000010010873227,0xf3003cfcc00f7bf097fe607a73003cfcc0079f98799e603ccf379f9801023000445897ff530f30812f66,0x0,0x4000000210000000840000002100000008400020001000000000000200010000800040000100100000400400000800020001004000001010000004040000008002000010010873227,0x0,0xf300003cc1e60f3097e0007a73003cfcc0079f9bcc1e61e60f37d4c0010231e6079897e0f30f30799766,0x0,0x40000010100000040400000081000000080002010000002040000008080000020080683290010000000010010040000040000120003419420008000080000000200010000810fdda8,0xf30007d4c001f530003cc07a73003cfcc0079f980204600088b7980f310230f30798d4a0f30f307ac726,0x0,0xf30007d4c001f530003cc07a73003cfcc0079f98020460010237981e610230798798d4a0f30f30b78726,0xf3000f6cc003db30003cc07b66003d3980079f981e7e702388b001e6010232d9079800f3f30f30b85da6,0xf30007d4c001f530003cc07a73003cfcc0079f980f4e6003db37987981023001ed989897330f307ac726,0x0,0xf30007d4c001f530003cc07a73003cfcc0079f980f4e6007a73798f301023001ed9898d3f30f307ac726,0x400020001000080004000000010000000042002000108000000000000000050000000200010000400040000400080001000100400000101000000404000000800000001001087fa27,0xf30007d4c001f530003cc07a73003cfcc0079f98799e601e6f379bcc010230008118980e830f307ac726,0x400020001000080004000000010000000042002000108000000000000000040000000200010000800040001000080002000100400000101000000404000000800000001001087faa7,0xf30007d4c001f530003cc0f3f3003cfcc0079f98f33cc03ccf379f98011160008118b65f530f307acc36,0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080010000100400000101000000404000000800000001001087fea7,0x0,0x400020001000000004000000010000000060002000180000000000000000400000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x0,0x0,0xf30b643cc0000f301e6000f4e6001ed980079faec83cde6007980000011162d903cc0000f307983cddc6,0xf303cc3cc3528f303cc0007a73003cfcc0079f980204600088b7980f310230f30798d4a0f30f30799766,0x0,0xf303cc3cc2d90f303cc000f3f3003cfcc0079f980408c0010237981e611160f30798b640f30f30799c76,0xf307983cc0000f301e600079f9801ed980079f9800000f3007980000010231e603cc0000f307983cd556,0xf30007d4c26268303cc0007a73003cfcc0079f980f4e6003db37987981023001ed989897330f307ac726,0x0,0xf30007d4c2635b303cc0007a73003cfcc0079f980f4e6007a73798f301023001ed9898d3f30f307ac726],
[0x400000101000000404000000810000001042002000108000000010000000020000000200010000400040000800080001000100420000101080000404100000800200001001087fa67,0xf3000222c26045703cc0007a73003cfcc0079f98799e601e6f379bcc010230008118980e830f3079d426,0x0,0xf3000222c2d988b03cc000f3f3003cfcc0079f98f33cc03ccf379f98011160008118b65f530f3079d936,0x0,0x0,0x0,0x0,0xf3000f6cc003db30007980f3f3003cfcc0079fa7303cc3cc0f388b00011161e60798b640f30f307b8276,0x0,0xf30bdfa2c0000f3001e600f4e6001ed980079fafbf08de6007980000011162d97d4c0000f307983cddc6,0xf303cc3cc361bf3001e6007a73003cfcc0079f980204600088b7980f310230f30798d4a0f30f30799766,0x0,0xf303cc3cc2e83f3001e600f3f3003cfcc0079f980408c0010237981e611160f30798b640f30f30799c76,0xf3001e9cc0000f3001e60079f9801ed980079f9800000f3007980000010231e603cc0000f307983cd556,0xf30007d4c271983001e6007a73003cfcc0079f980f4e6003db37987981023001ed989897330f307ac726,0x0,0xf30007d4c2728b3001e6007a73003cfcc0079f980f4e6007a73798f301023001ed9898d3f30f307ac726,0x400001001000002004000004010000008042002000108000000010000000020000000200010000400040000800080001000100420000101080000404100000800200001001087fa67,0xf3000222c26f757001e6007a73003cfcc0079f98799e601e6f379bcc010230008118980e830f3079d426,0x0,0xf3000222c2e8b8b001e600f3f3003cfcc0079f98f33cc03ccf379f98011160008118b65f530f3079d936,0x0,0x0,0x0,0x0,0x8008200100108004108020a00024060100805104,0xf303cc3cc0f388b0000f30f3f3003cfcc0079fa7303cc3cc0f388b00011161e60798b640f30f30799c76,0x8008200200108004108020a00024060100805104,0x0,0x1023000408c0010230003cde6016cfd4c5d2553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0xa04028101040041080202000240401008140e4],
[0x1023000f6cc001f5300000000007983cc1e60f3001e9cc01e6f3003cc00000f30000f300799e703375,0x0,0x0,0x0,0x0,0x4200108001040041080202000240401008844e4,0x0,0x8040201001040041080202000240401009048e4,0x798f303cc3cc0798f300000000007983cc1e60f3003cfcc01e6f3003cc00001e60000f31e601e703885,0x1004040100104004108020200024040100a058e4,0x1040041080202000240401008040e4,0x2000080000104004108020200024040100c060e4,0x1040041080202000240401008040e4,0x40001000001040041080202000240401008040e4,0x8020200400108004108020a00024060100804104,0x0,0x10230004bf00011160003cde6016cfd4c5d2553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0xa00028101040041080202000240401008140e4,0x2046001023000204600000000007983cc1e60f3003cfcc01e6f3003cc00001e60000f3016c9e703885,0xf303cc00003ccf301e63cc1e600007983cc0000f30079bcc007a73003cfcc003db30003cc0001e64dc35,0x0,0x0,0x0,0x0,0x0,0x0,0x40200048001040041080202000240401008040e4,0x0,0x1040041080202000240401008040e4,0x2010080400104004108020200024040100c060e4,0x1040041080202000240401008040e4,0x40201008001040041080202000240401008040e4],
[0x8020200800108004108020a00024060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_404 : TreeBound (n := 4) 107 (programCode 0x4a2b0754) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part102_405 part102_406 part102_407 part102_408 part102_489 part102_570 part102_651 part102_732 part102_733 part102_814 part102_815 part102_816 part102_817 part102_962 part102_1107 part102_1300

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1461 : TreeBound (n := 4) 107 (programCode 0x4a2b0755) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080890240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1463 : TreeBound (n := 4) 107 (programCode 0x4a2b075631) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081881240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1464 : TreeBound (n := 4) 107 (programCode 0x4a2b075632) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201000408008100102c02048040a00010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1465 : TreeBound (n := 4) 107 (programCode 0x4a2b075633) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081881240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1466 : TreeBound (n := 4) 107 (programCode 0x4a2b075634) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081881204481,0x1080000210481,0x1081881204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x181881220481,0x80400410000000000010080402020020800814e3,0x181881220481,0x80000220481,0x281002220481,0x80000220481,0x281002220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x10488811a12a2],
[0x10088811a12a2,0x0,0x10088811a12a2,0x10588811a12c2,0x10108811a12c2,0x10488811a12a2,0x10108811a12c2,0x10388811a1302,0x10208811a12e2,0x10188811a12c2,0x10208811a12e2,0x0,0x10408811a12a2,0x0,0x10408811a12a2,0x0,0x181881220481,0x0,0x181881220481,0x80000220481,0x281002220481,0x80000220481,0x281002220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x10488811a12a2,0x10088811a12a2,0x0,0x10088811a12a2,0x10588811a12c2,0x10108811a12c2,0x10488811a12a2,0x10108811a12c2,0x10388811a1302,0x10208811a12e2,0x10188811a12c2,0x10208811a12e2,0x0,0x10408811a12a2,0x0,0x10408811a12a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1547 : TreeBound (n := 4) 107 (programCode 0x4a2b075635) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081002240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1548 : TreeBound (n := 4) 107 (programCode 0x4a2b075636) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1549 : TreeBound (n := 4) 107 (programCode 0x4a2b075637) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081002240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1550 : TreeBound (n := 4) 107 (programCode 0x4a2b075638) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1551 : TreeBound (n := 4) 107 (programCode 0x4a2b075639) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1552 : TreeBound (n := 4) 107 (programCode 0x4a2b07563a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1553 : TreeBound (n := 4) 107 (programCode 0x4a2b07563b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1554 : TreeBound (n := 4) 107 (programCode 0x4a2b07563c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1555 : TreeBound (n := 4) 107 (programCode 0x4a2b07563d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1009cc8240481,0x80402002010000000020080802080022000814e3,0x1009cc8240481,0x80402004020100804020080802080022000834e3,0x1011888240481,0x1000008240481,0x1011888240481,0x80402000000000000020080802080022000814e3,0x1021008240481,0x1000008240481,0x1021008240481,0x1000008240481,0x1042108240501,0x802020040040800810c072080048060200402104,0x1042108240501,0x802020080040800810c062100048060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1572 : TreeBound (n := 4) 107 (programCode 0x4a2b07563e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8040200000408008104032080048060200402104,0x8000a00010408008104032080048060200402104,0x0,0x109002240481,0x140802010408008104032080048020e00402104,0x109002240481,0x25f8f3097e0001e60f3799e601e679801e679f9800f4e612fc1e600408c0f34bf00012fc03cc1e9716,0x209006240481,0x409002240481,0x209006240481,0x609006240481,0x409002240481,0x9002240481,0x409002240481,0x409002240481,0x809883240481,0x609006240481,0x809883240481,0x0,0x0,0x8000804020204008102010080048000a004221e4,0x1088885412a2,0x80008000202040081020100800480002004021e4,0x1088885412a2,0xb088885416c2,0x2088885414c2,0x8088885410a2,0x2088885414c2,0xe08888541d02,0x4088885418e2,0xa088885414c2],
[0x4088885418e2,0x9088885412a2,0x8088885410a2,0x0,0x8088885410a2,0x8033200040408008104032080048060200402304,0x8002200040408008104032080048060200402304,0x8060200400408008104032080048060200402104,0x8002200080408008104032080048060200406504,0x803b200100408008104032080048060200402904,0x8008200100408008104032080048060200402904,0x8032200040408008104032080048060200402304,0x8008200200408008104032080048060200403104,0x8040200000408008104032080048060200402104,0x8020200400408008104032080048060200402104,0x8040200000408008104032080048060200402104,0x8020200800408008104032080048060200406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1621 : TreeBound (n := 4) 107 (programCode 0x4a2b07563f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1009cc8240481,0x0,0x1031888204481,0x1021008210481,0x1031888204481,0x0,0x1021008208481,0x1021008210481,0x1021008208481,0xf300012fc0004bf000079bccf300f33cc01e67a7307a76d3981e60f303cc7b66001eda7303cc1e610f76,0x1021008210481,0x1021008200481,0x1021008210481,0x1021008210481,0x1021008220481,0x8000a0001040800810c072080044060080402104,0x1021008220481,0x0,0x1009cc8240481,0x0,0x104bde8204501,0x80002008000000000040081002000020400814e3,0x104bde8204501,0x0,0x1042108208501,0x80002008000000000040081002000020000814e3,0x1042108208501,0xf300012fc0004bf0000f31e67981e679801e67980f30408c001e60f303cc3ea6000fa98003cc1e610856,0x1042108210501,0x80002008000000000040081002000020000814e3,0x1042108210501],
[0x80002008000000000040081002000020000814e3,0x0,0x0,0x0,0x0,0x1011888240481,0x1000008240481,0x1011888240481,0x0,0x139cc8240481,0x0,0x139cc8240481,0x0,0x231888240481,0x8240481,0x231888240481,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x1021008240481,0x1000008240481,0x1021008240481,0x1000008240481,0x1042108240501,0x0,0x131888240481],
[0x120002400408008108142c02048040a00010104,0x131888240481,0x0,0x221008240481,0x8240481,0x221008240481,0x8240481,0x400008240481,0x8240481,0x400008240481,0x8240481,0x800008240481,0x8240481,0x800008240481,0x8240481,0x1042108240501,0x0,0x0,0x0,0x0,0x0,0x2539c8240501,0x8240481,0x2539c8240501,0x8240481,0x400008240481,0x8240481,0x400008240481,0x8240481,0x842108240501,0x8240481,0x842108240501],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1718 : TreeBound (n := 4) 107 (programCode 0x4a2b075640) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf307983cc0000f3000000799e601e679801e679f983db3f316c83cc00408c2d9000079800007983cddc6,0xf30b643cc0798f301e600799e601e679801e679f983db4e607983cc003cc1209000445800044583cde56,0x0,0x0,0xf307983cc001023079bcc1e67981e679801e679bcc003db307983cc003cc20460008118001ed983d4ed6,0xf307983cc001023079bcc1e67981e679801e679bcc003db307983cc003cc2046001ed98001ed983d4ed6,0xf307983cc0000f3000000799e601e679801e679f983db4e607983cc0042722d90f307980f307983cde56,0xf307983cc0798f3097e001e67981e679801e679bcc003db307983cc003cc3ea6000fa98003d3983cd556,0xf307983cc0089a307ba2c1e67981e679801e679bcc003db307983cc003ccf4e6000811800f3798411ad6,0xf307983cc007a7307b6601e67981e679801e679bcc003db307983cc003ccf4e600f379800f379840a156,0xf307983cc001023079bcc1e67981e679801e679bcc003db307983cc003cc204603cc798001ed983d4ed6,0xf307983cc01e6f30811801e67981e679801e679bcc003db307983cc003cde7e60079f9801e67984fd156,0xf307983cc0000f3000000799e601e679801e679f983db4e607983cc00408c2d90f3079800007983cde56,0xf307983cc0000f3000000799e601e679801e679f983db4e607983cc003ea62d9079879807987983cde56,0xf307983cc0000f3000000799e601e679801e679f983db4e607983cc00408c2d90f3079800007983cde56,0xf307983cc0000f30798001e67981e679801e679bcc003db307983cc003db31e603cc7980f307983cd556,0x0,0x0,0x1088885412a2,0x0,0x1088885412a2,0xb088885416c2,0x2088885414c2,0x8088885410a2,0x2088885414c2,0xe08888541d02,0x4088885418e2,0xa088885414c2,0x4088885418e2,0x9088885412a2],
[0x8088885410a2,0x0,0x8088885410a2,0x0,0xf307983cc0000f3079800799e601e679801e679f983db3f316c83cc00408c2d9000079800007983cddc6,0xf307983cc0002d90798001e67981e679801e679bcc003db307983cc003cc05b2000445800044583cd556,0x0,0x0,0xf30b643cc0798f3079800799e601e679801e679f983db4e607983cc00436cc5903cc798001ed983cde56,0xf307983cc0798f30798001e67981e679801e679bcc003db307983cc003cc2046001ed98001ed983cd556,0x0,0xf307983cc0798f30798001e67981e679801e679bcc003db307983cc003cc3ea6000fa98003d3983cd556,0xf307983cc07a8230798001e67981e679801e679bcc003db307983cc003ccf4e6000811800f37983d4ed6,0xf307983cc0010230798001e67981e679801e679bcc003db307983cc003ccf4e600f379800f37983d4ed6,0xf30b643cc0798f3079800799e601e679801e679f983db4e607983cc003eadc5903cc798001ed983cde56,0xf307983cc003db30798001e67981e679801e679bcc003db307983cc003cde7e60079f9801e67983f34d6,0x0,0x0,0x0,0x0,0x0,0x0,0x1088885412a2,0x0,0x1088885412a2,0xb088885416c2,0x2088885414c2,0x8088885410a2,0x2088885414c2,0xe08888541d02,0x4088885418e2,0xa088885414c2],
[0x4088885418e2,0x9088885412a2,0x8088885410a2,0x0,0x8088885410a2,0x8022200040408008104022100048060200804504,0x8002200040408008104022100048060200804504,0x0,0x0,0x1488885412a2,0x0,0x1488885412a2,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x811888240481,0x410000240481,0x811888240481,0x10000240481,0x8002200080408008104022100048060200804504,0x802b200100408008104022100048060200805704,0x8008200100408008104022100048060200805104,0x8022200040408008104022100048060200804504,0x8008200200408008104022100048060200805104,0x0,0xf307983cc000000000000799e600f33cc01e679f983db4e607b69cc00408c2d90f30b643cc07983cde26,0x1488885412a2],
[0x0,0x1488885412a2,0x241002240481,0x40000240481,0x241002240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x8020200400408008104022100048060200804104,0x0,0xf307983cc000000000000799e600f33cc01e679f983db4e607b69cc00408c2d90f30b643cc07983cde26,0x0,0x0,0x0,0x241002240481,0x40000240481,0x241002240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481],
[0x8020200800408008104022100048060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1462 : TreeBound (n := 4) 107 (programCode 0x4a2b0756) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part102_1463 part102_1464 part102_1465 part102_1466 part102_1547 part102_1548 part102_1549 part102_1550 part102_1551 part102_1552 part102_1553 part102_1554 part102_1555 part102_1572 part102_1621 part102_1718

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1847 : TreeBound (n := 4) 107 (programCode 0x4a2b0757) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080890240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1849 : TreeBound (n := 4) 107 (programCode 0x4a2b075831) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081001210481,0x10804c1204481,0x10804c1204481,0x1080881208481,0x1081881218481,0x1080881208481,0x1080001200481,0x1081001210481,0x1080001200481,0x1081001210481,0x1080001200481,0x0,0x100a0e1220481,0x1022081220481,0x100a0e1220481,0x80402000120004802900880022020020800814e3,0x10120c1220481,0x10320c1220481,0x10120c1220481,0x1042101220501,0x1022081220481,0x1002001220481,0x1022081220481,0x80402000020000800000880022020020800814e3,0x1042101220501,0xf303cc3cc0f30f300f300799e601e679803cc7aec8b7337983cc1e6007f322d90f3079807983cc1e7e56,0x1042101220501,0xf303cc3cc0f30f301e600799e601e679803cc7aec8b734e60f30798007f322d90f307981e60f30799e56,0x0,0x1000880120022],
[0x80006000104040101000806820820500804120e4,0x8000a000204080102000880022080020100814e3,0xf3000222c00088b0000f3799e601e679803cc7aecc8351607983cc0007b662d981180000798003cc3cb6,0x1010882120442,0x1010882120442,0x1000880120022,0x1010882120442,0x1030886320c82,0x1020886320c82,0x1010882120442,0x1020886320c82,0x80102004020100804000880022080020800834e3,0xf300f33cc0f30f300f3003cc7980f379803cc7a7300079f983cd1160079f99e6079879807983cc1e7556,0x80202008040201008000880022080021000854e3,0xf301e63cc0798f301e6003cc7980f379803cc7a730007a7307992fc0079f99e6079879807987983cd556,0x0,0x100a0e1220481,0x1022081220481,0x100a0e1220481,0x0,0x10120c1220481,0x10320c1220481,0x10120c1220481,0x1042101220501,0x1022081220481,0x1002001220481,0x1022081220481,0x0,0x1042101220501,0x0,0x1042101220501,0x0],
[0x0,0x1000880120022,0x80006000104040101000807020840601008140e4,0x0,0xf3000222c00088b0000f37987981e61e603cc79803cc1e60f30904bcc7b660f30798b640f30f3811d756,0x1010882120442,0x1010882120442,0x1000880120022,0x1010882120442,0x1030886320c82,0x1020886320c82,0x1010882120442,0x1020886320c82,0x0,0xf300f33cc0f30f300f3003cc7980f379803cc7a730007b660f31116007a731e603cc7980f30f3097f556,0x0,0xf301e63cc0798f301e6003cc7980f379803cc7a730007a7307992fc007a731e603cc7980f307983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1930 : TreeBound (n := 4) 107 (programCode 0x4a2b075832) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081886204481,0x1080004210481,0x1081886204481,0x1080004210481,0x1080004208481,0x1080004200481,0x1080004208481,0x1080004200481,0x1080004210481,0x1080004200481,0x1080004210481,0x1080004200481,0x0,0x100a0e5220481,0x1020004220481,0x100a0e5220481,0x80402000000000000000080402020020800814e3,0x1011886220481,0x1000004220481,0x1011886220481,0x1000004220481,0x1020004220481,0x1000004220481,0x1020004220481,0x1000004220481,0x0,0x80102004004040101000804020880100804120e4,0x0,0x80202008004040101000804020880201008140e4,0x0,0x10488811a12a2],
[0x10088811a12a2,0x0,0x10088811a12a2,0x10588811a12c2,0x10108811a12c2,0x10488811a12a2,0x10108811a12c2,0x10388811a1302,0x10208811a12e2,0x10188811a12c2,0x10208811a12e2,0x0,0x10408811a12a2,0x0,0x10408811a12a2,0x0,0x100a0e5220481,0x1020004220481,0x100a0e5220481,0x0,0x1011886220481,0x1000004220481,0x1011886220481,0x1000004220481,0x1020004220481,0x1000004220481,0x1020004220481,0x1000004220481,0x0,0x0,0x0,0x0],
[0x0,0x10488811a12a2,0x10088811a12a2,0x0,0x10088811a12a2,0x10588811a12c2,0x10108811a12c2,0x10488811a12a2,0x10108811a12c2,0x10388811a1302,0x10208811a12e2,0x10188811a12c2,0x10208811a12e2,0x0,0x10408811a12a2,0x0,0x10408811a12a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2011 : TreeBound (n := 4) 107 (programCode 0x4a2b075833) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081001210481,0x10804c1204481,0x10804c1204481,0x1080881208481,0x1081881218481,0x1080881208481,0x1080001200481,0x1081001210481,0x1080001200481,0x1081001210481,0x1080001200481,0x0,0x100a0e1220481,0x1022081220481,0x100a0e1220481,0x80402000220008802a01080042020020800815e3,0x10120c1220481,0x10320c1220481,0x10120c1220481,0x1042101220501,0x1022081220481,0x1002001220481,0x1022081220481,0x80402000020000800001080042020020800814e3,0x1042101220501,0x0,0x1042101220501,0x0,0x0,0xc00030004080102001080042004022000814e3],
[0x109cf983cc1e6003d3983cc1e600007983cc0000003d398003d39801e9cfcc003cc0000408c001e64dc35,0x80880120022,0xf362b83cc1e600016c83d96bb280fab69cfcc79803d398003d39801e9cfd57e3cc0f30408c001e64dc35,0x280882120442,0x280882120442,0x80880120022,0x280882120442,0x680886320c82,0x480886320c82,0x280882120442,0x480886320c82,0x0,0x0,0x0,0x0,0x0,0x100a0e1220481,0x1022081220481,0x100a0e1220481,0x0,0x10120c1220481,0x10320c1220481,0x10120c1220481,0x1042101220501,0x1022081220481,0x1002001220481,0x1022081220481,0x0,0x1042101220501,0x0,0x1042101220501,0x0],
[0x0,0x0,0x0,0x80880120022,0x0,0x280882120442,0x280882120442,0x80880120022,0x280882120442,0x680886320c82,0x480886320c82,0x280882120442,0x480886320c82,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2092 : TreeBound (n := 4) 107 (programCode 0x4a2b075834) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1080000210481,0x10804c1204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x0,0x80400410000000000010080402020020800814e3,0x0,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x10488811a12a2],
[0x10088811a12a2,0x0,0x10088811a12a2,0x10588811a12c2,0x10108811a12c2,0x10488811a12a2,0x10108811a12c2,0x10388811a1302,0x10208811a12e2,0x10188811a12c2,0x10208811a12e2,0x0,0x10408811a12a2,0x0,0x10408811a12a2,0x0,0x0,0x0,0x0,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x480004220481,0x80000220481,0x480004220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x10488811a12a2,0x10088811a12a2,0x0,0x10088811a12a2,0x10588811a12c2,0x10108811a12c2,0x10488811a12a2,0x10108811a12c2,0x10388811a1302,0x10208811a12e2,0x10188811a12c2,0x10208811a12e2,0x0,0x10408811a12a2,0x0,0x10408811a12a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2173 : TreeBound (n := 4) 107 (programCode 0x4a2b075835) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080882240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2174 : TreeBound (n := 4) 107 (programCode 0x4a2b075836) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2175 : TreeBound (n := 4) 107 (programCode 0x4a2b075837) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080882240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2176 : TreeBound (n := 4) 107 (programCode 0x4a2b075838) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2177 : TreeBound (n := 4) 107 (programCode 0x4a2b075839) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2178 : TreeBound (n := 4) 107 (programCode 0x4a2b07583a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2179 : TreeBound (n := 4) 107 (programCode 0x4a2b07583b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2180 : TreeBound (n := 4) 107 (programCode 0x4a2b07583c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2181 : TreeBound (n := 4) 107 (programCode 0x4a2b07583d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1804c8240481,0x80400410010000400020080802080022000814e3,0x1804c8240481,0x0,0x80004800120004802920080802080022000814e3,0x108880140022,0x80008800220008802a20080802080022000815e3,0x108880140022,0x110882140442,0x110882140442,0x100880140022,0x110882140442,0x130886340c82,0x120886340c82,0x110882140442,0x120886340c82,0x100880140022,0x408c0010230001f5300799e601e679803cc7aecc8351607983ea6007d4c2d988b00012fc0003cc3cb6,0x80200808020200808020080802080022000854e3,0x0,0x280888240481,0x80400010000000000020080802080022000814e3,0x280888240481,0x80008240481,0x481008240481,0x80008240481,0x481008240481,0x80008240481,0x0,0x80a0e8240481,0x8880140022],
[0x80a0e8240481,0x8880140022,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x609888240481,0x1e600097e0007b6600079bcc7980f379803cc7a7300079803cc1e60f37d4c1e60f307983cc0001e61556,0x609888240481,0x7980020460007b66000f3799e601e679803cc7a7344691607983cc0007d4c1e688b00003cc0003cc3cb6,0x411008240481,0x8240481,0x411008240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0],
[0x80a0e8240481,0x0,0x80a0e8240481,0x0,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x0,0x0,0x0,0x0,0x8120c8240481,0x8240481,0x8120c8240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40008240481,0x8240481,0x40008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2278 : TreeBound (n := 4) 107 (programCode 0x4a2b07583e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108882240481,0xc00024104040101020100800880006004120e4,0x108882240481,0x140004020404010102010080088000a004221e4,0x209886240481,0x409886240481,0x209886240481,0x609886240481,0x409886240481,0x409886240481,0x409886240481,0x609886240481,0x400000021000000084000000210000000c00020001000000100000600410001821000004100000010400000040800002001004000001010000004040000008100000010010873227,0x609886240481,0x2000000028000000090000000220000000c00020001000000100000600410001821000004100000010400000040800002001004000001010000004040000008100000010010873227,0x0,0xf30000b6400088b000079bcc7980f379803cc799e6007b660f301e6007d4c1e60f307983cc0f30799556,0x0,0x108882240481,0x0,0x108882240481,0x0,0x209886240481,0x409886240481,0x209886240481,0x609886240481,0x409886240481,0x409886240481,0x409886240481,0x609886240481],
[0x0,0x609886240481,0x0,0x0,0x0,0x8000804020404010102010080088000a004221e4,0x1088885412a2,0x80008000204040101020100800880002004021e4,0x1088885412a2,0xb088885416c2,0x2088885414c2,0x8088885410a2,0x2088885414c2,0xe08888541d02,0x4088885418e2,0xa088885414c2,0x4088885418e2,0x9088885412a2,0x8088885410a2,0x0,0x8088885410a2,0x8022200880408010104022080088060200804504,0x8002200040408010104022080088060200804504,0x0,0x111886240481,0x1488885412a2,0x111886240481,0x1488885412a2,0x210004240481,0x10004240481,0x210004240481,0x10004240481],
[0x410004240481,0x10004240481,0x410004240481,0x10004240481,0x811886240481,0x410004240481,0x811886240481,0x410004240481,0x8002200080408010104022080088060200804504,0x802a200100408010104022080088060200805504,0x8008200100408010104022080088060200805104,0x8022200080408010104022080088060200804504,0x8008200200408010104022080088060200805104,0x0,0x142dca240501,0x1488885412a2,0x142dca240501,0x1488885412a2,0x24088c240481,0x842108240501,0x24088c240481,0x40008240481,0x441008240481,0x40008240481,0x441008240481,0x40008240481,0x842108240501,0x842108240501,0x842108240501,0x40008240481,0x8020200400408010104022080088060200804104,0x0],
[0x142dca240501,0x0,0x142dca240501,0x0,0x24088c240481,0x842108240501,0x24088c240481,0x40008240481,0x441008240481,0x40008240481,0x441008240481,0x40008240481,0x842108240501,0x842108240501,0x842108240501,0x40008240481,0x8020200800408010104022080088060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2391 : TreeBound (n := 4) 107 (programCode 0x4a2b07583f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1804c8240481,0x0,0x681888204481,0x481008210481,0x681888204481,0x0,0x481008208481,0x16c800111600016c8003cc7980f379803cc7a730007981e610230007982046001ed98001e60f3181d6,0x481008208481,0x481008210481,0x481008210481,0x481008200481,0x481008210481,0x481008210481,0x0,0x0,0x0,0x0,0x1804c8240481,0x0,0xc01010000820022840081002000820020814e3,0x401010000000000040081002000020400814e3,0x1401010001020042840081002001020040814e3,0x401010000000000040081002000021000814e3,0x0,0x25f800097e00025f8003cc7980f379803cc7a730007987983db30007982046001ed98001e63cc2ee56,0x0,0x401010000000000040081002000020000814e3,0x401010000000000040081002008020200814e3,0x401010000000000040081002000020000814e3,0x401010000000000040081002010020400814e3],
[0x401010000000000040081002000020000814e3,0x0,0x0,0x401010000000000040081002040021000814e3,0x0,0x280888240481,0x0,0x709cc8240481,0x0,0x709cc8240481,0x0,0x611888240481,0x8240481,0x611888240481,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x280888240481,0x80008240481,0x481008240481,0x80008240481,0x481008240481,0x80008240481,0x0,0x80a0e8240481,0x20400802020080802040081002080022000814e3],
[0x80a0e8240481,0x0,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x609888240481,0x20004800104040101020102000880502004020e4,0x609888240481,0x0,0x411008240481,0x8240481,0x411008240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0],
[0x80a0e8240481,0x0,0x80a0e8240481,0x0,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x0,0x0,0x40005000104040101040202000880602008040e4,0x0,0xf30d4a0001e600001e63cc1e6000000000000007980798f300f33cc03cfcc003db30007d4c001e68a8c5,0x8120c8240481,0x8240481,0x8120c8240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40008240481,0x8240481,0x40008240481],
[0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2520 : TreeBound (n := 4) 107 (programCode 0x4a2b075840) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf307983cc0000f3000000799e600f379803cc79f983db3f307983cc007d4c2d9000079800007983cddc6,0x0,0x0,0x0,0xf307983cc0000f30798003cc7980f379803cc79bcc007a7307983cc0079801e600007980f307983cd556,0xf303db6cc2dec1303db30798f301e63cc03cc79f983cc1e60f6cfcc007983ea6000fe64001f5307b8276,0x0,0xf303cc3cc2dcdb303cc00798f301e63cc03cc79f983cc1e60f6cfcc007987b66001f164003db30799c76,0xf30408fcc2efd730408c0798f301e63cc03cc79f983cc1e60f6cfcc007b661e6083096400f3f30813476,0xf3003cfcc1fcd73003cc03ccf301e63cc03cc79bcc1e61e60f6cfcc00799e7e6007a17e00f3f30812f66,0xf303cc3cc2dcdb303cc00798f301e63cc03cc79f983cc1e60f6cfcc007b661e607b7164003db30799c76,0xf3003cfcc1f53f3003cc03ccf301e63cc03cc79bcc1e61e60f6cfcc00799e7e600f397e01e6f30812f66,0x0,0x0,0x0,0xf300003cc1e60f30000003ccf301e63cc03cc79bcc1e61e60f6cfcc007a731e6079897e0f30f30799766,0x0,0x0,0x1088885412a2,0x0,0x1088885412a2,0xb088885416c2,0x2088885414c2,0x8088885410a2,0x2088885414c2,0xe08888541d02,0x4088885418e2,0xa088885414c2,0x4088885418e2,0x9088885412a2],
[0x8088885410a2,0x0,0x8088885410a2,0x0,0xf307983cc0000f3079800799e600f379803cc79f983db3f307983cc007d4c2d9000079800007983cddc6,0xf307983cc0002d90798003cc7980f379803cc79bcc007a7307983cc0079805b2000445800044583cd556,0x0,0x0,0x0,0xf303cc3cc3528f30798003ccf301e63cc03cc79bcc1e61e60f6cfcc007983ea6000fc7e001f530799766,0x0,0xf303cc3cc2d90f3079800798f301e63cc03cc79f983cc1e60f6cfcc007987b66001f164003db30799c76,0x0,0xf3000f6cc1e7f53079800798f301e63cc03cc79f983cc1e60f6cfcc00799e7e6007a36400f3f307b8276,0x0,0xf3000f6cc1e9db3079800798f301e63cc03cc79f983cc1e60f6cfcc0079bcde600f3b6401e6f307b8276,0x0,0x0,0x0,0x0,0x0,0x0,0x1088885412a2,0x0,0x1088885412a2,0xb088885416c2,0x2088885414c2,0x8088885410a2,0x2088885414c2,0xe08888541d02,0x4088885418e2,0xa088885414c2],
[0x4088885418e2,0x9088885412a2,0x8088885410a2,0x0,0x8088885410a2,0x8022200880408010104022100088060200804504,0x8002200040408010104022100088060200804504,0x0,0x0,0x1488885412a2,0x0,0x1488885412a2,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x8120c8240481,0x410000240481,0x8120c8240481,0x10000240481,0x8002200080408010104022100088060200804504,0x802a200100408010104022100088060200805504,0x8008200100408010104022100088060200805104,0x8022200080408010104022100088060200804504,0x8008200200408010104022100088060200805104,0x0,0x0,0x1488885412a2],
[0x0,0x1488885412a2,0x240882240481,0x40000240481,0x240882240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x8020200400408010104022100088060200804104,0x0,0x0,0x0,0x0,0x0,0x240882240481,0x40000240481,0x240882240481,0x40000240481,0x440004240481,0x40000240481,0x440004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481],
[0x8020200800408010104022100088060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_1848 : TreeBound (n := 4) 107 (programCode 0x4a2b0758) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part102_1849 part102_1930 part102_2011 part102_2092 part102_2173 part102_2174 part102_2175 part102_2176 part102_2177 part102_2178 part102_2179 part102_2180 part102_2181 part102_2278 part102_2391 part102_2520

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2649 : TreeBound (n := 4) 107 (programCode 0x4a2b0759) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1081010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2650 : TreeBound (n := 4) 107 (programCode 0x4a2b075a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2651 : TreeBound (n := 4) 107 (programCode 0x4a2b075b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1081010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2652 : TreeBound (n := 4) 107 (programCode 0x4a2b075c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2653 : TreeBound (n := 4) 107 (programCode 0x4a2b075d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x100a0f0240481,0x80402002020080802080082002080022000814e3,0x100a0f0240481,0x0,0x80402000120004802900880022080022000814e3,0x0,0x103a0e6204481,0x80102000020000800000080402000020400814e3,0x103a0e6204481,0x80002000020000800000080402000020000814e3,0x1022084208481,0x80002000020000800000080402000020000814e3,0x1022084208481,0x80402000020000800000080402020020800814e3,0x106218c210501,0x80002000020000800000080402000020000814e3,0x106218c210501,0x0,0x80402000020000800000080402020020800814e3,0x0,0x0,0x0,0x80402000220008802a01080042080022000815e3,0x0,0x100a0e1204481,0xf300012fc0004bf0000f30f37a730079800f379801e61e6097e1e61e61e605b21e63cc1e603cc1e61556,0x100a0e1204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481],
[0x0,0x1042108210501,0x1002000200481,0x1042108210501,0x0,0x0,0x0,0x0,0x0,0x80402000420010802402080082080022000816e3,0x80402000020000800000080002080022000814e3,0x80402000820020802804080102080022000814e3,0x0,0x0,0x108882140442,0x0,0x108882140442,0x208882140442,0x208882140442,0x208882140442,0x208882140442,0x609882340c82,0x409882340c82,0x208882140442,0x409882340c82,0x208882140442,0x0,0x0,0x0,0x8040200102004080000808020208002200081ce3,0x80402000020000800000080002080022000814e3,0x80402002020080802010080402080022000814e3],
[0x0,0xc00020120004802900882822080022000814e3,0x108084040022,0x1400040220008802a01082842080022000815e3,0x108084040022,0x409084240862,0x208084040022,0x8084040022,0x208084040022,0x409084240862,0x409084240862,0x8084040022,0x409084240862,0x8084040022,0x0,0x0,0x0,0x80402004020100804020080802080022000834e3,0x0,0xc00020820020802804082402080022000814e3,0x0,0x1400040820020802804082402080022000814e3,0x0,0x2400082020080802010082402080022000814e3,0x20a8885414c2,0x8088040022,0x20a8885414c2,0x409088240862,0x409088240862,0x8088040022,0x409088240862,0x8088040022],
[0x1e60011160003ea6000fa98079801ed987980799e60f31e6222c1e60f33cc222cf300f33cc03cc1e93b6,0x0,0x3cc001023000408c0010230079801ed98f300799e61e61e625f81e61e63cc25f8f301e63cc07983cf3b6,0x0,0x104a1e8204501,0x1dcd6500000773597b9acbdcd6577359b735947735b1cd653b9acaee6b45cd653b9ad1735943b9b059aca3b9acdb9aca3b9b059acaee6b283b9b059aca0ee6b45cd650773770d6507735b1cd6507735940000077359400001dcd82cd6500ef59932800ee6c166b280ef5d54810fd99,0x104a1e8204501,0x0,0x1042108208501,0x0,0x1042108208501,0x0,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20a8885414c2,0x8088040022,0x20a8885414c2,0x409088240862,0x409088240862,0x8088040022],
[0x409088240862,0x8088040022,0x1e60011160003ea60011160079801ed99e60079bcc3cc0f3222c3cc3cc3cc222cf303cc3cc03cc9813b6,0x0,0x3cc001023000408c0010230079801ed98f30079bcc1e60f325f83cc1e63cc25f8f301e63cc07983cf3b6,0x10120d0240481,0x80402000020000800080082002080022000814e3,0x10120d0240481,0x80402004020100804080082002080022000834e3,0x1022090240481,0x1002010240481,0x1022090240481,0x80402000020000800080082002080022000814e3,0x1042110240501,0x0,0x1320d0240481,0x12000240c188080108060e00408040a00010104,0x1320d0240481,0x0,0x408c0010230001f535b2f4e6000079879807a73482622c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0x408c00088b0001f535b2f4e6001ed9879807aece685ed99e63ea60f33cc1e688b00012fc0003cc3c26,0x1f5300088b0001f5307980798079f98798079807a730079812fc7a733cc1e7023000408c0003eb0d36,0x0,0x1f5300088b0001f53079807980f379879807980f3f3003cc222cf3f33cc1e7f530007d4c0003cd26b6,0x408c0010230001f535b36e661e6079879807b1a7686e098003cfccf33cc2d9c5700f33cc0003ea9cb6,0x1f5300088b0001f5307980799e6079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x408c0010230001f535b2f4e6001ed9879807aecc825e607983ea60f33cc1e688b00012fc0003cc3cb6,0x1f5300088b0001f53079807980007987980798798f301e6003d398f33cc1e60f300003cc0003cc33b6,0x408c0010230001f535b2f4e6001ed9879807aecc825e607983ea60f33cc1e688b00012fc0003cc3cb6],
[0x1f5300088b0001f530798079801ed987980799e60f31e61e63ea60f33cc1e60f300012fc0003cc33b6,0x0,0x1f5300088b0001f530798079801ed98798079bcc0f30f31e6408c0f33cc1e60f300012fc0003cc33b6,0x222090240481,0x42000840e608080108073200408043200042304,0x222090240481,0x1e7e60079f9800f3f33d398f33db33cc79807a7307a76cc07b75300f33cc1e60f307a76cc001e9dcf76,0x402010240481,0x2010240481,0x402010240481,0x2010240481,0x802010240481,0x2010240481,0x802010240481,0x2010240481,0x1042110240501,0x0,0x0,0x10a0f0204481,0x880026120184806980082002034820400834e3,0x10a0f0204481,0x0,0x0,0x800020020000800080082002080020000814e3,0x0,0x900024120104806980082002080020800834e3,0x16a1f0210501,0x102010200481,0x16a1f0210501,0x800020020000800080082002000820000814e3,0x14a1f0220501,0x800020020000800080082002004020000814e3],
[0x14a1f0220501,0x102010200481,0x0,0x0,0xc62190230501,0x0,0x0,0x462190208501,0x0,0x462190208501,0x0,0xc62190210501,0xc62190230501,0xc62190210501,0xc62190230501,0xc62190220501,0xc62190230501,0xc62190220501,0xc62190230501,0x0,0x10a0f0204481,0x1000040020000800080082002000020400814e3,0x10a0f0204481,0x0,0x0,0x0,0x0,0x0,0x16a1f0210501,0x102010200481,0x16a1f0210501,0x1008040220008802a80082002001022840815e3],
[0x14a1f0220501,0x0,0x14a1f0220501,0x102010200481,0x0,0x0,0x0,0x0,0x0,0x408c00081180020466a66e66001ed98f3007b29a86ce831e6408c1e63cc1e6c5700012fc0003cc3c26,0x204600081180020460f300798079f98f30079807b660079812fc7b663cc1e7023000408c0004096d36,0x0,0x204600081180020460f3007980f3798f3007980f4e6003cc222cf4e63cc1e7f530007d4c0003cd26b6,0x2b962f6000000ae58bd80000015cb17b0000000ae58bd800000ae58bd8000000ae58bd8000000002b3fb0000acff6cfec0002b3fdb3ff0df880002b3fdb3fb0002b3fbacfec0002b3fb00000acfec00000002b3fb00567f6000000acff168166fc41037e200000206fc967fb67f6159fd80000000567f600000057d95d80000015f657602b3fb0159fd80159fd8567f600000081bf104375ce34ac,0x204600081180020460f30079bcc0798f3007983cde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x0,0x408c001023000204600000f46cbcfcde600798f3799e9ced979f9bcc3cc0000f30b6622c0007985936,0x0,0x408c0010230002046000f3f46cdb5cde60079bcc799f532d9b8263cc3cc00088b079b15c0007985936,0x0,0x408c0010230002046000f3f46cbcfcde60079f9879a0462d97d4c3cc3cc00088b079a22c0007985936,0x0,0x0,0x2080086420190806480080402080022000836e3,0x0,0x0,0x2120c2240481,0x202000240481,0x2120c2240481,0x2521ca240501,0x2721c4240501,0x202000240481],
[0x2721c4240501,0x2521ca240501,0x2521c8240501,0x2721ce240501,0x2521c8240501,0x202000240481,0xf6cc003db30007b661e9ccf379803cde6007a73079fd4c0f4f5303cc3cc1e60f3079fd4c001eda8f76,0x0,0x0,0x0,0x0,0x0,0x2120c2240481,0x202000240481,0x2120c2240481,0x2521ca240501,0x2721c4240501,0x202000240481,0x2721c4240501,0x2521ca240501,0x2521c8240501,0x2721ce240501,0x2521c8240501,0x202000240481,0x0,0x0,0x0,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x462190240501,0x2010240481,0x462190240501,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2959 : TreeBound (n := 4) 107 (programCode 0x4a2b075e71) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001004008080108060200408040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2960 : TreeBound (n := 4) 107 (programCode 0x4a2b075e72) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x140003004008080108020e00408040a00010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2961 : TreeBound (n := 4) 107 (programCode 0x4a2b075e73) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001004008080108060200408040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2962 : TreeBound (n := 4) 107 (programCode 0x4a2b075e74) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x445800111600025f81e601e6798079879807a73408e22c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0x0,0x0,0x182081484222,0x1400050020040801000808024004020100a05e4,0x25f800097e00025f80798079f980798798079801023000f303cc102300f4e60f3001e60f3003cfffb6,0x182081490a62,0x0,0x182081490a62,0x0,0x0,0x0,0x0,0x0,0x182081484222,0x182081484222,0x182080480222,0x182081484222,0x25f800097e000445800799e601ed983cc2046003d39800f4e6001e9cc01e63cc0798f301e61e703d95,0x25f800097e00025f80798079f9807987980798000f30079803cde6f3001e63cc1e600001e603cc33b6,0x182081484222,0x1400050020040801000008104004000100a05e4,0x0,0x0,0xc00050020040801001008044201008840201a4,0x0],
[0x4458001116000445800799e601ed983cc2046003d39800f4e6001e9cc79803cde600f379801e703d95,0xf362b83cc1e600016c83d59f3900fa983cc0079803d398003d39801e9cfd57e3cc0f30408c001e64dc35,0x7980001e6000445800001e601ed983cc2046003d39800f4e6001e9cde6003d39800f3f3001e703d95,0x0,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0x1400050020040801001008044000002000201e4,0x0,0x182081484222,0x1400050020040801001008044004020100a05e4,0x0,0x182081490a62,0x1400050020040801001008044001008800201e4,0x182081490a62,0x1400050020040801001008044000002000201e4,0x0,0x1400050020040801001008044000002000201e4,0x0,0x0,0x4459e6097e0001e601e601e6798079879807a73408de60000b6400f33cc1e688b00003cc0003cc3c26,0x0,0x0,0x0,0x1e600007980001e600798079f9807987980798000f30000003cc00f33cc1e60f300003cc0003cc33b6,0x3ccf30079bcc01e63ea601e6798079879807b0d9e6dedb660b647a733cc31b4470004fbc0003eb15a6,0x0,0x3ccf300f33cc01e67b6601e6798079879807aeec4ede607983ccf3f33cc2dd91700012fc0003cc3cb6,0x3d398007bdf801e7e7e601e6798079879807b1e3aede6f300b67ccf33cc31685700f33cc0003ee6826,0x3d398007b66001e7e7e601e6798079879807b1e3aede6f300b67ccf33cc31685700f33cc0003ee6826],
[0x408de60798b641f531e601e6798079879807aecdeeded9800b8260f33cc1e688b00012fc0003cc3c26,0x3d398007a73001e9cde601e6798079879807afbf08de9cc00b6b98f33cc2d988b03cc3cc000454ec26,0x1e600007980001e600798079f9807987980798000f30000003cc00f33cc1e60f300003cc0003cc33b6,0x408c00088b0001f531e601e6798079879807aecdeeded9800b8260f33cc1e688b00012fc0003cc3c26,0x445800097e0001e601e601e6798079879807a73408de60000b6400f33cc1e688b00003cc0003cc3c26,0x408c00081180020461e601e6798079879807aecdeedf53000ba0c0f33cc1e688b00012fc0003cc3c26,0x0,0x49281611160001e63ea601e6798079879807981e9cde679803cc7a733cc1ea54b000408c0003eb1636,0x1e607987987981e608118079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x0,0x1e60f307983cc1e60fa98079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x1e63cc07d4c001e600798079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x1e63cc079bcc01e63d398079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x25f8000798f301e60fa98079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x1e67980799e601e679f98079f980798798079807a730079803cc7a733cc1e60f3000408c0003ec0036,0x1e7e60079f9801e7e6798079f980798798079807a730079803cc7a733cc1e60f3000408c0003eed936,0x1e7e6007b66001e7e6798079f980798798079807a730079803cc7a733cc1e60f3000408c0003eed936,0x1f530007983cc1f530798079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x1e9cc007a73001e9cc798079f980798798079807a730079803cc7a733cc1e60f3000408c000405a136,0x1f53000798f301e600798079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x1f5300088b0001f530798079f980798798079807a730079803cc7a733cc1e60f3000408c0003eb0d36,0x44580011160001e601e601e6798079879807981e9cde679803cc7a733cc1ea54b000408c0003eb1636,0x204600081180020460798079f980798798079807a730079803cc7a733cc1e60f3000408c000427cd36,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0xc00050020040801000008044200002000201a4,0x0,0x182081484222,0x1400050020040801004008144004020100a05e4],
[0x0,0x445800111600025f81e601e6798079879807a08f08de9cc003cc1f5303cd11da7307980f3003db6cb6,0xc00050020040801001008044201008840201a4,0x445800111600025f81e601e6798079879807a08f08de9cc003cc1f5303cd11da7307981e6003db6cb6,0xc00050020040801000008044200002040201a4,0x0,0xc00050020040801000008044200002000201a4,0x0,0x25f800097e00025f80798079f98079879807980f3f3003cc03ccf3f33cc1e60f30007d4c0003cd26b6,0x0,0x4919d911160001f531e601e6798079879807b1a6eeded98003cfccf33cc2d9c5700f33cc0003ea9cb6,0x3cc1e60f307981e6097e01e679807987980798f708de603cc3cfccf33cc2d988b00f33cc0003ea9cb6,0x0,0x3cc1e60f307981e6111601e679807987980798f708de607983cfccf33cc2d988b00f33cc0003ea9cb6,0x4993590f379801e601e601e6798079879807b1a6eede600003cfccf33cc2d9c5700f33cc0003ea9cb6,0x1e63cc079bcc01e63d398079f98079879807983ccf3001e603cfccf33cc1e60f301119cc0003eed936,0x4825e60f6cc001e6111601e6798079879807afbf08de607983cfccf33cc2d988b00f33cc0003ea9cb6,0x1e67980799e601e679f98079f98079879807983ccf3003cc03cfccf33cc1e60f300fad4c0003eb86b6,0x1e7e60079f9801e7e6798079f98079879807983ccf300f3003cfccf33cc1e60f300f33cc0003ee5fb6,0x1e7e6007b66001e7e6798079f98079879807983ccf300f3003cfccf33cc1e60f300f33cc0003ee5fb6,0x1f530007983cc1f530798079f98079879807983ccf30798003cfccf33cc1e60f300f42fc0003ea93b6,0x1e9cc007a73001e9cc798079f98079879807983ccf301e6003cfccf33cc1e60f304bf3cc00047ea7b6,0x1e600007d4c001e600798079f98079879807983ccf30000003cfccf33cc1e60f300f33cc0003ea93b6,0x1f5300088b0001f530798079f98079879807983ccf30798003cfccf33cc1e60f300f42fc0003ea93b6,0x44580011160001e601e601e6798079879807a8233cde600003cfccf33cc2d988b00f33cc0003ea9cb6,0x204600081180020460798079f98079879807983ccf30f30003cfccf33cc1e60f300f42fc00042753b6,0x0,0x4918e611160001f531e601e679807987980798f33cde9cc003cfccf33cc2d988b00f33cc0003ea9cb6,0x1e607987987981e608118079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x0,0x1e60f307983cc1e60fa98079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x1f5300079f9801e600798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6],
[0x1e63cc079bcc01e63d398079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003eb0d36,0x25f80007d4c001e60fa98079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x1e67980799e601e679f98079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003eb86b6,0x1e7e60079f9801e7e6798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ee5fb6,0x1e7e6007b66001e7e6798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ee5fb6,0x1f530007983cc1f530798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x1e9cc007a73001e9cc798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc00040527b6,0x1e600007d4c001e600798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x1f5300088b0001f530798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x44580011160001e601e601e679807987980798f33cde9cc003cfccf33cc2d988b00f33cc0003ea9cb6,0x204600081180020460798079f98079879807983ccf303cc003cfccf33cc1e60f300f33cc00042753b6,0x445800111600025f81e601e67980798798079f9c08de607983ea60f33cc1e688b00012fc0003cc3cb6,0x0,0x1e6000097e00029c40798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000445b3b6,0x1e607987987981e608118079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000445b3b6,0x1e60f3097e00025f80798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000445b3b6,0x1e60f307983cc1e60fa98079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000445b3b6,0x222c0007b66001e600798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000445b3b6,0x1e63cc079bcc01e63d398079f9807987980798798f301e6003d398f33cc1e60f303cc3cc0004648d36,0x0,0x1e67980799e601e679f98079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000446a6b6,0x1e7e60079f9801e7e6798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc0004497fb6,0x1e7e6007b66001e7e6798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc0004497fb6,0x1f530007983cc1f530798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc00046413b6,0x1e9cc007a73001e9cc798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc00046047b6,0x1e6000088b0001e600798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc000445b3b6,0x1f5300088b0001f530798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc00046413b6,0x0,0x204600081180020460798079f9807987980798798f301e6003d398f33cc1e60f303cc3cc00048273b6,0x0,0x4459e6097e0001e601e601e6798079879807a73408de60000b6400f33cc1e688b00003cc0003cc3c26,0x0],
[0x0,0x1e60f307983cc1e60fa98079f9807987980798000f30000003cc00f33cc1e60f300003cc0003cc33b6,0x1e600007980001e600798079f9807987980798000f30000003cc00f33cc1e60f300003cc0003cc33b6,0x3ccf300f33cc01e63ea601e6798079879807aecc08de607983ea60f33cc1e688b00012fc0003cc3cb6,0x4459e607980001e6111601e6798079879807a73408de60000b6400f33cc1e688b00003cc0003cc3c26,0x0,0x3d39800f379801e7e7e601e6798079879807b1e3aeded98003cfccf33cc31685700f33cc0003ee68b6,0x3d39800f4e6001e7e7e601e6798079879807afc0eeded98003cfccf33cc2d9c5700f33cc0003ee68b6,0x408de60f303cc1f531e601e6798079879807aecdeede607983ea60f33cc1e688b00012fc0003cc3cb6,0x3d39800f4e6001e9cde601e6798079879807afbf08e0460003db30f33cc2d988b03cc3cc000454ecb6,0x1e600007980001e600798079f9807987980798000f30000003cc00f33cc1e60f300003cc0003cc33b6,0x408c0010230001f531e601e6798079879807aecc08de607983ea60f33cc1e688b00012fc0003cc3cb6,0x445800097e0001e601e601e6798079879807a73408de60000b6400f33cc1e688b00003cc0003cc3c26,0x0,0x25f800097e00025f80798079f9807987980799e60f31e60003ea60f33cc1e60f300012fc0003cc33b6,0x0,0x4459e611160001e601e601e6798079879807a7303ce22c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0x4459e60f300001e601e601e6798079879807a7303ce22c0003cc00f33cc1e688b00003cc0003cc3cb6,0x3ccf300f33cc01e63ea601e6798079879807a7303ce22c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0,0x0,0x3d39800f379801e7e7e601e6798079879807b0ae3ce22c0003ea60f33cc1e6c5700012fc0003cc3cb6,0x3d39800f4e6001e7e7e601e6798079879807aec83ce22c0003ea60f33cc1e688b00012fc0003cc3cb6,0x0,0x600020001000000006000000004000000040002000100000000000000000000000002000010008000040010000080020000100400000101000000404000000810000001001087f667,0x4459e60f300001e601e601e6798079879807a7303ce22c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0,0x44580011160001e601e601e6798079879807a7303ce22c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0],
[0x25f800097e00025f80798079f980798798079bcc0f30f3000408c0f33cc1e60f300012fc0003cc33b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3155 : TreeBound (n := 4) 107 (programCode 0x4a2b075e75) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x209890240481,0x8180802014008080108060e00408040e00010104,0x209890240481,0x0,0xf33cc1e600007981e6111601e6798079879807a73482622c0003cc00f33cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0x0,0x1ef7e0fa98003cc1e60fa98079f980798798079807a730079bdefc7a733cc1e73ef000408c0003eb0d36,0x0,0x11160f344583cc1e60fa98079f98079879807980f3f3003cc222cf3f33cc1e7f530007d4c0003cd26b6,0x19a6b21e6f3007981e6111601e679807987980798f79935907983cfccf33cc334e5700f33cc0003ea9cb6,0x222c00f3f3001e9ea60fa98079f98079879807983ccf303cc07d4fcd119cc222cf300f33cc04496e5f26,0xf35b21e607987981e6111601e6798079879807aece686d907983ea60f33cc1e6c5700012fc0003cc3cb6,0x7d4c00f6cc001e9ea60fa98079f9807987980798798f300f307d539cdd9cc222cf303cc3cc1379e7df26,0xf300003cc1e60fa98079f9807987980798000f30000003cc00f33cc1e60f300003cc0003cc33b6,0x1e60f307983cc1e60fa98079f9807987980799e60f31e60003ea60f33cc1e60f300012fc0003cc33b6,0x0,0x1e60f307983cc1e60fa98079f980798798079bcc0f30f3000408c0f33cc1e60f300012fc0003cc33b6,0x211010240481,0xe602008044008080108073200408073200042304,0x211010240481,0xf307d4c001e60f3079f98079f98079879807a7300f33cc001f5300f33cc1e60f307983cc001e610856,0x221010240481,0x201010240481,0x221010240481,0x221010240481,0x243110240501,0x221010240481,0x243110240501],
[0xc020100804008080108060200408060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3188 : TreeBound (n := 4) 107 (programCode 0x4a2b075e76) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x463008404008080108023200408042200042304,0x400808014008080108023200408042200042304,0x0,0x609881240481,0x440808014008080100123002408042e00042304,0x609881240481,0x0,0x409882240481,0x409884240481,0x409882240481,0x409886240481,0x409884240481,0x409884240481,0x409884240481,0x409886240481,0x509888240481,0x409886240481,0x509888240481,0x0,0x0,0x1e601e67980798798111601e6798079879807b0d9e7b6cc000f4e60f33cc31b447000408c000f4f1636,0x0,0x10bb59ad93ea60079801362a53907983cc03cc00003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x0,0x20a0825404c2,0x20a0825404c2,0x20a0825404c2,0x7981e61e607987980fa980799e601e6798079801e63cc0798f33ccf33cc1e60f300f33cc0088d2de76,0x20a084541d02,0x20a08a5414c2],
[0x20a084541d02,0x20a08a5414c2,0x20a0885414c2,0x0,0x20a0885414c2,0x473008004008080108023200408042200042304,0x402008044008080108023200408042200042304,0x442008044008080108023200408042200042304,0x402008084008080108023200408042200046704,0x40c008104008080108023200408042200042b04,0x408008104008080108023200408042200042b04,0x423008404008080108023200408042200042304,0x408008204008080108023200408042200043304,0x433008004008080108023200408042200042304,0x420008404008080108023200408042200042304,0x440008004008080108023200408042200042304,0x420008804008080108023200408042200046304]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3237 : TreeBound (n := 4) 107 (programCode 0x4a2b075e77) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80400010020040801080002004080402000000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3238 : TreeBound (n := 4) 107 (programCode 0x4a2b075e78) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xfa98003ea6000fa980798079f98079879807a7300f33cc001f5300f33cc1e60f307983cc001e610856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3239 : TreeBound (n := 4) 107 (programCode 0x4a2b075e79) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x904002100400808010806c200408078200100904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3240 : TreeBound (n := 4) 107 (programCode 0x4a2b075e7a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x104002100400808010802c200408078200100904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3241 : TreeBound (n := 4) 107 (programCode 0x4a2b075e7b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x409890240481,0x20004800120040801080102004080402004020e4,0x409890240481,0x0,0x0,0x0,0xf379adae7e60079801362a53907983cc03cc00003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x0,0x80a0824414c2,0x80a0884410a2,0x80a0824414c2,0x1e6001ed98007b66000fa980799e601e6798079801f530007d4c03ccf33cc1e60f300f33cc03cc1e98f6,0x80a0844410a2,0x80a0884410a2,0x80a0844410a2,0x798001ed98007b6600111601e6798079879807b0b3eec0007d4c0000f33cc315cf300003cc03cc1e9cb6,0x80a0884410a2,0x0,0x80a0884410a2,0x411010240481,0x20010800420040801080102004080402004022e4,0x411010240481,0x20020800820040801080102004080402004024e4,0x420010240481,0x400010240481,0x420010240481,0x400010240481,0x442110240501,0x400010240481,0x442110240501],
[0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3274 : TreeBound (n := 4) 107 (programCode 0x4a2b075e7c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040041004008080108028200408068200201104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3275 : TreeBound (n := 4) 107 (programCode 0x4a2b075e7d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x808cd0240481,0x4000120040801080002004080402000000e4,0x808cd0240481,0x0,0x1e67980799e601e60007983cde60174954fec64600f6cc003ea6000f6cfcc001f53000f6cc001e703885,0x0,0x1e67980799e601e6001e60f33cc044d1bd3b882c03d39800f4e6001e9cfcc003db3000f6cc001e722395,0x0,0x0,0x23008080220040801002010084080012000423e4,0xa080440022,0x4008100220040801004020104080022000804e4,0x18b3b21e607987b6600111601e679807987980798f7919d907d4c03ccf33cc31685700f33cc03cc1e9cb6,0x1004800220040801008100204080102004021a4,0xa088440022,0x1004800220040801008100404080102004021a4,0xa080440022,0xa088440022,0x0,0xa088440022,0x811890240481,0x22010800420040801080102004080402004022e4,0x811890240481,0x20000820040801080002004080402000000e4,0x821010240481,0x800010240481,0x821010240481,0x800010240481,0x842110240501,0x800010240481,0x842110240501],
[0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3308 : TreeBound (n := 4) 107 (programCode 0x4a2b075e7e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x609890240481,0x20004800120040801080102004080402004020e4,0x609890240481,0x0,0x0,0x0,0x10ca89adae7e6000f301362a53907983cc03cc00003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x0,0x80a0824414c2,0x80a0884410a2,0x80a0824414c2,0x1e6001ed98007b66000fa980799e601e6798079801f530007d4c03ccf33cc1e60f300f33cc03cc1e98f6,0x80a0844410a2,0x80a0884410a2,0x80a0844410a2,0x7980020460007b6600111601e6798079879807b0b208c0007d4c0000f33cc315cf300003cc03cc1e9cb6,0x80a0884410a2,0x0,0x80a0884410a2,0x411010240481,0x20010800420040801080102004080402004022e4,0x411010240481,0x20020800820040801080102004080402004024e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x842110240501,0x10240481,0x842110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3341 : TreeBound (n := 4) 107 (programCode 0x4a2b075e7f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x808cd0240481,0x0,0x831890204481,0x821010210481,0x831890204481,0x0,0x821010208481,0x8400808014008080108063200400442008042304,0x821010208481,0xf300b64000798f3008118079f98079879807a7300f33cc001f5300f3003ea6000fa98003cc1e610856,0x821010210481,0x821010200481,0x821010210481,0x821010210481,0x821010220481,0x821010210481,0x821010220481,0x821010230481,0x808cd0240481,0x0,0x1e600097e000222c7987983cde601749550292553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x808020220040801080006004000c00020100e4,0x3cc0011160007d4c798000799e60451dad7859513003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x0,0x0,0x0,0xf3012fc0003ccf300fa98079f98079879807a7300f33cc001f5300f3003ea6000fa98003cc1e610856,0x0,0x5000840024008080108028200401068020201104,0x8000220040801080002004000400800000e4],
[0x5000840024008080108028200401068040201104,0x8000220040801080002004000402000000e4,0x0,0x8000220040801080002004000400000000e4,0x0,0x811890240481,0x0,0x831881240481,0x8102002044008080100160c02408040a00010104,0x831881240481,0x0,0x821002240481,0x800000240481,0x821002240481,0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x800008240481,0x800000240481,0x800008240481,0x800008240481,0x811890240481,0x0,0x0,0x0,0x0,0x0,0x831882240481,0x800000240481,0x831882240481],
[0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x821010240481,0x800010240481,0x821010240481,0x800010240481,0x842110240501,0x800010240481,0x842110240501,0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3422 : TreeBound (n := 4) 107 (programCode 0x4a2b075e80) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108890204481,0x10004400110080102080082002010020400814e3,0x108890204481,0x0,0x7987981e600003cc0001e601e6798079879807a7303cc3cc0798f300f33cc2d90f3079800007983cde56,0x10004400110080102080082002080020400814e3,0x7987981e600003cc0001e601e6798079879807a7303cc3cc0798f300f35b22d90f307980f307983cde56,0x4000100080102080082002080020000814e3,0x79882ffe60079bcc01e7e601e6798079879807a7303cc3cc0798f300f34181d9003d39800f379840aa56,0x400010004010008004200200801000080ca3,0x10004400110080102080082002010020400814e3,0x4000100080102080082002080020000814e3,0x808cd0220481,0x7987981e600003cc0001e601e6798079879807a7303cc3cc0798f300f31e62d9079879807987983cde56,0x808cd0220481,0x8890200481,0x40005000120040801080202004080402008040e4,0x0,0x108890204481,0x10008400210080102080082002010020400814e3,0x108890204481,0x0,0x0,0x0,0x0,0x0,0x0,0x10008400210080102080082002010020400814e3,0x10008400210080102080082002010020400814e3,0x0],
[0x808cd0220481,0x8000200080102080082002000020100814e3,0x808cd0220481,0x8890200481,0x0,0x0,0x0,0x0,0x0,0x0,0x80a0824414c2,0x80a0884410a2,0x80a0824414c2,0x0,0x80a0844410a2,0x80a0884410a2,0x80a0844410a2,0x0,0x80a0884410a2,0x7980020460007d4c000fa980799e601e6798079f981e61e60798f300f33cc0f30f307983cc16c8b69756,0x80a0884410a2,0x0,0x7987981e600003cc0001e601e63cc03cc79807a7303cc3cc07980000f33cc2d90f303cc3cc07983cde26,0x10400400000400080080402080022000814e3,0x0,0x0,0x211002240481,0x11000240481,0x211002240481,0x411004240481,0x411004240481,0x11000240481],
[0x411004240481,0x411004240481,0x811888240481,0x411004240481,0x811888240481,0x11000240481,0x40011000420040801080202004080402008062e4,0x0,0x798b641e600003cc1e61e601e6798079879807aec83cc3cc07980000f33cc2d90f300003cc07983cde56,0x0,0x0,0x0,0x211002240481,0x11000240481,0x211002240481,0x411004240481,0x411004240481,0x11000240481,0x411004240481,0x411004240481,0x811888240481,0x411004240481,0x811888240481,0x11000240481,0x40021000820040801080202004080402008044e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x42110240501,0x10240481,0x42110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_2958 : TreeBound (n := 4) 107 (programCode 0x4a2b075e) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part102_2959 part102_2960 part102_2961 part102_2962 part102_3155 part102_3188 part102_3237 part102_3238 part102_3239 part102_3240 part102_3241 part102_3274 part102_3275 part102_3308 part102_3341 part102_3422

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3520 : TreeBound (n := 4) 107 (programCode 0x4a2b075f61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100a0f0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3521 : TreeBound (n := 4) 107 (programCode 0x4a2b075f62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10320d0204481,0x1022090210481,0x10320d0204481,0x0,0x10320c1204481,0x80002002040001000000080402000020000814e3,0x10320c1204481,0x1022080200481,0x1022082208481,0x80002002040001000000080002000020000814e3,0x1022082208481,0x0,0x4000000090000000240000000900000000c0000080100040200400000800000200804000200010404800200008001001000001000100010000480020002000040002000400026aba8,0x80002002040001000000080002000020000814e3,0x0,0x0,0x0,0x0,0x0,0x0,0x1022090208481,0x0,0x1022081218481,0x1022084210481,0x1022081218481,0x1022088210481,0x1022082210481,0x1022084210481,0x1022082210481,0xf3000222c00088b0000b6b99e6f30079801e67981eda7307981e60f303cc7b69cc1e60f301e61e611156,0x1022084210481],
[0x1022084210481,0x1022084210481,0x8000a0001840800810104a04004044a008201104,0x1022088210481,0x8000a00018408008104072080040460008402104,0x1022088210481,0x0,0x1022090208481,0x0,0x1022081220481,0x1022084220481,0x1022081220481,0x0,0x1022082228481,0x1022084220481,0x1022082228481,0x0,0x1022084220481,0x1022084220481,0x1022084220481,0x8000a0001840801010104a04008044a010201104,0x0,0xf30000b6400088b000079bcc7a730079803cc799e6007b662d901e6007983ea6000fa98003db30799556,0x0,0x0,0x1022090210481,0x1022090210481,0x1022090210481,0x0,0xf379805e90e0100c3f9801ed9887447321d1d3001e9cc01e6f3003cc003ccf300f3fa1ebcde703375,0x422090230481,0x1e6798111bb201f164f3001ed987aed73219513003cfcc01e6f3003cc00799e603ccf9a5001e703885],
[0x2002040001000080082002000020000814e3,0x222090228481,0x0,0x222090228481,0x0,0x422090230481,0x422090230481,0x422090230481,0x822090220481,0x822090220481,0x422090230481,0x822090220481,0x822090220481,0x1022090220481,0x0,0x122090218481,0x422090210481,0x122090218481,0x0,0x222090210481,0x40080801c008080108063200404042080042304,0x222090210481,0x1e601e67980798f300d4a01e6f30079879807a730b736cc001f5300f31e61e9d398798079801e611156,0x422090210481,0x422090210481,0x422090210481,0x822090210481,0x822090210481,0x422090210481,0x822090210481,0x822090210481,0x1022090220481],
[0x0,0x122090220481,0x422090220481,0x122090220481,0x0,0x0,0x0,0x0,0x0,0x422090220481,0x422090220481,0x422090220481,0x822090220481,0x822090220481,0x422090220481,0x822090220481,0x822090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3634 : TreeBound (n := 4) 107 (programCode 0x4a2b075f63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100a0f0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3635 : TreeBound (n := 4) 107 (programCode 0x4a2b075f64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80006010040005002980082002000820020814e3,0xf300003cc0f30f307981e600007983cc0f30000f30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0x8000a010040009002a80082002001020040815e3,0x0,0x100a0e1204481,0x80002000040001000000080402000020000814e3,0x100a0e1204481,0x1002000200481,0x10120c2208481,0x1002000200481,0x10120c2208481,0x0,0x0,0x1002000200481,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0e1208481,0x1022084208481,0x100a0e1208481,0x1002000208481,0x10120c2208481,0x1002000208481,0x10120c2208481,0x80202010040201008080081002002020080854e3,0x1022084208481,0x1002000208481],
[0x1022084208481,0x80002010040001000080080002002020080814e3,0x1042108208501,0x0,0x1042108208501,0x0,0x0,0x80006000140005002900880022004020020814e3,0x80002000040001000000080402000020000814e3,0x8002a000240029002a01080042004020140815e3,0x1002000200481,0xf303cc3cc2da02303cfd398f30798b67db32e9230799e601e7e60079bcc1e600f37980f8d2461ee9b375,0x1002000200481,0xf303cc3cc1e60f3000f4e60f307987980f32d9001e67980799e600f33cc3cc03ccf300f8b2001ee9bd95,0x400030001000000004000200010000c00020003000080000000100020000200000006000010010000040060000080040000100600000101800000400000000810000001001087fe67,0x80002001040001000008080202000020000814e3,0x1002000200481,0x80002002040001000010080402000020000814e3,0x8000a0002840801010104a04008044a008201104,0x0,0x0,0x80002008040001000040081002000020000814e3,0x0,0x0,0x100a0e1208481,0x1022084208481,0x100a0e1208481,0x1002000208481,0x10120c2208481,0x1002000208481,0x10120c2208481,0x0],
[0x1022084208481,0x1002000208481,0x1022084208481,0x0,0x1042108208501,0x0,0x1042108208501,0x0,0x0,0x0,0x0,0xf300003cc1e60f300035a180007987980f3222a1a0f4e600f4e6001e9cc00000f30000f652801e703375,0x0,0x0,0x0,0xf30007d4c1e9db30016d73001ed987a73f3219420f33cc0799e600f33cc03cc1e61e60f5d9001e703885,0x0,0x0,0x8000a0002840801010104a02008044a010201104,0x0,0x8000a0002840801010104a04008044a010201104,0x0,0x0,0x0,0x0,0x80202010040201008080082002008020200854e3,0x80002010040001000080082002000020000814e3,0x80202010040201008080082002010020400854e3,0x0,0x800030040001000080082002000820000814e3,0x410040001000080082002000020000814e3,0xf307992c014a2ca05a180025f8e4061b3cbf0d001e9cc01e6f3003cc003ccf303ccfa20295e703375],
[0x2010040001000080082002000020000814e3,0x0,0x0,0x0,0x0,0x8200210040201008080082002008020200854e3,0x10040001000080082002000020000814e3,0x10200410040201008080082002010020400854e3,0x10040001000080082002000020000814e3,0x0,0x0,0x40201010040201008080082002040021000854e3,0x0,0x0,0x804030040005002980082002020020800814e3,0x80080410040081002080082002020020800814e3,0x1008050040009002a80082002020020800815e3,0x0,0x2010090040011002480082002020020800816e3,0x80000010040001000080082002020020800814e3,0x4020110040021002880082002020020800814e3,0x80201010040201008080082002020020800854e3,0x804021004004100008008200202002080081ce3,0x10040001000080082002020020800814e3,0x10080410040081002080082002020020800814e3,0x10040001000080082002020020800814e3,0x0,0x0,0x40201010040201008080082002020020800854e3,0x0,0x0,0x0],
[0xf30f30f303cc0f3111600799e60799e6007a7303cc3cc0002d903cc07983cc7987980798001e61556,0x0,0x0,0x7d4c002139f3084e40798f30798b67db32e9323001e9cc01e6f3003cc1e600f37980f8d0601ee9b375,0x0,0x1e9cc007c5ccc0fa981e60f30798b733f32f76f30079bcc01e6f3003cc3cc03ccf300f8eec01ee9bd95,0x4000000014000800050002000080008000100000000400080002000200002000000040000080100000200400001001000001004000000810000002000000010100000010020866ba7,0x3cc00f307983cfcc011160079f980799e6007a7303cc3cc007a7303cc0798f30798798079807983e156,0x1000820024008100108028200804068080201104,0x0,0x10008400200040801080082004020400802018e4,0x0,0x0,0x0,0x0,0x0,0x804030040005002980082002040021000814e3,0x410040001000080082002040021000814e3,0x1008050040009002a80082002040021000815e3,0x2010040001000080082002040021000814e3,0x2010090040011002480082002040021000816e3,0x0,0x4020110040021002880082002040021000814e3,0x0,0x804021004004100008008200204002100081ce3,0x10040001000080082002040021000814e3,0x10080410040081002080082002040021000814e3,0x10040001000080082002040021000814e3,0x0,0x0,0x40201010040201008080082002040021000854e3,0x0],
[0x0,0x0,0x0,0xf3000111600025f807980007987980f31e60f3001e9cc01e6f3003cc00000f30000f6cc001e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x1000820024008100108028200804068100201104,0x9000200041001080002008040401000000e4,0x10008400200041001080082008040401002018e4,0x0,0x0,0x9000200041001080002008040401000000e4,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3812 : TreeBound (n := 4) 107 (programCode 0x4a2b075f65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10120d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3813 : TreeBound (n := 4) 107 (programCode 0x4a2b075f66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10320c1240481,0x0,0x1022086204481,0x1002004210481,0x1022086204481,0x80002000040001000000080402000020000814e3,0x1002004208481,0x1002004200481,0x1002004208481,0x1002004220481,0x1002004210481,0x1002004200481,0x1002004210481,0x8002200048108002100148802011048840201104,0x1002004220481,0x8002200048108002100170802014070080402304,0x1002004220481,0xf3000408c003db30003cc03d3a7300798003d39800f3079918f8000f3088b1e603cc1e60f307983ebb56,0x10320c1240481,0x0,0x10320c1204481,0x1002008210481,0x10320c1204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481,0x0,0x1002008210481,0x1002000200481,0x1002008210481],
[0x8002200048108004100148804021048840201104,0x0,0xf3000408c003db30003cc079fa73007980079f9801e60f30a710001e60fa99e607983cc0798f307a2d36,0x0,0xf3000408c003db30003cc079fa73007980079f9801e60f309f78001e610231e603cc1e60f307983ed9b6,0x1022082240481,0x1002000240481,0x1022082240481,0x0,0x600000001001000006004000018010200020000800000101000200402000821040000100100000400000040800c00001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x22208a240481,0x2008240481,0x22208a240481,0x802008240481,0x40200c240481,0x2008240481,0x40200c240481,0x2008240481,0x802008240481,0x2008240481,0x802008240481,0x2008240481,0x1002004240481,0x1002000240481,0x1002004240481,0x0,0x1320c9240481,0x0,0x1320c9240481],
[0x0,0x22208a240481,0x2000240481,0x22208a240481,0x802008240481,0x402004240481,0x2000240481,0x402004240481,0x2000240481,0x802008240481,0x2000240481,0x802008240481,0x2000240481,0x1002008240481,0x0,0x122086240481,0x10200204c008080104060c80408040e00010104,0x122086240481,0x1e63cc079bcc01e63d39807a73007987980799e60f31e61e63ea60f33cc1e60f300012fc0003cc33b6,0x202004240481,0x2000240481,0x202004240481,0x802000240481,0x402000240481,0x2000240481,0x402000240481,0x2000240481,0x802000240481,0x2000240481,0x802000240481,0x2000240481,0x1002008240481],
[0x0,0x0,0x0,0x0,0x3cc7980f31e601e6408c00f46c803ccf30079f9879a0462d97d4c1e63cc00088b079a22c0007985936,0x202000240481,0x2000240481,0x202000240481,0x802008240481,0x402008240481,0x2000240481,0x402008240481,0x2000240481,0x802008240481,0x2000240481,0x802008240481,0x2000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3926 : TreeBound (n := 4) 107 (programCode 0x4a2b075f67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10120d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3927 : TreeBound (n := 4) 107 (programCode 0x4a2b075f68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x104a1e1204501,0x1062181230501,0x104a1e1204501,0x104a1e1204501,0x10521c1208501,0x10721c1238501,0x10521c1208501,0x1042101220501,0x1062181210501,0x1042101220501,0x1062181210501,0x80002008040001000000880022080020000814e3,0x1042101220501,0x80002008040001000000880022080020000814e3,0x1042101220501,0x0,0x0,0x10721c6204501,0xf300003cc0f30f303cc1e600007983cc0f3000000007980001e60f303cc00003cc0000f33cc01e703d95,0x10721c6204501,0x80202008040201008000080402000020000854e3,0x1042104208501,0xf300003cc0f30f303cc1e600007983cc0f3000000007980001e60f303cc00003cc0000f4e6001e703d95,0x1042104208501,0xf300003cc0f30f303cc1e600007983cc0f3000000007980001e60f303cc00003d39800f4e6001e703d95,0xf300003cc0f30f303cc1e600007983cc0f3000000007980001e60f303cc0f303cc3cc0f30f301e703d95,0x800220008810800410014880202104c820201104,0x0,0x8002200088108004100148802021048840201104,0x0],
[0x4000000010000a000400008001000040001000000004000a000200008000200000004000008014400020000000100008000100400000081400000204000001000000001002086aba7,0x0,0x0,0x0,0x104a1e1204501,0x1062181230501,0x104a1e1204501,0x104a1e1204501,0x10521c1208501,0x10721c1238501,0x10521c1208501,0x1042101220501,0x1062181210501,0x1042101220501,0x1062181210501,0x0,0x1042101220501,0x0,0x1042101220501,0x0,0x0,0x104a1e1204501,0x0,0x104a1e1204501,0x1042100200501,0x1042100208501,0x80002008040001000000080002000020000814e3,0x1042100208501,0x0,0x0,0x80002008040001000000080002000020000814e3,0x0],
[0x8002200088108004100148804021048840201104,0x0,0x4000000010000a000400000001000040001000000004000a000200000000200000004000008010000020000000100000000100400000081400000204000001000000001002086aba7,0x0,0x0,0x10521c2240501,0x80002008040001000000080002080022000814e3,0x10521c2240501,0x0,0x0,0x0,0x0,0x0,0x2521ca240501,0x842108240501,0x2521ca240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1042104240501,0x80002008040001000000080002080022000814e3,0x1042104240501,0x0,0x0,0x0,0x0],
[0x0,0x2521ca240501,0x842108240501,0x2521ca240501,0x842108240501,0x442104240501,0x842108240501,0x442104240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501,0x0,0x14a1e8240501,0x80080408040081002020080802080022000814e3,0x14a1e8240501,0x8010080804010100c020080802080022000874e3,0x2521c8240501,0x842108240501,0x2521c8240501,0x842108240501,0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x0,0xf379805f0c4615dc9f9801ed9889320b3afa46f31e603cde7d7d26cfcc001023000f6cc001e703375],
[0xf37980f31e600f37b66007a7300799e600799e63cc1e61e620463cc3cc1e60f30000b640001e61556,0x1e67981288e8424120f3001ed98d63b03386784f33cc0799e7c33c5cfcc001f53000f6cc001e703885,0x1e67980f33cc01e67d4c00f42fc03ccf30079bcc799f5325ffb661e63cc00088b079b15c0007985426,0x2721ce240501,0x842108240501,0x2721ce240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x0,0x14a1e8240501,0x0,0x14a1e8240501,0x0,0x2521c8240501,0x842108240501,0x2521c8240501,0x842108240501,0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501],
[0x0,0x0,0x0,0x0,0x3ccf300f33cc01e67d4c00f46c803cde60079f9879a0462d97d4c3cc3cc00088b079a22c0007985936,0x2521c2240501,0x842108240501,0x2521c2240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4104 : TreeBound (n := 4) 107 (programCode 0x4a2b075f69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1022090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4105 : TreeBound (n := 4) 107 (programCode 0x4a2b075f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1002010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4106 : TreeBound (n := 4) 107 (programCode 0x4a2b075f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1022090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4107 : TreeBound (n := 4) 107 (programCode 0x4a2b075f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x804038040005002980082002080022000814e3,0x0,0x4020418040021002880082002000820020814e3,0xc62190230501,0x4020418040021002880082002001020040814e3,0x0,0x462190208501,0x0,0x462190208501,0x0,0xc62190210501,0xc62190230501,0xc62190210501,0xc62190230501,0xc62190220501,0xc62190230501,0xc62190220501,0xc62190230501,0x1008058040009002a80082002080022000815e3,0x0,0x806018140005002980082002000820020814e3,0x40202008040201008080082002040020400854e3,0x100a018240009002a80082002001020040815e3,0x0,0x0,0x0,0x0,0x0,0x40202008040201008080082002008020200854e3,0x2000040001000080082002000020000814e3,0x40202008040201008080082002010020400854e3],
[0x2000040001000080082002000020000814e3,0x0,0x0,0x2000040001000080082002040021000814e3,0x0,0x2010098040011002480082002080022000816e3,0x0,0x4020108140021002800880022080022000814e3,0x0,0x4020108240021002801080042080022000814e3,0x0,0xc62182240501,0x2000240481,0xc62182240501,0x2008240481,0x2004240481,0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x4020118040021002880082002080022000814e3,0x0,0x0,0x0,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x462190240501,0x2010240481,0x462190240501,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4188 : TreeBound (n := 4) 107 (programCode 0x4a2b075f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1042110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4189 : TreeBound (n := 4) 107 (programCode 0x4a2b075f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1320d0240481,0x0,0x622090204481,0x402010210481,0x622090204481,0x0,0x402010208481,0x120002400708002108043a00010442008040304,0x402010208481,0x408c00102300010230088ce600f3798003d3a7307a952c001f53000079fb69cc1ed98003cc1e611156,0x402010210481,0x402010200481,0x402010210481,0x402010210481,0x402010220481,0x402010200481,0x402010220481,0x402010220481,0x1320d0240481,0x0,0xf379805b3f5317491f9801ed9879fa73206553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x1100044000840041080006000200c00020100e4,0x1e67981119db30865173001ed987a73f3219513003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x0,0x0,0x0,0x0,0x0,0x120004401108004108008a00021048820201104,0x1100044000040041080002000200400040000e4],
[0x1100044010040041080082000210400402018e4,0x0,0x120004404108004108020a00024060880804104,0x1100044000040041080002000200400040000e4,0x120004404108004108020a00024060900804104,0x222090240481,0x0,0x622081240481,0x420008400588008100142c02048040a00010104,0x622081240481,0x0,0x402002240481,0x2000240481,0x402002240481,0x2008240481,0x2004240481,0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x222090240481,0x0,0x0,0x0,0x0,0x0,0xa22082240481,0x802000240481,0xa22082240481],
[0x802008240481,0x802004240481,0x802000240481,0x802004240481,0x802008240481,0x802008240481,0x802000240481,0x802008240481,0x802008240481,0x402010240481,0x2010240481,0x402010240481,0x2010240481,0x802010240481,0x2010240481,0x802010240481,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4270 : TreeBound (n := 4) 107 (programCode 0x4a2b075f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1042110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4271 : TreeBound (n := 4) 107 (programCode 0x4a2b075f70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10a0f0204481,0x88002a140081002080082002010020400814e3,0x10a0f0204481,0x0,0x810030040011002480082002002020080816e3,0x800020040001000080082002080020000814e3,0x820030040021002880082002004020100814e3,0xa00028140201008080082002080021000854e3,0x16a1f0210501,0x102010200481,0x16a1f0210501,0x800020040001000080082002000820000814e3,0x14a1f0220501,0x800020040001000080082002004020000814e3,0x14a1f0220501,0x102010200481,0x0,0x0,0xc62190230501,0x0,0x0,0x462190208501,0x0,0x462190208501,0x4000000014400a200000008000080000001000000004000a200200008000200000004000008010000020040000100100000100400000081400000204000001008000001002086aba7,0xc62190210501,0xc62190230501,0xc62190210501,0xc62190230501,0xc62190220501],
[0xc62190230501,0xc62190220501,0xc62190230501,0x0,0x10a0f0204481,0x1000040040001000080082002000020400814e3,0x10a0f0204481,0x0,0x1010050040011002480082002002020080816e3,0x0,0x1020050040021002880082002004020100814e3,0x0,0x16a1f0210501,0x102010200481,0x16a1f0210501,0x1008040240009002a80082002001023040815e3,0x14a1f0220501,0x1020050040021002880082002004022400814e3,0x14a1f0220501,0x102010200481,0x0,0xf307985b22d916c881180025f879888b206739001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x1200048000840041080006000200c00020100e4,0xf3079911688b25fb5a180025f8799f53222b0d001e9cc01e6f3003cc003ccf303ccf300799e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x120004801108004108008a00021048820201104,0x1200048000040041080002000200400040000e4],
[0x1200048010040041080082000210400402018e4,0x0,0x120004804108004108020a00024060880804104,0x1200048000040041080002000200400040000e4,0x120004804108004108020a00024060900804104,0x0,0x2004090040005002900880022080022000814e3,0x208008a440081002080080402080022000814e3,0x2008090040009002a01080042080022000815e3,0x0,0x2120c2240481,0x202000240481,0x2120c2240481,0x2521ca240501,0x2721c4240501,0x202000240481,0x2721c4240501,0x2521ca240501,0x2521c8240501,0x2721ce240501,0x2521c8240501,0x202000240481,0x0,0xf30079bf033679b3c99180025f890ca0b2432460f4e6003ea6000f6cfcc001023000f6cc001e703375,0x7b660079f98007b660079879800fa98079879800f3f3011161e60f3f6cc1e60f307983cc0001e61556,0x798079fd4bfffffff8e180025f8f2f95b3cbe1a0f4e600f4e6001e9cfcc001023000f6cc001e703375,0x0,0xc62182240501,0x2000240481,0xc62182240501,0x2008240481,0x2004240481],
[0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x0,0x4004110040005002900880022080022000814e3,0x0,0x4008110040009002a01080042080022000815e3,0x0,0x2120c2240481,0x202000240481,0x2120c2240481,0x2521ca240501,0x2721c4240501,0x202000240481,0x2721c4240501,0x2521ca240501,0x2521c8240501,0x2721ce240501,0x2521c8240501,0x202000240481,0x0,0x0,0x0,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x462190240501,0x2010240481,0x462190240501,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_3519 : TreeBound (n := 4) 107 (programCode 0x4a2b075f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part102_3520 part102_3521 part102_3634 part102_3635 part102_3812 part102_3813 part102_3926 part102_3927 part102_4104 part102_4105 part102_4106 part102_4107 part102_4188 part102_4189 part102_4270 part102_4271

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4417 : TreeBound (n := 4) 107 (programCode 0x4a2b076071) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c80003cde6016cfd4c5d2553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x402010040041001080002008000c00020000e4,0x16c80005b200016c800079bcc025f83cc2083b30079bcc01e6f3003cc00f33cc03ccf300799e722395,0x0,0x82080404022,0x182081484222,0x182081484222,0x182081484222,0x0,0x0,0x82080404022,0x4400110040041001004020108001020040804e4,0x0,0x0,0x82088404022,0x0,0x0,0x82088404022,0x0,0x82088404022,0x0,0x108890208481,0x120890208481,0x108890208481,0x0,0x0,0x16e660f3f30010237983ea601e679801e6f3007a730b736cc0798f301e65b9c5cdb30798001ed983d5776,0x0,0x0,0x120890208481,0x120890208481],
[0x120890208481,0x102307983cc1e702303cde601e679801e6f3007a730bddbcc01e6f301e6408ef76f3079803cd11688cdf6,0x140cd0208481,0x16c83cc1e60f307980f31e601e67980798f3007a730b643cc0f30f301e65b22d90f307981e60f30799e56,0x140cd0208481,0x16c83cc1e60f307981e61e601e67980798f3007a730b643cc0f30f301e65b22d90f307981e60f30799e56,0x0,0x804020100000000080082002080020000814e3,0x40006020140041001080202008002400088040e4,0x0,0x0,0x0,0x40012080440041001080202008002400088042e4,0x0,0x40022100840041001080202008002400088044e4,0x840021000000000080082002080020000814e3,0x800020000000000080082002080020000814e3,0x880022000000000080082002080020000814e3,0x800020000000000080082002080020000814e3,0x9000240140a0022880082002080020500814e3,0x40102804040041001080202008002400088060e4,0xa000280140a0022880082002080020500814e3,0x800020000000000080082002080020000814e3,0x16c80005b200016c8003cde600fb11bcfec46f3001e9cc01e6f3003cc01e60f31e60f303cc1e703375,0x402010040041001080002008004400100000e4,0x445800111600016c8408de6003d398408c000f30079bcc007a73003cc3cc03ccf3003ccf301e64dc35,0x445800111600016c83cc1e600007983cc0000f30079bcc007a73003cfcc003db30003cc0001e64dc35,0x0,0x109010210481,0x121010210481,0x109010210481,0x0],
[0x0,0xf30003dba983df1a603db30079bcc0798f3007a7301e63cc07d5b301e60f32634fead980f307d4febb56,0x0,0xf30007983cc1f53f307a730079bcc0798f3007a7301e63cc001f5301e60f31e6000fa980f3001e610856,0x121010210481,0x101010210481,0x121010210481,0x121010210481,0x1414d0210481,0xf300f325f8f311160f30f30079bcc0798f3007a7301e63cc12fcf301e60f3222c97e7980f312fc97f556,0x1414d0210481,0x121010210481,0x445800111600016c83cc1e600007983cc0000f30079bcc007a73003cfcc003db30003cc0001e64dc35,0x0,0x10a0f0220481,0x122090220481,0x10a0f0220481,0x0,0x0,0x220000000480000001200000001000070002000140000000040000000000000004000010010000040040000080100000100200000100400000401000000801000001001087faa7,0xf33cc03cfcc00f379f9801e7e679fdc5a06553001e9cc01e6f3003cc79800f4e600f379801e703375,0x16c80005b2000102307983cc1e6892d4c60d2f3003cfcc01e6f3003cc79801e7e600f379801e8e9885,0x122090220481,0x102010220481,0x122090220481,0x804020020000800080082002020020800814e3,0x1425d0220501,0xf379803cde600fb11f982047e68195c5a06553001e9cc01e6f3003cc79800f4e600f379801e703375,0x1425d0220501,0x14a5f0220501,0x0,0x108890208481],
[0x121890218481,0x108890208481,0x0,0x0,0xf30003cc1e63defc003db30079bcc0798f3007a7301e63cc00102301e60799e60798798079800f6f34d6,0x402000040041001080002008020400800000e4,0xf30007983cc1f53f307a730079bcc0798f3007a7301e63cc001f5301e60799e60798798079801e610856,0x121890218481,0x121890218481,0x121890218481,0x800020000000000080082002004020000814e3,0x142dd0228501,0xf379803cde600fb11c08de6102b11c0cac46f3001e9cc01e6f3003cc03cc0f30f30f3408c1e703375,0x142dd0228501,0x800020000000000080082002004020000814e3,0x0,0x10a0f0220481,0x122090220481,0x10a0f0220481,0xf307983cc1e616c888b000222c798c57206739001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x0,0x0,0xf3f3003cfcc00f37a73003cfcc7983cc2083b30079bcc01e6f3003cde6003d39800f3f3001e722395,0x0,0x122090220481,0x102010220481,0x122090220481,0x10d943cc5b21e70d943ccf301e679801e6f3007a730a52dcc02d9f301e62d93802a947982d919a1d0ece6,0x1425d0220501,0xf379803cde600fb1273001e9cc79fe3f206553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x1425d0220501,0x14a5f0220501],
[0x0,0x108010200481,0x120010200481,0x108010200481,0x0,0x0,0xf30003cc7983defc003db30079bcc0798f3007a7301e63cc003db301e60f31e603cc7980f3003cfebb56,0x0,0xf30007983cc1f53f307a730079bcc0798f3007a7301e63cc001f5301e60f31e603cc7980f3001e610856,0x120010200481,0x100010200481,0x120010200481,0x100010200481,0x1404d0204481,0xf300f31e60f311160f30f30079bcc0798f3007a7301e63cc0f30f301e60f31e603cc7980f30f3097f556,0x1404d0204481,0x100010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4562 : TreeBound (n := 4) 107 (programCode 0x4a2b076072) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x182081484222,0x182081484222,0x182081484222,0x182081484222,0x0,0x0,0x182081484222,0xc00030040041001004004108000820020100e4,0x0,0x0,0x182089484222,0x0,0x0,0x182088484222,0x0,0x182088484222,0xc00030040041001080006008000c00020100e4,0x0,0x182081480222,0x182081480222,0x182080480222,0x182081480222,0x0,0x0,0x182081480222,0xc00030040041001004004108004020100904e4,0x44580005b200016c81e601e679801e6f3007a8233ce22c0001e9cde63cd5d597e11160003cc1e61df6,0xc00030040041001008004208000a00020100e4,0x182089480222,0xc00030040041001010004408000a00020100e4],
[0x0,0x182088480222,0x0,0x182088480222,0x0,0x182081484222,0x182081484222,0x182081484222,0x182081484222,0x79f9801e7e6016cf9800000000007983cc1e600079bcc01e7e60079bcc01e61e60798f301e61e703885,0x0,0x182081484222,0xc00030040041001004004108001020040305e4,0x0,0x0,0x182089484222,0x0,0x0,0x182088484222,0x0,0x182088484222,0x79f9801e7e6016cf9800000000007983cc1e60f3003cfcc01e6f3003cc01e61e60798f301e61e703885,0x0,0xa00038540041001080006008002400080542e4,0x804020140041001080006008002400080542e4,0x0,0x0,0x0,0x810020440041001080006008002400080542e4,0x0,0x820020840041001080006008002400080546e4,0x800021040041001080006008002400080542e4],
[0x84002104004100108000600800240008054ae4,0x804028040041001080006008002400080542e4,0x88002204004100108000600800240008055ae4,0x814028540041001080006008002400080542e4,0x900024040041001080006008002400080562e4,0x810030040041001080006008002400080542e4,0xa00028040041001080006008002400080542e4,0xc00030040041001080006008080400020100e4,0xc00030040041001080006008004400100904e4,0xc00030040041001080006008080400201108e4,0xc00030040041001080006008008400201108e4,0x0,0x409010210481,0x420010210481,0x409010210481,0x0,0x0,0x810020440041001080006008000c01008142e4,0x0,0x820020840041001080006008000c01008144e4,0x420010210481,0x400010210481,0x420010210481,0x400010210481,0x441010210481,0x400010210481,0x441010210481,0x400010210481,0xc00030040041001080006008010400402118e4,0x0,0x50a0f0220481,0x420010220481],
[0x50a0f0220481,0x0,0x0,0x810020440041001080006008040c01008142e4,0x0,0x820020840041001080006008000c00020100e4,0x420010220481,0x400010220481,0x420010220481,0x400010220481,0xc43110220501,0x400010220481,0xc43110220501,0x400010220481,0x0,0x409890218481,0x420010200481,0x409890218481,0x0,0x0,0x810020440041001080006008020400804162e4,0xc00024140041001080006008020400804120e4,0x820020840041001080006008020400804124e4,0x420010200481,0x400010200481,0x420010200481,0x400010200481,0xc43110220501,0x400010200481,0xc43110220501,0x400010200481,0x0],
[0x50a0f0220481,0x420010220481,0x50a0f0220481,0x808020240041001080006008000400000100e4,0x0,0x0,0x0,0x0,0x420010220481,0x400010220481,0x420010220481,0x400010220481,0xc43110220501,0x400010220481,0xc43110220501,0x400010220481,0x0,0x408010200481,0x420010200481,0x408010200481,0x0,0x0,0x810020440041001080006008040401008142e4,0x0,0x820020840041001080006008040401008144e4,0x420010200481,0x400010200481,0x420010200481,0x400010200481,0x441010210481,0x400010200481,0x441010210481],
[0x400010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4723 : TreeBound (n := 4) 107 (programCode 0x4a2b076073) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600025f80003cde6016cfd4c5d2553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0xc02030040041001080006008000c00020100e4,0x25f800111600025f8000799e6044676cc219513003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x182081484222,0x182081484222,0x182081484222,0x182081484222,0x0,0x0,0x182081484222,0x1400150040041001004008108001020040205e4,0x0,0x0,0x182089484222,0x0,0x445800111600025f800079bcc025f83cc2082de607987981e61e603cc0079bcc01e6f379801e722395,0x182088484222,0x445800111600025f8000003cc044583cc20833980799e601e63cc03cc00003cc03ccf4e6001e722395,0x182088484222,0x0,0x108890208481,0x120890208481,0x108890208481,0x0,0x0,0x0,0x0,0x0,0x120890208481,0x120890208481],
[0x120890208481,0x16c80799e601e76c803cde601e67980798f3007a730b643cc0f30f301e6408ed90f3079803ccf3088ce56,0x140cd0208481,0x0,0x140cd0208481,0x0,0x0,0x400010040041001040000008002000080000e4,0x44580005b200025f83cc1e600007983cc000109c879bcc007983cc3cfcc003cc0000408c001e64dc35,0x82080408022,0x0,0x0,0x0,0x82080408022,0x4400110040041001004020108002020080804e4,0x44580005b200025f83cc1e600007983cc00000f307983cc07983cc3cfcc003cc0000408c001e64dc35,0x44580005b200025f83cc1e600007983cc0000f30079bcc007980003cfcc003cc0000408c001e64dc35,0x0,0x44580005b200025f83cc1e600007983cc0000f30079bcc007980003cfcc003cc0000408c001e64dc35,0x0,0x0,0x0,0x0,0x445800111600025f800799e601ed983cc2046f30079bcc01e6f3003cc07983cc1e60f303cc1e703d95,0x0,0x401010020041001000001008002000100000a4,0xc00130020041001000804028902020100904a4,0x82080408022,0x1400150040041001001008048004020100a05e4,0x0,0x0,0x82080408022],
[0x4400110040041001004020108004020100804e4,0x0,0x44580005b200025f83cc1e600007983cc0000f30079bcc007980003cfcc003cc0000408c001e64dc35,0x401010020041001000001008002000100000a4,0x44580005b200025f83cc1e600007983cc0000f30079bcc007980003cfcc003cc0000408c001e64dc35,0x445800111600025f800079bcc025f83cc2082de607987981e61e603cc0079bcc01e6f300799e722395,0x0,0x25f800111600025f8000799e6044676cc21945cc03cde601e63cc03cc00799e603ccf3016c9e703885,0x0,0x0,0x109010210481,0x121010210481,0x109010210481,0x0,0x0,0x16c800f3f300105fc003ea601e679801e6f3007a730b643cc0798f301e6044859000811800f37983d5776,0x0,0x0,0x121010210481,0x101010210481,0x121010210481,0x121010210481,0x1414d0210481,0x1a943cc0f303cd2fc0f31e601e679801e6f3007a730d4a3cc0798f301e6222f5281e679800f37985b3df6,0x1414d0210481,0x121010210481,0x0,0x108010200481,0x120010200481,0x108010200481,0x0,0x0],
[0x40013000440041001080202008008400208042e4,0x0,0x40023000840041001080202008008400208044e4,0x120010200481,0x100010200481,0x120010200481,0x100010200481,0x141cd0218481,0x40103004040041001080202008008400208060e4,0x141cd0218481,0x100010200481,0x402010040041001080002008000401000000e4,0x0,0x108010200481,0x120010200481,0x108010200481,0x0,0x0,0x40013000440041001080202008010400408042e4,0x0,0x40023000840041001080202008010400408044e4,0x120010200481,0x100010200481,0x120010200481,0x100010200481,0x1100044000020042880082002000022000814e3,0x40103004040041001080202008010400408060e4,0x1200048000020042880082002000022000814e3,0x100010200481,0x0,0x10a0f0220481,0x122090220481],
[0x10a0f0220481,0x0,0x0,0x1e600005b200025f83cc1e607987984458000f3003cfcc007a73003ccf3001ed98003d39801e64d575,0xf33cc0f33cc01e679f9801e7e679fdc5a06553001e9cc01e6f3003cc79800f4e600f379801e703375,0x25f80011160001f5307983cc1e689a6cc9cdcb3003cfcc01e6f3003cc79801e7e600f379801e8e9885,0x122090220481,0x102010220481,0x122090220481,0x1008040020000800080082002020020800814e3,0x1425d0220501,0x3ccf300f33cc01ed987981e61e6811c45a046f30079bcc01e6f3003cc79803cde600f379801e703d95,0x1425d0220501,0x14a5f0220501,0x445800111600025f800799e601ed983cc2046f30079bcc01e6f3003cc07983cc1e60f6cc001e703d95,0x0,0x10a0f0220481,0x122090220481,0x10a0f0220481,0xf30798f3079825f8fa980025f879bc46a22b0d001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x0,0x0,0x1e67980f33cc01e67a73001ed987a76cc219513003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x0,0x122090220481,0x102010220481,0x122090220481,0xf307992c014a2ca05a180025f8e5b58865ff0d001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x1425d0220501,0x1e67980f33cc026c5173001ed987af325219513003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x1425d0220501,0x14a5f0220501],
[0x402010040041001080002008040401000000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4884 : TreeBound (n := 4) 107 (programCode 0x4a2b076074) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0x0,0x422220000000180004222200000004800042222110100008440000021101088800000002010000008040000010020000010100422000100000000400008000210880001000487fca7,0x182081484222,0x1400050040041001001008148004028100a05e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0x16cf9805b3e60079f9800000000007983cc1e6007983cc1e61e616c83cc01e61e60798f301e61e703885,0x0,0x182081484222,0x1400050040041001000808028004020100a05e4,0x25f800097e00025f80f30079bcc0798f30079801116000f303cc111600f4e60f3001e60f3003cfffb6,0x182081490a62,0x0,0x182081490a62,0x0],
[0x0,0x0,0x0,0x0,0x182081484222,0x182081484222,0x182080480222,0x182081484222,0x0,0x25f800097e00025f80f30079bcc0798f300798001e60079803cde7e6001e63cc1e600001e603cc33b6,0x182081484222,0x1400050040041001000008108004000100a05e4,0x410120001040480004000200000008800040000000104008000020020001000000000001008000004020000020100000020100020000080040000200100001000100001002086eba7,0xc00050020041001040005228208244201108a4,0x1400050040041001001008048001009000201e4,0x445800111600025f81e60079f9801e6f30079f98002046000820eea603cc007a7344767e61edab5356,0x0,0x0,0x0,0x0,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0x1400050040041001001008048000002000201e4,0x0,0x182081484222,0x1400050040041001001008048004020100a05e4,0x0,0x182081490a62,0x1400050040041001001008048001009000201e4],
[0x182081490a62,0x1400050040041001001008048000002000201e4,0x0,0x1400050040041001001008048000002000201e4,0x0,0x0,0x0,0x0,0x0,0x20001000020001000200010000200012000004002000008020000080020000080000000010000810000000100100008100040000000100008004400020001000000040002753a8,0x3cc0000f300001e601e600f379803ccf30079800001e600f379801e63cc0000f3079a22c0007985936,0x3b9b4135947735b1cd650ee6b45cd650ee6d04d6503b9ae7d4d85943b9bb86b280ee6d04d6500ee6d04d650ee6b9f35940ee6b280000001dcd6500003b9acbe08ffcbdd11eaca07736827a0eb9f359400001dcd65ee6b2f73597b9acbdcd650000f5de814000430e257faac0a,0x25f80007980001e610230079bcc0798f300798001e60000003cc01e63cc1e60f300003cc0003cc33b6,0x0,0x1e7e6007980001e7e6f30079bcc0798f300798001e60000003cc01e63cc1e60f300003cc0003cc33b6,0x3d398007b66001e7e7e601e63cc0798f3007afbf08de9cc003db31e63cc2d988b03cc3cc000454ec26,0x20001000021000000200010000210002000008002000008020000080020000080000000010000010000000000100008100040000000100008000400020001000000040002793a8,0x3d398007a73001e9cde601e63cc0798f3007b4066ede9cc003d399e63cc35345705b23cc0004994426,0x1e600007980001e600f30079bcc0798f300798001e60000003cc01e63cc1e60f300003cc0003cc33b6,0x0,0x0,0x408c00081180020461e601e63cc0798f3007aecdeedf53000408c1e63cc1e688b00012fc0003cc3c26,0x0,0x0,0x0,0x0,0x3cc1e60f307981e6111600f379803ccf3007980f301e63db37987b663cc001f53079deec000812cc36,0x222de612860f42bb84c300f379803ccf3007980f300f33db37987b663cc001f5307a493c000812c726,0x1e67980f31e601e63db300f379803ccf3007980f300f33db37987b663cc001f5307a493c000812c726,0x1e6798111915c1e61f5300f379803ccf3007980f300f33db37987b663cc001f5307a493c000812c726,0x1e67980f33cc01e67a7300f379803ccf3007980f300f33db37987b663cc001f5307a493c000812c726,0x1e60000f3f3001e7e6f300f379803ccf3007980f300f33db37987b663cc001f5307a493c000812c726],
[0x1e9cc00f3f3001e7e6f300f379803ccf3007980f300f33db37987b663cc001f5307a493c00081a5f26,0x3cc1e6102379820461e600f379803ccf3007980f301e63db37987b663cc001f53079deec000812cc36,0x1e9cc00f4e6001e9ccf300f379803ccf3007980f300f33db37987b663cc001f5307a493c00081a5f26,0x1e679812860f41e600f300f379803ccf3007980f300f33db37987b663cc001f5307a493c000812c726,0x2046000fa98001f530f300f379803ccf3007980f300f33db37987b663cc001f5307a493c00084f8726,0x0,0x204600102300020460f300f379803ccf3007980f300f33db37987b663cc001f5307a493c00084f8726,0x0,0x182081484222,0x182081484222,0x182081480222,0x182081484222,0x1400050040041001000008048000002000201e4,0x0,0x182081484222,0x1400050040041001004008148004020100a05e4,0x0,0x0,0x1400050040041001001008048001009000201e4,0x0,0x1400050040041001000008048000002000201e4,0x1dcd65ee6b2800003b9acbdd3eadc832f73597b9aca001ddc4bb2800003b9acbdcd6501dcddc4fab8c205863ba9b0b2f7359407735941dcd82cd650ee6c166b280ee6c166b2877360b3594077360b3594000003bb89765001dd50c80b0c1dcddc35940eee25d94000ee6ee95304f99,0x1400050040041001000008048000002000201e4,0xf5e0983cc1e600081183d59f3900fa983cc007981e679801e67980f33cfd57e3cc0f30408c001e64dc35,0x445800111600025f81e600f379803ccf3007981e601e67a73798f4e63cc003db307a952c00079a3f36,0x0,0x0,0x0,0x0,0x0,0x204600079f9801e7e6f30079bcc0798f3007983cde600f3003cfcde63cc1e60f301e63cc00040cbfb6,0x1e67980f31e601e63db300f379803ccf3007980f300f523b379bcde63cc10425309c387c00081a5f26],
[0x420000101080000404100000800200001042002000108000000010000000020000000200010000400040000800080001000100400000101000000404000000810000001001087fa67,0x1e67980f33cc01e67a7300f379803ccf3007980f300f5607379bcde63cc0f4f5309cb1fc000812c726,0x1e60000f3f3001e7e6f300f379803ccf30079800000f4e6f379bcde63cc0f30f3097f2fc000811d426,0x1e9cc00f3f3001e7e6f300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc0008196c26,0x0,0x1e9cc00f4e6001e9ccf300f379803ccf30079879800f8b2f379bcde63cc16c8f30d4b2fc0008655c26,0x1000100004b006000204000000200001000008004000020020000080020000080000200009640c2002080000010010010004000000110000a0064000040010000000400026aba8,0x2046000fa98001f530f300f379803ccf30079bcc0010416f379bcde63cc0f388b098115c00084e9426,0x0,0x408c00102300020461e600f379803ccf30079f980020646f379bcde63cc0f388b098022c000811d936,0x0,0x0,0x0,0x0,0x3cc1e60f307981e6111600f379803ccf30079879801e7e6f379bcde63cc0f30f3098022c000811d936,0x1e9cc0129984c2c0622300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc0008196c26,0x1e67980f31e601e63db300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc000812c726,0x222c001282bcc1e61f5300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc000811d426,0x1e67980f33cc01e67a7300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc000812c726,0x1e60000f3f3001e7e6f300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc000811d426,0x1e9cc00f3f3001e7e6f300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc0008196c26,0x3cc1e6102379820461e600f379803ccf30079879801e7e6f379bcde63cc0f30f3098022c000811d936,0x1e9cc00f4e6001e9ccf300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc0008196c26,0x222c001282bcc1e600f300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc000811d426,0x2046000fa98001f530f300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc00084e9426,0x0,0x204600102300020460f300f379803ccf30079879800f4e6f379bcde63cc0f30f30d4b2fc00084e9426,0x0,0x182089484222,0x182089484222,0x182089480222,0x182089484222],
[0x79f9801e7e6016cf9800000000007983cc1e6007983cc3cc1e607983cc01e61e60798f301e61e703885,0x0,0x182089484222,0x1400050040041001001009008004028100a05e4,0x0,0x182089490a62,0x1400050040041001001009008001009000201e4,0x182089490a62,0x140005004004100100100900800100a000201e4,0x0,0x140005004004100100100900800000a000201e4,0x0,0x0,0x0,0x0,0x0,0x1e60f30f307981e6102300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc0007d51426,0x3cfcc010323002268de600f379803ccf300798f3001e9ccf379f99e63cc0f30f30b6622c0008197136,0x1e67980f31e601e63db300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc00084f8726,0x408c0012097981e6204600f379803ccf300798f3001e9ccf379f99e63cc0f30f30b6622c000811d936,0x3ccf300f33cc01e67b6600f379803ccf300798f3001e9ccf379f99e63cc0f30f30b6622c000813bf36,0x1e60000f3f3001e7e6f300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc0007dcac26,0x1e9cc00f3f3001e7e6f300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc0007dcac26,0x3cc1e6102379820461e600f379803ccf300798f3001e9ccf379f99e63cc0f30f30b6622c000811d936,0x1e9cc00f4e6001e9ccf300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc0007ebdc26,0x408c0012097981e601e600f379803ccf300798f3001e9ccf379f99e63cc0f30f30b6622c000811d936,0x2046000fa98001f530f300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc0007d51426,0x0,0x204600102300020460f300f379803ccf30079879800f6ccf379f99e63cc0798f30b652fc00084e9426,0x0,0x4459e6097e0001e601e601e63cc0798f3007a73408de600003cc01e63cc1e688b00003cc0003cc3c26,0x0],
[0x0,0x1e60f307983cc1e610230079bcc0798f300798001e60000003cc01e63cc1e60f300003cc0003cc33b6,0x1e600007980001e600f30079bcc0798f300798001e60000003cc01e63cc1e60f300003cc0003cc33b6,0x0,0x4459e607980001e6111601e63cc0798f3007a73408de600003cc01e63cc1e688b00003cc0003cc3c26,0x0,0x1000000004020000020000000020080100000800400002002000008002000008000020000944042002080000010010010004000000110000a0024000040010000000400026aba8,0x1008000004020000020080000020080100000800400002002000008002000008000020000944042002080000010010010004000000110000a0024000040010000000400026aba8,0x0,0x1dd11eaca0077447ab28003ba23d59403ba23d594003ba23d94daca03b9bb86b280ee6b9f35940ee729b5940ee6b9f35940ee88f5650000ee6b2bb9acdb9ca6d73e6b2f73594001dcf41d73e6b9f3597b9acbdcd6500007ea8ed7b9acbdcd650ee6b9f35940001dcd662781c1a,0x1e600007980001e600f30079bcc0798f300798001e60000003cc01e63cc1e60f300003cc0003cc33b6,0x0,0x445800097e0001e601e601e63cc0798f3007a73408de600003cc01e63cc1e688b00003cc0003cc3c26,0x0,0x25f800111600025f80f300f379803ccf30079bcc0010230f37b661e63cc00088b079b15c0007985426,0x0,0x16c80005b20b647980003cde6016cfd4c20649cc03cde601e63cc03cc003cde600f3f3003cde703885,0xc00050020041001000806028200c04020100a4,0x44580011160798798000f33cc044583cc20833980799e601e63cc03cc00f33cc03ccf300799e722395,0x7980001e60b6479800000000007983cc1e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x7980001e60b6479800000000007983cc1e603cc03cde601e63cc03cc00001e60000f300001e703885,0x0,0x0,0x7980001e60b6479800000000007983cc1e603cc03cde601e63cc03cc1e601e6f300f31e601e703885,0x0,0x0,0x0,0x7980001e60b6479800000000007983cc1e603cc03cde601e63cc03ccf3001ed9800f3f3001e703885,0x200016000800040002000080008000400000001600080000000200010000000008000040040000200200001000200001004000000416000002000000010100000010020852ba7],
[0x445800111600025f81e600f379803ccf30079f980020460f37d4c1e63cc00088b079a22c0007985936]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5109 : TreeBound (n := 4) 107 (programCode 0x4a2b076075) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x811800204600081180003cde6016cfd4c5d24600f4e6003ea6000f6cfcc001023000f6cc001e703375,0x402010040041001000800028080402000000e4,0x8118002046000811800079bcc025f83cc2082c03d39800f4e6001e9cfcc003db3000f6cc001e722395,0x0,0x402010040041001001000048000000000000e4,0xc02030040041001001004048000804020100e4,0x402010040041001001000048000000000000e4,0x1402050040041001001008048001008040201e4,0x402010040041001001000048000002000000e4,0x0,0x402010040041001001000048000000000000e4,0x4402110040041001001020048004020100a05e4,0x0,0x3d39803cde60f307980f30079bcc0798f300798020460007b6600204600f37980f307980f31e6131156,0x402010040041001001000048000001000000e4,0xf379801e7e60f307980f30079bcc0798f300798020460007a7300204601e679807983cc1e60f31aa956,0x0,0x0,0x0,0x0,0x0,0x0,0x4020140041001000000028080402000000e4,0x0,0xf300007983cc10230079f9801e6f300798000000000000003ea63cc0000f307983cc0000001586,0x210882240481,0x220882240481,0x210882240481,0x210882240481,0x220882240481,0x220882240481],
[0x220882240481,0x210882240481,0x240882240481,0x220882240481,0x240882240481,0x210882240481,0x0,0x0,0x40004020140041001002200088080012008040e4,0x0,0x40008040240041001002200088080012008043e4,0x210000240481,0x200000240481,0x210000240481,0x200000240481,0x220000240481,0x200000240481,0x220000240481,0x200000240481,0x241884240481,0x220000240481,0x241884240481,0x200000240481,0x402010040041001000000008080002000000e4,0x402010040041001004000108080022000000e4,0x1ed98007b660008118408de6003d398408c0000f307983cc07983cc3cfcc003db3000408c001e64dc35,0x1ed98007b6600081183cc1e600007983cc0000f30079bcc007980003cfcc003db3000408c001e64dc35,0x0,0x0,0x0,0x0,0x0],
[0x211004240481,0x201004240481,0x211004240481,0x221004240481,0x221004240481,0x201004240481,0x221004240481,0x221004240481,0x241884240481,0x221004240481,0x241884240481,0x221004240481,0x1ed98007b6600081183cc1e600007983cc0000f30079bcc007980003cfcc003db3000408c001e64dc35,0x0,0x7980799e601e679808118002046798bdda06664601e67981e61e603cfcc001023000f6cc001e703375,0x4020140041001000000008080002000000e4,0x7981e61e607987980fa98003ea67983cc2086aa607987981e61e603cfcc003db3000f6cc001e7241f5,0x8040240041001000000008080002000000e4,0x2120c8240481,0x202008240481,0x2120c8240481,0x2529c8240501,0x222088240481,0x202008240481,0x222088240481,0x2529c8240501,0x242988240501,0x222088240481,0x242988240501,0x2529c8240501,0x0,0x7980799e601e6798079bcde600fb11bcc204607983cc1e61e600f33cfcc001f53000f6cc001e703885],
[0xf307983cc7983cc088b0079bcc0798f300799e61e61e600020461e63cc1e60f300029c40001e61556,0x7981e61e607987980f3799e601ed983cc204607987981e61e601e63cfcc003db3000f6cc001e703d95,0x1e60f307983cc1e610230079bcc0798f300799e61e61e60003ea61e63cc1e60f300012fc0003cc33b6,0x211004240481,0x201004240481,0x211004240481,0x221004240481,0x221004240481,0x201004240481,0x221004240481,0x221004240481,0x24398c240501,0x221004240481,0x24398c240501,0x221004240481,0x0,0x7980799e601e6798088b000222c798c57206664601e7e601e63cc03cfcc001023000f6cc001e703375,0x0,0x7980f31e6079879810230007d4c79a22c206c34c03cde601e63cc03cfcc001f53000f6cc001e707545,0x0,0x2120c8240481,0x202008240481,0x2120c8240481,0x2529c8240501,0x222088240481,0x202008240481,0x222088240481,0x2529c8240501,0x242988240501,0x222088240481,0x242988240501,0x2529c8240501],
[0x0,0x0,0x0,0x0,0x3cc1e60f307983cc111600f379803ccf30079f980020460f37d4c1e63cc00088b079a22c0007985936,0x210000240481,0x200000240481,0x210000240481,0x200000240481,0x220000240481,0x200000240481,0x220000240481,0x200000240481,0x240882240481,0x220000240481,0x240882240481,0x200000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5254 : TreeBound (n := 4) 107 (programCode 0x4a2b076076) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x4000000110000000240000000800000000c2002000108000000000000000040000004000010010000040040000080100000100420000100080000400000000800400001001087faa7,0x0,0x0,0x4200000110000000142000000202000000c0202100100800100000400400001001004000010010000040040000080100000100002000100002000400004000800010001001887f627,0xf6d39840146607d53a7300f379803ccf3007a730007d4c0f4f5301e6003ea6000fa9f981e61eda8a66,0x0,0xf307983f9ae607d53a7300f379803ccf3007a730007d4c0f4f5301e6003ea6001ed9f983cc1eda8a66,0x811800798798082fe0f30079bcc0798f3007a7301e63cc003db301e600f4e6003d39800f303d028756,0xf33cc03fb1ae07d53a7300f379803ccf3007a730007d4c0f4f5301e601e7e60079f9f98f301ee22266,0xf6d3983f9ae607d53a7300f379803ccf3007a730007d4c0f4f5301e6003ea607a7a9fa73001eda8a66,0xf33cc03faa1607d53a7300f379803ccf3007a730007d4c0f4f5301e601e7e600f379f99e601ee22266,0x432a400110000000440000000200010000e400219530000000084000000210000210c000010010000040040000080100000100200000100800000400400000801000001001087fe27,0x0,0x432a400110000000440000000200010000e800219530000000088000000220000210c000010010000040040000080100000100200000100800000401000000802000001001087fe27,0xf300003f9ae607d53a7300f379803ccf3007a730007d4c0f4f5301e60f31e6079879fa73001eda8a66,0x0,0x20000100080000400100000800100000a0000100020000400200000800200000806833101002000100040000008020001000400034199000010004000000810000002008117dfa8,0x2004080140041001000810028080402000542e4,0x10ca94e403ea6000f33cfcd8e14201e679807980003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x2004080140041001042811028080616008542e4,0x20a0825404c2,0x20a0825404c2,0x20a0825404c2,0x200408014004100100081020808060200144ae4,0x20a084541d02,0x20a08a5414c2,0x20a084541d02,0x20a08a5414c2],
[0x20a0885414c2,0x0,0x20a0885414c2,0x0,0x0,0x81180079801e681180f30079bcc0798f3007a7301e63cc003db301e60005b200044580003cfcfebb56,0x0,0x0,0x1000080001080000010200000010800008000080080000080080000800200000804000000810000400040000008100001000400020000800080004000200010040002020105b1a8,0x0,0x0,0x0,0x400000011000000044000000080000000142002000108000000000000000050000004000010010000040040000080100000100020000100040000400040000800100001001087fa27,0xf6cc00401280081180f300f379803ccf3007a730007d4c0f4f5301e601e7e60079f9f98f301eda8a66,0x400000011000000044000000080000000142002000108000000000000000040000004000010010000040040000080100000100020000100080000400100000800200001001087faa7,0xf6cc003f9900081181e600f379803ccf3007a730007d4c0f4f5301e603cde600f379f99e601eda8f76,0x0,0xf307983ea8d9081180f300f379803ccf3007a730007d4c0f4f5301e60f31e603cc79f9f9801eda8a66,0x0,0xf307983ea7e6081180f300f379803ccf3007a730007d4c0f4f5301e60f31e6079879fa73001eda8a66,0x0,0x0,0x0,0x0,0x0,0x0,0x20a0825404c2,0x20a0825404c2,0x20a0825404c2,0x0,0x20a084541d02,0x20a08a5414c2],
[0x20a084541d02,0x20a08a5414c2,0x20a0885414c2,0x0,0x20a0885414c2,0x0,0x6104c1240481,0x2014088540041001000810028080402000542e4,0x6104c1240481,0x0,0x410882240481,0x10000240481,0x410882240481,0x10000240481,0x11004240481,0x10000240481,0x11004240481,0x10000240481,0x6120c8240481,0x11004240481,0x6120c8240481,0x10000240481,0x402008044008100108022200808042200084504,0x0,0x6104c1240481,0x0,0x6104c1240481,0x0,0x410882240481,0x10000240481,0x410882240481,0x10000240481],
[0x11004240481,0x10000240481,0x11004240481,0x10000240481,0x6120c8240481,0x11004240481,0x6120c8240481,0x10000240481,0x402008084008100108022200808042200084504,0x408008104008100108022200808042200085504,0x408008104008100108022200808042200085504,0x422008804008100108022200808042200084504,0x408008204008100108022200808042200085504,0x422008004008100108022200808042200084504,0x420008404008100108022200808042200084504,0x0,0x641cc1240481,0x2004090040041001000810028080402000542e4,0x641cc1240481,0x0,0x441002240481,0x40000240481,0x441002240481,0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481],
[0x420008804008100108022200808042200084504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5383 : TreeBound (n := 4) 107 (programCode 0x4a2b076077) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8118007b66000fa980003cde6016cfd4c5d24600f4e6003ea6000f6cfcc001023000f6cc001e703375,0x0,0x82081400022,0x182081484222,0x82081400022,0x182081484222,0x0,0x0,0x82081400022,0x4400130020041001000820028902020100904a4,0x1ed98002046000fa984273e600007983db300109c879800007a76cc3cc3cc03ccf3003ccf301e64dc35,0x1ed98002046000fa984273e600007983db300109c879800007a76cc3cfcc003db30003cc0001e64dc35,0x0,0x1ed98002046000fa984273e600007983db300109c879800007a76cc3d027203db6cc03cc0001e64dc35,0x0,0x0,0x0,0x0,0xfa98007b66000fa98000799e6044676cc2194201e9cc00f4e6001e9cfcc001f53000f6cc001e703885,0x0,0x82081400022,0x182081484222,0x82081400022,0x182081484222,0x400010040041001001000048000002000000e4,0x0,0x82081400022,0x4400150040041001001020048004020100a05e4,0x0,0x1ed98002046000fa983cc1e600007983cc0000f30079800007a73003cfcc003db30003cc0001e64dc35,0x400010040041001001000048000001000000e4],
[0x1ed98002046000fa983cc1e600007983cc0000f30079800007a73003cfcc003db30003cc0001e64dc35,0x400010040041001001000048000002000000e4,0x0,0x400010040041001001000048000002000000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x220882240481,0x210882240481,0x210882240481,0x220882240481,0x220882240481,0x220882240481,0x210882240481,0x240882240481,0x220882240481,0x240882240481,0x210882240481,0x0,0x0,0x20a0825404c2,0x0,0x20a0825404c2,0x210000240481,0x200000240481,0x210000240481,0x200000240481,0x220000240481],
[0x200000240481,0x220000240481,0x200000240481,0x241884240481,0x220000240481,0x241884240481,0x200000240481,0x82080440022,0x4400110040041001004020108080022000804e4,0x0,0x0,0x16c8001f53000222c00097e01e679801e6f300798f7824000445803cde63cc2d90f301e63cc07983cddf6,0x0,0x0,0x211004240481,0x201004240481,0x211004240481,0x221004240481,0x221004240481,0x201004240481,0x221004240481,0x221004240481,0x241884240481,0x221004240481,0x241884240481,0x221004240481,0x0,0x0,0x80a0844410a2,0x0,0x80a0844410a2,0x210000240481],
[0x200000240481,0x210000240481,0x200000240481,0x220000240481,0x200000240481,0x220000240481,0x200000240481,0x241884240481,0x220000240481,0x241884240481,0x200000240481,0x82088440022,0x0,0x0,0x80a0844410a2,0x0,0x80a0844410a2,0x210000240481,0x200000240481,0x210000240481,0x200000240481,0x220000240481,0x200000240481,0x220000240481,0x200000240481,0x240882240481,0x220000240481,0x240882240481,0x200000240481,0x0,0x798079f9801e6f3008118002046798bdda06664601e67981e61e603cfcc001023000f6cc001e703375,0xa080440022],
[0x1e601e67980798f300fa98003ea67983cc2086aa607987981e61e603cfcc003db3000f6cc001e7241f5,0xa080440022,0x2120c8240481,0x202008240481,0x2120c8240481,0x2529c8240501,0x222088240481,0x202008240481,0x222088240481,0x2529c8240501,0x242988240501,0x222088240481,0x242988240501,0x2529c8240501,0x82088440022,0x0,0x798079f9801e6f30081180025f8798c57206664601e7e601e63cc03cfcc001023000f6cc001e703375,0x0,0x798079f980798f300fa980025f879a31f222a38601e7e601e63cc03cfcc001023000f6cc001e703375,0x0,0x2120c8240481,0x202008240481,0x2120c8240481,0x2529c8240501,0x222088240481,0x202008240481,0x222088240481,0x2529c8240501,0x242988240501,0x222088240481,0x242988240501,0x2529c8240501],
[0x82088440022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5544 : TreeBound (n := 4) 107 (programCode 0x4a2b076078) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1ed98007b66000fa981e600f379803ccf3007a73000f6cc0f6db301e63cc1e60f307a76cc003cc20276]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5545 : TreeBound (n := 4) 107 (programCode 0x4a2b076079) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x4084d0204481,0x409010210481,0x4084d0204481,0x0,0x408890208481,0x8004200100000000080082002080020000814e3,0x408890208481,0x8004200100000000080082002080020000814e3,0x409010210481,0x408010200481,0x409010210481,0x408010200481,0x40a0f0220481,0x409890218481,0x40a0f0220481,0x408010200481,0x0,0x0,0x420010210481,0x0,0x0,0x420010208481,0x804200140041001080006008002400080542e4,0x420010208481,0x804200140041001080006008004400100904e4,0x420010210481,0x420010200481,0x420010210481,0x420010200481,0x420010220481],
[0x420010200481,0x420010220481,0x420010200481,0x0,0x4084d0204481,0x409010210481,0x4084d0204481,0x0,0x408890208481,0x0,0x408890208481,0x0,0x409010210481,0x408010200481,0x409010210481,0x408010200481,0x40a0f0220481,0x409890218481,0x40a0f0220481,0x408010200481,0x0,0x0,0x0,0x0,0x0,0x20001001000001000200010010000012000008002000008020000080020000080000000010000010000000000100008100040000000100008000400020001000000040002793a8,0x3cc1e7f53079bcc0111600f379803ccf3007980f301e63dc2a987b663cc001f530b69eec00fb1a6436,0x0,0x3cc1e7f53079bcc0111600f379803ccf3007981e601e67a82a98f4e63cc003db30b7552c00faa1d736,0x0,0x3cc1e7f53079bcc0111600f379803ccf30079879801e7e702a9bcde63cc0f30f30d4c22c00fb197136,0x0],
[0x1e60f4f53079bcc0102300f379803ccf30079879800f6cd02a9f99e63cc0798f30b652fc00fadcac26,0x200300000400e000010020000010020004300200010c000000010000000040000002000010004000040010000080010000100400000101000000404000000810000001001087faa7,0x1e60f4f53079bcc0102300f379803ccf30079bcc001023102ab661e63cc00fb8b0bc235c00fa9fec26,0x200300000400c0000100200000100200042002000108000000010000000040000002000010008000040010000080020000100400000101000000404000000810000001001087faa7,0x3cc1e7f53079bcc0111600f379803ccf30079f98002046102ad4c1e63cc00088b0ba2e2c00fa9ff136,0x0,0x4104c1240481,0x8010200410000400080080402080022000814e3,0x4104c1240481,0x0,0x410882240481,0x410000240481,0x410882240481,0x410000240481,0x411004240481,0x410000240481,0x411004240481,0x410000240481,0x4120c8240481,0x411004240481,0x4120c8240481,0x410000240481,0x140202004400810010802a20080806a200285504,0x0,0x4104c1240481,0x0,0x4104c1240481,0x0,0x410882240481,0x410000240481,0x410882240481,0x410000240481],
[0x411004240481,0x410000240481,0x411004240481,0x410000240481,0x4120c8240481,0x411004240481,0x4120c8240481,0x410000240481,0x140202008400810010802a20080806a200285504,0x420010240481,0x400010240481,0x420010240481,0x400010240481,0x441010240481,0x400010240481,0x441010240481,0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5658 : TreeBound (n := 4) 107 (programCode 0x4a2b07607a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040021004008100108028200808068200201104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5659 : TreeBound (n := 4) 107 (programCode 0x4a2b07607b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x401010040041001080002008080402000000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5660 : TreeBound (n := 4) 107 (programCode 0x4a2b07607c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040041004008100108028200808068200201104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5661 : TreeBound (n := 4) 107 (programCode 0x4a2b07607d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1e600081180020460008118002046798bdda06739001e9cc01e6f3003cfcc001023000f6cc001e703375,0x4000140041001080002008080402000000e4,0x1e6001ed98007b66000fa98003ea67983cc20877f0079bcc01e6f3003cfcc003db3000f6cc001e7241f5,0x0,0x1e67980799e601e60008118002046798b642066460f6cc003ea6000f6cfcc001f53000f6cc001e703885,0x0,0x1e67980799e601e6001ed98007b667983cc208a583d39800f4e6001e9cfcc003db3000f6cc001e726055,0x0,0x0,0x79810255f83cc79810230079bcc0798f30079807b660079faafc7b663cc260bef000408c07ab396d36,0xa080440022,0x8100240041001004000108080022000000e4,0x0,0x3cc001023798408c0010230079bcc0798f3007983cde603cc79bcfcde63cc25fcbf01e63cc079c08f3b6,0xa088440022,0x1c80a51e60798204600111601e61e60798f300798f3e405373003d39ad93cc39023d00f33cc0b68275b96,0xa080440022,0xa088440022,0x0,0xa088440022,0x0,0x8124c1240481,0x20010800420010402480080402080022000816e3,0x8124c1240481,0x0,0x8128c2240481,0x8138c6240481,0x8128c2240481,0x8120c8240481,0x8130c4240481,0x8138c6240481],
[0x8130c4240481,0x8120c8240481,0x8120c8240481,0x8138c6240481,0x8120c8240481,0x8120c8240481,0x4402100044008100108022200808062200884504,0x1e6003d39803cde60079f9801e7e679fdc5a06553001e9cc01e6f3003cfcc001023000f6cc001e703375,0x20000840041001080002008080402000000e4,0x822090240481,0x802010240481,0x822090240481,0x842110240501,0x842110240501,0x802010240481,0x842110240501,0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5710 : TreeBound (n := 4) 107 (programCode 0x4a2b07607e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1023007d88c01f623007983cde6016cfd4c5d24600f4e6003ea6000f6cfcc001023000f6cc001e703375,0x0,0xf3007d4c001e6f300798001e6044583cc2064601e9cc00f4e6001e9cfcc001f53000f6cc001e703885,0x0,0x0,0x0,0x20400800040041001020100808080102004020e4,0x20400804040041001004100108080022004020e4,0x0,0x0,0x20400800040041001020101008080102004020e4,0x0,0xf307d4c001e6f30079800020467983cc206664601e67981e61e603cfcc001023000f6cc001e703375,0x20400800040041001020100808080102004020e4,0xf307d4c001e6f30079800025f87983cc206664601e7e601e63cc03cfcc001023000f6cc001e703375,0x20400800040041001040101008080102004020e4,0x20004800140041001080102008080402004020e4,0x0,0x102301e9cc00799e600f303cde6016c83cc2064600fa98003ea6000f6cfcc003db3000f6cc001e703d95,0x0,0x111601e9cc00799e600f30f33cc044583cc2082c03d39800f4e6001e9cfcc003db3000f6cc001e722395,0x0,0x0,0x0,0x20400804040041001020100808080102004020e4,0x20400804840041001004100108080022004024e4,0x798b640799e601e60f31e601e679801e6f3007afbb3cc3cc03cc03cde63cc2d90f301e63cc03cc1e7df6,0x20400804040041001008100208080202004020e4,0x20400804040041001020101008080102004020e4,0x20400804040041001010100408080202004020e4],
[0x100000000402000000800c000010000000000000000104002000100008420040001000100004000400008001000010040000010100000040400000081000000100318f3227,0x20400804040041001020100808080102004020e4,0x100000000402000000800c00001000000000000000042000200010000844020000100080000400100000800200001004000001010000004040000008100000010032a73227,0x20400804040041001040101008080102004020e4,0x0,0x0,0x0,0x798001ed98007b6600111601e679801e6f3007aec83cc3cc03cc1e61e63cc2d90f300f33cc03cc1e9c56,0x0,0x0,0x80a0824414c2,0x80a0884410a2,0x80a0824414c2,0x0,0x80a0844410a2,0x80a0884410a2,0x80a0844410a2,0x0,0x80a0884410a2,0x0,0x80a0884410a2,0x1e60001e61e601e67980f30079bcc0798f3007a7301e63cc0f30f301e63cc03ccf307983cc0f30799556,0x20010800440041001080102008080402004062e4,0x20400804040041001080102008080402004020e4,0x20020800840041001080102008080402004024e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x842110240501,0x10240481,0x842110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5775 : TreeBound (n := 4) 107 (programCode 0x4a2b07607f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1e600097e000222c00081180025f8798c57206739001e9cc01e6f3003cfcc001023000f6cc001e703375,0x0,0x1e6007b66001e9cc0dc3f9801ed98874a9ea1d1d3001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x822090210481,0x3cc007b66003cfcc0b64f3001ed987af325219513003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x822090208481,0x0,0x822090208481,0x0,0x822090210481,0x822090210481,0x822090210481,0x822090220481,0x822090220481,0x822090210481,0x822090220481,0x822090220481,0x1e600097e0007d4c000fa980025f879a31f222b0d001e9cc01e6f3003cfcc001023000f6cc001e703375,0x0,0x1e600097e000222c79881180025f87a05d75d2739001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x808020240041001080006008000c00020100e4,0x1e600097e0007d4c798fa980025f87b4c60cb6b0d001e9cc01e6f3003cc003ccf303ccf300799e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000240041001080002008000401000000e4],
[0x0,0x8000240041001080002008000402000000e4,0x0,0x8000240041001080002008000400000000e4,0x9000240041001080002008040401000000e4,0x0,0x8124c1240481,0x40011000440010402480080402080022000816e3,0x8124c1240481,0x0,0x8128c2240481,0x8138c6240481,0x8128c2240481,0x8120c8240481,0x8130c4240481,0x8138c6240481,0x8130c4240481,0x8120c8240481,0x8120c8240481,0x8138c6240481,0x8120c8240481,0x8120c8240481,0x0,0x8324c1240481,0x0,0x8324c1240481,0x0,0x822082240481,0x802000240481,0x822082240481,0x802008240481,0x802004240481],
[0x802000240481,0x802004240481,0x802008240481,0x802008240481,0x802000240481,0x802008240481,0x802008240481,0x3cc007b66003cfcc007a73001ed987a76cc219513003cfcc01e6f3003cfcc001f53000f6cc001e703885,0x0,0x0,0x0,0x0,0x0,0x8529c2240501,0x842108240501,0x8529c2240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x822090240481,0x802010240481,0x822090240481,0x842110240501,0x842110240501,0x802010240481,0x842110240501],
[0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_5872 : TreeBound (n := 4) 107 (programCode 0x4a2b076080) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1084d0204481,0x409010210481,0x1084d0204481,0x0,0x0,0x4000100000000080082002080020000814e3,0x0,0x4000100000000080082002080020000814e3,0x409010210481,0x8010200481,0x409010210481,0x8010200481,0x80a0f0220481,0x0,0x80a0f0220481,0x8010200481,0x40005000140041001080202008080402008040e4,0x0,0x1084d0204481,0x409010210481,0x1084d0204481,0x0,0x0,0x0,0x0,0x0,0x409010210481,0x8010200481,0x409010210481,0x8010200481],
[0x80a0f0220481,0x8000200000000080082002000020100814e3,0x80a0f0220481,0x8010200481,0x0,0x0,0x0,0x0,0x0,0x7980020460007d4c0011160079f9801e6f300798003cc0000f30003ea63cc0000f307983cc0f3079d756,0x80a0824414c2,0x80a0884410a2,0x80a0824414c2,0x0,0x80a0844410a2,0x80a0884410a2,0x80a0844410a2,0x0,0x80a0884410a2,0xf30d4a0001e600001e63cc1e6000000000000007980798f300f33cc03cfcc003db30007d4c001e68a8c5,0x80a0884410a2,0x0,0x0,0x10400400000400080080402080022000814e3,0x0,0x0,0x210882240481,0x10000240481,0x210882240481,0x10000240481,0x411004240481,0x10000240481],
[0x411004240481,0x10000240481,0x8120c8240481,0x411004240481,0x8120c8240481,0x10000240481,0x40011000440041001080202008080402008042e4,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x10000240481,0x210882240481,0x10000240481,0x411004240481,0x10000240481,0x411004240481,0x10000240481,0x8120c8240481,0x411004240481,0x8120c8240481,0x10000240481,0x40021000840041001080202008080402008044e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x40010240481,0x10240481,0x40010240481],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_4416 : TreeBound (n := 4) 107 (programCode 0x4a2b0760) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part102_4417 part102_4562 part102_4723 part102_4884 part102_5109 part102_5254 part102_5383 part102_5544 part102_5545 part102_5658 part102_5659 part102_5660 part102_5661 part102_5710 part102_5775 part102_5872

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part102_0 : TreeBound (n := 4) 107 (programCode 0x4a2b07) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part102_1 part102_2 part102_403 part102_404 part102_1461 part102_1462 part102_1847 part102_1848 part102_2649 part102_2650 part102_2651 part102_2652 part102_2653 part102_2958 part102_3519 part102_4416

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned102 : TreeBound (n := 4) 107 [((0,0),⟨1,1,false⟩),((1,0),⟨2,1,false⟩),((2,0),⟨2,0,true⟩)] := part102_0
open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem one_zero_return_1_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 1 .right))
    (h2 : M 2 0 = some (some 1, Stmt.write 0 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 107 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,1,false⟩),((2,0), ⟨1,0,true⟩)] := by
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
  rcases partitioned101 M hm with h | h
  · exact h
  · exact (h halts).elim


open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem one_zero_return_2_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 1 .right))
    (h2 : M 2 0 = some (some 2, Stmt.write 0 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 107 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,1,false⟩),((2,0), ⟨2,0,true⟩)] := by
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
  rcases partitioned102 M hm with h | h
  · exact h
  · exact (h halts).elim

open Turing Turing.BusyBeaver in
theorem one_zero_middle_machine (M : Machine (Fin 2) (Fin 4)) (q : Fin 4)
    (hq : q = 1 ∨ q = 2)
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 1 .right))
    (h2 : M 2 0 = some (some q, Stmt.write 0 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 107 := by
  rcases hq with rfl | rfl
  · exact one_zero_return_1_machine M h0 h1 h2 halts
  · exact one_zero_return_2_machine M h0 h1 h2 halts

end BeaverBound


theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1.H2 := BeaverBound.one_zero_middle_machine
