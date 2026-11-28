import OMAReductions.R_Constant14_c14_ge_4_R1_H4_R1
import Mathlib.Computability.Partrec
import Mathlib.Tactic

-- Step Constant14.c14_ge_4.R1.H4.R1.H1: hypothesis H1 of reduction Constant14.c14_ge_4.R1.H4.R1
-- Credit: @Narden91

/-!
# Proof of `Constant14.c14_ge_4.R1.H4.R1.H1`

Proves computable enumerability of `𝗭𝗙𝗖`-provable non-halting under the elementary base-`B`
binary Turing machine decoder `dec`:
`∃ f : ℕ →. ℕ, Nat.Partrec f ∧ ∀ c : ℕ, (f c).Dom ↔ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (dec c).2)`.

Architecture:
1. Primitive-recursive Gödel encoding of `ℒₛₑₜ` terms (`Semiterm ℒₛₑₜ ℕ k`) and formulas
   (`Semiformula ℒₛₑₜ ℕ k`) into `ℕ` with strict subformula monotonicity (`a < c`, `b < c`).
2. A single depth-bounded `Primrec.nat_strong_rec` combinator (`formRec`) powering all syntactic
   operations (`wfForm`, `negCode`, `fvSupCode`, and general `Rew` lifting `rewMapCode` covering
   `shift`, `free`, `subst`, `fixitr`, and `univCl`).
3. Primitive-recursive construction of `haltsCode c = encSent (Constant14.halts (dec c).2)` and
   forward witness checker for all axioms of `𝗭𝗙𝗖` (13 fixed axioms + Separation + Replacement).
4. Primitive-recursive flat-trace checker for `FFL.FirstOrder.Derivation` + `Theory.Proof 𝗭𝗙𝗖`,
   closed via `Nat.Partrec.rfind`.
-/

namespace C14H4R1H1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver

/- ## Section 1: Basic Primitive-Recursive Combinators -/

def natPair (a b : ℕ) : ℕ := Nat.pair a b

lemma primrec₂_natPair : Primrec₂ natPair := by
  show Primrec (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
  have h1 : Primrec (fun n : ℕ => Nat.pair (Nat.unpair n).1 (Nat.unpair n).2) := by
    rw [Primrec.nat_iff]
    exact Nat.Primrec.pair (Primrec.nat_iff.mp (Primrec.fst.comp Primrec.unpair))
      (Primrec.nat_iff.mp (Primrec.snd.comp Primrec.unpair))
  have h2 : Primrec (fun p : ℕ × ℕ => Nat.pair (Nat.unpair (Encodable.encode p)).1
      (Nat.unpair (Encodable.encode p)).2) := h1.comp Primrec.encode
  refine h2.of_eq fun p => ?_
  change Nat.pair (Nat.unpair (Nat.pair p.1 p.2)).1 (Nat.unpair (Nat.pair p.1 p.2)).2 = Nat.pair p.1 p.2
  rw [Nat.unpair_pair]

def natPow (b e : ℕ) : ℕ :=
  Nat.rec 1 (fun _ acc => acc * b) e

lemma natPow_eq (b e : ℕ) : natPow b e = b ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change natPow b e * b = b ^ (e + 1)
    rw [ih, pow_succ]

lemma primrec₂_natPow : Primrec₂ natPow := by
  have hstep : Primrec₂ (fun (b : ℕ) (p : ℕ × ℕ) => p.2 * b) :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  exact Primrec.nat_rec (Primrec.const 1) hstep

def natMax (a b : ℕ) : ℕ := if a ≤ b then b else a

lemma natMax_eq (a b : ℕ) : natMax a b = max a b := by
  unfold natMax
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right h]
  · rw [if_neg h, max_eq_left (Nat.le_of_not_ge h)]

lemma primrec₂_natMax : Primrec₂ natMax :=
  Primrec.ite (Primrec.nat_le.comp Primrec.fst Primrec.snd) Primrec.snd Primrec.fst

def natEqB (a b : ℕ) : Bool := decide (a = b)

lemma primrec₂_natEqB : Primrec₂ natEqB :=
  Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd) (Primrec.const true) (Primrec.const false)
    |>.of_eq fun p => by
      by_cases h : p.1 = p.2 <;> simp [natEqB, h]

def natLtB (a b : ℕ) : Bool := decide (a < b)

lemma primrec₂_natLtB : Primrec₂ natLtB :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.fst Primrec.snd) (Primrec.const true) (Primrec.const false)
    |>.of_eq fun p => by
      by_cases h : p.1 < p.2 <;> simp [natLtB, h]

def natLeB (a b : ℕ) : Bool := decide (a ≤ b)

lemma primrec₂_natLeB : Primrec₂ natLeB :=
  Primrec.ite (Primrec.nat_le.comp Primrec.fst Primrec.snd) (Primrec.const true) (Primrec.const false)
    |>.of_eq fun p => by
      by_cases h : p.1 ≤ p.2 <;> simp [natLeB, h]

def listCount (l : List ℕ) (a : ℕ) : ℕ :=
  l.foldl (fun acc x => if x = a then acc + 1 else acc) 0

lemma listCount_eq (l : List ℕ) (a : ℕ) : listCount l a = l.count a := by
  unfold listCount
  suffices ∀ (init : ℕ), l.foldl (fun acc x => if x = a then acc + 1 else acc) init = init + l.count a by
    simpa using this 0
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    simp only [List.foldl_cons, ih, List.count_cons, beq_iff_eq]
    by_cases h : x = a
    · simp [h]; omega
    · simp [h]

lemma primrec₂_listCount : Primrec₂ listCount := by
  have hstep : Primrec₂ (fun (p : List ℕ × ℕ) (sb : ℕ × ℕ) => if sb.2 = p.2 then sb.1 + 1 else sb.1) :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_foldl Primrec.fst (Primrec.const 0) hstep

def listAll {α : Type} (p : α → Bool) (l : List α) : Bool :=
  l.foldl (fun acc x => acc && p x) true

lemma listAll_iff {α : Type} (p : α → Bool) (l : List α) :
    listAll p l = true ↔ ∀ x ∈ l, p x = true := by
  unfold listAll
  suffices ∀ (init : Bool),
      l.foldl (fun acc x => acc && p x) init = true ↔ init = true ∧ ∀ x ∈ l, p x = true by
    simpa using this true
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

lemma primrec_listAll {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => listAll (p a) (f a)) := by
  have hstep : Primrec₂ (fun (a : α) (sb : Bool × β) => sb.1 && p a sb.2) :=
    Primrec.and.comp (Primrec.fst.comp Primrec.snd)
      (hp.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldl hf (Primrec.const true) hstep

def listPerm (l₁ l₂ : List ℕ) : Bool :=
  listAll (fun a => natEqB (listCount l₁ a) (listCount l₂ a)) (l₁ ++ l₂)

lemma listPerm_iff (l₁ l₂ : List ℕ) : listPerm l₁ l₂ = true ↔ l₁.Perm l₂ := by
  rw [listPerm, listAll_iff, List.perm_iff_count]
  constructor
  · intro h a
    by_cases ha : a ∈ l₁ ∨ a ∈ l₂
    · have hmem : a ∈ l₁ ++ l₂ := List.mem_append.mpr ha
      have h1 := h a hmem
      simp only [natEqB, decide_eq_true_eq, listCount_eq] at h1
      exact h1
    · push Not at ha
      rw [List.count_eq_zero.mpr ha.1, List.count_eq_zero.mpr ha.2]
  · intro h a _
    simp only [natEqB, decide_eq_true_eq, listCount_eq]
    exact h a

lemma primrec₂_listPerm : Primrec₂ listPerm := by
  refine primrec_listAll (Primrec.list_append.comp Primrec.fst Primrec.snd) ?_
  exact primrec₂_natEqB.comp
    (primrec₂_listCount.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (primrec₂_listCount.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

def listSub (l₁ l₂ : List ℕ) : Bool :=
  listAll (fun a => natLtB 0 (listCount l₂ a)) l₁

lemma listSub_iff (l₁ l₂ : List ℕ) : listSub l₁ l₂ = true ↔ ∀ a ∈ l₁, a ∈ l₂ := by
  rw [listSub, listAll_iff]
  refine forall₂_congr fun a _ => ?_
  simp only [natLtB, decide_eq_true_eq, listCount_eq, List.count_pos_iff]

lemma primrec₂_listSub : Primrec₂ listSub := by
  refine primrec_listAll Primrec.fst ?_
  exact primrec₂_natLtB.comp (Primrec.const 0)
    (primrec₂_listCount.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

def mkNode (tag payload : ℕ) : ℕ := natPair tag payload + 2

lemma primrec₂_mkNode : Primrec₂ mkNode :=
  Primrec.nat_add.comp primrec₂_natPair (Primrec.const 2)

lemma payload_lt_mkNode (tag payload : ℕ) : payload < mkNode tag payload := by
  have h : payload ≤ Nat.pair tag payload := Nat.right_le_pair tag payload
  unfold mkNode natPair
  omega

lemma left_lt_mkNode (tag a b : ℕ) : a < mkNode tag (natPair a b) := by
  have h1 : a ≤ Nat.pair a b := Nat.left_le_pair a b
  have h2 : Nat.pair a b < mkNode tag (natPair a b) := payload_lt_mkNode tag (natPair a b)
  unfold natPair at h2 ⊢
  omega

lemma right_lt_mkNode (tag a b : ℕ) : b < mkNode tag (natPair a b) := by
  have h1 : b ≤ Nat.pair a b := Nat.right_le_pair a b
  have h2 : Nat.pair a b < mkNode tag (natPair a b) := payload_lt_mkNode tag (natPair a b)
  unfold natPair at h2 ⊢
  omega

lemma unpair_left_lt_of_ge2 {c : ℕ} (hc : 2 ≤ c) : (Nat.unpair (Nat.unpair (c - 2)).2).1 < c := by
  have h1 : (Nat.unpair (Nat.unpair (c - 2)).2).1 ≤ (Nat.unpair (c - 2)).2 := Nat.unpair_left_le _
  have h2 : (Nat.unpair (c - 2)).2 ≤ c - 2 := Nat.unpair_right_le _
  omega

lemma unpair_right_lt_of_ge2 {c : ℕ} (hc : 2 ≤ c) : (Nat.unpair (Nat.unpair (c - 2)).2).2 < c := by
  have h1 : (Nat.unpair (Nat.unpair (c - 2)).2).2 ≤ (Nat.unpair (c - 2)).2 := Nat.unpair_right_le _
  have h2 : (Nat.unpair (c - 2)).2 ≤ c - 2 := Nat.unpair_right_le _
  omega

lemma payload_lt_of_ge2 {c : ℕ} (hc : 2 ≤ c) : (Nat.unpair (c - 2)).2 < c := by
  have h : (Nat.unpair (c - 2)).2 ≤ c - 2 := Nat.unpair_right_le _
  omega

/- ## Section 2: Gödel Encoding and Decoding of `ℒₛₑₜ` Terms and Formulas -/

def encTerm {k : ℕ} : Semiterm ℒₛₑₜ ℕ k → ℕ
  | .bvar i => 2 * i.val
  | .fvar x => 2 * x + 1
  | .func f _ => f.elim

def wfTerm (k t : ℕ) : Bool :=
  natEqB (t % 2) 1 || natLtB (t / 2) k

lemma primrec₂_wfTerm : Primrec₂ wfTerm :=
  Primrec.or.comp
    (primrec₂_natEqB.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1))
    (primrec₂_natLtB.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)) Primrec.fst)

def decTerm (k t : ℕ) : Option (Semiterm ℒₛₑₜ ℕ k) :=
  if t % 2 = 0 then
    if h : t / 2 < k then some (.bvar ⟨t / 2, h⟩) else none
  else
    some (.fvar (t / 2))

lemma decTerm_encTerm {k : ℕ} (t : Semiterm ℒₛₑₜ ℕ k) : decTerm k (encTerm t) = some t := by
  cases t with
  | bvar i =>
    have hmod : (2 * i.val) % 2 = 0 := by omega
    have hdiv : (2 * i.val) / 2 = i.val := by omega
    simp [encTerm, decTerm, hmod, hdiv, i.isLt]
  | fvar x =>
    have hmod : (2 * x + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * x + 1) / 2 = x := by omega
    simp [encTerm, decTerm, hdiv]
  | func f _ => exact f.elim

lemma encTerm_of_decTerm {k t : ℕ} {tm : Semiterm ℒₛₑₜ ℕ k} (h : decTerm k t = some tm) :
    encTerm tm = t := by
  unfold decTerm at h
  split_ifs at h with h1 h2
  · injection h with h; subst h; simp only [encTerm]; omega
  · injection h with h; subst h; simp only [encTerm]; omega

lemma wfTerm_iff_isSome (k t : ℕ) : wfTerm k t = true ↔ (decTerm k t).isSome = true := by
  unfold wfTerm decTerm natEqB natLtB
  by_cases h0 : t % 2 = 0
  · by_cases hlt : t / 2 < k <;> simp [h0, hlt]
  · have h1 : t % 2 = 1 := by omega
    simp [h1]

def encForm {k : ℕ} : Semiformula ℒₛₑₜ ℕ k → ℕ
  | .verum => 0
  | .falsum => 1
  | .rel .eq v => mkNode 0 (natPair (encTerm (v 0)) (encTerm (v 1)))
  | .rel .mem v => mkNode 1 (natPair (encTerm (v 0)) (encTerm (v 1)))
  | .nrel .eq v => mkNode 2 (natPair (encTerm (v 0)) (encTerm (v 1)))
  | .nrel .mem v => mkNode 3 (natPair (encTerm (v 0)) (encTerm (v 1)))
  | .and φ ψ => mkNode 4 (natPair (encForm φ) (encForm ψ))
  | .or φ ψ => mkNode 5 (natPair (encForm φ) (encForm ψ))
  | .all φ => mkNode 6 (encForm φ)
  | .exs φ => mkNode 7 (encForm φ)

def encSent {k : ℕ} (φ : Semisentence ℒₛₑₜ k) : ℕ :=
  encForm (Rewriting.emb (ξ := ℕ) φ)

def decForm : (k : ℕ) → (c : ℕ) → Option (Semiformula ℒₛₑₜ ℕ k)
  | _, 0 => some .verum
  | _, 1 => some .falsum
  | k, c + 2 =>
    match (Nat.unpair c).1 with
    | 0 =>
      match decTerm k (Nat.unpair (Nat.unpair c).2).1, decTerm k (Nat.unpair (Nat.unpair c).2).2 with
      | some t, some u => some (.rel .eq ![t, u])
      | _, _ => none
    | 1 =>
      match decTerm k (Nat.unpair (Nat.unpair c).2).1, decTerm k (Nat.unpair (Nat.unpair c).2).2 with
      | some t, some u => some (.rel .mem ![t, u])
      | _, _ => none
    | 2 =>
      match decTerm k (Nat.unpair (Nat.unpair c).2).1, decTerm k (Nat.unpair (Nat.unpair c).2).2 with
      | some t, some u => some (.nrel .eq ![t, u])
      | _, _ => none
    | 3 =>
      match decTerm k (Nat.unpair (Nat.unpair c).2).1, decTerm k (Nat.unpair (Nat.unpair c).2).2 with
      | some t, some u => some (.nrel .mem ![t, u])
      | _, _ => none
    | 4 =>
      have _ : (Nat.unpair (Nat.unpair c).2).1 < c + 2 := by
        have h1 := Nat.unpair_left_le (Nat.unpair c).2
        have h2 := Nat.unpair_right_le c
        omega
      have _ : (Nat.unpair (Nat.unpair c).2).2 < c + 2 := by
        have h1 := Nat.unpair_right_le (Nat.unpair c).2
        have h2 := Nat.unpair_right_le c
        omega
      match decForm k (Nat.unpair (Nat.unpair c).2).1, decForm k (Nat.unpair (Nat.unpair c).2).2 with
      | some φ, some ψ => some (.and φ ψ)
      | _, _ => none
    | 5 =>
      have _ : (Nat.unpair (Nat.unpair c).2).1 < c + 2 := by
        have h1 := Nat.unpair_left_le (Nat.unpair c).2
        have h2 := Nat.unpair_right_le c
        omega
      have _ : (Nat.unpair (Nat.unpair c).2).2 < c + 2 := by
        have h1 := Nat.unpair_right_le (Nat.unpair c).2
        have h2 := Nat.unpair_right_le c
        omega
      match decForm k (Nat.unpair (Nat.unpair c).2).1, decForm k (Nat.unpair (Nat.unpair c).2).2 with
      | some φ, some ψ => some (.or φ ψ)
      | _, _ => none
    | 6 =>
      have _ : (Nat.unpair c).2 < c + 2 := by
        have h2 := Nat.unpair_right_le c
        omega
      match decForm (k + 1) (Nat.unpair c).2 with
      | some φ => some (.all φ)
      | none => none
    | 7 =>
      have _ : (Nat.unpair c).2 < c + 2 := by
        have h2 := Nat.unpair_right_le c
        omega
      match decForm (k + 1) (Nat.unpair c).2 with
      | some φ => some (.exs φ)
      | none => none
    | _ => none
termination_by _ c => c

lemma vec2_eq {α : Type*} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  funext i; fin_cases i <;> rfl

lemma decForm_encForm {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) : decForm k (encForm φ) = some φ := by
  induction φ with
  | verum => simp [encForm, decForm]
  | falsum => simp [encForm, decForm]
  | rel r v =>
    cases r with
    | eq =>
      simp only [encForm, mkNode, natPair]
      rw [decForm]
      simp only [Nat.unpair_pair, decTerm_encTerm, vec2_eq]
    | mem =>
      simp only [encForm, mkNode, natPair]
      rw [decForm]
      simp only [Nat.unpair_pair, decTerm_encTerm, vec2_eq]
  | nrel r v =>
    cases r with
    | eq =>
      simp only [encForm, mkNode, natPair]
      rw [decForm]
      simp only [Nat.unpair_pair, decTerm_encTerm, vec2_eq]
    | mem =>
      simp only [encForm, mkNode, natPair]
      rw [decForm]
      simp only [Nat.unpair_pair, decTerm_encTerm, vec2_eq]
  | and φ ψ ih1 ih2 =>
    simp only [encForm, mkNode, natPair]
    rw [decForm]
    simp only [Nat.unpair_pair, ih1, ih2]
  | or φ ψ ih1 ih2 =>
    simp only [encForm, mkNode, natPair]
    rw [decForm]
    simp only [Nat.unpair_pair, ih1, ih2]
  | all φ ih =>
    simp only [encForm, mkNode, natPair]
    rw [decForm]
    simp only [Nat.unpair_pair, ih]
  | exs φ ih =>
    simp only [encForm, mkNode, natPair]
    rw [decForm]
    simp only [Nat.unpair_pair, ih]

lemma encForm_inj {k : ℕ} {φ ψ : Semiformula ℒₛₑₜ ℕ k} (h : encForm φ = encForm ψ) : φ = ψ := by
  have h1 : some φ = some ψ := by rw [← decForm_encForm φ, ← decForm_encForm ψ, h]
  exact Option.some.inj h1

lemma encForm_of_decForm : ∀ (c k : ℕ) (φ : Semiformula ℒₛₑₜ ℕ k),
    decForm k c = some φ → encForm φ = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro k φ hdec
    match c with
    | 0 =>
      rw [decForm] at hdec; injection hdec with h; subst h; rfl
    | 1 =>
      rw [decForm] at hdec; injection hdec with h; subst h; rfl
    | c + 2 =>
      rw [decForm] at hdec
      dsimp only at hdec
      have hpair : Nat.pair (Nat.unpair c).1 (Nat.unpair c).2 = c := Nat.pair_unpair c
      have hsub_l : (Nat.unpair (Nat.unpair c).2).1 < c + 2 := by
        have := Nat.unpair_left_le (Nat.unpair c).2; have := Nat.unpair_right_le c; omega
      have hsub_r : (Nat.unpair (Nat.unpair c).2).2 < c + 2 := by
        have := Nat.unpair_right_le (Nat.unpair c).2; have := Nat.unpair_right_le c; omega
      have hsub_p : (Nat.unpair c).2 < c + 2 := by
        have := Nat.unpair_right_le c; omega
      rcases htag : (Nat.unpair c).1 with _ | _ | _ | _ | _ | _ | _ | _ | n
      · rw [htag] at hdec
        cases ht : decTerm k (Nat.unpair (Nat.unpair c).2).1 with
        | none => rw [ht] at hdec; simp at hdec
        | some t =>
          cases hu : decTerm k (Nat.unpair (Nat.unpair c).2).2 with
          | none => rw [ht, hu] at hdec; simp at hdec
          | some u =>
            rw [ht, hu] at hdec; injection hdec with h; subst h
            simp only [encForm, mkNode, natPair, Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [encTerm_of_decTerm ht, encTerm_of_decTerm hu, Nat.pair_unpair]
            conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ht : decTerm k (Nat.unpair (Nat.unpair c).2).1 with
        | none => rw [ht] at hdec; simp at hdec
        | some t =>
          cases hu : decTerm k (Nat.unpair (Nat.unpair c).2).2 with
          | none => rw [ht, hu] at hdec; simp at hdec
          | some u =>
            rw [ht, hu] at hdec; injection hdec with h; subst h
            simp only [encForm, mkNode, natPair, Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [encTerm_of_decTerm ht, encTerm_of_decTerm hu, Nat.pair_unpair]
            conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ht : decTerm k (Nat.unpair (Nat.unpair c).2).1 with
        | none => rw [ht] at hdec; simp at hdec
        | some t =>
          cases hu : decTerm k (Nat.unpair (Nat.unpair c).2).2 with
          | none => rw [ht, hu] at hdec; simp at hdec
          | some u =>
            rw [ht, hu] at hdec; injection hdec with h; subst h
            simp only [encForm, mkNode, natPair, Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [encTerm_of_decTerm ht, encTerm_of_decTerm hu, Nat.pair_unpair]
            conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ht : decTerm k (Nat.unpair (Nat.unpair c).2).1 with
        | none => rw [ht] at hdec; simp at hdec
        | some t =>
          cases hu : decTerm k (Nat.unpair (Nat.unpair c).2).2 with
          | none => rw [ht, hu] at hdec; simp at hdec
          | some u =>
            rw [ht, hu] at hdec; injection hdec with h; subst h
            simp only [encForm, mkNode, natPair, Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [encTerm_of_decTerm ht, encTerm_of_decTerm hu, Nat.pair_unpair]
            conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ha : decForm k (Nat.unpair (Nat.unpair c).2).1 with
        | none => rw [ha] at hdec; simp at hdec
        | some a =>
          cases hb : decForm k (Nat.unpair (Nat.unpair c).2).2 with
          | none => rw [ha, hb] at hdec; simp at hdec
          | some b =>
            rw [ha, hb] at hdec; injection hdec with h; subst h
            simp only [encForm, mkNode, natPair]
            rw [ih _ hsub_l k a ha, ih _ hsub_r k b hb, Nat.pair_unpair]; conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ha : decForm k (Nat.unpair (Nat.unpair c).2).1 with
        | none => rw [ha] at hdec; simp at hdec
        | some a =>
          cases hb : decForm k (Nat.unpair (Nat.unpair c).2).2 with
          | none => rw [ha, hb] at hdec; simp at hdec
          | some b =>
            rw [ha, hb] at hdec; injection hdec with h; subst h
            simp only [encForm, mkNode, natPair]
            rw [ih _ hsub_l k a ha, ih _ hsub_r k b hb, Nat.pair_unpair]; conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ha : decForm (k + 1) (Nat.unpair c).2 with
        | none => rw [ha] at hdec; simp at hdec
        | some a =>
          rw [ha] at hdec; injection hdec with h; subst h
          simp only [encForm, mkNode, natPair]
          rw [ih _ hsub_p (k + 1) a ha]; conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec
        cases ha : decForm (k + 1) (Nat.unpair c).2 with
        | none => rw [ha] at hdec; simp at hdec
        | some a =>
          rw [ha] at hdec; injection hdec with h; subst h
          simp only [encForm, mkNode, natPair]
          rw [ih _ hsub_p (k + 1) a ha]; conv_rhs => rw [← hpair, htag]
      · rw [htag] at hdec; simp at hdec

@[simp] lemma rew_bind_bvar {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
    (b : Fin n₁ → Semiterm ℒₛₑₜ ξ₂ n₂) (e : ξ₁ → Semiterm ℒₛₑₜ ξ₂ n₂) (i : Fin n₁) :
    (Rew.bind b e) #i = b i := rfl

@[simp] lemma rew_bind_fvar {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
    (b : Fin n₁ → Semiterm ℒₛₑₜ ξ₂ n₂) (e : ξ₁ → Semiterm ℒₛₑₜ ξ₂ n₂) (x : ξ₁) :
    (Rew.bind b e) &x = e x := rfl

@[simp] lemma rew_emb_bvar {n : ℕ} (i : Fin n) :
    (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ)) #i = #i := rfl

lemma rew_ext {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ} {ω₁ ω₂ : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂}
    (h : ∀ t, ω₁ t = ω₂ t) : ω₁ = ω₂ := by
  cases ω₁
  cases ω₂
  congr
  funext t
  exact h t

lemma rew_emb_q {k : ℕ} :
    (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := k)).q = Rew.emb := by
  apply rew_ext
  intro t
  cases t with
  | bvar i => exact Fin.cases rfl (fun _ => rfl) i
  | fvar x => exact x.elim
  | func f _ => exact f.elim

lemma emb_all {k : ℕ} (φ : Semisentence ℒₛₑₜ (k + 1)) :
    Rewriting.emb (ξ := ℕ) (∀¹ φ) = ∀¹ Rewriting.emb (ξ := ℕ) φ := by
  change ∀¹ Semiformula.rewAux Rew.emb.q φ = ∀¹ Semiformula.rewAux Rew.emb φ
  rw [rew_emb_q]

lemma emb_exs {k : ℕ} (φ : Semisentence ℒₛₑₜ (k + 1)) :
    Rewriting.emb (ξ := ℕ) (∃¹ φ) = ∃¹ Rewriting.emb (ξ := ℕ) φ := by
  change ∃¹ Semiformula.rewAux Rew.emb.q φ = ∃¹ Semiformula.rewAux Rew.emb φ
  rw [rew_emb_q]

lemma emb_imp {k : ℕ} (a b : Semisentence ℒₛₑₜ k) :
    Rewriting.emb (ξ := ℕ) (a 🡒 b) = Rewriting.emb (ξ := ℕ) a 🡒 Rewriting.emb (ξ := ℕ) b :=
  (Rewriting.emb (ξ := ℕ)).map_imply' a b

lemma emb_neg {k : ℕ} (a : Semisentence ℒₛₑₜ k) :
    Rewriting.emb (ξ := ℕ) (∼a) = ∼Rewriting.emb (ξ := ℕ) a :=
  (Rewriting.emb (ξ := ℕ)).map_neg' a

lemma emb_term_toEmpty {k : ℕ} (t : Semiterm ℒₛₑₜ ℕ k) (h : t.freeVariables = ∅) :
    Rew.emb (t.toEmpty h) = t := by
  cases t with
  | bvar i => rfl
  | fvar x => simp [Semiterm.freeVariables] at h
  | func f _ => exact f.elim

lemma emb_toEmpty {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) (h : φ.freeVariables = ∅) :
    Rewriting.emb (ξ := ℕ) (φ.toEmpty h) = φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    change Semiformula.rel r _ = Semiformula.rel r v
    congr 1; funext i; exact emb_term_toEmpty (v i) _
  | nrel r v =>
    change Semiformula.nrel r _ = Semiformula.nrel r v
    congr 1; funext i; exact emb_term_toEmpty (v i) _
  | and φ ψ ih1 ih2 =>
    change Rewriting.emb (φ.toEmpty _) ⋏ Rewriting.emb (ψ.toEmpty _) = φ ⋏ ψ
    rw [ih1, ih2]
  | or φ ψ ih1 ih2 =>
    change Rewriting.emb (φ.toEmpty _) ⋎ Rewriting.emb (ψ.toEmpty _) = φ ⋎ ψ
    rw [ih1, ih2]
  | all φ ih =>
    have h' : φ.freeVariables = ∅ := h
    change Rewriting.emb (∀¹ φ.toEmpty h') = ∀¹ φ
    rw [emb_all, ih h']
  | exs φ ih =>
    have h' : φ.freeVariables = ∅ := h
    change Rewriting.emb (∃¹ φ.toEmpty h') = ∃¹ φ
    rw [emb_exs, ih h']

/- ## Section 3: Universal `Primrec` Formula-Recursion Combinator `formRec` -/

/-- Depth-indexed structural recursion on encoded formulas `c : ℕ`.
At `all`/`exs` nodes, `d` increments to `d + 1`. -/
def formRec {α : Type}
    (f0 f1 : α → ℕ → ℕ)
    (fRel : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ)
    (fBad : α → ℕ → ℕ)
    (p : α) : ℕ → ℕ → ℕ
  | d, 0 => f0 p d
  | d, 1 => f1 p d
  | d, c + 2 =>
    if (Nat.unpair c).1 < 4 then
      fRel p (Nat.unpair c).1 d (Nat.unpair (Nat.unpair c).2).1 (Nat.unpair (Nat.unpair c).2).2
    else if (Nat.unpair c).1 < 6 then
      have _ : (Nat.unpair (Nat.unpair c).2).1 < c + 2 := by
        have := Nat.unpair_left_le (Nat.unpair c).2; have := Nat.unpair_right_le c; omega
      have _ : (Nat.unpair (Nat.unpair c).2).2 < c + 2 := by
        have := Nat.unpair_right_le (Nat.unpair c).2; have := Nat.unpair_right_le c; omega
      fBin p (Nat.unpair c).1 d (formRec f0 f1 fRel fBin fQuant fBad p d (Nat.unpair (Nat.unpair c).2).1)
        (formRec f0 f1 fRel fBin fQuant fBad p d (Nat.unpair (Nat.unpair c).2).2)
    else if (Nat.unpair c).1 < 8 then
      have _ : (Nat.unpair c).2 < c + 2 := by have := Nat.unpair_right_le c; omega
      fQuant p (Nat.unpair c).1 d (formRec f0 f1 fRel fBin fQuant fBad p (d + 1) (Nat.unpair c).2)
    else
      fBad p d
termination_by _ c => c

lemma formRec_zero {α : Type}
    (f0 f1 : α → ℕ → ℕ) (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ) (fBad : α → ℕ → ℕ) (p : α) (d : ℕ) :
    formRec f0 f1 fRel fBin fQuant fBad p d 0 = f0 p d := by
  rw [formRec]

lemma formRec_one {α : Type}
    (f0 f1 : α → ℕ → ℕ) (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ) (fBad : α → ℕ → ℕ) (p : α) (d : ℕ) :
    formRec f0 f1 fRel fBin fQuant fBad p d 1 = f1 p d := by
  rw [formRec]

lemma formRec_mkNode_rel {α : Type}
    (f0 f1 : α → ℕ → ℕ) (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ) (fBad : α → ℕ → ℕ)
    (p : α) (d tag t u : ℕ) (htag : tag < 4) :
    formRec f0 f1 fRel fBin fQuant fBad p d (mkNode tag (natPair t u)) = fRel p tag d t u := by
  simp only [mkNode, natPair]
  rw [formRec]
  simp only [Nat.unpair_pair, htag, ↓reduceIte]

lemma formRec_mkNode_bin {α : Type}
    (f0 f1 : α → ℕ → ℕ) (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ) (fBad : α → ℕ → ℕ)
    (p : α) (d tag a b : ℕ) (h4 : ¬(tag < 4)) (h6 : tag < 6) :
    formRec f0 f1 fRel fBin fQuant fBad p d (mkNode tag (natPair a b)) =
      fBin p tag d (formRec f0 f1 fRel fBin fQuant fBad p d a)
        (formRec f0 f1 fRel fBin fQuant fBad p d b) := by
  simp only [mkNode, natPair]
  rw [formRec]
  simp only [Nat.unpair_pair, h4, h6, ↓reduceIte]

lemma formRec_mkNode_quant {α : Type}
    (f0 f1 : α → ℕ → ℕ) (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ) (fBad : α → ℕ → ℕ)
    (p : α) (d tag a : ℕ) (h4 : ¬(tag < 4)) (h6 : ¬(tag < 6)) (h8 : tag < 8) :
    formRec f0 f1 fRel fBin fQuant fBad p d (mkNode tag a) =
      fQuant p tag d (formRec f0 f1 fRel fBin fQuant fBad p (d + 1) a) := by
  simp only [mkNode, natPair]
  rw [formRec]
  simp only [Nat.unpair_pair, h4, h6, h8, ↓reduceIte]

/-- Truncated table whose entries at `d` with `d + c ≤ B` agree with `formRec`. -/
def formRecTrunc {α : Type}
    (f0 f1 : α → ℕ → ℕ)
    (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ)
    (fBad : α → ℕ → ℕ)
    (pB : α × ℕ) (c : ℕ) : List ℕ :=
  (List.range (pB.2 + 1)).map (fun d =>
    if d + c ≤ pB.2 then formRec f0 f1 fRel fBin fQuant fBad pB.1 d c else 0)

def formRecTruncStep {α : Type}
    (f0 f1 : α → ℕ → ℕ)
    (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ)
    (fBad : α → ℕ → ℕ)
    (pB : α × ℕ) (prev : List (List ℕ)) : Option (List ℕ) :=
  let c := prev.length
  let ds := List.range (pB.2 + 1)
  some (ds.map fun d =>
    if d + c ≤ pB.2 then
      if c = 0 then f0 pB.1 d
      else if c = 1 then f1 pB.1 d
      else
        let u := Nat.unpair (c - 2)
        let tag := u.1
        let pay := u.2
        if tag < 4 then
          let q := Nat.unpair pay
          fRel pB.1 tag d q.1 q.2
        else if tag < 6 then
          let q := Nat.unpair pay
          let ta := (prev[q.1]?).getD []
          let tb := (prev[q.2]?).getD []
          fBin pB.1 tag d ((ta[d]?).getD 0) ((tb[d]?).getD 0)
        else if tag < 8 then
          let ta := (prev[pay]?).getD []
          fQuant pB.1 tag d ((ta[d + 1]?).getD 0)
        else
          fBad pB.1 d
    else 0)

lemma formRecTruncStep_eq {α : Type}
    (f0 f1 : α → ℕ → ℕ)
    (fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fQuant : α → ℕ → ℕ → ℕ → ℕ)
    (fBad : α → ℕ → ℕ)
    (pB : α × ℕ) (c : ℕ) :
    formRecTruncStep f0 f1 fRel fBin fQuant fBad pB
      ((List.range c).map (formRecTrunc f0 f1 fRel fBin fQuant fBad pB))
      = some (formRecTrunc f0 f1 fRel fBin fQuant fBad pB c) := by
  unfold formRecTruncStep formRecTrunc
  apply congrArg some
  simp only [List.length_map, List.length_range]
  refine List.map_congr_left fun d hd => ?_
  have hd_le : d < pB.2 + 1 := List.mem_range.mp hd
  by_cases hbound : d + c ≤ pB.2
  · rw [if_pos hbound, if_pos hbound]
    match c with
    | 0 => simp [formRec]
    | 1 => simp [formRec]
    | c' + 2 =>
      have hne0 : c' + 2 ≠ 0 := by omega
      have hne1 : c' + 2 ≠ 1 := by omega
      simp only [hne0, hne1, ↓reduceIte, Nat.add_sub_cancel]
      rw [formRec]
      dsimp only
      by_cases h4 : (Nat.unpair c').1 < 4
      · simp [h4]
      · by_cases h6 : (Nat.unpair c').1 < 6
        · simp only [h4, h6, ↓reduceIte]
          have hq1 : (Nat.unpair (Nat.unpair c').2).1 < c' + 2 := by
            have := Nat.unpair_left_le (Nat.unpair c').2; have := Nat.unpair_right_le c'; omega
          have hq2 : (Nat.unpair (Nat.unpair c').2).2 < c' + 2 := by
            have := Nat.unpair_right_le (Nat.unpair c').2; have := Nat.unpair_right_le c'; omega
          have hb1 : d + (Nat.unpair (Nat.unpair c').2).1 ≤ pB.2 := by omega
          have hb2 : d + (Nat.unpair (Nat.unpair c').2).2 ≤ pB.2 := by omega
          simp [hq1, hq2, hd_le, hb1, hb2]
        · by_cases h8 : (Nat.unpair c').1 < 8
          · simp only [h4, h6, h8, ↓reduceIte]
            have hp : (Nat.unpair c').2 < c' + 2 := by
              have := Nat.unpair_right_le c'; omega
            have hp1 : (Nat.unpair c').2 + 1 < c' + 2 := by
              have := Nat.unpair_right_le c'; omega
            have hd1 : d + 1 < pB.2 + 1 := by omega
            have hb : (d + 1) + (Nat.unpair c').2 ≤ pB.2 := by omega
            simp [hp, hd1, hb]
          · simp [h4, h6, h8]
  · rw [if_neg hbound, if_neg hbound]

lemma primrec_formRec {α : Type} [Primcodable α]
    {f0 f1 : α → ℕ → ℕ}
    {fRel fBin : α → ℕ → ℕ → ℕ → ℕ → ℕ}
    {fQuant : α → ℕ → ℕ → ℕ → ℕ}
    {fBad : α → ℕ → ℕ}
    (hf0 : Primrec₂ f0) (hf1 : Primrec₂ f1)
    (hfRel : Primrec fun x : α × ℕ × ℕ × ℕ × ℕ => fRel x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (hfBin : Primrec fun x : α × ℕ × ℕ × ℕ × ℕ => fBin x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (hfQuant : Primrec fun x : α × ℕ × ℕ × ℕ => fQuant x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hfBad : Primrec₂ fBad) :
    Primrec (fun x : α × ℕ × ℕ => formRec f0 f1 fRel fBin fQuant fBad x.1 x.2.1 x.2.2) := by
  have hstep : Primrec₂ (formRecTruncStep f0 f1 fRel fBin fQuant fBad) := by
    show Primrec (fun inp : (α × ℕ) × List (List ℕ) =>
      formRecTruncStep f0 f1 fRel fBin fQuant fBad inp.1 inp.2)
    unfold formRecTruncStep
    have hA : Primrec (fun inp : (α × ℕ) × List (List ℕ) => inp.1.1) := Primrec.fst.comp Primrec.fst
    have hB : Primrec (fun inp : (α × ℕ) × List (List ℕ) => inp.1.2) := Primrec.snd.comp Primrec.fst
    have hprev : Primrec (fun inp : (α × ℕ) × List (List ℕ) => inp.2) := Primrec.snd
    have hc : Primrec (fun inp : (α × ℕ) × List (List ℕ) => inp.2.length) := Primrec.list_length.comp hprev
    have hds : Primrec (fun inp : (α × ℕ) × List (List ℕ) => List.range (inp.1.2 + 1)) :=
      Primrec.list_range.comp (Primrec.succ.comp hB)
    refine Primrec.option_some.comp (Primrec.list_map hds ?_)
    -- Inner function takes `z : ((α × ℕ) × List (List ℕ)) × ℕ` where `z.2 = d`
    have zA : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => z.1.1.1) := hA.comp Primrec.fst
    have zB : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => z.1.1.2) := hB.comp Primrec.fst
    have zprev : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => z.1.2) := hprev.comp Primrec.fst
    have zc : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => z.1.2.length) := hc.comp Primrec.fst
    have zd : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => z.2) := Primrec.snd
    have zu : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => Nat.unpair (z.1.2.length - 2)) :=
      Primrec.unpair.comp (Primrec.nat_sub.comp zc (Primrec.const 2))
    have ztag : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => (Nat.unpair (z.1.2.length - 2)).1) :=
      Primrec.fst.comp zu
    have zpay : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => (Nat.unpair (z.1.2.length - 2)).2) :=
      Primrec.snd.comp zu
    have zq : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => Nat.unpair (Nat.unpair (z.1.2.length - 2)).2) :=
      Primrec.unpair.comp zpay
    have zq1 : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => (Nat.unpair (Nat.unpair (z.1.2.length - 2)).2).1) :=
      Primrec.fst.comp zq
    have zq2 : Primrec (fun z : ((α × ℕ) × List (List ℕ)) × ℕ => (Nat.unpair (Nat.unpair (z.1.2.length - 2)).2).2) :=
      Primrec.snd.comp zq
    have getAt (idx : (((α × ℕ) × List (List ℕ)) × ℕ) → ℕ)
        (didx : (((α × ℕ) × List (List ℕ)) × ℕ) → ℕ)
        (hidx : Primrec idx) (hdidx : Primrec didx) :
        Primrec (fun z => let ta := (z.1.2[idx z]?).getD []; (ta[didx z]?).getD 0) :=
      Primrec.option_getD.comp
        (Primrec.list_getElem?.comp
          (Primrec.option_getD.comp (Primrec.list_getElem?.comp zprev hidx) (Primrec.const []))
          hdidx)
        (Primrec.const 0)
    refine Primrec.ite (Primrec.nat_le.comp (Primrec.nat_add.comp zd zc) zB) ?_ (Primrec.const 0)
    refine Primrec.ite (Primrec.eq.comp zc (Primrec.const 0)) (hf0.comp zA zd) ?_
    refine Primrec.ite (Primrec.eq.comp zc (Primrec.const 1)) (hf1.comp zA zd) ?_
    refine Primrec.ite (Primrec.nat_lt.comp ztag (Primrec.const 4))
      (hfRel.comp (zA.pair (ztag.pair (zd.pair (zq1.pair zq2))))) ?_
    refine Primrec.ite (Primrec.nat_lt.comp ztag (Primrec.const 6))
      (hfBin.comp (zA.pair (ztag.pair (zd.pair
        ((getAt _ _ zq1 zd).pair (getAt _ _ zq2 zd)))))) ?_
    refine Primrec.ite (Primrec.nat_lt.comp ztag (Primrec.const 8))
      (hfQuant.comp (zA.pair (ztag.pair (zd.pair (getAt _ _ zpay (Primrec.succ.comp zd))))))
      (hfBad.comp zA zd)
  have htrunc : Primrec₂ (formRecTrunc f0 f1 fRel fBin fQuant fBad) :=
    Primrec.nat_strong_rec _ hstep (formRecTruncStep_eq f0 f1 fRel fBin fQuant fBad)
  have hmain : Primrec (fun x : α × ℕ × ℕ =>
      let row := formRecTrunc f0 f1 fRel fBin fQuant fBad (x.1, x.2.1 + x.2.2) x.2.2
      (row[x.2.1]?).getD 0) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp
        (htrunc.comp
          (Primrec.pair Primrec.fst (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0)
  refine hmain.of_eq fun x => ?_
  have hlt : x.2.1 < (x.2.1 + x.2.2) + 1 := by omega
  simp [formRecTrunc, hlt]

/- ### Instantiations of `formRec` -/

/-- Well-formedness check for formula codes with `k` bound variables (`1` = true, `0` = false). -/
def wfFormN (k c : ℕ) : ℕ :=
  formRec
    (fun _ _ => 1)
    (fun _ _ => 1)
    (fun k _ d t u => if wfTerm (k + d) t && wfTerm (k + d) u then 1 else 0)
    (fun _ _ _ a b => if a = 1 ∧ b = 1 then 1 else 0)
    (fun _ _ _ a => a)
    (fun _ _ => 0)
    k 0 c

def wfForm (k c : ℕ) : Bool := natEqB (wfFormN k c) 1

lemma primrec₂_wfForm : Primrec₂ wfForm := by
  have hN : Primrec₂ wfFormN := by
    have h := primrec_formRec
      (f0 := fun (_ : ℕ) _ => 1) (f1 := fun (_ : ℕ) _ => 1)
      (fRel := fun k _ d t u => if wfTerm (k + d) t && wfTerm (k + d) u then 1 else 0)
      (fBin := fun _ _ _ a b => if a = 1 ∧ b = 1 then 1 else 0)
      (fQuant := fun _ _ _ a => a) (fBad := fun _ _ => 0)
      (Primrec.const 1) (Primrec.const 1)
      (Primrec.cond
        (Primrec.and.comp
          (primrec₂_wfTerm.comp (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (primrec₂_wfTerm.comp (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
        (Primrec.const 1) (Primrec.const 0)
        |>.of_eq fun x => by cases wfTerm (x.1 + x.2.2.1) x.2.2.2.1 <;> cases wfTerm (x.1 + x.2.2.1) x.2.2.2.2 <;> rfl)
      (Primrec.ite
        (PrimrecPred.and
          (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const 1))
          (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const 1)))
        (Primrec.const 1) (Primrec.const 0))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const 0)
    exact h.comp (Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd))
  exact primrec₂_natEqB.comp hN (Primrec.const 1)

lemma wfForm_aux : ∀ (c k d : ℕ),
    formRec (fun _ _ => 1) (fun _ _ => 1)
      (fun k _ d t u => if wfTerm (k + d) t && wfTerm (k + d) u then 1 else 0)
      (fun _ _ _ a b => if a = 1 ∧ b = 1 then 1 else 0)
      (fun _ _ _ a => a) (fun _ _ => 0) k d c = 1 ↔ (decForm (k + d) c).isSome = true := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro k d
    match c with
    | 0 => simp [formRec, decForm]
    | 1 => simp [formRec, decForm]
    | c + 2 =>
      rw [formRec, decForm]
      dsimp only
      have hsub_l : (Nat.unpair (Nat.unpair c).2).1 < c + 2 := by
        have := Nat.unpair_left_le (Nat.unpair c).2; have := Nat.unpair_right_le c; omega
      have hsub_r : (Nat.unpair (Nat.unpair c).2).2 < c + 2 := by
        have := Nat.unpair_right_le (Nat.unpair c).2; have := Nat.unpair_right_le c; omega
      have hsub_p : (Nat.unpair c).2 < c + 2 := by
        have := Nat.unpair_right_le c; omega
      rcases htag : (Nat.unpair c).1 with _ | _ | _ | _ | _ | _ | _ | _ | n
      · simp only [Nat.zero_lt_succ, ↓reduceIte, Bool.and_eq_true, wfTerm_iff_isSome]
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).1 <;>
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).2 <;> simp
      · simp only [show 1 < 4 by decide, ↓reduceIte, Bool.and_eq_true, wfTerm_iff_isSome]
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).1 <;>
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).2 <;> simp
      · simp only [show 2 < 4 by decide, ↓reduceIte, Bool.and_eq_true, wfTerm_iff_isSome]
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).1 <;>
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).2 <;> simp
      · simp only [show 3 < 4 by decide, ↓reduceIte, Bool.and_eq_true, wfTerm_iff_isSome]
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).1 <;>
        cases decTerm (k + d) (Nat.unpair (Nat.unpair c).2).2 <;> simp
      · simp only [show ¬(4 < 4) by decide, show 4 < 6 by decide, ↓reduceIte]
        have i1 := ih _ hsub_l k d
        have i2 := ih _ hsub_r k d
        cases h1 : decForm (k + d) (Nat.unpair (Nat.unpair c).2).1 <;>
        cases h2 : decForm (k + d) (Nat.unpair (Nat.unpair c).2).2 <;>
        simp [h1, h2] at i1 i2 ⊢ <;> simp [i1, i2]
      · simp only [show ¬(5 < 4) by decide, show 5 < 6 by decide, ↓reduceIte]
        have i1 := ih _ hsub_l k d
        have i2 := ih _ hsub_r k d
        cases h1 : decForm (k + d) (Nat.unpair (Nat.unpair c).2).1 <;>
        cases h2 : decForm (k + d) (Nat.unpair (Nat.unpair c).2).2 <;>
        simp [h1, h2] at i1 i2 ⊢ <;> simp [i1, i2]
      · simp only [show ¬(6 < 4) by decide, show ¬(6 < 6) by decide, show 6 < 8 by decide, ↓reduceIte]
        have i1 := ih _ hsub_p k (d + 1)
        rw [show k + (d + 1) = k + d + 1 by omega] at i1
        cases h1 : decForm (k + d + 1) (Nat.unpair c).2 <;> simp [h1] at i1 ⊢ <;> exact i1
      · simp only [show ¬(7 < 4) by decide, show ¬(7 < 6) by decide, show 7 < 8 by decide, ↓reduceIte]
        have i1 := ih _ hsub_p k (d + 1)
        rw [show k + (d + 1) = k + d + 1 by omega] at i1
        cases h1 : decForm (k + d + 1) (Nat.unpair c).2 <;> simp [h1] at i1 ⊢ <;> exact i1
      · simp [show ¬(n + 8 < 4) by omega, show ¬(n + 8 < 6) by omega, show ¬(n + 8 < 8) by omega]

lemma wfForm_iff_isSome (k c : ℕ) : wfForm k c = true ↔ (decForm k c).isSome = true := by
  simpa [wfForm, wfFormN, natEqB] using wfForm_aux c k 0

lemma wfForm_encForm {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) : wfForm k (encForm φ) = true := by
  rw [wfForm_iff_isSome, decForm_encForm]; rfl

/-- Negation on formula codes. -/
def negCode (c : ℕ) : ℕ :=
  formRec
    (fun _ _ => 1)
    (fun _ _ => 0)
    (fun _ tag _ t u =>
      let tag' := if tag < 2 then tag + 2 else tag - 2
      mkNode tag' (natPair t u))
    (fun _ tag _ a b =>
      let tag' := if tag = 4 then 5 else 4
      mkNode tag' (natPair a b))
    (fun _ tag _ a =>
      let tag' := if tag = 6 then 7 else 6
      mkNode tag' a)
    (fun _ _ => 0)
    () 0 c

lemma primrec_negCode : Primrec negCode := by
  have h := primrec_formRec
    (f0 := fun (_ : Unit) _ => 1) (f1 := fun (_ : Unit) _ => 0)
    (fRel := fun _ tag _ t u => mkNode (if tag < 2 then tag + 2 else tag - 2) (natPair t u))
    (fBin := fun _ tag _ a b => mkNode (if tag = 4 then 5 else 4) (natPair a b))
    (fQuant := fun _ tag _ a => mkNode (if tag = 6 then 7 else 6) a)
    (fBad := fun _ _ => 0)
    (Primrec.const 1) (Primrec.const 0)
    (primrec₂_mkNode.comp
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
        (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)))
      (primrec₂_natPair.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (primrec₂_mkNode.comp
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 4))
        (Primrec.const 5) (Primrec.const 4))
      (primrec₂_natPair.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (primrec₂_mkNode.comp
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 6))
        (Primrec.const 7) (Primrec.const 6))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.const 0)
  exact h.comp ((Primrec.const ()).pair ((Primrec.const 0).pair Primrec.id))

lemma negCode_aux {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) :
    ∀ d, formRec (fun (_ : Unit) _ => 1) (fun _ _ => 0)
      (fun _ tag _ t u => mkNode (if tag < 2 then tag + 2 else tag - 2) (natPair t u))
      (fun _ tag _ a b => mkNode (if tag = 4 then 5 else 4) (natPair a b))
      (fun _ tag _ a => mkNode (if tag = 6 then 7 else 6) a)
      (fun _ _ => 0) () d (encForm φ) = encForm (∼φ) := by
  induction φ with
  | verum => intro d; simp only [encForm]; rw [formRec_zero]; rfl
  | falsum => intro d; simp only [encForm]; rw [formRec_one]; rfl
  | rel r v =>
    intro d; cases r <;> (simp only [encForm]; rw [formRec_mkNode_rel (htag := by decide)]; rfl)
  | nrel r v =>
    intro d; cases r <;> (simp only [encForm]; rw [formRec_mkNode_rel (htag := by decide)]; rfl)
  | and φ ψ ih1 ih2 =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_bin (h4 := by decide) (h6 := by decide), ih1, ih2]; rfl
  | or φ ψ ih1 ih2 =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_bin (h4 := by decide) (h6 := by decide), ih1, ih2]; rfl
  | all φ ih =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_quant (h4 := by decide) (h6 := by decide) (h8 := by decide), ih]; rfl
  | exs φ ih =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_quant (h4 := by decide) (h6 := by decide) (h8 := by decide), ih]; rfl

lemma negCode_encForm {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) : negCode (encForm φ) = encForm (∼φ) :=
  negCode_aux φ 0

/-- Upper bound on free variables `φ.fvSup` on formula codes. -/
def fvSupTerm (t : ℕ) : ℕ := if t % 2 = 1 then t / 2 + 1 else 0

lemma primrec_fvSupTerm : Primrec fvSupTerm :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1))
    (Primrec.succ.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))) (Primrec.const 0)

def fvSupCode (c : ℕ) : ℕ :=
  formRec
    (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ _ t u => natMax (fvSupTerm t) (fvSupTerm u))
    (fun _ _ _ a b => natMax a b)
    (fun _ _ _ a => a)
    (fun _ _ => 0)
    () 0 c

lemma primrec_fvSupCode : Primrec fvSupCode := by
  have h := primrec_formRec
    (f0 := fun (_ : Unit) _ => 0) (f1 := fun (_ : Unit) _ => 0)
    (fRel := fun _ _ _ t u => natMax (fvSupTerm t) (fvSupTerm u))
    (fBin := fun _ _ _ a b => natMax a b)
    (fQuant := fun _ _ _ a => a) (fBad := fun _ _ => 0)
    (Primrec.const 0) (Primrec.const 0)
    (primrec₂_natMax.comp
      (primrec_fvSupTerm.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (primrec_fvSupTerm.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (primrec₂_natMax.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.const 0)
  exact h.comp ((Primrec.const ()).pair ((Primrec.const 0).pair Primrec.id))

lemma fvSup_union (s t : Finset ℕ) :
    (WithBot.recBotCoe 0 Nat.succ (s ∪ t).max : ℕ) =
      max (WithBot.recBotCoe 0 Nat.succ s.max : ℕ) (WithBot.recBotCoe 0 Nat.succ t.max : ℕ) := by
  rw [Finset.max_union]
  cases s.max with
  | bot => simp
  | coe a =>
    cases t.max with
    | bot => simp
    | coe b =>
      rcases le_total a b with h | h <;> simp [h]

lemma fvSupTerm_encTerm {k : ℕ} (t : Semiterm ℒₛₑₜ ℕ k) :
    fvSupTerm (encTerm t) = (t.freeVariables.max).recBotCoe 0 Nat.succ := by
  cases t with
  | bvar i =>
    simp [encTerm, fvSupTerm, Semiterm.freeVariables]
  | fvar x =>
    have h1 : (2 * x + 1) % 2 = 1 := by omega
    have h2 : (2 * x + 1) / 2 = x := by omega
    simp [encTerm, fvSupTerm, h1, h2, Semiterm.freeVariables]
  | func f _ => exact f.elim

lemma fvSupCode_aux {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) :
    ∀ d, formRec (fun (_ : Unit) _ => 0) (fun _ _ => 0)
      (fun _ _ _ t u => natMax (fvSupTerm t) (fvSupTerm u))
      (fun _ _ _ a b => natMax a b)
      (fun _ _ _ a => a) (fun _ _ => 0) () d (encForm φ) = φ.fvSup := by
  induction φ with
  | verum => intro d; simp only [encForm]; rw [formRec_zero]; rfl
  | falsum => intro d; simp only [encForm]; rw [formRec_one]; rfl
  | rel r v =>
    intro d
    cases r with
    | eq =>
      have hfv : (Semiformula.rel Language.Set.Rel.eq v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      simp only [encForm]
      rw [formRec_mkNode_rel (htag := by decide), natMax_eq, fvSupTerm_encTerm, fvSupTerm_encTerm]
      unfold Semiformula.fvSup; rw [hfv, fvSup_union]
    | mem =>
      have hfv : (Semiformula.rel Language.Set.Rel.mem v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      simp only [encForm]
      rw [formRec_mkNode_rel (htag := by decide), natMax_eq, fvSupTerm_encTerm, fvSupTerm_encTerm]
      unfold Semiformula.fvSup; rw [hfv, fvSup_union]
  | nrel r v =>
    intro d
    cases r with
    | eq =>
      have hfv : (Semiformula.nrel Language.Set.Rel.eq v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      simp only [encForm]
      rw [formRec_mkNode_rel (htag := by decide), natMax_eq, fvSupTerm_encTerm, fvSupTerm_encTerm]
      unfold Semiformula.fvSup; rw [hfv, fvSup_union]
    | mem =>
      have hfv : (Semiformula.nrel Language.Set.Rel.mem v).freeVariables = (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      simp only [encForm]
      rw [formRec_mkNode_rel (htag := by decide), natMax_eq, fvSupTerm_encTerm, fvSupTerm_encTerm]
      unfold Semiformula.fvSup; rw [hfv, fvSup_union]
  | and φ ψ ih1 ih2 =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_bin (h4 := by decide) (h6 := by decide), ih1, ih2, natMax_eq]
    unfold Semiformula.fvSup
    simp only [Semiformula.freeVariables, fvSup_union]
  | or φ ψ ih1 ih2 =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_bin (h4 := by decide) (h6 := by decide), ih1, ih2, natMax_eq]
    unfold Semiformula.fvSup
    simp only [Semiformula.freeVariables, fvSup_union]
  | all φ ih =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_quant (h4 := by decide) (h6 := by decide) (h8 := by decide), ih]
    rfl
  | exs φ ih =>
    intro d; simp only [encForm]
    rw [formRec_mkNode_quant (h4 := by decide) (h6 := by decide) (h8 := by decide), ih]
    rfl

lemma fvSupCode_encForm {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) : fvSupCode (encForm φ) = φ.fvSup :=
  fvSupCode_aux φ 0

/-- Bound-variable shift by `d` on term codes (`#j ↦ #(j + d)`, `&x ↦ &x`). -/
def bShiftCode (d t : ℕ) : ℕ := if t % 2 = 0 then t + 2 * d else t

lemma primrec₂_bShiftCode : Primrec₂ bShiftCode :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    (Primrec.nat_add.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))
    Primrec.snd

lemma bShiftCode_encTerm {k : ℕ} (t : Semiterm ℒₛₑₜ ℕ k) :
    bShiftCode 1 (encTerm t) = encTerm (Rew.bShift t) := by
  cases t with
  | bvar i =>
    have h : (2 * i.val) % 2 = 0 := by omega
    simp only [encTerm, bShiftCode, h, ↓reduceIte, Rew.bShift, Rew.map, rew_bind_bvar, Fin.val_succ]
    omega
  | fvar x =>
    simp [encTerm, bShiftCode, Rew.bShift, Rew.map]
  | func f _ => exact f.elim

lemma bShiftCode_add (d₁ d₂ t : ℕ) : bShiftCode d₁ (bShiftCode d₂ t) = bShiftCode (d₁ + d₂) t := by
  unfold bShiftCode
  by_cases h : t % 2 = 0
  · have h' : (t + 2 * d₂) % 2 = 0 := by omega
    simp only [h, h', ↓reduceIte]; omega
  · simp [h]

/-- Lifting a base term-rewriting function `f0 : α → ℕ → ℕ` under `d` quantifiers (`ω.q^[d]`). -/
def liftTerm {α : Type} (f0 : α → ℕ → ℕ) (p : α) (d t : ℕ) : ℕ :=
  if t % 2 = 0 then
    if t / 2 < d then t
    else bShiftCode d (f0 p (2 * (t / 2 - d)))
  else bShiftCode d (f0 p t)

lemma primrec_liftTerm {α : Type} [Primcodable α] {f0 : α → ℕ → ℕ} (hf0 : Primrec₂ f0) :
    Primrec (fun x : α × ℕ × ℕ => liftTerm f0 x.1 x.2.1 x.2.2) := by
  unfold liftTerm
  have hp : Primrec (fun x : α × ℕ × ℕ => x.1) := Primrec.fst
  have hd : Primrec (fun x : α × ℕ × ℕ => x.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun x : α × ℕ × ℕ => x.2.2) := Primrec.snd.comp Primrec.snd
  refine Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp ht (Primrec.const 2)) (Primrec.const 0)) ?_ ?_
  · refine Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_div.comp ht (Primrec.const 2)) hd) ht ?_
    exact primrec₂_bShiftCode.comp hd
      (hf0.comp hp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.nat_div.comp ht (Primrec.const 2)) hd)))
  · exact primrec₂_bShiftCode.comp hd (hf0.comp hp ht)

/-- General formula rewriting on codes via `formRec` + `liftTerm`. -/
def rewMapCode {α : Type} (f0 : α → ℕ → ℕ) (p : α) (c : ℕ) : ℕ :=
  formRec
    (fun _ _ => 0)
    (fun _ _ => 1)
    (fun p tag d t u => mkNode tag (natPair (liftTerm f0 p d t) (liftTerm f0 p d u)))
    (fun _ tag _ a b => mkNode tag (natPair a b))
    (fun _ tag _ a => mkNode tag a)
    (fun _ _ => 0)
    p 0 c

lemma primrec₂_rewMapCode {α : Type} [Primcodable α] {f0 : α → ℕ → ℕ} (hf0 : Primrec₂ f0) :
    Primrec₂ (rewMapCode f0) := by
  have hlt := primrec_liftTerm hf0
  have h := primrec_formRec
    (f0 := fun (_ : α) _ => 0) (f1 := fun (_ : α) _ => 1)
    (fRel := fun p tag d t u => mkNode tag (natPair (liftTerm f0 p d t) (liftTerm f0 p d u)))
    (fBin := fun _ tag _ a b => mkNode tag (natPair a b))
    (fQuant := fun _ tag _ a => mkNode tag a)
    (fBad := fun _ _ => 0)
    (Primrec.const 0) (Primrec.const 1)
    (primrec₂_mkNode.comp (Primrec.fst.comp Primrec.snd)
      (primrec₂_natPair.comp
        (hlt.comp (Primrec.fst.pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
        (hlt.comp (Primrec.fst.pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))))
    (primrec₂_mkNode.comp (Primrec.fst.comp Primrec.snd)
      (primrec₂_natPair.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (primrec₂_mkNode.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.const 0)
  exact h.comp (Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd))

lemma liftTerm_zero {α : Type} (f0 : α → ℕ → ℕ) (p : α) {k : ℕ} (t : Semiterm ℒₛₑₜ ℕ k) :
    liftTerm f0 p 0 (encTerm t) = f0 p (encTerm t) := by
  cases t with
  | bvar i =>
    have h0 : (2 * i.val) % 2 = 0 := by omega
    have h1 : ¬ ((2 * i.val) / 2 < 0) := by omega
    have h2 : 2 * ((2 * i.val) / 2 - 0) = 2 * i.val := by omega
    simp only [encTerm, liftTerm, h0, h1, ↓reduceIte, h2, bShiftCode]
    by_cases he : f0 p (2 * i.val) % 2 = 0 <;> simp [he]
  | fvar x =>
    have h0 : (2 * x + 1) % 2 ≠ 0 := by omega
    simp only [encTerm, liftTerm, h0, ↓reduceIte, bShiftCode]
    by_cases he : f0 p (2 * x + 1) % 2 = 0 <;> simp [he]
  | func f _ => exact f.elim

lemma liftTerm_succ {α : Type} (f0 : α → ℕ → ℕ) (p : α) (d : ℕ) {n₁ n₂ : ℕ}
    (ω : SyntacticRew ℒₛₑₜ n₁ n₂)
    (hω : ∀ t : Semiterm ℒₛₑₜ ℕ n₁, liftTerm f0 p d (encTerm t) = encTerm (ω t)) :
    ∀ t : Semiterm ℒₛₑₜ ℕ (n₁ + 1), liftTerm f0 p (d + 1) (encTerm t) = encTerm (ω.q t) := by
  intro t
  cases t with
  | bvar i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [encTerm, liftTerm, Rew.q]
    · have h0 : (2 * j.succ.val) % 2 = 0 := by omega
      have hdiv : (2 * j.succ.val) / 2 = j.val + 1 := by simp [Fin.val_succ]
      change liftTerm f0 p (d + 1) (2 * j.succ.val) = encTerm (Rew.bShift (ω #j))
      rw [← bShiftCode_encTerm, ← hω #j]
      simp only [liftTerm, encTerm, h0, hdiv, ↓reduceIte]
      have hj0 : (2 * j.val) % 2 = 0 := by omega
      have hjdiv : (2 * j.val) / 2 = j.val := by omega
      simp only [hj0, hjdiv, ↓reduceIte]
      by_cases hjd : j.val < d
      · have h1 : j.val + 1 < d + 1 := by omega
        simp only [hjd, h1, ↓reduceIte, bShiftCode, hj0, Fin.val_succ]
        omega
      · have h1 : ¬ (j.val + 1 < d + 1) := by omega
        have hsub : j.val + 1 - (d + 1) = j.val - d := by omega
        simp only [hjd, h1, ↓reduceIte, hsub]
        rw [bShiftCode_add, Nat.add_comm 1 d]
  | fvar x =>
    have h0 : (2 * x + 1) % 2 ≠ 0 := by omega
    change liftTerm f0 p (d + 1) (2 * x + 1) = encTerm (Rew.bShift (ω &x))
    rw [← bShiftCode_encTerm, ← hω &x]
    simp only [liftTerm, encTerm, h0, ↓reduceIte]
    rw [bShiftCode_add, Nat.add_comm 1 d]
  | func f _ => exact f.elim

lemma rewMapCode_aux {α : Type} (f0 : α → ℕ → ℕ) (p : α) :
    ∀ {n₁ n₂ : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n₁) (d : ℕ) (ω : SyntacticRew ℒₛₑₜ n₁ n₂),
      (∀ t : Semiterm ℒₛₑₜ ℕ n₁, liftTerm f0 p d (encTerm t) = encTerm (ω t)) →
      formRec (fun _ _ => 0) (fun _ _ => 1)
        (fun p tag d t u => mkNode tag (natPair (liftTerm f0 p d t) (liftTerm f0 p d u)))
        (fun _ tag _ a b => mkNode tag (natPair a b))
        (fun _ tag _ a => mkNode tag a) (fun _ _ => 0) p d (encForm φ)
        = encForm (Semiformula.rewAux ω φ) := by
  intro n₁ n₂ φ
  induction φ generalizing n₂ with
  | verum => intro _ _ _; simp only [encForm]; rw [formRec_zero]; rfl
  | falsum => intro _ _ _; simp only [encForm]; rw [formRec_one]; rfl
  | rel r v =>
    intro d ω hω
    cases r <;> (simp only [encForm]; rw [formRec_mkNode_rel (htag := by decide), hω, hω]; rfl)
  | nrel r v =>
    intro d ω hω
    cases r <;> (simp only [encForm]; rw [formRec_mkNode_rel (htag := by decide), hω, hω]; rfl)
  | and φ ψ ih1 ih2 =>
    intro d ω hω
    simp only [encForm]
    rw [formRec_mkNode_bin (h4 := by decide) (h6 := by decide), ih1 d ω hω, ih2 d ω hω]; rfl
  | or φ ψ ih1 ih2 =>
    intro d ω hω
    simp only [encForm]
    rw [formRec_mkNode_bin (h4 := by decide) (h6 := by decide), ih1 d ω hω, ih2 d ω hω]; rfl
  | all φ ih =>
    intro d ω hω
    simp only [encForm]
    rw [formRec_mkNode_quant (h4 := by decide) (h6 := by decide) (h8 := by decide),
      ih (d + 1) ω.q (liftTerm_succ f0 p d ω hω)]; rfl
  | exs φ ih =>
    intro d ω hω
    simp only [encForm]
    rw [formRec_mkNode_quant (h4 := by decide) (h6 := by decide) (h8 := by decide),
      ih (d + 1) ω.q (liftTerm_succ f0 p d ω hω)]; rfl

lemma rewMapCode_encForm {α : Type} (f0 : α → ℕ → ℕ) (p : α) {n₁ n₂ : ℕ}
    (ω : SyntacticRew ℒₛₑₜ n₁ n₂) (φ : Semiformula ℒₛₑₜ ℕ n₁)
    (hω : ∀ t : Semiterm ℒₛₑₜ ℕ n₁, f0 p (encTerm t) = encTerm (ω t)) :
    rewMapCode f0 p (encForm φ) = encForm (Semiformula.rewAux ω φ) :=
  rewMapCode_aux f0 p φ 0 ω (fun t => (liftTerm_zero f0 p t).trans (hω t))

/- ### Concrete Rewriting Codes: `shiftCode`, `freeCode`, `subst1Code`, `substListCode`, `fixitrCode`, `univClCode` -/

def shiftTerm (_ : Unit) (t : ℕ) : ℕ := if t % 2 = 1 then t + 2 else t

def shiftCode (c : ℕ) : ℕ := rewMapCode shiftTerm () c

lemma primrec_shiftCode : Primrec shiftCode :=
  (primrec₂_rewMapCode (f0 := shiftTerm) (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1))
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)) Primrec.snd)).comp
    (Primrec.const ()) Primrec.id

lemma shiftCode_encForm {k : ℕ} (φ : Semiformula ℒₛₑₜ ℕ k) :
    shiftCode (encForm φ) = encForm (Rewriting.shift φ) := by
  refine rewMapCode_encForm shiftTerm () Rew.shift φ fun t => ?_
  cases t with
  | bvar i =>
    simp [encTerm, shiftTerm, Rew.shift, Rew.map]
  | fvar x =>
    have h : (2 * x + 1) % 2 = 1 := by omega
    simp only [encTerm, shiftTerm, h, ↓reduceIte, Rew.shift, Rew.map, rew_bind_fvar]
    omega
  | func f _ => exact f.elim

def freeTerm (_ : Unit) (t : ℕ) : ℕ := if t % 2 = 0 then 1 else t + 2

def freeCode (c : ℕ) : ℕ := rewMapCode freeTerm () c

lemma primrec_freeCode : Primrec freeCode :=
  (primrec₂_rewMapCode (f0 := freeTerm) (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    (Primrec.const 1) (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)))).comp
    (Primrec.const ()) Primrec.id

lemma freeCode_encForm (φ : Semiproposition ℒₛₑₜ 1) :
    freeCode (encForm φ) = encForm φ.free := by
  refine rewMapCode_encForm freeTerm () Rew.free φ fun t => ?_
  cases t with
  | bvar i =>
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have h : (2 * (0 : Fin 1).val) % 2 = 0 := by simp
    change (if (2 * (0 : Fin 1).val) % 2 = 0 then 1 else _) = encTerm ((Rew.free : SyntacticRew ℒₛₑₜ 1 0) #0)
    rw [if_pos h]
    rfl
  | fvar x =>
    have h : (2 * x + 1) % 2 ≠ 0 := by omega
    simp only [encTerm, freeTerm, h, ↓reduceIte, Rew.free, rew_bind_fvar]
    change 2 * x + 1 + 2 = 2 * (x + 1) + 1; omega
  | func f _ => exact f.elim

def subst1Term (u t : ℕ) : ℕ := if t % 2 = 0 then u else t

def subst1Code (u c : ℕ) : ℕ := rewMapCode subst1Term u c

lemma primrec₂_subst1Code : Primrec₂ subst1Code :=
  primrec₂_rewMapCode (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    Primrec.fst Primrec.snd)

lemma subst1Code_encForm (u : Semiterm ℒₛₑₜ ℕ 0) (φ : Semiproposition ℒₛₑₜ 1) :
    subst1Code (encTerm u) (encForm φ) = encForm (φ/[u]) := by
  refine rewMapCode_encForm subst1Term (encTerm u) (Rew.subst ![u]) φ fun t => ?_
  cases t with
  | bvar i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [encTerm, subst1Term, Rew.subst]
  | fvar x =>
    simp [encTerm, subst1Term, Rew.subst]
  | func f _ => exact f.elim

def substListTerm (ws : List ℕ) (t : ℕ) : ℕ :=
  if t % 2 = 0 then (ws[t / 2]?).getD 0 else t

def substListCode (ws : List ℕ) (c : ℕ) : ℕ := rewMapCode substListTerm ws c

lemma primrec₂_substListCode : Primrec₂ substListCode :=
  primrec₂_rewMapCode (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)))
      (Primrec.const 0))
    Primrec.snd)

lemma substListCode_encForm {n₁ n₂ : ℕ} (w : Fin n₁ → Semiterm ℒₛₑₜ ℕ n₂)
    (φ : Semiformula ℒₛₑₜ ℕ n₁) :
    substListCode (List.ofFn fun i => encTerm (w i)) (encForm φ) = encForm (φ ⇜ w) := by
  refine rewMapCode_encForm substListTerm _ (Rew.subst w) φ fun t => ?_
  cases t with
  | bvar i =>
    have h0 : (2 * i.val) % 2 = 0 := by omega
    have h1 : (2 * i.val) / 2 = i.val := by omega
    simp [encTerm, substListTerm, h0, h1, Rew.subst, i.isLt]
  | fvar x =>
    simp [encTerm, substListTerm, Rew.subst]
  | func f _ => exact f.elim

def fixitrTerm (m t : ℕ) : ℕ :=
  if t % 2 = 0 then t
  else if t / 2 < m then 2 * (t / 2)
  else 2 * (t / 2 - m) + 1

def fixitrCode (m c : ℕ) : ℕ := rewMapCode fixitrTerm m c

lemma primrec₂_fixitrCode : Primrec₂ fixitrCode :=
  primrec₂_rewMapCode (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    Primrec.snd
    (Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)) Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)))
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)) Primrec.fst)))))

lemma fixitr_fvar_zero (m x : ℕ) :
    Rew.fixitr 0 m (&x : Semiterm ℒₛₑₜ ℕ 0) =
      if h : x < m then #(Fin.natAdd 0 ⟨x, h⟩) else &(x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr 0 m &x) = _
    rw [ih]
    by_cases hx : x < m
    · have hx' : x < m + 1 := by omega
      simp only [dif_pos hx, dif_pos hx']; rfl
    · by_cases hx' : x < m + 1
      · have he : x = m := by omega
        subst x
        simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]; rfl
      · have he : x - m = x - (m + 1) + 1 := by omega
        simp only [dif_neg hx, dif_neg hx', he]; rfl

lemma fixitrCode_encForm (m : ℕ) (φ : Proposition ℒₛₑₜ) :
    fixitrCode m (encForm φ) = encForm (@Rew.fixitr ℒₛₑₜ 0 m ▹ φ) := by
  refine rewMapCode_encForm fixitrTerm m (Rew.fixitr 0 m) φ fun t => ?_
  cases t with
  | bvar i => exact Fin.elim0 i
  | fvar x =>
    have h0 : (2 * x + 1) % 2 ≠ 0 := by omega
    have h1 : (2 * x + 1) / 2 = x := by omega
    rw [fixitr_fvar_zero]
    simp only [encTerm, fixitrTerm, h0, h1, ↓reduceIte]
    by_cases hxm : x < m
    · simp [hxm]
    · simp [hxm]
  | func f _ => exact f.elim

def allItrCode (k c : ℕ) : ℕ := Nat.rec c (fun _ acc => mkNode 6 acc) k

lemma primrec₂_allItrCode : Primrec₂ allItrCode := by
  have hstep : Primrec₂ (fun (_ : ℕ) (p : ℕ × ℕ) => mkNode 6 p.2) :=
    primrec₂_mkNode.comp (Primrec.const 6) (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec Primrec.id hstep
  exact (h.comp Primrec.snd Primrec.fst).of_eq fun _ => rfl

lemma allItrCode_encForm {n : ℕ} : ∀ (k : ℕ) (φ : Semiformula ℒₛₑₜ ℕ (n + k)),
    allItrCode k (encForm φ) = encForm (∀¹^[k] φ) := by
  intro k
  induction k with
  | zero => intro φ; rfl
  | succ k ih =>
    intro φ
    change mkNode 6 (allItrCode k (encForm φ)) = encForm (∀¹^[k] (∀¹ φ))
    -- Wait: check induction order: `allItr (k + 1) φ = allItr k (∀¹ φ)`, so `mkNode 6` is INSIDE!
    have hcomm : ∀ (m c : ℕ), allItrCode m (mkNode 6 c) = mkNode 6 (allItrCode m c) := by
      intro m c
      induction m with
      | zero => rfl
      | succ m ihm => change mkNode 6 (allItrCode m (mkNode 6 c)) = _; rw [ihm]; rfl
    rw [← hcomm]
    exact ih (∀¹ φ)

lemma allClosure_eq_allItr : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n),
    allItrCode n (encForm φ) = encForm (∀¹* φ) := by
  intro n
  induction n with
  | zero => intro φ; rfl
  | succ n ih =>
    intro φ
    have hcomm : ∀ (m c : ℕ), allItrCode m (mkNode 6 c) = mkNode 6 (allItrCode m c) := by
      intro m c
      induction m with
      | zero => rfl
      | succ m ihm => change mkNode 6 (allItrCode m (mkNode 6 c)) = _; rw [ihm]; rfl
    change mkNode 6 (allItrCode n (encForm φ)) = encForm (∀¹* (∀¹ φ))
    rw [← hcomm]
    exact ih (∀¹ φ)

def univClCode (c : ℕ) : ℕ :=
  let m := fvSupCode c
  allItrCode m (fixitrCode m c)

lemma primrec_univClCode : Primrec univClCode :=
  primrec₂_allItrCode.comp primrec_fvSupCode (primrec₂_fixitrCode.comp primrec_fvSupCode Primrec.id)

lemma univClCode_encForm (φ : Proposition ℒₛₑₜ) :
    univClCode (encForm φ) = encSent (Semiformula.univCl φ) := by
  unfold encSent Semiformula.univCl
  rw [emb_toEmpty]
  unfold Semiformula.univCl' univClCode
  dsimp only
  rw [fvSupCode_encForm, fixitrCode_encForm]
  simpa only [Nat.zero_add] using allClosure_eq_allItr ((@Rew.fixitr ℒₛₑₜ 0 φ.fvSup) ▹ φ)

/- ## Section 4: `Primrec` Builders for `Constant14.halts (dec c).2` and ZFC Axioms -/

def mkAnd (a b : ℕ) : ℕ := mkNode 4 (natPair a b)
def mkOr (a b : ℕ) : ℕ := mkNode 5 (natPair a b)
def mkAll (a : ℕ) : ℕ := mkNode 6 a
def mkExs (a : ℕ) : ℕ := mkNode 7 a
def mkImp (a b : ℕ) : ℕ := mkOr (negCode a) b
def mkIff (a b : ℕ) : ℕ := mkAnd (mkImp a b) (mkImp b a)
def mkEq (t u : ℕ) : ℕ := mkNode 0 (natPair t u)
def mkMem (t u : ℕ) : ℕ := mkNode 1 (natPair t u)
def mkBexsMem (t a : ℕ) : ℕ := mkExs (mkAnd (mkMem 0 (bShiftCode 1 t)) a)

lemma primrec₂_mkAnd : Primrec₂ mkAnd := primrec₂_mkNode.comp (Primrec.const 4) primrec₂_natPair
lemma primrec₂_mkOr : Primrec₂ mkOr := primrec₂_mkNode.comp (Primrec.const 5) primrec₂_natPair
lemma primrec_mkAll : Primrec mkAll := primrec₂_mkNode.comp (Primrec.const 6) Primrec.id
lemma primrec_mkExs : Primrec mkExs := primrec₂_mkNode.comp (Primrec.const 7) Primrec.id
lemma primrec₂_mkImp : Primrec₂ mkImp := primrec₂_mkOr.comp (primrec_negCode.comp Primrec.fst) Primrec.snd
lemma primrec₂_mkIff : Primrec₂ mkIff :=
  primrec₂_mkAnd.comp (primrec₂_mkImp.comp Primrec.fst Primrec.snd) (primrec₂_mkImp.comp Primrec.snd Primrec.fst)
lemma primrec₂_mkEq : Primrec₂ mkEq := primrec₂_mkNode.comp (Primrec.const 0) primrec₂_natPair
lemma primrec₂_mkMem : Primrec₂ mkMem := primrec₂_mkNode.comp (Primrec.const 1) primrec₂_natPair
lemma primrec₂_mkBexsMem : Primrec₂ mkBexsMem :=
  primrec_mkExs.comp (primrec₂_mkAnd.comp
    (primrec₂_mkMem.comp (Primrec.const 0) (primrec₂_bShiftCode.comp (Primrec.const 1) Primrec.fst))
    Primrec.snd)

lemma encForm_all {k : ℕ} (a : Semiformula ℒₛₑₜ ℕ (k + 1)) : encForm (∀¹ a) = mkAll (encForm a) := rfl
lemma encForm_exs {k : ℕ} (a : Semiformula ℒₛₑₜ ℕ (k + 1)) : encForm (∃¹ a) = mkExs (encForm a) := rfl
lemma encForm_and {k : ℕ} (a b : Semiformula ℒₛₑₜ ℕ k) : encForm (a ⋏ b) = mkAnd (encForm a) (encForm b) := rfl
lemma encForm_or {k : ℕ} (a b : Semiformula ℒₛₑₜ ℕ k) : encForm (a ⋎ b) = mkOr (encForm a) (encForm b) := rfl

lemma encForm_imp {k : ℕ} (a b : Semiformula ℒₛₑₜ ℕ k) :
    encForm (a 🡒 b) = mkImp (encForm a) (encForm b) := by
  change encForm ((∼a) ⋎ b) = mkOr (negCode (encForm a)) (encForm b)
  rw [negCode_encForm]; rfl

lemma encForm_iff {k : ℕ} (a b : Semiformula ℒₛₑₜ ℕ k) :
    encForm (a 🡘 b) = mkIff (encForm a) (encForm b) := by
  change encForm ((a 🡒 b) ⋏ (b 🡒 a)) = mkAnd (mkImp (encForm a) (encForm b)) (mkImp (encForm b) (encForm a))
  rw [encForm_and, encForm_imp, encForm_imp]

lemma encForm_bexsMem {k : ℕ} (t : Semiterm ℒₛₑₜ ℕ k) (a : Semiformula ℒₛₑₜ ℕ (k + 1)) :
    encForm (Semiformula.bexsMem t a) = mkBexsMem (encTerm t) (encForm a) := by
  change encForm (∃¹ (Semiformula.rel Language.Set.Rel.mem ![#0, Rew.bShift t] ⋏ a)) =
    mkExs (mkAnd (mkMem 0 (bShiftCode 1 (encTerm t))) (encForm a))
  rw [bShiftCode_encTerm]; rfl

lemma emb_rewAux {n₁ n₂ : ℕ} (w : Fin n₁ → Semiterm ℒₛₑₜ Empty n₂) (φ : Semisentence ℒₛₑₜ n₁) :
    Rewriting.emb (ξ := ℕ) (φ ⇜ w) =
      (Rewriting.emb (ξ := ℕ) φ) ⇜ (fun i => Rew.emb (w i)) := by
  have hcomp : ∀ {k₁ k₂ : ℕ} (ω₁ : Rew ℒₛₑₜ Empty k₁ Empty k₂) (ω₂ : Rew ℒₛₑₜ ℕ k₁ ℕ k₂),
      (∀ t : Semiterm ℒₛₑₜ Empty k₁, Rew.emb (ω₁ t) = ω₂ (Rew.emb t)) →
      ∀ (ψ : Semisentence ℒₛₑₜ k₁),
        Semiformula.rewAux Rew.emb (Semiformula.rewAux ω₁ ψ) =
          Semiformula.rewAux ω₂ (Semiformula.rewAux Rew.emb ψ) := by
    intro k₁ k₂ ω₁ ω₂ hterm ψ
    induction ψ generalizing k₂ with
    | verum => rfl
    | falsum => rfl
    | rel r v =>
      change Semiformula.rel r _ = Semiformula.rel r _
      congr 1; funext i; exact hterm (v i)
    | nrel r v =>
      change Semiformula.nrel r _ = Semiformula.nrel r _
      congr 1; funext i; exact hterm (v i)
    | and a b ih1 ih2 =>
      change _ ⋏ _ = _ ⋏ _; rw [ih1 ω₁ ω₂ hterm, ih2 ω₁ ω₂ hterm]
    | or a b ih1 ih2 =>
      change _ ⋎ _ = _ ⋎ _; rw [ih1 ω₁ ω₂ hterm, ih2 ω₁ ω₂ hterm]
    | all a ih =>
      change ∀¹ _ = ∀¹ _
      rw [rew_emb_q, rew_emb_q]
      refine congrArg Semiformula.all (ih ω₁.q ω₂.q fun t => ?_)
      cases t with
      | bvar i =>
        refine Fin.cases rfl (fun j => ?_) i
        change Rew.emb (Rew.bShift (ω₁ #j)) = Rew.bShift (ω₂ (Rew.emb (o := Empty) #j))
        rw [← hterm #j]
        cases ω₁ #j with
        | bvar m => rfl
        | fvar x => exact x.elim
        | func f _ => exact f.elim
      | fvar x => exact x.elim
      | func f _ => exact f.elim
    | exs a ih =>
      change ∃¹ _ = ∃¹ _
      rw [rew_emb_q, rew_emb_q]
      refine congrArg Semiformula.exs (ih ω₁.q ω₂.q fun t => ?_)
      cases t with
      | bvar i =>
        refine Fin.cases rfl (fun j => ?_) i
        change Rew.emb (Rew.bShift (ω₁ #j)) = Rew.bShift (ω₂ (Rew.emb (o := Empty) #j))
        rw [← hterm #j]
        cases ω₁ #j with
        | bvar m => rfl
        | fvar x => exact x.elim
        | func f _ => exact f.elim
      | fvar x => exact x.elim
      | func f _ => exact f.elim
  refine hcomp (Rew.subst w) (Rew.subst (fun i => Rew.emb (w i))) (fun t => ?_) φ
  cases t with
  | bvar i => rfl
  | fvar x => exact x.elim
  | func f _ => exact f.elim

def conjListCode (xs : List ℕ) : ℕ :=
  xs.reverse.foldl (fun acc x => mkAnd x acc) 0

lemma primrec_conjListCode : Primrec conjListCode := by
  have hstep : Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) => mkAnd p.2 p.1) :=
    primrec₂_mkAnd.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_foldl Primrec.list_reverse (Primrec.const 0) hstep

lemma conjListCode_ofFn {n k : ℕ} (v : Fin n → Semiformula ℒₛₑₜ ℕ k) :
    conjListCode (List.ofFn fun i => encForm (v i)) = encForm (Matrix.conj v) := by
  have hfold : ∀ (l : List ℕ), l.reverse.foldl (fun acc x => mkAnd x acc) 0 =
      l.foldr mkAnd 0 := by
    intro l; rw [List.foldl_reverse]
  unfold conjListCode
  rw [hfold]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldr_cons, ih (fun i => v i.succ)]
    rfl

/-- Code builder for `Semiformula.nestFormulaeFunc φ Ψ` (`m` remaining bound vars, `n = Ψ.length`). -/
def nestFormulaeFuncCode (m : ℕ) (φ : ℕ) (Ψ : List ℕ) : ℕ :=
  let n := Ψ.length
  let tailVars := (List.range m).map (fun j => 2 * ((j + 1) + n))
  let hypCodes := (List.range n).map fun i =>
    substListCode ((2 * i) :: tailVars) ((Ψ[i]?).getD 0)
  let phiVars := (2 * n) :: ((List.range n).map (fun i => 2 * i))
  allItrCode n (mkImp (conjListCode hypCodes) (substListCode phiVars φ))

lemma primrec_nestFormulaeFuncCode :
    Primrec (fun x : ℕ × ℕ × List ℕ => nestFormulaeFuncCode x.1 x.2.1 x.2.2) := by
  unfold nestFormulaeFuncCode
  have hm : Primrec (fun x : ℕ × ℕ × List ℕ => x.1) := Primrec.fst
  have hφ : Primrec (fun x : ℕ × ℕ × List ℕ => x.2.1) := Primrec.fst.comp Primrec.snd
  have hΨ : Primrec (fun x : ℕ × ℕ × List ℕ => x.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun x : ℕ × ℕ × List ℕ => x.2.2.length) := Primrec.list_length.comp hΨ
  have htail : Primrec (fun x : ℕ × ℕ × List ℕ =>
      (List.range x.1).map (fun j => 2 * ((j + 1) + x.2.2.length))) :=
    Primrec.list_map (Primrec.list_range.comp hm)
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.succ.comp Primrec.snd) (hn.comp Primrec.fst)))
  have hhyps : Primrec (fun x : ℕ × ℕ × List ℕ =>
      (List.range x.2.2.length).map fun i =>
        substListCode ((2 * i) :: (List.range x.1).map (fun j => 2 * ((j + 1) + x.2.2.length)))
          ((x.2.2[i]?).getD 0)) :=
    Primrec.list_map (Primrec.list_range.comp hn)
      (primrec₂_substListCode.comp
        (Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (htail.comp Primrec.fst))
        (Primrec.option_getD.comp (Primrec.list_getElem?.comp (hΨ.comp Primrec.fst) Primrec.snd) (Primrec.const 0)))
  have hphiVars : Primrec (fun x : ℕ × ℕ × List ℕ =>
      (2 * x.2.2.length) :: (List.range x.2.2.length).map (fun i => 2 * i)) :=
    Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec.list_map (Primrec.list_range.comp hn) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))
  exact primrec₂_allItrCode.comp hn
    (primrec₂_mkImp.comp
      (primrec_conjListCode.comp hhyps)
      (primrec₂_substListCode.comp hphiVars hφ))

lemma nestFormulaeFuncCode_eq {n m : ℕ} (φ : SetTheorySemisentence (n + 1))
    (Ψ : Fin n → SetTheorySemisentence (m + 1)) :
    nestFormulaeFuncCode m (encSent φ) (List.ofFn fun i => encSent (Ψ i)) =
      encSent (Semiformula.nestFormulaeFunc φ Ψ) := by
  unfold encSent Semiformula.nestFormulaeFunc nestFormulaeFuncCode
  simp only [List.length_ofFn]
  have hemb_allItr : ∀ (k : ℕ) {r : ℕ} (χ : Semisentence ℒₛₑₜ (r + k)),
      Rewriting.emb (ξ := ℕ) (∀¹^[k] χ) = ∀¹^[k] (Rewriting.emb (ξ := ℕ) χ) := by
    intro k
    induction k with
    | zero => intro r χ; rfl
    | succ k ih =>
      intro r χ
      change Rewriting.emb (∀¹^[k] (∀¹ χ)) = ∀¹^[k] (∀¹ Rewriting.emb χ)
      rw [ih (∀¹ χ), emb_all]
  rw [hemb_allItr, ← allItrCode_encForm]
  congr 1
  have hemb_imp : ∀ {r : ℕ} (a b : Semisentence ℒₛₑₜ r),
      encForm (Rewriting.emb (ξ := ℕ) (a 🡒 b)) =
        mkImp (encForm (Rewriting.emb (ξ := ℕ) a)) (encForm (Rewriting.emb (ξ := ℕ) b)) := by
    intro r a b
    rw [emb_imp, encForm_imp]
  rw [hemb_imp]
  congr 1
  · have hemb_conj : ∀ {k r : ℕ} (v : Fin k → Semisentence ℒₛₑₜ r),
        Rewriting.emb (ξ := ℕ) (Matrix.conj v) = Matrix.conj (fun i => Rewriting.emb (ξ := ℕ) (v i)) := by
      intro k
      induction k with
      | zero => intro r v; rfl
      | succ k ih =>
        intro r v
        change Rewriting.emb (v 0) ⋏ Rewriting.emb (Matrix.conj (Matrix.vecTail v)) = _
        rw [ih]; rfl
    rw [hemb_conj, ← conjListCode_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, List.getElem?_ofFn]
      have hin : i < n := by simpa using hi1
      simp only [hin, ↓reduceDIte, Option.getD_some]
      rw [emb_rewAux, ← substListCode_encForm]
      congr 1
      apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        cases j with
        | zero => simp [encTerm, Fin.addCast]
        | succ j =>
          simp [encTerm, Fin.addNat]
  · rw [emb_rewAux, ← substListCode_encForm]
    congr 1
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      cases j with
      | zero => simp [encTerm, Fin.addNat]
      | succ j =>
        simp [encTerm, Fin.addCast]

/-- Code builder for `Semiformula.nestFormulae φ Ψ` (`m` remaining bound vars, `n = Ψ.length`). -/
def nestFormulaeCode (m : ℕ) (φ : ℕ) (Ψ : List ℕ) : ℕ :=
  let n := Ψ.length
  let tailVars := (List.range m).map (fun j => 2 * (j + n))
  let hypCodes := (List.range n).map fun i =>
    substListCode ((2 * i) :: tailVars) ((Ψ[i]?).getD 0)
  let phiVars := (List.range n).map (fun i => 2 * i)
  allItrCode n (mkImp (conjListCode hypCodes) (substListCode phiVars φ))

lemma primrec_nestFormulaeCode :
    Primrec (fun x : ℕ × ℕ × List ℕ => nestFormulaeCode x.1 x.2.1 x.2.2) := by
  unfold nestFormulaeCode
  have hm : Primrec (fun x : ℕ × ℕ × List ℕ => x.1) := Primrec.fst
  have hφ : Primrec (fun x : ℕ × ℕ × List ℕ => x.2.1) := Primrec.fst.comp Primrec.snd
  have hΨ : Primrec (fun x : ℕ × ℕ × List ℕ => x.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun x : ℕ × ℕ × List ℕ => x.2.2.length) := Primrec.list_length.comp hΨ
  have htail : Primrec (fun x : ℕ × ℕ × List ℕ =>
      (List.range x.1).map (fun j => 2 * (j + x.2.2.length))) :=
    Primrec.list_map (Primrec.list_range.comp hm)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.snd (hn.comp Primrec.fst)))
  have hhyps : Primrec (fun x : ℕ × ℕ × List ℕ =>
      (List.range x.2.2.length).map fun i =>
        substListCode ((2 * i) :: (List.range x.1).map (fun j => 2 * (j + x.2.2.length)))
          ((x.2.2[i]?).getD 0)) :=
    Primrec.list_map (Primrec.list_range.comp hn)
      (primrec₂_substListCode.comp
        (Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (htail.comp Primrec.fst))
        (Primrec.option_getD.comp (Primrec.list_getElem?.comp (hΨ.comp Primrec.fst) Primrec.snd) (Primrec.const 0)))
  have hphiVars : Primrec (fun x : ℕ × ℕ × List ℕ =>
      (List.range x.2.2.length).map (fun i => 2 * i)) :=
    Primrec.list_map (Primrec.list_range.comp hn) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
  exact primrec₂_allItrCode.comp hn
    (primrec₂_mkImp.comp
      (primrec_conjListCode.comp hhyps)
      (primrec₂_substListCode.comp hphiVars hφ))

lemma nestFormulaeCode_eq {n m : ℕ} (φ : SetTheorySemisentence n)
    (Ψ : Fin n → SetTheorySemisentence (m + 1)) :
    nestFormulaeCode m (encSent φ) (List.ofFn fun i => encSent (Ψ i)) =
      encSent (Semiformula.nestFormulae φ Ψ) := by
  unfold encSent Semiformula.nestFormulae nestFormulaeCode
  simp only [List.length_ofFn]
  have hemb_allItr : ∀ (k : ℕ) {r : ℕ} (χ : Semisentence ℒₛₑₜ (r + k)),
      Rewriting.emb (ξ := ℕ) (∀¹^[k] χ) = ∀¹^[k] (Rewriting.emb (ξ := ℕ) χ) := by
    intro k
    induction k with
    | zero => intro r χ; rfl
    | succ k ih =>
      intro r χ
      change Rewriting.emb (∀¹^[k] (∀¹ χ)) = ∀¹^[k] (∀¹ Rewriting.emb χ)
      rw [ih (∀¹ χ), emb_all]
  rw [hemb_allItr, ← allItrCode_encForm]
  congr 1
  have hemb_imp : ∀ {r : ℕ} (a b : Semisentence ℒₛₑₜ r),
      encForm (Rewriting.emb (ξ := ℕ) (a 🡒 b)) =
        mkImp (encForm (Rewriting.emb (ξ := ℕ) a)) (encForm (Rewriting.emb (ξ := ℕ) b)) := by
    intro r a b
    rw [emb_imp, encForm_imp]
  rw [hemb_imp]
  congr 1
  · have hemb_conj : ∀ {k r : ℕ} (v : Fin k → Semisentence ℒₛₑₜ r),
        Rewriting.emb (ξ := ℕ) (Matrix.conj v) = Matrix.conj (fun i => Rewriting.emb (ξ := ℕ) (v i)) := by
      intro k
      induction k with
      | zero => intro r v; rfl
      | succ k ih =>
        intro r v
        change Rewriting.emb (v 0) ⋏ Rewriting.emb (Matrix.conj (Matrix.vecTail v)) = _
        rw [ih]; rfl
    rw [hemb_conj, ← conjListCode_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, List.getElem?_ofFn]
      have hin : i < n := by simpa using hi1
      simp only [hin, ↓reduceDIte, Option.getD_some]
      rw [emb_rewAux, ← substListCode_encForm]
      congr 1
      apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        cases j with
        | zero => simp [encTerm, Fin.addCast]
        | succ j =>
          simp [encTerm, Fin.addNat]
  · rw [emb_rewAux, ← substListCode_encForm]
    congr 1
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp [encTerm, Fin.addCast]

/- ### `haltsCode` matching `Constant14.halts (dec c).2` -/

def decMachine (c : ℕ) : (n : ℕ) × Machine (Fin 2) (Fin (n + 1)) :=
  let n := (Nat.unpair c).1
  let t := (Nat.unpair c).2
  let B := 4 * (n + 2) + 1
  ⟨n, fun q a =>
    let v := (t / B ^ (2 * q.val + a.val)) % B
    if v = 0 then none
    else
      let w := v - 1
      let s := w / 4
      let b : Fin 2 := ⟨(w / 2) % 2, Nat.mod_lt _ (by decide)⟩
      let d : Dir := if w % 2 = 0 then .left else .right
      some (if h : s < n + 1 then some ⟨s, h⟩ else none, Stmt.write b d)⟩

def numeralCode (k : ℕ) : ℕ :=
  Nat.rec (encSent Constant14.zero)
    (fun _ acc => nestFormulaeFuncCode 0 (encSent SetTheory.succ.dfn) [acc]) k

lemma primrec_numeralCode : Primrec numeralCode := by
  have hstep : Primrec₂ (fun (_ : Unit) (p : ℕ × ℕ) =>
      nestFormulaeFuncCode 0 (encSent SetTheory.succ.dfn) [p.2]) :=
    primrec_nestFormulaeFuncCode.comp
      ((Primrec.const 0).pair ((Primrec.const (encSent SetTheory.succ.dfn)).pair
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))))
  have h : Primrec₂ (fun (_ : Unit) (k : ℕ) => numeralCode k) :=
    Primrec.nat_rec (Primrec.const (encSent Constant14.zero)) hstep
  exact h.comp (Primrec.const ()) Primrec.id

lemma numeralCode_eq (k : ℕ) : numeralCode k = encSent (Constant14.numeral k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change nestFormulaeFuncCode 0 (encSent SetTheory.succ.dfn) [numeralCode k] = _
    rw [ih]
    have hlist : [encSent (Constant14.numeral k)] =
        List.ofFn (fun i : Fin 1 => encSent (![Constant14.numeral k] i)) := by simp
    rw [hlist, nestFormulaeFuncCode_eq]
    rfl

def setPairCode (x y : ℕ) : ℕ :=
  nestFormulaeFuncCode 0 (encSent SetTheory.kpair.dfn) [x, y]

lemma primrec₂_setPairCode : Primrec₂ setPairCode :=
  primrec_nestFormulaeFuncCode.comp
    ((Primrec.const 0).pair ((Primrec.const (encSent SetTheory.kpair.dfn)).pair
      (Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))))

lemma setPairCode_eq (x y : SetTheorySemisentence 1) :
    setPairCode (encSent x) (encSent y) = encSent (Constant14.setPair x y) := by
  unfold setPairCode Constant14.setPair
  have h : [encSent x, encSent y] = List.ofFn (fun i : Fin 2 => encSent (![x, y] i)) := by
    simp [List.ofFn_succ]
  rw [h, nestFormulaeFuncCode_eq]

def setTripleCode (x y z : ℕ) : ℕ := setPairCode x (setPairCode y z)

lemma setTripleCode_eq (x y z : SetTheorySemisentence 1) :
    setTripleCode (encSent x) (encSent y) (encSent z) = encSent (Constant14.setTriple x y z) := by
  simp [setTripleCode, Constant14.setTriple, setPairCode_eq]

def transitionEntryCode (q a q' w d : ℕ) : ℕ :=
  setPairCode (setPairCode (numeralCode q) (numeralCode a))
    (setTripleCode (numeralCode q') (numeralCode w) (numeralCode d))

lemma transitionEntryCode_eq (q a q' w d : ℕ) :
    transitionEntryCode q a q' w d = encSent (Constant14.transitionEntry q a q' w d) := by
  simp [transitionEntryCode, Constant14.transitionEntry, numeralCode_eq, setPairCode_eq, setTripleCode_eq]

def finiteSetCode (xs : List ℕ) : ℕ :=
  xs.reverse.foldl (fun acc x => nestFormulaeFuncCode 0 (encSent SetTheory.insert.dfn) [x, acc])
    (encSent Constant14.zero)

lemma primrec_finiteSetCode : Primrec finiteSetCode := by
  have hstep : Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) =>
      nestFormulaeFuncCode 0 (encSent SetTheory.insert.dfn) [p.2, p.1]) :=
    primrec_nestFormulaeFuncCode.comp
      ((Primrec.const 0).pair ((Primrec.const (encSent SetTheory.insert.dfn)).pair
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])))))
  exact Primrec.list_foldl Primrec.list_reverse (Primrec.const (encSent Constant14.zero)) hstep

lemma finiteSetCode_eq (xs : List (SetTheorySemisentence 1)) :
    finiteSetCode (xs.map encSent) = encSent (Constant14.finiteSet xs) := by
  have hfold : ∀ (l : List ℕ),
      l.reverse.foldl (fun acc x => nestFormulaeFuncCode 0 (encSent SetTheory.insert.dfn) [x, acc])
        (encSent Constant14.zero) =
      l.foldr (fun x acc => nestFormulaeFuncCode 0 (encSent SetTheory.insert.dfn) [x, acc])
        (encSent Constant14.zero) := by
    intro l; rw [List.foldl_reverse]
  unfold finiteSetCode; rw [hfold]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, ih, Constant14.finiteSet]
    have h : [encSent x, encSent (Constant14.finiteSet xs)] =
        List.ofFn (fun i : Fin 2 => encSent (![x, Constant14.finiteSet xs] i)) := by
      simp [List.ofFn_succ]
    rw [h, nestFormulaeFuncCode_eq]

def decEntry (c idx : ℕ) : ℕ :=
  let n := (Nat.unpair c).1
  let t := (Nat.unpair c).2
  let B := 4 * (n + 2) + 1
  let q := idx / 2
  let a := idx % 2
  let v := (t / natPow B idx) % B
  if v = 0 then
    transitionEntryCode q a (n + 1) a 1
  else
    let w := v - 1
    let s := w / 4
    let b := (w / 2) % 2
    let d := if w % 2 = 0 then 0 else 2
    let q' := if s < n + 1 then s else n + 1
    transitionEntryCode q a q' b d

lemma primrec_transitionEntryCode :
    Primrec (fun x : ℕ × ℕ × ℕ × ℕ × ℕ =>
      transitionEntryCode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold transitionEntryCode setTripleCode
  have x1 : Primrec (fun x : ℕ × ℕ × ℕ × ℕ × ℕ => x.1) := Primrec.fst
  have x2 : Primrec (fun x : ℕ × ℕ × ℕ × ℕ × ℕ => x.2.1) := Primrec.fst.comp Primrec.snd
  have x3 : Primrec (fun x : ℕ × ℕ × ℕ × ℕ × ℕ => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have x4 : Primrec (fun x : ℕ × ℕ × ℕ × ℕ × ℕ => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have x5 : Primrec (fun x : ℕ × ℕ × ℕ × ℕ × ℕ => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact primrec₂_setPairCode.comp
    (primrec₂_setPairCode.comp (primrec_numeralCode.comp x1) (primrec_numeralCode.comp x2))
    (primrec₂_setPairCode.comp (primrec_numeralCode.comp x3)
      (primrec₂_setPairCode.comp (primrec_numeralCode.comp x4) (primrec_numeralCode.comp x5)))

lemma primrec₂_decEntry : Primrec₂ decEntry := by
  have hc : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hidx : Primrec (fun p : ℕ × ℕ => p.2) := Primrec.snd
  have hn : Primrec (fun p : ℕ × ℕ => (Nat.unpair p.1).1) := Primrec.fst.comp (Primrec.unpair.comp hc)
  have ht : Primrec (fun p : ℕ × ℕ => (Nat.unpair p.1).2) := Primrec.snd.comp (Primrec.unpair.comp hc)
  have hB : Primrec (fun p : ℕ × ℕ => 4 * ((Nat.unpair p.1).1 + 2) + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.nat_add.comp hn (Primrec.const 2)))
      (Primrec.const 1)
  have hq : Primrec (fun p : ℕ × ℕ => p.2 / 2) := Primrec.nat_div.comp hidx (Primrec.const 2)
  have ha : Primrec (fun p : ℕ × ℕ => p.2 % 2) := Primrec.nat_mod.comp hidx (Primrec.const 2)
  have hv := Primrec.nat_mod.comp (Primrec.nat_div.comp ht (primrec₂_natPow.comp hB hidx)) hB
  have hw := Primrec.nat_sub.comp hv (Primrec.const 1)
  have hs := Primrec.nat_div.comp hw (Primrec.const 4)
  have hb := Primrec.nat_mod.comp (Primrec.nat_div.comp hw (Primrec.const 2)) (Primrec.const 2)
  have hd := Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hw (Primrec.const 2)) (Primrec.const 0))
    (Primrec.const 0) (Primrec.const 2)
  have hn1 := Primrec.nat_add.comp hn (Primrec.const 1)
  have hq' := Primrec.ite (Primrec.nat_lt.comp hs hn1) hs hn1
  have hres := Primrec.ite (Primrec.eq.comp hv (Primrec.const 0))
    (primrec_transitionEntryCode.comp (hq.pair (ha.pair (hn1.pair (ha.pair (Primrec.const 1))))))
    (primrec_transitionEntryCode.comp (hq.pair (ha.pair (hq'.pair (hb.pair hd)))))
  exact hres.of_eq fun p => rfl

def instructionTableCode (c : ℕ) : ℕ :=
  let n := (Nat.unpair c).1
  let mainEntries := (List.range (2 * (n + 1))).map (decEntry c)
  let haltEntries := [transitionEntryCode (n + 1) 0 (n + 1) 0 1,
                      transitionEntryCode (n + 1) 1 (n + 1) 1 1]
  finiteSetCode (mainEntries ++ haltEntries)

lemma primrec_instructionTableCode : Primrec instructionTableCode := by
  have hn : Primrec (fun c : ℕ => (Nat.unpair c).1) := Primrec.fst.comp Primrec.unpair
  have hn1 : Primrec (fun c : ℕ => (Nat.unpair c).1 + 1) := Primrec.nat_add.comp hn (Primrec.const 1)
  have hmain : Primrec (fun c : ℕ => (List.range (2 * ((Nat.unpair c).1 + 1))).map (decEntry c)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) hn1))
      primrec₂_decEntry
  have hhalt0 := primrec_transitionEntryCode.comp
    (hn1.pair ((Primrec.const 0).pair (hn1.pair ((Primrec.const 0).pair (Primrec.const 1)))))
  have hhalt1 := primrec_transitionEntryCode.comp
    (hn1.pair ((Primrec.const 1).pair (hn1.pair ((Primrec.const 1).pair (Primrec.const 1)))))
  have hhalt := Primrec.list_cons.comp hhalt0 (Primrec.list_cons.comp hhalt1 (Primrec.const []))
  exact (primrec_finiteSetCode.comp (Primrec.list_append.comp hmain hhalt)).of_eq fun c => rfl

lemma instructionTableCode_eq (c : ℕ) :
    instructionTableCode c = encSent (Constant14.instructionTable (decMachine c).2) := by
  unfold instructionTableCode Constant14.instructionTable
  dsimp only
  rw [← finiteSetCode_eq]
  refine congrArg finiteSetCode ?_
  unfold Constant14.transitionEntries
  rw [List.map_append]
  refine congrArg₂ List.append ?_ ?_
  · set n := (Nat.unpair c).1
    have hflat_get : ∀ (k : ℕ) (f : Fin k → Fin 2 → ℕ) (idx : ℕ) (hq : idx / 2 < k),
        (List.ofFn fun q : Fin k => List.ofFn fun a : Fin 2 => f q a).flatten[idx]? =
          some (f ⟨idx / 2, hq⟩ ⟨idx % 2, Nat.mod_lt _ (by decide)⟩) := by
      intro k
      induction k with
      | zero => intro f idx hq; omega
      | succ k ihk =>
        intro f idx hq
        rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
        rcases idx with _ | _ | idx'
        · rfl
        · rfl
        · have hq' : idx' / 2 < k := by omega
          have heq := ihk (fun q a => f q.succ a) idx' hq'
          have hdiv : (idx' + 2) / 2 = idx' / 2 + 1 := by omega
          have hmod : (idx' + 2) % 2 = idx' % 2 := by omega
          simpa [hdiv, hmod] using heq
    have hflat : ∀ (k : ℕ) (f : Fin k → Fin 2 → ℕ),
        ((List.ofFn fun q : Fin k => List.ofFn fun a : Fin 2 => f q a).flatten) =
        (List.range (2 * k)).map (fun idx =>
          if h : idx / 2 < k then f ⟨idx / 2, h⟩ ⟨idx % 2, Nat.mod_lt _ (by decide)⟩ else 0) := by
      intro k f
      apply List.ext_getElem
      · have hlen : ∀ (m : ℕ) (g : Fin m → List ℕ), (∀ i, (g i).length = 2) →
            (List.ofFn g).flatten.length = 2 * m := by
          intro m
          induction m with
          | zero => intro g _; simp
          | succ m ihm =>
            intro g hg
            rw [List.ofFn_succ, List.flatten_cons, List.length_append, hg 0, ihm _ (fun i => hg i.succ)]
            omega
        rw [hlen k _ (fun _ => by simp), List.length_map, List.length_range]
      · intro idx h1 h2
        have hidx : idx < 2 * k := by simpa using h2
        have hq : idx / 2 < k := by omega
        simp only [List.getElem_map, List.getElem_range, dif_pos hq]
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem h1]
        exact hflat_get k f idx hq
    rw [List.map_flatten, List.map_ofFn]
    have hmap2 : (List.ofFn
        (List.map encSent ∘ fun q : Fin ((decMachine c).1 + 1) =>
          List.ofFn fun symbol : Fin 2 =>
            Constant14.transitionEntry q.val symbol.val
              (Constant14.transitionCode (decMachine c).2 q symbol).1
              (Constant14.transitionCode (decMachine c).2 q symbol).2.1
              (Constant14.transitionCode (decMachine c).2 q symbol).2.2)) =
        (List.ofFn fun q : Fin ((decMachine c).1 + 1) =>
          List.ofFn fun symbol : Fin 2 =>
            encSent (Constant14.transitionEntry q.val symbol.val
              (Constant14.transitionCode (decMachine c).2 q symbol).1
              (Constant14.transitionCode (decMachine c).2 q symbol).2.1
              (Constant14.transitionCode (decMachine c).2 q symbol).2.2)) := by
      refine congrArg List.ofFn (funext fun q => by simp only [Function.comp_def, List.map_ofFn])
    rw [hmap2, hflat]
    refine List.map_congr_left fun idx hidx => ?_
    have hlt : idx < 2 * (n + 1) := List.mem_range.mp hidx
    have hq : idx / 2 < (decMachine c).1 + 1 := by
      change idx / 2 < n + 1; omega
    rw [dif_pos hq, ← transitionEntryCode_eq]
    let p : ℕ × ℕ × ℕ :=
      let v := (Nat.unpair c).2 / (4 * ((Nat.unpair c).1 + 2) + 1) ^ idx % (4 * ((Nat.unpair c).1 + 2) + 1)
      if v = 0 then ((Nat.unpair c).1 + 1, idx % 2, 1)
      else (if (v - 1) / 4 < (Nat.unpair c).1 + 1 then (v - 1) / 4 else (Nat.unpair c).1 + 1,
            ((v - 1) / 2) % 2, if (v - 1) % 2 = 0 then 0 else 2)
    have hdec : decEntry c idx = transitionEntryCode (idx / 2) (idx % 2) p.1 p.2.1 p.2.2 := by
      unfold decEntry
      dsimp only [p]
      rw [natPow_eq]
      split_ifs <;> rfl
    have hcode : p = Constant14.transitionCode (decMachine c).2 ⟨idx / 2, hq⟩ ⟨idx % 2, Nat.mod_lt _ (by decide)⟩ := by
      dsimp only [p]
      unfold Constant14.transitionCode decMachine
      have hidx_eq : 2 * (idx / 2) + idx % 2 = idx := by omega
      dsimp only
      simp only [hidx_eq]
      by_cases hv : (Nat.unpair c).2 / (4 * ((Nat.unpair c).1 + 2) + 1) ^ idx % (4 * ((Nat.unpair c).1 + 2) + 1) = 0
      · simp [hv, Constant14.directionCode]
      · by_cases hs : ((Nat.unpair c).2 / (4 * ((Nat.unpair c).1 + 2) + 1) ^ idx % (4 * ((Nat.unpair c).1 + 2) + 1) - 1) / 4 < (Nat.unpair c).1 + 1 <;>
        by_cases hmod : ((Nat.unpair c).2 / (4 * ((Nat.unpair c).1 + 2) + 1) ^ idx % (4 * ((Nat.unpair c).1 + 2) + 1) - 1) % 2 = 0 <;>
        simp [hv, hs, hmod, Constant14.stateCode, Constant14.directionCode]
    rw [hdec, hcode]
  · simp [List.ofFn_succ, transitionEntryCode_eq, Constant14.directionCode, decMachine]

def configSetCode (n : ℕ) : ℕ :=
  mkAll (mkImp (mkEq 0 2)
    (mkAll (mkImp
      (nestFormulaeFuncCode 2 (encSent SetTheory.prod.dfn)
        [nestFormulaeFuncCode 2 (numeralCode n) [],
         nestFormulaeFuncCode 2 (encSent SetTheory.prod.dfn)
          [nestFormulaeFuncCode 2 (encSent Constant14.integers) [],
           nestFormulaeFuncCode 2 (encSent SetTheory.function.dfn)
            [nestFormulaeFuncCode 2 (numeralCode 2) [],
             nestFormulaeFuncCode 2 (encSent Constant14.integers) []]]])
      (mkEq 2 0))))

lemma primrec_configSetCode : Primrec configSetCode := by
  unfold configSetCode
  have h0 : Primrec (fun n : ℕ => nestFormulaeFuncCode 2 (numeralCode n) []) :=
    primrec_nestFormulaeFuncCode.comp
      ((Primrec.const 2).pair (primrec_numeralCode.pair (Primrec.const [])))
  have hinner := primrec_nestFormulaeFuncCode.comp
    ((Primrec.const 2).pair ((Primrec.const (encSent SetTheory.prod.dfn)).pair
      (Primrec.list_cons.comp h0 (Primrec.const
        [nestFormulaeFuncCode 2 (encSent SetTheory.prod.dfn)
          [nestFormulaeFuncCode 2 (encSent Constant14.integers) [],
           nestFormulaeFuncCode 2 (encSent SetTheory.function.dfn)
            [nestFormulaeFuncCode 2 (numeralCode 2) [],
             nestFormulaeFuncCode 2 (encSent Constant14.integers) []]]]))))
  exact primrec_mkAll.comp (primrec₂_mkImp.comp (Primrec.const (mkEq 0 2))
    (primrec_mkAll.comp (primrec₂_mkImp.comp hinner (Primrec.const (mkEq 2 0)))))

lemma encSent_imp {k : ℕ} (a b : Semisentence ℒₛₑₜ k) :
    encSent (a 🡒 b) = mkImp (encSent a) (encSent b) := by
  unfold encSent
  rw [emb_imp, encForm_imp]

lemma encSent_iff {k : ℕ} (a b : Semisentence ℒₛₑₜ k) :
    encSent (a 🡘 b) = mkIff (encSent a) (encSent b) := by
  change encForm (Rewriting.emb (a 🡒 b) ⋏ Rewriting.emb (b 🡒 a)) = _
  unfold mkIff mkAnd
  rw [← encSent_imp, ← encSent_imp]; rfl

lemma encSent_and {k : ℕ} (a b : Semisentence ℒₛₑₜ k) :
    encSent (a ⋏ b) = mkAnd (encSent a) (encSent b) := rfl

lemma encSent_all {k : ℕ} (a : Semisentence ℒₛₑₜ (k + 1)) :
    encSent (∀¹ a) = mkAll (encSent a) := by
  unfold encSent; rw [emb_all]; rfl

lemma encSent_exs {k : ℕ} (a : Semisentence ℒₛₑₜ (k + 1)) :
    encSent (∃¹ a) = mkExs (encSent a) := by
  unfold encSent; rw [emb_exs]; rfl

lemma encSent_bexsMem {k : ℕ} (t : Semiterm ℒₛₑₜ Empty k) (a : Semisentence ℒₛₑₜ (k + 1)) :
    encSent (Semiformula.bexsMem t a) = mkBexsMem (encTerm (Rew.emb t)) (encSent a) := by
  unfold Semiformula.bexsMem mkBexsMem encSent
  change encForm (Rewriting.emb (∃¹ (Semiformula.Operator.Mem.mem.operator (#0 :> Rew.bShift t :> ![]) ⋏ a))) = _
  rw [emb_exs]
  change encForm (∃¹ (Semiformula.rel Language.Set.Rel.mem ![#0, Rew.emb (Rew.bShift t)] ⋏ Rewriting.emb a)) = _
  have hsh : encTerm (Rew.emb (Rew.bShift t)) = bShiftCode 1 (encTerm (Rew.emb t)) := by
    rw [bShiftCode_encTerm]
    cases t with
    | bvar i => rfl
    | fvar x => exact x.elim
    | func f _ => exact f.elim
  rw [encForm_exs, encForm_and]
  refine congrArg mkExs (congrArg (fun x => mkAnd x _) ?_)
  change mkMem 0 (encTerm (Rew.emb (Rew.bShift t))) = mkMem 0 (bShiftCode 1 (encTerm (Rew.emb t)))
  rw [hsh]

lemma nest0_eq {m : ℕ} (φ : SetTheorySemisentence 1) :
    nestFormulaeFuncCode m (encSent φ) [] = encSent (Semiformula.nestFormulaeFunc (m := m) φ ![]) := by
  have h : ([] : List ℕ) =
      List.ofFn (fun i : Fin 0 => encSent ((![] : Fin 0 → SetTheorySemisentence (m + 1)) i)) := rfl
  rw [h, nestFormulaeFuncCode_eq]

lemma nest2_eq {m : ℕ} (φ : SetTheorySemisentence 3) (a b : SetTheorySemisentence (m + 1)) :
    nestFormulaeFuncCode m (encSent φ) [encSent a, encSent b] =
      encSent (Semiformula.nestFormulaeFunc (m := m) φ ![a, b]) := by
  have h : [encSent a, encSent b] = List.ofFn (fun i : Fin 2 => encSent (![a, b] i)) := by
    simp [List.ofFn_succ]
  rw [h, nestFormulaeFuncCode_eq]

lemma nestRel2_eq {m : ℕ} (φ : SetTheorySemisentence 2) (a b : SetTheorySemisentence (m + 1)) :
    nestFormulaeCode m (encSent φ) [encSent a, encSent b] =
      encSent (Semiformula.nestFormulae (m := m) φ ![a, b]) := by
  have h : [encSent a, encSent b] = List.ofFn (fun i : Fin 2 => encSent (![a, b] i)) := by
    simp [List.ofFn_succ]
  rw [h, nestFormulaeCode_eq]

lemma configSetCode_eq (n : ℕ) : configSetCode n = encSent (Constant14.configSet n) := by
  unfold configSetCode Constant14.configSet
  rw [numeralCode_eq n, numeralCode_eq 2, nest0_eq, nest0_eq, nest0_eq,
      nest2_eq, nest2_eq, nest2_eq]
  rw [encSent_all, encSent_imp, encSent_all, encSent_imp]
  rfl

/-- Constant right-hand subformula inside `Constant14.nextConfig` (independent of `n` and `instructions`). -/
def nextConfigConstPart : SetTheorySemisentence 3 :=
  match Constant14.nextConfig 0 Constant14.zero with
  | .and _ (.and _ (.exs (.and _ rest))) => rest
  | _ => ⊤

/-- Constant second argument inside `value.dfn` in `Constant14.nextConfig`. -/
def nextConfigLookupArg : SetTheorySemisentence 5 :=
  Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
    (Semiformula.nestFormulaeFunc SetTheory.kpair.π₁.dfn (op(=).operator (#0 :> #4 :> ![]) :> ![]) :>
      Semiformula.nestFormulaeFunc SetTheory.value.dfn
        (Semiformula.nestFormulaeFunc SetTheory.kpair.π₂.dfn
          (Semiformula.nestFormulaeFunc SetTheory.kpair.π₂.dfn
            (op(=).operator (#0 :> #4 :> ![]) :> ![]) :> ![]) :>
        Semiformula.nestFormulaeFunc SetTheory.kpair.π₁.dfn
          (Semiformula.nestFormulaeFunc SetTheory.kpair.π₂.dfn
            (op(=).operator (#0 :> #4 :> ![]) :> ![]) :> ![]) :> ![]) :> ![])

def nextConfigCode (n instr : ℕ) : ℕ :=
  let cs := configSetCode n
  let p1 := mkAll (mkImp (mkEq 0 4) (mkAll (mkImp (nestFormulaeFuncCode 3 cs []) (mkMem 2 0))))
  let p2 := mkAll (mkImp (mkEq 0 2) (mkAll (mkImp (nestFormulaeFuncCode 3 cs []) (mkMem 2 0))))
  let p3a := mkAll (mkImp (mkEq 0 2)
    (mkAll (mkImp
      (nestFormulaeFuncCode 4 (encSent SetTheory.value.dfn)
        [nestFormulaeFuncCode 4 instr [], encSent nextConfigLookupArg])
      (mkEq 2 0))))
  mkAnd p1 (mkAnd p2 (mkExs (mkAnd p3a (encSent nextConfigConstPart))))

lemma primrec₂_nextConfigCode : Primrec₂ nextConfigCode := by
  unfold nextConfigCode
  have hcs : Primrec (fun p : ℕ × ℕ => configSetCode p.1) := primrec_configSetCode.comp Primrec.fst
  have hcsN : Primrec (fun p : ℕ × ℕ => nestFormulaeFuncCode 3 (configSetCode p.1) []) :=
    primrec_nestFormulaeFuncCode.comp ((Primrec.const 3).pair (hcs.pair (Primrec.const [])))
  have hp1 : Primrec (fun p : ℕ × ℕ =>
      mkAll (mkImp (mkEq 0 4) (mkAll (mkImp (nestFormulaeFuncCode 3 (configSetCode p.1) []) (mkMem 2 0))))) :=
    primrec_mkAll.comp (primrec₂_mkImp.comp (Primrec.const (mkEq 0 4))
      (primrec_mkAll.comp (primrec₂_mkImp.comp hcsN (Primrec.const (mkMem 2 0)))))
  have hp2 : Primrec (fun p : ℕ × ℕ =>
      mkAll (mkImp (mkEq 0 2) (mkAll (mkImp (nestFormulaeFuncCode 3 (configSetCode p.1) []) (mkMem 2 0))))) :=
    primrec_mkAll.comp (primrec₂_mkImp.comp (Primrec.const (mkEq 0 2))
      (primrec_mkAll.comp (primrec₂_mkImp.comp hcsN (Primrec.const (mkMem 2 0)))))
  have hinstrN : Primrec (fun p : ℕ × ℕ => nestFormulaeFuncCode 4 p.2 []) :=
    primrec_nestFormulaeFuncCode.comp ((Primrec.const 4).pair (Primrec.snd.pair (Primrec.const [])))
  have hp3a : Primrec (fun p : ℕ × ℕ =>
      mkAll (mkImp (mkEq 0 2)
        (mkAll (mkImp
          (nestFormulaeFuncCode 4 (encSent SetTheory.value.dfn)
            [nestFormulaeFuncCode 4 p.2 [], encSent nextConfigLookupArg])
          (mkEq 2 0))))) :=
    primrec_mkAll.comp (primrec₂_mkImp.comp (Primrec.const (mkEq 0 2))
      (primrec_mkAll.comp (primrec₂_mkImp.comp
        (primrec_nestFormulaeFuncCode.comp
          ((Primrec.const 4).pair ((Primrec.const (encSent SetTheory.value.dfn)).pair
            (Primrec.list_cons.comp hinstrN (Primrec.const [encSent nextConfigLookupArg])))))
        (Primrec.const (mkEq 2 0)))))
  exact primrec₂_mkAnd.comp hp1 (primrec₂_mkAnd.comp hp2
    (primrec_mkExs.comp (primrec₂_mkAnd.comp hp3a (Primrec.const (encSent nextConfigConstPart)))))

lemma nextConfigCode_eq (n : ℕ) (instr : SetTheorySemisentence 1) :
    nextConfigCode n (encSent instr) = encSent (Constant14.nextConfig n instr) := by
  unfold nextConfigCode
  dsimp only
  rw [configSetCode_eq, nest0_eq, nest0_eq]
  rw [nest2_eq (φ := SetTheory.value.dfn)]
  unfold Constant14.nextConfig nextConfigConstPart nextConfigLookupArg
  rw [encSent_and, encSent_and, encSent_exs, encSent_and]
  rw [encSent_all, encSent_imp, encSent_all, encSent_imp]
  rw [encSent_all, encSent_imp, encSent_all, encSent_imp]
  rw [encSent_all, encSent_imp, encSent_all, encSent_imp]
  rfl

def nextStepConstLeft : SetTheorySemisentence 2 :=
  ∀¹ (op(=).operator (#0 :> #1 :> ![]) 🡒
    ∀¹ (op(=).operator (#0 :> #3 :> ![]) 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))

def nextStepConstPair : SetTheorySemisentence 6 :=
  ∀¹ (op(=).operator (#0 :> #5 :> ![]) 🡒
    ∀¹ (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
      (op(=).operator (#0 :> #4 :> ![]) :> op(=).operator (#0 :> #2 :> ![]) :> ![]) 🡒
      op(=).operator (#1 :> #0 :> ![])))

def nextStepCode (n instr : ℕ) : ℕ :=
  let cs := configSetCode n
  let nc := nextConfigCode n instr
  mkAll (mkIff (encSent nextStepConstLeft)
    (mkAll (mkImp (nestFormulaeFuncCode 2 cs [])
      (mkBexsMem 0
        (mkAll (mkImp (nestFormulaeFuncCode 4 cs [])
          (mkBexsMem 0
            (mkAnd (encSent nextStepConstPair)
              (nestFormulaeCode 6 nc [mkEq 0 2, mkEq 0 6])))))))))

lemma primrec₂_nextStepCode : Primrec₂ nextStepCode := by
  unfold nextStepCode
  have hcs : Primrec (fun p : ℕ × ℕ => configSetCode p.1) := primrec_configSetCode.comp Primrec.fst
  have hcs2 := primrec_nestFormulaeFuncCode.comp ((Primrec.const 2).pair (hcs.pair (Primrec.const [])))
  have hcs4 := primrec_nestFormulaeFuncCode.comp ((Primrec.const 4).pair (hcs.pair (Primrec.const [])))
  have hnc := primrec_nestFormulaeCode.comp
    ((Primrec.const 6).pair (Primrec.pair primrec₂_nextConfigCode (Primrec.const [mkEq 0 2, mkEq 0 6])))
  exact primrec_mkAll.comp (primrec₂_mkIff.comp (Primrec.const (encSent nextStepConstLeft))
    (primrec_mkAll.comp (primrec₂_mkImp.comp hcs2
      (primrec₂_mkBexsMem.comp (Primrec.const 0)
        (primrec_mkAll.comp (primrec₂_mkImp.comp hcs4
          (primrec₂_mkBexsMem.comp (Primrec.const 0)
            (primrec₂_mkAnd.comp (Primrec.const (encSent nextStepConstPair)) hnc))))))))

lemma nextStepCode_eq (n : ℕ) (instr : SetTheorySemisentence 1) :
    nextStepCode n (encSent instr) = encSent (Constant14.nextStep n instr) := by
  unfold nextStepCode Constant14.nextStep
  dsimp only
  rw [configSetCode_eq, nextConfigCode_eq, nest0_eq, nest0_eq]
  have heq1 : mkEq 0 2 = encSent (op(=).operator (#0 :> #1 :> ![]) : SetTheorySemisentence 7) := rfl
  have heq2 : mkEq 0 6 = encSent (op(=).operator (#0 :> #3 :> ![]) : SetTheorySemisentence 7) := rfl
  rw [heq1, heq2, nestRel2_eq]
  rw [encSent_all, encSent_iff]
  refine congrArg mkAll (congrArg₂ mkIff rfl ?_)
  rw [encSent_all, encSent_imp, encSent_bexsMem, encSent_all, encSent_imp, encSent_bexsMem, encSent_and]
  rfl

def haltsConstFunc : SetTheorySemisentence 3 :=
  Semiformula.nestFormulaeFunc SetTheory.function.dfn
    (Semiformula.nestFormulaeFunc (Constant14.numeral 2) ![] :>
      Semiformula.nestFormulaeFunc Constant14.integers ![] :> ![])

def haltsConstPairMG : SetTheorySemisentence 5 :=
  Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
    (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![])

def haltsCode (c : ℕ) : ℕ :=
  let n := (Nat.unpair c).1 + 1
  let ns := nextStepCode (n + 1) (instructionTableCode c)
  mkAll (mkImp (nestFormulaeFuncCode 0 (encSent Constant14.integers) [])
    (mkBexsMem 0
      (mkAll (mkImp (encSent haltsConstFunc)
        (mkBexsMem 0
          (mkAll (mkImp
            (nestFormulaeFuncCode 4 (encSent SetTheory.kpair.dfn)
              [nestFormulaeFuncCode 4 (numeralCode n) [], encSent haltsConstPairMG])
            (mkAll (mkImp
              (nestFormulaeFuncCode 5 (encSent Constant14.orbit)
                [nestFormulaeFuncCode 5 ns [],
                 nestFormulaeFuncCode 5 (encSent Constant14.initialConfig) []])
              (mkMem 2 0))))))))))

lemma primrec_haltsCode : Primrec haltsCode := by
  unfold haltsCode
  have hn : Primrec (fun c : ℕ => (Nat.unpair c).1 + 1) := Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)
  have hns : Primrec (fun c : ℕ => nextStepCode ((Nat.unpair c).1 + 1 + 1) (instructionTableCode c)) :=
    primrec₂_nextStepCode.comp (Primrec.succ.comp hn) primrec_instructionTableCode
  have htarget := primrec_nestFormulaeFuncCode.comp
    ((Primrec.const 4).pair ((Primrec.const (encSent SetTheory.kpair.dfn)).pair
      (Primrec.list_cons.comp
        (primrec_nestFormulaeFuncCode.comp ((Primrec.const 4).pair ((primrec_numeralCode.comp hn).pair (Primrec.const []))))
        (Primrec.const [encSent haltsConstPairMG]))))
  have horb := primrec_nestFormulaeFuncCode.comp
    ((Primrec.const 5).pair ((Primrec.const (encSent Constant14.orbit)).pair
      (Primrec.list_cons.comp
        (primrec_nestFormulaeFuncCode.comp ((Primrec.const 5).pair (hns.pair (Primrec.const []))))
        (Primrec.const [nestFormulaeFuncCode 5 (encSent Constant14.initialConfig) []]))))
  exact primrec_mkAll.comp (primrec₂_mkImp.comp
    (Primrec.const (nestFormulaeFuncCode 0 (encSent Constant14.integers) []))
    (primrec₂_mkBexsMem.comp (Primrec.const 0)
      (primrec_mkAll.comp (primrec₂_mkImp.comp (Primrec.const (encSent haltsConstFunc))
        (primrec₂_mkBexsMem.comp (Primrec.const 0)
          (primrec_mkAll.comp (primrec₂_mkImp.comp htarget
            (primrec_mkAll.comp (primrec₂_mkImp.comp horb (Primrec.const (mkMem 2 0)))))))))))

lemma haltsCode_eq (c : ℕ) : haltsCode c = encSent (Constant14.halts (decMachine c).2) := by
  unfold haltsCode Constant14.halts
  dsimp only
  rw [instructionTableCode_eq, nextStepCode_eq, numeralCode_eq]
  rw [nest0_eq, nest0_eq, nest0_eq, nest0_eq]
  rw [nest2_eq (φ := SetTheory.kpair.dfn), nest2_eq (φ := Constant14.orbit)]
  rw [encSent_all, encSent_imp, encSent_bexsMem, encSent_all, encSent_imp, encSent_bexsMem,
      encSent_all, encSent_imp, encSent_all, encSent_imp]
  rfl

/- ### Forward Witness Checker for `𝗭𝗙𝗖` Axioms -/

def sepBodyCode (φ : ℕ) : ℕ :=
  mkAll (mkExs (mkAll (mkIff (mkMem 0 2) (mkAnd (mkMem 0 4) (substListCode [0] φ)))))

def repBodyCode (φ : ℕ) : ℕ :=
  let φ1 := substListCode [2, 0] φ
  let exUniq := mkExs (mkAnd (substListCode [0, 2] φ1)
    (mkAll (mkImp (substListCode [0, 4] φ1) (mkEq 0 2))))
  mkImp (mkAll exUniq)
    (mkAll (mkExs (mkAll (mkIff (mkMem 0 2) (mkBexsMem 4 (substListCode [0, 2] φ))))))

lemma sepBodyCode_eq (φ : SetTheorySemiproposition 1) :
    univClCode (sepBodyCode (encForm φ)) = encSent (Axiom.separationSchema φ) := by
  unfold Axiom.separationSchema
  rw [← univClCode_encForm]
  refine congrArg univClCode ?_
  unfold sepBodyCode
  have h1 : [0] = List.ofFn (fun i : Fin 1 => encTerm ((#0 :> ![] : Fin 1 → Semiterm ℒₛₑₜ ℕ 3) i)) := by
    simp [encTerm]
  rw [h1, substListCode_encForm, encForm_all, encForm_exs, encForm_all, encForm_iff, encForm_and]
  rfl

lemma repBodyCode_eq (φ : SetTheorySemiproposition 2) :
    univClCode (repBodyCode (encForm φ)) = encSent (Axiom.replacementSchema φ) := by
  unfold Axiom.replacementSchema
  rw [← univClCode_encForm]
  refine congrArg univClCode ?_
  unfold repBodyCode
  dsimp only
  have h1 : [2, 0] = List.ofFn (fun i : Fin 2 => encTerm ((#1 :> #0 :> ![] : Fin 2 → Semiterm ℒₛₑₜ ℕ 2) i)) := by
    simp [List.ofFn_succ, encTerm]
  have h2 : [0, 2] = List.ofFn (fun i : Fin 2 => encTerm ((#0 :> fun x : Fin 1 => #(BinderNotation.finSuccItr x 1) : Fin 2 → Semiterm ℒₛₑₜ ℕ 2) i)) := by
    simp [List.ofFn_succ, encTerm]
  have h3 : [0, 4] = List.ofFn (fun i : Fin 2 => encTerm ((#0 :> fun x : Fin 1 => #(BinderNotation.finSuccItr x 2) : Fin 2 → Semiterm ℒₛₑₜ ℕ 3) i)) := by
    simp [List.ofFn_succ, encTerm]
  have h4 : [0, 2] = List.ofFn (fun i : Fin 2 => encTerm ((#0 :> #1 :> ![] : Fin 2 → Semiterm ℒₛₑₜ ℕ 4) i)) := by
    simp [List.ofFn_succ, encTerm]
  rw [encForm_imp]
  refine congrArg₂ mkImp ?_ ?_
  · rw [h1, substListCode_encForm, h2, substListCode_encForm, h3, substListCode_encForm]
    unfold Semiformula.existsUnique
    rw [encForm_all, encForm_exs, encForm_and, encForm_all, encForm_imp]
    rfl
  · rw [h4, substListCode_encForm, encForm_all, encForm_exs, encForm_all, encForm_iff, encForm_bexsMem]
    rfl

def fixedZFC : List SetTheorySentence :=
  [ Theory.Eq.refl ℒₛₑₜ,
    Theory.Eq.symm ℒₛₑₜ,
    Theory.Eq.trans ℒₛₑₜ,
    Theory.Eq.relExt Language.Set.Rel.eq,
    Theory.Eq.relExt Language.Set.Rel.mem,
    Axiom.empty,
    Axiom.extentionality,
    Axiom.pairing,
    Axiom.union,
    Axiom.power,
    Axiom.infinity,
    Axiom.foundation,
    Axiom.choice ]

def fixedZFCCodes : List ℕ := fixedZFC.map encSent

def validAxWit (w : ℕ) : Bool :=
  let tag := (Nat.unpair w).1
  let param := (Nat.unpair w).2
  if tag < 13 then true
  else if tag = 13 then wfForm 1 param
  else if tag = 14 then wfForm 2 param
  else false

def axCode (w : ℕ) : ℕ :=
  let tag := (Nat.unpair w).1
  let param := (Nat.unpair w).2
  if tag < 13 then (fixedZFCCodes[tag]?).getD 0
  else if tag = 13 then univClCode (sepBodyCode param)
  else univClCode (repBodyCode param)

lemma primrec_validAxWit : Primrec validAxWit := by
  unfold validAxWit
  have htag := Primrec.fst.comp Primrec.unpair
  have hpar := Primrec.snd.comp Primrec.unpair
  refine Primrec.ite (Primrec.nat_lt.comp htag (Primrec.const 13)) (Primrec.const true) ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 13)) (primrec₂_wfForm.comp (Primrec.const 1) hpar) ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 14)) (primrec₂_wfForm.comp (Primrec.const 2) hpar)
    (Primrec.const false)

lemma primrec_sepBodyCode : Primrec sepBodyCode :=
  primrec_mkAll.comp (primrec_mkExs.comp (primrec_mkAll.comp
    (primrec₂_mkIff.comp (Primrec.const (mkMem 0 2))
      (primrec₂_mkAnd.comp (Primrec.const (mkMem 0 4))
        (primrec₂_substListCode.comp (Primrec.const [0]) Primrec.id)))))

lemma primrec_repBodyCode : Primrec repBodyCode := by
  unfold repBodyCode
  have hφ1 := primrec₂_substListCode.comp (Primrec.const [2, 0]) Primrec.id
  have hex := primrec_mkExs.comp (primrec₂_mkAnd.comp
    (primrec₂_substListCode.comp (Primrec.const [0, 2]) hφ1)
    (primrec_mkAll.comp (primrec₂_mkImp.comp
      (primrec₂_substListCode.comp (Primrec.const [0, 4]) hφ1) (Primrec.const (mkEq 0 2)))))
  exact primrec₂_mkImp.comp (primrec_mkAll.comp hex)
    (primrec_mkAll.comp (primrec_mkExs.comp (primrec_mkAll.comp
      (primrec₂_mkIff.comp (Primrec.const (mkMem 0 2))
        (primrec₂_mkBexsMem.comp (Primrec.const 4)
          (primrec₂_substListCode.comp (Primrec.const [0, 2]) Primrec.id))))))

lemma primrec_axCode : Primrec axCode := by
  unfold axCode
  have htag := Primrec.fst.comp Primrec.unpair
  have hpar := Primrec.snd.comp Primrec.unpair
  refine Primrec.ite (Primrec.nat_lt.comp htag (Primrec.const 13))
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.const fixedZFCCodes) htag) (Primrec.const 0)) ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 13))
    (primrec_univClCode.comp (primrec_sepBodyCode.comp hpar))
    (primrec_univClCode.comp (primrec_repBodyCode.comp hpar))

lemma fixedZFC_mem (i : ℕ) (hi : i < 13) :
    ∃ ψ ∈ 𝗭𝗙𝗖, (fixedZFCCodes[i]?).getD 0 = encSent ψ := by
  interval_cases i
  · exact ⟨_, Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.refl), rfl⟩
  · exact ⟨_, Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.symm), rfl⟩
  · exact ⟨_, Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.trans), rfl⟩
  · exact ⟨_, Or.inl (ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt Language.Set.Rel.eq)), rfl⟩
  · exact ⟨_, Or.inl (ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt Language.Set.Rel.mem)), rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_empty_set, rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_extentionality, rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_pairing, rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_union, rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_power_set, rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_infinity, rfl⟩
  · exact ⟨_, Or.inl ZermeloFraenkel.axiom_of_foundation, rfl⟩
  · exact ⟨_, Or.inr rfl, rfl⟩

lemma axWit_sound {w : ℕ} (h : validAxWit w = true) : ∃ ψ ∈ 𝗭𝗙𝗖, axCode w = encSent ψ := by
  unfold validAxWit at h
  unfold axCode
  dsimp only at h ⊢
  split_ifs at h with h13 heq13 heq14
  · rw [if_pos h13]; exact fixedZFC_mem _ h13
  · rw [if_neg h13, if_pos heq13]
    rw [wfForm_iff_isSome] at h
    obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h
    refine ⟨Axiom.separationSchema φ, Or.inl (ZermeloFraenkel.axiom_of_separation φ), ?_⟩
    rw [← encForm_of_decForm _ 1 φ hφ, sepBodyCode_eq]
  · rw [if_neg h13, if_neg heq13]
    rw [wfForm_iff_isSome] at h
    obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h
    refine ⟨Axiom.replacementSchema φ, Or.inl (ZermeloFraenkel.axiom_of_replacement φ), ?_⟩
    rw [← encForm_of_decForm _ 2 φ hφ, repBodyCode_eq]

lemma axWit_complete {ψ : SetTheorySentence} (h : ψ ∈ 𝗭𝗙𝗖) :
    ∃ w : ℕ, validAxWit w = true ∧ axCode w = encSent ψ := by
  rcases h with h | h
  · cases h with
    | axiom_of_equality _ heq =>
      cases heq with
      | refl => exact ⟨Nat.pair 0 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
      | symm => exact ⟨Nat.pair 1 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
      | trans => exact ⟨Nat.pair 2 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
      | funcExt f => exact f.elim
      | relExt r =>
        cases r with
        | eq => exact ⟨Nat.pair 3 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
        | mem => exact ⟨Nat.pair 4 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_empty_set => exact ⟨Nat.pair 5 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_extentionality => exact ⟨Nat.pair 6 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_pairing => exact ⟨Nat.pair 7 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_union => exact ⟨Nat.pair 8 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_power_set => exact ⟨Nat.pair 9 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_infinity => exact ⟨Nat.pair 10 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_foundation => exact ⟨Nat.pair 11 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩
    | axiom_of_separation φ =>
      refine ⟨Nat.pair 13 (encForm φ), ?_, ?_⟩
      · simp [validAxWit, wfForm_encForm]
      · simp [axCode, sepBodyCode_eq]
    | axiom_of_replacement φ =>
      refine ⟨Nat.pair 14 (encForm φ), ?_, ?_⟩
      · simp [validAxWit, wfForm_encForm]
      · simp [axCode, repBodyCode_eq]
  · have h' : ψ = Axiom.choice := h
    subst h'
    exact ⟨Nat.pair 12 0, by simp [validAxWit], by simp [axCode, fixedZFCCodes, fixedZFC]⟩

/- ## Section 5: Flat LK Derivation Trace Checker & `Nat.Partrec.rfind` -/

abbrev Step := List ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ
abbrev Cert := List ℕ × List Step

def wfSeq (l : List ℕ) : Bool := listAll (wfForm 0) l

lemma primrec_wfSeq : Primrec wfSeq :=
  primrec_listAll Primrec.id (primrec₂_wfForm.comp (Primrec.const 0) Primrec.snd)

def stepSeqAt (steps : List Step) (i : ℕ) : List ℕ :=
  Option.casesOn (steps[i]?) [] (fun st => st.1)

lemma primrec₂_stepSeqAt : Primrec₂ stepSeqAt :=
  Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const []) (Primrec.fst.comp Primrec.snd)

lemma stepSeqAt_of_lt {steps : List Step} {i : ℕ} (hi : i < steps.length) :
    stepSeqAt steps i = steps[i].1 := by
  unfold stepSeqAt
  rw [List.getElem?_eq_getElem hi]

lemma stepSeqAt_append_left {s₁ s₂ : List Step} {i : ℕ} (hi : i < s₁.length) :
    stepSeqAt (s₁ ++ s₂) i = stepSeqAt s₁ i := by
  unfold stepSeqAt
  rw [List.getElem?_append_left hi]

lemma stepSeqAt_append_right {s₁ s₂ : List Step} {i : ℕ} (hge : s₁.length ≤ i) :
    stepSeqAt (s₁ ++ s₂) i = stepSeqAt s₂ (i - s₁.length) := by
  unfold stepSeqAt
  rw [List.getElem?_append_right hge]

lemma stepSeqAt_snoc_last (steps : List Step) (st : Step) :
    stepSeqAt (steps ++ [st]) ((steps ++ [st]).length - 1) = st.1 := by
  rw [stepSeqAt_of_lt (by simp)]
  simp

def checkStep (steps : List Step) (idx : ℕ) (st : Step) : Bool :=
  let seq := st.1
  let tag := st.2.1
  let a1 := st.2.2.1
  let a2 := st.2.2.2.1
  let a3 := st.2.2.2.2.1
  let g1 := st.2.2.2.2.2.1
  let g2 := st.2.2.2.2.2.2
  if tag = 0 then
    -- identity: a1 = rel (0 eq, 1 mem), a2 = t, a3 = u
    natLtB a1 2 && wfTerm 0 a2 && wfTerm 0 a3 &&
      listPerm seq [mkNode a1 (natPair a2 a3), mkNode (a1 + 2) (natPair a2 a3)]
  else if tag = 1 then
    -- cut: a1 = i, a2 = j, a3 = φ, g1 = Γ, g2 = Δ
    natLtB a1 idx && natLtB a2 idx && wfForm 0 a3 && wfSeq g1 && wfSeq g2 &&
      listPerm (stepSeqAt steps a1) (g1 ++ [a3]) &&
      listPerm (stepSeqAt steps a2) (g2 ++ [negCode a3]) &&
      listPerm seq (g1 ++ g2)
  else if tag = 2 then
    -- contraction: a1 = i
    natLtB a1 idx && wfSeq seq && listSub (stepSeqAt steps a1) seq
  else if tag = 3 then
    -- verum
    listPerm seq [0]
  else if tag = 4 then
    -- or: a1 = i, a2 = φ, a3 = ψ, g1 = Γ
    natLtB a1 idx && wfForm 0 a2 && wfForm 0 a3 && wfSeq g1 &&
      listPerm (stepSeqAt steps a1) (g1 ++ [a2, a3]) &&
      listPerm seq (g1 ++ [mkOr a2 a3])
  else if tag = 5 then
    -- and: a1 = i, a2 = j, a3 = Nat.pair φ ψ, g1 = Γ
    let φ := (Nat.unpair a3).1
    let ψ := (Nat.unpair a3).2
    natLtB a1 idx && natLtB a2 idx && wfForm 0 φ && wfForm 0 ψ && wfSeq g1 &&
      listPerm (stepSeqAt steps a1) (g1 ++ [φ]) &&
      listPerm (stepSeqAt steps a2) (g1 ++ [ψ]) &&
      listPerm seq (g1 ++ [mkAnd φ ψ])
  else if tag = 6 then
    -- all: a1 = i, a2 = φ, g1 = Γ
    natLtB a1 idx && wfForm 1 a2 && wfSeq g1 &&
      listPerm (stepSeqAt steps a1) (g1.map shiftCode ++ [freeCode a2]) &&
      listPerm seq (g1 ++ [mkAll a2])
  else if tag = 7 then
    -- exs: a1 = i, a2 = φ, a3 = t, g1 = Γ
    natLtB a1 idx && wfForm 1 a2 && wfTerm 0 a3 && wfSeq g1 &&
      listPerm (stepSeqAt steps a1) (g1 ++ [subst1Code a3 a2]) &&
      listPerm seq (g1 ++ [mkExs a2])
  else false

lemma primrec_checkStep : Primrec (fun x : List Step × ℕ × Step => checkStep x.1 x.2.1 x.2.2) := by
  unfold checkStep
  have hsteps : Primrec (fun x : List Step × ℕ × Step => x.1) := Primrec.fst
  have hidx : Primrec (fun x : List Step × ℕ × Step => x.2.1) := Primrec.fst.comp Primrec.snd
  have hst : Primrec (fun x : List Step × ℕ × Step => x.2.2) := Primrec.snd.comp Primrec.snd
  have hseq := Primrec.fst.comp hst
  have htag := Primrec.fst.comp (Primrec.snd.comp hst)
  have ha1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have ha2 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst)))
  have ha3 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))))
  have hg1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst)))))
  have hg2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst)))))
  have pAnd {f g : (List Step × ℕ × Step) → Bool} (hf : Primrec f) (hg : Primrec g) :
      Primrec (fun x => f x && g x) := Primrec.and.comp hf hg
  have hs1 := primrec₂_stepSeqAt.comp hsteps ha1
  have hs2 := primrec₂_stepSeqAt.comp hsteps ha2
  have snoc {l : (List Step × ℕ × Step) → List ℕ} {a : (List Step × ℕ × Step) → ℕ}
      (hl : Primrec l) (ha : Primrec a) : Primrec (fun x => l x ++ [a x]) :=
    Primrec.list_append.comp hl (Primrec.list_cons.comp ha (Primrec.const []))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) ?_ ?_
  · exact pAnd (pAnd (pAnd (primrec₂_natLtB.comp ha1 (Primrec.const 2))
        (primrec₂_wfTerm.comp (Primrec.const 0) ha2))
        (primrec₂_wfTerm.comp (Primrec.const 0) ha3))
      (primrec₂_listPerm.comp hseq
        (Primrec.list_cons.comp (primrec₂_mkNode.comp ha1 (primrec₂_natPair.comp ha2 ha3))
          (Primrec.list_cons.comp (primrec₂_mkNode.comp (Primrec.nat_add.comp ha1 (Primrec.const 2))
            (primrec₂_natPair.comp ha2 ha3)) (Primrec.const []))))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) ?_ ?_
  · exact pAnd (pAnd (pAnd (pAnd (pAnd (pAnd (pAnd
        (primrec₂_natLtB.comp ha1 hidx)
        (primrec₂_natLtB.comp ha2 hidx))
        (primrec₂_wfForm.comp (Primrec.const 0) ha3))
        (primrec_wfSeq.comp hg1))
        (primrec_wfSeq.comp hg2))
        (primrec₂_listPerm.comp hs1 (snoc hg1 ha3)))
        (primrec₂_listPerm.comp hs2 (snoc hg2 (primrec_negCode.comp ha3))))
      (primrec₂_listPerm.comp hseq (Primrec.list_append.comp hg1 hg2))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) ?_ ?_
  · exact pAnd (pAnd (primrec₂_natLtB.comp ha1 hidx) (primrec_wfSeq.comp hseq))
      (primrec₂_listSub.comp hs1 hseq)
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) ?_ ?_
  · exact primrec₂_listPerm.comp hseq (Primrec.const [0])
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) ?_ ?_
  · exact pAnd (pAnd (pAnd (pAnd (pAnd
        (primrec₂_natLtB.comp ha1 hidx)
        (primrec₂_wfForm.comp (Primrec.const 0) ha2))
        (primrec₂_wfForm.comp (Primrec.const 0) ha3))
        (primrec_wfSeq.comp hg1))
        (primrec₂_listPerm.comp hs1 (Primrec.list_append.comp hg1
          (Primrec.list_cons.comp ha2 (Primrec.list_cons.comp ha3 (Primrec.const []))))))
      (primrec₂_listPerm.comp hseq (snoc hg1 (primrec₂_mkOr.comp ha2 ha3)))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) ?_ ?_
  · have hφ := Primrec.fst.comp (Primrec.unpair.comp ha3)
    have hψ := Primrec.snd.comp (Primrec.unpair.comp ha3)
    exact pAnd (pAnd (pAnd (pAnd (pAnd (pAnd (pAnd
        (primrec₂_natLtB.comp ha1 hidx)
        (primrec₂_natLtB.comp ha2 hidx))
        (primrec₂_wfForm.comp (Primrec.const 0) hφ))
        (primrec₂_wfForm.comp (Primrec.const 0) hψ))
        (primrec_wfSeq.comp hg1))
        (primrec₂_listPerm.comp hs1 (snoc hg1 hφ)))
        (primrec₂_listPerm.comp hs2 (snoc hg1 hψ)))
      (primrec₂_listPerm.comp hseq (snoc hg1 (primrec₂_mkAnd.comp hφ hψ)))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) ?_ ?_
  · exact pAnd (pAnd (pAnd (pAnd
        (primrec₂_natLtB.comp ha1 hidx)
        (primrec₂_wfForm.comp (Primrec.const 1) ha2))
        (primrec_wfSeq.comp hg1))
        (primrec₂_listPerm.comp hs1 (snoc (Primrec.list_map hg1 (primrec_shiftCode.comp Primrec.snd))
          (primrec_freeCode.comp ha2))))
      (primrec₂_listPerm.comp hseq (snoc hg1 (primrec_mkAll.comp ha2)))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) ?_ (Primrec.const false)
  · exact pAnd (pAnd (pAnd (pAnd (pAnd
        (primrec₂_natLtB.comp ha1 hidx)
        (primrec₂_wfForm.comp (Primrec.const 1) ha2))
        (primrec₂_wfTerm.comp (Primrec.const 0) ha3))
        (primrec_wfSeq.comp hg1))
        (primrec₂_listPerm.comp hs1 (snoc hg1 (primrec₂_subst1Code.comp ha3 ha2))))
      (primrec₂_listPerm.comp hseq (snoc hg1 (primrec_mkExs.comp ha2)))

def checkSteps (steps : List Step) : Bool :=
  listAll (fun idx => Option.casesOn (steps[idx]?) false (fun st => checkStep steps idx st))
    (List.range steps.length)

lemma primrec_checkSteps : Primrec checkSteps :=
  primrec_listAll (Primrec.list_range.comp Primrec.list_length)
    (Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const false)
      (primrec_checkStep.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))))

lemma checkSteps_iff {steps : List Step} :
    checkSteps steps = true ↔ ∀ idx (hlt : idx < steps.length), checkStep steps idx steps[idx] = true := by
  rw [checkSteps, listAll_iff]
  constructor
  · intro h idx hlt
    have h1 := h idx (List.mem_range.mpr hlt)
    rw [List.getElem?_eq_getElem hlt] at h1
    exact h1
  · intro h idx hidx
    have hlt : idx < steps.length := List.mem_range.mp hidx
    rw [List.getElem?_eq_getElem hlt]
    exact h idx hlt

def checkCert (c : ℕ) (cert : Cert) : Bool :=
  let axWits := cert.1
  let steps := cert.2
  natLtB 0 steps.length &&
    listAll validAxWit axWits &&
    checkSteps steps &&
    listPerm (stepSeqAt steps (steps.length - 1))
      (negCode (haltsCode c) :: axWits.map (fun w => negCode (axCode w)))

lemma primrec₂_checkCert : Primrec₂ checkCert := by
  unfold checkCert
  have hc : Primrec (fun p : ℕ × Cert => p.1) := Primrec.fst
  have hax : Primrec (fun p : ℕ × Cert => p.2.1) := Primrec.fst.comp Primrec.snd
  have hst : Primrec (fun p : ℕ × Cert => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlen := Primrec.list_length.comp hst
  exact Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp
        (primrec₂_natLtB.comp (Primrec.const 0) hlen)
        (primrec_listAll hax (primrec_validAxWit.comp Primrec.snd)))
      (primrec_checkSteps.comp hst))
    (primrec₂_listPerm.comp
      (primrec₂_stepSeqAt.comp hst (Primrec.pred.comp hlen))
      (Primrec.list_cons.comp (primrec_negCode.comp (primrec_haltsCode.comp hc))
        (Primrec.list_map hax (primrec_negCode.comp (primrec_axCode.comp Primrec.snd)))))

def checkNat (c p : ℕ) : Bool :=
  Option.casesOn (Encodable.decode (α := Cert) p) false (fun cert => checkCert c cert)

lemma primrec₂_checkNat : Primrec₂ checkNat :=
  Primrec.option_casesOn (Primrec.decode.comp Primrec.snd) (Primrec.const false)
    (primrec₂_checkCert.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

/- ### Soundness of `checkCert` -/

lemma decode_wfSeq {l : List ℕ} (h : wfSeq l = true) :
    ∃ L : List (Proposition ℒₛₑₜ), L.map encForm = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    rw [wfSeq, listAll_iff] at h
    have ha : wfForm 0 a = true := h a (List.mem_cons_self ..)
    have hl : wfSeq l = true := (listAll_iff _ _).mpr fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [wfForm_iff_isSome] at ha
    obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨L, hL⟩ := ih hl
    exact ⟨φ :: L, by simp [encForm_of_decForm _ 0 φ hφ, hL]⟩

lemma perm_of_map_encForm {L₁ L₂ : List (Proposition ℒₛₑₜ)}
    (h : (L₁.map encForm).Perm (L₂.map encForm)) : L₁.Perm L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    have hnil : L₂.map encForm = [] := (List.Perm.nil_eq h).symm
    cases L₂ with
    | nil => exact List.Perm.nil
    | cons _ _ => simp at hnil
  | cons x xs ih =>
    have hx : encForm x ∈ L₂.map encForm := h.subset (List.mem_cons_self ..)
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx
    have hxy : y = x := encForm_inj heq
    subst hxy
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hy
    have hperm' : (xs.map encForm).Perm ((l1 ++ l2).map encForm) := by
      have h1 : (encForm y :: xs.map encForm).Perm (encForm y :: (l1 ++ l2).map encForm) := by
        refine h.trans ?_
        simp only [List.map_append, List.map_cons]
        exact List.perm_middle
      exact List.Perm.cons_inv h1
    have htail : xs.Perm (l1 ++ l2) := ih hperm'
    exact (List.Perm.cons y htail).trans List.perm_middle.symm

lemma multiset_eq_of_perm_map {L₁ L₂ : List (Proposition ℒₛₑₜ)}
    (h : (L₁.map encForm).Perm (L₂.map encForm)) :
    (L₁ : Sequent ℒₛₑₜ) = (L₂ : Sequent ℒₛₑₜ) :=
  Multiset.coe_eq_coe.mpr (perm_of_map_encForm h)

lemma coe_append_singleton {α : Type*} (L : List α) (a : α) :
    ((L ++ [a] : List α) : Multiset α) = (L : Multiset α) + ⦃a⦄ := by
  rw [← Multiset.coe_add]; rfl

lemma coe_append_pair {α : Type*} (L : List α) (a b : α) :
    ((L ++ [a, b] : List α) : Multiset α) = (L : Multiset α) + ⦃a, b⦄ := by
  rw [← Multiset.coe_add]
  change (L : Multiset α) + (a ::ₘ b ::ₘ 0) = (L : Multiset α) + ({a} + {b})
  simp [Multiset.singleton_add]

lemma coe_pair {α : Type*} (a b : α) :
    (([a, b] : List α) : Multiset α) = ⦃a, b⦄ := by
  simpa using coe_append_pair ([] : List α) a b

lemma decode_of_perm_map {l : List ℕ} {L : List (Proposition ℒₛₑₜ)}
    (h : l.Perm (L.map encForm)) :
    ∃ L' : List (Proposition ℒₛₑₜ), L'.map encForm = l ∧ (L' : Sequent ℒₛₑₜ) = (L : Sequent ℒₛₑₜ) := by
  have hwf : wfSeq l = true := by
    rw [wfSeq, listAll_iff]
    intro x hx
    have hx' : x ∈ L.map encForm := h.subset hx
    obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hx'
    exact wfForm_encForm φ
  obtain ⟨L', hL'⟩ := decode_wfSeq hwf
  refine ⟨L', hL', multiset_eq_of_perm_map (hL'.symm ▸ h)⟩

lemma checkSteps_sound {steps : List Step} (hsteps : checkSteps steps = true) :
    ∀ idx (hlt : idx < steps.length),
      ∃ L : List (Proposition ℒₛₑₜ), L.map encForm = steps[idx].1 ∧ Nonempty (Derivation (L : Sequent ℒₛₑₜ)) := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | h idx ih =>
    intro hlt
    have hst := (checkSteps_iff.mp hsteps) idx hlt
    set st := steps[idx]
    set seq := st.1
    set tag := st.2.1
    set a1 := st.2.2.1
    set a2 := st.2.2.2.1
    set a3 := st.2.2.2.2.1
    set g1 := st.2.2.2.2.2.1
    set g2 := st.2.2.2.2.2.2
    unfold checkStep at hst
    dsimp only at hst
    split_ifs at hst with h0 h1 h2 h3 h4 h5 h6 h7
    · -- identity
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, wfTerm_iff_isSome, listPerm_iff] at hst
      rcases hst with ⟨⟨⟨hr, ht⟩, hu⟩, hperm⟩
      obtain ⟨t, ht'⟩ := Option.isSome_iff_exists.mp ht
      obtain ⟨u, hu'⟩ := Option.isSome_iff_exists.mp hu
      have ht_eq := encTerm_of_decTerm ht'
      have hu_eq := encTerm_of_decTerm hu'
      have ha1 : st.2.2.1 = 0 ∨ st.2.2.1 = 1 := by omega
      rcases ha1 with ha1 | ha1
      · rw [ha1] at hperm
        have hL : [Semiformula.rel Language.Set.Rel.eq ![t, u],
            Semiformula.nrel Language.Set.Rel.eq ![t, u]].map encForm =
            [mkNode 0 (natPair st.2.2.2.1 st.2.2.2.2.1), mkNode 2 (natPair st.2.2.2.1 st.2.2.2.2.1)] := by
          simp [encForm, ht_eq, hu_eq]
        obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (hL ▸ hperm)
        exact ⟨L', hL'1, (hL'2.trans (coe_pair _ _)) ▸ ⟨Derivation.identity Language.Set.Rel.eq ![t, u]⟩⟩
      · rw [ha1] at hperm
        have hL : [Semiformula.rel Language.Set.Rel.mem ![t, u],
            Semiformula.nrel Language.Set.Rel.mem ![t, u]].map encForm =
            [mkNode 1 (natPair st.2.2.2.1 st.2.2.2.2.1), mkNode 3 (natPair st.2.2.2.1 st.2.2.2.2.1)] := by
          simp [encForm, ht_eq, hu_eq]
        obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (hL ▸ hperm)
        exact ⟨L', hL'1, (hL'2.trans (coe_pair _ _)) ▸ ⟨Derivation.identity Language.Set.Rel.mem ![t, u]⟩⟩
    · -- cut
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_iff_isSome, listPerm_iff] at hst
      rcases hst with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, hφ⟩, hg1⟩, hg2⟩, hp1⟩, hp2⟩, hpseq⟩
      obtain ⟨L1, hL1, ⟨d1⟩⟩ := ih a1 hi (lt_trans hi hlt)
      obtain ⟨L2, hL2, ⟨d2⟩⟩ := ih a2 hj (lt_trans hj hlt)
      obtain ⟨φ, hφ'⟩ := Option.isSome_iff_exists.mp hφ
      have hφ_eq := encForm_of_decForm _ 0 φ hφ'
      obtain ⟨G1, hG1⟩ := decode_wfSeq hg1
      obtain ⟨G2, hG2⟩ := decode_wfSeq hg2
      have hs1 : stepSeqAt steps a1 = L1.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hi hlt), hL1]
      have hs2 : stepSeqAt steps a2 = L2.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hj hlt), hL2]
      rw [hs1, ← hG1, ← hφ_eq] at hp1
      rw [hs2, ← hG2, ← hφ_eq, negCode_encForm] at hp2
      have hM1 : (L1 : Sequent ℒₛₑₜ) = (G1 : Sequent ℒₛₑₜ) + ⦃φ⦄ :=
        (multiset_eq_of_perm_map (L₂ := G1 ++ [φ]) (by simpa using hp1)).trans (coe_append_singleton G1 φ)
      have hM2 : (L2 : Sequent ℒₛₑₜ) = (G2 : Sequent ℒₛₑₜ) + ⦃∼φ⦄ :=
        (multiset_eq_of_perm_map (L₂ := G2 ++ [∼φ]) (by simpa using hp2)).trans (coe_append_singleton G2 (∼φ))
      rw [hM1] at d1; rw [hM2] at d2
      rw [← hG1, ← hG2] at hpseq
      obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (L := G1 ++ G2) (by simpa using hpseq)
      exact ⟨L', hL'1, hL'2 ▸ ⟨Derivation.cut d1 d2⟩⟩
    · -- contraction
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, listSub_iff] at hst
      rcases hst with ⟨⟨hi, hwfseq⟩, hsub⟩
      obtain ⟨L1, hL1, ⟨d1⟩⟩ := ih a1 hi (lt_trans hi hlt)
      obtain ⟨L', hL'⟩ := decode_wfSeq hwfseq
      have hs1 : stepSeqAt steps a1 = L1.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hi hlt), hL1]
      rw [hs1, ← hL'] at hsub
      have hsubM : (L1 : Sequent ℒₛₑₜ) ⊆ (L' : Sequent ℒₛₑₜ) := by
        rw [Multiset.subset_iff]
        intro φ hφ
        have hmem : encForm φ ∈ L'.map encForm := hsub (encForm φ) (List.mem_map_of_mem hφ)
        obtain ⟨ψ, hψ, heq⟩ := List.mem_map.mp hmem
        exact encForm_inj heq ▸ hψ
      exact ⟨L', hL', ⟨Derivation.contraction d1 hsubM⟩⟩
    · -- verum
      rw [listPerm_iff] at hst
      obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (L := [⊤]) (by simpa [encForm] using hst)
      exact ⟨L', hL'1, hL'2 ▸ ⟨Derivation.verum⟩⟩
    · -- or
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_iff_isSome, listPerm_iff] at hst
      rcases hst with ⟨⟨⟨⟨⟨hi, hφ⟩, hψ⟩, hg1⟩, hp1⟩, hpseq⟩
      obtain ⟨L1, hL1, ⟨d1⟩⟩ := ih a1 hi (lt_trans hi hlt)
      obtain ⟨φ, hφ'⟩ := Option.isSome_iff_exists.mp hφ
      obtain ⟨ψ, hψ'⟩ := Option.isSome_iff_exists.mp hψ
      have hφ_eq := encForm_of_decForm _ 0 φ hφ'
      have hψ_eq := encForm_of_decForm _ 0 ψ hψ'
      obtain ⟨G1, hG1⟩ := decode_wfSeq hg1
      have hs1 : stepSeqAt steps a1 = L1.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hi hlt), hL1]
      rw [hs1, ← hG1, ← hφ_eq, ← hψ_eq] at hp1
      have hM1 : (L1 : Sequent ℒₛₑₜ) = (G1 : Sequent ℒₛₑₜ) + ⦃φ, ψ⦄ :=
        (multiset_eq_of_perm_map (L₂ := G1 ++ [φ, ψ]) (by simpa using hp1)).trans (coe_append_pair G1 φ ψ)
      rw [hM1] at d1
      rw [← hG1, ← hφ_eq, ← hψ_eq] at hpseq
      obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (L := G1 ++ [φ ⋎ ψ])
        (by simpa [encForm_or] using hpseq)
      exact ⟨L', hL'1, hL'2 ▸ (coe_append_singleton G1 (φ ⋎ ψ)).symm ▸ ⟨Derivation.or d1⟩⟩
    · -- and
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_iff_isSome, listPerm_iff] at hst
      rcases hst with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, hφ⟩, hψ⟩, hg1⟩, hp1⟩, hp2⟩, hpseq⟩
      obtain ⟨L1, hL1, ⟨d1⟩⟩ := ih a1 hi (lt_trans hi hlt)
      obtain ⟨L2, hL2, ⟨d2⟩⟩ := ih a2 hj (lt_trans hj hlt)
      obtain ⟨φ, hφ'⟩ := Option.isSome_iff_exists.mp hφ
      obtain ⟨ψ, hψ'⟩ := Option.isSome_iff_exists.mp hψ
      have hφ_eq := encForm_of_decForm _ 0 φ hφ'
      have hψ_eq := encForm_of_decForm _ 0 ψ hψ'
      obtain ⟨G1, hG1⟩ := decode_wfSeq hg1
      have hs1 : stepSeqAt steps a1 = L1.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hi hlt), hL1]
      have hs2 : stepSeqAt steps a2 = L2.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hj hlt), hL2]
      rw [hs1, ← hG1, ← hφ_eq] at hp1
      rw [hs2, ← hG1, ← hψ_eq] at hp2
      have hM1 : (L1 : Sequent ℒₛₑₜ) = (G1 : Sequent ℒₛₑₜ) + ⦃φ⦄ :=
        (multiset_eq_of_perm_map (L₂ := G1 ++ [φ]) (by simpa using hp1)).trans (coe_append_singleton G1 φ)
      have hM2 : (L2 : Sequent ℒₛₑₜ) = (G1 : Sequent ℒₛₑₜ) + ⦃ψ⦄ :=
        (multiset_eq_of_perm_map (L₂ := G1 ++ [ψ]) (by simpa using hp2)).trans (coe_append_singleton G1 ψ)
      rw [hM1] at d1; rw [hM2] at d2
      rw [← hG1, ← hφ_eq, ← hψ_eq] at hpseq
      obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (L := G1 ++ [φ ⋏ ψ])
        (by simpa [encForm_and] using hpseq)
      exact ⟨L', hL'1, hL'2 ▸ (coe_append_singleton G1 (φ ⋏ ψ)).symm ▸ ⟨Derivation.and d1 d2⟩⟩
    · -- all
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_iff_isSome, listPerm_iff] at hst
      rcases hst with ⟨⟨⟨⟨hi, hφ⟩, hg1⟩, hp1⟩, hpseq⟩
      obtain ⟨L1, hL1, ⟨d1⟩⟩ := ih a1 hi (lt_trans hi hlt)
      obtain ⟨φ, hφ'⟩ := Option.isSome_iff_exists.mp hφ
      have hφ_eq := encForm_of_decForm _ 1 φ hφ'
      obtain ⟨G1, hG1⟩ := decode_wfSeq hg1
      have hs1 : stepSeqAt steps a1 = L1.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hi hlt), hL1]
      have hmap_shift : st.2.2.2.2.2.1.map shiftCode = (G1.map Rewriting.shift).map encForm := by
        rw [← hG1, List.map_map, List.map_map]
        refine List.map_congr_left fun x _ => shiftCode_encForm x
      rw [hs1, hmap_shift, ← hφ_eq, freeCode_encForm] at hp1
      have hM1 : (L1 : Sequent ℒₛₑₜ) = (G1 : Sequent ℒₛₑₜ)⁺ + ⦃φ.free⦄ :=
        (multiset_eq_of_perm_map (L₂ := G1.map Rewriting.shift ++ [φ.free]) (by simpa using hp1)).trans
          (coe_append_singleton (G1.map Rewriting.shift) φ.free)
      rw [hM1] at d1
      rw [← hG1, ← hφ_eq] at hpseq
      obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (L := G1 ++ [∀¹ φ])
        (by simpa [encForm_all] using hpseq)
      exact ⟨L', hL'1, hL'2 ▸ (coe_append_singleton G1 (∀¹ φ)).symm ▸ ⟨Derivation.all d1⟩⟩
    · -- exs
      simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_iff_isSome, wfTerm_iff_isSome,
        listPerm_iff] at hst
      rcases hst with ⟨⟨⟨⟨⟨hi, hφ⟩, ht⟩, hg1⟩, hp1⟩, hpseq⟩
      obtain ⟨L1, hL1, ⟨d1⟩⟩ := ih a1 hi (lt_trans hi hlt)
      obtain ⟨φ, hφ'⟩ := Option.isSome_iff_exists.mp hφ
      obtain ⟨t, ht'⟩ := Option.isSome_iff_exists.mp ht
      have hφ_eq := encForm_of_decForm _ 1 φ hφ'
      have ht_eq := encTerm_of_decTerm ht'
      obtain ⟨G1, hG1⟩ := decode_wfSeq hg1
      have hs1 : stepSeqAt steps a1 = L1.map encForm := by
        rw [stepSeqAt_of_lt (lt_trans hi hlt), hL1]
      rw [hs1, ← hG1, ← hφ_eq, ← ht_eq, subst1Code_encForm] at hp1
      have hM1 : (L1 : Sequent ℒₛₑₜ) = (G1 : Sequent ℒₛₑₜ) + ⦃φ/[t]⦄ :=
        (multiset_eq_of_perm_map (L₂ := G1 ++ [φ/[t]]) (by simpa using hp1)).trans
          (coe_append_singleton G1 (φ/[t]))
      rw [hM1] at d1
      rw [← hG1, ← hφ_eq] at hpseq
      obtain ⟨L', hL'1, hL'2⟩ := decode_of_perm_map (L := G1 ++ [∃¹ φ])
        (by simpa [encForm_exs] using hpseq)
      exact ⟨L', hL'1, hL'2 ▸ (coe_append_singleton G1 (∃¹ φ)).symm ▸ ⟨Derivation.exs d1⟩⟩

lemma checkCert_sound {c : ℕ} {cert : Cert} (h : checkCert c cert = true) :
    FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (decMachine c).2) := by
  unfold checkCert at h
  simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, listAll_iff, listPerm_iff] at h
  rcases h with ⟨⟨⟨hlen, hax⟩, hsteps⟩, hlast⟩
  have hlast_idx : cert.2.length - 1 < cert.2.length := by omega
  obtain ⟨L, hL, ⟨d⟩⟩ := checkSteps_sound hsteps (cert.2.length - 1) hlast_idx
  have hax_list : ∀ (ws : List ℕ), (∀ w ∈ ws, validAxWit w = true) →
      ∃ Ψ : List SetTheorySentence, (∀ ψ ∈ Ψ, ψ ∈ 𝗭𝗙𝗖) ∧
        Ψ.map (fun ψ => encForm (Rewriting.emb (ξ := ℕ) (∼ψ))) = ws.map (fun w => negCode (axCode w)) := by
    intro ws
    induction ws with
    | nil => intro _; exact ⟨[], ⟨fun _ h => by simp at h, rfl⟩⟩
    | cons w ws ih =>
      intro hw
      obtain ⟨ψ, hψmem, hψeq⟩ := axWit_sound (hw w (List.mem_cons_self ..))
      obtain ⟨Ψ, hΨmem, hΨeq⟩ := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
      refine ⟨ψ :: Ψ, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hψmem
        · exact hΨmem x hx
      · simp only [List.map_cons, hΨeq, hψeq]
        refine congrArg (fun x => x :: _) ?_
        unfold encSent
        rw [negCode_encForm, emb_neg]
  obtain ⟨Ψ, hΨmem, hΨeq⟩ := hax_list cert.1 hax
  have hs_last : stepSeqAt cert.2 (cert.2.length - 1) = L.map encForm := by
    rw [stepSeqAt_of_lt hlast_idx, hL]
  rw [hs_last, haltsCode_eq, ← hΨeq] at hlast
  have hneg_halts : negCode (encSent (Constant14.halts (decMachine c).2)) =
      encForm (Rewriting.emb (ξ := ℕ) (∼Constant14.halts (decMachine c).2)) := by
    unfold encSent; rw [negCode_encForm, emb_neg]
  rw [hneg_halts] at hlast
  let goalList : List (Proposition ℒₛₑₜ) :=
    Rewriting.emb (ξ := ℕ) (∼Constant14.halts (decMachine c).2) ::
      Ψ.map (fun ψ => Rewriting.emb (ξ := ℕ) (∼ψ))
  have hgoal_map : goalList.map encForm =
      encForm (Rewriting.emb (ξ := ℕ) (∼Constant14.halts (decMachine c).2)) ::
        Ψ.map (fun ψ => encForm (Rewriting.emb (ξ := ℕ) (∼ψ))) := by
    simp [goalList, List.map_map]
  have hM : (L : Sequent ℒₛₑₜ) = (goalList : Sequent ℒₛₑₜ) :=
    multiset_eq_of_perm_map (hgoal_map ▸ hlast)
  have hM2 : (goalList : Sequent ℒₛₑₜ) =
      (⦃∼Constant14.halts (decMachine c).2⦄ + ∼(Ψ : Multiset SetTheorySentence)).map (Rewriting.emb (ξ := ℕ)) := by
    have hatom : ⦃∼Constant14.halts (decMachine c).2⦄ = ({∼Constant14.halts (decMachine c).2} : Multiset SetTheorySentence) := rfl
    have hnegM : ∼(Ψ : Multiset SetTheorySentence) = ((Ψ.map (fun ψ => ∼ψ)) : Multiset SetTheorySentence) := rfl
    rw [hatom, hnegM, Multiset.map_add, Multiset.map_singleton, Multiset.map_coe, Multiset.singleton_add]
    simp only [goalList, List.map_map]
    rfl
  rw [hM, hM2] at d
  exact ⟨⟨(Ψ : Multiset SetTheorySentence), fun ψ hψ => hΨmem ψ hψ, d⟩⟩

/- ### Completeness of `checkCert` -/

def shiftStep (off : ℕ) (st : Step) : Step :=
  let tag := st.2.1
  let a1 := st.2.2.1
  let a2 := st.2.2.2.1
  let a1' := if tag = 0 ∨ tag = 3 then a1 else a1 + off
  let a2' := if tag = 1 ∨ tag = 5 then a2 + off else a2
  (st.1, tag, a1', a2', st.2.2.2.2.1, st.2.2.2.2.2.1, st.2.2.2.2.2.2)

lemma checkStep_mono_append {s₁ s₂ : List Step} {idx : ℕ} {st : Step}
    (hidx : idx ≤ s₁.length) (h : checkStep s₁ idx st = true) :
    checkStep (s₁ ++ s₂) idx st = true := by
  have hget : ∀ i, i < idx → stepSeqAt (s₁ ++ s₂) i = stepSeqAt s₁ i := by
    intro i hi
    have hi1 : i < s₁.length := lt_of_lt_of_le hi hidx
    exact stepSeqAt_append_left hi1
  unfold checkStep at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢
  · exact h
  · simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    rw [hget _ hi, hget _ hj]
    exact ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  · simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨hi, h2⟩, h3⟩
    rw [hget _ hi]; exact ⟨⟨hi, h2⟩, h3⟩
  · exact h
  · simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    rw [hget _ hi]; exact ⟨⟨⟨⟨⟨hi, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  · simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    rw [hget _ hi, hget _ hj]
    exact ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  · simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨hi, h2⟩, h3⟩, h4⟩, h5⟩
    rw [hget _ hi]; exact ⟨⟨⟨⟨hi, h2⟩, h3⟩, h4⟩, h5⟩
  · simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    rw [hget _ hi]; exact ⟨⟨⟨⟨⟨hi, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

lemma checkStep_shift_prepend {s₁ s₂ : List Step} {idx : ℕ} {st : Step}
    (hidx : idx < s₂.length) (h : checkStep s₂ idx st = true) :
    checkStep (s₁ ++ s₂.map (shiftStep s₁.length)) (s₁.length + idx) (shiftStep s₁.length st) = true := by
  set s12 := s₁ ++ s₂.map (shiftStep s₁.length)
  have hget : ∀ i, i < idx → stepSeqAt s12 (i + s₁.length) = stepSeqAt s₂ i := by
    intro i hi
    have hi2 : i < s₂.length := lt_trans hi hidx
    rw [stepSeqAt_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
        stepSeqAt_of_lt (by simpa using hi2), stepSeqAt_of_lt hi2, List.getElem_map]
    rfl
  unfold checkStep at h ⊢
  unfold shiftStep
  dsimp only at h ⊢
  by_cases h0 : st.2.1 = 0
  · simp only [h0, ↓reduceIte, true_or, show (0 : ℕ) ≠ 1 by decide,
      show (0 : ℕ) ≠ 5 by decide, or_self] at h ⊢
    exact h
  by_cases h1 : st.2.1 = 1
  · simp only [h1, ↓reduceIte, true_or, or_self, show (1 : ℕ) ≠ 0 by decide,
      show (1 : ℕ) ≠ 3 by decide, Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    rw [hget _ hi, hget _ hj]
    exact ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  by_cases h2 : st.2.1 = 2
  · simp only [h2, ↓reduceIte, or_self, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      show (2 : ℕ) ≠ 3 by decide, Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨hi, h2'⟩, h3⟩
    rw [hget _ hi]; exact ⟨⟨by omega, h2'⟩, h3⟩
  by_cases h3 : st.2.1 = 3
  · simp only [h3, ↓reduceIte, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide] at h ⊢
    exact h
  by_cases h4 : st.2.1 = 4
  · simp only [h4, ↓reduceIte, or_self, show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
      show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, show (4 : ℕ) ≠ 5 by decide,
      Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, h2'⟩, h3'⟩, h4'⟩, h5⟩, h6⟩
    rw [hget _ hi]; exact ⟨⟨⟨⟨⟨by omega, h2'⟩, h3'⟩, h4'⟩, h5⟩, h6⟩
  by_cases h5 : st.2.1 = 5
  · simp only [h5, ↓reduceIte, or_true, or_self, show (5 : ℕ) ≠ 0 by decide, show (5 : ℕ) ≠ 1 by decide,
      show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
      Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h3'⟩, h4'⟩, h5'⟩, h6⟩, h7⟩, h8⟩
    rw [hget _ hi, hget _ hj]
    exact ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, h3'⟩, h4'⟩, h5'⟩, h6⟩, h7⟩, h8⟩
  by_cases h6 : st.2.1 = 6
  · simp only [h6, ↓reduceIte, or_self, show (6 : ℕ) ≠ 0 by decide, show (6 : ℕ) ≠ 1 by decide,
      show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide,
      show (6 : ℕ) ≠ 5 by decide, Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨hi, h2'⟩, h3'⟩, h4'⟩, h5'⟩
    rw [hget _ hi]; exact ⟨⟨⟨⟨by omega, h2'⟩, h3'⟩, h4'⟩, h5'⟩
  by_cases h7 : st.2.1 = 7
  · simp only [h7, ↓reduceIte, or_self, show (7 : ℕ) ≠ 0 by decide, show (7 : ℕ) ≠ 1 by decide,
      show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 4 by decide,
      show (7 : ℕ) ≠ 5 by decide, show (7 : ℕ) ≠ 6 by decide,
      Bool.and_eq_true, natLtB, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩
    rw [hget _ hi]; exact ⟨⟨⟨⟨⟨by omega, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩
  · simp only [h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte] at h
    exact (Bool.false_ne_true h).elim

lemma checkSteps_snoc {steps : List Step} {st : Step}
    (hsteps : checkSteps steps = true) (hst : checkStep steps steps.length st = true) :
    checkSteps (steps ++ [st]) = true := by
  rw [checkSteps_iff] at hsteps ⊢
  intro idx hlt
  have hlt' : idx < steps.length + 1 := by simpa using hlt
  by_cases hi : idx < steps.length
  · rw [List.getElem_append_left hi]
    exact checkStep_mono_append (Nat.le_of_lt hi) (hsteps idx hi)
  · have heq : idx = steps.length := by omega
    subst heq
    let xs := steps ++ [st]
    have hlast : xs[steps.length]'(by simp [xs]) = st := by simp [xs]
    change checkStep xs steps.length (xs[steps.length]'(by simp [xs])) = true
    rw [hlast]
    exact checkStep_mono_append (le_refl _) hst

lemma checkSteps_append_shift {s₁ s₂ : List Step}
    (h1 : checkSteps s₁ = true) (h2 : checkSteps s₂ = true) :
    checkSteps (s₁ ++ s₂.map (shiftStep s₁.length)) = true := by
  rw [checkSteps_iff] at h1 h2 ⊢
  intro idx hlt
  have hlt' : idx < s₁.length + s₂.length := by simpa using hlt
  by_cases hi : idx < s₁.length
  · rw [List.getElem_append_left hi]
    exact checkStep_mono_append (Nat.le_of_lt hi) (h1 idx hi)
  · have hge : s₁.length ≤ idx := Nat.le_of_not_lt hi
    have h2lt : idx - s₁.length < s₂.length := by omega
    rw [List.getElem_append_right hge, List.getElem_map]
    have hres := checkStep_shift_prepend (s₁ := s₁) h2lt (h2 (idx - s₁.length) h2lt)
    rwa [Nat.add_sub_of_le hge] at hres

lemma wfSeq_map_encForm (L : List (Proposition ℒₛₑₜ)) : wfSeq (L.map encForm) = true := by
  rw [wfSeq, listAll_iff]
  intro x hx
  obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hx
  exact wfForm_encForm φ

lemma perm_encForm_of_multiset_eq {L₁ L₂ : List (Proposition ℒₛₑₜ)}
    (h : (L₁ : Sequent ℒₛₑₜ) = (L₂ : Sequent ℒₛₑₜ)) :
    (L₁.map encForm).Perm (L₂.map encForm) :=
  (Multiset.coe_eq_coe.mp h).map encForm

lemma derivation_complete {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    ∃ (steps : List Step) (L : List (Proposition ℒₛₑₜ)),
      0 < steps.length ∧ checkSteps steps = true ∧
      (L : Sequent ℒₛₑₜ) = Γ ∧
      stepSeqAt steps (steps.length - 1) = L.map encForm := by
  induction d with
  | identity r v =>
    cases r with
    | eq =>
      let L : List (Proposition ℒₛₑₜ) := [Semiformula.rel .eq v, Semiformula.nrel .eq v]
      let st : Step := (L.map encForm, 0, 0, encTerm (v 0), encTerm (v 1), [], [])
      refine ⟨[st], L, by simp, ?_, rfl, rfl⟩
      rw [checkSteps_iff]
      intro idx hlt
      have hi : idx = 0 := by simpa using hlt
      subst hi
      simp [st, L, checkStep, natLtB, wfTerm_iff_isSome, decTerm_encTerm, listPerm_iff, encForm]
    | mem =>
      let L : List (Proposition ℒₛₑₜ) := [Semiformula.rel .mem v, Semiformula.nrel .mem v]
      let st : Step := (L.map encForm, 0, 1, encTerm (v 0), encTerm (v 1), [], [])
      refine ⟨[st], L, by simp, ?_, rfl, rfl⟩
      rw [checkSteps_iff]
      intro idx hlt
      have hi : idx = 0 := by simpa using hlt
      subst hi
      simp [st, L, checkStep, natLtB, wfTerm_iff_isSome, decTerm_encTerm, listPerm_iff, encForm]
  | @cut Γ φ Δ _ _ ih1 ih2 =>
    obtain ⟨s1, L1, hlen1, hcs1, hM1, hlast1⟩ := ih1
    obtain ⟨s2, L2, hlen2, hcs2, hM2, hlast2⟩ := ih2
    obtain ⟨G1, rfl⟩ := Quotient.exists_rep Γ
    obtain ⟨G2, rfl⟩ := Quotient.exists_rep Δ
    let s12 := s1 ++ s2.map (shiftStep s1.length)
    let i1 := s1.length - 1
    let i2 := (s2.length - 1) + s1.length
    let seq := (G1 ++ G2).map encForm
    let st : Step := (seq, 1, i1, i2, encForm φ, G1.map encForm, G2.map encForm)
    have hcs12 : checkSteps s12 = true := checkSteps_append_shift hcs1 hcs2
    have hlen12 : s12.length = s1.length + s2.length := by simp [s12]
    have hstep1 : stepSeqAt s12 i1 = L1.map encForm := by
      have hi1 : i1 < s1.length := by omega
      rw [stepSeqAt_append_left hi1]; exact hlast1
    have hstep2 : stepSeqAt s12 i2 = L2.map encForm := by
      have hi2 : s2.length - 1 < s2.length := by omega
      rw [stepSeqAt_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
          stepSeqAt_of_lt (by simpa using hi2), List.getElem_map]
      simpa [shiftStep, stepSeqAt_of_lt hi2] using hlast2
    have hp1 : (L1.map encForm).Perm (G1.map encForm ++ [encForm φ]) := by
      have := perm_encForm_of_multiset_eq (hM1.trans (coe_append_singleton G1 φ).symm)
      simpa using this
    have hp2 : (L2.map encForm).Perm (G2.map encForm ++ [negCode (encForm φ)]) := by
      rw [negCode_encForm]
      have := perm_encForm_of_multiset_eq (hM2.trans (coe_append_singleton G2 (∼φ)).symm)
      simpa using this
    have hst : checkStep s12 s12.length st = true := by
      unfold checkStep
      simp only [st, seq, i1, i2, hlen12, Bool.and_eq_true, natLtB, decide_eq_true_eq,
        wfForm_encForm, wfSeq_map_encForm, listPerm_iff, hstep1, hstep2,
        show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
      exact ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, trivial⟩, trivial⟩, trivial⟩, hp1⟩, hp2⟩, by simp [List.map_append]⟩
    refine ⟨s12 ++ [st], G1 ++ G2, by simp, checkSteps_snoc hcs12 hst, Multiset.coe_add G1 G2, ?_⟩
    rw [stepSeqAt_snoc_last]
  | @contraction Δ Γ _ hsub ih =>
    obtain ⟨s1, L1, hlen1, hcs1, hM1, hlast1⟩ := ih
    obtain ⟨G, rfl⟩ := Quotient.exists_rep Γ
    let i1 := s1.length - 1
    let st : Step := (G.map encForm, 2, i1, 0, 0, [], [])
    have hsubL : ∀ a ∈ L1.map encForm, a ∈ G.map encForm := by
      intro a ha
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp ha
      have hφΔ : φ ∈ Δ := hM1 ▸ hφ
      have hφG : φ ∈ (G : Sequent ℒₛₑₜ) := Multiset.subset_iff.mp hsub hφΔ
      exact List.mem_map_of_mem hφG
    have hst : checkStep s1 s1.length st = true := by
      unfold checkStep
      simp only [st, i1, Bool.and_eq_true, natLtB, decide_eq_true_eq, wfSeq_map_encForm,
        listSub_iff, hlast1, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
      exact ⟨⟨by omega, trivial⟩, hsubL⟩
    refine ⟨s1 ++ [st], G, by simp, checkSteps_snoc hcs1 hst, rfl, ?_⟩
    rw [stepSeqAt_snoc_last]
  | verum =>
    let st : Step := ([0], 3, 0, 0, 0, [], [])
    refine ⟨[st], [⊤], by simp, ?_, rfl, rfl⟩
    rw [checkSteps_iff]
    intro idx hlt
    have hi : idx = 0 := by simpa using hlt
    subst hi
    simp [st, checkStep, listPerm_iff]
  | @or Γ φ ψ _ ih =>
    obtain ⟨s1, L1, hlen1, hcs1, hM1, hlast1⟩ := ih
    obtain ⟨G1, rfl⟩ := Quotient.exists_rep Γ
    let i1 := s1.length - 1
    let st : Step := ((G1 ++ [φ ⋎ ψ]).map encForm, 4, i1, encForm φ, encForm ψ, G1.map encForm, [])
    have hp1 : (L1.map encForm).Perm (G1.map encForm ++ [encForm φ, encForm ψ]) := by
      have := perm_encForm_of_multiset_eq (hM1.trans (coe_append_pair G1 φ ψ).symm)
      simpa using this
    have hst : checkStep s1 s1.length st = true := by
      unfold checkStep
      simp only [st, i1, Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_encForm,
        wfSeq_map_encForm, listPerm_iff, hlast1,
        show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
        show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ↓reduceIte]
      exact ⟨⟨⟨⟨⟨by omega, trivial⟩, trivial⟩, trivial⟩, hp1⟩, by simp [List.map_append, encForm_or]⟩
    refine ⟨s1 ++ [st], G1 ++ [φ ⋎ ψ], by simp, checkSteps_snoc hcs1 hst, coe_append_singleton G1 (φ ⋎ ψ), ?_⟩
    rw [stepSeqAt_snoc_last]
  | @and Γ φ ψ _ _ ih1 ih2 =>
    obtain ⟨s1, L1, hlen1, hcs1, hM1, hlast1⟩ := ih1
    obtain ⟨s2, L2, hlen2, hcs2, hM2, hlast2⟩ := ih2
    obtain ⟨G1, rfl⟩ := Quotient.exists_rep Γ
    let s12 := s1 ++ s2.map (shiftStep s1.length)
    let i1 := s1.length - 1
    let i2 := (s2.length - 1) + s1.length
    let seq := (G1 ++ [φ ⋏ ψ]).map encForm
    let st : Step := (seq, 5, i1, i2, Nat.pair (encForm φ) (encForm ψ), G1.map encForm, [])
    have hcs12 : checkSteps s12 = true := checkSteps_append_shift hcs1 hcs2
    have hlen12 : s12.length = s1.length + s2.length := by simp [s12]
    have hstep1 : stepSeqAt s12 i1 = L1.map encForm := by
      have hi1 : i1 < s1.length := by omega
      rw [stepSeqAt_append_left hi1]; exact hlast1
    have hstep2 : stepSeqAt s12 i2 = L2.map encForm := by
      have hi2 : s2.length - 1 < s2.length := by omega
      rw [stepSeqAt_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
          stepSeqAt_of_lt (by simpa using hi2), List.getElem_map]
      simpa [shiftStep, stepSeqAt_of_lt hi2] using hlast2
    have hp1 : (L1.map encForm).Perm (G1.map encForm ++ [encForm φ]) := by
      have := perm_encForm_of_multiset_eq (hM1.trans (coe_append_singleton G1 φ).symm)
      simpa using this
    have hp2 : (L2.map encForm).Perm (G1.map encForm ++ [encForm ψ]) := by
      have := perm_encForm_of_multiset_eq (hM2.trans (coe_append_singleton G1 ψ).symm)
      simpa using this
    have hst : checkStep s12 s12.length st = true := by
      unfold checkStep
      simp only [st, seq, i1, i2, hlen12, Nat.unpair_pair, Bool.and_eq_true, natLtB,
        decide_eq_true_eq, wfForm_encForm, wfSeq_map_encForm, listPerm_iff, hstep1, hstep2,
        show (5 : ℕ) ≠ 0 by decide, show (5 : ℕ) ≠ 1 by decide,
        show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide,
        show (5 : ℕ) ≠ 4 by decide, ↓reduceIte]
      exact ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, trivial⟩, trivial⟩, trivial⟩, hp1⟩, hp2⟩, by simp [List.map_append, encForm_and]⟩
    refine ⟨s12 ++ [st], G1 ++ [φ ⋏ ψ], by simp, checkSteps_snoc hcs12 hst, coe_append_singleton G1 (φ ⋏ ψ), ?_⟩
    rw [stepSeqAt_snoc_last]
  | @all Γ φ _ ih =>
    obtain ⟨s1, L1, hlen1, hcs1, hM1, hlast1⟩ := ih
    obtain ⟨G1, rfl⟩ := Quotient.exists_rep Γ
    let i1 := s1.length - 1
    let st : Step := ((G1 ++ [∀¹ φ]).map encForm, 6, i1, encForm φ, 0, G1.map encForm, [])
    have hmap_shift : (G1.map encForm).map shiftCode = (G1.map Rewriting.shift).map encForm := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun x _ => shiftCode_encForm x
    have hp1 : (L1.map encForm).Perm ((G1.map encForm).map shiftCode ++ [freeCode (encForm φ)]) := by
      rw [hmap_shift, freeCode_encForm]
      have hM1' : (L1 : Sequent ℒₛₑₜ) = ((G1.map Rewriting.shift ++ [φ.free]) : Sequent ℒₛₑₜ) :=
        hM1.trans (coe_append_singleton (G1.map Rewriting.shift) φ.free).symm
      simpa using perm_encForm_of_multiset_eq hM1'
    have hst : checkStep s1 s1.length st = true := by
      unfold checkStep
      simp only [st, i1, Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_encForm,
        wfSeq_map_encForm, listPerm_iff, hlast1,
        show (6 : ℕ) ≠ 0 by decide, show (6 : ℕ) ≠ 1 by decide,
        show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide,
        show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide, ↓reduceIte]
      exact ⟨⟨⟨⟨by omega, trivial⟩, trivial⟩, hp1⟩, by simp [List.map_append, encForm_all]⟩
    refine ⟨s1 ++ [st], G1 ++ [∀¹ φ], by simp, checkSteps_snoc hcs1 hst, coe_append_singleton G1 (∀¹ φ), ?_⟩
    rw [stepSeqAt_snoc_last]
  | @exs Γ φ t _ ih =>
    obtain ⟨s1, L1, hlen1, hcs1, hM1, hlast1⟩ := ih
    obtain ⟨G1, rfl⟩ := Quotient.exists_rep Γ
    let i1 := s1.length - 1
    let st : Step := ((G1 ++ [∃¹ φ]).map encForm, 7, i1, encForm φ, encTerm t, G1.map encForm, [])
    have hp1 : (L1.map encForm).Perm (G1.map encForm ++ [subst1Code (encTerm t) (encForm φ)]) := by
      rw [subst1Code_encForm]
      have := perm_encForm_of_multiset_eq (hM1.trans (coe_append_singleton G1 (φ/[t])).symm)
      simpa using this
    have hst : checkStep s1 s1.length st = true := by
      unfold checkStep
      simp only [st, i1, Bool.and_eq_true, natLtB, decide_eq_true_eq, wfForm_encForm,
        wfTerm_iff_isSome, decTerm_encTerm, wfSeq_map_encForm, listPerm_iff, hlast1,
        show (7 : ℕ) ≠ 0 by decide, show (7 : ℕ) ≠ 1 by decide,
        show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide,
        show (7 : ℕ) ≠ 4 by decide, show (7 : ℕ) ≠ 5 by decide,
        show (7 : ℕ) ≠ 6 by decide, ↓reduceIte]
      exact ⟨⟨⟨⟨⟨by omega, trivial⟩, rfl⟩, trivial⟩, hp1⟩, by simp [List.map_append, encForm_exs]⟩
    refine ⟨s1 ++ [st], G1 ++ [∃¹ φ], by simp, checkSteps_snoc hcs1 hst, coe_append_singleton G1 (∃¹ φ), ?_⟩
    rw [stepSeqAt_snoc_last]

lemma checkCert_complete {c : ℕ}
    (h : FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (decMachine c).2)) :
    ∃ p : ℕ, checkNat c p = true := by
  obtain ⟨⟨axM, haxM, hderiv⟩⟩ := h
  obtain ⟨axL, haxL_raw⟩ := Quotient.exists_rep axM
  have haxL : (axL : Multiset SetTheorySentence) = axM := haxL_raw
  have hax_wits : ∀ (Ψ : List SetTheorySentence), (∀ ψ ∈ Ψ, ψ ∈ 𝗭𝗙𝗖) →
      ∃ ws : List ℕ, (∀ w ∈ ws, validAxWit w = true) ∧
        ws.map (fun w => negCode (axCode w)) =
          Ψ.map (fun ψ => encForm (Rewriting.emb (ξ := ℕ) (∼ψ))) := by
    intro Ψ
    induction Ψ with
    | nil => intro _; exact ⟨[], ⟨fun _ h => by simp at h, rfl⟩⟩
    | cons ψ Ψ ih =>
      intro hmem
      obtain ⟨w, hw1, hw2⟩ := axWit_complete (hmem ψ (List.mem_cons_self ..))
      obtain ⟨ws, hws1, hws2⟩ := ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      refine ⟨w :: ws, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hw1
        · exact hws1 x hx
      · simp only [List.map_cons, hws2, hw2]
        refine congrArg (fun x => x :: _) ?_
        unfold encSent; rw [negCode_encForm, emb_neg]
  obtain ⟨ws, hws_val, hws_eq⟩ := hax_wits axL (fun ψ hψ => haxM ψ (haxL ▸ hψ))
  obtain ⟨steps, L, hlen, hcs, hM, hlast⟩ := derivation_complete hderiv
  let cert : Cert := (ws, steps)
  refine ⟨Encodable.encode cert, ?_⟩
  unfold checkNat
  rw [Encodable.encodek]
  dsimp only
  unfold checkCert
  simp only [Bool.and_eq_true, natLtB, decide_eq_true_eq, listAll_iff, listPerm_iff]
  refine ⟨⟨⟨hlen, hws_val⟩, hcs⟩, ?_⟩
  rw [hlast, haltsCode_eq, hws_eq]
  have hneg_halts : negCode (encSent (Constant14.halts (decMachine c).2)) =
      encForm (Rewriting.emb (ξ := ℕ) (∼Constant14.halts (decMachine c).2)) := by
    unfold encSent; rw [negCode_encForm, emb_neg]
  rw [hneg_halts]
  let goalList : List (Proposition ℒₛₑₜ) :=
    Rewriting.emb (ξ := ℕ) (∼Constant14.halts (decMachine c).2) ::
      axL.map (fun ψ => Rewriting.emb (ξ := ℕ) (∼ψ))
  have hM_eq : (L : Sequent ℒₛₑₜ) = (goalList : Sequent ℒₛₑₜ) := by
    rw [hM, ← haxL]
    have hatom : ⦃∼Constant14.halts (decMachine c).2⦄ = ({∼Constant14.halts (decMachine c).2} : Multiset SetTheorySentence) := rfl
    have hnegM : ∼(axL : Multiset SetTheorySentence) = ((axL.map (fun ψ => ∼ψ)) : Multiset SetTheorySentence) := rfl
    rw [hatom, hnegM, Multiset.map_add, Multiset.map_singleton, Multiset.map_coe, Multiset.singleton_add]
    simp only [goalList, List.map_map]
    rfl
  have hperm := perm_encForm_of_multiset_eq hM_eq
  simpa [goalList, List.map_map, Function.comp_def] using hperm

/- ### Closing via `Partrec.rfind` -/

lemma partrec_enum :
    ∃ f : ℕ →. ℕ, Nat.Partrec f ∧
      ∀ c : ℕ, (f c).Dom ↔ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (decMachine c).2) := by
  let p : ℕ → ℕ →. Bool := fun c n => Part.some (checkNat c n)
  have hp : Partrec₂ p := primrec₂_checkNat.to_comp.partrec.to₂
  have hf : Nat.Partrec (fun c => Nat.rfind (p c)) := Partrec.nat_iff.mp (Partrec.rfind hp)
  refine ⟨fun c => Nat.rfind (p c), hf, fun c => ?_⟩
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, _⟩
    have hchk : checkNat c n = true := by simpa [p] using hn
    unfold checkNat at hchk
    cases hd : Encodable.decode (α := Cert) n with
    | none => rw [hd] at hchk; simp at hchk
    | some cert => rw [hd] at hchk; exact checkCert_sound hchk
  · intro hprov
    obtain ⟨n, hn⟩ := checkCert_complete hprov
    exact ⟨n, by simpa [p] using hn, fun {m} _ => trivial⟩

end C14H4R1H1

theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1_H4_R1.H1 :=
  C14H4R1H1.partrec_enum
