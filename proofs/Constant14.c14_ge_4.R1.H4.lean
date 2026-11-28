import OMAReductions.R_Constant14_c14_ge_4_R1
import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Tactic

/-!
# Proof of `Constant14.c14_ge_4.R1.H4` (Gödel Incompleteness for `Constant14.halts` in `𝗭𝗙𝗖`)

Proves that there exists a non-halting 2-symbol Busy Beaver Turing machine `M` such that
`𝗭𝗙𝗖 ⊬ ∼Constant14.halts M`.

Architecture:
1. Soundness (`C14Stage2`, `C14H4Sound`): every halting machine `M` satisfies `Constant14.halts M`
   in the standard model `ZFSet.{0}`, so by `OMA.R_Constant14_c14_ge_4_R1.sound_theory`,
   `M.IsHalting → ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)`.
2. Universal 2-symbol Busy Beaver Turing machine (`C14H4TM`): constructs a fixed universal machine
   `U` and a primitive-recursive tape-initialization encoding `inputBits` such that
   `(prependMachine (inputBits ... (encode c)) U).IsHalting ↔ (c.eval 0).Dom`.
3. Recursively enumerable provability (`C14H4RE`): builds a primitive-recursive Gödel numbering of
   `ℒₛₑₜ` semiformulas, the `Constant14.halts (prependMachine L U)` sentence builder, the `𝗭𝗙𝗖`
   axiom checker (including both separation and replacement schemas), and a sound and complete
   primitive-recursive checker for one-sided LK derivations, proving
   `REPred (fun c => Provable 𝗭𝗙𝗖 (∼Constant14.halts (M c)))`.
4. Diagonalization (`OMA.solution`): if every non-halting machine were provably non-halting in
   `𝗭𝗙𝗖`, then `{c | ¬ (c.eval 0).Dom}` would be `REPred`, contradicting
   `ComputablePred.halting_problem_not_re 0`.

Credit: @KevinBigham
-/

/-
# Stage 2: Semantic $\Sigma_1$-Completeness of `Constant14.halts` in Any Model of ZFC
-/

namespace C14Completeness

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped Classical

def tvRaw {V : Type*} {ξ : Type*} {n : ℕ} (e : Fin n → V) (ε : ξ → V) :
    Semiterm ℒₛₑₜ ξ n → V
  | Semiterm.bvar i => e i
  | Semiterm.fvar x => ε x
  | Semiterm.func f _ => (f : Empty).elim

def evalRaw {V : Type*} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ}, (Fin n → V) → (ξ → V) → Semiformula ℒₛₑₜ ξ n → Prop
  | _, _, _, Semiformula.verum => True
  | _, _, _, Semiformula.falsum => False
  | _, e, ε, Semiformula.rel Language.Set.Rel.eq v => req (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.rel Language.Set.Rel.mem v => rmem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.nrel Language.Set.Rel.eq v => ¬ req (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.nrel Language.Set.Rel.mem v => ¬ rmem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
  | _, e, ε, Semiformula.and φ ψ => evalRaw req rmem e ε φ ∧ evalRaw req rmem e ε ψ
  | _, e, ε, Semiformula.or φ ψ => evalRaw req rmem e ε φ ∨ evalRaw req rmem e ε ψ
  | _, e, ε, Semiformula.all φ => ∀ d : V, evalRaw req rmem (d :> e) ε φ
  | _, e, ε, Semiformula.exs φ => ∃ d : V, evalRaw req rmem (d :> e) ε φ

abbrev evalM {V : Type*} (mem : V → V → Prop) {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n) : Prop :=
  evalRaw (V := V) Eq mem e ε φ

lemma evalRaw_neg {V : Type*} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ} (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n),
      evalRaw req rmem e ε (∼φ) ↔ ¬ evalRaw req rmem e ε φ
  | _, _, _, Semiformula.verum => by simp [evalRaw, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | _, _, _, Semiformula.falsum => by simp [evalRaw, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | _, _, _, Semiformula.rel Language.Set.Rel.eq _ => Iff.rfl
  | _, _, _, Semiformula.rel Language.Set.Rel.mem _ => Iff.rfl
  | _, _, _, Semiformula.nrel Language.Set.Rel.eq _ => by
      change _ ↔ ¬ ¬ _; exact not_not.symm
  | _, _, _, Semiformula.nrel Language.Set.Rel.mem _ => by
      change _ ↔ ¬ ¬ _; exact not_not.symm
  | _, e, ε, Semiformula.and φ ψ => by
      change evalRaw req rmem e ε (∼φ) ∨ evalRaw req rmem e ε (∼ψ) ↔
        ¬ (evalRaw req rmem e ε φ ∧ evalRaw req rmem e ε ψ)
      rw [evalRaw_neg req rmem e ε φ, evalRaw_neg req rmem e ε ψ, not_and_or]
  | _, e, ε, Semiformula.or φ ψ => by
      change evalRaw req rmem e ε (∼φ) ∧ evalRaw req rmem e ε (∼ψ) ↔
        ¬ (evalRaw req rmem e ε φ ∨ evalRaw req rmem e ε ψ)
      rw [evalRaw_neg req rmem e ε φ, evalRaw_neg req rmem e ε ψ, not_or]
  | _, e, ε, Semiformula.all φ => by
      change (∃ d, evalRaw req rmem (d :> e) ε (∼φ)) ↔ ¬ ∀ d, evalRaw req rmem (d :> e) ε φ
      simp_rw [evalRaw_neg req rmem _ ε φ]
      exact not_forall.symm
  | _, e, ε, Semiformula.exs φ => by
      change (∀ d, evalRaw req rmem (d :> e) ε (∼φ)) ↔ ¬ ∃ d, evalRaw req rmem (d :> e) ε φ
      simp_rw [evalRaw_neg req rmem _ ε φ]
      exact not_exists.symm

lemma tvRaw_rew {V : Type*} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    tvRaw e ε (ω t) = tvRaw (fun i => tvRaw e ε (ω #i)) (fun x => tvRaw e ε (ω &x)) t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

lemma tvRaw_bShift {V : Type*} {ξ : Type*} {n : ℕ} (d : V) (e : Fin n → V) (ε : ξ → V)
    (t : Semiterm ℒₛₑₜ ξ n) :
    tvRaw (d :> e) ε (Rew.bShift t) = tvRaw e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

lemma evalRaw_congr {V : Type*} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ} {e₁ e₂ : Fin n → V} {ε₁ ε₂ : ξ → V} (φ : Semiformula ℒₛₑₜ ξ n),
      e₁ = e₂ → ε₁ = ε₂ → (evalRaw req rmem e₁ ε₁ φ ↔ evalRaw req rmem e₂ ε₂ φ) := by
  intro n e₁ e₂ ε₁ ε₂ φ he hε
  subst he hε; rfl

lemma evalRaw_rew {V : Type*} (req rmem : V → V → Prop) {ξ₁ ξ₂ : Type*} :
    ∀ {n₁ n₂ : ℕ} (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
      (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      evalRaw req rmem e ε (ω ▹ φ) ↔
        evalRaw req rmem (fun i => tvRaw e ε (ω #i)) (fun x => tvRaw e ε (ω &x)) φ
  | _, _, _, _, _, Semiformula.verum => Iff.rfl
  | _, _, _, _, _, Semiformula.falsum => Iff.rfl
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.eq v => by
      change req (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.mem v => by
      change rmem (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.eq v => by
      change ¬ req (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.mem v => by
      change ¬ rmem (tvRaw e ε (ω (v 0))) (tvRaw e ε (ω (v 1))) ↔ _
      rw [tvRaw_rew e ε ω (v 0), tvRaw_rew e ε ω (v 1)]; rfl
  | _, _, e, ε, ω, Semiformula.and φ ψ =>
      and_congr (evalRaw_rew req rmem e ε ω φ) (evalRaw_rew req rmem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.or φ ψ =>
      or_congr (evalRaw_rew req rmem e ε ω φ) (evalRaw_rew req rmem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.all φ => by
      change (∀ d, evalRaw req rmem (d :> e) ε (ω.q ▹ φ)) ↔ _
      refine forall_congr' fun d => (evalRaw_rew req rmem (d :> e) ε ω.q φ).trans ?_
      refine evalRaw_congr req rmem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          change tvRaw (d :> e) ε (Rew.bShift (ω #i)) = tvRaw e ε (ω #i)
          exact tvRaw_bShift d e ε _
      · funext x
        change tvRaw (d :> e) ε (Rew.bShift (ω &x)) = tvRaw e ε (ω &x)
        exact tvRaw_bShift d e ε _
  | _, _, e, ε, ω, Semiformula.exs φ => by
      change (∃ d, evalRaw req rmem (d :> e) ε (ω.q ▹ φ)) ↔ _
      refine exists_congr fun d => (evalRaw_rew req rmem (d :> e) ε ω.q φ).trans ?_
      refine evalRaw_congr req rmem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          change tvRaw (d :> e) ε (Rew.bShift (ω #i)) = tvRaw e ε (ω #i)
          exact tvRaw_bShift d e ε _
      · funext x
        change tvRaw (d :> e) ε (Rew.bShift (ω &x)) = tvRaw e ε (ω &x)
        exact tvRaw_bShift d e ε _

end C14Completeness

namespace C14Stage2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver C14Completeness
open scoped Classical

/- ## Section 1: `evalM` Connective Rules and `univCl` Elimination -/

lemma evalM_top {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    evalM mem e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True := Iff.rfl

lemma evalM_bot {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    evalM mem e ε (⊥ : Semiformula ℒₛₑₜ ξ n) ↔ False := Iff.rfl

lemma evalM_eq {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    evalM mem e ε (op(=).operator ![t₁, t₂]) ↔ tvRaw e ε t₁ = tvRaw e ε t₂ := Iff.rfl

lemma evalM_mem {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    evalM mem e ε (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔
      mem (tvRaw e ε t₁) (tvRaw e ε t₂) := Iff.rfl

lemma evalM_not {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (∼φ) ↔ ¬ evalM mem e ε φ :=
  evalRaw_neg Eq mem e ε φ

lemma evalM_and {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ ⋏ ψ) ↔ evalM mem e ε φ ∧ evalM mem e ε ψ := Iff.rfl

lemma evalM_or {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ ⋎ ψ) ↔ evalM mem e ε φ ∨ evalM mem e ε ψ := Iff.rfl

lemma evalM_imp {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ 🡒 ψ) ↔ (evalM mem e ε φ → evalM mem e ε ψ) := by
  change evalM mem e ε (∼φ) ∨ evalM mem e ε ψ ↔ _
  rw [evalM_not, imp_iff_not_or]

lemma evalM_iff {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ 🡘 ψ) ↔ (evalM mem e ε φ ↔ evalM mem e ε ψ) := by
  change evalM mem e ε (φ 🡒 ψ) ∧ evalM mem e ε (ψ 🡒 φ) ↔ _
  rw [evalM_imp, evalM_imp]
  exact iff_iff_implies_and_implies.symm

lemma evalM_all {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∀¹ φ) ↔ ∀ d : V, evalM mem (d :> e) ε φ := Iff.rfl

lemma evalM_exs {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∃¹ φ) ↔ ∃ d : V, evalM mem (d :> e) ε φ := Iff.rfl

lemma evalM_ballMem {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (Semiformula.ballMem t φ) ↔
      ∀ d : V, mem d (tvRaw e ε t) → evalM mem (d :> e) ε φ := by
  change (∀ d : V, evalM mem (d :> e) ε
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] 🡒 φ)) ↔ _
  refine forall_congr' fun d => ?_
  rw [evalM_imp, evalM_mem]
  change (mem d (tvRaw (d :> e) ε (Rew.bShift t)) → _) ↔ _
  rw [tvRaw_bShift]

lemma evalM_bexsMem {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (Semiformula.bexsMem t φ) ↔
      ∃ d : V, mem d (tvRaw e ε t) ∧ evalM mem (d :> e) ε φ := by
  change (∃ d : V, evalM mem (d :> e) ε
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] ⋏ φ)) ↔ _
  refine exists_congr fun d => ?_
  rw [evalM_and, evalM_mem]
  change (mem d (tvRaw (d :> e) ε (Rew.bShift t)) ∧ _) ↔ _
  rw [tvRaw_bShift]

lemma evalM_subst {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ → V) (v : Fin n₁ → Semiterm ℒₛₑₜ ξ n₂)
    (φ : Semiformula ℒₛₑₜ ξ n₁) :
    evalM mem e ε (φ ⇜ v) ↔ evalM mem (fun i => tvRaw e ε (v i)) ε φ := by
  exact evalRaw_rew Eq mem e ε (Rew.subst v) φ

lemma evalM_emb {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semisentence ℒₛₑₜ n) :
    evalM mem e ε (Rewriting.emb φ) ↔ evalM mem e Empty.elim φ := by
  refine (evalRaw_rew Eq mem e ε Rew.emb φ).trans ?_
  exact evalRaw_congr Eq mem φ rfl (funext fun x => x.elim)

lemma evalM_existsUnique {V : Type*} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∃¹! φ) ↔ ∃! y : V, evalM mem (y :> e) ε φ := by
  unfold Semiformula.existsUnique ExistsUnique
  rw [evalM_exs]
  refine exists_congr fun y => ?_
  rw [evalM_and, evalM_subst, evalM_all]
  have he1 : (fun k : Fin (n + 1) =>
      tvRaw (y :> e) ε ((#0 :> fun x : Fin n => #(BinderNotation.finSuccItr x 1)) k)) =
      (y :> e) := by
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    simp [BinderNotation.finSuccItr, tvRaw]
  rw [he1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [evalM_imp, evalM_subst, evalM_eq]
  have he2 : (fun k : Fin (n + 1) =>
      tvRaw (z :> y :> e) ε ((#0 :> fun x : Fin n => #(BinderNotation.finSuccItr x 2)) k)) =
      (z :> e) := by
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    simp [BinderNotation.finSuccItr, tvRaw]
  rw [he2]
  rfl

lemma tvRaw_toEmpty {V : Type*} {n : ℕ} (e : Fin n → V) (ε : ℕ → V) (ε0 : Empty → V)
    (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    tvRaw e ε0 (t.toEmpty h) = tvRaw e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => exact absurd h (by simp [Semiterm.freeVariables])
  | func f _ => exact (f : Empty).elim

lemma evalM_toEmpty {V : Type*} {mem : V → V → Prop} :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (h : φ.freeVariables = ∅)
      (e : Fin n → V) (ε : ℕ → V) (ε0 : Empty → V),
      evalM mem e ε0 (φ.toEmpty h) ↔ evalM mem e ε φ
  | _, Semiformula.verum, _, _, _, _ => Iff.rfl
  | _, Semiformula.falsum, _, _, _, _ => Iff.rfl
  | _, Semiformula.rel Language.Set.Rel.eq v, h, e, ε, ε0 => by
      change tvRaw e ε0 ((v 0).toEmpty _) = tvRaw e ε0 ((v 1).toEmpty _) ↔
        tvRaw e ε (v 0) = tvRaw e ε (v 1)
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.rel Language.Set.Rel.mem v, h, e, ε, ε0 => by
      change mem (tvRaw e ε0 ((v 0).toEmpty _)) (tvRaw e ε0 ((v 1).toEmpty _)) ↔
        mem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.nrel Language.Set.Rel.eq v, h, e, ε, ε0 => by
      change ¬ tvRaw e ε0 ((v 0).toEmpty _) = tvRaw e ε0 ((v 1).toEmpty _) ↔
        ¬ tvRaw e ε (v 0) = tvRaw e ε (v 1)
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.nrel Language.Set.Rel.mem v, h, e, ε, ε0 => by
      change ¬ mem (tvRaw e ε0 ((v 0).toEmpty _)) (tvRaw e ε0 ((v 1).toEmpty _)) ↔
        ¬ mem (tvRaw e ε (v 0)) (tvRaw e ε (v 1))
      rw [tvRaw_toEmpty, tvRaw_toEmpty]
  | _, Semiformula.and φ ψ, h, e, ε, ε0 =>
      and_congr (evalM_toEmpty φ _ e ε ε0) (evalM_toEmpty ψ _ e ε ε0)
  | _, Semiformula.or φ ψ, h, e, ε, ε0 =>
      or_congr (evalM_toEmpty φ _ e ε ε0) (evalM_toEmpty ψ _ e ε ε0)
  | _, Semiformula.all φ, h, e, ε, ε0 =>
      forall_congr' fun d => evalM_toEmpty φ h (d :> e) ε ε0
  | _, Semiformula.exs φ, h, e, ε, ε0 =>
      exists_congr fun d => evalM_toEmpty φ h (d :> e) ε ε0

lemma evalM_allClosure_elim {V : Type*} {mem : V → V → Prop} :
    ∀ {m : ℕ} (ψ : Semiformula ℒₛₑₜ ℕ m) (ε : ℕ → V),
      evalM mem (Fin.elim0 : Fin 0 → V) ε (∀¹* ψ) →
        ∀ w : Fin m → V, evalM mem w ε ψ
  | 0, ψ, ε, h, w => by
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      rwa [hw]
  | m + 1, ψ, ε, h, w => by
      have h1 := evalM_allClosure_elim (m := m) (∀¹ ψ) ε h (fun i => w i.succ)
      have h2 := h1 (w 0)
      have hw : (w 0 :> fun i : Fin m => w i.succ) = w := by
        funext i; cases i using Fin.cases <;> rfl
      rwa [hw] at h2

lemma fixitr_fvar_aux (n m x : ℕ) :
    Rew.fixitr n m (Semiterm.fvar x : Semiterm ℒₛₑₜ ℕ n) =
      if h : x < m then Semiterm.bvar (Fin.natAdd n ⟨x, h⟩) else Semiterm.fvar (x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr n m (Semiterm.fvar x)) = _
    rw [ih]
    by_cases hx : x < m
    · have hx' : x < m + 1 := by omega
      simp only [dif_pos hx, dif_pos hx']
      rfl
    · by_cases hx' : x < m + 1
      · have he : x = m := by omega
        subst x
        simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]
        rfl
      · have he : x - m = x - (m + 1) + 1 := by omega
        simp only [dif_neg hx, dif_neg hx', he]
        rfl

lemma evalM_univCl_elim {V : Type*} {mem : V → V → Prop} (ψ : Proposition ℒₛₑₜ)
    (h : evalM mem Fin.elim0 Empty.elim (Semiformula.univCl ψ)) (ε : ℕ → V) :
    evalM mem Fin.elim0 ε ψ := by
  let m := ψ.fvSup
  let εOuter : ℕ → V := fun k => ε (k + m)
  unfold Semiformula.univCl at h
  rw [evalM_toEmpty _ _ Fin.elim0 εOuter Empty.elim] at h
  unfold Semiformula.univCl' at h
  have h1 := evalM_allClosure_elim (Rew.fixitr 0 m ▹ ψ) εOuter h (fun i => ε i.val)
  have h2 := (evalRaw_rew Eq mem (fun i : Fin (0 + m) => ε i.val) εOuter (Rew.fixitr 0 m) ψ).mp h1
  refine (evalRaw_congr Eq mem ψ (Subsingleton.elim _ _) ?_).mp h2
  funext x
  rw [fixitr_fvar_aux 0 m x]
  by_cases hx : x < m
  · simp only [dif_pos hx, tvRaw, Fin.natAdd]
    simp
  · simp only [dif_neg hx, tvRaw, εOuter]
    congr 1
    omega

/- ## Section 2: Arbitrary Model of ZFC Toolkit -/

structure ZFCModel where
  V : Type 1
  mem : V → V → Prop
  sat : ∀ ψ ∈ 𝗭𝗙𝗖, evalM mem Fin.elim0 Empty.elim ψ

section WithModel

variable (M0 : ZFCModel)

def mEv {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence n) : Prop :=
  evalM M0.mem e Empty.elim φ

lemma mEv_top {n : ℕ} (e : Fin n → M0.V) : mEv M0 e (⊤ : SetTheorySemisentence n) ↔ True := Iff.rfl
lemma mEv_bot {n : ℕ} (e : Fin n → M0.V) : mEv M0 e (⊥ : SetTheorySemisentence n) ↔ False := Iff.rfl
lemma mEv_eq {n : ℕ} (e : Fin n → M0.V) (t₁ t₂ : Semiterm ℒₛₑₜ Empty n) :
    mEv M0 e (op(=).operator ![t₁, t₂]) ↔ tvRaw e Empty.elim t₁ = tvRaw e Empty.elim t₂ := Iff.rfl
lemma mEv_mem {n : ℕ} (e : Fin n → M0.V) (t₁ t₂ : Semiterm ℒₛₑₜ Empty n) :
    mEv M0 e (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔
      M0.mem (tvRaw e Empty.elim t₁) (tvRaw e Empty.elim t₂) := Iff.rfl
lemma mEv_not {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence n) :
    mEv M0 e (∼φ) ↔ ¬ mEv M0 e φ := evalM_not e Empty.elim φ
lemma mEv_and {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ ⋏ ψ) ↔ mEv M0 e φ ∧ mEv M0 e ψ := Iff.rfl
lemma mEv_or {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ ⋎ ψ) ↔ mEv M0 e φ ∨ mEv M0 e ψ := Iff.rfl
lemma mEv_imp {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ 🡒 ψ) ↔ (mEv M0 e φ → mEv M0 e ψ) := evalM_imp e Empty.elim φ ψ
lemma mEv_iff {n : ℕ} (e : Fin n → M0.V) (φ ψ : SetTheorySemisentence n) :
    mEv M0 e (φ 🡘 ψ) ↔ (mEv M0 e φ ↔ mEv M0 e ψ) := evalM_iff e Empty.elim φ ψ
lemma mEv_all {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (∀¹ φ) ↔ ∀ d : M0.V, mEv M0 (d :> e) φ := Iff.rfl
lemma mEv_exs {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (∃¹ φ) ↔ ∃ d : M0.V, mEv M0 (d :> e) φ := Iff.rfl
lemma mEv_ballMem {n : ℕ} (e : Fin n → M0.V) (t : Semiterm ℒₛₑₜ Empty n)
    (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (Semiformula.ballMem t φ) ↔
      ∀ d : M0.V, M0.mem d (tvRaw e Empty.elim t) → mEv M0 (d :> e) φ :=
  evalM_ballMem e Empty.elim t φ
lemma mEv_bexsMem {n : ℕ} (e : Fin n → M0.V) (t : Semiterm ℒₛₑₜ Empty n)
    (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (Semiformula.bexsMem t φ) ↔
      ∃ d : M0.V, M0.mem d (tvRaw e Empty.elim t) ∧ mEv M0 (d :> e) φ :=
  evalM_bexsMem e Empty.elim t φ
lemma mEv_subst {n₁ n₂ : ℕ} (e : Fin n₂ → M0.V) (v : Fin n₁ → Semiterm ℒₛₑₜ Empty n₂)
    (φ : SetTheorySemisentence n₁) :
    mEv M0 e (φ ⇜ v) ↔ mEv M0 (fun i => tvRaw e Empty.elim (v i)) φ :=
  evalM_subst e Empty.elim v φ
lemma mEv_existsUnique {n : ℕ} (e : Fin n → M0.V) (φ : SetTheorySemisentence (n + 1)) :
    mEv M0 e (∃¹! φ) ↔ ∃! y : M0.V, mEv M0 (y :> e) φ :=
  evalM_existsUnique e Empty.elim φ

lemma extV {x y : M0.V} (h : ∀ z : M0.V, M0.mem z x ↔ M0.mem z y) : x = y := by
  have hax : mEv M0 Fin.elim0 Axiom.extentionality :=
    M0.sat Axiom.extentionality (Or.inl ZermeloFraenkel.axiom_of_extentionality)
  unfold Axiom.extentionality at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_all] at h1
  have h2 := h1 y
  rw [mEv_iff, mEv_eq, mEv_all] at h2
  refine h2.mpr fun z => ?_
  rw [mEv_iff, mEv_mem, mEv_mem]
  exact h z

lemma exists_emptyV : ∃ e : M0.V, ∀ y : M0.V, ¬ M0.mem y e := by
  have hax : mEv M0 Fin.elim0 Axiom.empty :=
    M0.sat Axiom.empty (Or.inl ZermeloFraenkel.axiom_of_empty_set)
  unfold Axiom.empty at hax
  rw [mEv_exs] at hax
  obtain ⟨e, he⟩ := hax
  rw [mEv_all] at he
  refine ⟨e, fun y => ?_⟩
  have hy := he y
  rw [mEv_not, mEv_mem] at hy
  exact hy

noncomputable def emptyV : M0.V := (exists_emptyV M0).choose

lemma not_mem_emptyV (y : M0.V) : ¬ M0.mem y (emptyV M0) :=
  (exists_emptyV M0).choose_spec y

lemma exists_doubletonV (x y : M0.V) :
    ∃ p : M0.V, ∀ z : M0.V, M0.mem z p ↔ z = x ∨ z = y := by
  have hax : mEv M0 Fin.elim0 Axiom.pairing :=
    M0.sat Axiom.pairing (Or.inl ZermeloFraenkel.axiom_of_pairing)
  unfold Axiom.pairing at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_all] at h1
  have h2 := h1 y
  rw [mEv_exs] at h2
  obtain ⟨p, hp⟩ := h2
  rw [mEv_all] at hp
  refine ⟨p, fun z => ?_⟩
  have hz := hp z
  rw [mEv_iff, mEv_mem, mEv_or, mEv_eq, mEv_eq] at hz
  exact hz

noncomputable def doubletonV (x y : M0.V) : M0.V := (exists_doubletonV M0 x y).choose

lemma mem_doubletonV {z x y : M0.V} :
    M0.mem z (doubletonV M0 x y) ↔ z = x ∨ z = y :=
  (exists_doubletonV M0 x y).choose_spec z

noncomputable def singletonV (x : M0.V) : M0.V := doubletonV M0 x x

lemma mem_singletonV {z x : M0.V} :
    M0.mem z (singletonV M0 x) ↔ z = x := by
  unfold singletonV
  rw [mem_doubletonV, or_self]

lemma exists_sUnionV (x : M0.V) :
    ∃ u : M0.V, ∀ z : M0.V, M0.mem z u ↔ ∃ w : M0.V, M0.mem w x ∧ M0.mem z w := by
  have hax : mEv M0 Fin.elim0 Axiom.union :=
    M0.sat Axiom.union (Or.inl ZermeloFraenkel.axiom_of_union)
  unfold Axiom.union at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_exs] at h1
  obtain ⟨u, hu⟩ := h1
  rw [mEv_all] at hu
  refine ⟨u, fun z => ?_⟩
  have hz := hu z
  rw [mEv_iff, mEv_mem, mEv_bexsMem] at hz
  exact hz

noncomputable def sUnionV (x : M0.V) : M0.V := (exists_sUnionV M0 x).choose

lemma mem_sUnionV {z x : M0.V} :
    M0.mem z (sUnionV M0 x) ↔ ∃ w : M0.V, M0.mem w x ∧ M0.mem z w :=
  (exists_sUnionV M0 x).choose_spec z

noncomputable def unionV (x y : M0.V) : M0.V := sUnionV M0 (doubletonV M0 x y)

lemma mem_unionV {z x y : M0.V} :
    M0.mem z (unionV M0 x y) ↔ M0.mem z x ∨ M0.mem z y := by
  unfold unionV
  rw [mem_sUnionV]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases (mem_doubletonV M0).mp hw with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨x, (mem_doubletonV M0).mpr (Or.inl rfl), hz⟩
    · exact ⟨y, (mem_doubletonV M0).mpr (Or.inr rfl), hz⟩

noncomputable def insertV (x y : M0.V) : M0.V := unionV M0 (singletonV M0 x) y

lemma mem_insertV {z x y : M0.V} :
    M0.mem z (insertV M0 x y) ↔ z = x ∨ M0.mem z y := by
  unfold insertV
  rw [mem_unionV, mem_singletonV]

lemma sUnionV_singletonV (x : M0.V) : sUnionV M0 (singletonV M0 x) = x := by
  apply extV M0
  intro z
  rw [mem_sUnionV]
  constructor
  · rintro ⟨w, hw, hz⟩
    rwa [(mem_singletonV M0).mp hw] at hz
  · intro hz
    exact ⟨x, (mem_singletonV M0).mpr rfl, hz⟩

lemma exists_powersetV (x : M0.V) :
    ∃ P : M0.V, ∀ z : M0.V, M0.mem z P ↔ ∀ w : M0.V, M0.mem w z → M0.mem w x := by
  have hax : mEv M0 Fin.elim0 Axiom.power :=
    M0.sat Axiom.power (Or.inl ZermeloFraenkel.axiom_of_power_set)
  unfold Axiom.power at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_exs] at h1
  obtain ⟨P, hP⟩ := h1
  rw [mEv_all] at hP
  refine ⟨P, fun z => ?_⟩
  have hz := hP z
  rw [mEv_iff, mEv_mem, mEv_subst] at hz
  refine hz.trans ?_
  unfold SetTheory.isSubsetOf
  rw [mEv_ballMem]
  rfl

noncomputable def powersetV (x : M0.V) : M0.V := (exists_powersetV M0 x).choose

lemma mem_powersetV {z x : M0.V} :
    M0.mem z (powersetV M0 x) ↔ ∀ w : M0.V, M0.mem w z → M0.mem w x :=
  (exists_powersetV M0 x).choose_spec z

lemma foundationV (x : M0.V) (hne : ∃ y : M0.V, M0.mem y x) :
    ∃ y : M0.V, M0.mem y x ∧ ∀ z : M0.V, M0.mem z x → ¬ M0.mem z y := by
  have hax : mEv M0 Fin.elim0 Axiom.foundation :=
    M0.sat Axiom.foundation (Or.inl ZermeloFraenkel.axiom_of_foundation)
  unfold Axiom.foundation at hax
  rw [mEv_all] at hax
  have h1 := hax x
  rw [mEv_imp, mEv_subst, mEv_bexsMem] at h1
  have hne' : mEv M0 ![x] SetTheory.isNonempty := hne
  have h2 := h1 (by
    unfold mEv at hne' ⊢
    refine (evalRaw_congr Eq M0.mem SetTheory.isNonempty ?_ rfl).mpr hne'
    funext i; fin_cases i; rfl)
  obtain ⟨y, hyx, hymin⟩ := h2
  rw [mEv_ballMem] at hymin
  refine ⟨y, hyx, fun z hzx => ?_⟩
  have hz := hymin z hzx
  rw [mEv_not, mEv_mem] at hz
  exact hz

lemma irreflV (x : M0.V) : ¬ M0.mem x x := by
  intro hxx
  obtain ⟨y, hy, hmin⟩ := foundationV M0 (singletonV M0 x) ⟨x, (mem_singletonV M0).mpr rfl⟩
  have hyx : y = x := (mem_singletonV M0).mp hy
  subst y
  exact hmin x ((mem_singletonV M0).mpr rfl) hxx

lemma asymmV {x y : M0.V} (hxy : M0.mem x y) (hyx : M0.mem y x) : False := by
  obtain ⟨u, hu, hmin⟩ := foundationV M0 (doubletonV M0 x y) ⟨x, (mem_doubletonV M0).mpr (Or.inl rfl)⟩
  rcases (mem_doubletonV M0).mp hu with rfl | rfl
  · exact hmin y ((mem_doubletonV M0).mpr (Or.inr rfl)) hyx
  · exact hmin x ((mem_doubletonV M0).mpr (Or.inl rfl)) hxy

lemma succV_inj {a b : M0.V} (h : insertV M0 a a = insertV M0 b b) : a = b := by
  by_contra hne
  have ha : M0.mem a (insertV M0 b b) := h ▸ (mem_insertV M0).mpr (Or.inl rfl)
  have hb : M0.mem b (insertV M0 a a) := h.symm ▸ (mem_insertV M0).mpr (Or.inl rfl)
  have hab : M0.mem a b := ((mem_insertV M0).mp ha).resolve_left hne
  have hba : M0.mem b a := ((mem_insertV M0).mp hb).resolve_left (Ne.symm hne)
  exact asymmV M0 hab hba

lemma sepV (X : M0.V) (φ : SetTheorySemiproposition 1) (ε : ℕ → M0.V) :
    ∃ Y : M0.V, ∀ z : M0.V, M0.mem z Y ↔ M0.mem z X ∧ evalM M0.mem ![z] ε φ := by
  have hax := M0.sat (Axiom.separationSchema φ) (Or.inl (ZermeloFraenkel.axiom_of_separation φ))
  have hinst := evalM_univCl_elim _ hax ε
  rw [evalM_all] at hinst
  have h1 := hinst X
  rw [evalM_exs] at h1
  obtain ⟨Y, hY⟩ := h1
  rw [evalM_all] at hY
  refine ⟨Y, fun z => ?_⟩
  have hz := hY z
  rw [evalM_iff, evalM_mem, evalM_and, evalM_mem, evalM_subst] at hz
  refine hz.trans (and_congr Iff.rfl ?_)
  refine evalRaw_congr Eq M0.mem φ ?_ rfl
  funext i; fin_cases i; rfl

lemma exists_sInterV (x : M0.V) :
    ∃ u : M0.V, ∀ z : M0.V, M0.mem z u ↔ (∃ y : M0.V, M0.mem y x) ∧ ∀ y : M0.V, M0.mem y x → M0.mem z y := by
  by_cases hne : ∃ w₀ : M0.V, M0.mem w₀ x
  · obtain ⟨w₀, hw₀⟩ := hne
    let φ : SetTheorySemiproposition 1 :=
      Semiformula.ballMem (&0) (Semiformula.rel Language.Set.Rel.mem ![#1, #0])
    obtain ⟨Y, hY⟩ := sepV M0 w₀ φ (fun _ => x)
    refine ⟨Y, fun z => ?_⟩
    rw [hY z]
    have hφ : evalM M0.mem ![z] (fun _ => x) φ ↔ ∀ y : M0.V, M0.mem y x → M0.mem z y := by
      dsimp only [φ]
      rw [evalM_ballMem]
      rfl
    rw [hφ]
    exact ⟨fun ⟨_, hall⟩ => ⟨⟨w₀, hw₀⟩, hall⟩, fun ⟨_, hall⟩ => ⟨hall w₀ hw₀, hall⟩⟩
  · refine ⟨emptyV M0, fun z => ?_⟩
    simp only [not_mem_emptyV, hne, false_and]

noncomputable def sInterV (x : M0.V) : M0.V := (exists_sInterV M0 x).choose

lemma mem_sInterV {z x : M0.V} :
    M0.mem z (sInterV M0 x) ↔ (∃ y : M0.V, M0.mem y x) ∧ ∀ y : M0.V, M0.mem y x → M0.mem z y :=
  (exists_sInterV M0 x).choose_spec z

noncomputable def kpairV (a b : M0.V) : M0.V :=
  doubletonV M0 (singletonV M0 a) (doubletonV M0 a b)

lemma kpairV_inj {a b c d : M0.V} (h : kpairV M0 a b = kpairV M0 c d) : a = c ∧ b = d := by
  have hc_mem : M0.mem (singletonV M0 c) (kpairV M0 a b) :=
    h ▸ (mem_doubletonV M0).mpr (Or.inl rfl)
  have hac : a = c := by
    have ha_mem : M0.mem (singletonV M0 a) (kpairV M0 c d) :=
      h ▸ (mem_doubletonV M0).mpr (Or.inl rfl)
    rcases (mem_doubletonV M0).mp ha_mem with h1 | h1
    · have : M0.mem c (singletonV M0 a) := h1 ▸ (mem_singletonV M0).mpr rfl
      exact ((mem_singletonV M0).mp this).symm
    · have : M0.mem c (singletonV M0 a) := h1 ▸ (mem_doubletonV M0).mpr (Or.inl rfl)
      exact ((mem_singletonV M0).mp this).symm
  subst hac
  refine ⟨rfl, ?_⟩
  by_cases hab : a = b
  · subst hab
    have hd_mem : M0.mem (doubletonV M0 a d) (kpairV M0 a a) :=
      h ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    have hdaa : doubletonV M0 a d = singletonV M0 a := by
      rcases (mem_doubletonV M0).mp hd_mem with h1 | h1
      · exact h1
      · exact h1
    have : M0.mem d (singletonV M0 a) := hdaa ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    exact ((mem_singletonV M0).mp this).symm
  · have hne : doubletonV M0 a b ≠ singletonV M0 a := by
      intro heq
      have : M0.mem b (singletonV M0 a) := heq ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
      exact hab ((mem_singletonV M0).mp this).symm
    have hab_mem : M0.mem (doubletonV M0 a b) (kpairV M0 a d) :=
      h ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    have heq : doubletonV M0 a b = doubletonV M0 a d :=
      ((mem_doubletonV M0).mp hab_mem).resolve_left hne
    have : M0.mem b (doubletonV M0 a d) := heq ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
    exact ((mem_doubletonV M0).mp this).resolve_left (Ne.symm hab)

lemma sInterV_kpairV (a b : M0.V) : sInterV M0 (kpairV M0 a b) = singletonV M0 a := by
  apply extV M0
  intro z
  rw [mem_sInterV, mem_singletonV]
  constructor
  · rintro ⟨_, hall⟩
    exact (mem_singletonV M0).mp (hall (singletonV M0 a) ((mem_doubletonV M0).mpr (Or.inl rfl)))
  · rintro rfl
    refine ⟨⟨singletonV M0 z, (mem_doubletonV M0).mpr (Or.inl rfl)⟩, fun y hy => ?_⟩
    rcases (mem_doubletonV M0).mp hy with rfl | rfl
    · exact (mem_singletonV M0).mpr rfl
    · exact (mem_doubletonV M0).mpr (Or.inl rfl)

lemma sUnionV_kpairV (a b : M0.V) : sUnionV M0 (kpairV M0 a b) = doubletonV M0 a b := by
  apply extV M0
  intro z
  rw [mem_sUnionV, mem_doubletonV]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases (mem_doubletonV M0).mp hw with rfl | rfl
    · exact Or.inl ((mem_singletonV M0).mp hz)
    · exact (mem_doubletonV M0).mp hz
  · rintro (rfl | rfl)
    · exact ⟨singletonV M0 z, (mem_doubletonV M0).mpr (Or.inl rfl), (mem_singletonV M0).mpr rfl⟩
    · exact ⟨doubletonV M0 a z, (mem_doubletonV M0).mpr (Or.inr rfl), (mem_doubletonV M0).mpr (Or.inr rfl)⟩

noncomputable def pi1V (w : M0.V) : M0.V := sUnionV M0 (sInterV M0 w)

lemma pi1V_kpairV (a b : M0.V) : pi1V M0 (kpairV M0 a b) = a := by
  unfold pi1V
  rw [sInterV_kpairV, sUnionV_singletonV]

lemma exists_pi2SepV (w : M0.V) :
    ∃ s : M0.V, ∀ z : M0.V, M0.mem z s ↔
      M0.mem z (sUnionV M0 w) ∧ (M0.mem z (sInterV M0 w) → sUnionV M0 w = sInterV M0 w) := by
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.rel Language.Set.Rel.mem ![#0, &0] 🡒
      Semiformula.rel Language.Set.Rel.eq ![&1, &0]
  let ε : ℕ → M0.V := fun k => if k = 0 then sInterV M0 w else sUnionV M0 w
  obtain ⟨s, hs⟩ := sepV M0 (sUnionV M0 w) φ ε
  refine ⟨s, fun z => ?_⟩
  rw [hs z]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_imp]
  rfl

noncomputable def pi2SepV (w : M0.V) : M0.V := (exists_pi2SepV M0 w).choose

lemma mem_pi2SepV {z w : M0.V} :
    M0.mem z (pi2SepV M0 w) ↔
      M0.mem z (sUnionV M0 w) ∧ (M0.mem z (sInterV M0 w) → sUnionV M0 w = sInterV M0 w) :=
  (exists_pi2SepV M0 w).choose_spec z

noncomputable def pi2V (w : M0.V) : M0.V := sUnionV M0 (pi2SepV M0 w)

lemma pi2V_kpairV (a b : M0.V) : pi2V M0 (kpairV M0 a b) = b := by
  unfold pi2V
  have hsep : pi2SepV M0 (kpairV M0 a b) = singletonV M0 b := by
    apply extV M0
    intro z
    rw [mem_pi2SepV, sUnionV_kpairV, sInterV_kpairV, mem_doubletonV, mem_singletonV, mem_singletonV]
    by_cases hab : a = b
    · subst hab
      have hdd : doubletonV M0 a a = singletonV M0 a := rfl
      simp [hdd]
    · have hne : doubletonV M0 a b ≠ singletonV M0 a := by
        intro heq
        have : M0.mem b (singletonV M0 a) := heq ▸ (mem_doubletonV M0).mpr (Or.inr rfl)
        exact hab ((mem_singletonV M0).mp this).symm
      constructor
      · rintro ⟨rfl | rfl, h2⟩
        · exact (hne (h2 rfl)).elim
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, fun hba => (hab hba.symm).elim⟩
  rw [hsep, sUnionV_singletonV]

/- ## Section 3: Basic `mEv` Evaluations & Remaining ZFC Set Constructors -/

lemma mEv_e0 (e1 e2 : Fin 0 → M0.V) (φ : SetTheorySemisentence 0) :
    mEv M0 e1 φ ↔ mEv M0 e2 φ := by
  rw [Subsingleton.elim e1 e2]

lemma mEv_e1 (y : M0.V) (e : Fin 0 → M0.V) (φ : SetTheorySemisentence 1) :
    mEv M0 (y :> e) φ ↔ mEv M0 ![y] φ := by
  rw [Subsingleton.elim e ![]]

lemma mEv_congr {n : ℕ} {e₁ e₂ : Fin n → M0.V} (φ : SetTheorySemisentence n) (he : e₁ = e₂) :
    mEv M0 e₁ φ ↔ mEv M0 e₂ φ := by
  subst he; rfl

lemma mEv_subst1 {m : ℕ} (e : Fin m → M0.V) (φ : SetTheorySemisentence 1) (i₀ : Fin m) :
    mEv M0 e (φ ⇜ ![#i₀]) ↔ mEv M0 ![e i₀] φ := by
  rw [mEv_subst]
  refine mEv_congr M0 φ ?_
  funext k; fin_cases k; rfl

lemma mEv_subst2 {m : ℕ} (e : Fin m → M0.V) (φ : SetTheorySemisentence 2) (i₀ i₁ : Fin m) :
    mEv M0 e (φ ⇜ ![#i₀, #i₁]) ↔ mEv M0 ![e i₀, e i₁] φ := by
  rw [mEv_subst]
  refine mEv_congr M0 φ ?_
  funext k; fin_cases k <;> rfl

lemma mEv_subst3 {m : ℕ} (e : Fin m → M0.V) (φ : SetTheorySemisentence 3) (i₀ i₁ i₂ : Fin m) :
    mEv M0 e (φ ⇜ ![#i₀, #i₁, #i₂]) ↔ mEv M0 ![e i₀, e i₁, e i₂] φ := by
  rw [mEv_subst]
  refine mEv_congr M0 φ ?_
  funext k; fin_cases k <;> rfl

lemma ev_isEmpty (x : M0.V) : mEv M0 ![x] SetTheory.isEmpty ↔ x = emptyV M0 := by
  unfold SetTheory.isEmpty
  rw [mEv_all]
  constructor
  · intro h
    apply extV M0
    intro z
    have hz := h z
    rw [mEv_not, mEv_mem] at hz
    exact ⟨fun hzx => (hz hzx).elim, fun hze => (not_mem_emptyV M0 z hze).elim⟩
  · rintro rfl y
    rw [mEv_not, mEv_mem]
    exact not_mem_emptyV M0 y

lemma ev_isNonempty (x : M0.V) : mEv M0 ![x] SetTheory.isNonempty ↔ ∃ y : M0.V, M0.mem y x := Iff.rfl

lemma ev_isSubsetOf (x y : M0.V) :
    mEv M0 ![x, y] SetTheory.isSubsetOf ↔ ∀ z : M0.V, M0.mem z x → M0.mem z y := by
  unfold SetTheory.isSubsetOf
  rw [mEv_ballMem]
  rfl

lemma ev_doubleton (p x y : M0.V) :
    mEv M0 ![p, x, y] SetTheory.doubleton.dfn ↔ p = doubletonV M0 x y := by
  unfold SetTheory.doubleton.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z p ↔ z = x ∨ z = y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_or, mEv_eq, mEv_eq]
    rfl
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_doubletonV]
    · rintro rfl z
      rw [mem_doubletonV]

lemma ev_singleton (p x : M0.V) :
    mEv M0 ![p, x] SetTheory.singleton.dfn ↔ p = singletonV M0 x := by
  unfold SetTheory.singleton.dfn
  exact (mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 p x x)

lemma ev_sUnion (u x : M0.V) :
    mEv M0 ![u, x] SetTheory.sUnion.dfn ↔ u = sUnionV M0 x := by
  unfold SetTheory.sUnion.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z u ↔ ∃ w : M0.V, M0.mem w x ∧ M0.mem z w).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_bexsMem]
    rfl
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_sUnionV]
    · rintro rfl z
      rw [mem_sUnionV]

lemma ev_union (u x y : M0.V) :
    mEv M0 ![u, x, y] SetTheory.union.dfn ↔ u = unionV M0 x y := by
  unfold SetTheory.union.dfn unionV
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d : M0.V, d = doubletonV M0 x y → u = sUnionV M0 d).trans
    ⟨fun h => h (doubletonV M0 x y) rfl, fun h d hd => hd ▸ h⟩
  refine forall_congr' fun d => ?_
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 d x y))
    ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 u d))

lemma ev_insert (u x y : M0.V) :
    mEv M0 ![u, x, y] SetTheory.insert.dfn ↔ u = insertV M0 x y := by
  unfold SetTheory.insert.dfn insertV
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ s : M0.V, s = singletonV M0 x → u = unionV M0 s y).trans
    ⟨fun h => h (singletonV M0 x) rfl, fun h s hs => hs ▸ h⟩
  refine forall_congr' fun s => ?_
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst2 M0 _ _ _ _).trans (ev_singleton M0 s x))
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_union M0 u s y))

lemma ev_sInter (u x : M0.V) :
    mEv M0 ![u, x] SetTheory.sInter.dfn ↔ u = sInterV M0 x := by
  unfold SetTheory.sInter.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V,
      M0.mem z u ↔ (∃ y : M0.V, M0.mem y x) ∧ ∀ y : M0.V, M0.mem y x → M0.mem z y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_and, mEv_ballMem]
    exact iff_congr Iff.rfl (and_congr ((mEv_subst1 M0 _ _ _).trans (ev_isNonempty M0 x)) Iff.rfl)
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_sInterV]
    · rintro rfl z
      rw [mem_sInterV]

lemma ev_kpair (k x y : M0.V) :
    mEv M0 ![k, x, y] SetTheory.kpair.dfn ↔ k = kpairV M0 x y := by
  unfold SetTheory.kpair.dfn kpairV
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ x' : M0.V, x' = singletonV M0 x →
      ∀ z : M0.V, z = doubletonV M0 x y → k = doubletonV M0 x' z).trans
    ⟨fun h => h (singletonV M0 x) rfl (doubletonV M0 x y) rfl,
     fun h x' hx' z hz => by subst hx' hz; exact h⟩
  refine forall_congr' fun x' => ?_
  rw [mEv_imp, mEv_all]
  refine imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_singleton M0 x' x)) (forall_congr' fun z => ?_)
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 z x y))
    ((mEv_subst3 M0 _ _ _ _ _).trans (ev_doubleton M0 k x' z))

lemma ev_pi1 (p w : M0.V) :
    mEv M0 ![p, w] SetTheory.kpair.π₁.dfn ↔ p = pi1V M0 w := by
  unfold SetTheory.kpair.π₁.dfn pi1V
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ i : M0.V, i = sInterV M0 w → p = sUnionV M0 i).trans
    ⟨fun h => h (sInterV M0 w) rfl, fun h i hi => hi ▸ h⟩
  refine forall_congr' fun i => ?_
  rw [mEv_imp]
  exact imp_congr
    ((mEv_subst2 M0 _ _ _ _).trans (ev_sInter M0 i w))
    ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 p i))

lemma ev_pi2 (p w : M0.V) :
    mEv M0 ![p, w] SetTheory.kpair.π₂.dfn ↔ p = pi2V M0 w := by
  unfold SetTheory.kpair.π₂.dfn pi2V
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ u : M0.V, u = sUnionV M0 w → ∀ i : M0.V, i = sInterV M0 w →
      ∀ s : M0.V, (∀ z : M0.V, M0.mem z s ↔ M0.mem z u ∧ (M0.mem z i → u = i)) →
        p = sUnionV M0 s).trans ?_
  · refine forall_congr' fun u => ?_
    rw [mEv_imp, mEv_all]
    refine imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 u w)) (forall_congr' fun i => ?_)
    rw [mEv_imp, mEv_all]
    refine imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_sInter M0 i w)) (forall_congr' fun s => ?_)
    rw [mEv_imp, mEv_all]
    refine imp_congr (forall_congr' fun z => ?_) ((mEv_subst2 M0 _ _ _ _).trans (ev_sUnion M0 p s))
    rw [mEv_iff, mEv_mem, mEv_and, mEv_mem, mEv_imp, mEv_mem, mEv_eq]
    rfl
  · constructor
    · intro h
      exact h (sUnionV M0 w) rfl (sInterV M0 w) rfl (pi2SepV M0 w) (fun z => mem_pi2SepV M0)
    · intro hp u hu i hi s hs
      subst hu hi
      have hseq : s = pi2SepV M0 w := extV M0 fun z => (hs z).trans (mem_pi2SepV M0).symm
      rw [hseq, hp]

lemma ev_succ (y x : M0.V) :
    mEv M0 ![y, x] SetTheory.succ.dfn ↔ y = insertV M0 x x := by
  unfold SetTheory.succ.dfn SetTheory.isSucc
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z y ↔ z = x ∨ M0.mem z x).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_or, mEv_eq, mEv_mem]
    rfl
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_insertV]
    · rintro rfl z
      rw [mem_insertV]

lemma ev_IsInductive (I : M0.V) :
    mEv M0 ![I] SetTheory.IsInductive.dfn ↔
      (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) := by
  unfold SetTheory.IsInductive.dfn
  rw [mEv_and, mEv_all, mEv_ballMem]
  refine and_congr ?_ ?_
  · refine (?_ : _ ↔ ∀ e : M0.V, e = emptyV M0 → M0.mem e I).trans
      ⟨fun h => h (emptyV M0) rfl, fun h e he => he.symm ▸ h⟩
    refine forall_congr' fun e => ?_
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst1 M0 _ _ _).trans (ev_isEmpty M0 e)) Iff.rfl
  · refine forall₂_congr fun y _ => ?_
    rw [mEv_all]
    refine (?_ : _ ↔ ∀ y' : M0.V, y' = insertV M0 y y → M0.mem y' I).trans
      ⟨fun h => h (insertV M0 y y) rfl, fun h y' hy' => hy'.symm ▸ h⟩
    refine forall_congr' fun y' => ?_
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst2 M0 _ _ _ _).trans (ev_succ M0 y' y)) Iff.rfl

/- Product, Von Neumann numerals, `vnOmegaV`, `relRangeV`, `funsV`, `zfcAppV` -/

lemma exists_prodV (X Y : M0.V) :
    ∃ P : M0.V, ∀ z : M0.V, M0.mem z P ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y := by
  let ambient := powersetV M0 (powersetV M0 (unionV M0 X Y))
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&0)
      (Semiformula.bexsMem (&1)
        (Rew.subst ![#2, #1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn))
  let ε : ℕ → M0.V := fun k => if k = 0 then X else Y
  obtain ⟨P, hP⟩ := sepV M0 ambient φ ε
  refine ⟨P, fun z => ?_⟩
  rw [hP z]
  have hφ : evalM M0.mem ![z] ε φ ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y := by
    dsimp only [φ]
    rw [evalM_bexsMem]
    refine exists_congr fun x => and_congr Iff.rfl ?_
    rw [evalM_bexsMem]
    refine exists_congr fun y => and_congr Iff.rfl ?_
    change evalM M0.mem (y :> x :> z :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#2, #1, #0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 z x y)
    funext i; fin_cases i <;> rfl
  rw [hφ]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨x, hx, y, hy, rfl⟩
  rw [mem_powersetV]
  intro w hw
  rw [mem_powersetV]
  intro u hu
  rw [mem_unionV]
  rcases (mem_doubletonV M0).mp hw with rfl | rfl
  · rw [(mem_singletonV M0).mp hu]; exact Or.inl hx
  · rcases (mem_doubletonV M0).mp hu with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hy

noncomputable def prodV (X Y : M0.V) : M0.V := (exists_prodV M0 X Y).choose

lemma mem_prodV {z X Y : M0.V} :
    M0.mem z (prodV M0 X Y) ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y :=
  (exists_prodV M0 X Y).choose_spec z

lemma kpairV_mem_prodV {x y X Y : M0.V} :
    M0.mem (kpairV M0 x y) (prodV M0 X Y) ↔ M0.mem x X ∧ M0.mem y Y := by
  rw [mem_prodV]
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩

lemma ev_prod (p X Y : M0.V) :
    mEv M0 ![p, X, Y] SetTheory.prod.dfn ↔ p = prodV M0 X Y := by
  unfold SetTheory.prod.dfn
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z p ↔
      ∃ x : M0.V, M0.mem x X ∧ ∃ y : M0.V, M0.mem y Y ∧ z = kpairV M0 x y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff, mEv_mem, mEv_bexsMem]
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ => ?_)
    rw [mEv_bexsMem]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (mEv_subst3 M0 _ _ _ _ _).trans (ev_kpair M0 z x y)
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_prodV]
    · rintro rfl z
      rw [mem_prodV]

noncomputable def vnNatV : ℕ → M0.V
  | 0 => emptyV M0
  | k + 1 => insertV M0 (vnNatV k) (vnNatV k)

lemma mem_vnNatV_iff {x : M0.V} {m : ℕ} :
    M0.mem x (vnNatV M0 m) ↔ ∃ k < m, x = vnNatV M0 k := by
  induction m with
  | zero =>
    simp [vnNatV, not_mem_emptyV]
  | succ m ih =>
    simp only [vnNatV, mem_insertV, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hlt, rfl⟩

lemma vnNatV_lt_mem {a b : ℕ} (h : a < b) : M0.mem (vnNatV M0 a) (vnNatV M0 b) :=
  (mem_vnNatV_iff M0).mpr ⟨a, h, rfl⟩

lemma vnNatV_inj : Function.Injective (vnNatV M0) := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm := vnNatV_lt_mem M0 hlt
    rw [← hab] at hm
    exact (irreflV M0 _ hm).elim
  · rfl
  · have hm := vnNatV_lt_mem M0 hgt
    rw [hab] at hm
    exact (irreflV M0 _ hm).elim

lemma exists_inductiveV :
    ∃ I : M0.V, M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I := by
  have hax : mEv M0 Fin.elim0 Axiom.infinity :=
    M0.sat Axiom.infinity (Or.inl ZermeloFraenkel.axiom_of_infinity)
  unfold Axiom.infinity at hax
  rw [mEv_exs] at hax
  obtain ⟨I, hI⟩ := hax
  refine ⟨I, (ev_IsInductive M0 I).mp ?_⟩
  exact (mEv_congr M0 SetTheory.IsInductive.dfn (by funext i; fin_cases i; rfl)).mp hI

lemma exists_vnOmegaV :
    ∃ ω : M0.V, ∀ x : M0.V, M0.mem x ω ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I := by
  obtain ⟨I₀, hI₀⟩ := exists_inductiveV M0
  let φ : SetTheorySemiproposition 1 :=
    Rewriting.emb “x. ∀ I, !SetTheory.IsInductive.dfn I → x ∈ I”
  obtain ⟨ω, hω⟩ := sepV M0 I₀ φ (fun _ => emptyV M0)
  refine ⟨ω, fun x => ?_⟩
  rw [hω x]
  have hφ : evalM M0.mem ![x] (fun _ => emptyV M0) φ ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I := by
    dsimp only [φ]
    rw [evalM_emb]
    change mEv M0 ![x] “x. ∀ I, !SetTheory.IsInductive.dfn I → x ∈ I” ↔ _
    rw [mEv_all]
    refine forall_congr' fun I => ?_
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst1 M0 _ _ _).trans (ev_IsInductive M0 I)) Iff.rfl
  rw [hφ]
  exact ⟨And.right, fun hall => ⟨hall I₀ hI₀, hall⟩⟩

noncomputable def vnOmegaV : M0.V := (exists_vnOmegaV M0).choose

lemma mem_vnOmegaV_iff {x : M0.V} :
    M0.mem x (vnOmegaV M0) ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I :=
  (exists_vnOmegaV M0).choose_spec x

lemma vnNatV_mem_vnOmegaV (k : ℕ) : M0.mem (vnNatV M0 k) (vnOmegaV M0) := by
  rw [mem_vnOmegaV_iff]
  intro I ⟨h0, hs⟩
  induction k with
  | zero => exact h0
  | succ k ih => exact hs (vnNatV M0 k) ih

lemma exists_relRangeV (R : M0.V) :
    ∃ r : M0.V, ∀ y : M0.V, M0.mem y r ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R := by
  let ambient := sUnionV M0 (sUnionV M0 R)
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (∃¹
        ((Rew.subst ![#0, #1, #2] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
          Semiformula.rel Language.Set.Rel.mem ![#0, &0]))
  obtain ⟨r, hr⟩ := sepV M0 ambient φ (fun _ => R)
  refine ⟨r, fun y => ?_⟩
  rw [hr y]
  have hφ : evalM M0.mem ![y] (fun _ => R) φ ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R := by
    dsimp only [φ]
    rw [evalM_exs]
    refine exists_congr fun x => ?_
    rw [evalM_exs]
    constructor
    · rintro ⟨p, hp1, hp2⟩
      change evalM M0.mem (p :> x :> y :> ![]) _
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #1, #2]) at hp1
      rw [evalM_subst, evalM_emb] at hp1
      have hpeq : p = kpairV M0 x y := (ev_kpair M0 p x y).mp (by
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hp1
        funext i; fin_cases i <;> rfl)
      subst hpeq
      exact hp2
    · intro hxy
      refine ⟨kpairV M0 x y, ?_, hxy⟩
      change evalM M0.mem (kpairV M0 x y :> x :> y :> ![]) _
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #1, #2])
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ x y).mpr rfl)
      funext i; fin_cases i <;> rfl
  rw [hφ]
  refine ⟨And.right, fun ⟨x, hx⟩ => ⟨?_, x, hx⟩⟩
  rw [mem_sUnionV]
  refine ⟨doubletonV M0 x y, ?_, (mem_doubletonV M0).mpr (Or.inr rfl)⟩
  rw [mem_sUnionV]
  exact ⟨kpairV M0 x y, hx, (mem_doubletonV M0).mpr (Or.inr rfl)⟩

noncomputable def relRangeV (R : M0.V) : M0.V := (exists_relRangeV M0 R).choose

lemma mem_relRangeV {y R : M0.V} :
    M0.mem y (relRangeV M0 R) ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R :=
  (exists_relRangeV M0 R).choose_spec y

lemma exists_funsV (X Y : M0.V) :
    ∃ F : M0.V, ∀ f : M0.V, M0.mem f F ↔
      (∀ p : M0.V, M0.mem p f → M0.mem p (prodV M0 X Y)) ∧
      ∀ x : M0.V, M0.mem x X → ∃! y : M0.V, M0.mem (kpairV M0 x y) f := by
  let ambient := powersetV M0 (prodV M0 X Y)
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.ballMem (&0)
      (Semiformula.existsUnique
        (∃¹
          ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
            Semiformula.rel Language.Set.Rel.mem ![#0, #3])))
  obtain ⟨F, hF⟩ := sepV M0 ambient φ (fun _ => X)
  refine ⟨F, fun f => ?_⟩
  rw [hF f, mem_powersetV]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_ballMem]
  refine forall₂_congr fun x _ => ?_
  rw [evalM_existsUnique]
  refine existsUnique_congr fun y => ?_
  rw [evalM_exs]
  constructor
  · rintro ⟨p, hp1, hp2⟩
    change evalM M0.mem (p :> y :> x :> f :> ![]) _
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) at hp1
    rw [evalM_subst, evalM_emb] at hp1
    have hpeq : p = kpairV M0 x y := (ev_kpair M0 p x y).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hp1
      funext i; fin_cases i <;> rfl)
    subst hpeq
    exact hp2
  · intro hxy
    refine ⟨kpairV M0 x y, ?_, hxy⟩
    change evalM M0.mem (kpairV M0 x y :> y :> x :> f :> ![]) _
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1])
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ x y).mpr rfl)
    funext i; fin_cases i <;> rfl

noncomputable def funsV (X Y : M0.V) : M0.V := (exists_funsV M0 X Y).choose

lemma mem_funsV {f X Y : M0.V} :
    M0.mem f (funsV M0 X Y) ↔
      (∀ p : M0.V, M0.mem p f → M0.mem p (prodV M0 X Y)) ∧
      ∀ x : M0.V, M0.mem x X → ∃! y : M0.V, M0.mem (kpairV M0 x y) f :=
  (exists_funsV M0 X Y).choose_spec f

lemma exists_zfcAppV (f x : M0.V) :
    ∃ v : M0.V, ∀ z : M0.V, M0.mem z v ↔
      M0.mem z (sUnionV M0 (relRangeV M0 f)) ∧ ∃ y : M0.V, M0.mem z y ∧ M0.mem (kpairV M0 x y) f := by
  let ambient := sUnionV M0 (relRangeV M0 f)
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (Semiformula.rel Language.Set.Rel.mem ![#1, #0] ⋏
        (∃¹ ((Rew.subst ![#0, &1, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
            Semiformula.rel Language.Set.Rel.mem ![#0, &0])))
  let ε : ℕ → M0.V := fun k => if k = 0 then f else x
  obtain ⟨v, hv⟩ := sepV M0 ambient φ ε
  refine ⟨v, fun z => ?_⟩
  rw [hv z]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_exs]
  refine exists_congr fun y => ?_
  rw [evalM_and]
  refine and_congr Iff.rfl ?_
  rw [evalM_exs]
  constructor
  · rintro ⟨p, hp1, hp2⟩
    change evalM M0.mem (p :> y :> z :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, &1, #1]) at hp1
    rw [evalM_subst, evalM_emb] at hp1
    have hpeq : p = kpairV M0 x y := (ev_kpair M0 p x y).mp (by
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hp1
      funext i; fin_cases i <;> rfl)
    subst hpeq
    exact hp2
  · intro hxy
    refine ⟨kpairV M0 x y, ?_, hxy⟩
    change evalM M0.mem (kpairV M0 x y :> y :> z :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, &1, #1])
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ x y).mpr rfl)
    funext i; fin_cases i <;> rfl

noncomputable def zfcAppV (f x : M0.V) : M0.V := (exists_zfcAppV M0 f x).choose

lemma mem_zfcAppV {z f x : M0.V} :
    M0.mem z (zfcAppV M0 f x) ↔
      M0.mem z (sUnionV M0 (relRangeV M0 f)) ∧ ∃ y : M0.V, M0.mem z y ∧ M0.mem (kpairV M0 x y) f :=
  (exists_zfcAppV M0 f x).choose_spec z

lemma zfcAppV_of_unique {f x y : M0.V} (huniq : ∀ y' : M0.V, M0.mem (kpairV M0 x y') f ↔ y' = y) :
    zfcAppV M0 f x = y := by
  apply extV M0
  intro z
  rw [mem_zfcAppV]
  constructor
  · rintro ⟨_, y', hzy', hp⟩
    rw [(huniq y').mp hp] at hzy'
    exact hzy'
  · intro hzy
    have hmem : M0.mem (kpairV M0 x y) f := (huniq y).mpr rfl
    refine ⟨?_, y, hzy, hmem⟩
    rw [mem_sUnionV]
    exact ⟨y, (mem_relRangeV M0).mpr ⟨x, hmem⟩, hzy⟩

lemma zfcAppV_of_mem_funs {X Y f x y : M0.V}
    (hf : M0.mem f (funsV M0 X Y)) (hx : M0.mem x X) (hp : M0.mem (kpairV M0 x y) f) :
    zfcAppV M0 f x = y := by
  obtain ⟨_, huniq⟩ := (mem_funsV M0).mp hf
  obtain ⟨y0, hy0, hyeq⟩ := huniq x hx
  have hy : y = y0 := hyeq y hp
  subst hy
  exact zfcAppV_of_unique M0 fun y' => ⟨fun h => hyeq y' h, fun h => h ▸ hy0⟩

lemma zfcAppV_mem_codomain {X Y f x : M0.V}
    (hf : M0.mem f (funsV M0 X Y)) (hx : M0.mem x X) :
    M0.mem (zfcAppV M0 f x) Y := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hf
  obtain ⟨y, hy, _⟩ := huniq x hx
  rw [zfcAppV_of_mem_funs M0 hf hx hy]
  exact ((kpairV_mem_prodV M0).mp (hsub _ hy)).2

lemma funsV_ext {X Y f1 f2 : M0.V}
    (hf1 : M0.mem f1 (funsV M0 X Y)) (hf2 : M0.mem f2 (funsV M0 X Y))
    (heq : ∀ x : M0.V, M0.mem x X → zfcAppV M0 f1 x = zfcAppV M0 f2 x) : f1 = f2 := by
  obtain ⟨hsub1, huniq1⟩ := (mem_funsV M0).mp hf1
  obtain ⟨hsub2, huniq2⟩ := (mem_funsV M0).mp hf2
  apply extV M0
  intro p
  constructor
  · intro hp1
    obtain ⟨x, hx, y, _, rfl⟩ := (mem_prodV M0).mp (hsub1 p hp1)
    have ha1 := zfcAppV_of_mem_funs M0 hf1 hx hp1
    obtain ⟨y2, hy2, _⟩ := huniq2 x hx
    have ha2 := zfcAppV_of_mem_funs M0 hf2 hx hy2
    have hy : y = y2 := by rw [← ha1, heq x hx, ha2]
    rwa [hy]
  · intro hp2
    obtain ⟨x, hx, y, _, rfl⟩ := (mem_prodV M0).mp (hsub2 p hp2)
    have ha2 := zfcAppV_of_mem_funs M0 hf2 hx hp2
    obtain ⟨y1, hy1, _⟩ := huniq1 x hx
    have ha1 := zfcAppV_of_mem_funs M0 hf1 hx hy1
    have hy : y = y1 := by rw [← ha2, ← heq x hx, ha1]
    rwa [hy]

/- Encoded integers, finite lists, configurations, and tapes inside `M0` -/

noncomputable def intSetV : M0.V := prodV M0 (vnNatV M0 2) (vnOmegaV M0)

noncomputable def encodeIntV : ℤ → M0.V
  | Int.ofNat k => kpairV M0 (vnNatV M0 0) (vnNatV M0 k)
  | Int.negSucc k => kpairV M0 (vnNatV M0 1) (vnNatV M0 k)

lemma encodeIntV_mem (z : ℤ) : M0.mem (encodeIntV M0 z) (intSetV M0) := by
  unfold intSetV
  cases z with
  | ofNat k =>
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), vnNatV_mem_vnOmegaV M0 k⟩
  | negSucc k =>
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), vnNatV_mem_vnOmegaV M0 k⟩

lemma encodeIntV_inj : Function.Injective (encodeIntV M0) := by
  intro z1 z2 heq
  cases z1 <;> cases z2 <;> dsimp only [encodeIntV] at heq
  · rw [vnNatV_inj M0 (kpairV_inj M0 heq).2]
  · exact absurd (vnNatV_inj M0 (kpairV_inj M0 heq).1) (by decide)
  · exact absurd (vnNatV_inj M0 (kpairV_inj M0 heq).1) (by decide)
  · rw [vnNatV_inj M0 (kpairV_inj M0 heq).2]

noncomputable def listToV : List M0.V → M0.V
  | [] => emptyV M0
  | x :: xs => insertV M0 x (listToV xs)

lemma mem_listToV {z : M0.V} {xs : List M0.V} :
    M0.mem z (listToV M0 xs) ↔ z ∈ xs := by
  induction xs with
  | nil => simp [listToV, not_mem_emptyV]
  | cons x xs ih => simp [listToV, mem_insertV, ih]

noncomputable def cfgSetV (N : ℕ) : M0.V :=
  prodV M0 (vnNatV M0 N) (prodV M0 (intSetV M0) (funsV M0 (intSetV M0) (vnNatV M0 2)))

lemma exists_emptyTapeV :
    ∃ g : M0.V, ∀ p : M0.V, M0.mem p g ↔ ∃ u : M0.V, M0.mem u (intSetV M0) ∧ p = kpairV M0 u (vnNatV M0 0) := by
  let ambient := prodV M0 (intSetV M0) (vnNatV M0 2)
  let φ : SetTheorySemiproposition 1 :=
    ∃¹ (Rew.subst ![#1, #0, &0] ▹ Rewriting.emb SetTheory.kpair.dfn)
  obtain ⟨g, hg⟩ := sepV M0 ambient φ (fun _ => vnNatV M0 0)
  refine ⟨g, fun p => ?_⟩
  rw [hg p]
  have hφ : evalM M0.mem ![p] (fun _ => vnNatV M0 0) φ ↔ ∃ u : M0.V, p = kpairV M0 u (vnNatV M0 0) := by
    dsimp only [φ]
    rw [evalM_exs]
    refine exists_congr fun u => ?_
    change evalM M0.mem (u :> p :> ![]) _
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#1, #0, &0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p u (vnNatV M0 0))
    funext i; fin_cases i <;> rfl
  rw [hφ]
  constructor
  · rintro ⟨hp, u, rfl⟩
    exact ⟨u, ((kpairV_mem_prodV M0).mp hp).1, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(kpairV_mem_prodV M0).mpr ⟨hu, vnNatV_lt_mem M0 (by decide : 0 < 2)⟩, u, rfl⟩

noncomputable def emptyTapeV : M0.V := (exists_emptyTapeV M0).choose

lemma mem_emptyTapeV {p : M0.V} :
    M0.mem p (emptyTapeV M0) ↔ ∃ u : M0.V, M0.mem u (intSetV M0) ∧ p = kpairV M0 u (vnNatV M0 0) :=
  (exists_emptyTapeV M0).choose_spec p

lemma emptyTapeV_mem_funs : M0.mem (emptyTapeV M0) (funsV M0 (intSetV M0) (vnNatV M0 2)) := by
  rw [mem_funsV]
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := (mem_emptyTapeV M0).mp hp
    exact (kpairV_mem_prodV M0).mpr ⟨hu, vnNatV_lt_mem M0 (by decide : 0 < 2)⟩
  · intro u hu
    refine ⟨vnNatV M0 0, (mem_emptyTapeV M0).mpr ⟨u, hu, rfl⟩, fun y hy => ?_⟩
    obtain ⟨u', _, heq⟩ := (mem_emptyTapeV M0).mp hy
    exact (kpairV_inj M0 heq).2

lemma emptyTapeV_app {u : M0.V} (hu : M0.mem u (intSetV M0)) :
    zfcAppV M0 (emptyTapeV M0) u = vnNatV M0 0 :=
  zfcAppV_of_mem_funs M0 (emptyTapeV_mem_funs M0) hu ((mem_emptyTapeV M0).mpr ⟨u, hu, rfl⟩)

lemma exists_updateTapeV (g pos val : M0.V) :
    ∃ g' : M0.V, ∀ p : M0.V, M0.mem p g' ↔
      M0.mem p (prodV M0 (intSetV M0) (vnNatV M0 2)) ∧
      (p = kpairV M0 pos val ∨ (M0.mem p g ∧ ∀ v : M0.V, p ≠ kpairV M0 pos v)) := by
  let ambient := prodV M0 (intSetV M0) (vnNatV M0 2)
  let φ : SetTheorySemiproposition 1 :=
    (Rew.subst ![#0, &1, &2] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋎
      (Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏
        (∀¹ (∼(Rew.subst ![#1, &1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn))))
  let ε : ℕ → M0.V := fun k => if k = 0 then g else if k = 1 then pos else val
  obtain ⟨g', hg'⟩ := sepV M0 ambient φ ε
  refine ⟨g', fun p => ?_⟩
  rw [hg' p]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_or, evalM_and, evalM_all]
  refine or_congr ?_ (and_congr Iff.rfl (forall_congr' fun v => ?_))
  · change evalM M0.mem ![p] ε ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, &1, &2]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p pos val)
    funext i; fin_cases i <;> rfl
  · rw [evalM_not]
    refine not_congr ?_
    change evalM M0.mem (v :> p :> ![]) ε ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#1, &1, #0]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 p pos v)
    funext i; fin_cases i <;> rfl

noncomputable def updateTapeV (g pos val : M0.V) : M0.V := (exists_updateTapeV M0 g pos val).choose

lemma mem_updateTapeV {p g pos val : M0.V} :
    M0.mem p (updateTapeV M0 g pos val) ↔
      M0.mem p (prodV M0 (intSetV M0) (vnNatV M0 2)) ∧
      (p = kpairV M0 pos val ∨ (M0.mem p g ∧ ∀ v : M0.V, p ≠ kpairV M0 pos v)) :=
  (exists_updateTapeV M0 g pos val).choose_spec p

lemma updateTapeV_mem_funs {g pos val : M0.V}
    (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (hpos : M0.mem pos (intSetV M0)) (hval : M0.mem val (vnNatV M0 2)) :
    M0.mem (updateTapeV M0 g pos val) (funsV M0 (intSetV M0) (vnNatV M0 2)) := by
  obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
  rw [mem_funsV]
  refine ⟨fun p hp => ((mem_updateTapeV M0).mp hp).1, fun u hu => ?_⟩
  by_cases hup : u = pos
  · subst hup
    refine ⟨val, (mem_updateTapeV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hpos, hval⟩, Or.inl rfl⟩, ?_⟩
    intro y hy
    rcases ((mem_updateTapeV M0).mp hy).2 with heq | ⟨_, hne⟩
    · exact (kpairV_inj M0 heq).2
    · exact (hne y rfl).elim
  · obtain ⟨y0, hy0, hyeq⟩ := huniq u hu
    refine ⟨y0, ?_, ?_⟩
    · exact (mem_updateTapeV M0).mpr
        ⟨hsub _ hy0, Or.inr ⟨hy0, fun v heq => hup (kpairV_inj M0 heq).1⟩⟩
    · intro y hy
      rcases ((mem_updateTapeV M0).mp hy).2 with heq | ⟨hyg, _⟩
      · exact (hup (kpairV_inj M0 heq).1).elim
      · exact hyeq y hyg

lemma updateTapeV_app {g pos val u : M0.V}
    (hg : M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)))
    (hpos : M0.mem pos (intSetV M0)) (hval : M0.mem val (vnNatV M0 2))
    (hu : M0.mem u (intSetV M0)) :
    zfcAppV M0 (updateTapeV M0 g pos val) u =
      if u = pos then val else zfcAppV M0 g u := by
  have hf := updateTapeV_mem_funs M0 hg hpos hval
  by_cases hup : u = pos
  · subst hup
    rw [if_pos rfl]
    exact zfcAppV_of_mem_funs M0 hf hpos
      ((mem_updateTapeV M0).mpr ⟨(kpairV_mem_prodV M0).mpr ⟨hpos, hval⟩, Or.inl rfl⟩)
  · rw [if_neg hup]
    obtain ⟨hsub, huniq⟩ := (mem_funsV M0).mp hg
    obtain ⟨y0, hy0, _⟩ := huniq u hu
    have happ_g : zfcAppV M0 g u = y0 := zfcAppV_of_mem_funs M0 hg hu hy0
    rw [happ_g]
    exact zfcAppV_of_mem_funs M0 hf hu
      ((mem_updateTapeV M0).mpr
        ⟨hsub _ hy0, Or.inr ⟨hy0, fun v heq => hup (kpairV_inj M0 heq).1⟩⟩)

/- ## Section 4: `EvalTermAt` Combinators and `Constant14` Evaluations in `M0` -/

def EvalTermAt {m : ℕ} (e : Fin m → M0.V) (Ψ : SetTheorySemisentence (m + 1)) (val : M0.V) : Prop :=
  ∀ y : M0.V, mEv M0 (y :> e) Ψ ↔ y = val

def DefinesConst (Ψ : SetTheorySemisentence 1) (c : M0.V) : Prop :=
  ∀ y : M0.V, mEv M0 ![y] Ψ ↔ y = c

lemma et_bvar_succ {m : ℕ} (e : Fin m → M0.V) (i : Fin m) :
    EvalTermAt M0 e (op(=).operator (#0 :> #(i.succ) :> ![])) (e i) := by
  intro y
  change y = (y :> e) i.succ ↔ y = e i
  rfl

lemma et_bvar1 {m : ℕ} (a : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> e) (op(=).operator (#0 :> #1 :> ![])) a :=
  et_bvar_succ M0 (a :> e) 0

lemma et_bvar2 {m : ℕ} (a b : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> e) (op(=).operator (#0 :> #2 :> ![])) b :=
  et_bvar_succ M0 (a :> b :> e) 1

lemma et_bvar3 {m : ℕ} (a b c : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> e) (op(=).operator (#0 :> #3 :> ![])) c :=
  et_bvar_succ M0 (a :> b :> c :> e) 2

lemma et_bvar4 {m : ℕ} (a b c d : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> d :> e) (op(=).operator (#0 :> #4 :> ![])) d :=
  et_bvar_succ M0 (a :> b :> c :> d :> e) 3

lemma et_bvar5 {m : ℕ} (a b c d f : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> d :> f :> e) (op(=).operator (#0 :> #5 :> ![])) f :=
  et_bvar_succ M0 (a :> b :> c :> d :> f :> e) 4

lemma et_bvar6 {m : ℕ} (a b c d f g : M0.V) (e : Fin m → M0.V) :
    EvalTermAt M0 (a :> b :> c :> d :> f :> g :> e) (op(=).operator (#0 :> #6 :> ![])) g :=
  et_bvar_succ M0 (a :> b :> c :> d :> f :> g :> e) 5

lemma ev_nestFunc0_raw {m : ℕ} (φ : SetTheorySemisentence 1) (y : M0.V) (e : Fin m → M0.V) :
    mEv M0 (y :> e) (Semiformula.nestFormulaeFunc φ ![]) ↔ mEv M0 ![y] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_imp, mEv_top, mEv_subst]
  simp only [true_imp_iff]
  refine mEv_congr M0 φ ?_
  funext i; fin_cases i; rfl

lemma et_const0 {m : ℕ} {Ψ : SetTheorySemisentence 1} {c : M0.V}
    (hΨ : DefinesConst M0 Ψ c) (e : Fin m → M0.V) :
    EvalTermAt M0 e (Semiformula.nestFormulaeFunc Ψ ![]) c := by
  intro y
  rw [ev_nestFunc0_raw]
  exact hΨ y

lemma ev_nestFunc1_raw {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → M0.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (y : M0.V) :
    mEv M0 (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔ mEv M0 ![y, v₀] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₀ : M0.V, d₀ = v₀ → mEv M0 ![y, d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [mEv_imp, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst]
  have he0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin 1).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rfl
  have he1 : (fun k : Fin 2 =>
      tvRaw (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 1) :> fun i : Fin 1 => #(i.addCast m.succ)) k)) =
      ![y, d₀] := by
    funext k; fin_cases k <;> rfl
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

lemma et_comp1 {m : ℕ} {φ : SetTheorySemisentence 2} {G : M0.V → M0.V}
    (hφ : ∀ y x₀ : M0.V, mEv M0 ![y, x₀] φ ↔ y = G x₀)
    {e : Fin m → M0.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) :
    EvalTermAt M0 e (Semiformula.nestFormulaeFunc φ ![Ψ₀]) (G v₀) := by
  intro y
  rw [ev_nestFunc1_raw M0 φ h₀ y, hφ y v₀]

lemma ev_nestFunc2_raw {m : ℕ} (φ : SetTheorySemisentence 3)
    {e : Fin m → M0.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (h₁ : EvalTermAt M0 e Ψ₁ v₁) (y : M0.V) :
    mEv M0 (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔ mEv M0 ![y, v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₁ d₀ : M0.V, (d₀ = v₀ ∧ d₁ = v₁) → mEv M0 ![y, d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [mEv_all]
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [mEv_imp, mEv_and, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst, mEv_subst]
  have he_psi0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases rfl (fun j => rfl) k
  have he_psi1 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((1 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => rfl) k
    simp [h1, tvRaw]
  have he_phi : (fun k : Fin 3 =>
      tvRaw (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 2) :> fun i : Fin 2 => #(i.addCast m.succ)) k)) =
      ![y, d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · rfl
    · rfl
    · change tvRaw (d₀ :> d₁ :> y :> e) Empty.elim (#((1 : Fin 2).addCast m.succ)) = d₁
      simp [h1, tvRaw]
  rw [he_psi0, he_psi1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

lemma et_comp2 {m : ℕ} {φ : SetTheorySemisentence 3} {G : M0.V → M0.V → M0.V}
    (hφ : ∀ y x₀ x₁ : M0.V, mEv M0 ![y, x₀, x₁] φ ↔ y = G x₀ x₁)
    {e : Fin m → M0.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (h₁ : EvalTermAt M0 e Ψ₁ v₁) :
    EvalTermAt M0 e (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) (G v₀ v₁) := by
  intro y
  rw [ev_nestFunc2_raw M0 φ h₀ h₁ y, hφ y v₀ v₁]

lemma ev_nest1 {m : ℕ} (φ : SetTheorySemisentence 1)
    {e : Fin m → M0.V} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) :
    mEv M0 e (Semiformula.nestFormulae φ ![Ψ₀]) ↔ mEv M0 ![v₀] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₀ : M0.V, d₀ = v₀ → mEv M0 ![d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [mEv_imp, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst]
  have he0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> e) Empty.elim
        ((#((0 : Fin 1).addCast m) :> fun j : Fin m => #(j.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases rfl (fun j => rfl) k
  have he1 : (fun k : Fin 1 =>
      tvRaw (d₀ :> e) Empty.elim (#(k.addCast m))) = ![d₀] := by
    funext k; fin_cases k; rfl
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

lemma ev_nest2 {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → M0.V} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : M0.V}
    (h₀ : EvalTermAt M0 e Ψ₀ v₀) (h₁ : EvalTermAt M0 e Ψ₁ v₁) :
    mEv M0 e (Semiformula.nestFormulae φ ![Ψ₀, Ψ₁]) ↔ mEv M0 ![v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ d₁ d₀ : M0.V, (d₀ = v₀ ∧ d₁ = v₁) → mEv M0 ![d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [mEv_all]
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [mEv_imp, mEv_and, mEv_and, mEv_top, and_true, mEv_subst, mEv_subst, mEv_subst]
  have he0 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> e) Empty.elim
        ((#((0 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k; refine Fin.cases rfl (fun j => rfl) k
  have he1 : (fun k : Fin (m + 1) =>
      tvRaw (d₀ :> d₁ :> e) Empty.elim
        ((#((1 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => rfl) k
    simp [h1, tvRaw]
  have he_phi : (fun k : Fin 2 =>
      tvRaw (d₀ :> d₁ :> e) Empty.elim (#(k.addCast m))) = ![d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · rfl
    · change tvRaw (d₀ :> d₁ :> e) Empty.elim (#((1 : Fin 2).addCast m)) = d₁
      simp [h1, tvRaw]
  rw [he0, he1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

lemma ev_faf_eq {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ = v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    exact (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
  · intro heq d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    exact heq

lemma ev_faf_ne {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ ≠ v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    have hv2 := (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rwa [mEv_not, mEv_eq] at hv2
  · intro hne d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [mEv_not, mEv_eq]
    exact hne

lemma ev_faf_mem {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      M0.mem v₁ v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    exact (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
  · intro hmem d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    exact hmem

lemma ev_faf_notMem {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : M0.V} (h₁ : EvalTermAt M0 e T₁ v₁) (h₂ : EvalTermAt M0 (v₁ :> e) T₂ v₂) :
    mEv M0 e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      ¬ M0.mem v₁ v₂ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_all] at hv1
    have hv2 := (mEv_imp M0 _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rwa [mEv_not, mEv_mem] at hv2
  · intro hnm d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_all]
    intro d₂
    rw [mEv_imp]
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [mEv_not, mEv_mem]
    exact hnm

lemma ev_faf_ball {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : M0.V}
    (h₁ : EvalTermAt M0 e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    mEv M0 e (∀¹ (T₁ 🡒 Semiformula.ballMem (#0) φ)) ↔
      ∀ x : M0.V, M0.mem x v₁ → mEv M0 (x :> v₁ :> e) φ := by
  rw [mEv_all]
  constructor
  · intro h x hx
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_ballMem] at hv1
    exact hv1 x hx
  · intro h d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_ballMem]
    exact h

lemma ev_faf_bexs {m : ℕ} {e : Fin m → M0.V}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : M0.V}
    (h₁ : EvalTermAt M0 e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    mEv M0 e (∀¹ (T₁ 🡒 Semiformula.bexsMem (#0) φ)) ↔
      ∃ x : M0.V, M0.mem x v₁ ∧ mEv M0 (x :> v₁ :> e) φ := by
  rw [mEv_all]
  constructor
  · intro h
    have hv1 := (mEv_imp M0 _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [mEv_bexsMem] at hv1
    exact hv1
  · intro h d₁
    rw [mEv_imp]
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [mEv_bexsMem]
    exact h

lemma dc_isω : DefinesConst M0 SetTheory.isω (vnOmegaV M0) := by
  intro w
  unfold SetTheory.isω
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ x : M0.V, M0.mem x w ↔
      ∀ I : M0.V, (M0.mem (emptyV M0) I ∧ ∀ y : M0.V, M0.mem y I → M0.mem (insertV M0 y y) I) →
        M0.mem x I).trans ?_
  · refine forall_congr' fun x => ?_
    rw [mEv_iff, mEv_mem, mEv_all]
    refine iff_congr Iff.rfl (forall_congr' fun I => ?_)
    rw [mEv_imp, mEv_mem]
    exact imp_congr ((mEv_subst1 M0 _ _ _).trans (ev_IsInductive M0 I)) Iff.rfl
  · constructor
    · intro h
      apply extV M0
      intro x
      rw [h x, mem_vnOmegaV_iff]
    · rintro rfl x
      rw [mem_vnOmegaV_iff]

lemma ev_range (r R : M0.V) :
    mEv M0 ![r, R] SetTheory.range.dfn ↔ r = relRangeV M0 R := by
  unfold SetTheory.range.dfn
  change mEv M0 ![r, R] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ y : M0.V, M0.mem y r ↔ ∃ x : M0.V, M0.mem (kpairV M0 x y) R).trans ?_
  · refine forall_congr' fun y => ?_
    rw [mEv_iff]
    refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 y _) (et_bvar3 M0 _ y r _)) ?_
    rw [mEv_exs]
    refine exists_congr fun x => ?_
    exact ev_faf_mem M0
      (et_comp2 M0 (ev_kpair M0) (et_bvar1 M0 x _) (et_bvar2 M0 x y _))
      (et_bvar5 M0 _ x y r R _)
  · constructor
    · intro h
      apply extV M0
      intro y
      rw [h y, mem_relRangeV]
    · rintro rfl y
      rw [mem_relRangeV]

lemma ev_function (F Y X : M0.V) :
    mEv M0 ![F, Y, X] SetTheory.function.dfn ↔ F = funsV M0 X Y := by
  unfold SetTheory.function.dfn
  change mEv M0 ![F, Y, X] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ f : M0.V, M0.mem f F ↔ M0.mem f (funsV M0 X Y)).trans ?_
  · refine forall_congr' fun f => ?_
    rw [mEv_iff]
    refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 f _) (et_bvar3 M0 _ f F _)) ?_
    rw [mEv_and, mem_funsV]
    refine and_congr ?_ ?_
    · rw [ev_nest2 M0 SetTheory.isSubsetOf (et_bvar1 M0 f _)
        (et_comp2 M0 (ev_prod M0) (et_bvar4 M0 f F Y X _) (et_bvar3 M0 f F Y _)), ev_isSubsetOf]
    · rw [ev_faf_ball M0 (et_bvar4 M0 f F Y X _)]
      refine forall₂_congr fun x _ => ?_
      rw [mEv_existsUnique]
      refine existsUnique_congr fun y => ?_
      exact ev_faf_mem M0
        (et_comp2 M0 (ev_kpair M0) (et_bvar2 M0 y x _) (et_bvar1 M0 y _))
        (et_bvar5 M0 _ y x _ f _)
  · constructor
    · intro h; exact extV M0 h
    · rintro rfl f; rfl

lemma ev_value (v f x : M0.V) :
    mEv M0 ![v, f, x] SetTheory.value.dfn ↔ v = zfcAppV M0 f x := by
  unfold SetTheory.value.dfn
  change mEv M0 ![v, f, x] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z v ↔
      M0.mem z (sUnionV M0 (relRangeV M0 f)) ∧ ∃ y : M0.V, M0.mem z y ∧ M0.mem (kpairV M0 x y) f).trans ?_
  · refine forall_congr' fun z => ?_
    rw [mEv_iff]
    refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 z _) (et_bvar3 M0 _ z v _)) ?_
    rw [mEv_and]
    refine and_congr ?_ ?_
    · exact ev_faf_mem M0 (et_bvar1 M0 z _)
        (et_comp1 M0 (ev_sUnion M0) (et_comp1 M0 (ev_range M0) (et_bvar4 M0 _ z v f _)))
    · rw [mEv_exs]
      refine exists_congr fun y => ?_
      rw [mEv_and]
      refine and_congr
        (ev_faf_mem M0 (et_bvar2 M0 y z _) (et_bvar2 M0 _ y _))
        (ev_faf_mem M0 (et_comp2 M0 (ev_kpair M0) (et_bvar5 M0 y z v f x _) (et_bvar1 M0 y _))
          (et_bvar5 M0 _ y z v f _))
  · constructor
    · intro h
      apply extV M0
      intro z
      rw [h z, mem_zfcAppV]
    · rintro rfl z
      rw [mem_zfcAppV]

/- `Constant14` evaluations -/

lemma dc_zero : DefinesConst M0 Constant14.zero (emptyV M0) := by
  intro z
  unfold Constant14.zero
  exact (mEv_subst1 M0 _ _ _).trans (ev_isEmpty M0 z)

lemma dc_numeral (k : ℕ) : DefinesConst M0 (Constant14.numeral k) (vnNatV M0 k) := by
  induction k with
  | zero => exact dc_zero M0
  | succ k ih =>
    intro y
    unfold Constant14.numeral vnNatV
    exact et_comp1 M0 (ev_succ M0) ih y

lemma dc_setPair {Ψ₁ Ψ₂ : SetTheorySemisentence 1} {v₁ v₂ : M0.V}
    (h₁ : DefinesConst M0 Ψ₁ v₁) (h₂ : DefinesConst M0 Ψ₂ v₂) :
    DefinesConst M0 (Constant14.setPair Ψ₁ Ψ₂) (kpairV M0 v₁ v₂) := by
  intro y
  unfold Constant14.setPair
  have h := et_comp2 M0 (ev_kpair M0) (h₁ ·) (h₂ ·) y
  rwa [mEv_e1] at h

lemma dc_setTriple {Ψ₁ Ψ₂ Ψ₃ : SetTheorySemisentence 1} {v₁ v₂ v₃ : M0.V}
    (h₁ : DefinesConst M0 Ψ₁ v₁) (h₂ : DefinesConst M0 Ψ₂ v₂) (h₃ : DefinesConst M0 Ψ₃ v₃) :
    DefinesConst M0 (Constant14.setTriple Ψ₁ Ψ₂ Ψ₃) (kpairV M0 v₁ (kpairV M0 v₂ v₃)) :=
  dc_setPair M0 h₁ (dc_setPair M0 h₂ h₃)

lemma dc_finiteSet_map {α : Type*} (l : List α)
    (fForm : α → SetTheorySemisentence 1) (fVal : α → M0.V)
    (hf : ∀ a, DefinesConst M0 (fForm a) (fVal a)) :
    DefinesConst M0 (Constant14.finiteSet (l.map fForm)) (listToV M0 (l.map fVal)) := by
  induction l with
  | nil => exact dc_zero M0
  | cons a as ih =>
    intro y
    simp only [List.map_cons, Constant14.finiteSet, listToV]
    have h := et_comp2 M0 (ev_insert M0) (hf a ·) (ih ·) y
    rwa [mEv_e1] at h

lemma dc_integers : DefinesConst M0 Constant14.integers (intSetV M0) := by
  intro y
  unfold Constant14.integers intSetV
  exact ev_faf_eq M0 (et_bvar1 M0 y _)
    (et_comp2 M0 (ev_prod M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_isω M0) _))

lemma dc_integerZero : DefinesConst M0 Constant14.integerZero (encodeIntV M0 0) := by
  intro y
  unfold Constant14.integerZero
  exact ev_faf_eq M0 (et_bvar1 M0 y _)
    (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _) (et_const0 M0 (dc_numeral M0 0) _))

lemma ev_integerSucc_of_mem {w : M0.V} (hw : M0.mem w (intSetV M0)) (w' : M0.V) :
    mEv M0 ![w', w] Constant14.integerSucc.dfn ↔
      ((pi1V M0 w = vnNatV M0 0 ∧
          w' = kpairV M0 (vnNatV M0 0) (insertV M0 (pi2V M0 w) (pi2V M0 w))) ∨
        (pi1V M0 w = vnNatV M0 1 ∧
          ((pi2V M0 w = vnNatV M0 0 ∧ w' = encodeIntV M0 0) ∨
            ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧ pi2V M0 w = insertV M0 m m ∧
              w' = kpairV M0 (vnNatV M0 1) m))) := by
  unfold Constant14.integerSucc.dfn
  rw [mEv_or, mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 w' w _) (et_const0 M0 (dc_integers M0) _),
      ev_faf_notMem M0 (et_bvar2 M0 w' w _) (et_const0 M0 (dc_integers M0) _)]
  simp only [hw, not_true_eq_false, false_and, or_false, true_and]
  rw [mEv_or, mEv_and, mEv_and, mEv_or, mEv_and]
  refine or_congr
    (and_congr
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 w' w _)) (et_const0 M0 (dc_numeral M0 0) _))
      (ev_faf_eq M0 (et_bvar1 M0 w' _)
        (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _)
          (et_comp1 M0 (ev_succ M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 _ w' w _))))))
    (and_congr
      (ev_faf_eq M0 (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 w' w _)) (et_const0 M0 (dc_numeral M0 1) _))
      (or_congr
        (and_congr
          (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 w' w _)) (et_const0 M0 (dc_numeral M0 0) _))
          (ev_faf_eq M0 (et_bvar1 M0 w' _) (et_const0 M0 (dc_integerZero M0) _)))
        ?_))
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_isω M0) _)]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  rw [mEv_and]
  exact and_congr
    (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 m (vnOmegaV M0) w' w _))
      (et_comp1 M0 (ev_succ M0) (et_bvar2 M0 _ m _)))
    (ev_faf_eq M0 (et_bvar3 M0 m (vnOmegaV M0) w' _)
      (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 1) _) (et_bvar2 M0 _ m _)))

lemma ev_integerSucc_encode (z : ℤ) (w' : M0.V) :
    mEv M0 ![w', encodeIntV M0 z] Constant14.integerSucc.dfn ↔ w' = encodeIntV M0 (z + 1) := by
  rw [ev_integerSucc_of_mem M0 (encodeIntV_mem M0 z)]
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := h01.symm
  cases z with
  | ofNat k =>
    simp only [encodeIntV, pi1V_kpairV, pi2V_kpairV, h01, false_and, or_false, true_and]
    rfl
  | negSucc k =>
    simp only [encodeIntV, pi1V_kpairV, pi2V_kpairV, h10, false_and, false_or, true_and]
    cases k with
    | zero =>
      have hno : ¬ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
          vnNatV M0 0 = insertV M0 m m ∧ w' = kpairV M0 (vnNatV M0 1) m := by
        rintro ⟨m, _, hm, _⟩
        have : M0.mem m (vnNatV M0 0) := hm ▸ (mem_insertV M0).mpr (Or.inl rfl)
        exact not_mem_emptyV M0 m this
      simp only [true_and, hno, or_false]
      rfl
    | succ k =>
      have hne0 : vnNatV M0 (k + 1) ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by omega)
      simp only [hne0, false_and, false_or]
      constructor
      · rintro ⟨m, _, hsucc, rfl⟩
        have hm : vnNatV M0 k = m := succV_inj M0 hsucc
        subst hm
        rfl
      · rintro rfl
        exact ⟨vnNatV M0 k, vnNatV_mem_vnOmegaV M0 k, rfl, rfl⟩

lemma ev_integerPred_encode (z : ℤ) (w' : M0.V) :
    mEv M0 ![w', encodeIntV M0 z] Constant14.integerPred.dfn ↔ w' = encodeIntV M0 (z - 1) := by
  unfold Constant14.integerPred.dfn
  rw [mEv_or, mEv_and, mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 w' (encodeIntV M0 z) _) (et_const0 M0 (dc_integers M0) _),
      ev_faf_mem M0 (et_bvar1 M0 w' _) (et_const0 M0 (dc_integers M0) _),
      ev_nest2 M0 Constant14.integerSucc.dfn (et_bvar2 M0 w' (encodeIntV M0 z) _) (et_bvar1 M0 w' _),
      ev_faf_notMem M0 (et_bvar2 M0 w' (encodeIntV M0 z) _) (et_const0 M0 (dc_integers M0) _)]
  simp only [encodeIntV_mem M0 z, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw', hsucc⟩
    rw [ev_integerSucc_of_mem M0 hw'] at hsucc
    obtain ⟨a, ha, r, hr, rfl⟩ := (mem_prodV M0).mp hw'
    rw [pi1V_kpairV, pi2V_kpairV] at hsucc
    have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
    rcases hsucc with ⟨rfl, hzeq⟩ | ⟨rfl, ⟨rfl, hzeq⟩ | ⟨m, _, hr_eq, hzeq⟩⟩
    · cases z with
      | ofNat k =>
        have hk := (kpairV_inj M0 hzeq).2
        cases k with
        | zero =>
          have : M0.mem r (vnNatV M0 0) := hk ▸ (mem_insertV M0).mpr (Or.inl rfl)
          exact (not_mem_emptyV M0 r this).elim
        | succ k' =>
          have hrk : vnNatV M0 k' = r := succV_inj M0 hk
          subst r
          change encodeIntV M0 (Int.ofNat k') = _
          exact congrArg (encodeIntV M0) (by simp only [Int.ofNat_eq_natCast]; omega)
      | negSucc k =>
        exact (h01.symm (kpairV_inj M0 hzeq).1).elim
    · have hz0 : z = 0 := encodeIntV_inj M0 hzeq
      subst hz0
      rfl
    · cases z with
      | ofNat k =>
        exact (h01 (kpairV_inj M0 hzeq).1).elim
      | negSucc k =>
        have hmk : vnNatV M0 k = m := (kpairV_inj M0 hzeq).2
        subst m
        rw [hr_eq]
        change encodeIntV M0 (Int.negSucc (k + 1)) = _
        exact congrArg (encodeIntV M0) (by omega)
  · rintro rfl
    refine ⟨encodeIntV_mem M0 (z - 1), ?_⟩
    rw [ev_integerSucc_encode M0 (z - 1) (encodeIntV M0 z)]
    congr 1
    omega

lemma dc_configSet (N : ℕ) : DefinesConst M0 (Constant14.configSet N) (cfgSetV M0 N) := by
  intro y
  unfold Constant14.configSet cfgSetV
  exact ev_faf_eq M0 (et_bvar1 M0 y _)
    (et_comp2 M0 (ev_prod M0) (et_const0 M0 (dc_numeral M0 N) _)
      (et_comp2 M0 (ev_prod M0) (et_const0 M0 (dc_integers M0) _)
        (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _))))

def entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) : SetTheorySemisentence 1 :=
  Constant14.transitionEntry t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

noncomputable def entryVal (t : ℕ × ℕ × ℕ × ℕ × ℕ) : M0.V :=
  kpairV M0 (kpairV M0 (vnNatV M0 t.1) (vnNatV M0 t.2.1))
    (kpairV M0 (vnNatV M0 t.2.2.1) (kpairV M0 (vnNatV M0 t.2.2.2.1) (vnNatV M0 t.2.2.2.2)))

lemma dc_entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) :
    DefinesConst M0 (entryForm t) (entryVal M0 t) := by
  unfold entryForm Constant14.transitionEntry entryVal
  exact dc_setPair M0 (dc_setPair M0 (dc_numeral M0 _) (dc_numeral M0 _))
    (dc_setTriple M0 (dc_numeral M0 _) (dc_numeral M0 _) (dc_numeral M0 _))

def transTuples {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.ofFn fun q : Fin n =>
    List.ofFn fun sym : Fin 2 =>
      let o := Constant14.transitionCode M q sym
      (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
  List.ofFn fun sym : Fin 2 =>
    (n, sym.val, n, sym.val, Constant14.directionCode none)

noncomputable def instrTableV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : M0.V :=
  listToV M0 ((transTuples M).map (entryVal M0))

lemma dc_instructionTable {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst M0 (Constant14.instructionTable M) (instrTableV M0 M) := by
  unfold Constant14.instructionTable instrTableV
  have hmap : (transTuples M).map entryForm = Constant14.transitionEntries M := by
    simp [transTuples, Constant14.transitionEntries, entryForm, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  rw [← hmap]
  exact dc_finiteSet_map M0 (transTuples M) entryForm (entryVal M0) (dc_entryForm M0)

def transLookup {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (qCode symCode : ℕ) :
    ℕ × ℕ × ℕ :=
  if hq : qCode < n then
    if hs : symCode < 2 then
      Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
    else (n, 0, 1)
  else (n, symCode, 1)

lemma transitionCode_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (q : Fin n) (sym : Fin 2) :
    let o := Constant14.transitionCode M q sym
    o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
  dsimp only [Constant14.transitionCode]
  cases M q sym with
  | none =>
    dsimp only [Constant14.directionCode]
    exact ⟨Nat.lt_succ_self n, sym.isLt, by decide⟩
  | some p =>
    rcases p with ⟨q', ⟨sym', d⟩⟩
    dsimp only
    refine ⟨?_, sym'.isLt, ?_⟩
    · cases q' with
      | none => exact Nat.lt_succ_self n
      | some qv => exact Nat.lt_succ_of_lt qv.isLt
    · cases d <;> decide

lemma instrTableV_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode symCode : ℕ) (hq : qCode < n + 1) (hs : symCode < 2) :
    zfcAppV M0 (instrTableV M0 M) (kpairV M0 (vnNatV M0 qCode) (vnNatV M0 symCode)) =
      let o := transLookup M qCode symCode
      kpairV M0 (vnNatV M0 o.1) (kpairV M0 (vnNatV M0 o.2.1) (vnNatV M0 o.2.2)) := by
  have hmem_iff : ∀ p : M0.V, M0.mem p (instrTableV M0 M) ↔
      (∃ (q : Fin n) (sym : Fin 2),
        let o := Constant14.transitionCode M q sym
        p = entryVal M0 (q.val, sym.val, o.1, o.2.1, o.2.2)) ∨
      (∃ sym : Fin 2, p = entryVal M0 (n, sym.val, n, sym.val, 1)) := by
    intro p
    unfold instrTableV
    rw [mem_listToV, List.mem_map]
    simp only [transTuples, List.mem_append, List.mem_flatten, List.mem_ofFn, Constant14.directionCode]
    constructor
    · rintro ⟨t, (⟨l, ⟨q, rfl⟩, ht⟩ | ⟨sym, rfl⟩), rfl⟩
      · obtain ⟨sym, rfl⟩ := List.mem_ofFn.mp ht
        exact Or.inl ⟨q, sym, rfl⟩
      · exact Or.inr ⟨sym, rfl⟩
    · rintro (⟨q, sym, rfl⟩ | ⟨sym, rfl⟩)
      · exact ⟨_, Or.inl ⟨_, ⟨q, rfl⟩, List.mem_ofFn.mpr ⟨sym, rfl⟩⟩, rfl⟩
      · exact ⟨_, Or.inr ⟨sym, rfl⟩, rfl⟩
  let o := transLookup M qCode symCode
  apply zfcAppV_of_unique M0
  intro y
  rw [hmem_iff]
  constructor
  · rintro (⟨q, sym, heq⟩ | ⟨sym, heq⟩)
    · obtain ⟨h1, rfl⟩ := kpairV_inj M0 heq
      obtain ⟨hq1, hs1⟩ := kpairV_inj M0 h1
      have hqc : qCode = q.val := vnNatV_inj M0 hq1
      have hsc : symCode = sym.val := vnNatV_inj M0 hs1
      subst hqc hsc
      dsimp only [o, transLookup]
      rw [dif_pos q.isLt, dif_pos sym.isLt]
    · obtain ⟨h1, rfl⟩ := kpairV_inj M0 heq
      obtain ⟨hq1, hs1⟩ := kpairV_inj M0 h1
      have hqc : qCode = n := vnNatV_inj M0 hq1
      have hsc : symCode = sym.val := vnNatV_inj M0 hs1
      subst qCode symCode
      dsimp only [o, transLookup]
      rw [dif_neg (Nat.lt_irrefl n)]
  · rintro rfl
    by_cases hqn : qCode < n
    · left
      refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]
      rw [dif_pos hqn, dif_pos hs]; rfl
    · have hqe : qCode = n := by omega
      subst qCode
      right
      refine ⟨⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]
      rw [dif_neg (Nat.lt_irrefl n)]; rfl

lemma dc_emptyTape : DefinesConst M0 Constant14.emptyTape (emptyTapeV M0) := by
  intro f
  unfold Constant14.emptyTape
  rw [mEv_and]
  rw [ev_faf_mem M0 (et_bvar1 M0 f _)
        (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _)),
      ev_faf_ball M0 (et_const0 M0 (dc_integers M0) _)]
  refine (and_congr Iff.rfl (forall₂_congr fun i _ =>
      (?_ : _ ↔ zfcAppV M0 f i = vnNatV M0 0))).trans ?_
  · exact ev_faf_eq M0
      (et_comp2 M0 (ev_value M0) (et_bvar3 M0 i (intSetV M0) f _) (et_bvar1 M0 i _))
      (et_const0 M0 (dc_numeral M0 0) _)
  · constructor
    · rintro ⟨hf, hall⟩
      refine funsV_ext M0 hf (emptyTapeV_mem_funs M0) fun u hu => ?_
      rw [hall u hu, emptyTapeV_app M0 hu]
    · rintro rfl
      exact ⟨emptyTapeV_mem_funs M0, fun u hu => emptyTapeV_app M0 hu⟩

/- ## Section 5: `nextStepV`, Halting Trace Simulation, and `model_satisfies_halts` -/

lemma exists_nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ F : M0.V, ∀ e : M0.V, M0.mem e F ↔
      ∃ z : M0.V, M0.mem z (cfgSetV M0 (n + 1)) ∧
        ∃ z' : M0.V, M0.mem z' (cfgSetV M0 (n + 1)) ∧
          e = kpairV M0 z z' ∧
          mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) := by
  let ambient := prodV M0 (cfgSetV M0 (n + 1)) (cfgSetV M0 (n + 1))
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.bexsMem (&0)
      (Semiformula.bexsMem (&0)
        ((Rew.subst ![#2, #1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
          (Rew.subst ![#0, #1] ▹
            Rewriting.emb (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)))))
  obtain ⟨F, hF⟩ := sepV M0 ambient φ (fun _ => cfgSetV M0 (n + 1))
  refine ⟨F, fun e => ?_⟩
  rw [hF e]
  have hφ : evalM M0.mem ![e] (fun _ => cfgSetV M0 (n + 1)) φ ↔
      ∃ z : M0.V, M0.mem z (cfgSetV M0 (n + 1)) ∧
        ∃ z' : M0.V, M0.mem z' (cfgSetV M0 (n + 1)) ∧
          e = kpairV M0 z z' ∧
          mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) := by
    dsimp only [φ]
    rw [evalM_bexsMem]
    refine exists_congr fun z => and_congr Iff.rfl ?_
    rw [evalM_bexsMem]
    refine exists_congr fun z' => and_congr Iff.rfl ?_
    rw [evalM_and]
    refine and_congr ?_ ?_
    · change evalM M0.mem (z' :> z :> e :> ![]) _
        ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#2, #1, #0]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 e z z')
      funext i; fin_cases i <;> rfl
    · change evalM M0.mem (z' :> z :> e :> ![]) _
        ((Rewriting.emb (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))) ⇜ ![#0, #1]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine evalRaw_congr Eq M0.mem _ ?_ rfl
      funext i; fin_cases i <;> rfl
  rw [hφ]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨z, hz, z', hz', rfl, _⟩
  exact (kpairV_mem_prodV M0).mpr ⟨hz, hz'⟩

noncomputable def nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : M0.V :=
  (exists_nextStepV M0 M).choose

lemma mem_nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {e : M0.V} :
    M0.mem e (nextStepV M0 M) ↔
      ∃ z : M0.V, M0.mem z (cfgSetV M0 (n + 1)) ∧
        ∃ z' : M0.V, M0.mem z' (cfgSetV M0 (n + 1)) ∧
          e = kpairV M0 z z' ∧
          mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) :=
  (exists_nextStepV M0 M).choose_spec e

lemma dc_nextStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst M0 (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) (nextStepV M0 M) := by
  intro p
  unfold Constant14.nextStep
  change mEv M0 ![p] (∀¹ _) ↔ _
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ e : M0.V, M0.mem e p ↔ M0.mem e (nextStepV M0 M)).trans
    ⟨fun h => extV M0 h, fun h e => by rw [h]⟩
  refine forall_congr' fun e => ?_
  rw [mEv_iff, mem_nextStepV]
  refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 e _) (et_bvar3 M0 _ e p _)) ?_
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  refine exists_congr fun z => and_congr_right fun _ => ?_
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  refine exists_congr fun z' => and_congr_right fun _ => ?_
  rw [mEv_and]
  exact and_congr
    (ev_faf_eq M0 (et_bvar5 M0 z' _ z _ e _)
      (et_comp2 M0 (ev_kpair M0) (et_bvar4 M0 _ z' _ z _) (et_bvar2 M0 _ z' _)))
    (ev_nest2 M0 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
      (et_bvar1 M0 z' _) (et_bvar3 M0 z' _ z _))

abbrev ExtCfg (n : ℕ) := Option (Fin n) × ℤ × Tape (Fin 2)

def extInit (n : ℕ) [NeZero n] : ExtCfg n := (some 0, 0, Tape.mk₁ [])

def extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ExtCfg n → ExtCfg n
  | (none, pos, T) => (none, pos, T)
  | (some q, pos, T) =>
    match M q T.head with
    | none => (none, pos, T)
    | some (q', Stmt.write sym d) =>
      let pos' := match d with
        | Dir.left => pos - 1
        | Dir.right => pos + 1
      (q', pos', (T.write sym).move d)

lemma blank_tape_nth (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  cases i with
  | ofNat k =>
    cases k <;> simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]
  | negSucc k =>
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]

noncomputable def simStepTape {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : ExtCfg n) (g : M0.V) : M0.V :=
  match c with
  | (none, _, _) => g
  | (some q, pos, T) =>
    match M q T.head with
    | none => g
    | some (_, Stmt.write sym _) =>
      updateTapeV M0 g (encodeIntV M0 pos) (vnNatV M0 sym.val)

noncomputable def simTape {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ℕ → M0.V
  | 0 => emptyTapeV M0
  | k + 1 => simStepTape M0 M ((extStep M)^[k] (extInit n)) (simTape M k)

lemma simTape_spec {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    let c := (extStep M)^[k] (extInit n)
    M0.mem (simTape M0 M k) (funsV M0 (intSetV M0) (vnNatV M0 2)) ∧
      ∀ m : ℤ, zfcAppV M0 (simTape M0 M k) (encodeIntV M0 m) =
        vnNatV M0 (c.2.2.nth (m - c.2.1)).val := by
  induction k with
  | zero =>
    refine ⟨emptyTapeV_mem_funs M0, fun m => ?_⟩
    rw [simTape, emptyTapeV_app M0 (encodeIntV_mem M0 m)]
    change vnNatV M0 0 = vnNatV M0 ((Tape.mk₁ ([] : List (Fin 2))).nth (m - 0)).val
    rw [blank_tape_nth]
    rfl
  | succ k ih =>
    rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
    rw [hext] at ih
    dsimp only at ih
    obtain ⟨hg, happ⟩ := ih
    dsimp only
    rw [Function.iterate_succ_apply', hext, simTape, hext]
    cases qOpt with
    | none =>
      exact ⟨hg, happ⟩
    | some q =>
      dsimp only [extStep, simStepTape]
      cases hMq : M q T.head with
      | none =>
        exact ⟨hg, happ⟩
      | some out =>
        rcases out with ⟨q', ⟨sym, d⟩⟩
        dsimp only
        have hg' : M0.mem (updateTapeV M0 (simTape M0 M k) (encodeIntV M0 pos) (vnNatV M0 sym.val))
            (funsV M0 (intSetV M0) (vnNatV M0 2)) :=
          updateTapeV_mem_funs M0 hg (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt)
        refine ⟨hg', fun m => ?_⟩
        rw [updateTapeV_app M0 hg (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) (encodeIntV_mem M0 m)]
        cases d with
        | left =>
          dsimp only
          rw [Tape.move_left_nth]
          have hidx : m - (pos - 1) - 1 = m - pos := by omega
          rw [hidx, Tape.write_nth]
          by_cases hmp : m = pos
          · subst hmp
            rw [if_pos rfl, sub_self, if_pos rfl]
          · have hne1 : encodeIntV M0 m ≠ encodeIntV M0 pos := fun h => hmp (encodeIntV_inj M0 h)
            have hne2 : m - pos ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne2, happ m]
        | right =>
          dsimp only
          rw [Tape.move_right_nth]
          have hidx : m - (pos + 1) + 1 = m - pos := by omega
          rw [hidx, Tape.write_nth]
          by_cases hmp : m = pos
          · subst hmp
            rw [if_pos rfl, sub_self, if_pos rfl]
          · have hne1 : encodeIntV M0 m ≠ encodeIntV M0 pos := fun h => hmp (encodeIntV_inj M0 h)
            have hne2 : m - pos ≠ 0 := by omega
            rw [if_neg hne1, if_neg hne2, happ m]

noncomputable def simCfgV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) : M0.V :=
  let c := (extStep M)^[k] (extInit n)
  kpairV M0 (vnNatV M0 (Constant14.stateCode c.1))
    (kpairV M0 (encodeIntV M0 c.2.1) (simTape M0 M k))

lemma simCfgV_mem {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    M0.mem (simCfgV M0 M k) (cfgSetV M0 (n + 1)) := by
  unfold simCfgV cfgSetV
  refine (kpairV_mem_prodV M0).mpr ⟨?_, (kpairV_mem_prodV M0).mpr ⟨encodeIntV_mem M0 _, (simTape_spec M0 M k).1⟩⟩
  apply vnNatV_lt_mem
  cases ((extStep M)^[k] (extInit n)).1 with
  | none => exact Nat.lt_succ_self n
  | some q => exact Nat.lt_succ_of_lt q.isLt

lemma dc_initialConfig {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst M0 Constant14.initialConfig (simCfgV M0 M 0) := by
  intro z
  unfold Constant14.initialConfig
  rw [ev_faf_eq M0 (et_bvar1 M0 z _)
    (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _)
      (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_integerZero M0) _) (et_const0 M0 (dc_emptyTape M0) _)))]
  rfl

lemma ev_nextConfig_simCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (k : ℕ) (z' : M0.V) :
    mEv M0 ![z', simCfgV M0 M k]
      (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z' = simCfgV M0 M (k + 1) := by
  let z0 := simCfgV M0 M k
  have hz0 : M0.mem z0 (cfgSetV M0 (n + 1)) := simCfgV_mem M0 M k
  have hz1 : M0.mem (simCfgV M0 M (k + 1)) (cfgSetV M0 (n + 1)) := simCfgV_mem M0 M (k + 1)
  obtain ⟨hg0, happ0⟩ := simTape_spec M0 M k
  rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
  rw [hext] at happ0
  dsimp only at happ0
  let qCode := Constant14.stateCode qOpt
  have hq : qCode < n + 1 := by
    dsimp only [qCode]
    cases qOpt with
    | none => exact Nat.lt_succ_self n
    | some q => exact Nat.lt_succ_of_lt q.isLt
  have hz0_eq : z0 = kpairV M0 (vnNatV M0 qCode) (kpairV M0 (encodeIntV M0 pos) (simTape M0 M k)) := by
    dsimp only [z0, simCfgV, qCode]; rw [hext]
  have hsym : zfcAppV M0 (simTape M0 M k) (encodeIntV M0 pos) = vnNatV M0 T.head.val := by
    have h := happ0 pos
    rw [sub_self] at h
    exact h
  let o := transLookup M qCode T.head.val
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o, transLookup]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos T.head.isLt]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ T.head
    · rw [dif_neg hqn]
      dsimp only
      exact ⟨Nat.lt_succ_self n, T.head.isLt, by decide⟩
  let tVal := kpairV M0 (vnNatV M0 o.1) (kpairV M0 (vnNatV M0 o.2.1) (vnNatV M0 o.2.2))
  have htVal_eq : zfcAppV M0 (instrTableV M0 M)
      (kpairV M0 (pi1V M0 z0) (zfcAppV M0 (pi2V M0 (pi2V M0 z0)) (pi1V M0 (pi2V M0 z0)))) = tVal := by
    rw [hz0_eq, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, hsym]
    exact instrTableV_app M0 M qCode T.head.val hq T.head.isLt
  -- Compute exact next state, head position, and tape
  have hnext_eq :
      let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
      simCfgV M0 M (k + 1) =
        kpairV M0 (vnNatV M0 o.1) (kpairV M0 (encodeIntV M0 pos') (simTape M0 M (k + 1))) ∧
      (zfcAppV M0 (simTape M0 M (k + 1)) (encodeIntV M0 pos) = vnNatV M0 o.2.1 ∧
       ∀ u : M0.V, M0.mem u (intSetV M0) → u ≠ encodeIntV M0 pos →
         zfcAppV M0 (simTape M0 M (k + 1)) u = zfcAppV M0 (simTape M0 M k) u) := by
    dsimp only [simCfgV]
    rw [Function.iterate_succ_apply', hext, simTape, hext]
    cases qOpt with
    | none =>
      have ho : o = (n, T.head.val, 1) := by
        dsimp only [o, qCode, Constant14.stateCode, transLookup]
        rw [dif_neg (Nat.lt_irrefl n)]
      rw [ho]
      dsimp only [extStep, simStepTape, Constant14.stateCode]
      refine ⟨by simp, hsym, fun _ _ _ => rfl⟩
    | some q =>
      have ho : o = Constant14.transitionCode M q T.head := by
        dsimp only [o, qCode, Constant14.stateCode, transLookup]
        rw [dif_pos q.isLt, dif_pos T.head.isLt]
      rw [ho]
      rcases hMq : M q T.head with _ | ⟨q', ⟨sym, d⟩⟩
      · rw [Constant14.transitionCode, extStep, simStepTape, hMq]
        dsimp only [Constant14.directionCode, Constant14.stateCode]
        refine ⟨by simp, hsym, fun _ _ _ => rfl⟩
      · cases d with
        | left =>
          rw [Constant14.transitionCode, extStep, simStepTape, hMq]
          dsimp only [Constant14.directionCode]
          refine ⟨by simp, ?_, ?_⟩
          · rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) (encodeIntV_mem M0 pos),
              if_pos rfl]
          · intro u hu hne
            rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) hu,
              if_neg hne]
        | right =>
          rw [Constant14.transitionCode, extStep, simStepTape, hMq]
          dsimp only [Constant14.directionCode]
          refine ⟨by simp, ?_, ?_⟩
          · rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) (encodeIntV_mem M0 pos),
              if_pos rfl]
          · intro u hu hne
            rw [updateTapeV_app M0 hg0 (encodeIntV_mem M0 pos) (vnNatV_lt_mem M0 sym.isLt) hu,
              if_neg hne]
  let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
  obtain ⟨hcfg1_eq, htap1_pos, htap1_rest⟩ := hnext_eq
  -- Evaluate `Constant14.nextConfig` formula
  unfold Constant14.nextConfig
  rw [mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 z' z0 _) (et_const0 M0 (dc_configSet M0 (n + 1)) _),
      ev_faf_mem M0 (et_bvar1 M0 z' _) (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  simp only [hz0, true_and]
  rw [mEv_exs]
  refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
      (t = tVal ∧
       pi1V M0 z' = pi1V M0 t ∧
       ((pi2V M0 (pi2V M0 t) = vnNatV M0 0 ∧
           mEv M0 ![pi1V M0 (pi2V M0 z'), pi1V M0 (pi2V M0 z0)] Constant14.integerPred.dfn) ∨
         (pi2V M0 (pi2V M0 t) = vnNatV M0 1 ∧ pi1V M0 (pi2V M0 z') = pi1V M0 (pi2V M0 z0)) ∨
         (pi2V M0 (pi2V M0 t) = vnNatV M0 2 ∧
           mEv M0 ![pi1V M0 (pi2V M0 z'), pi1V M0 (pi2V M0 z0)] Constant14.integerSucc.dfn)) ∧
       zfcAppV M0 (pi2V M0 (pi2V M0 z')) (pi1V M0 (pi2V M0 z0)) = pi1V M0 (pi2V M0 t) ∧
       ∀ u : M0.V, M0.mem u (intSetV M0) → u ≠ pi1V M0 (pi2V M0 z0) →
         zfcAppV M0 (pi2V M0 (pi2V M0 z')) u = zfcAppV M0 (pi2V M0 (pi2V M0 z0)) u)))).trans ?_
  · rw [mEv_and, mEv_and, mEv_and, mEv_and]
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
    · rw [ev_faf_eq M0 (et_bvar1 M0 t _)
        (et_comp2 M0 (ev_value M0) (et_const0 M0 (dc_instructionTable M0 M) _)
          (et_comp2 M0 (ev_kpair M0)
            (et_comp1 M0 (ev_pi1 M0) (et_bvar4 M0 _ t z' z0 _))
            (et_comp2 M0 (ev_value M0)
              (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z0 _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z0 _)))))),
        htVal_eq]
    · exact ev_faf_eq M0
        (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 t z' _))
        (et_comp1 M0 (ev_pi1 M0) (et_bvar2 M0 _ t _))
    · rw [mEv_or, mEv_or, mEv_and, mEv_and, mEv_and]
      refine or_congr
        (and_congr
          (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
            (et_const0 M0 (dc_numeral M0 0) _))
          (ev_nest2 M0 Constant14.integerPred.dfn
            (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
            (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z0 _)))))
        (or_congr
          (and_congr
            (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
              (et_const0 M0 (dc_numeral M0 1) _))
            (ev_faf_eq M0
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z0 _)))))
          (and_congr
            (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
              (et_const0 M0 (dc_numeral M0 2) _))
            (ev_nest2 M0 Constant14.integerSucc.dfn
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z0 _))))))
    · exact ev_faf_eq M0
        (et_comp2 M0 (ev_value M0)
          (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
          (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z0 _))))
        (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 _ t _)))
    · rw [ev_faf_ball M0 (et_const0 M0 (dc_integers M0) _)]
      refine forall₂_congr fun u _ => ?_
      rw [mEv_imp]
      exact imp_congr
        (ev_faf_ne M0 (et_bvar1 M0 u _)
          (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar6 M0 _ u (intSetV M0) t z' z0 _))))
        (ev_faf_eq M0
          (et_comp2 M0 (ev_value M0)
            (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 u (intSetV M0) t z' _)))
            (et_bvar1 M0 u _))
          (et_comp2 M0 (ev_value M0)
            (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar6 M0 _ u (intSetV M0) t z' z0 _)))
            (et_bvar2 M0 _ u _)))
  · constructor
    · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
      obtain ⟨s2, _, p_tail, hp_tail, rfl⟩ := (mem_prodV M0).mp hz'
      obtain ⟨p2, _, g2, hg2, rfl⟩ := (mem_prodV M0).mp hp_tail
      rw [hz0_eq] at hdir hwr hrest
      dsimp only [tVal] at hq_eq hdir hwr
      rw [pi1V_kpairV, pi1V_kpairV] at hq_eq
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hdir
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hwr
      simp only [pi2V_kpairV, pi1V_kpairV] at hrest
      rw [hcfg1_eq, hq_eq]
      congr 1; congr 1
      · have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h02 : vnNatV M0 0 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h01, h02, false_and, or_false] at hdir
          rw [ev_integerPred_encode] at hdir
          simpa [pos', hdv] using hdir
        · have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h12 : vnNatV M0 1 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
          simpa [pos', hdv] using hdir
        · have h20 : vnNatV M0 2 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h21 : vnNatV M0 2 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h20, h21, false_and, false_or] at hdir
          rw [ev_integerSucc_encode] at hdir
          simpa [pos', hdv] using hdir
      · refine funsV_ext M0 hg2 (simTape_spec M0 M (k + 1)).1 fun u hu => ?_
        by_cases hup : u = encodeIntV M0 pos
        · subst hup; rw [hwr, htap1_pos]
        · rw [hrest u hu hup, htap1_rest u hu hup]
    · rintro rfl
      refine ⟨hz1, tVal, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hcfg1_eq]; dsimp only [tVal]; rw [pi1V_kpairV, pi1V_kpairV]
      · rw [hcfg1_eq, hz0_eq]; dsimp only [tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · left; refine ⟨rfl, ?_⟩
          rw [ev_integerPred_encode]; simp
        · right; left; refine ⟨rfl, ?_⟩
          simp
        · right; right; refine ⟨rfl, ?_⟩
          rw [ev_integerSucc_encode]; simp
      · rw [hcfg1_eq, hz0_eq]; dsimp only [tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        exact htap1_pos
      · intro u hu hne
        rw [hz0_eq, pi2V_kpairV, pi1V_kpairV] at hne
        rw [hcfg1_eq, hz0_eq]
        simp only [pi2V_kpairV]
        exact htap1_rest u hu hne

lemma zfcAppV_nextStepV_simCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    zfcAppV M0 (nextStepV M0 M) (simCfgV M0 M k) = simCfgV M0 M (k + 1) := by
  apply zfcAppV_of_unique M0
  intro y
  rw [mem_nextStepV]
  constructor
  · rintro ⟨z, _, z', _, heq, hnc⟩
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact (ev_nextConfig_simCfg M0 M k y).mp hnc
  · rintro rfl
    exact ⟨simCfgV M0 M k, simCfgV_mem M0 M k, simCfgV M0 M (k + 1), simCfgV_mem M0 M (k + 1),
      rfl, (ev_nextConfig_simCfg M0 M k (simCfgV M0 M (k + 1))).mpr rfl⟩

lemma multiStep_agrees_extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    match M.multiStep (Machine.init []) k with
    | none => ((extStep M)^[k] (extInit n)).1 = none
    | some cfg => ((extStep M)^[k] (extInit n)).1 = cfg.q ∧
                  ((extStep M)^[k] (extInit n)).2.2 = cfg.tape := by
  induction k with
  | zero =>
    simp [Machine.multiStep_zero, Machine.init, extInit, Fin.default_eq_zero]
  | succ k ih =>
    rw [Machine.multiStep_succ, Function.iterate_succ_apply']
    cases hmk : M.multiStep (Machine.init []) k with
    | none =>
      rw [hmk] at ih
      dsimp only at ih ⊢
      rcases hext : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
      rw [hext] at ih; dsimp only at ih; subst ih
      rfl
    | some cfg =>
      rw [hmk] at ih
      dsimp only [Option.bind_some] at ih ⊢
      rcases cfg with ⟨qOpt, Tk⟩
      rcases hext : (extStep M)^[k] (extInit n) with ⟨c1, pos, cT⟩
      rw [hext] at ih; dsimp only at ih
      rcases ih with ⟨rfl, rfl⟩
      cases c1 with
      | none =>
        simp [Machine.step, extStep]
      | some qk =>
        dsimp only [Machine.step, extStep]
        cases hMq : M qk cT.head with
        | none =>
          simp
        | some out =>
          rcases out with ⟨qNext, ⟨sym, d⟩⟩
          simp

theorem model_satisfies_halts {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (h : ∃ N : ℕ, M.multiStep (Machine.init []) N = none) :
    evalM M0.mem Fin.elim0 Empty.elim (Constant14.halts M) := by
  obtain ⟨N, hN⟩ := h
  have hnone : ((extStep M)^[N] (extInit n)).1 = none := by
    have h1 := multiStep_agrees_extStep M N
    rw [hN] at h1
    exact h1
  let cN := (extStep M)^[N] (extInit n)
  let mVal := encodeIntV M0 cN.2.1
  let gVal := simTape M0 M N
  have htarget_eq : kpairV M0 (vnNatV M0 n) (kpairV M0 mVal gVal) = simCfgV M0 M N := by
    dsimp only [simCfgV, mVal, gVal, cN]
    rw [hnone]
    rfl
  change mEv M0 (Fin.elim0 : Fin 0 → M0.V) (Constant14.halts M)
  rw [mEv_e0 M0 (Fin.elim0 : Fin 0 → M0.V) ![]]
  unfold Constant14.halts
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_integers M0) ![])]
  refine ⟨mVal, encodeIntV_mem M0 _, ?_⟩
  rw [ev_faf_bexs M0
    (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _))]
  refine ⟨gVal, (simTape_spec M0 M N).1, ?_⟩
  have htarget : EvalTermAt M0 (gVal :> funsV M0 (intSetV M0) (vnNatV M0 2) :> mVal :> intSetV M0 :> ![])
      (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
        (Semiformula.nestFormulaeFunc (Constant14.numeral n) ![] :>
          Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
            (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![]) :> ![]))
      (simCfgV M0 M N) := by
    rw [← htarget_eq]
    exact et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 n) _)
      (et_comp2 M0 (ev_kpair M0) (et_bvar3 M0 gVal _ mVal _) (et_bvar1 M0 gVal _))
  rw [mEv_all]
  intro t
  rw [mEv_imp]
  intro ht
  have ht_eq : t = simCfgV M0 M N := (htarget t).mp ht
  subst ht_eq
  rw [mEv_all]
  intro O
  rw [mEv_imp]
  intro hO_nest
  rw [ev_nestFunc2_raw M0 Constant14.orbit
    (et_const0 M0 (dc_nextStep M0 M) _) (et_const0 M0 (dc_initialConfig M0 M) _) O] at hO_nest
  unfold Constant14.orbit at hO_nest
  rw [mEv_and] at hO_nest
  have hO_mem := hO_nest.2
  rw [mEv_all] at hO_mem
  have hO_t := hO_mem (simCfgV M0 M N)
  rw [mEv_iff,
      ev_faf_mem M0 (et_bvar1 M0 (simCfgV M0 M N) _) (et_bvar3 M0 _ (simCfgV M0 M N) O _)] at hO_t
  refine hO_t.mpr ?_
  rw [mEv_all]
  intro A
  rw [mEv_imp, mEv_and]
  rintro ⟨hA0_raw, hAstep_raw⟩
  have hA0 : M0.mem (simCfgV M0 M 0) A :=
    (ev_faf_mem M0 (et_bvar5 M0 A (simCfgV M0 M N) O (nextStepV M0 M) (simCfgV M0 M 0) _)
      (et_bvar2 M0 _ A _)).mp hA0_raw
  rw [ev_faf_ball M0 (et_bvar1 M0 A _)] at hAstep_raw
  have hAstep : ∀ y : M0.V, M0.mem y A → M0.mem (zfcAppV M0 (nextStepV M0 M) y) A := by
    intro y hy
    exact (ev_faf_mem M0
      (et_comp2 M0 (ev_value M0) (et_bvar6 M0 y A A (simCfgV M0 M N) O (nextStepV M0 M) _) (et_bvar1 M0 y _))
      (et_bvar4 M0 _ y A A _)).mp (hAstep_raw y hy)
  have hAk : ∀ k : ℕ, M0.mem (simCfgV M0 M k) A := by
    intro k
    induction k with
    | zero => exact hA0
    | succ k ih =>
      rw [← zfcAppV_nextStepV_simCfg M0 M k]
      exact hAstep _ ih
  exact (ev_faf_mem M0 (et_bvar2 M0 A (simCfgV M0 M N) _) (et_bvar2 M0 _ A _)).mpr (hAk N)

end WithModel

end C14Stage2

namespace C14H4Sound

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver

lemma tvRaw_eq_exTv {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (t : Semiterm ℒₛₑₜ ξ n) :
    C14Completeness.tvRaw e ε t = OMA.R_Constant14_c14_ge_4_R1.exTv.choose e ε t := by
  cases t with
  | bvar i => exact (OMA.R_Constant14_c14_ge_4_R1.tv_bvar e ε i).symm
  | fvar x => exact (OMA.R_Constant14_c14_ge_4_R1.tv_fvar e ε x).symm
  | func f _ => exact (f : Empty).elim

lemma evalM_eq_exEv {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ n) :
    C14Completeness.evalM (· ∈ ·) e ε φ ↔ OMA.R_Constant14_c14_ge_4_R1.exEv.choose e ε φ := by
  induction φ with
  | verum => exact (OMA.R_Constant14_c14_ge_4_R1.ev_verum_c e ε).symm
  | falsum => exact (OMA.R_Constant14_c14_ge_4_R1.ev_falsum_c e ε).symm
  | rel r v =>
    cases r with
    | eq => rw [OMA.R_Constant14_c14_ge_4_R1.ev_rel_eq_c, ← tvRaw_eq_exTv, ← tvRaw_eq_exTv]; rfl
    | mem => rw [OMA.R_Constant14_c14_ge_4_R1.ev_rel_mem_c, ← tvRaw_eq_exTv, ← tvRaw_eq_exTv]; rfl
  | nrel r v =>
    rw [OMA.R_Constant14_c14_ge_4_R1.ev_nrel_c]
    cases r with
    | eq => rw [OMA.R_Constant14_c14_ge_4_R1.ev_rel_eq_c, ← tvRaw_eq_exTv, ← tvRaw_eq_exTv]; rfl
    | mem => rw [OMA.R_Constant14_c14_ge_4_R1.ev_rel_mem_c, ← tvRaw_eq_exTv, ← tvRaw_eq_exTv]; rfl
  | and a b iha ihb =>
    rw [OMA.R_Constant14_c14_ge_4_R1.ev_and_c]; exact and_congr (iha e) (ihb e)
  | or a b iha ihb =>
    rw [OMA.R_Constant14_c14_ge_4_R1.ev_or_c]; exact or_congr (iha e) (ihb e)
  | all a iha =>
    rw [OMA.R_Constant14_c14_ge_4_R1.ev_all_c]; exact forall_congr' fun d => iha (d :> e)
  | exs a iha =>
    rw [OMA.R_Constant14_c14_ge_4_R1.ev_exs_c]; exact exists_congr fun d => iha (d :> e)

theorem not_provable_not_halts_of_isHalting {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hH : M.IsHalting) : ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
  intro hprov
  have hsat := OMA.R_Constant14_c14_ge_4_R1.sound_theory OMA.R_Constant14_c14_ge_4_R1.zfsetModel hprov
  have hnot : ¬ OMA.R_Constant14_c14_ge_4_R1.exEv.choose Fin.elim0 Empty.elim (Constant14.halts M) :=
    (OMA.R_Constant14_c14_ge_4_R1.ev_neg Fin.elim0 Empty.elim (Constant14.halts M)).mp hsat
  let M_std : C14Stage2.ZFCModel :=
    ⟨ZFSet.{0}, (· ∈ ·), fun ψ hψ => (evalM_eq_exEv Fin.elim0 Empty.elim ψ).mpr
      (OMA.R_Constant14_c14_ge_4_R1.zfsetModel ψ hψ)⟩
  rw [Machine.isHalting_iff_exists_haltsAt] at hH
  obtain ⟨k, hk⟩ := hH
  exact hnot ((evalM_eq_exEv Fin.elim0 Empty.elim (Constant14.halts M)).mp
    (C14Stage2.model_satisfies_halts M_std M ⟨k + 1, hk⟩))

end C14H4Sound

/-
# Universal 2-symbol BusyBeaver Turing Machine for `Constant14.c14_ge_4.R1.H4`
-/

namespace C14H4TM

open Turing Turing.BusyBeaver StateTransition Relation
open scoped Classical

def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0

def fin2ToBool (a : Fin 2) : Bool := a == 1

lemma fin2ToBool_boolToFin2 (b : Bool) : fin2ToBool (boolToFin2 b) = b := by
  cases b <;> rfl

lemma boolToFin2_fin2ToBool (a : Fin 2) : boolToFin2 (fin2ToBool a) = a := by
  fin_cases a <;> rfl

def boolToFin2PM : PointedMap Bool (Fin 2) := ⟨boolToFin2, rfl⟩

lemma tape_map_mk1 (L : List Bool) :
    (Tape.mk₁ L).map boolToFin2PM = Tape.mk₁ (L.map boolToFin2) := by
  cases L with
  | nil =>
    change Tape.mk' ((ListBlank.mk []).map boolToFin2PM) ((ListBlank.mk []).map boolToFin2PM) =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk [])
    simp [ListBlank.map_mk]
  | cons b bs =>
    change Tape.mk' ((ListBlank.mk []).map boolToFin2PM) ((ListBlank.mk (b :: bs)).map boolToFin2PM) =
      Tape.mk' (ListBlank.mk []) (ListBlank.mk (boolToFin2 b :: bs.map boolToFin2))
    simp [ListBlank.map_mk]
    rfl

lemma listBlank_map_cons (a : Bool) (L : ListBlank Bool) :
    (L.cons a).map boolToFin2PM = (L.map boolToFin2PM).cons (boolToFin2 a) := by
  induction L using ListBlank.induction_on with
  | h l =>
    rw [ListBlank.cons_mk, ListBlank.map_mk, ListBlank.map_mk, ListBlank.cons_mk]
    rfl

lemma tape_map_move (T : Tape Bool) (d : Dir) :
    (T.move d).map boolToFin2PM = (T.map boolToFin2PM).move d := by
  obtain ⟨a, L, R⟩ := T
  cases d
  · simp only [Tape.map, Tape.move, ListBlank.head_map, ListBlank.tail_map]
    rw [listBlank_map_cons]
    rfl
  · simp only [Tape.map, Tape.move, ListBlank.head_map, ListBlank.tail_map]
    rw [listBlank_map_cons]
    rfl

lemma tape_map_write (T : Tape Bool) (b : Bool) :
    (T.write b).map boolToFin2PM = (T.map boolToFin2PM).write (boolToFin2 b) := by
  obtain ⟨a, L, R⟩ := T
  rfl

/- ## Connection between `StateTransition.eval M.step` and `BusyBeaver.Machine.IsHalting` -/

lemma eval_dom_iff_exists_multiStep_none {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : Cfg (Fin 2) (Fin n)) :
    (StateTransition.eval M.step c).Dom ↔ ∃ k : ℕ, M.multiStep c k = none := by
  constructor
  · intro hdom
    have hmem : (StateTransition.eval M.step c).get hdom ∈ StateTransition.eval M.step c :=
      Part.get_mem hdom
    obtain ⟨hreach, hterm⟩ := StateTransition.mem_eval.mp hmem
    generalize (StateTransition.eval M.step c).get hdom = y at hreach hterm
    refine ReflTransGen.head_induction_on hreach ?_ ?_
    · exact ⟨1, by simp [hterm]⟩
    · intro a b hstep _ ih
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      have hms : ∀ (x : Cfg (Fin 2) (Fin n)) (m : ℕ),
          M.multiStep x (m + 1) = (M.step x).bind (fun x' => M.multiStep x' m) := by
        intro x m
        induction m with
        | zero => rw [Machine.multiStep_one]; cases M.step x <;> rfl
        | succ m ihm =>
          rw [Machine.multiStep_succ, ihm]
          cases M.step x <;> simp [Machine.multiStep_succ]
      rw [hms a k, hstep, Option.bind_some]
      exact hk
  · rintro ⟨k, hk⟩
    have hms : ∀ (m : ℕ) (x : Cfg (Fin 2) (Fin n)),
        M.multiStep x m = none → (StateTransition.eval M.step x).Dom := by
      intro m
      induction m with
      | zero => intro x hx; simp [Machine.multiStep_zero] at hx
      | succ m ih =>
        intro x hx
        have hfront : M.multiStep x (m + 1) = (M.step x).bind (fun x' => M.multiStep x' m) := by
          clear hx ih
          induction m with
          | zero => rw [Machine.multiStep_one]; cases M.step x <;> rfl
          | succ m ihm =>
            rw [Machine.multiStep_succ, ihm]
            cases M.step x <;> simp [Machine.multiStep_succ]
        rw [hfront] at hx
        cases hstep : M.step x with
        | none =>
          exact Part.dom_iff_mem.mpr ⟨x, StateTransition.mem_eval.mpr ⟨ReflTransGen.refl, hstep⟩⟩
        | some x' =>
          rw [hstep, Option.bind_some] at hx
          obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (ih x' hx)
          obtain ⟨hr, ht⟩ := StateTransition.mem_eval.mp hy
          exact Part.dom_iff_mem.mpr ⟨y, StateTransition.mem_eval.mpr ⟨ReflTransGen.head hstep hr, ht⟩⟩
    exact hms k c hk

lemma isHalting_iff_eval_dom {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    M.IsHalting ↔ (StateTransition.eval M.step (Machine.init [])).Dom := by
  rw [eval_dom_iff_exists_multiStep_none, Machine.isHalting_iff_exists_haltsAt]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k + 1, hk⟩
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp [Machine.multiStep_zero] at hk
    | succ k => exact ⟨k, hk⟩

/- ## Compiling a finitely supported `TM0.Machine Bool Λ0` to `BusyBeaver.Machine (Fin 2) (Fin N)` -/

lemma tm0_to_bb {Λ0 : Type*} [Inhabited Λ0] (M0 : TM0.Machine Bool Λ0)
    (S0 : Finset Λ0) (hS0 : TM0.Supports M0 ↑S0) :
    ∃ (N : ℕ) (_ : NeZero N) (U : Machine (Fin 2) (Fin N)),
      ∀ L : List Bool,
        (StateTransition.eval U.step (Machine.init (L.map boolToFin2))).Dom ↔
          (TM0.eval M0 L).Dom := by
  have hdef : default ∈ S0 := hS0.1
  have hpos : 0 < S0.card := Finset.card_pos.mpr ⟨default, hdef⟩
  let e0 : S0 ≃ Fin S0.card := (S0.equivFin).setValue ⟨default, hdef⟩ ⟨0, hpos⟩
  have he0_def : e0 ⟨default, hdef⟩ = ⟨0, hpos⟩ := by
    dsimp [e0]; exact Equiv.setValue_eq _ _ _
  let N := 2 * S0.card
  have : NeZero N := ⟨by omega⟩
  let U : Machine (Fin 2) (Fin N) := fun q a =>
    if hmod : q.val % 2 = 0 then
      let i : Fin S0.card := ⟨q.val / 2, by omega⟩
      let l : Λ0 := (e0.symm i).val
      match M0 l (fin2ToBool a) with
      | none => none
      | some (l', stmt) =>
        if hl' : l' ∈ S0 then
          let j := e0 ⟨l', hl'⟩
          match stmt with
          | TM0.Stmt.move d => some (some ⟨2 * j.val, by omega⟩, Stmt.write a d)
          | TM0.Stmt.write b => some (some ⟨2 * j.val + 1, by omega⟩, Stmt.write (boolToFin2 b) Dir.right)
        else none
    else
      some (some ⟨q.val - 1, by omega⟩, Stmt.write a Dir.left)
  refine ⟨N, inferInstance, U, fun L => ?_⟩
  let R : TM0.Cfg Bool Λ0 → Cfg (Fin 2) (Fin N) → Prop := fun c1 c2 =>
    ∃ hl : c1.q ∈ S0,
      c2 = ⟨some ⟨2 * (e0 ⟨c1.q, hl⟩).val, by omega⟩, c1.Tape.map boolToFin2PM⟩
  have hresp : Respects (TM0.step M0) U.step R := by
    intro c1 c2 ⟨hl, hc2⟩
    subst hc2
    obtain ⟨l, T⟩ := c1
    dsimp only at hl ⊢
    let idx : Fin S0.card := e0 ⟨l, hl⟩
    have hq_even : (2 * idx.val) % 2 = 0 := by omega
    have hq_div : (⟨(2 * idx.val) / 2, by omega⟩ : Fin S0.card) = idx := Fin.ext (by dsimp; omega)
    have hhead : (T.map boolToFin2PM).head = boolToFin2 T.head := rfl
    cases hM : M0 l T.head with
    | none =>
      simp only [TM0.step, hM, Option.map_none]
      change U.step ⟨some ⟨2 * idx.val, _⟩, T.map boolToFin2PM⟩ = none
      simp only [Machine.step, hhead, U, dif_pos hq_even]
      have hsymm : (e0.symm ⟨(2 * idx.val) / 2, by omega⟩).val = l := by
        rw [hq_div]; exact congrArg Subtype.val (e0.symm_apply_apply ⟨l, hl⟩)
      rw [hsymm, fin2ToBool_boolToFin2, hM]
      rfl
    | some out =>
      rcases out with ⟨l', stmt⟩
      have hl' : l' ∈ S0 := hS0.2 hM hl
      simp only [TM0.step, hM, Option.map_some]
      let j := e0 ⟨l', hl'⟩
      have hsymm : (e0.symm ⟨(2 * idx.val) / 2, by omega⟩).val = l := by
        rw [hq_div]; exact congrArg Subtype.val (e0.symm_apply_apply ⟨l, hl⟩)
      cases stmt with
      | move d =>
        refine ⟨⟨some ⟨2 * j.val, by omega⟩, (T.move d).map boolToFin2PM⟩, ⟨hl', rfl⟩, ?_⟩
        refine TransGen.single ?_
        change U.step ⟨some ⟨2 * idx.val, _⟩, T.map boolToFin2PM⟩ =
          some ⟨some ⟨2 * j.val, _⟩, (T.move d).map boolToFin2PM⟩
        simp only [Machine.step, hhead, U, dif_pos hq_even, hsymm, fin2ToBool_boolToFin2, hM,
          dif_pos hl', Option.map_some]
        congr 1
        rw [← hhead, Tape.write_self, ← tape_map_move]
      | write b =>
        refine ⟨⟨some ⟨2 * j.val, by omega⟩, (T.write b).map boolToFin2PM⟩, ⟨hl', rfl⟩, ?_⟩
        let mid : Cfg (Fin 2) (Fin N) :=
          ⟨some ⟨2 * j.val + 1, by omega⟩, ((T.map boolToFin2PM).write (boolToFin2 b)).move Dir.right⟩
        have hstep1 : U.step ⟨some ⟨2 * idx.val, by omega⟩, T.map boolToFin2PM⟩ = some mid := by
          simp only [Machine.step, hhead, U, dif_pos hq_even, hsymm, fin2ToBool_boolToFin2, hM,
            dif_pos hl', Option.map_some, mid]
          rfl
        have hodd : ¬ (2 * j.val + 1) % 2 = 0 := by omega
        have hstep2 : U.step mid = some ⟨some ⟨2 * j.val, by omega⟩, (T.write b).map boolToFin2PM⟩ := by
          simp only [Machine.step, mid, U, dif_neg hodd, Option.map_some]
          refine congrArg Option.some ?_
          refine congrArg₂ Cfg.mk ?_ ?_
          · exact congrArg Option.some (Fin.ext rfl)
          · rw [Tape.write_self, Tape.move_right_left, tape_map_write]
        exact TransGen.head hstep1 (TransGen.single hstep2)
  have hinit : R (TM0.init L) (Machine.init (L.map boolToFin2)) := by
    refine ⟨hdef, ?_⟩
    simp only [TM0.init, Machine.init, he0_def, mul_zero, tape_map_mk1]
    rfl
  rw [TM0.eval]
  simp only [Part.map_Dom]
  exact StateTransition.tr_eval_dom hresp hinit

/- ## Prepending a finite `List Bool` tape initialization to a fixed `BusyBeaver.Machine` -/

def prependMachine {N : ℕ} [NeZero N] (L : List Bool) (U : Machine (Fin 2) (Fin N)) :
    Machine (Fin 2) (Fin (L.length + 1 + N)) :=
  fun q a =>
    if hq : q.val < L.length then
      some (some ⟨q.val + 1, by omega⟩,
        Stmt.write (boolToFin2 (L.reverse.getD q.val false)) Dir.left)
    else if hq2 : q.val = L.length then
      some (some ⟨L.length + 1, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩,
        Stmt.write 0 Dir.right)
    else
      (U ⟨q.val - (L.length + 1), by omega⟩ a).map fun (q', stmt) =>
        (q'.map fun r => ⟨L.length + 1 + r.val, by omega⟩, stmt)

lemma prependMachine_isHalting {N : ℕ} [NeZero N] (L : List Bool) (U : Machine (Fin 2) (Fin N)) :
    (prependMachine L U).IsHalting ↔
      (StateTransition.eval U.step (Machine.init (L.map boolToFin2))).Dom := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  let M := prependMachine L U
  have hpref : ∀ i (hi : i ≤ L.length),
      Reaches M.step (Machine.init [])
        ⟨some ⟨i, by omega⟩,
         ⟨0, ListBlank.mk [], ListBlank.mk ((L.reverse.take i).reverse.map boolToFin2)⟩⟩ := by
    intro i hi
    induction i with
    | zero =>
      simp only [List.take_zero, List.reverse_nil, List.map_nil]
      exact ReflTransGen.refl
    | succ i ih =>
      have hi' : i ≤ L.length := by omega
      have hprev := ih hi'
      refine ReflTransGen.tail hprev ?_
      have hlt : i < L.length := by omega
      have hstep : M.step ⟨some ⟨i, by omega⟩,
          ⟨0, ListBlank.mk [], ListBlank.mk ((L.reverse.take i).reverse.map boolToFin2)⟩⟩ =
          some ⟨some ⟨i + 1, by omega⟩,
          ⟨0, ListBlank.mk [], ListBlank.mk ((L.reverse.take (i + 1)).reverse.map boolToFin2)⟩⟩ := by
        simp only [Machine.step, M, prependMachine, dif_pos hlt, Option.map_some,
          Tape.write, Tape.move]
        congr 1
        have hhead : (ListBlank.mk ([] : List (Fin 2))).head = 0 := rfl
        have htail : (ListBlank.mk ([] : List (Fin 2))).tail = ListBlank.mk [] := rfl
        have htake : L.reverse.take (i + 1) = L.reverse.take i ++ [L.reverse.getD i false] := by
          have hlen : i < L.reverse.length := by simp [hlt]
          rw [List.take_succ_eq_append_getElem hlen, List.getD_eq_getElem _ _ hlen]
        rw [hhead, htail, htake, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.map_cons, ListBlank.cons_mk]
      exact hstep
  have hstart : Reaches M.step (Machine.init [])
      ⟨some ⟨L.length + 1, by omega⟩, Tape.mk₁ (L.map boolToFin2)⟩ := by
    refine ReflTransGen.tail (hpref L.length le_rfl) ?_
    have htake : L.reverse.take L.length = L.reverse := by
      rw [List.take_of_length_le]; simp
    rw [htake, List.reverse_reverse]
    have hnotlt : ¬ L.length < L.length := Nat.lt_irrefl _
    change M.step _ = some _
    simp only [Machine.step, M, prependMachine, dif_neg hnotlt, ↓reduceDIte, Option.map_some,
      Tape.write, Tape.move]
    congr 1
    congr 1
    cases L with
    | nil =>
      change Tape.mk (ListBlank.mk []).head (ListBlank.cons 0 (ListBlank.mk [])) (ListBlank.mk []).tail =
        Tape.mk₁ []
      simp [Tape.mk₁, Tape.mk₂, Tape.mk']
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons b bs =>
      change Tape.mk (ListBlank.mk (boolToFin2 b :: bs.map boolToFin2)).head
          (ListBlank.cons 0 (ListBlank.mk []))
          (ListBlank.mk (boolToFin2 b :: bs.map boolToFin2)).tail =
        Tape.mk₁ (boolToFin2 b :: bs.map boolToFin2)
      have hcons0 : ListBlank.cons (0 : Fin 2) (ListBlank.mk []) = ListBlank.mk [] :=
        ListBlank.cons_head_tail (ListBlank.mk [])
      rw [hcons0]
      rfl
  let liftCfg : Cfg (Fin 2) (Fin N) → Cfg (Fin 2) (Fin (L.length + 1 + N)) := fun c =>
    ⟨c.q.map fun r => ⟨L.length + 1 + r.val, by omega⟩, c.tape⟩
  have hresp : Respects U.step M.step (fun c1 c2 => liftCfg c1 = c2) := by
    refine fun_respects.2 fun ⟨qOpt, T⟩ => ?_
    cases qOpt with
    | none => rfl
    | some q =>
      have h1 : ¬ L.length + 1 + q.val < L.length := by omega
      have h2 : ¬ L.length + 1 + q.val = L.length := by omega
      have hsub : (⟨L.length + 1 + q.val - (L.length + 1), by omega⟩ : Fin N) = q :=
        Fin.ext (by dsimp; omega)
      cases hU : U q T.head with
      | none =>
        simp only [FRespects, Machine.step, liftCfg, Option.map_some, M, prependMachine,
          dif_neg h1, dif_neg h2, hsub, hU, Option.map_none]
      | some out =>
        rcases out with ⟨q', stmt⟩
        simp only [FRespects, Machine.step, liftCfg, Option.map_some, hU]
        refine TransGen.single ?_
        show M.step ⟨some ⟨L.length + 1 + q.val, _⟩, T⟩ =
          some ⟨Option.map (fun r => ⟨L.length + 1 + r.val, _⟩) q', (T.write stmt.symbol).move stmt.dir⟩
        simp only [Machine.step, M, prependMachine, dif_neg h1, dif_neg h2, hsub, hU, Option.map_some]
  rw [isHalting_iff_eval_dom, StateTransition.reaches_eval hstart]
  exact StateTransition.tr_eval_dom hresp (by
    dsimp only [liftCfg, Machine.init, Fin.default_eq_zero]
    congr 2)

/- ## Universal `ToPartrec.Code` → `TM2` → `TM1` → `TM0` → `BusyBeaver.Machine` -/

instance : Fintype PartrecToTM2.K' :=
  Fintype.ofEquiv (Fin 4)
    { toFun := fun i => match i.val with | 0 => .main | 1 => .rev | 2 => .aux | _ => .stack
      invFun := fun k => match k with | .main => 0 | .rev => 1 | .aux => 2 | .stack => 3
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun k => by cases k <;> rfl }

def univPartVec (v : List.Vector ℕ 1) : Part ℕ :=
  ((Encodable.decode (α := Nat.Partrec.Code) v.head : Option Nat.Partrec.Code) : Part Nat.Partrec.Code).bind
    fun c => c.eval 0

lemma univPartVec_partrec' : Nat.Partrec' univPartVec := by
  have h1 : Partrec (fun n : ℕ =>
      ((Encodable.decode (α := Nat.Partrec.Code) n : Option Nat.Partrec.Code) : Part Nat.Partrec.Code).bind
        fun c => c.eval 0) :=
    (Computable.decode (α := Nat.Partrec.Code)).ofOption.bind
      (Nat.Partrec.Code.eval_part.comp Computable.snd (Computable.const 0)).to₂
  exact Nat.Partrec'.of_part (h1.comp Primrec.vector_head.to_comp)

def inputBits (B_head B_bit0 B_bit1 : List Bool) (n : ℕ) : List Bool :=
  B_head ++ ((PartrecToTM2.trNat n).reverse.flatMap fun g =>
    match g with
    | .bit1 => B_bit1
    | _ => B_bit0)

theorem exists_universal_bb :
    ∃ (N_U : ℕ) (_ : NeZero N_U) (U : Machine (Fin 2) (Fin N_U))
      (B_head B_bit0 B_bit1 : List Bool),
      ∀ c : Nat.Partrec.Code,
        (prependMachine (inputBits B_head B_bit0 B_bit1 (Encodable.encode c)) U).IsHalting ↔
          (c.eval 0).Dom := by
  obtain ⟨cU, hcU⟩ := ToPartrec.Code.exists_code univPartVec_partrec'
  let _ : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal cU PartrecToTM2.Cont'.halt⟩
  let M2 : PartrecToTM2.Λ' → TM2.Stmt (fun _ : PartrecToTM2.K' => PartrecToTM2.Γ') PartrecToTM2.Λ' (Option PartrecToTM2.Γ') :=
    PartrecToTM2.tr
  have hS2 : TM2.Supports M2 (PartrecToTM2.codeSupp cU PartrecToTM2.Cont'.halt) :=
    PartrecToTM2.tr_supports cU PartrecToTM2.Cont'.halt
  let M1_big := TM2to1.tr M2
  have hS1_big : TM1.Supports M1_big (TM2to1.trSupp M2 (PartrecToTM2.codeSupp cU PartrecToTM2.Cont'.halt)) :=
    TM2to1.tr_supports M2 hS2
  let Γ1 := TM2to1.Γ' PartrecToTM2.K' (fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
  obtain ⟨w, enc, dec, henc0, hencdec⟩ := TM1to1.exists_enc_dec (Γ := Γ1)
  let M1_bool := TM1to1.tr enc dec M1_big
  have hS1_bool : TM1.Supports M1_bool
      (TM1to1.trSupp M1_big (TM2to1.trSupp M2 (PartrecToTM2.codeSupp cU PartrecToTM2.Cont'.halt))) :=
    TM1to1.tr_supports enc dec M1_big hS1_big
  let M0 := TM1to0.tr M1_bool
  have hS0 : TM0.Supports M0
      ↑(TM1to0.trStmts M1_bool
        (TM1to1.trSupp M1_big (TM2to1.trSupp M2 (PartrecToTM2.codeSupp cU PartrecToTM2.Cont'.halt)))) :=
    TM1to0.tr_supports M1_bool hS1_bool
  obtain ⟨N_U, hN_U, U, hU⟩ := tm0_to_bb M0 _ hS0
  let sym1 (b : Bool) (g : PartrecToTM2.Γ') : Γ1 :=
    (b, Function.update (fun _ : PartrecToTM2.K' => none) PartrecToTM2.K'.main (some g))
  let B_head : List Bool := (enc (sym1 true .cons)).toList
  let B_bit0 : List Bool := (enc (sym1 false .bit0)).toList
  let B_bit1 : List Bool := (enc (sym1 false .bit1)).toList
  refine ⟨N_U, hN_U, U, B_head, B_bit0, B_bit1, fun c => ?_⟩
  let m := Encodable.encode c
  rw [prependMachine_isHalting, hU, TM1to0.tr_eval]
  -- Match `inputBits` with `TM1to1` encoding of `TM2to1.trInit .main (trList [m])`
  have hbits_eq : inputBits B_head B_bit0 B_bit1 m =
      (TM2to1.trInit (K := PartrecToTM2.K') (Γ := fun _ => PartrecToTM2.Γ')
        PartrecToTM2.K'.main (PartrecToTM2.trList [m])).flatMap fun x => (enc x).toList := by
    have htrList : PartrecToTM2.trList [m] = PartrecToTM2.trNat m ++ [PartrecToTM2.Γ'.cons] := by
      simp [PartrecToTM2.trList]
    rw [htrList, TM2to1.trInit]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      inputBits, B_head, sym1]
    change (enc (sym1 true .cons)).toList ++ _ =
      (enc (sym1 true .cons)).toList ++
        List.flatMap (fun x => (enc x).toList) ((PartrecToTM2.trNat m).reverse.map (sym1 false))
    congr 1
    rw [List.flatMap_map]
    refine List.flatMap_congr fun g hg => ?_
    have hgb : g = .bit0 ∨ g = .bit1 := by
      have hg' : g ∈ PartrecToTM2.trNat m := List.mem_reverse.mp hg
      have hne := PartrecToTM2.trNat_natEnd m g hg'
      cases g with
      | consₗ => simp [PartrecToTM2.natEnd] at hne
      | cons => simp [PartrecToTM2.natEnd] at hne
      | bit0 => exact Or.inl rfl
      | bit1 => exact Or.inr rfl
    rcases hgb with rfl | rfl <;> rfl
  rw [hbits_eq]
  -- Step through `TM1to1`
  have htm11 : (TM1.eval M1_bool
      ((TM2to1.trInit (K := PartrecToTM2.K') (Γ := fun _ => PartrecToTM2.Γ')
        PartrecToTM2.K'.main (PartrecToTM2.trList [m])).flatMap fun x => (enc x).toList)).Dom ↔
      (TM1.eval M1_big (TM2to1.trInit (K := PartrecToTM2.K') (Γ := fun _ => PartrecToTM2.Γ')
        PartrecToTM2.K'.main (PartrecToTM2.trList [m]))).Dom := by
    rw [TM1.eval, TM1.eval]
    simp only [Part.map_Dom]
    refine StateTransition.tr_eval_dom (TM1to1.tr_respects (enc0 := henc0) dec M1_big hencdec) ?_
    dsimp only [TM1to1.trCfg, TM1.init, TM1to1.trTape, TM1to1.trTape']
    simp only [Tape.mk₁, Tape.mk₂, Tape.mk'_left, Tape.mk'_right₀,
      ListBlank.flatMap_mk, List.flatMap_nil]
    rfl
  rw [htm11]
  have htm21 : (TM1.eval M1_big (TM2to1.trInit (K := PartrecToTM2.K') (Γ := fun _ => PartrecToTM2.Γ')
        PartrecToTM2.K'.main (PartrecToTM2.trList [m]))).Dom ↔
      (TM2.eval M2 PartrecToTM2.K'.main (PartrecToTM2.trList [m])).Dom :=
    TM2to1.tr_eval_dom M2 PartrecToTM2.K'.main (PartrecToTM2.trList [m])
  rw [htm21]
  -- Step through `TM2` = `PartrecToTM2`
  have htm2 : (TM2.eval M2 PartrecToTM2.K'.main (PartrecToTM2.trList [m])).Dom ↔
      (cU.eval [m]).Dom := by
    rw [TM2.eval]
    simp only [Part.map_Dom]
    have hinit2 : TM2.init (K := PartrecToTM2.K') (Γ := fun _ => PartrecToTM2.Γ')
        (Λ := PartrecToTM2.Λ') (σ := Option PartrecToTM2.Γ')
        PartrecToTM2.K'.main (PartrecToTM2.trList [m]) =
        PartrecToTM2.init cU [m] := by
      dsimp only [TM2.init, PartrecToTM2.init]
      congr 1
      funext k
      cases k <;> rfl
    rw [hinit2, PartrecToTM2.tr_eval]
    simp only [Part.map_eq_map, Part.map_Dom]
  rw [htm2]
  have hev := hcU ⟨[m], rfl⟩
  change cU.eval [m] = pure <$> univPartVec ⟨[m], rfl⟩ at hev
  rw [hev]
  simp only [Part.map_eq_map, Part.map_Dom, univPartVec, List.Vector.head, m,
    Encodable.encodek, Part.coe_some, Part.bind_some]

def natBits (n : ℕ) : List Bool :=
  if h : n = 0 then []
  else (n % 2 == 1) :: natBits (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

lemma natBits_primrec : Primrec natBits := by
  refine Primrec.nat_omega_rec' natBits (m := id)
    (l := fun n => if n == 0 then [] else [n / 2])
    (g := fun n rs => some (if n == 0 then [] else (n % 2 == 1) :: rs.getD 0 []))
    Primrec.id ?_ ?_ ?_ ?_
  · exact (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const 0)) (Primrec.const [])
      (Primrec.list_cons.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) (Primrec.const []))).of_eq
      fun n => by dsimp; cases (n == 0) <;> rfl
  · refine Primrec₂.of_eq (f := fun (n : ℕ) (rs : List (List Bool)) =>
      some (cond (n == 0) [] ((n % 2 == 1) :: rs.getD 0 []))) ?_ ?_
    · exact Primrec.to₂ <| Primrec.option_some.comp <|
        Primrec.cond (Primrec.beq.comp Primrec.fst (Primrec.const 0)) (Primrec.const []) <|
        Primrec.list_cons.comp
          (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 1))
          ((Primrec.list_getD ([] : List Bool)).comp Primrec.snd (Primrec.const 0))
    · intro n rs; cases (n == 0) <;> rfl
  · intro n n' hn'
    by_cases h0 : n = 0
    · simp [h0] at hn'
    · simp only [beq_iff_eq, h0, ↓reduceIte, List.mem_singleton] at hn'
      subst hn'
      exact Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
  · intro n
    by_cases h0 : n = 0
    · subst h0; simp [natBits]
    · simp only [beq_iff_eq, h0, ↓reduceIte, List.map_cons, List.map_nil, List.getD_cons_zero]
      congr 1
      conv_rhs => rw [natBits, dif_neg h0]

lemma natBits_eq_trNat (n : ℕ) :
    natBits n = (PartrecToTM2.trNat n).map (fun g => g == PartrecToTM2.Γ'.bit1) := by
  have hpos : ∀ p : PosNum,
      natBits (p : ℕ) = (PartrecToTM2.trPosNum p).map (fun g => g == PartrecToTM2.Γ'.bit1) := by
    intro p
    induction p with
    | one =>
      rw [PartrecToTM2.trPosNum]
      change natBits 1 = [true]
      rw [natBits, dif_neg (by decide)]; simp [natBits]
    | bit0 p ih =>
      have hp : 0 < (p : ℕ) := PosNum.cast_pos p
      have hcast : ((PosNum.bit0 p : PosNum) : ℕ) = 2 * (p : ℕ) := by
        rw [PosNum.cast_bit0]; omega
      rw [hcast, natBits, dif_neg (by omega), PartrecToTM2.trPosNum, List.map_cons]
      have hmod : (2 * (p : ℕ)) % 2 = 0 := by omega
      have hdiv : (2 * (p : ℕ)) / 2 = (p : ℕ) := by omega
      rw [hmod, hdiv, ih]; rfl
    | bit1 p ih =>
      have hcast : ((PosNum.bit1 p : PosNum) : ℕ) = 2 * (p : ℕ) + 1 := by
        rw [PosNum.cast_bit1]; omega
      rw [hcast, natBits, dif_neg (by omega), PartrecToTM2.trPosNum, List.map_cons]
      have hmod : (2 * (p : ℕ) + 1) % 2 = 1 := by omega
      have hdiv : (2 * (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
      rw [hmod, hdiv, ih]; rfl
  have hcast_num : ((n : Num) : ℕ) = n := by simp
  rw [PartrecToTM2.trNat]
  conv_lhs => rw [← hcast_num]
  cases (n : Num) with
  | zero =>
    change natBits 0 = []
    simp [natBits]
  | pos p =>
    exact hpos p

lemma inputBits_eq (B_head B_bit0 B_bit1 : List Bool) (n : ℕ) :
    inputBits B_head B_bit0 B_bit1 n =
      B_head ++ (natBits n).reverse.flatMap (fun b => if b then B_bit1 else B_bit0) := by
  unfold inputBits
  congr 1
  rw [natBits_eq_trNat, ← List.map_reverse, List.flatMap_map]
  refine List.flatMap_congr fun g _ => ?_
  cases g <;> rfl

lemma inputBits_primrec (B_head B_bit0 B_bit1 : List Bool) :
    Primrec (inputBits B_head B_bit0 B_bit1) := by
  have hbranch : Primrec₂ (fun (_ : ℕ) (b : Bool) => if b then B_bit1 else B_bit0) :=
    Primrec₂.of_eq (f := fun (_ : ℕ) (b : Bool) => cond b B_bit1 B_bit0)
      (Primrec.to₂ <| Primrec.cond Primrec.snd (Primrec.const B_bit1) (Primrec.const B_bit0))
      (fun _ b => by cases b <;> rfl)
  have h : Primrec (fun n : ℕ =>
      B_head ++ (natBits n).reverse.flatMap (fun b => if b then B_bit1 else B_bit0)) :=
    Primrec.list_append.comp (Primrec.const B_head) <|
      Primrec.list_flatMap (Primrec.list_reverse.comp natBits_primrec) hbranch
  exact h.of_eq fun n => (inputBits_eq B_head B_bit0 B_bit1 n).symm

end C14H4TM

/-
# Part 1 of RE Engine for `Constant14.c14_ge_4.R1.H4`:
Primitive recursive syntax operations (`wfForm`, `codeNeg`, `codeRew`, `codeFvSup`, `codeUnivCl`,
`codeNestFormulae`, `codeNestFormulaeFunc`) on `ℕ`-coded `ℒₛₑₜ` semiformulas.
-/

namespace C14H4RE

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped Classical

/- ## 0. Tiny `Primrec` Combinators -/

lemma primrec_natPair : Primrec₂ Nat.pair :=
  Primrec.to₂ (Primrec.encode (α := ℕ × ℕ))

lemma primrec_iteBool {α β : Type*} [Primcodable α] [Primcodable β]
    {c : α → Bool} {t f : α → β} (hc : Primrec c) (ht : Primrec t) (hf : Primrec f) :
    Primrec (fun a => if c a then t a else f a) :=
  (Primrec.cond hc ht hf).of_eq fun a => by cases c a <;> rfl

lemma primrec_boolAnd {α : Type*} [Primcodable α] {f g : α → Bool}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a && g a) :=
  (Primrec.cond hf hg (Primrec.const false)).of_eq fun a => by cases f a <;> rfl

lemma primrec_boolOr {α : Type*} [Primcodable α] {f g : α → Bool}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a || g a) :=
  (Primrec.cond hf (Primrec.const true) hg).of_eq fun a => by cases f a <;> rfl

lemma primrec_natMax {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => max (f a) (g a)) := by
  have hlt : Primrec (fun a => decide (f a ≤ g a)) := (Primrec.nat_le.comp hf hg).decide
  exact (primrec_iteBool hlt hg hf).of_eq fun a => by
    by_cases h : f a ≤ g a
    · simp [h]
    · simp [h, max_eq_left (le_of_not_ge h)]

/- ## 1. Injective `ℕ`-encoding of `Semiterm ℒₛₑₜ ℕ m` and `Semiformula ℒₛₑₜ ℕ m` -/

def encTerm {m : ℕ} : Semiterm ℒₛₑₜ ℕ m → ℕ
  | Semiterm.bvar i => Nat.pair 0 i.val
  | Semiterm.fvar x => Nat.pair 1 x
  | Semiterm.func f _ => (f : Empty).elim

def encForm {m : ℕ} : Semiformula ℒₛₑₜ ℕ m → ℕ
  | Semiformula.verum => Nat.pair 0 0
  | Semiformula.falsum => Nat.pair 1 0
  | Semiformula.rel Language.Set.Rel.eq v => Nat.pair 2 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | Semiformula.rel Language.Set.Rel.mem v => Nat.pair 3 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | Semiformula.nrel Language.Set.Rel.eq v => Nat.pair 4 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | Semiformula.nrel Language.Set.Rel.mem v => Nat.pair 5 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | Semiformula.and φ ψ => Nat.pair 6 (Nat.pair (encForm φ) (encForm ψ))
  | Semiformula.or φ ψ => Nat.pair 7 (Nat.pair (encForm φ) (encForm ψ))
  | Semiformula.all φ => Nat.pair 8 (encForm φ)
  | Semiformula.exs φ => Nat.pair 9 (encForm φ)

def encClosed {m : ℕ} (φ : Semisentence ℒₛₑₜ m) : ℕ := encForm (Rewriting.emb φ)

lemma rew_emb_q {m : ℕ} : (Rew.emb : Rew ℒₛₑₜ Empty m ℕ m).q = Rew.emb := by
  refine DFunLike.ext _ _ fun t => ?_
  cases t with
  | bvar i => cases i using Fin.cases <;> rfl
  | fvar x => exact x.elim
  | func f _ => exact (f : Empty).elim

lemma emb_all {m : ℕ} (φ : Semisentence ℒₛₑₜ (m + 1)) :
    (Rewriting.emb (Semiformula.all φ) : Semiproposition ℒₛₑₜ m) =
      Semiformula.all (Rewriting.emb φ) := by
  change Semiformula.all (Rew.emb.q ▹ φ) = Semiformula.all (Rew.emb ▹ φ)
  rw [rew_emb_q]

lemma emb_exs {m : ℕ} (φ : Semisentence ℒₛₑₜ (m + 1)) :
    (Rewriting.emb (Semiformula.exs φ) : Semiproposition ℒₛₑₜ m) =
      Semiformula.exs (Rewriting.emb φ) := by
  change Semiformula.exs (Rew.emb.q ▹ φ) = Semiformula.exs (Rew.emb ▹ φ)
  rw [rew_emb_q]

lemma emb_imp {m : ℕ} (φ ψ : Semisentence ℒₛₑₜ m) :
    (Rewriting.emb (φ 🡒 ψ) : Semiproposition ℒₛₑₜ m) = Rewriting.emb φ 🡒 Rewriting.emb ψ :=
  (Rewriting.app (Rew.emb : Rew ℒₛₑₜ Empty m ℕ m)).map_imply' φ ψ

lemma emb_neg {m : ℕ} (φ : Semisentence ℒₛₑₜ m) :
    (Rewriting.emb (∼φ) : Semiproposition ℒₛₑₜ m) = ∼(Rewriting.emb φ) :=
  (Rewriting.app (Rew.emb : Rew ℒₛₑₜ Empty m ℕ m)).map_neg' φ

lemma encTerm_inj {m : ℕ} : Function.Injective (@encTerm m) := by
  intro t1 t2 h
  cases t1 with
  | bvar i =>
    cases t2 with
    | bvar j =>
      simp only [encTerm, Nat.pair_eq_pair, true_and] at h
      exact congrArg Semiterm.bvar (Fin.ext h)
    | fvar y => simp [encTerm] at h
    | func f _ => exact (f : Empty).elim
  | fvar x =>
    cases t2 with
    | bvar j => simp [encTerm] at h
    | fvar y =>
      simp only [encTerm, Nat.pair_eq_pair, true_and] at h
      exact congrArg Semiterm.fvar h
    | func f _ => exact (f : Empty).elim
  | func f _ => exact (f : Empty).elim

lemma encForm_inj {m : ℕ} : Function.Injective (@encForm m) := by
  intro φ1
  induction φ1 with
  | verum =>
    intro φ2 h; cases φ2 with
    | verum => rfl
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | falsum =>
    intro φ2 h; cases φ2 with
    | falsum => rfl
    | rel r _ | nrel r _ => cases r <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | rel r1 v1 =>
    intro φ2 h; cases r1 <;> cases φ2 with
    | rel r2 v2 =>
      cases r2 <;> simp only [encForm, Nat.pair_eq_pair, true_and] at h
      all_goals try exact False.elim (by omega)
      congr 1; funext i; fin_cases i
      · exact encTerm_inj h.1
      · exact encTerm_inj h.2
    | nrel r2 _ => cases r2 <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | nrel r1 v1 =>
    intro φ2 h; cases r1 <;> cases φ2 with
    | nrel r2 v2 =>
      cases r2 <;> simp only [encForm, Nat.pair_eq_pair, true_and] at h
      all_goals try exact False.elim (by omega)
      congr 1; funext i; fin_cases i
      · exact encTerm_inj h.1
      · exact encTerm_inj h.2
    | rel r2 _ => cases r2 <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | and a1 b1 iha ihb =>
    intro φ2 h; cases φ2 with
    | and a2 b2 =>
      simp only [encForm, Nat.pair_eq_pair, true_and] at h
      rw [iha h.1, ihb h.2]
    | rel r2 _ | nrel r2 _ => cases r2 <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | or a1 b1 iha ihb =>
    intro φ2 h; cases φ2 with
    | or a2 b2 =>
      simp only [encForm, Nat.pair_eq_pair, true_and] at h
      rw [iha h.1, ihb h.2]
    | rel r2 _ | nrel r2 _ => cases r2 <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | all a1 iha =>
    intro φ2 h; cases φ2 with
    | all a2 =>
      simp only [encForm, Nat.pair_eq_pair, true_and] at h
      rw [iha h]
    | rel r2 _ | nrel r2 _ => cases r2 <;> simp [encForm] at h
    | _ => simp [encForm] at h
  | exs a1 iha =>
    intro φ2 h; cases φ2 with
    | exs a2 =>
      simp only [encForm, Nat.pair_eq_pair, true_and] at h
      rw [iha h]
    | rel r2 _ | nrel r2 _ => cases r2 <;> simp [encForm] at h
    | _ => simp [encForm] at h

lemma emb_term_inj {m : ℕ} :
    Function.Injective (fun t : Semiterm ℒₛₑₜ Empty m => (Rew.emb t : Semiterm ℒₛₑₜ ℕ m)) := by
  intro t1 t2 h
  cases t1 with
  | bvar i =>
    cases t2 with
    | bvar j =>
      change (#i : Semiterm ℒₛₑₜ ℕ m) = #j at h
      cases h; rfl
    | fvar x => exact x.elim
    | func f _ => exact (f : Empty).elim
  | fvar x => exact x.elim
  | func f _ => exact (f : Empty).elim

lemma emb_inj {m : ℕ} :
    Function.Injective (fun φ : Semisentence ℒₛₑₜ m => (Rewriting.emb φ : Semiproposition ℒₛₑₜ m)) := by
  intro φ1
  induction φ1 with
  | verum => intro φ2 h; cases φ2 <;> first | rfl | exact nomatch h
  | falsum => intro φ2 h; cases φ2 <;> first | rfl | exact nomatch h
  | rel r1 v1 =>
    intro φ2 h; cases φ2 with
    | rel r2 v2 =>
      change Semiformula.rel r1 (fun i => Rew.emb (v1 i)) = Semiformula.rel r2 (fun i => Rew.emb (v2 i)) at h
      cases r1 <;> cases r2
      · simp only [Semiformula.rel.injEq, heq_eq_eq, true_and] at h
        congr 1; funext i; exact emb_term_inj (congrFun h i)
      · exact nomatch h
      · exact nomatch h
      · simp only [Semiformula.rel.injEq, heq_eq_eq, true_and] at h
        congr 1; funext i; exact emb_term_inj (congrFun h i)
    | _ => exact nomatch h
  | nrel r1 v1 =>
    intro φ2 h; cases φ2 with
    | nrel r2 v2 =>
      change Semiformula.nrel r1 (fun i => Rew.emb (v1 i)) = Semiformula.nrel r2 (fun i => Rew.emb (v2 i)) at h
      cases r1 <;> cases r2
      · simp only [Semiformula.nrel.injEq, heq_eq_eq, true_and] at h
        congr 1; funext i; exact emb_term_inj (congrFun h i)
      · exact nomatch h
      · exact nomatch h
      · simp only [Semiformula.nrel.injEq, heq_eq_eq, true_and] at h
        congr 1; funext i; exact emb_term_inj (congrFun h i)
    | _ => exact nomatch h
  | and a1 b1 iha ihb =>
    intro φ2 h; cases φ2 with
    | and a2 b2 =>
      change Semiformula.and (Rewriting.emb a1) (Rewriting.emb b1) =
        Semiformula.and (Rewriting.emb a2) (Rewriting.emb b2) at h
      simp only [Semiformula.and.injEq] at h
      rw [iha h.1, ihb h.2]
    | _ => exact nomatch h
  | or a1 b1 iha ihb =>
    intro φ2 h; cases φ2 with
    | or a2 b2 =>
      change Semiformula.or (Rewriting.emb a1) (Rewriting.emb b1) =
        Semiformula.or (Rewriting.emb a2) (Rewriting.emb b2) at h
      simp only [Semiformula.or.injEq] at h
      rw [iha h.1, ihb h.2]
    | _ => exact nomatch h
  | all a1 iha =>
    intro φ2 h; cases φ2 with
    | all a2 =>
      dsimp only at h
      rw [emb_all, emb_all, Semiformula.all.injEq] at h
      rw [iha h]
    | _ => exact nomatch h
  | exs a1 iha =>
    intro φ2 h; cases φ2 with
    | exs a2 =>
      dsimp only at h
      rw [emb_exs, emb_exs, Semiformula.exs.injEq] at h
      rw [iha h]
    | _ => exact nomatch h

lemma encClosed_inj {m : ℕ} : Function.Injective (@encClosed m) :=
  fun _ _ h => emb_inj (encForm_inj h)

lemma encTerm_emb_toEmpty {m : ℕ} (t : Semiterm ℒₛₑₜ ℕ m) (ht : t.freeVariables = ∅) :
    encTerm (Rew.emb (t.toEmpty ht)) = encTerm t := by
  cases t with
  | bvar i => rfl
  | fvar x => simp [Semiterm.freeVariables] at ht
  | func f _ => exact (f : Empty).elim

lemma encClosed_toEmpty {m : ℕ} (φ : Semiproposition ℒₛₑₜ m) (h : φ.freeVariables = ∅) :
    encClosed (φ.toEmpty h) = encForm φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    cases r
    · change Nat.pair 2 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
        Nat.pair 2 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
      rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
    · change Nat.pair 3 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
        Nat.pair 3 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
      rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
  | nrel r v =>
    cases r
    · change Nat.pair 4 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
        Nat.pair 4 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
      rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
    · change Nat.pair 5 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
        Nat.pair 5 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
      rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
  | and a b iha ihb =>
    change Nat.pair 6 (Nat.pair (encClosed (a.toEmpty _)) (encClosed (b.toEmpty _))) =
      Nat.pair 6 (Nat.pair (encForm a) (encForm b))
    rw [iha, ihb]
  | or a b iha ihb =>
    change Nat.pair 7 (Nat.pair (encClosed (a.toEmpty _)) (encClosed (b.toEmpty _))) =
      Nat.pair 7 (Nat.pair (encForm a) (encForm b))
    rw [iha, ihb]
  | all a iha =>
    change encForm (Rewriting.emb (Semiformula.all (a.toEmpty h))) = Nat.pair 8 (encForm a)
    rw [emb_all]
    exact congrArg (Nat.pair 8) (iha h)
  | exs a iha =>
    change encForm (Rewriting.emb (Semiformula.exs (a.toEmpty h))) = Nat.pair 9 (encForm a)
    rw [emb_exs]
    exact congrArg (Nat.pair 9) (iha h)

/- ## 2. Strictly decreasing pairing lemma -/

lemma unpair_right_lt_of_left_pos {c : ℕ} (h : 0 < c.unpair.1) : c.unpair.2 < c := by
  have heq := Nat.pair_unpair c
  set a := c.unpair.1
  set b := c.unpair.2
  rw [← heq, Nat.pair]
  split_ifs with hab
  · have : 2 ≤ b := by omega
    nlinarith
  · nlinarith

lemma unpair_right_left_lt {c : ℕ} (h : 0 < c.unpair.1) : c.unpair.2.unpair.1 < c :=
  lt_of_le_of_lt (Nat.unpair_left_le _) (unpair_right_lt_of_left_pos h)

lemma unpair_right_right_lt {c : ℕ} (h : 0 < c.unpair.1) : c.unpair.2.unpair.2 < c :=
  lt_of_le_of_lt (Nat.unpair_right_le _) (unpair_right_lt_of_left_pos h)

/- ## 3. `wfTerm` and `wfForm` -/

def wfTerm (m t : ℕ) : Bool :=
  (t.unpair.1 == 0 && decide (t.unpair.2 < m)) || (t.unpair.1 == 1)

lemma wfTerm_primrec : Primrec₂ wfTerm := by
  have h1 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 0) :=
    Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 0)
  have h2 : Primrec (fun p : ℕ × ℕ => decide (p.2.unpair.2 < p.1)) :=
    (Primrec.nat_lt.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst).decide
  have h3 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 1) :=
    Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 1)
  exact Primrec.to₂ (primrec_boolOr (primrec_boolAnd h1 h2) h3)

lemma wfTerm_iff (m t : ℕ) : wfTerm m t = true ↔ ∃ tm : Semiterm ℒₛₑₜ ℕ m, encTerm tm = t := by
  unfold wfTerm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro (⟨h1, h2⟩ | h1)
    · refine ⟨Semiterm.bvar ⟨t.unpair.2, h2⟩, ?_⟩
      simp only [encTerm, ← h1, Nat.pair_unpair]
    · refine ⟨Semiterm.fvar t.unpair.2, ?_⟩
      simp only [encTerm, ← h1, Nat.pair_unpair]
  · rintro ⟨tm, rfl⟩
    cases tm with
    | bvar i => exact Or.inl ⟨by simp [encTerm], by simp [encTerm]⟩
    | fvar x => exact Or.inr (by simp [encTerm])
    | func f _ => exact (f : Empty).elim

def wfForm (p : ℕ × ℕ) : Bool :=
  let m := p.1
  let c := p.2
  let tag := c.unpair.1
  let body := c.unpair.2
  if tag == 0 || tag == 1 then body == 0
  else if tag == 2 || tag == 3 || tag == 4 || tag == 5 then
    wfTerm m body.unpair.1 && wfTerm m body.unpair.2
  else if h67 : tag == 6 || tag == 7 then
    have hpos : 0 < c.unpair.1 := by simp only [tag, Bool.or_eq_true, beq_iff_eq] at h67; omega
    have : body.unpair.1 < c := unpair_right_left_lt hpos
    have : body.unpair.2 < c := unpair_right_right_lt hpos
    wfForm (m, body.unpair.1) && wfForm (m, body.unpair.2)
  else if h89 : tag == 8 || tag == 9 then
    have : body < c := unpair_right_lt_of_left_pos (by simp only [tag, Bool.or_eq_true, beq_iff_eq] at h89; omega)
    wfForm (m + 1, body)
  else false
termination_by p.2

lemma wfForm_primrec : Primrec wfForm := by
  let l : ℕ × ℕ → List (ℕ × ℕ) := fun p =>
    let tag := p.2.unpair.1
    let body := p.2.unpair.2
    if tag == 6 || tag == 7 then [(p.1, body.unpair.1), (p.1, body.unpair.2)]
    else if tag == 8 || tag == 9 then [(p.1 + 1, body)]
    else []
  let g : ℕ × ℕ → List Bool → Option Bool := fun p rs =>
    let m := p.1
    let c := p.2
    let tag := c.unpair.1
    let body := c.unpair.2
    some <|
      if tag == 0 || tag == 1 then body == 0
      else if tag == 2 || tag == 3 || tag == 4 || tag == 5 then
        wfTerm m body.unpair.1 && wfTerm m body.unpair.2
      else if tag == 6 || tag == 7 then
        rs.getD 0 false && rs.getD 1 false
      else if tag == 8 || tag == 9 then
        rs.getD 0 false
      else false
  have htag : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hbody : Primrec (fun p : ℕ × ℕ => p.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have h01 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 0 || p.2.unpair.1 == 1) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 0)) (Primrec.beq.comp htag (Primrec.const 1))
  have h25 : Primrec (fun p : ℕ × ℕ =>
      p.2.unpair.1 == 2 || p.2.unpair.1 == 3 || p.2.unpair.1 == 4 || p.2.unpair.1 == 5) :=
    primrec_boolOr (primrec_boolOr (primrec_boolOr
      (Primrec.beq.comp htag (Primrec.const 2)) (Primrec.beq.comp htag (Primrec.const 3)))
      (Primrec.beq.comp htag (Primrec.const 4))) (Primrec.beq.comp htag (Primrec.const 5))
  have h67 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 6 || p.2.unpair.1 == 7) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 6)) (Primrec.beq.comp htag (Primrec.const 7))
  have h89 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 8 || p.2.unpair.1 == 9) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 8)) (Primrec.beq.comp htag (Primrec.const 9))
  refine Primrec.nat_omega_rec' wfForm (m := Prod.snd) (l := l) (g := g) Primrec.snd ?_ ?_ ?_ ?_
  · have hb1 : Primrec (fun p : ℕ × ℕ => (p.1, p.2.unpair.2.unpair.1)) :=
      Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp hbody))
    have hb2 : Primrec (fun p : ℕ × ℕ => (p.1, p.2.unpair.2.unpair.2)) :=
      Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp hbody))
    have hb3 : Primrec (fun p : ℕ × ℕ => (p.1 + 1, p.2.unpair.2)) :=
      Primrec.pair (Primrec.succ.comp Primrec.fst) hbody
    exact primrec_iteBool h67
      (Primrec.list_cons.comp hb1 (Primrec.list_cons.comp hb2 (Primrec.const [])))
      (primrec_iteBool h89 (Primrec.list_cons.comp hb3 (Primrec.const [])) (Primrec.const []))
  · have hg' : Primrec (fun q : (ℕ × ℕ) × List Bool =>
        if q.1.2.unpair.1 == 0 || q.1.2.unpair.1 == 1 then q.1.2.unpair.2 == 0
        else if q.1.2.unpair.1 == 2 || q.1.2.unpair.1 == 3 || q.1.2.unpair.1 == 4 || q.1.2.unpair.1 == 5 then
          wfTerm q.1.1 q.1.2.unpair.2.unpair.1 && wfTerm q.1.1 q.1.2.unpair.2.unpair.2
        else if q.1.2.unpair.1 == 6 || q.1.2.unpair.1 == 7 then
          q.2.getD 0 false && q.2.getD 1 false
        else if q.1.2.unpair.1 == 8 || q.1.2.unpair.1 == 9 then
          q.2.getD 0 false
        else false) :=
      primrec_iteBool (h01.comp Primrec.fst)
        (Primrec.beq.comp (hbody.comp Primrec.fst) (Primrec.const 0)) <|
      primrec_iteBool (h25.comp Primrec.fst)
        (primrec_boolAnd
          (wfTerm_primrec.comp (Primrec.fst.comp Primrec.fst)
            (Primrec.fst.comp (Primrec.unpair.comp (hbody.comp Primrec.fst))))
          (wfTerm_primrec.comp (Primrec.fst.comp Primrec.fst)
            (Primrec.snd.comp (Primrec.unpair.comp (hbody.comp Primrec.fst))))) <|
      primrec_iteBool (h67.comp Primrec.fst)
        (primrec_boolAnd
          ((Primrec.list_getD false).comp Primrec.snd (Primrec.const 0))
          ((Primrec.list_getD false).comp Primrec.snd (Primrec.const 1))) <|
      primrec_iteBool (h89.comp Primrec.fst)
        ((Primrec.list_getD false).comp Primrec.snd (Primrec.const 0))
        (Primrec.const false)
    exact Primrec.to₂ (Primrec.option_some.comp hg')
  · intro ⟨m, c⟩ ⟨m', c'⟩ hm'
    dsimp only [l] at hm'
    split_ifs at hm' with h1 h2
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h1; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm'
      rcases hm' with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact unpair_right_left_lt hpos
      · exact unpair_right_right_lt hpos
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h2; omega
      simp only [List.mem_singleton, Prod.mk.injEq] at hm'
      rcases hm' with ⟨_, rfl⟩
      exact unpair_right_lt_of_left_pos hpos
    · simp at hm'
  · intro ⟨m, c⟩
    conv_rhs => rw [wfForm]
    dsimp only [g, l]
    by_cases h1 : (c.unpair.1 == 0 || c.unpair.1 == 1) = true
    · simp [h1]
    · by_cases h2 : (c.unpair.1 == 2 || c.unpair.1 == 3 || c.unpair.1 == 4 || c.unpair.1 == 5) = true
      · simp [h1, h2]
      · by_cases h3 : (c.unpair.1 == 6 || c.unpair.1 == 7) = true
        · simp [h1, h2, h3]
        · by_cases h4 : (c.unpair.1 == 8 || c.unpair.1 == 9) = true
          · simp [h1, h2, h3, h4]
          · simp [h1, h2, h3, h4]

lemma wfForm_iff (m c : ℕ) : wfForm (m, c) = true ↔ ∃ φ : Semiproposition ℒₛₑₜ m, encForm φ = c := by
  induction c using Nat.strong_induction_on generalizing m with
  | h c ih =>
    rw [wfForm]
    dsimp only
    constructor
    · intro h
      have hp := Nat.pair_unpair c
      split_ifs at h with h01 h25 h67 h89
      · simp only [Bool.or_eq_true, beq_iff_eq] at h01 h
        rcases h01 with h0 | h1
        · exact ⟨Semiformula.verum, by rw [encForm, ← hp, h0, h]⟩
        · exact ⟨Semiformula.falsum, by rw [encForm, ← hp, h1, h]⟩
      · simp only [Bool.and_eq_true, wfTerm_iff] at h
        obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := h
        simp only [Bool.or_eq_true, beq_iff_eq] at h25
        rcases h25 with ((h2 | h3) | h4) | h5
        · refine ⟨Semiformula.rel Language.Set.Rel.eq ![t1, t2], ?_⟩
          simp [encForm, ht1, ht2, ← h2, Nat.pair_unpair]
        · refine ⟨Semiformula.rel Language.Set.Rel.mem ![t1, t2], ?_⟩
          simp [encForm, ht1, ht2, ← h3, Nat.pair_unpair]
        · refine ⟨Semiformula.nrel Language.Set.Rel.eq ![t1, t2], ?_⟩
          simp [encForm, ht1, ht2, ← h4, Nat.pair_unpair]
        · refine ⟨Semiformula.nrel Language.Set.Rel.mem ![t1, t2], ?_⟩
          simp [encForm, ht1, ht2, ← h5, Nat.pair_unpair]
      · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h67; omega
        simp only [Bool.and_eq_true] at h
        obtain ⟨φ1, hφ1⟩ := (ih _ (unpair_right_left_lt hpos) m).mp h.1
        obtain ⟨φ2, hφ2⟩ := (ih _ (unpair_right_right_lt hpos) m).mp h.2
        simp only [Bool.or_eq_true, beq_iff_eq] at h67
        rcases h67 with h6 | h7
        · exact ⟨Semiformula.and φ1 φ2, by simp [encForm, hφ1, hφ2, ← h6, Nat.pair_unpair]⟩
        · exact ⟨Semiformula.or φ1 φ2, by simp [encForm, hφ1, hφ2, ← h7, Nat.pair_unpair]⟩
      · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h89; omega
        obtain ⟨φ1, hφ1⟩ := (ih _ (unpair_right_lt_of_left_pos hpos) (m + 1)).mp h
        simp only [Bool.or_eq_true, beq_iff_eq] at h89
        rcases h89 with h8 | h9
        · exact ⟨Semiformula.all φ1, by simp [encForm, hφ1, ← h8, Nat.pair_unpair]⟩
        · exact ⟨Semiformula.exs φ1, by simp [encForm, hφ1, ← h9, Nat.pair_unpair]⟩
    · rintro ⟨φ, rfl⟩
      cases φ with
      | verum => simp [encForm]
      | falsum => simp [encForm]
      | rel r v => cases r <;> simp [encForm, wfTerm_iff]
      | nrel r v => cases r <;> simp [encForm, wfTerm_iff]
      | and φ1 φ2 =>
        have hpos : 0 < (encForm (Semiformula.and φ1 φ2)).unpair.1 := by simp [encForm]
        have h1 := (ih (encForm φ1) (by simpa [encForm] using unpair_right_left_lt hpos) m).mpr ⟨φ1, rfl⟩
        have h2 := (ih (encForm φ2) (by simpa [encForm] using unpair_right_right_lt hpos) m).mpr ⟨φ2, rfl⟩
        simp [encForm, h1, h2]
      | or φ1 φ2 =>
        have hpos : 0 < (encForm (Semiformula.or φ1 φ2)).unpair.1 := by simp [encForm]
        have h1 := (ih (encForm φ1) (by simpa [encForm] using unpair_right_left_lt hpos) m).mpr ⟨φ1, rfl⟩
        have h2 := (ih (encForm φ2) (by simpa [encForm] using unpair_right_right_lt hpos) m).mpr ⟨φ2, rfl⟩
        simp [encForm, h1, h2]
      | all φ1 =>
        have hpos : 0 < (encForm (Semiformula.all φ1)).unpair.1 := by simp [encForm]
        have h1 := (ih (encForm φ1) (by simpa [encForm] using unpair_right_lt_of_left_pos hpos) (m + 1)).mpr ⟨φ1, rfl⟩
        simp [encForm, h1]
      | exs φ1 =>
        have hpos : 0 < (encForm (Semiformula.exs φ1)).unpair.1 := by simp [encForm]
        have h1 := (ih (encForm φ1) (by simpa [encForm] using unpair_right_lt_of_left_pos hpos) (m + 1)).mpr ⟨φ1, rfl⟩
        simp [encForm, h1]

/- ## 4. `codeNeg` -/

def codeNeg (c : ℕ) : ℕ :=
  let tag := c.unpair.1
  let body := c.unpair.2
  if tag == 0 then Nat.pair 1 0
  else if tag == 1 then Nat.pair 0 0
  else if tag == 2 then Nat.pair 4 body
  else if tag == 3 then Nat.pair 5 body
  else if tag == 4 then Nat.pair 2 body
  else if tag == 5 then Nat.pair 3 body
  else if h6 : tag == 6 then
    have hpos : 0 < c.unpair.1 := by simp only [tag, beq_iff_eq] at h6; omega
    have : body.unpair.1 < c := unpair_right_left_lt hpos
    have : body.unpair.2 < c := unpair_right_right_lt hpos
    Nat.pair 7 (Nat.pair (codeNeg body.unpair.1) (codeNeg body.unpair.2))
  else if h7 : tag == 7 then
    have hpos : 0 < c.unpair.1 := by simp only [tag, beq_iff_eq] at h7; omega
    have : body.unpair.1 < c := unpair_right_left_lt hpos
    have : body.unpair.2 < c := unpair_right_right_lt hpos
    Nat.pair 6 (Nat.pair (codeNeg body.unpair.1) (codeNeg body.unpair.2))
  else if h8 : tag == 8 then
    have : body < c := unpair_right_lt_of_left_pos (by simp only [tag, beq_iff_eq] at h8; omega)
    Nat.pair 9 (codeNeg body)
  else if h9 : tag == 9 then
    have : body < c := unpair_right_lt_of_left_pos (by simp only [tag, beq_iff_eq] at h9; omega)
    Nat.pair 8 (codeNeg body)
  else 0
termination_by c

lemma codeNeg_primrec : Primrec codeNeg := by
  let l : ℕ → List ℕ := fun c =>
    let tag := c.unpair.1
    let body := c.unpair.2
    if tag == 6 || tag == 7 then [body.unpair.1, body.unpair.2]
    else if tag == 8 || tag == 9 then [body]
    else []
  let g : ℕ → List ℕ → Option ℕ := fun c rs =>
    let tag := c.unpair.1
    let body := c.unpair.2
    some <|
      if tag == 0 then Nat.pair 1 0
      else if tag == 1 then Nat.pair 0 0
      else if tag == 2 then Nat.pair 4 body
      else if tag == 3 then Nat.pair 5 body
      else if tag == 4 then Nat.pair 2 body
      else if tag == 5 then Nat.pair 3 body
      else if tag == 6 then Nat.pair 7 (Nat.pair (rs.getD 0 0) (rs.getD 1 0))
      else if tag == 7 then Nat.pair 6 (Nat.pair (rs.getD 0 0) (rs.getD 1 0))
      else if tag == 8 then Nat.pair 9 (rs.getD 0 0)
      else if tag == 9 then Nat.pair 8 (rs.getD 0 0)
      else 0
  have htag : Primrec (fun c : ℕ => c.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hbody : Primrec (fun c : ℕ => c.unpair.2) := Primrec.snd.comp Primrec.unpair
  have h67 : Primrec (fun c : ℕ => c.unpair.1 == 6 || c.unpair.1 == 7) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 6)) (Primrec.beq.comp htag (Primrec.const 7))
  have h89 : Primrec (fun c : ℕ => c.unpair.1 == 8 || c.unpair.1 == 9) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 8)) (Primrec.beq.comp htag (Primrec.const 9))
  refine Primrec.nat_omega_rec' codeNeg (m := id) (l := l) (g := g) Primrec.id ?_ ?_ ?_ ?_
  · exact primrec_iteBool h67
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.unpair.comp hbody))
        (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.unpair.comp hbody)) (Primrec.const [])))
      (primrec_iteBool h89 (Primrec.list_cons.comp hbody (Primrec.const [])) (Primrec.const []))
  · have ht : Primrec (fun p : ℕ × List ℕ => p.1.unpair.1) := htag.comp Primrec.fst
    have hb : Primrec (fun p : ℕ × List ℕ => p.1.unpair.2) := hbody.comp Primrec.fst
    have hr0 : Primrec (fun p : ℕ × List ℕ => p.2.getD 0 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
    have hr1 : Primrec (fun p : ℕ × List ℕ => p.2.getD 1 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 1)
    have hg' : Primrec (fun p : ℕ × List ℕ =>
        if p.1.unpair.1 == 0 then Nat.pair 1 0
        else if p.1.unpair.1 == 1 then Nat.pair 0 0
        else if p.1.unpair.1 == 2 then Nat.pair 4 p.1.unpair.2
        else if p.1.unpair.1 == 3 then Nat.pair 5 p.1.unpair.2
        else if p.1.unpair.1 == 4 then Nat.pair 2 p.1.unpair.2
        else if p.1.unpair.1 == 5 then Nat.pair 3 p.1.unpair.2
        else if p.1.unpair.1 == 6 then Nat.pair 7 (Nat.pair (p.2.getD 0 0) (p.2.getD 1 0))
        else if p.1.unpair.1 == 7 then Nat.pair 6 (Nat.pair (p.2.getD 0 0) (p.2.getD 1 0))
        else if p.1.unpair.1 == 8 then Nat.pair 9 (p.2.getD 0 0)
        else if p.1.unpair.1 == 9 then Nat.pair 8 (p.2.getD 0 0)
        else 0) :=
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 0)) (Primrec.const (Nat.pair 1 0)) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 1)) (Primrec.const (Nat.pair 0 0)) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 2)) (primrec_natPair.comp (Primrec.const 4) hb) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 3)) (primrec_natPair.comp (Primrec.const 5) hb) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 4)) (primrec_natPair.comp (Primrec.const 2) hb) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 5)) (primrec_natPair.comp (Primrec.const 3) hb) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 6)) (primrec_natPair.comp (Primrec.const 7) (primrec_natPair.comp hr0 hr1)) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 7)) (primrec_natPair.comp (Primrec.const 6) (primrec_natPair.comp hr0 hr1)) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 8)) (primrec_natPair.comp (Primrec.const 9) hr0) <|
      primrec_iteBool (Primrec.beq.comp ht (Primrec.const 9)) (primrec_natPair.comp (Primrec.const 8) hr0) <|
        (Primrec.const 0)
    exact Primrec.to₂ (Primrec.option_some.comp hg')
  · intro c c' hc'
    dsimp only [l] at hc'
    split_ifs at hc' with h1 h2
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h1; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl
      · exact unpair_right_left_lt hpos
      · exact unpair_right_right_lt hpos
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h2; omega
      simp only [List.mem_singleton] at hc'
      subst hc'; exact unpair_right_lt_of_left_pos hpos
    · simp at hc'
  · intro c
    conv_rhs => rw [codeNeg]
    dsimp only [g, l]
    rcases Nat.lt_or_ge c.unpair.1 10 with hlt | hge
    · interval_cases h : c.unpair.1 <;> simp
    · have hne : ∀ k < 10, (c.unpair.1 == k) = false := fun k hk => by simp; omega
      simp [hne 0 (by decide), hne 1 (by decide), hne 2 (by decide), hne 3 (by decide),
        hne 4 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide),
        hne 8 (by decide), hne 9 (by decide)]

lemma codeNeg_encForm {m : ℕ} (φ : Semiproposition ℒₛₑₜ m) :
    codeNeg (encForm φ) = encForm (∼φ) := by
  induction φ with
  | verum => rw [codeNeg]; simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | falsum => rw [codeNeg]; simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg]
  | rel r v => cases r <;> (rw [codeNeg]; simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg])
  | nrel r v => cases r <;> (rw [codeNeg]; simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg])
  | and a b iha ihb =>
    rw [codeNeg]
    simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg, iha, ihb]
  | or a b iha ihb =>
    rw [codeNeg]
    simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg, iha, ihb]
  | all a iha =>
    rw [codeNeg]
    simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg, iha]
  | exs a iha =>
    rw [codeNeg]
    simp [encForm, HTilde.hTilde, Tilde.tilde, Semiformula.neg, iha]

/- ## 5. `codeRew` (Unified Rewriting for `shift`, `free`, `subst`, `fix`, `bShift`, `nest`) -/

def bShiftTerm (t : ℕ) : ℕ :=
  if t.unpair.1 == 0 then Nat.pair 0 (t.unpair.2 + 1) else t

lemma bShiftTerm_primrec : Primrec bShiftTerm :=
  primrec_iteBool (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
    (primrec_natPair.comp (Primrec.const 0) (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair)))
    Primrec.id

lemma bShiftTerm_encTerm {m : ℕ} (t : Semiterm ℒₛₑₜ ℕ m) :
    bShiftTerm (encTerm t) = encTerm (Rew.bShift t) := by
  cases t with
  | bvar i =>
    change (if (Nat.pair 0 i.val).unpair.1 == 0 then Nat.pair 0 ((Nat.pair 0 i.val).unpair.2 + 1) else Nat.pair 0 i.val) =
      Nat.pair 0 (i.val + 1)
    simp
  | fvar x =>
    change (if (Nat.pair 1 x).unpair.1 == 0 then Nat.pair 0 ((Nat.pair 1 x).unpair.2 + 1) else Nat.pair 1 x) =
      Nat.pair 1 x
    simp
  | func f _ => exact (f : Empty).elim

def applyTerm (bmap fmap : List ℕ) (fshift t : ℕ) : ℕ :=
  if t.unpair.1 == 0 then bmap.getD t.unpair.2 t
  else if decide (t.unpair.2 < fmap.length) then fmap.getD t.unpair.2 t
  else Nat.pair 1 (t.unpair.2 - fmap.length + fshift)

lemma applyTerm_primrec :
    Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => applyTerm p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hb : Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hf : Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hsh : Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => p.2) := Primrec.snd
  have ht1 := Primrec.fst.comp (Primrec.unpair.comp ht)
  have ht2 := Primrec.snd.comp (Primrec.unpair.comp ht)
  have hgetB : Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => p.1.1.getD p.2.unpair.2 p.2) := by
    refine (Primrec.option_casesOn (Primrec.list_getElem?.comp hb ht2) ht (Primrec.to₂ Primrec.snd)).of_eq ?_
    intro p; cases h : p.1.1[p.2.unpair.2]? <;> simp [List.getD_eq_getElem?_getD, h]
  have hgetF : Primrec (fun p : (List ℕ × List ℕ × ℕ) × ℕ => p.1.2.1.getD p.2.unpair.2 p.2) := by
    refine (Primrec.option_casesOn (Primrec.list_getElem?.comp hf ht2) ht (Primrec.to₂ Primrec.snd)).of_eq ?_
    intro p; cases h : p.1.2.1[p.2.unpair.2]? <;> simp [List.getD_eq_getElem?_getD, h]
  exact primrec_iteBool (Primrec.beq.comp ht1 (Primrec.const 0)) hgetB <|
    primrec_iteBool (Primrec.nat_lt.comp ht2 (Primrec.list_length.comp hf)).decide hgetF <|
    primrec_natPair.comp (Primrec.const 1)
      (Primrec.nat_add.comp (Primrec.nat_sub.comp ht2 (Primrec.list_length.comp hf)) hsh)

def qBmap (bmap : List ℕ) : List ℕ := Nat.pair 0 0 :: bmap.map bShiftTerm
def qFmap (fmap : List ℕ) : List ℕ := fmap.map bShiftTerm

lemma qBmap_primrec : Primrec qBmap :=
  Primrec.list_cons.comp (Primrec.const (Nat.pair 0 0))
    (Primrec.list_map Primrec.id (bShiftTerm_primrec.comp Primrec.snd).to₂)

lemma qFmap_primrec : Primrec qFmap :=
  Primrec.list_map Primrec.id (bShiftTerm_primrec.comp Primrec.snd).to₂

def codeRew (p : (List ℕ × List ℕ × ℕ) × ℕ) : ℕ :=
  let bmap := p.1.1
  let fmap := p.1.2.1
  let fshift := p.1.2.2
  let c := p.2
  let tag := c.unpair.1
  let body := c.unpair.2
  if tag == 0 || tag == 1 then c
  else if tag == 2 || tag == 3 || tag == 4 || tag == 5 then
    Nat.pair tag (Nat.pair (applyTerm bmap fmap fshift body.unpair.1)
      (applyTerm bmap fmap fshift body.unpair.2))
  else if h67 : tag == 6 || tag == 7 then
    have hpos : 0 < c.unpair.1 := by simp only [tag, Bool.or_eq_true, beq_iff_eq] at h67; omega
    have : body.unpair.1 < c := unpair_right_left_lt hpos
    have : body.unpair.2 < c := unpair_right_right_lt hpos
    Nat.pair tag (Nat.pair (codeRew ((bmap, fmap, fshift), body.unpair.1))
      (codeRew ((bmap, fmap, fshift), body.unpair.2)))
  else if h89 : tag == 8 || tag == 9 then
    have : body < c := unpair_right_lt_of_left_pos (by simp only [tag, Bool.or_eq_true, beq_iff_eq] at h89; omega)
    Nat.pair tag (codeRew ((qBmap bmap, qFmap fmap, fshift), body))
  else 0
termination_by p.2

private def decRewS (s : ℕ) : List ℕ × List ℕ × ℕ :=
  (Encodable.decode s).getD ([], [], 0)

private lemma decRewS_primrec : Primrec decRewS := by
  refine (Primrec.option_casesOn (Primrec.decode (α := List ℕ × List ℕ × ℕ))
    (Primrec.const ([], [], 0)) (Primrec.to₂ Primrec.snd)).of_eq ?_
  intro s
  change Option.casesOn (Encodable.decode (α := List ℕ × List ℕ × ℕ) s) ([], [], 0) (fun x => x) =
    (Encodable.decode (α := List ℕ × List ℕ × ℕ) s).getD ([], [], 0)
  cases Encodable.decode (α := List ℕ × List ℕ × ℕ) s <;> rfl

private def qRewSEnc (s : ℕ) : ℕ :=
  let st := decRewS s
  Encodable.encode (qBmap st.1, qFmap st.2.1, st.2.2)

private lemma qRewSEnc_primrec : Primrec qRewSEnc :=
  Primrec.encode.comp <|
    Primrec.pair (qBmap_primrec.comp (Primrec.fst.comp decRewS_primrec))
      (Primrec.pair (qFmap_primrec.comp (Primrec.fst.comp (Primrec.snd.comp decRewS_primrec)))
        (Primrec.snd.comp (Primrec.snd.comp decRewS_primrec)))

private def applyTermEnc (p : ℕ × ℕ) : ℕ :=
  let st := decRewS p.1
  applyTerm st.1 st.2.1 st.2.2 p.2

private lemma applyTermEnc_primrec : Primrec applyTermEnc :=
  applyTerm_primrec.comp (Primrec.pair (decRewS_primrec.comp Primrec.fst) Primrec.snd)

private def codeRewEnc (p : ℕ × ℕ) : ℕ := codeRew (decRewS p.1, p.2)

private lemma codeRewEnc_primrec : Primrec codeRewEnc := by
  let l : ℕ × ℕ → List (ℕ × ℕ) := fun p =>
    let tag := p.2.unpair.1
    let body := p.2.unpair.2
    if tag == 6 || tag == 7 then [(p.1, body.unpair.1), (p.1, body.unpair.2)]
    else if tag == 8 || tag == 9 then [(qRewSEnc p.1, body)]
    else []
  let g : ℕ × ℕ → List ℕ → Option ℕ := fun p rs =>
    let tag := p.2.unpair.1
    let body := p.2.unpair.2
    some <|
      if tag == 0 || tag == 1 then p.2
      else if tag == 2 || tag == 3 || tag == 4 || tag == 5 then
        Nat.pair tag (Nat.pair (applyTermEnc (p.1, body.unpair.1)) (applyTermEnc (p.1, body.unpair.2)))
      else if tag == 6 || tag == 7 then
        Nat.pair tag (Nat.pair (rs.getD 0 0) (rs.getD 1 0))
      else if tag == 8 || tag == 9 then
        Nat.pair tag (rs.getD 0 0)
      else 0
  have htag : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hbody : Primrec (fun p : ℕ × ℕ => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have h01 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 0 || p.2.unpair.1 == 1) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 0)) (Primrec.beq.comp htag (Primrec.const 1))
  have h25 : Primrec (fun p : ℕ × ℕ =>
      p.2.unpair.1 == 2 || p.2.unpair.1 == 3 || p.2.unpair.1 == 4 || p.2.unpair.1 == 5) :=
    primrec_boolOr (primrec_boolOr (primrec_boolOr
      (Primrec.beq.comp htag (Primrec.const 2)) (Primrec.beq.comp htag (Primrec.const 3)))
      (Primrec.beq.comp htag (Primrec.const 4))) (Primrec.beq.comp htag (Primrec.const 5))
  have h67 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 6 || p.2.unpair.1 == 7) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 6)) (Primrec.beq.comp htag (Primrec.const 7))
  have h89 : Primrec (fun p : ℕ × ℕ => p.2.unpair.1 == 8 || p.2.unpair.1 == 9) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 8)) (Primrec.beq.comp htag (Primrec.const 9))
  refine Primrec.nat_omega_rec' codeRewEnc (m := Prod.snd) (l := l) (g := g) Primrec.snd ?_ ?_ ?_ ?_
  · exact primrec_iteBool h67
      (Primrec.list_cons.comp (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp hbody)))
        (Primrec.list_cons.comp (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp hbody)))
          (Primrec.const [])))
      (primrec_iteBool h89
        (Primrec.list_cons.comp (Primrec.pair (qRewSEnc_primrec.comp Primrec.fst) hbody) (Primrec.const []))
        (Primrec.const []))
  · have ht : Primrec (fun p : (ℕ × ℕ) × List ℕ => p.1.2.unpair.1) := htag.comp Primrec.fst
    have hb : Primrec (fun p : (ℕ × ℕ) × List ℕ => p.1.2.unpair.2) := hbody.comp Primrec.fst
    have hs : Primrec (fun p : (ℕ × ℕ) × List ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
    have hr0 : Primrec (fun p : (ℕ × ℕ) × List ℕ => p.2.getD 0 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
    have hr1 : Primrec (fun p : (ℕ × ℕ) × List ℕ => p.2.getD 1 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 1)
    have hg' : Primrec (fun p : (ℕ × ℕ) × List ℕ =>
        if p.1.2.unpair.1 == 0 || p.1.2.unpair.1 == 1 then p.1.2
        else if p.1.2.unpair.1 == 2 || p.1.2.unpair.1 == 3 || p.1.2.unpair.1 == 4 || p.1.2.unpair.1 == 5 then
          Nat.pair p.1.2.unpair.1 (Nat.pair (applyTermEnc (p.1.1, p.1.2.unpair.2.unpair.1))
            (applyTermEnc (p.1.1, p.1.2.unpair.2.unpair.2)))
        else if p.1.2.unpair.1 == 6 || p.1.2.unpair.1 == 7 then
          Nat.pair p.1.2.unpair.1 (Nat.pair (p.2.getD 0 0) (p.2.getD 1 0))
        else if p.1.2.unpair.1 == 8 || p.1.2.unpair.1 == 9 then
          Nat.pair p.1.2.unpair.1 (p.2.getD 0 0)
        else 0) :=
      primrec_iteBool (h01.comp Primrec.fst) (Primrec.snd.comp Primrec.fst) <|
      primrec_iteBool (h25.comp Primrec.fst)
        (primrec_natPair.comp ht (primrec_natPair.comp
          (applyTermEnc_primrec.comp (Primrec.pair hs (Primrec.fst.comp (Primrec.unpair.comp hb))))
          (applyTermEnc_primrec.comp (Primrec.pair hs (Primrec.snd.comp (Primrec.unpair.comp hb)))))) <|
      primrec_iteBool (h67.comp Primrec.fst) (primrec_natPair.comp ht (primrec_natPair.comp hr0 hr1)) <|
      primrec_iteBool (h89.comp Primrec.fst) (primrec_natPair.comp ht hr0) <|
        (Primrec.const 0)
    exact Primrec.to₂ (Primrec.option_some.comp hg')
  · intro ⟨s, c⟩ ⟨s', c'⟩ hc'
    dsimp only [l] at hc'
    split_ifs at hc' with h1 h2
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h1; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc'
      rcases hc' with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact unpair_right_left_lt hpos
      · exact unpair_right_right_lt hpos
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h2; omega
      simp only [List.mem_singleton, Prod.mk.injEq] at hc'
      rcases hc' with ⟨_, rfl⟩
      exact unpair_right_lt_of_left_pos hpos
    · simp at hc'
  · intro ⟨s, c⟩
    dsimp only [codeRewEnc, g, l]
    conv_rhs => rw [codeRew]
    have hqDec : decRewS (qRewSEnc s) = (qBmap (decRewS s).1, qFmap (decRewS s).2.1, (decRewS s).2.2) := by
      simp only [decRewS, qRewSEnc, Encodable.encodek, Option.getD_some]
    by_cases h1 : (c.unpair.1 == 0 || c.unpair.1 == 1) = true
    · simp [h1]
    · by_cases h2 : (c.unpair.1 == 2 || c.unpair.1 == 3 || c.unpair.1 == 4 || c.unpair.1 == 5) = true
      · simp [h1, h2, applyTermEnc]
      · by_cases h3 : (c.unpair.1 == 6 || c.unpair.1 == 7) = true
        · simp [h1, h2, h3, codeRewEnc]
        · by_cases h4 : (c.unpair.1 == 8 || c.unpair.1 == 9) = true
          · simp [h1, h2, h3, h4, codeRewEnc, hqDec]
          · simp [h1, h2, h3, h4]

lemma codeRew_primrec : Primrec codeRew := by
  refine (codeRewEnc_primrec.comp (Primrec.pair (Primrec.encode.comp Primrec.fst) Primrec.snd)).of_eq ?_
  intro ⟨st, c⟩
  simp only [codeRewEnc, decRewS, Encodable.encodek, Option.getD_some]

def RewMatches {n1 n2 : ℕ} (ω : Rew ℒₛₑₜ ℕ n1 ℕ n2) (bmap fmap : List ℕ) (fshift : ℕ) : Prop :=
  (∀ i : Fin n1, applyTerm bmap fmap fshift (encTerm (#i : Semiterm ℒₛₑₜ ℕ n1)) = encTerm (ω #i)) ∧
  (∀ x : ℕ, applyTerm bmap fmap fshift (encTerm (&x : Semiterm ℒₛₑₜ ℕ n1)) = encTerm (ω &x))

lemma rewMatches_term {n1 n2 : ℕ} {ω : Rew ℒₛₑₜ ℕ n1 ℕ n2} {bmap fmap : List ℕ} {fshift : ℕ}
    (hm : RewMatches ω bmap fmap fshift) (t : Semiterm ℒₛₑₜ ℕ n1) :
    applyTerm bmap fmap fshift (encTerm t) = encTerm (ω t) := by
  cases t with
  | bvar i => exact hm.1 i
  | fvar x => exact hm.2 x
  | func f _ => exact (f : Empty).elim

lemma rewMatches_q {n1 n2 : ℕ} {ω : Rew ℒₛₑₜ ℕ n1 ℕ n2} {bmap fmap : List ℕ} {fshift : ℕ}
    (hbLen : bmap.length = n1) (hm : RewMatches ω bmap fmap fshift) :
    RewMatches ω.q (qBmap bmap) (qFmap fmap) fshift := by
  constructor
  · intro i
    cases i using Fin.cases with
    | zero =>
      change applyTerm (qBmap bmap) (qFmap fmap) fshift (Nat.pair 0 0) = Nat.pair 0 0
      simp [applyTerm, qBmap]
    | succ j =>
      have hj : j.val < bmap.length := by omega
      have h1 : applyTerm bmap fmap fshift (encTerm (#j : Semiterm ℒₛₑₜ ℕ n1)) = bmap.getD j.val (Nat.pair 0 j.val) := by
        simp [applyTerm, encTerm]
      have hget : bmap.getD j.val (Nat.pair 0 j.val) = bmap[j.val] := List.getD_eq_getElem _ _ hj
      have hm1 : bmap[j.val] = encTerm (ω #j) := by rw [← hget, ← h1]; exact hm.1 j
      change applyTerm (qBmap bmap) (qFmap fmap) fshift (Nat.pair 0 (j.val + 1)) = encTerm (Rew.bShift (ω #j))
      simp only [applyTerm, qBmap, Nat.unpair_pair, beq_self_eq_true, ↓reduceIte, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, hm1, bShiftTerm_encTerm]
  · intro x
    have hm2 := hm.2 x
    change applyTerm bmap fmap fshift (Nat.pair 1 x) = encTerm (ω &x) at hm2
    have h10 : ((1 : ℕ) == 0) = false := rfl
    simp only [applyTerm, Nat.unpair_pair, h10, Bool.false_eq_true, ↓reduceIte] at hm2
    change applyTerm (qBmap bmap) (qFmap fmap) fshift (Nat.pair 1 x) = encTerm (Rew.bShift (ω &x))
    simp only [applyTerm, Nat.unpair_pair, h10, Bool.false_eq_true, ↓reduceIte, qFmap, List.length_map]
    by_cases hx : x < fmap.length
    · simp only [hx, decide_true, ↓reduceIte] at hm2 ⊢
      rw [List.getD_eq_getElem _ _ (by simp [hx]), List.getElem_map]
      rw [List.getD_eq_getElem _ _ hx] at hm2
      rw [hm2, bShiftTerm_encTerm]
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte] at hm2 ⊢
      change encTerm (&(x - fmap.length + fshift) : Semiterm ℒₛₑₜ ℕ n2) = encTerm (ω &x) at hm2
      have heq := encTerm_inj hm2
      rw [← heq]
      rfl

lemma codeRew_encForm {n1 : ℕ} (φ : Semiproposition ℒₛₑₜ n1) :
    ∀ {n2 : ℕ} (ω : Rew ℒₛₑₜ ℕ n1 ℕ n2) (bmap fmap : List ℕ) (fshift : ℕ),
      bmap.length = n1 → RewMatches ω bmap fmap fshift →
      codeRew ((bmap, fmap, fshift), encForm φ) = encForm (ω ▹ φ) := by
  induction φ with
  | verum =>
    intro n2 ω bmap fmap fshift _ _
    change codeRew ((bmap, fmap, fshift), Nat.pair 0 0) = Nat.pair 0 0
    rw [codeRew]; simp
  | falsum =>
    intro n2 ω bmap fmap fshift _ _
    change codeRew ((bmap, fmap, fshift), Nat.pair 1 0) = Nat.pair 1 0
    rw [codeRew]; simp
  | rel r v =>
    intro n2 ω bmap fmap fshift _ hm
    cases r
    · change codeRew ((bmap, fmap, fshift), Nat.pair 2 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))) =
        Nat.pair 2 (Nat.pair (encTerm (ω (v 0))) (encTerm (ω (v 1))))
      rw [codeRew]; simp [rewMatches_term hm]
    · change codeRew ((bmap, fmap, fshift), Nat.pair 3 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))) =
        Nat.pair 3 (Nat.pair (encTerm (ω (v 0))) (encTerm (ω (v 1))))
      rw [codeRew]; simp [rewMatches_term hm]
  | nrel r v =>
    intro n2 ω bmap fmap fshift _ hm
    cases r
    · change codeRew ((bmap, fmap, fshift), Nat.pair 4 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))) =
        Nat.pair 4 (Nat.pair (encTerm (ω (v 0))) (encTerm (ω (v 1))))
      rw [codeRew]; simp [rewMatches_term hm]
    · change codeRew ((bmap, fmap, fshift), Nat.pair 5 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))) =
        Nat.pair 5 (Nat.pair (encTerm (ω (v 0))) (encTerm (ω (v 1))))
      rw [codeRew]; simp [rewMatches_term hm]
  | and a b iha ihb =>
    intro n2 ω bmap fmap fshift hlen hm
    change codeRew ((bmap, fmap, fshift), Nat.pair 6 (Nat.pair (encForm a) (encForm b))) =
      Nat.pair 6 (Nat.pair (encForm (ω ▹ a)) (encForm (ω ▹ b)))
    rw [codeRew]
    simp [iha ω bmap fmap fshift hlen hm, ihb ω bmap fmap fshift hlen hm]
  | or a b iha ihb =>
    intro n2 ω bmap fmap fshift hlen hm
    change codeRew ((bmap, fmap, fshift), Nat.pair 7 (Nat.pair (encForm a) (encForm b))) =
      Nat.pair 7 (Nat.pair (encForm (ω ▹ a)) (encForm (ω ▹ b)))
    rw [codeRew]
    simp [iha ω bmap fmap fshift hlen hm, ihb ω bmap fmap fshift hlen hm]
  | all a iha =>
    rename_i k
    intro n2 ω bmap fmap fshift hlen hm
    change codeRew ((bmap, fmap, fshift), Nat.pair 8 (encForm a)) = Nat.pair 8 (encForm (ω.q ▹ a))
    rw [codeRew]
    have hqLen : (qBmap bmap).length = k + 1 := by simp [qBmap, hlen]
    simp [iha ω.q (qBmap bmap) (qFmap fmap) fshift hqLen (rewMatches_q hlen hm)]
  | exs a iha =>
    rename_i k
    intro n2 ω bmap fmap fshift hlen hm
    change codeRew ((bmap, fmap, fshift), Nat.pair 9 (encForm a)) = Nat.pair 9 (encForm (ω.q ▹ a))
    rw [codeRew]
    have hqLen : (qBmap bmap).length = k + 1 := by simp [qBmap, hlen]
    simp [iha ω.q (qBmap bmap) (qFmap fmap) fshift hqLen (rewMatches_q hlen hm)]

/- ## 6. `codeFvSup`, `codeFixitr`, `codeAllClosure`, `codeUnivCl` -/

def fvSupTerm (t : ℕ) : ℕ :=
  if t.unpair.1 == 0 then 0 else t.unpair.2 + 1

lemma fvSupTerm_primrec : Primrec fvSupTerm :=
  primrec_iteBool (Primrec.beq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
    (Primrec.const 0) (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))

def codeFvSup (c : ℕ) : ℕ :=
  let tag := c.unpair.1
  let body := c.unpair.2
  if tag == 0 || tag == 1 then 0
  else if tag == 2 || tag == 3 || tag == 4 || tag == 5 then
    max (fvSupTerm body.unpair.1) (fvSupTerm body.unpair.2)
  else if h67 : tag == 6 || tag == 7 then
    have hpos : 0 < c.unpair.1 := by simp only [tag, Bool.or_eq_true, beq_iff_eq] at h67; omega
    have : body.unpair.1 < c := unpair_right_left_lt hpos
    have : body.unpair.2 < c := unpair_right_right_lt hpos
    max (codeFvSup body.unpair.1) (codeFvSup body.unpair.2)
  else if h89 : tag == 8 || tag == 9 then
    have : body < c := unpair_right_lt_of_left_pos (by simp only [tag, Bool.or_eq_true, beq_iff_eq] at h89; omega)
    codeFvSup body
  else 0
termination_by c

lemma codeFvSup_primrec : Primrec codeFvSup := by
  let l : ℕ → List ℕ := fun c =>
    let tag := c.unpair.1
    let body := c.unpair.2
    if tag == 6 || tag == 7 then [body.unpair.1, body.unpair.2]
    else if tag == 8 || tag == 9 then [body]
    else []
  let g : ℕ → List ℕ → Option ℕ := fun c rs =>
    let tag := c.unpair.1
    let body := c.unpair.2
    some <|
      if tag == 0 || tag == 1 then 0
      else if tag == 2 || tag == 3 || tag == 4 || tag == 5 then
        max (fvSupTerm body.unpair.1) (fvSupTerm body.unpair.2)
      else if tag == 6 || tag == 7 then max (rs.getD 0 0) (rs.getD 1 0)
      else if tag == 8 || tag == 9 then rs.getD 0 0
      else 0
  have htag : Primrec (fun c : ℕ => c.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hbody : Primrec (fun c : ℕ => c.unpair.2) := Primrec.snd.comp Primrec.unpair
  have h01 : Primrec (fun c : ℕ => c.unpair.1 == 0 || c.unpair.1 == 1) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 0)) (Primrec.beq.comp htag (Primrec.const 1))
  have h25 : Primrec (fun c : ℕ =>
      c.unpair.1 == 2 || c.unpair.1 == 3 || c.unpair.1 == 4 || c.unpair.1 == 5) :=
    primrec_boolOr (primrec_boolOr (primrec_boolOr
      (Primrec.beq.comp htag (Primrec.const 2)) (Primrec.beq.comp htag (Primrec.const 3)))
      (Primrec.beq.comp htag (Primrec.const 4))) (Primrec.beq.comp htag (Primrec.const 5))
  have h67 : Primrec (fun c : ℕ => c.unpair.1 == 6 || c.unpair.1 == 7) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 6)) (Primrec.beq.comp htag (Primrec.const 7))
  have h89 : Primrec (fun c : ℕ => c.unpair.1 == 8 || c.unpair.1 == 9) :=
    primrec_boolOr (Primrec.beq.comp htag (Primrec.const 8)) (Primrec.beq.comp htag (Primrec.const 9))
  refine Primrec.nat_omega_rec' codeFvSup (m := id) (l := l) (g := g) Primrec.id ?_ ?_ ?_ ?_
  · exact primrec_iteBool h67
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.unpair.comp hbody))
        (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.unpair.comp hbody)) (Primrec.const [])))
      (primrec_iteBool h89 (Primrec.list_cons.comp hbody (Primrec.const [])) (Primrec.const []))
  · have hb : Primrec (fun p : ℕ × List ℕ => p.1.unpair.2) := hbody.comp Primrec.fst
    have hr0 : Primrec (fun p : ℕ × List ℕ => p.2.getD 0 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
    have hr1 : Primrec (fun p : ℕ × List ℕ => p.2.getD 1 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 1)
    have hg' : Primrec (fun p : ℕ × List ℕ =>
        if p.1.unpair.1 == 0 || p.1.unpair.1 == 1 then 0
        else if p.1.unpair.1 == 2 || p.1.unpair.1 == 3 || p.1.unpair.1 == 4 || p.1.unpair.1 == 5 then
          max (fvSupTerm p.1.unpair.2.unpair.1) (fvSupTerm p.1.unpair.2.unpair.2)
        else if p.1.unpair.1 == 6 || p.1.unpair.1 == 7 then max (p.2.getD 0 0) (p.2.getD 1 0)
        else if p.1.unpair.1 == 8 || p.1.unpair.1 == 9 then p.2.getD 0 0
        else 0) :=
      primrec_iteBool (h01.comp Primrec.fst) (Primrec.const 0) <|
      primrec_iteBool (h25.comp Primrec.fst)
        (primrec_natMax (fvSupTerm_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hb)))
          (fvSupTerm_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp hb)))) <|
      primrec_iteBool (h67.comp Primrec.fst) (primrec_natMax hr0 hr1) <|
      primrec_iteBool (h89.comp Primrec.fst) hr0 (Primrec.const 0)
    exact Primrec.to₂ (Primrec.option_some.comp hg')
  · intro c c' hc'
    dsimp only [l] at hc'
    split_ifs at hc' with h1 h2
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h1; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl
      · exact unpair_right_left_lt hpos
      · exact unpair_right_right_lt hpos
    · have hpos : 0 < c.unpair.1 := by simp only [Bool.or_eq_true, beq_iff_eq] at h2; omega
      simp only [List.mem_singleton] at hc'
      subst hc'; exact unpair_right_lt_of_left_pos hpos
    · simp at hc'
  · intro c
    conv_rhs => rw [codeFvSup]
    dsimp only [g, l]
    by_cases h1 : (c.unpair.1 == 0 || c.unpair.1 == 1) = true
    · simp [h1]
    · by_cases h2 : (c.unpair.1 == 2 || c.unpair.1 == 3 || c.unpair.1 == 4 || c.unpair.1 == 5) = true
      · simp [h1, h2]
      · by_cases h3 : (c.unpair.1 == 6 || c.unpair.1 == 7) = true
        · simp [h1, h2, h3]
        · by_cases h4 : (c.unpair.1 == 8 || c.unpair.1 == 9) = true
          · simp [h1, h2, h3, h4]
          · simp [h1, h2, h3, h4]

private lemma finset_max_recBotCoe_union (s t : Finset ℕ) :
    (((s ∪ t).max).recBotCoe (0 : ℕ) Nat.succ : ℕ) =
      max (((s.max).recBotCoe (0 : ℕ) Nat.succ : ℕ)) (((t.max).recBotCoe (0 : ℕ) Nat.succ : ℕ)) := by
  rw [Finset.max_union]
  cases hs : s.max <;> cases ht : t.max
  · rfl
  · simp
  · simp
  · rename_i a b
    change Nat.succ (max a b) = max (Nat.succ a) (Nat.succ b)
    omega

private lemma fvSupTerm_encTerm {m : ℕ} (t : Semiterm ℒₛₑₜ ℕ m) :
    fvSupTerm (encTerm t) = (t.freeVariables.max).recBotCoe (0 : ℕ) Nat.succ := by
  cases t with
  | bvar i => simp [fvSupTerm, encTerm, Semiterm.freeVariables]
  | fvar x => simp [fvSupTerm, encTerm, Semiterm.freeVariables]
  | func f _ => exact (f : Empty).elim

lemma codeFvSup_encForm {m : ℕ} (φ : Semiproposition ℒₛₑₜ m) :
    codeFvSup (encForm φ) = φ.fvSup := by
  induction φ with
  | verum => rw [codeFvSup]; simp [encForm, Semiformula.fvSup, Semiformula.freeVariables]
  | falsum => rw [codeFvSup]; simp [encForm, Semiformula.fvSup, Semiformula.freeVariables]
  | rel r v =>
    cases r
    · have hfv : (Semiformula.rel Language.Set.Rel.eq v).freeVariables =
          (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      rw [codeFvSup]
      simp [encForm, Semiformula.fvSup, hfv, finset_max_recBotCoe_union, fvSupTerm_encTerm]
    · have hfv : (Semiformula.rel Language.Set.Rel.mem v).freeVariables =
          (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      rw [codeFvSup]
      simp [encForm, Semiformula.fvSup, hfv, finset_max_recBotCoe_union, fvSupTerm_encTerm]
  | nrel r v =>
    cases r
    · have hfv : (Semiformula.nrel Language.Set.Rel.eq v).freeVariables =
          (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      rw [codeFvSup]
      simp [encForm, Semiformula.fvSup, hfv, finset_max_recBotCoe_union, fvSupTerm_encTerm]
    · have hfv : (Semiformula.nrel Language.Set.Rel.mem v).freeVariables =
          (v 0).freeVariables ∪ (v 1).freeVariables := by
        ext x; simp [Semiformula.freeVariables, Fin.exists_fin_two]
      rw [codeFvSup]
      simp [encForm, Semiformula.fvSup, hfv, finset_max_recBotCoe_union, fvSupTerm_encTerm]
  | and a b iha ihb =>
    rw [codeFvSup]
    simp [encForm, Semiformula.fvSup, Semiformula.freeVariables, finset_max_recBotCoe_union]
    rw [iha, ihb]; rfl
  | or a b iha ihb =>
    rw [codeFvSup]
    simp [encForm, Semiformula.fvSup, Semiformula.freeVariables, finset_max_recBotCoe_union]
    rw [iha, ihb]; rfl
  | all a iha =>
    rw [codeFvSup]; simpa [encForm, Semiformula.fvSup, Semiformula.freeVariables] using iha
  | exs a iha =>
    rw [codeFvSup]; simpa [encForm, Semiformula.fvSup, Semiformula.freeVariables] using iha

def idBmap (n : ℕ) : List ℕ := (List.range n).map (Nat.pair 0)

lemma idBmap_primrec : Primrec idBmap :=
  Primrec.list_map Primrec.list_range (primrec_natPair.comp (Primrec.const 0) Primrec.snd).to₂

def codeFixitr (k c : ℕ) : ℕ :=
  k.rec c fun i ih => codeRew ((idBmap i, [Nat.pair 0 i], 0), ih)

lemma codeFixitr_primrec : Primrec₂ codeFixitr := by
  have hstep : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      codeRew ((idBmap p.2.1, [Nat.pair 0 p.2.1], 0), p.2.2)) := by
    have hi : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) := Primrec.fst.comp Primrec.snd
    exact codeRew_primrec.comp <| Primrec.pair
      (Primrec.pair (idBmap_primrec.comp hi)
        (Primrec.pair (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 0) hi) (Primrec.const []))
          (Primrec.const 0)))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.to₂ <| (Primrec.nat_rec' Primrec.fst Primrec.snd (Primrec.to₂ hstep)).of_eq fun _ => rfl

private lemma rew_id_app {m : ℕ} (φ : Semiproposition ℒₛₑₜ m) :
    (Rew.id : Rew ℒₛₑₜ ℕ m ℕ m) ▹ φ = φ := by
  induction φ with
  | verum | falsum => rfl
  | rel r v => rfl
  | nrel r v => rfl
  | and a b iha ihb =>
    change Semiformula.and (Rew.id ▹ a) (Rew.id ▹ b) = _
    rw [iha, ihb]
  | or a b iha ihb =>
    change Semiformula.or (Rew.id ▹ a) (Rew.id ▹ b) = _
    rw [iha, ihb]
  | all a iha =>
    rename_i k
    change Semiformula.all (Rew.id.q ▹ a) = _
    have hq : (Rew.id : Rew ℒₛₑₜ ℕ k ℕ k).q = Rew.id := by
      refine DFunLike.ext _ _ fun t => ?_
      cases t with
      | bvar i => cases i using Fin.cases <;> rfl
      | fvar x => rfl
      | func f _ => exact (f : Empty).elim
    rw [hq, iha]
  | exs a iha =>
    rename_i k
    change Semiformula.exs (Rew.id.q ▹ a) = _
    have hq : (Rew.id : Rew ℒₛₑₜ ℕ k ℕ k).q = Rew.id := by
      refine DFunLike.ext _ _ fun t => ?_
      cases t with
      | bvar i => cases i using Fin.cases <;> rfl
      | fvar x => rfl
      | func f _ => exact (f : Empty).elim
    rw [hq, iha]

private lemma rew_comp_app {m1 m2 m3 : ℕ} (ω2 : Rew ℒₛₑₜ ℕ m2 ℕ m3)
    (ω1 : Rew ℒₛₑₜ ℕ m1 ℕ m2) (ψ : Semiproposition ℒₛₑₜ m1) :
    (ω2.comp ω1) ▹ ψ = ω2 ▹ (ω1 ▹ ψ) := by
  induction ψ generalizing m2 m3 with
  | verum | falsum => rfl
  | rel r v => rfl
  | nrel r v => rfl
  | and a b iha ihb =>
    change Semiformula.and ((ω2.comp ω1) ▹ a) ((ω2.comp ω1) ▹ b) =
      Semiformula.and (ω2 ▹ (ω1 ▹ a)) (ω2 ▹ (ω1 ▹ b))
    rw [iha ω2 ω1, ihb ω2 ω1]
  | or a b iha ihb =>
    change Semiformula.or ((ω2.comp ω1) ▹ a) ((ω2.comp ω1) ▹ b) =
      Semiformula.or (ω2 ▹ (ω1 ▹ a)) (ω2 ▹ (ω1 ▹ b))
    rw [iha ω2 ω1, ihb ω2 ω1]
  | all a iha =>
    change Semiformula.all ((ω2.comp ω1).q ▹ a) = Semiformula.all (ω2.q ▹ (ω1.q ▹ a))
    have hq : (ω2.comp ω1).q = ω2.q.comp ω1.q := by
      refine DFunLike.ext _ _ fun t => ?_
      cases t with
      | bvar i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          change Rew.bShift (ω2 (ω1 #j)) = ω2.q (Rew.bShift (ω1 #j))
          cases ω1 #j with
          | bvar l => rfl
          | fvar x => rfl
          | func f _ => exact (f : Empty).elim
      | fvar x =>
        change Rew.bShift (ω2 (ω1 &x)) = ω2.q (Rew.bShift (ω1 &x))
        cases ω1 &x with
        | bvar l => rfl
        | fvar y => rfl
        | func f _ => exact (f : Empty).elim
      | func f _ => exact (f : Empty).elim
    rw [hq, iha ω2.q ω1.q]
  | exs a iha =>
    change Semiformula.exs ((ω2.comp ω1).q ▹ a) = Semiformula.exs (ω2.q ▹ (ω1.q ▹ a))
    have hq : (ω2.comp ω1).q = ω2.q.comp ω1.q := by
      refine DFunLike.ext _ _ fun t => ?_
      cases t with
      | bvar i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          change Rew.bShift (ω2 (ω1 #j)) = ω2.q (Rew.bShift (ω1 #j))
          cases ω1 #j with
          | bvar l => rfl
          | fvar x => rfl
          | func f _ => exact (f : Empty).elim
      | fvar x =>
        change Rew.bShift (ω2 (ω1 &x)) = ω2.q (Rew.bShift (ω1 &x))
        cases ω1 &x with
        | bvar l => rfl
        | fvar y => rfl
        | func f _ => exact (f : Empty).elim
      | func f _ => exact (f : Empty).elim
    rw [hq, iha ω2.q ω1.q]

lemma codeFixitr_encForm (k : ℕ) (φ : Proposition ℒₛₑₜ) :
    codeFixitr k (encForm φ) = encForm (Rew.fixitr 0 k ▹ φ) := by
  induction k with
  | zero =>
    change encForm φ = encForm (Rew.id ▹ φ)
    rw [rew_id_app]
  | succ k ih =>
    change codeRew ((idBmap k, [Nat.pair 0 k], 0), codeFixitr k (encForm φ)) =
      encForm (Rew.fix.comp (Rew.fixitr 0 k) ▹ φ)
    rw [ih, rew_comp_app]
    have hm : RewMatches (Rew.fix : Rew ℒₛₑₜ ℕ (0 + k) ℕ (0 + k + 1)) (idBmap k) [Nat.pair 0 k] 0 := by
      refine ⟨fun i => ?_, fun x => ?_⟩
      · have hi : i.val < (idBmap k).length := by simp [idBmap]; omega
        have hfix : (Rew.fix : Rew ℒₛₑₜ ℕ (0 + k) ℕ (0 + k + 1)) #i = #i.castSucc := rfl
        rw [hfix]
        simp only [applyTerm, encTerm, Nat.unpair_pair, beq_self_eq_true, ↓reduceIte]
        rw [List.getD_eq_getElem _ _ hi]
        simp [idBmap]
      · cases x with
        | zero =>
          change applyTerm (idBmap k) [Nat.pair 0 k] 0 (Nat.pair 1 0) = Nat.pair 0 (0 + k)
          simp [applyTerm]
        | succ x =>
          change applyTerm (idBmap k) [Nat.pair 0 k] 0 (Nat.pair 1 (x + 1)) = Nat.pair 1 x
          simp [applyTerm]
    exact codeRew_encForm _ Rew.fix (idBmap k) [Nat.pair 0 k] 0 (by simp [idBmap]) hm

def codeAllClosure (m c : ℕ) : ℕ :=
  m.rec c fun _ ih => Nat.pair 8 ih

lemma codeAllClosure_primrec : Primrec₂ codeAllClosure :=
  Primrec.to₂ <| (Primrec.nat_rec' Primrec.fst Primrec.snd
    (Primrec.to₂ <| primrec_natPair.comp (Primrec.const 8) (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

lemma codeAllClosure_step (m c : ℕ) :
    codeAllClosure (m + 1) c = codeAllClosure m (Nat.pair 8 c) := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    change Nat.pair 8 (codeAllClosure (m + 1) c) = Nat.pair 8 (codeAllClosure m (Nat.pair 8 c))
    rw [ih]

lemma codeAllClosure_encForm : ∀ {m : ℕ} (φ : Semiproposition ℒₛₑₜ m),
    codeAllClosure m (encForm φ) = encForm (∀¹* φ)
  | 0, _ => rfl
  | m + 1, φ => by
    rw [codeAllClosure_step]
    exact codeAllClosure_encForm (∀¹ φ)

def codeUnivCl (c : ℕ) : ℕ :=
  codeAllClosure (codeFvSup c) (codeFixitr (codeFvSup c) c)

lemma codeUnivCl_primrec : Primrec codeUnivCl :=
  codeAllClosure_primrec.comp codeFvSup_primrec (codeFixitr_primrec.comp codeFvSup_primrec Primrec.id)

lemma codeUnivCl_encForm (φ : Proposition ℒₛₑₜ) :
    codeUnivCl (encForm φ) = encClosed (Semiformula.univCl φ) := by
  rw [Semiformula.univCl, encClosed_toEmpty, Semiformula.univCl', codeUnivCl,
    codeFvSup_encForm, codeFixitr_encForm]
  have h := codeAllClosure_encForm (Rew.fixitr 0 φ.fvSup ▹ φ)
  simpa only [Nat.zero_add] using h

/- ## 7. `codeNestFormulae` and `codeNestFormulaeFunc` -/

def codeConj (xs : List ℕ) : ℕ :=
  xs.foldr (fun a b => Nat.pair 6 (Nat.pair a b)) (Nat.pair 0 0)

lemma codeConj_primrec : Primrec codeConj :=
  Primrec.list_foldr Primrec.id (Primrec.const (Nat.pair 0 0))
    (Primrec.to₂ <| primrec_natPair.comp (Primrec.const 6)
      (primrec_natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

lemma codeConj_eq {m : ℕ} : ∀ {n : ℕ} (v : Fin n → Semiproposition ℒₛₑₜ m),
    codeConj (List.ofFn fun i => encForm (v i)) = encForm (Matrix.conj v)
  | 0, _ => rfl
  | n + 1, v => by
    simp only [List.ofFn_succ, codeConj, List.foldr_cons, Matrix.conj]
    exact congrArg (Nat.pair 6) (congrArg (Nat.pair (encForm (v 0))) (codeConj_eq (Matrix.vecTail v)))

def codeImp (a b : ℕ) : ℕ := Nat.pair 7 (Nat.pair (codeNeg a) b)

lemma codeImp_primrec : Primrec₂ codeImp :=
  Primrec.to₂ <| primrec_natPair.comp (Primrec.const 7)
    (primrec_natPair.comp (codeNeg_primrec.comp Primrec.fst) Primrec.snd)

lemma codeImp_encForm {m : ℕ} (a b : Semiproposition ℒₛₑₜ m) :
    codeImp (encForm a) (encForm b) = encForm (a 🡒 b) := by
  simp only [codeImp, codeNeg_encForm]
  rfl

def codeAllItr (n c : ℕ) : ℕ := codeAllClosure n c

lemma codeAllItr_primrec : Primrec₂ codeAllItr := codeAllClosure_primrec

lemma codeAllItr_encForm : ∀ {n m : ℕ} (φ : Semiproposition ℒₛₑₜ (m + n)),
    codeAllItr n (encForm φ) = encForm (∀¹^[n] φ)
  | 0, _, _ => rfl
  | n + 1, m, φ => by
    change codeAllClosure (n + 1) (encForm φ) = encForm (∀¹^[n] (∀¹ φ))
    rw [codeAllClosure_step]
    exact codeAllItr_encForm (∀¹ φ)

private lemma emb_allItr : ∀ {r k : ℕ} (χ : Semisentence ℒₛₑₜ (k + r)),
    (Rewriting.emb (∀¹^[r] χ) : Semiproposition ℒₛₑₜ k) = ∀¹^[r] (Rewriting.emb χ)
  | 0, _, _ => rfl
  | r + 1, k, χ => by
    change (Rewriting.emb (∀¹^[r] (Semiformula.all χ)) : Semiproposition ℒₛₑₜ k) =
      ∀¹^[r] (Semiformula.all (Rewriting.emb χ))
    rw [emb_allItr (Semiformula.all χ), emb_all]

private lemma emb_conj : ∀ {r k : ℕ} (v : Fin r → Semisentence ℒₛₑₜ k),
    (Rewriting.emb (Matrix.conj v) : Semiproposition ℒₛₑₜ k) =
      Matrix.conj (fun i => Rewriting.emb (v i))
  | 0, _, _ => rfl
  | r + 1, k, v => by
    change Semiformula.and (Rewriting.emb (v 0)) (Rewriting.emb (Matrix.conj (Matrix.vecTail v))) =
      Semiformula.and (Rewriting.emb (v 0)) (Matrix.conj (Matrix.vecTail fun i => Rewriting.emb (v i)))
    rw [emb_conj (Matrix.vecTail v)]
    rfl

private lemma emb_subst_comm {k1 k2 : ℕ} (χ : Semisentence ℒₛₑₜ k1)
    (v : Fin k1 → Semiterm ℒₛₑₜ Empty k2) :
    (Rewriting.emb (Rewriting.subst χ v) : Semiproposition ℒₛₑₜ k2) =
      Rewriting.subst (Rewriting.emb χ) (fun i => Rew.emb (v i)) := by
  have hcomp : ∀ {a b : ℕ} (ω2 : Rew ℒₛₑₜ Empty b ℕ b) (ω1 : Rew ℒₛₑₜ Empty a Empty b)
      (ω3 : Rew ℒₛₑₜ ℕ a ℕ b) (ω4 : Rew ℒₛₑₜ Empty a ℕ a)
      (h : ∀ t, ω2 (ω1 t) = ω3 (ω4 t)) (ψ : Semisentence ℒₛₑₜ a),
      ω2 ▹ (ω1 ▹ ψ) = ω3 ▹ (ω4 ▹ ψ) := by
    intro a b ω2 ω1 ω3 ω4 h ψ
    induction ψ generalizing b with
    | verum | falsum => rfl
    | rel r w =>
      change Semiformula.rel r (fun i => ω2 (ω1 (w i))) = Semiformula.rel r (fun i => ω3 (ω4 (w i)))
      congr 1; funext i; exact h (w i)
    | nrel r w =>
      change Semiformula.nrel r (fun i => ω2 (ω1 (w i))) = Semiformula.nrel r (fun i => ω3 (ω4 (w i)))
      congr 1; funext i; exact h (w i)
    | and x y ihx ihy =>
      change Semiformula.and (ω2 ▹ (ω1 ▹ x)) (ω2 ▹ (ω1 ▹ y)) =
        Semiformula.and (ω3 ▹ (ω4 ▹ x)) (ω3 ▹ (ω4 ▹ y))
      rw [ihx ω2 ω1 ω3 ω4 h, ihy ω2 ω1 ω3 ω4 h]
    | or x y ihx ihy =>
      change Semiformula.or (ω2 ▹ (ω1 ▹ x)) (ω2 ▹ (ω1 ▹ y)) =
        Semiformula.or (ω3 ▹ (ω4 ▹ x)) (ω3 ▹ (ω4 ▹ y))
      rw [ihx ω2 ω1 ω3 ω4 h, ihy ω2 ω1 ω3 ω4 h]
    | all x ihx =>
      change Semiformula.all (ω2.q ▹ (ω1.q ▹ x)) = Semiformula.all (ω3.q ▹ (ω4.q ▹ x))
      refine congrArg Semiformula.all (ihx ω2.q ω1.q ω3.q ω4.q (fun t => ?_))
      cases t with
      | bvar i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          have hj := h #j
          change ω2.q (Rew.bShift (ω1 #j)) = ω3.q (Rew.bShift (ω4 #j))
          cases h1 : ω1 #j with
          | bvar l1 =>
            cases h4 : ω4 #j with
            | bvar l4 =>
              change Rew.bShift (ω2 #l1) = Rew.bShift (ω3 #l4)
              rw [h1, h4] at hj; rw [hj]
            | fvar z =>
              change Rew.bShift (ω2 #l1) = Rew.bShift (ω3 &z)
              rw [h1, h4] at hj; rw [hj]
            | func f _ => exact (f : Empty).elim
          | fvar x => exact x.elim
          | func f _ => exact (f : Empty).elim
      | fvar x => exact x.elim
      | func f _ => exact (f : Empty).elim
    | exs x ihx =>
      change Semiformula.exs (ω2.q ▹ (ω1.q ▹ x)) = Semiformula.exs (ω3.q ▹ (ω4.q ▹ x))
      refine congrArg Semiformula.exs (ihx ω2.q ω1.q ω3.q ω4.q (fun t => ?_))
      cases t with
      | bvar i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ j =>
          have hj := h #j
          change ω2.q (Rew.bShift (ω1 #j)) = ω3.q (Rew.bShift (ω4 #j))
          cases h1 : ω1 #j with
          | bvar l1 =>
            cases h4 : ω4 #j with
            | bvar l4 =>
              change Rew.bShift (ω2 #l1) = Rew.bShift (ω3 #l4)
              rw [h1, h4] at hj; rw [hj]
            | fvar z =>
              change Rew.bShift (ω2 #l1) = Rew.bShift (ω3 &z)
              rw [h1, h4] at hj; rw [hj]
            | func f _ => exact (f : Empty).elim
          | fvar x => exact x.elim
          | func f _ => exact (f : Empty).elim
      | fvar x => exact x.elim
      | func f _ => exact (f : Empty).elim
  refine hcomp Rew.emb (Rew.subst v) (Rew.subst fun i => Rew.emb (v i)) Rew.emb (fun t => ?_) χ
  cases t with
  | bvar i => rfl
  | fvar x => exact x.elim
  | func f _ => exact (f : Empty).elim

def codeNestFormulaeFunc (m : ℕ) (φCode : ℕ) (ΨCodes : List ℕ) : ℕ :=
  let n := ΨCodes.length
  let restTail := (List.range m).map fun j => Nat.pair 0 (j + 1 + n)
  let conjParts := (List.range n).map fun i =>
    codeRew ((Nat.pair 0 i :: restTail, [], 0), ΨCodes.getD i 0)
  let lhs := codeConj conjParts
  let phiBmap := Nat.pair 0 n :: (List.range n).map (Nat.pair 0)
  let rhs := codeRew ((phiBmap, [], 0), φCode)
  codeAllItr n (codeImp lhs rhs)

lemma codeNestFormulaeFunc_primrec :
    Primrec (fun p : ℕ × ℕ × List ℕ => codeNestFormulaeFunc p.1 p.2.1 p.2.2) := by
  have hm : Primrec (fun p : ℕ × ℕ × List ℕ => p.1) := Primrec.fst
  have hφ : Primrec (fun p : ℕ × ℕ × List ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hΨ : Primrec (fun p : ℕ × ℕ × List ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun p : ℕ × ℕ × List ℕ => p.2.2.length) := Primrec.list_length.comp hΨ
  have hrest : Primrec (fun p : ℕ × ℕ × List ℕ =>
      (List.range p.1).map fun j => Nat.pair 0 (j + 1 + p.2.2.length)) :=
    Primrec.list_map (Primrec.list_range.comp hm) <| Primrec.to₂ <|
      primrec_natPair.comp (Primrec.const 0)
        (Primrec.nat_add.comp (Primrec.succ.comp Primrec.snd) (hn.comp Primrec.fst))
  have hparts : Primrec (fun p : ℕ × ℕ × List ℕ =>
      (List.range p.2.2.length).map fun i =>
        codeRew ((Nat.pair 0 i :: ((List.range p.1).map fun j => Nat.pair 0 (j + 1 + p.2.2.length)), [], 0),
          p.2.2.getD i 0)) :=
    Primrec.list_map (Primrec.list_range.comp hn) <| Primrec.to₂ <|
      codeRew_primrec.comp <| Primrec.pair
        (Primrec.pair
          (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 0) Primrec.snd) (hrest.comp Primrec.fst))
          (Primrec.const ([], 0)))
        ((Primrec.list_getD 0).comp (hΨ.comp Primrec.fst) Primrec.snd)
  have hphiB : Primrec (fun p : ℕ × ℕ × List ℕ =>
      Nat.pair 0 p.2.2.length :: (List.range p.2.2.length).map (Nat.pair 0)) :=
    Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 0) hn) (idBmap_primrec.comp hn)
  have hrhs : Primrec (fun p : ℕ × ℕ × List ℕ =>
      codeRew ((Nat.pair 0 p.2.2.length :: (List.range p.2.2.length).map (Nat.pair 0), [], 0), p.2.1)) :=
    codeRew_primrec.comp (Primrec.pair (Primrec.pair hphiB (Primrec.const ([], 0))) hφ)
  exact codeAllItr_primrec.comp hn (codeImp_primrec.comp (codeConj_primrec.comp hparts) hrhs)

lemma codeNestFormulaeFunc_encClosed {m n : ℕ}
    (φ : Semisentence ℒₛₑₜ (n + 1)) (Ψ : Fin n → Semisentence ℒₛₑₜ (m + 1)) :
    codeNestFormulaeFunc m (encClosed φ) (List.ofFn fun i => encClosed (Ψ i)) =
      encClosed (φ.nestFormulaeFunc Ψ) := by
  unfold encClosed Semiformula.nestFormulaeFunc codeNestFormulaeFunc
  simp only [List.length_ofFn]
  rw [emb_allItr, ← codeAllItr_encForm, emb_imp, ← codeImp_encForm]
  congr 1
  congr 1
  · rw [emb_conj, ← codeConj_eq]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, emb_subst_comm]
    let bmap := Nat.pair 0 i :: (List.range m).map fun j => Nat.pair 0 (j + 1 + n)
    have hlen : bmap.length = m + 1 := by simp [bmap]
    let v : Fin (m + 1) → Semiterm ℒₛₑₜ ℕ ((m + 1) + n) :=
      fun k => (Rew.emb : Rew ℒₛₑₜ Empty ((m + 1) + n) ℕ ((m + 1) + n))
        ((#((⟨i, hi⟩ : Fin n).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat n)) k)
    have hm : RewMatches (Rew.subst v) bmap [] 0 := by
      refine ⟨fun k => ?_, fun x => ?_⟩
      · cases k using Fin.cases with
        | zero =>
          change applyTerm bmap [] 0 (Nat.pair 0 0) = Nat.pair 0 i
          simp [applyTerm, bmap]
        | succ j =>
          change applyTerm bmap [] 0 (Nat.pair 0 (j.val + 1)) = Nat.pair 0 (j.val + 1 + n)
          simp only [applyTerm, bmap, Nat.unpair_pair, beq_self_eq_true, ↓reduceIte, List.getD_cons_succ]
          rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_map, List.getElem_range]
      · change applyTerm bmap [] 0 (Nat.pair 1 x) = Nat.pair 1 x
        simp [applyTerm]
    rw [List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn]
    exact codeRew_encForm (Rewriting.emb (Ψ ⟨i, hi⟩)) (Rew.subst v) bmap [] 0 hlen hm
  · rw [emb_subst_comm]
    let bmap := Nat.pair 0 n :: (List.range n).map (Nat.pair 0)
    have hlen : bmap.length = n + 1 := by simp [bmap]
    let v : Fin (n + 1) → Semiterm ℒₛₑₜ ℕ ((m + 1) + n) :=
      fun k => (Rew.emb : Rew ℒₛₑₜ Empty ((m + 1) + n) ℕ ((m + 1) + n))
        ((#((0 : Fin (m + 1)).addNat n) :> fun i : Fin n => #(i.addCast m.succ)) k)
    have hm : RewMatches (Rew.subst v) bmap [] 0 := by
      refine ⟨fun k => ?_, fun x => ?_⟩
      · cases k using Fin.cases with
        | zero =>
          change applyTerm bmap [] 0 (Nat.pair 0 0) = Nat.pair 0 (0 + n)
          simp [applyTerm, bmap]
        | succ j =>
          change applyTerm bmap [] 0 (Nat.pair 0 (j.val + 1)) = Nat.pair 0 j.val
          simp only [applyTerm, bmap, Nat.unpair_pair, beq_self_eq_true, ↓reduceIte, List.getD_cons_succ]
          rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_map, List.getElem_range]
      · change applyTerm bmap [] 0 (Nat.pair 1 x) = Nat.pair 1 x
        simp [applyTerm]
    exact codeRew_encForm (Rewriting.emb φ) (Rew.subst v) bmap [] 0 hlen hm

def codeNestFormulae (m : ℕ) (φCode : ℕ) (ΨCodes : List ℕ) : ℕ :=
  let n := ΨCodes.length
  let restTail := (List.range m).map fun j => Nat.pair 0 (j + n)
  let conjParts := (List.range n).map fun i =>
    codeRew ((Nat.pair 0 i :: restTail, [], 0), ΨCodes.getD i 0)
  let lhs := codeConj conjParts
  let phiBmap := (List.range n).map (Nat.pair 0)
  let rhs := codeRew ((phiBmap, [], 0), φCode)
  codeAllItr n (codeImp lhs rhs)

lemma codeNestFormulae_primrec :
    Primrec (fun p : ℕ × ℕ × List ℕ => codeNestFormulae p.1 p.2.1 p.2.2) := by
  have hm : Primrec (fun p : ℕ × ℕ × List ℕ => p.1) := Primrec.fst
  have hφ : Primrec (fun p : ℕ × ℕ × List ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hΨ : Primrec (fun p : ℕ × ℕ × List ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun p : ℕ × ℕ × List ℕ => p.2.2.length) := Primrec.list_length.comp hΨ
  have hrest : Primrec (fun p : ℕ × ℕ × List ℕ =>
      (List.range p.1).map fun j => Nat.pair 0 (j + p.2.2.length)) :=
    Primrec.list_map (Primrec.list_range.comp hm) <| Primrec.to₂ <|
      primrec_natPair.comp (Primrec.const 0) (Primrec.nat_add.comp Primrec.snd (hn.comp Primrec.fst))
  have hparts : Primrec (fun p : ℕ × ℕ × List ℕ =>
      (List.range p.2.2.length).map fun i =>
        codeRew ((Nat.pair 0 i :: ((List.range p.1).map fun j => Nat.pair 0 (j + p.2.2.length)), [], 0),
          p.2.2.getD i 0)) :=
    Primrec.list_map (Primrec.list_range.comp hn) <| Primrec.to₂ <|
      codeRew_primrec.comp <| Primrec.pair
        (Primrec.pair
          (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 0) Primrec.snd) (hrest.comp Primrec.fst))
          (Primrec.const ([], 0)))
        ((Primrec.list_getD 0).comp (hΨ.comp Primrec.fst) Primrec.snd)
  have hrhs : Primrec (fun p : ℕ × ℕ × List ℕ =>
      codeRew (((List.range p.2.2.length).map (Nat.pair 0), [], 0), p.2.1)) :=
    codeRew_primrec.comp (Primrec.pair (Primrec.pair (idBmap_primrec.comp hn) (Primrec.const ([], 0))) hφ)
  exact codeAllItr_primrec.comp hn (codeImp_primrec.comp (codeConj_primrec.comp hparts) hrhs)

lemma codeNestFormulae_encClosed {m n : ℕ}
    (φ : Semisentence ℒₛₑₜ n) (Ψ : Fin n → Semisentence ℒₛₑₜ (m + 1)) :
    codeNestFormulae m (encClosed φ) (List.ofFn fun i => encClosed (Ψ i)) =
      encClosed (φ.nestFormulae Ψ) := by
  unfold encClosed Semiformula.nestFormulae codeNestFormulae
  simp only [List.length_ofFn]
  rw [emb_allItr, ← codeAllItr_encForm, emb_imp, ← codeImp_encForm]
  congr 1
  congr 1
  · rw [emb_conj, ← codeConj_eq]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, emb_subst_comm]
    let bmap := Nat.pair 0 i :: (List.range m).map fun j => Nat.pair 0 (j + n)
    have hlen : bmap.length = m + 1 := by simp [bmap]
    let v : Fin (m + 1) → Semiterm ℒₛₑₜ ℕ (m + n) :=
      fun k => (Rew.emb : Rew ℒₛₑₜ Empty (m + n) ℕ (m + n))
        ((#((⟨i, hi⟩ : Fin n).addCast m) :> fun j : Fin m => #(j.addNat n)) k)
    have hm : RewMatches (Rew.subst v) bmap [] 0 := by
      refine ⟨fun k => ?_, fun x => ?_⟩
      · cases k using Fin.cases with
        | zero =>
          change applyTerm bmap [] 0 (Nat.pair 0 0) = Nat.pair 0 i
          simp [applyTerm, bmap]
        | succ j =>
          change applyTerm bmap [] 0 (Nat.pair 0 (j.val + 1)) = Nat.pair 0 (j.val + n)
          simp only [applyTerm, bmap, Nat.unpair_pair, beq_self_eq_true, ↓reduceIte, List.getD_cons_succ]
          rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_map, List.getElem_range]
      · change applyTerm bmap [] 0 (Nat.pair 1 x) = Nat.pair 1 x
        simp [applyTerm]
    rw [List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn]
    exact codeRew_encForm (Rewriting.emb (Ψ ⟨i, hi⟩)) (Rew.subst v) bmap [] 0 hlen hm
  · rw [emb_subst_comm]
    let bmap := (List.range n).map (Nat.pair 0)
    have hlen : bmap.length = n := by simp [bmap]
    let v : Fin n → Semiterm ℒₛₑₜ ℕ (m + n) :=
      fun i => (Rew.emb : Rew ℒₛₑₜ Empty (m + n) ℕ (m + n)) (#(i.addCast m))
    have hm : RewMatches (Rew.subst v) bmap [] 0 := by
      refine ⟨fun i => ?_, fun x => ?_⟩
      · change applyTerm bmap [] 0 (Nat.pair 0 i.val) = Nat.pair 0 i.val
        simp only [applyTerm, bmap, Nat.unpair_pair, beq_self_eq_true, ↓reduceIte]
        rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_map, List.getElem_range]
      · change applyTerm bmap [] 0 (Nat.pair 1 x) = Nat.pair 1 x
        simp [applyTerm]
    exact codeRew_encForm (Rewriting.emb φ) (Rew.subst v) bmap [] 0 hlen hm

end C14H4RE

namespace C14H4RE

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open scoped Classical

/-
## Part A: Primitive-Recursive Code of `Constant14.halts (prependMachine L U)`
-/

def codeBVar (i : ℕ) : ℕ := Nat.pair 0 i
def codeEq (t1 t2 : ℕ) : ℕ := Nat.pair 2 (Nat.pair t1 t2)
def codeMem (t1 t2 : ℕ) : ℕ := Nat.pair 3 (Nat.pair t1 t2)
def codeAnd (a b : ℕ) : ℕ := Nat.pair 6 (Nat.pair a b)
def codeOr (a b : ℕ) : ℕ := Nat.pair 7 (Nat.pair a b)
def codeAll (a : ℕ) : ℕ := Nat.pair 8 a
def codeExs (a : ℕ) : ℕ := Nat.pair 9 a
def codeIff (a b : ℕ) : ℕ := codeAnd (codeImp a b) (codeImp b a)
def codeBexsMem (k a : ℕ) : ℕ := codeExs (codeAnd (codeMem (codeBVar 0) (codeBVar (k + 1))) a)
def codeNestFunc0 (c : ℕ) : ℕ := codeNestFormulaeFunc 0 c []

lemma codeAnd_primrec : Primrec₂ codeAnd :=
  Primrec.to₂ <| primrec_natPair.comp (Primrec.const 6) (primrec_natPair.comp Primrec.fst Primrec.snd)

lemma codeOr_primrec : Primrec₂ codeOr :=
  Primrec.to₂ <| primrec_natPair.comp (Primrec.const 7) (primrec_natPair.comp Primrec.fst Primrec.snd)

lemma codeAll_primrec : Primrec codeAll :=
  primrec_natPair.comp (Primrec.const 8) Primrec.id

lemma codeExs_primrec : Primrec codeExs :=
  primrec_natPair.comp (Primrec.const 9) Primrec.id

lemma codeIff_primrec : Primrec₂ codeIff :=
  Primrec.to₂ <| codeAnd_primrec.comp (codeImp_primrec.comp Primrec.fst Primrec.snd)
    (codeImp_primrec.comp Primrec.snd Primrec.fst)

lemma codeBexsMem_primrec (k : ℕ) : Primrec (codeBexsMem k) :=
  codeExs_primrec.comp <| codeAnd_primrec.comp
    (Primrec.const (codeMem (codeBVar 0) (codeBVar (k + 1)))) Primrec.id

lemma codeNestFunc0_primrec : Primrec codeNestFunc0 :=
  codeNestFormulaeFunc_primrec.comp <|
    Primrec.pair (Primrec.const 0) (Primrec.pair Primrec.id (Primrec.const []))

lemma codeNestFunc0_encClosed {m : ℕ} (φ : Semisentence ℒₛₑₜ 1) :
    codeNestFunc0 (encClosed φ) = encClosed (φ.nestFormulaeFunc (m := m) ![]) := by
  have h := codeNestFormulaeFunc_encClosed (m := m) (n := 0) φ ![]
  simpa only [codeNestFunc0, codeNestFormulaeFunc, List.ofFn_zero, List.length_nil,
    List.range_zero, List.map_nil] using h

lemma codeBexsMem_encForm {m : ℕ} (k : Fin m) (φ : Semiproposition ℒₛₑₜ (m + 1)) :
    codeBexsMem k.val (encForm φ) = encForm (Semiformula.bexsMem (#k : Semiterm ℒₛₑₜ ℕ m) φ) := by
  rfl

lemma codeBexsMem_encClosed {m : ℕ} (k : Fin m) (φ : Semisentence ℒₛₑₜ (m + 1)) :
    codeBexsMem k.val (encClosed φ) = encClosed (Semiformula.bexsMem (#k : Semiterm ℒₛₑₜ Empty m) φ) := by
  unfold encClosed Semiformula.bexsMem
  change codeBexsMem k.val (encForm (Rewriting.emb φ)) =
    encForm (Rewriting.emb (Semiformula.exs (Semiformula.and
      (Semiformula.rel Language.Set.Rel.mem ![#0, #(Fin.succ k)]) φ)))
  rw [emb_exs]
  rfl

lemma codeIff_encForm {m : ℕ} (a b : Semiproposition ℒₛₑₜ m) :
    codeIff (encForm a) (encForm b) = encForm (a 🡘 b) := by
  simp only [codeIff, codeAnd, codeImp_encForm]
  rfl

lemma codeIff_encClosed {m : ℕ} (a b : Semisentence ℒₛₑₜ m) :
    codeIff (encClosed a) (encClosed b) = encClosed (a 🡘 b) := by
  unfold encClosed
  change codeIff (encForm (Rewriting.emb a)) (encForm (Rewriting.emb b)) =
    encForm (Semiformula.and (Rewriting.emb (a 🡒 b)) (Rewriting.emb (b 🡒 a)))
  rw [emb_imp, emb_imp]
  exact codeIff_encForm (Rewriting.emb a) (Rewriting.emb b)

lemma encClosed_and {m : ℕ} (a b : Semisentence ℒₛₑₜ m) :
    encClosed (a ⋏ b) = codeAnd (encClosed a) (encClosed b) := rfl

lemma encClosed_all {m : ℕ} (a : Semisentence ℒₛₑₜ (m + 1)) :
    encClosed (∀¹ a) = codeAll (encClosed a) := by
  unfold encClosed
  change encForm (Rewriting.emb (Semiformula.all a)) = codeAll (encForm (Rewriting.emb a))
  rw [emb_all]; rfl

lemma encClosed_exs {m : ℕ} (a : Semisentence ℒₛₑₜ (m + 1)) :
    encClosed (∃¹ a) = codeExs (encClosed a) := by
  unfold encClosed
  change encForm (Rewriting.emb (Semiformula.exs a)) = codeExs (encForm (Rewriting.emb a))
  rw [emb_exs]; rfl

lemma encClosed_imp {m : ℕ} (a b : Semisentence ℒₛₑₜ m) :
    encClosed (a 🡒 b) = codeImp (encClosed a) (encClosed b) := by
  unfold encClosed
  rw [emb_imp, ← codeImp_encForm]

lemma encClosed_eq_bvar {m : ℕ} (i j : Fin m) :
    encClosed (Semiformula.Operator.Eq.eq.operator (![#i, #j] : Fin 2 → Semiterm ℒₛₑₜ Empty m)) =
      codeEq (codeBVar i.val) (codeBVar j.val) := rfl

lemma encClosed_mem_bvar {m : ℕ} (i j : Fin m) :
    encClosed (Semiformula.Operator.Mem.mem.operator (![#i, #j] : Fin 2 → Semiterm ℒₛₑₜ Empty m)) =
      codeMem (codeBVar i.val) (codeBVar j.val) := rfl

/- ### A.1. Numerals, Pairs, Triples, Finite Sets, Transition Entries -/

def codeNumeral (n : ℕ) : ℕ :=
  n.rec (encClosed Constant14.zero) fun _ ih =>
    codeNestFormulaeFunc 0 (encClosed FFL.FirstOrder.SetTheory.succ.dfn) [ih]

lemma codeNumeral_primrec : Primrec codeNumeral := by
  have hstep : Primrec₂ (fun (_ : ℕ) (p : ℕ × ℕ) =>
      codeNestFormulaeFunc 0 (encClosed FFL.FirstOrder.SetTheory.succ.dfn) [p.2]) :=
    Primrec.to₂ <| codeNestFormulaeFunc_primrec.comp <|
      Primrec.pair (Primrec.const 0) <|
      Primrec.pair (Primrec.const (encClosed FFL.FirstOrder.SetTheory.succ.dfn)) <|
      Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])
  exact (Primrec.nat_rec' Primrec.id (Primrec.const (encClosed Constant14.zero)) hstep).of_eq fun _ => rfl

lemma codeNumeral_encClosed (n : ℕ) : codeNumeral n = encClosed (Constant14.numeral n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change codeNestFormulaeFunc 0 (encClosed FFL.FirstOrder.SetTheory.succ.dfn) [codeNumeral n] =
      encClosed (FFL.FirstOrder.SetTheory.succ.dfn.nestFormulaeFunc ![Constant14.numeral n])
    rw [ih]
    have h := codeNestFormulaeFunc_encClosed (m := 0) (n := 1)
      FFL.FirstOrder.SetTheory.succ.dfn ![Constant14.numeral n]
    have hlist : (List.ofFn fun i : Fin 1 => encClosed (![Constant14.numeral n] i)) =
        [encClosed (Constant14.numeral n)] := rfl
    rw [hlist] at h
    exact h

def codeSetPair (x y : ℕ) : ℕ :=
  codeNestFormulaeFunc 0 (encClosed kpair.dfn) [x, y]

lemma codeSetPair_primrec : Primrec₂ codeSetPair :=
  Primrec.to₂ <| codeNestFormulaeFunc_primrec.comp <|
    Primrec.pair (Primrec.const 0) <|
    Primrec.pair (Primrec.const (encClosed kpair.dfn)) <|
    Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))

lemma codeSetPair_encClosed (x y : SetTheorySemisentence 1) :
    codeSetPair (encClosed x) (encClosed y) = encClosed (Constant14.setPair x y) := by
  have h := codeNestFormulaeFunc_encClosed (m := 0) (n := 2) kpair.dfn ![x, y]
  have hlist : (List.ofFn fun i : Fin 2 => encClosed (![x, y] i)) = [encClosed x, encClosed y] := rfl
  rw [hlist] at h
  exact h

def codeSetTriple (x y z : ℕ) : ℕ := codeSetPair x (codeSetPair y z)

lemma codeSetTriple_encClosed (x y z : SetTheorySemisentence 1) :
    codeSetTriple (encClosed x) (encClosed y) (encClosed z) = encClosed (Constant14.setTriple x y z) := by
  rw [codeSetTriple, codeSetPair_encClosed, codeSetPair_encClosed]
  rfl

def codeFiniteSet (xs : List ℕ) : ℕ :=
  xs.foldr (fun x acc => codeNestFormulaeFunc 0 (encClosed insert.dfn) [x, acc])
    (encClosed Constant14.zero)

lemma codeFiniteSet_primrec : Primrec codeFiniteSet :=
  Primrec.list_foldr Primrec.id (Primrec.const (encClosed Constant14.zero)) <|
    Primrec.to₂ <| codeNestFormulaeFunc_primrec.comp <|
      Primrec.pair (Primrec.const 0) <|
      Primrec.pair (Primrec.const (encClosed insert.dfn)) <|
      Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))

lemma codeFiniteSet_encClosed (xs : List (SetTheorySemisentence 1)) :
    codeFiniteSet (xs.map encClosed) = encClosed (Constant14.finiteSet xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, codeFiniteSet, List.foldr_cons]
    have hfold : List.foldr (fun x acc => codeNestFormulaeFunc 0 (encClosed insert.dfn) [x, acc])
        (encClosed Constant14.zero) (List.map encClosed xs) = codeFiniteSet (xs.map encClosed) := rfl
    rw [hfold, ih, Constant14.finiteSet]
    have h := codeNestFormulaeFunc_encClosed (m := 0) (n := 2) insert.dfn ![x, Constant14.finiteSet xs]
    have hlist : (List.ofFn fun i : Fin 2 => encClosed (![x, Constant14.finiteSet xs] i)) =
        [encClosed x, encClosed (Constant14.finiteSet xs)] := rfl
    rw [hlist] at h
    exact h

def encTuple5 (q s q' w d : ℕ) : ℕ :=
  Nat.pair q (Nat.pair s (Nat.pair q' (Nat.pair w d)))

def codeEntryOfNat (e : ℕ) : ℕ :=
  let q := e.unpair.1
  let r1 := e.unpair.2
  let s := r1.unpair.1
  let r2 := r1.unpair.2
  let q' := r2.unpair.1
  let r3 := r2.unpair.2
  let w := r3.unpair.1
  let d := r3.unpair.2
  codeSetPair (codeSetPair (codeNumeral q) (codeNumeral s))
    (codeSetTriple (codeNumeral q') (codeNumeral w) (codeNumeral d))

lemma codeEntryOfNat_primrec : Primrec codeEntryOfNat := by
  have hq : Primrec (fun e : ℕ => e.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr1 : Primrec (fun e : ℕ => e.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hs : Primrec (fun e : ℕ => e.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hr1)
  have hr2 : Primrec (fun e : ℕ => e.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hr1)
  have hq' : Primrec (fun e : ℕ => e.unpair.2.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hr2)
  have hr3 : Primrec (fun e : ℕ => e.unpair.2.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hr2)
  have hw : Primrec (fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hr3)
  have hd : Primrec (fun e : ℕ => e.unpair.2.unpair.2.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hr3)
  exact codeSetPair_primrec.comp
    (codeSetPair_primrec.comp (codeNumeral_primrec.comp hq) (codeNumeral_primrec.comp hs))
    (codeSetPair_primrec.comp (codeNumeral_primrec.comp hq')
      (codeSetPair_primrec.comp (codeNumeral_primrec.comp hw) (codeNumeral_primrec.comp hd)))

lemma codeEntryOfNat_encTuple5 (q s q' w d : ℕ) :
    codeEntryOfNat (encTuple5 q s q' w d) = encClosed (Constant14.transitionEntry q s q' w d) := by
  simp only [codeEntryOfNat, encTuple5, Nat.unpair_pair, codeNumeral_encClosed,
    codeSetPair_encClosed, codeSetTriple_encClosed, Constant14.transitionEntry]

/- ### A.2. Transition Table of `C14H4TM.prependMachine L U` -/

def uTransOf {N : ℕ} [NeZero N] (U : Machine (Fin 2) (Fin N)) : List ℕ :=
  (List.ofFn fun q : Fin N =>
    List.ofFn fun s : Fin 2 =>
      let o := Constant14.transitionCode U q s
      encTuple5 q.val s.val o.1 o.2.1 o.2.2).flatten

def shiftEntry (off e : ℕ) : ℕ :=
  let q := e.unpair.1
  let r1 := e.unpair.2
  let s := r1.unpair.1
  let r2 := r1.unpair.2
  let q' := r2.unpair.1
  let r3 := r2.unpair.2
  encTuple5 (off + q) s (off + q') r3.unpair.1 r3.unpair.2

lemma shiftEntry_primrec : Primrec₂ shiftEntry := by
  have hoff : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hq : Primrec (fun p : ℕ × ℕ => p.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hr1 : Primrec (fun p : ℕ × ℕ => p.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hs : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hr1)
  have hr2 : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hr1)
  have hq' : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp hr2)
  have hr3 : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp hr2)
  have hw : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hr3)
  have hd : Primrec (fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hr3)
  have hwd : Primrec (fun p : ℕ × ℕ =>
      Nat.pair p.2.unpair.2.unpair.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2.unpair.2.unpair.2) :=
    primrec_natPair.comp hw hd
  have hq'wd : Primrec (fun p : ℕ × ℕ =>
      Nat.pair (p.1 + p.2.unpair.2.unpair.2.unpair.1)
        (Nat.pair p.2.unpair.2.unpair.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2.unpair.2.unpair.2)) :=
    primrec_natPair.comp (Primrec.nat_add.comp hoff hq') hwd
  have hsq'wd : Primrec (fun p : ℕ × ℕ =>
      Nat.pair p.2.unpair.2.unpair.1
        (Nat.pair (p.1 + p.2.unpair.2.unpair.2.unpair.1)
          (Nat.pair p.2.unpair.2.unpair.2.unpair.2.unpair.1 p.2.unpair.2.unpair.2.unpair.2.unpair.2))) :=
    primrec_natPair.comp hs hq'wd
  unfold Primrec₂ shiftEntry encTuple5
  dsimp only
  exact primrec_natPair.comp (Primrec.nat_add.comp hoff hq) hsq'wd

def prependEntries (N : ℕ) (uTrans : List ℕ) (L : List Bool) : List ℕ :=
  let k := L.length
  let n := k + 1 + N
  let pref := (List.range k).flatMap fun q =>
    let w := if L.reverse.getD q false then 1 else 0
    [encTuple5 q 0 (q + 1) w 0, encTuple5 q 1 (q + 1) w 0]
  let bridge := [encTuple5 k 0 (k + 1) 0 2, encTuple5 k 1 (k + 1) 0 2]
  let uPart := uTrans.map (shiftEntry (k + 1))
  let haltPart := [encTuple5 n 0 n 0 1, encTuple5 n 1 n 1 1]
  pref ++ bridge ++ uPart ++ haltPart

lemma prependEntries_primrec (N : ℕ) (uTrans : List ℕ) :
    Primrec (prependEntries N uTrans) := by
  have hk : Primrec (fun L : List Bool => L.length) := Primrec.list_length
  have hn : Primrec (fun L : List Bool => L.length + 1 + N) :=
    Primrec.nat_add.comp (Primrec.succ.comp hk) (Primrec.const N)
  have hbit : Primrec (fun p : List Bool × ℕ => if p.1.reverse.getD p.2 false then 1 else 0) :=
    primrec_iteBool ((Primrec.list_getD false).comp (Primrec.list_reverse.comp Primrec.fst) Primrec.snd)
      (Primrec.const 1) (Primrec.const 0)
  have hprefFn : Primrec₂ (fun (L : List Bool) (q : ℕ) =>
      let w := if L.reverse.getD q false then 1 else 0
      [encTuple5 q 0 (q + 1) w 0, encTuple5 q 1 (q + 1) w 0]) := by
    have hq : Primrec (fun p : List Bool × ℕ => p.2) := Primrec.snd
    have hq1 : Primrec (fun p : List Bool × ℕ => p.2 + 1) := Primrec.succ.comp hq
    have he0 := primrec_natPair.comp hq (primrec_natPair.comp (Primrec.const 0)
      (primrec_natPair.comp hq1 (primrec_natPair.comp hbit (Primrec.const 0))))
    have he1 := primrec_natPair.comp hq (primrec_natPair.comp (Primrec.const 1)
      (primrec_natPair.comp hq1 (primrec_natPair.comp hbit (Primrec.const 0))))
    exact Primrec.to₂ <| Primrec.list_cons.comp he0 (Primrec.list_cons.comp he1 (Primrec.const []))
  have hpref : Primrec (fun L : List Bool =>
      (List.range L.length).flatMap fun q =>
        let w := if L.reverse.getD q false then 1 else 0
        [encTuple5 q 0 (q + 1) w 0, encTuple5 q 1 (q + 1) w 0]) :=
    Primrec.list_flatMap (Primrec.list_range.comp hk) hprefFn
  have hbridge : Primrec (fun L : List Bool =>
      [encTuple5 L.length 0 (L.length + 1) 0 2, encTuple5 L.length 1 (L.length + 1) 0 2]) := by
    have hk1 := Primrec.succ.comp hk
    have hb0 := primrec_natPair.comp hk (primrec_natPair.comp (Primrec.const 0)
      (primrec_natPair.comp hk1 (Primrec.const (Nat.pair 0 2))))
    have hb1 := primrec_natPair.comp hk (primrec_natPair.comp (Primrec.const 1)
      (primrec_natPair.comp hk1 (Primrec.const (Nat.pair 0 2))))
    exact Primrec.list_cons.comp hb0 (Primrec.list_cons.comp hb1 (Primrec.const []))
  have huPart : Primrec (fun L : List Bool => uTrans.map (shiftEntry (L.length + 1))) :=
    Primrec.list_map (Primrec.const uTrans)
      (shiftEntry_primrec.comp (Primrec.succ.comp (hk.comp Primrec.fst)) Primrec.snd).to₂
  have hhalt : Primrec (fun L : List Bool =>
      [encTuple5 (L.length + 1 + N) 0 (L.length + 1 + N) 0 1,
       encTuple5 (L.length + 1 + N) 1 (L.length + 1 + N) 1 1]) := by
    have hh0 := primrec_natPair.comp hn (primrec_natPair.comp (Primrec.const 0)
      (primrec_natPair.comp hn (Primrec.const (Nat.pair 0 1))))
    have hh1 := primrec_natPair.comp hn (primrec_natPair.comp (Primrec.const 1)
      (primrec_natPair.comp hn (Primrec.const (Nat.pair 1 1))))
    exact Primrec.list_cons.comp hh0 (Primrec.list_cons.comp hh1 (Primrec.const []))
  exact Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp hpref hbridge) huPart) hhalt

private lemma prependEntries_eq {N : ℕ} [NeZero N] (U : Machine (Fin 2) (Fin N)) (L : List Bool) :
    prependEntries N (uTransOf U) L =
      (List.ofFn fun q : Fin (L.length + 1 + N) =>
        List.ofFn fun s : Fin 2 =>
          let o := Constant14.transitionCode (C14H4TM.prependMachine L U) q s
          encTuple5 q.val s.val o.1 o.2.1 o.2.2).flatten ++
      [encTuple5 (L.length + 1 + N) 0 (L.length + 1 + N) 0 1,
       encTuple5 (L.length + 1 + N) 1 (L.length + 1 + N) 1 1] := by
  unfold prependEntries
  dsimp only
  congr 1
  let f : Fin (L.length + 1 + N) → List ℕ := fun q =>
    List.ofFn fun s : Fin 2 =>
      let o := Constant14.transitionCode (C14H4TM.prependMachine L U) q s
      encTuple5 q.val s.val o.1 o.2.1 o.2.2
  have hsplit : List.ofFn f =
      List.ofFn (fun q : Fin L.length => f ⟨q.val, by omega⟩) ++
      [f ⟨L.length, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩] ++
      List.ofFn (fun r : Fin N => f ⟨L.length + 1 + r.val, by omega⟩) := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi _
      simp only [List.length_ofFn] at hi
      by_cases h1 : i < L.length
      · simp [List.getElem_append_left, h1]
      · by_cases h2 : i = L.length
        · subst h2
          simp [List.getElem_append_right]
        · have hlen1 : ((List.ofFn fun q : Fin L.length => f ⟨q.val, by omega⟩) ++
              [f ⟨L.length, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩]).length = L.length + 1 := by
            simp
          rw [List.getElem_append_right (by omega)]
          simp only [hlen1, List.getElem_ofFn]
          congr 1; apply Fin.ext; dsimp; omega
  rw [hsplit, List.flatten_append, List.flatten_append]
  have hprefEq :
      ((List.range L.length).flatMap fun q =>
        let w := if L.reverse.getD q false then 1 else 0
        [encTuple5 q 0 (q + 1) w 0, encTuple5 q 1 (q + 1) w 0]) =
      (List.ofFn fun q : Fin L.length => f ⟨q.val, by omega⟩).flatten := by
    have hrange : ((List.range L.length).flatMap fun q =>
          let w := if L.reverse.getD q false then 1 else 0
          [encTuple5 q 0 (q + 1) w 0, encTuple5 q 1 (q + 1) w 0]) =
        (List.ofFn fun q : Fin L.length =>
          let w := if L.reverse.getD q.val false then 1 else 0
          [encTuple5 q.val 0 (q.val + 1) w 0, encTuple5 q.val 1 (q.val + 1) w 0]).flatten := by
      rw [List.flatten_eq_flatMap, List.ofFn_eq_map, List.flatMap_map]
      have hr : List.range L.length = (List.finRange L.length).map Fin.val := by
        apply List.ext_getElem (by simp)
        intro i hi _; simp
      rw [hr, List.flatMap_map]; rfl
    rw [hrange]
    refine congrArg List.flatten (List.ext_getElem (by simp) fun i hi _ => ?_)
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, f, List.ofFn_succ, List.ofFn_zero]
    have htc : ∀ s : Fin 2,
        Constant14.transitionCode (C14H4TM.prependMachine L U) ⟨i, by omega⟩ s =
          (i + 1, if L.reverse.getD i false then 1 else 0, 0) := by
      intro s
      simp only [Constant14.transitionCode, C14H4TM.prependMachine, dif_pos hi,
        Constant14.stateCode, Constant14.directionCode, C14H4TM.boolToFin2]
      cases L.reverse.getD i false <;> rfl
    simp [htc 0, htc 1]
  have hbridgeEq :
      [encTuple5 L.length 0 (L.length + 1) 0 2,
       encTuple5 L.length 1 (L.length + 1) 0 2] =
      ([f ⟨L.length, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩]).flatten := by
    simp only [List.flatten_singleton, f, List.ofFn_succ, List.ofFn_zero]
    have htc : ∀ s : Fin 2,
        Constant14.transitionCode (C14H4TM.prependMachine L U)
          ⟨L.length, by have := Nat.pos_of_ne_zero (NeZero.ne N); omega⟩ s =
          (L.length + 1, 0, 2) := by
      intro s
      simp only [Constant14.transitionCode, C14H4TM.prependMachine,
        dif_neg (Nat.lt_irrefl L.length), ↓reduceDIte,
        Constant14.stateCode, Constant14.directionCode]
      rfl
    simp [htc 0, htc 1]
  have huEq :
      (uTransOf U).map (shiftEntry (L.length + 1)) =
      (List.ofFn fun r : Fin N => f ⟨L.length + 1 + r.val, by omega⟩).flatten := by
    unfold uTransOf
    rw [List.map_flatten]
    refine congrArg List.flatten (List.ext_getElem (by simp) fun r hr _ => ?_)
    simp only [List.length_map, List.length_ofFn] at hr
    simp only [List.getElem_map, List.getElem_ofFn, f, List.ofFn_succ, List.ofFn_zero,
      List.map_cons, List.map_nil]
    have htc_tuple : ∀ s : Fin 2,
        Constant14.transitionCode (C14H4TM.prependMachine L U) ⟨L.length + 1 + r, by omega⟩ s =
          (L.length + 1 + (Constant14.transitionCode U ⟨r, hr⟩ s).1,
           (Constant14.transitionCode U ⟨r, hr⟩ s).2.1,
           (Constant14.transitionCode U ⟨r, hr⟩ s).2.2) := by
      intro s
      have h1 : ¬ L.length + 1 + r < L.length := by omega
      have h2 : ¬ L.length + 1 + r = L.length := by omega
      have hsub : (⟨L.length + 1 + r - (L.length + 1), by omega⟩ : Fin N) = ⟨r, hr⟩ :=
        Fin.ext (by dsimp; omega)
      simp only [Constant14.transitionCode, C14H4TM.prependMachine, dif_neg h1, dif_neg h2, hsub]
      cases hU : U ⟨r, hr⟩ s with
      | none =>
        simp [Constant14.directionCode]
      | some out =>
        rcases out with ⟨qOpt, stmt⟩
        cases qOpt with
        | none =>
          simp [Constant14.stateCode, Constant14.directionCode]
        | some q' =>
          simp [Constant14.stateCode, Constant14.directionCode]
    have hsh : ∀ a b c d e, shiftEntry (L.length + 1) (encTuple5 a b c d e) =
        encTuple5 (L.length + 1 + a) b (L.length + 1 + c) d e := by
      intro a b c d e; simp [shiftEntry, encTuple5]
    rw [hsh, hsh, htc_tuple 0, htc_tuple (Fin.succ 0)]
  rw [hprefEq, hbridgeEq, huEq]

lemma codeInstructionTable_prepend {N : ℕ} [NeZero N] (U : Machine (Fin 2) (Fin N)) (L : List Bool) :
    codeFiniteSet ((prependEntries N (uTransOf U) L).map codeEntryOfNat) =
      encClosed (Constant14.instructionTable (C14H4TM.prependMachine L U)) := by
  rw [Constant14.instructionTable, ← codeFiniteSet_encClosed]
  refine congrArg codeFiniteSet ?_
  rw [prependEntries_eq, Constant14.transitionEntries, List.map_append, List.map_append]
  have hmain :
      ((List.ofFn fun q : Fin (L.length + 1 + N) =>
          List.ofFn fun s : Fin 2 =>
            let o := Constant14.transitionCode (C14H4TM.prependMachine L U) q s
            encTuple5 q.val s.val o.1 o.2.1 o.2.2).flatten).map codeEntryOfNat =
      ((List.ofFn fun q : Fin (L.length + 1 + N) =>
          List.ofFn fun s : Fin 2 =>
            let o := Constant14.transitionCode (C14H4TM.prependMachine L U) q s
            Constant14.transitionEntry q.val s.val o.1 o.2.1 o.2.2).flatten).map encClosed := by
    rw [List.map_flatten, List.map_flatten]
    refine congrArg List.flatten (List.ext_getElem (by simp) fun i hi _ => ?_)
    simp only [List.length_map, List.length_ofFn] at hi
    simp only [List.getElem_map, List.getElem_ofFn]
    refine List.ext_getElem (by simp) fun j hj _ => ?_
    simp only [List.length_map, List.length_ofFn] at hj
    simp only [List.getElem_map, List.getElem_ofFn]
    exact codeEntryOfNat_encTuple5 _ _ _ _ _
  have hhalt :
      ([encTuple5 (L.length + 1 + N) 0 (L.length + 1 + N) 0 1,
        encTuple5 (L.length + 1 + N) 1 (L.length + 1 + N) 1 1]).map codeEntryOfNat =
      (List.ofFn fun symbol : Fin 2 =>
        Constant14.transitionEntry (L.length + 1 + N) symbol.val (L.length + 1 + N) symbol.val
          (Constant14.directionCode none)).map encClosed := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [List.map_cons, List.map_nil]
    have hdir : Constant14.directionCode none = 1 := rfl
    have hs0 : (0 : Fin 2).val = 0 := rfl
    have hs1 : (Fin.succ (0 : Fin 1) : Fin 2).val = 1 := rfl
    rw [hdir, hs0, hs1]
    exact congrArg₂ List.cons
      (codeEntryOfNat_encTuple5 (L.length + 1 + N) 0 (L.length + 1 + N) 0 1)
      (congrArg₂ List.cons
        (codeEntryOfNat_encTuple5 (L.length + 1 + N) 1 (L.length + 1 + N) 1 1)
        rfl)
  exact congrArg₂ List.append hmain hhalt

/- ### A.3. `codeConfigSet`, `codeNextConfig`, `codeNextStep`, `codeHalts` -/

def configTail : SetTheorySemisentence 3 :=
  prod.dfn.nestFormulaeFunc ![
    Constant14.integers.nestFormulaeFunc ![],
    function.dfn.nestFormulaeFunc ![
      (Constant14.numeral 2).nestFormulaeFunc ![],
      Constant14.integers.nestFormulaeFunc ![]]]

def codeConfigSet (n : ℕ) : ℕ :=
  codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 1))
    (codeAll (codeImp
      (codeNestFormulaeFunc 2 (encClosed prod.dfn)
        [codeNestFunc0 (codeNumeral n), encClosed configTail])
      (codeEq (codeBVar 1) (codeBVar 0)))))

private lemma primrec_nestFunc2_nat (m cPhi cArg1 : ℕ) :
    Primrec (fun x : ℕ => codeNestFormulaeFunc m cPhi [codeNestFunc0 x, cArg1]) := by
  have hL : Primrec (fun x : ℕ => [codeNestFunc0 x, cArg1]) :=
    Primrec.list_cons.comp codeNestFunc0_primrec (Primrec.const [cArg1])
  have h1 : Primrec (fun x : ℕ => (cPhi, [codeNestFunc0 x, cArg1])) :=
    Primrec.pair (Primrec.const cPhi) hL
  have h2 : Primrec (fun x : ℕ => (m, (cPhi, [codeNestFunc0 x, cArg1]))) :=
    Primrec.pair (Primrec.const m) h1
  exact codeNestFormulaeFunc_primrec.comp h2

private lemma primrec_nestFunc2 {α : Type*} [Primcodable α] (m cPhi cArg1 : ℕ)
    {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun a => codeNestFormulaeFunc m cPhi [codeNestFunc0 (f a), cArg1]) :=
  (primrec_nestFunc2_nat m cPhi cArg1).comp hf

private lemma primrec_nestFormConst_nat (m : ℕ) (args : List ℕ) :
    Primrec (fun x : ℕ => codeNestFormulae m x args) := by
  have h1 : Primrec (fun x : ℕ => (x, args)) := Primrec.pair Primrec.id (Primrec.const args)
  have h2 : Primrec (fun x : ℕ => (m, (x, args))) := Primrec.pair (Primrec.const m) h1
  exact codeNestFormulae_primrec.comp h2

private lemma primrec_nestFormConst {α : Type*} [Primcodable α] (m : ℕ) (args : List ℕ)
    {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun a => codeNestFormulae m (f a) args) :=
  (primrec_nestFormConst_nat m args).comp hf

lemma codeConfigSet_primrec : Primrec codeConfigSet :=
  codeAll_primrec.comp <| codeImp_primrec.comp (Primrec.const (codeEq (codeBVar 0) (codeBVar 1))) <|
    codeAll_primrec.comp <| codeImp_primrec.comp
      (primrec_nestFunc2 2 (encClosed prod.dfn) (encClosed configTail) codeNumeral_primrec)
      (Primrec.const (codeEq (codeBVar 1) (codeBVar 0)))

lemma codeConfigSet_encClosed (n : ℕ) :
    codeConfigSet n = encClosed (Constant14.configSet n) := by
  have hnest := codeNestFormulaeFunc_encClosed (m := 2) (n := 2) prod.dfn
    ![(Constant14.numeral n).nestFormulaeFunc ![], configTail]
  have hlist : (List.ofFn fun i : Fin 2 =>
      encClosed (![(Constant14.numeral n).nestFormulaeFunc (m := 2) ![], configTail] i)) =
      [encClosed ((Constant14.numeral n).nestFormulaeFunc (m := 2) ![]), encClosed configTail] := rfl
  rw [hlist] at hnest
  have hdef : Constant14.configSet n =
      ∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #1] 🡒
        ∀¹ (prod.dfn.nestFormulaeFunc (m := 2) ![(Constant14.numeral n).nestFormulaeFunc (m := 2) ![], configTail] 🡒
          Semiformula.Operator.Eq.eq.operator ![#1, #0])) := rfl
  rw [hdef, encClosed_all, encClosed_imp, encClosed_all, encClosed_imp,
    encClosed_eq_bvar (0 : Fin 2) (1 : Fin 2), encClosed_eq_bvar (1 : Fin 3) (0 : Fin 3),
    ← hnest, ← codeNestFunc0_encClosed (m := 2), ← codeNumeral_encClosed]
  rfl

def nextConfigArg : SetTheorySemisentence 5 :=
  kpair.dfn.nestFormulaeFunc ![
    kpair.π₁.dfn.nestFormulaeFunc ![Semiformula.Operator.Eq.eq.operator ![#0, #4]],
    value.dfn.nestFormulaeFunc ![
      kpair.π₂.dfn.nestFormulaeFunc ![
        kpair.π₂.dfn.nestFormulaeFunc ![Semiformula.Operator.Eq.eq.operator ![#0, #4]]],
      kpair.π₁.dfn.nestFormulaeFunc ![
        kpair.π₂.dfn.nestFormulaeFunc ![Semiformula.Operator.Eq.eq.operator ![#0, #4]]]]]

def nextConfigRest : SetTheorySemisentence 3 :=
  f“t z' z.
    !kpair.π₁.dfn z' = !kpair.π₁.dfn t ∧
    ((!kpair.π₂.dfn (!kpair.π₂.dfn t) = (!(Constant14.numeral 0)) ∧
        !Constant14.integerPred.dfn (!kpair.π₁.dfn (!kpair.π₂.dfn z'))
          (!kpair.π₁.dfn (!kpair.π₂.dfn z))) ∨
      (!kpair.π₂.dfn (!kpair.π₂.dfn t) = (!(Constant14.numeral 1)) ∧
        !kpair.π₁.dfn (!kpair.π₂.dfn z') = !kpair.π₁.dfn (!kpair.π₂.dfn z)) ∨
      (!kpair.π₂.dfn (!kpair.π₂.dfn t) = (!(Constant14.numeral 2)) ∧
        !Constant14.integerSucc.dfn (!kpair.π₁.dfn (!kpair.π₂.dfn z'))
          (!kpair.π₁.dfn (!kpair.π₂.dfn z)))) ∧
    !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z'))
        (!kpair.π₁.dfn (!kpair.π₂.dfn z)) =
      !kpair.π₁.dfn (!kpair.π₂.dfn t) ∧
    ∀ k ∈ !Constant14.integers,
      k ≠ !kpair.π₁.dfn (!kpair.π₂.dfn z) →
        !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z')) k =
          !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn z)) k”

def codeNextConfig (n instrCode : ℕ) : ℕ :=
  let cs := codeNestFunc0 (codeConfigSet n)
  let p1 := codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 2))
    (codeAll (codeImp cs (codeMem (codeBVar 1) (codeBVar 0)))))
  let p2 := codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 1))
    (codeAll (codeImp cs (codeMem (codeBVar 1) (codeBVar 0)))))
  let p3 := codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 1))
    (codeAll (codeImp
      (codeNestFormulaeFunc 4 (encClosed value.dfn)
        [codeNestFunc0 instrCode, encClosed nextConfigArg])
      (codeEq (codeBVar 1) (codeBVar 0)))))
  codeAnd p1 (codeAnd p2 (codeExs (codeAnd p3 (encClosed nextConfigRest))))

lemma codeNextConfig_primrec : Primrec₂ codeNextConfig := by
  have hcs : Primrec (fun p : ℕ × ℕ => codeNestFunc0 (codeConfigSet p.1)) :=
    codeNestFunc0_primrec.comp (codeConfigSet_primrec.comp Primrec.fst)
  have hp1 : Primrec (fun p : ℕ × ℕ =>
      codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 2))
        (codeAll (codeImp (codeNestFunc0 (codeConfigSet p.1)) (codeMem (codeBVar 1) (codeBVar 0)))))) :=
    codeAll_primrec.comp <| codeImp_primrec.comp (Primrec.const (codeEq (codeBVar 0) (codeBVar 2))) <|
      codeAll_primrec.comp <| codeImp_primrec.comp hcs (Primrec.const (codeMem (codeBVar 1) (codeBVar 0)))
  have hp2 : Primrec (fun p : ℕ × ℕ =>
      codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 1))
        (codeAll (codeImp (codeNestFunc0 (codeConfigSet p.1)) (codeMem (codeBVar 1) (codeBVar 0)))))) :=
    codeAll_primrec.comp <| codeImp_primrec.comp (Primrec.const (codeEq (codeBVar 0) (codeBVar 1))) <|
      codeAll_primrec.comp <| codeImp_primrec.comp hcs (Primrec.const (codeMem (codeBVar 1) (codeBVar 0)))
  have hval : Primrec (fun p : ℕ × ℕ =>
      codeNestFormulaeFunc 4 (encClosed value.dfn) [codeNestFunc0 p.2, encClosed nextConfigArg]) :=
    primrec_nestFunc2 4 (encClosed value.dfn) (encClosed nextConfigArg) Primrec.snd
  have hp3 : Primrec (fun p : ℕ × ℕ =>
      codeAll (codeImp (codeEq (codeBVar 0) (codeBVar 1))
        (codeAll (codeImp
          (codeNestFormulaeFunc 4 (encClosed value.dfn)
            [codeNestFunc0 p.2, encClosed nextConfigArg])
          (codeEq (codeBVar 1) (codeBVar 0)))))) :=
    codeAll_primrec.comp <| codeImp_primrec.comp (Primrec.const (codeEq (codeBVar 0) (codeBVar 1))) <|
      codeAll_primrec.comp <| codeImp_primrec.comp hval (Primrec.const (codeEq (codeBVar 1) (codeBVar 0)))
  unfold Primrec₂ codeNextConfig
  dsimp only
  exact codeAnd_primrec.comp hp1 <| codeAnd_primrec.comp hp2 <|
    codeExs_primrec.comp <| codeAnd_primrec.comp hp3 (Primrec.const (encClosed nextConfigRest))

lemma codeNextConfig_encClosed (n : ℕ) (instr : SetTheorySemisentence 1) :
    codeNextConfig n (encClosed instr) = encClosed (Constant14.nextConfig n instr) := by
  have hval := codeNestFormulaeFunc_encClosed (m := 4) (n := 2) value.dfn
    ![instr.nestFormulaeFunc ![], nextConfigArg]
  have hlist : (List.ofFn fun i : Fin 2 =>
      encClosed (![instr.nestFormulaeFunc (m := 4) ![], nextConfigArg] i)) =
      [encClosed (instr.nestFormulaeFunc (m := 4) ![]), encClosed nextConfigArg] := rfl
  rw [hlist] at hval
  have hdef : Constant14.nextConfig n instr =
      (∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #2] 🡒
          ∀¹ ((Constant14.configSet n).nestFormulaeFunc (m := 3) ![] 🡒
            Semiformula.Operator.Mem.mem.operator ![#1, #0]))) ⋏
        ((∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #1] 🡒
            ∀¹ ((Constant14.configSet n).nestFormulaeFunc (m := 3) ![] 🡒
              Semiformula.Operator.Mem.mem.operator ![#1, #0]))) ⋏
          (∃¹ ((∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #1] 🡒
              ∀¹ (value.dfn.nestFormulaeFunc (m := 4) ![instr.nestFormulaeFunc (m := 4) ![], nextConfigArg] 🡒
                Semiformula.Operator.Eq.eq.operator ![#1, #0]))) ⋏
            nextConfigRest))) := rfl
  rw [hdef, encClosed_and, encClosed_and, encClosed_exs, encClosed_and,
    encClosed_all, encClosed_imp, encClosed_all, encClosed_imp,
    encClosed_all, encClosed_imp, encClosed_all, encClosed_imp,
    encClosed_all, encClosed_imp, encClosed_all, encClosed_imp,
    encClosed_eq_bvar (0 : Fin 3) (2 : Fin 3), encClosed_mem_bvar (1 : Fin 4) (0 : Fin 4),
    encClosed_eq_bvar (0 : Fin 3) (1 : Fin 3),
    encClosed_eq_bvar (0 : Fin 4) (1 : Fin 4), encClosed_eq_bvar (1 : Fin 5) (0 : Fin 5),
    ← hval, ← codeNestFunc0_encClosed (m := 3), ← codeNestFunc0_encClosed (m := 4),
    ← codeConfigSet_encClosed]
  rfl

def nextStepLhs : SetTheorySemisentence 2 :=
  ∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #1] 🡒
    ∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #3] 🡒
      Semiformula.Operator.Mem.mem.operator ![#1, #0]))

def nextStepPairEq : SetTheorySemisentence 6 :=
  ∀¹ (Semiformula.Operator.Eq.eq.operator ![#0, #5] 🡒
    ∀¹ (kpair.dfn.nestFormulaeFunc ![
        Semiformula.Operator.Eq.eq.operator ![#0, #4],
        Semiformula.Operator.Eq.eq.operator ![#0, #2]] 🡒
      Semiformula.Operator.Eq.eq.operator ![#1, #0]))

def codeNextStep (n instrCode : ℕ) : ℕ :=
  let cs := codeNestFunc0 (codeConfigSet n)
  let body := codeAnd (encClosed nextStepPairEq)
    (codeNestFormulae 6 (codeNextConfig n instrCode)
      [codeEq (codeBVar 0) (codeBVar 1), codeEq (codeBVar 0) (codeBVar 3)])
  let rhs := codeAll (codeImp cs (codeBexsMem 0 (codeAll (codeImp cs (codeBexsMem 0 body)))))
  codeAll (codeIff (encClosed nextStepLhs) rhs)

lemma codeNextStep_primrec : Primrec₂ codeNextStep := by
  have hcs : Primrec (fun p : ℕ × ℕ => codeNestFunc0 (codeConfigSet p.1)) :=
    codeNestFunc0_primrec.comp (codeConfigSet_primrec.comp Primrec.fst)
  have hnf : Primrec (fun p : ℕ × ℕ =>
      codeNestFormulae 6 (codeNextConfig p.1 p.2)
        [codeEq (codeBVar 0) (codeBVar 1), codeEq (codeBVar 0) (codeBVar 3)]) :=
    primrec_nestFormConst 6 [codeEq (codeBVar 0) (codeBVar 1), codeEq (codeBVar 0) (codeBVar 3)]
      codeNextConfig_primrec
  have hbody : Primrec (fun p : ℕ × ℕ =>
      codeAnd (encClosed nextStepPairEq)
        (codeNestFormulae 6 (codeNextConfig p.1 p.2)
          [codeEq (codeBVar 0) (codeBVar 1), codeEq (codeBVar 0) (codeBVar 3)])) :=
    codeAnd_primrec.comp (Primrec.const (encClosed nextStepPairEq)) hnf
  have hrhs : Primrec (fun p : ℕ × ℕ =>
      codeAll (codeImp (codeNestFunc0 (codeConfigSet p.1))
        (codeBexsMem 0 (codeAll (codeImp (codeNestFunc0 (codeConfigSet p.1))
          (codeBexsMem 0 (codeAnd (encClosed nextStepPairEq)
            (codeNestFormulae 6 (codeNextConfig p.1 p.2)
              [codeEq (codeBVar 0) (codeBVar 1), codeEq (codeBVar 0) (codeBVar 3)])))))))) :=
    codeAll_primrec.comp <| codeImp_primrec.comp hcs <|
      (codeBexsMem_primrec 0).comp <| codeAll_primrec.comp <| codeImp_primrec.comp hcs <|
        (codeBexsMem_primrec 0).comp hbody
  unfold Primrec₂ codeNextStep
  dsimp only
  exact codeAll_primrec.comp <|
    codeIff_primrec.comp (Primrec.const (encClosed nextStepLhs)) hrhs

lemma codeNextStep_encClosed (n : ℕ) (instr : SetTheorySemisentence 1) :
    codeNextStep n (encClosed instr) = encClosed (Constant14.nextStep n instr) := by
  have hnf := codeNestFormulae_encClosed (m := 6) (n := 2) (Constant14.nextConfig n instr)
    ![Semiformula.Operator.Eq.eq.operator ![#0, #1], Semiformula.Operator.Eq.eq.operator ![#0, #3]]
  have hlist : (List.ofFn fun i : Fin 2 =>
      encClosed (![(Semiformula.Operator.Eq.eq.operator ![#0, #1] : SetTheorySemisentence 7),
        Semiformula.Operator.Eq.eq.operator ![#0, #3]] i)) =
      [codeEq (codeBVar 0) (codeBVar 1), codeEq (codeBVar 0) (codeBVar 3)] := rfl
  rw [hlist] at hnf
  have hdef : Constant14.nextStep n instr =
      ∀¹ (nextStepLhs 🡘
        ∀¹ ((Constant14.configSet n).nestFormulaeFunc (m := 2) ![] 🡒
          Semiformula.bexsMem #0
            (∀¹ ((Constant14.configSet n).nestFormulaeFunc (m := 4) ![] 🡒
              Semiformula.bexsMem #0
                (nextStepPairEq ⋏
                  (Constant14.nextConfig n instr).nestFormulae (m := 6)
                    ![Semiformula.Operator.Eq.eq.operator ![#0, #1],
                      Semiformula.Operator.Eq.eq.operator ![#0, #3]]))))) := rfl
  rw [hdef, encClosed_all, ← codeIff_encClosed, encClosed_all, encClosed_imp,
    ← codeBexsMem_encClosed (0 : Fin 3), encClosed_all, encClosed_imp,
    ← codeBexsMem_encClosed (0 : Fin 5), encClosed_and,
    ← hnf, ← codeNestFunc0_encClosed (m := 2), ← codeNestFunc0_encClosed (m := 4),
    ← codeConfigSet_encClosed, ← codeNextConfig_encClosed]
  rfl

def haltsInts : SetTheorySemisentence 1 := Constant14.integers.nestFormulaeFunc ![]

def haltsFuns : SetTheorySemisentence 3 :=
  function.dfn.nestFormulaeFunc ![
    (Constant14.numeral 2).nestFormulaeFunc ![],
    Constant14.integers.nestFormulaeFunc ![]]

def haltsMG : SetTheorySemisentence 5 :=
  kpair.dfn.nestFormulaeFunc ![
    Semiformula.Operator.Eq.eq.operator ![#0, #3],
    Semiformula.Operator.Eq.eq.operator ![#0, #1]]

def haltsInit : SetTheorySemisentence 6 := Constant14.initialConfig.nestFormulaeFunc ![]

def codeHalts (n instrCode : ℕ) : ℕ :=
  let kp := codeNestFormulaeFunc 4 (encClosed kpair.dfn)
    [codeNestFunc0 (codeNumeral n), encClosed haltsMG]
  let orb := codeNestFormulaeFunc 5 (encClosed Constant14.orbit)
    [codeNestFunc0 (codeNextStep (n + 1) instrCode), encClosed haltsInit]
  let inner := codeAll (codeImp kp (codeAll (codeImp orb (codeMem (codeBVar 1) (codeBVar 0)))))
  codeAll (codeImp (encClosed haltsInts)
    (codeBexsMem 0 (codeAll (codeImp (encClosed haltsFuns) (codeBexsMem 0 inner)))))

lemma codeHalts_primrec : Primrec₂ codeHalts := by
  have hkp : Primrec (fun p : ℕ × ℕ =>
      codeNestFormulaeFunc 4 (encClosed kpair.dfn)
        [codeNestFunc0 (codeNumeral p.1), encClosed haltsMG]) :=
    primrec_nestFunc2 4 (encClosed kpair.dfn) (encClosed haltsMG)
      (codeNumeral_primrec.comp Primrec.fst)
  have horb : Primrec (fun p : ℕ × ℕ =>
      codeNestFormulaeFunc 5 (encClosed Constant14.orbit)
        [codeNestFunc0 (codeNextStep (p.1 + 1) p.2), encClosed haltsInit]) :=
    primrec_nestFunc2 5 (encClosed Constant14.orbit) (encClosed haltsInit)
      (codeNextStep_primrec.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  have hinner : Primrec (fun p : ℕ × ℕ =>
      codeAll (codeImp
        (codeNestFormulaeFunc 4 (encClosed kpair.dfn) [codeNestFunc0 (codeNumeral p.1), encClosed haltsMG])
        (codeAll (codeImp
          (codeNestFormulaeFunc 5 (encClosed Constant14.orbit)
            [codeNestFunc0 (codeNextStep (p.1 + 1) p.2), encClosed haltsInit])
          (codeMem (codeBVar 1) (codeBVar 0)))))) :=
    codeAll_primrec.comp <| codeImp_primrec.comp hkp <|
      codeAll_primrec.comp <| codeImp_primrec.comp horb (Primrec.const (codeMem (codeBVar 1) (codeBVar 0)))
  unfold Primrec₂ codeHalts
  dsimp only
  exact codeAll_primrec.comp <| codeImp_primrec.comp (Primrec.const (encClosed haltsInts)) <|
    (codeBexsMem_primrec 0).comp <| codeAll_primrec.comp <|
      codeImp_primrec.comp (Primrec.const (encClosed haltsFuns)) <| (codeBexsMem_primrec 0).comp hinner

lemma codeHalts_encClosed {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    codeHalts n (encClosed (Constant14.instructionTable M)) = encClosed (Constant14.halts M) := by
  have hkp := codeNestFormulaeFunc_encClosed (m := 4) (n := 2) kpair.dfn
    ![(Constant14.numeral n).nestFormulaeFunc ![], haltsMG]
  have hlistKp : (List.ofFn fun i : Fin 2 =>
      encClosed (![(Constant14.numeral n).nestFormulaeFunc (m := 4) ![], haltsMG] i)) =
      [encClosed ((Constant14.numeral n).nestFormulaeFunc (m := 4) ![]), encClosed haltsMG] := rfl
  rw [hlistKp] at hkp
  have horb := codeNestFormulaeFunc_encClosed (m := 5) (n := 2) Constant14.orbit
    ![(Constant14.nextStep (n + 1) (Constant14.instructionTable M)).nestFormulaeFunc ![], haltsInit]
  have hlistOrb : (List.ofFn fun i : Fin 2 =>
      encClosed (![(Constant14.nextStep (n + 1) (Constant14.instructionTable M)).nestFormulaeFunc (m := 5) ![],
        haltsInit] i)) =
      [encClosed ((Constant14.nextStep (n + 1) (Constant14.instructionTable M)).nestFormulaeFunc (m := 5) ![]),
        encClosed haltsInit] := rfl
  rw [hlistOrb] at horb
  have hdef : Constant14.halts M =
      ∀¹ (haltsInts 🡒
        Semiformula.bexsMem #0
          (∀¹ (haltsFuns 🡒
            Semiformula.bexsMem #0
              (∀¹ (kpair.dfn.nestFormulaeFunc (m := 4) ![(Constant14.numeral n).nestFormulaeFunc (m := 4) ![], haltsMG] 🡒
                ∀¹ (Constant14.orbit.nestFormulaeFunc (m := 5)
                    ![(Constant14.nextStep (n + 1) (Constant14.instructionTable M)).nestFormulaeFunc (m := 5) ![], haltsInit] 🡒
                  Semiformula.Operator.Mem.mem.operator ![#1, #0])))))) := rfl
  rw [hdef, encClosed_all, encClosed_imp, ← codeBexsMem_encClosed (0 : Fin 1),
    encClosed_all, encClosed_imp, ← codeBexsMem_encClosed (0 : Fin 3),
    encClosed_all, encClosed_imp, encClosed_all, encClosed_imp,
    encClosed_mem_bvar (1 : Fin 6) (0 : Fin 6),
    ← hkp, ← horb, ← codeNestFunc0_encClosed (m := 4), ← codeNestFunc0_encClosed (m := 5),
    ← codeNumeral_encClosed, ← codeNextStep_encClosed]
  rfl

def codeNotHaltsPrepend (N : ℕ) (uTrans : List ℕ) (L : List Bool) : ℕ :=
  codeNeg (codeHalts (L.length + 1 + N) (codeFiniteSet ((prependEntries N uTrans L).map codeEntryOfNat)))

lemma codeNotHaltsPrepend_primrec (N : ℕ) (uTrans : List ℕ) :
    Primrec (codeNotHaltsPrepend N uTrans) :=
  codeNeg_primrec.comp <| codeHalts_primrec.comp
    (Primrec.nat_add.comp (Primrec.succ.comp Primrec.list_length) (Primrec.const N))
    (codeFiniteSet_primrec.comp <|
      Primrec.list_map (prependEntries_primrec N uTrans) (codeEntryOfNat_primrec.comp Primrec.snd).to₂)

lemma codeNotHaltsPrepend_encClosed {N : ℕ} [NeZero N] (U : Machine (Fin 2) (Fin N)) (L : List Bool) :
    codeNotHaltsPrepend N (uTransOf U) L =
      encClosed (∼Constant14.halts (C14H4TM.prependMachine L U)) := by
  unfold codeNotHaltsPrepend
  rw [codeInstructionTable_prepend, codeHalts_encClosed]
  unfold encClosed
  rw [emb_neg, codeNeg_encForm]

end C14H4RE

namespace C14H4RE

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open scoped Classical

/-
## Part B: Primitive-Recursive Enumeration of ZFC Axioms (`zfcAxiomCode`)
-/

def decList (c : ℕ) : List ℕ := (Encodable.decode c).getD []

lemma decList_primrec : Primrec decList := by
  refine (Primrec.option_casesOn (Primrec.decode (α := List ℕ))
    (Primrec.const []) (Primrec.to₂ Primrec.snd)).of_eq ?_
  intro s
  change Option.casesOn (Encodable.decode (α := List ℕ) s) [] (fun x => x) =
    (Encodable.decode (α := List ℕ) s).getD []
  cases Encodable.decode (α := List ℕ) s <;> rfl

lemma primrec_listAll {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).all (p a)) := by
  have hfold : Primrec (fun a => (f a).foldr (fun x acc => p a x && acc) true) :=
    Primrec.list_foldr hf (Primrec.const true)
      (Primrec.to₂ <| primrec_boolAnd (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  refine hfold.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x xs ih => simp [List.all_cons, ih]

lemma primrec_listAny {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).any (p a)) := by
  have hfold : Primrec (fun a => (f a).foldr (fun x acc => p a x || acc) false) :=
    Primrec.list_foldr hf (Primrec.const false)
      (Primrec.to₂ <| primrec_boolOr (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  refine hfold.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons x xs ih => simp [List.any_cons, ih]

lemma primrec_listHead? : Primrec (List.head? : List ℕ → Option ℕ) := by
  refine (Primrec.list_casesOn Primrec.id (Primrec.const none)
    (Primrec.to₂ <| Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))).of_eq ?_
  intro l; cases l <;> rfl

lemma primrec_listTail : Primrec (List.tail : List ℕ → List ℕ) := by
  refine (Primrec.list_casesOn Primrec.id (Primrec.const [])
    (Primrec.to₂ <| Primrec.snd.comp Primrec.snd)).of_eq ?_
  intro l; cases l <;> rfl

lemma primrec_eqDecide {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]
    {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => decide (f a = g a)) :=
  (Primrec.eq.comp hf hg).decide

lemma primrec_optionIsSome {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Option β} (hf : Primrec f) :
    Primrec (fun a => (f a).isSome) := by
  refine (Primrec.option_casesOn hf (Primrec.const false) (Primrec.to₂ (Primrec.const true))).of_eq ?_
  intro a; cases f a <;> rfl

lemma primrec_optionGetD {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Option β} (hf : Primrec f) (d : β) :
    Primrec (fun a => (f a).getD d) := by
  refine (Primrec.option_casesOn hf (Primrec.const d) (Primrec.to₂ Primrec.snd)).of_eq ?_
  intro a; cases f a <;> rfl

def constZFCAxioms : List SetTheorySentence :=
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

def constZFCCodes : List ℕ := constZFCAxioms.map encClosed

def codeSepBody (c : ℕ) : ℕ :=
  codeAll (codeExs (codeAll (codeIff (codeMem (codeBVar 0) (codeBVar 1))
    (codeAnd (codeMem (codeBVar 0) (codeBVar 2))
      (codeRew (([codeBVar 0], [], 0), c))))))

lemma codeSepBody_primrec : Primrec codeSepBody :=
  codeAll_primrec.comp <| codeExs_primrec.comp <| codeAll_primrec.comp <|
    codeIff_primrec.comp (Primrec.const (codeMem (codeBVar 0) (codeBVar 1))) <|
      codeAnd_primrec.comp (Primrec.const (codeMem (codeBVar 0) (codeBVar 2))) <|
        codeRew_primrec.comp (Primrec.pair (Primrec.const ([codeBVar 0], [], 0)) Primrec.id)

private lemma encForm_and {m : ℕ} (a b : Semiproposition ℒₛₑₜ m) :
    encForm (a ⋏ b) = codeAnd (encForm a) (encForm b) := rfl

private lemma encForm_or {m : ℕ} (a b : Semiproposition ℒₛₑₜ m) :
    encForm (a ⋎ b) = codeOr (encForm a) (encForm b) := rfl

private lemma encForm_all {m : ℕ} (a : Semiproposition ℒₛₑₜ (m + 1)) :
    encForm (∀¹ a) = codeAll (encForm a) := rfl

private lemma encForm_exs {m : ℕ} (a : Semiproposition ℒₛₑₜ (m + 1)) :
    encForm (∃¹ a) = codeExs (encForm a) := rfl

lemma codeSepBody_encForm (φ : SetTheorySemiproposition 1) :
    codeUnivCl (codeSepBody (encForm φ)) = encClosed (Axiom.separationSchema φ) := by
  let v : Fin 1 → Semiterm ℒₛₑₜ ℕ 3 := ![#0]
  have hm : RewMatches (Rew.subst v) [codeBVar 0] [] 0 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      change applyTerm [codeBVar 0] [] 0 (encTerm (#0 : Semiterm ℒₛₑₜ ℕ 1)) =
        encTerm ((Rew.subst v) (#0 : Semiterm ℒₛₑₜ ℕ 1))
      have h0 : (Rew.subst v) (#0 : Semiterm ℒₛₑₜ ℕ 1) = #0 := rfl
      rw [h0]; simp [applyTerm, encTerm, codeBVar]
    · have hx : (Rew.subst v) &x = &x := rfl
      rw [hx]; simp [applyTerm, encTerm]
  have hrew := codeRew_encForm φ (Rew.subst v) [codeBVar 0] [] 0 rfl hm
  have hbody : codeSepBody (encForm φ) = encForm
      (∀¹ (∃¹ (∀¹ (
        (Semiformula.Operator.Mem.mem.operator ![#0, #1] : Semiproposition ℒₛₑₜ 3) 🡘
        (Semiformula.Operator.Mem.mem.operator ![#0, #2] ⋏
          Rewriting.subst φ v))))) := by
    rw [encForm_all, encForm_exs, encForm_all, ← codeIff_encForm, encForm_and]
    unfold codeSepBody
    rw [hrew]
    rfl
  rw [hbody, codeUnivCl_encForm]
  rfl

def codeRepBody (c : ℕ) : ℕ :=
  let cPsi := codeRew (([codeBVar 1, codeBVar 0], [], 0), c)
  let cPsi01 := codeRew (([codeBVar 0, codeBVar 1], [], 0), cPsi)
  let cPsi02 := codeRew (([codeBVar 0, codeBVar 2], [], 0), cPsi)
  let cExsUniq := codeExs (codeAnd cPsi01 (codeAll (codeImp cPsi02 (codeEq (codeBVar 0) (codeBVar 1)))))
  let cRhs := codeAll (codeExs (codeAll (codeIff (codeMem (codeBVar 0) (codeBVar 1))
    (codeBexsMem 2 (codeRew (([codeBVar 0, codeBVar 1], [], 0), c))))))
  codeImp (codeAll cExsUniq) cRhs

lemma codeRepBody_primrec : Primrec codeRepBody := by
  have hcPsi : Primrec (fun c : ℕ => codeRew (([codeBVar 1, codeBVar 0], [], 0), c)) :=
    codeRew_primrec.comp (Primrec.pair (Primrec.const ([codeBVar 1, codeBVar 0], [], 0)) Primrec.id)
  have hcPsi01 : Primrec (fun c : ℕ =>
      codeRew (([codeBVar 0, codeBVar 1], [], 0), codeRew (([codeBVar 1, codeBVar 0], [], 0), c))) :=
    codeRew_primrec.comp (Primrec.pair (Primrec.const ([codeBVar 0, codeBVar 1], [], 0)) hcPsi)
  have hcPsi02 : Primrec (fun c : ℕ =>
      codeRew (([codeBVar 0, codeBVar 2], [], 0), codeRew (([codeBVar 1, codeBVar 0], [], 0), c))) :=
    codeRew_primrec.comp (Primrec.pair (Primrec.const ([codeBVar 0, codeBVar 2], [], 0)) hcPsi)
  have hcExsUniq : Primrec (fun c : ℕ =>
      codeExs (codeAnd
        (codeRew (([codeBVar 0, codeBVar 1], [], 0), codeRew (([codeBVar 1, codeBVar 0], [], 0), c)))
        (codeAll (codeImp
          (codeRew (([codeBVar 0, codeBVar 2], [], 0), codeRew (([codeBVar 1, codeBVar 0], [], 0), c)))
          (codeEq (codeBVar 0) (codeBVar 1)))))) :=
    codeExs_primrec.comp <| codeAnd_primrec.comp hcPsi01 <|
      codeAll_primrec.comp <| codeImp_primrec.comp hcPsi02 (Primrec.const (codeEq (codeBVar 0) (codeBVar 1)))
  have hcRhs : Primrec (fun c : ℕ =>
      codeAll (codeExs (codeAll (codeIff (codeMem (codeBVar 0) (codeBVar 1))
        (codeBexsMem 2 (codeRew (([codeBVar 0, codeBVar 1], [], 0), c))))))) :=
    codeAll_primrec.comp <| codeExs_primrec.comp <| codeAll_primrec.comp <|
      codeIff_primrec.comp (Primrec.const (codeMem (codeBVar 0) (codeBVar 1))) <|
        (codeBexsMem_primrec 2).comp <|
          codeRew_primrec.comp (Primrec.pair (Primrec.const ([codeBVar 0, codeBVar 1], [], 0)) Primrec.id)
  exact codeImp_primrec.comp (codeAll_primrec.comp hcExsUniq) hcRhs

lemma codeRepBody_encForm (φ : SetTheorySemiproposition 2) :
    codeUnivCl (codeRepBody (encForm φ)) = encClosed (Axiom.replacementSchema φ) := by
  let v10 : Fin 2 → Semiterm ℒₛₑₜ ℕ 2 := ![#1, #0]
  let ψ : SetTheorySemiproposition 2 := Rewriting.subst φ v10
  have hm1 : RewMatches (Rew.subst v10) [codeBVar 1, codeBVar 0] [] 0 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      · change applyTerm [codeBVar 1, codeBVar 0] [] 0 (encTerm (#0 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst v10) (#0 : Semiterm ℒₛₑₜ ℕ 2))
        have h0 : (Rew.subst v10) (#0 : Semiterm ℒₛₑₜ ℕ 2) = #1 := rfl
        rw [h0]; simp [applyTerm, encTerm, codeBVar]
      · change applyTerm [codeBVar 1, codeBVar 0] [] 0 (encTerm (#1 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst v10) (#1 : Semiterm ℒₛₑₜ ℕ 2))
        have h1 : (Rew.subst v10) (#1 : Semiterm ℒₛₑₜ ℕ 2) = #0 := rfl
        rw [h1]; simp [applyTerm, encTerm, codeBVar]
    · have hx : (Rew.subst v10) &x = &x := rfl
      rw [hx]; simp [applyTerm, encTerm]
  have hPsi : codeRew (([codeBVar 1, codeBVar 0], [], 0), encForm φ) = encForm ψ :=
    codeRew_encForm φ _ _ [] 0 rfl hm1
  let v01 : Fin 2 → Semiterm ℒₛₑₜ ℕ 2 :=
    Matrix.vecCons #0 fun x : Fin 1 => #(BinderNotation.finSuccItr x 1)
  have hm01 : RewMatches (Rew.subst v01) [codeBVar 0, codeBVar 1] [] 0 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      · change applyTerm [codeBVar 0, codeBVar 1] [] 0 (encTerm (#0 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst v01) (#0 : Semiterm ℒₛₑₜ ℕ 2))
        have h0 : (Rew.subst v01) (#0 : Semiterm ℒₛₑₜ ℕ 2) = #0 := rfl
        rw [h0]; simp [applyTerm, encTerm, codeBVar]
      · change applyTerm [codeBVar 0, codeBVar 1] [] 0 (encTerm (#1 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst v01) (#1 : Semiterm ℒₛₑₜ ℕ 2))
        have h1 : (Rew.subst v01) (#1 : Semiterm ℒₛₑₜ ℕ 2) = #1 := rfl
        rw [h1]; simp [applyTerm, encTerm, codeBVar]
    · have hx : (Rew.subst v01) &x = &x := rfl
      rw [hx]; simp [applyTerm, encTerm]
  have hPsi01 : codeRew (([codeBVar 0, codeBVar 1], [], 0), encForm ψ) = encForm (Rewriting.subst ψ v01) :=
    codeRew_encForm ψ _ _ [] 0 rfl hm01
  let v02 : Fin 2 → Semiterm ℒₛₑₜ ℕ 3 :=
    Matrix.vecCons #0 fun x : Fin 1 => #(BinderNotation.finSuccItr x 2)
  have hm02 : RewMatches (Rew.subst v02) [codeBVar 0, codeBVar 2] [] 0 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      · change applyTerm [codeBVar 0, codeBVar 2] [] 0 (encTerm (#0 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst v02) (#0 : Semiterm ℒₛₑₜ ℕ 2))
        have h0 : (Rew.subst v02) (#0 : Semiterm ℒₛₑₜ ℕ 2) = #0 := rfl
        rw [h0]; simp [applyTerm, encTerm, codeBVar]
      · change applyTerm [codeBVar 0, codeBVar 2] [] 0 (encTerm (#1 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst v02) (#1 : Semiterm ℒₛₑₜ ℕ 2))
        have h1 : (Rew.subst v02) (#1 : Semiterm ℒₛₑₜ ℕ 2) = #2 := rfl
        rw [h1]; simp [applyTerm, encTerm, codeBVar]
    · have hx : (Rew.subst v02) &x = &x := rfl
      rw [hx]; simp [applyTerm, encTerm]
  have hPsi02 : codeRew (([codeBVar 0, codeBVar 2], [], 0), encForm ψ) = encForm (Rewriting.subst ψ v02) :=
    codeRew_encForm ψ _ _ [] 0 rfl hm02
  let vR : Fin 2 → Semiterm ℒₛₑₜ ℕ 4 := ![#0, #1]
  have hmR : RewMatches (Rew.subst vR) [codeBVar 0, codeBVar 1] [] 0 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      · change applyTerm [codeBVar 0, codeBVar 1] [] 0 (encTerm (#0 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst vR) (#0 : Semiterm ℒₛₑₜ ℕ 2))
        have h0 : (Rew.subst vR) (#0 : Semiterm ℒₛₑₜ ℕ 2) = #0 := rfl
        rw [h0]; simp [applyTerm, encTerm, codeBVar]
      · change applyTerm [codeBVar 0, codeBVar 1] [] 0 (encTerm (#1 : Semiterm ℒₛₑₜ ℕ 2)) =
          encTerm ((Rew.subst vR) (#1 : Semiterm ℒₛₑₜ ℕ 2))
        have h1 : (Rew.subst vR) (#1 : Semiterm ℒₛₑₜ ℕ 2) = #1 := rfl
        rw [h1]; simp [applyTerm, encTerm, codeBVar]
    · have hx : (Rew.subst vR) &x = &x := rfl
      rw [hx]; simp [applyTerm, encTerm]
  have hPhiR : codeRew (([codeBVar 0, codeBVar 1], [], 0), encForm φ) =
      encForm (Rewriting.subst φ vR) :=
    codeRew_encForm φ _ _ [] 0 rfl hmR
  have hbody : codeRepBody (encForm φ) = encForm
      ((∀¹ ψ.existsUnique) 🡒
        (∀¹ (∃¹ (∀¹ (
          (Semiformula.Operator.Mem.mem.operator ![#0, #1] : Semiproposition ℒₛₑₜ 3) 🡘
          Semiformula.bexsMem (#2 : Semiterm ℒₛₑₜ ℕ 3)
            (Rewriting.subst φ vR)))))) := by
    rw [← codeImp_encForm, encForm_all, encForm_all, encForm_exs, encForm_all,
      ← codeIff_encForm, ← codeBexsMem_encForm (2 : Fin 3)]
    have heu : encForm ψ.existsUnique =
        codeExs (codeAnd (encForm (Rewriting.subst ψ v01))
          (codeAll (codeImp (encForm (Rewriting.subst ψ v02)) (codeEq (codeBVar 0) (codeBVar 1))))) := by
      unfold Semiformula.existsUnique
      rw [encForm_exs, encForm_and, encForm_all, ← codeImp_encForm]
      rfl
    rw [heu]
    unfold codeRepBody
    dsimp only
    rw [hPsi, hPsi01, hPsi02, hPhiR]
    rfl
  rw [hbody, codeUnivCl_encForm]
  rfl

def zfcAxiomCode (tag φ : ℕ) : Option ℕ :=
  if decide (tag < 13) then constZFCCodes[tag]?
  else if tag == 13 then if wfForm (1, φ) then some (codeUnivCl (codeSepBody φ)) else none
  else if tag == 14 then if wfForm (2, φ) then some (codeUnivCl (codeRepBody φ)) else none
  else none

lemma zfcAxiomCode_primrec : Primrec₂ zfcAxiomCode := by
  have hlt13 : Primrec (fun p : ℕ × ℕ => decide (p.1 < 13)) :=
    (Primrec.nat_lt.comp Primrec.fst (Primrec.const 13)).decide
  have hconst : Primrec (fun p : ℕ × ℕ => constZFCCodes[p.1]?) :=
    Primrec.list_getElem?.comp (Primrec.const constZFCCodes) Primrec.fst
  have hsep : Primrec (fun p : ℕ × ℕ =>
      if wfForm (1, p.2) then some (codeUnivCl (codeSepBody p.2)) else none) :=
    primrec_iteBool (wfForm_primrec.comp (Primrec.pair (Primrec.const 1) Primrec.snd))
      (Primrec.option_some.comp (codeUnivCl_primrec.comp (codeSepBody_primrec.comp Primrec.snd)))
      (Primrec.const none)
  have hrep : Primrec (fun p : ℕ × ℕ =>
      if wfForm (2, p.2) then some (codeUnivCl (codeRepBody p.2)) else none) :=
    primrec_iteBool (wfForm_primrec.comp (Primrec.pair (Primrec.const 2) Primrec.snd))
      (Primrec.option_some.comp (codeUnivCl_primrec.comp (codeRepBody_primrec.comp Primrec.snd)))
      (Primrec.const none)
  exact Primrec.to₂ <| primrec_iteBool hlt13 hconst <|
    primrec_iteBool (Primrec.beq.comp Primrec.fst (Primrec.const 13)) hsep <|
    primrec_iteBool (Primrec.beq.comp Primrec.fst (Primrec.const 14)) hrep <|
      Primrec.const none

lemma constZFCAxioms_mem_zfc {i : ℕ} (hi : i < constZFCAxioms.length) :
    constZFCAxioms[i] ∈ 𝗭𝗙𝗖 := by
  have hlen : constZFCAxioms.length = 13 := rfl
  rw [hlen] at hi
  interval_cases i
  · exact Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.refl)
  · exact Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.symm)
  · exact Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.trans)
  · exact Or.inl (ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt (L := ℒₛₑₜ) Language.Set.Rel.eq))
  · exact Or.inl (ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt (L := ℒₛₑₜ) Language.Set.Rel.mem))
  · exact Or.inl ZermeloFraenkel.axiom_of_empty_set
  · exact Or.inl ZermeloFraenkel.axiom_of_extentionality
  · exact Or.inl ZermeloFraenkel.axiom_of_pairing
  · exact Or.inl ZermeloFraenkel.axiom_of_union
  · exact Or.inl ZermeloFraenkel.axiom_of_power_set
  · exact Or.inl ZermeloFraenkel.axiom_of_infinity
  · exact Or.inl ZermeloFraenkel.axiom_of_foundation
  · exact Or.inr (Set.mem_singleton Axiom.choice)

lemma zfcAxiomCode_iff (σ : ℕ) :
    (∃ tag φ, zfcAxiomCode tag φ = some σ) ↔ ∃ ψ ∈ 𝗭𝗙𝗖, encClosed ψ = σ := by
  constructor
  · rintro ⟨tag, φ, h⟩
    unfold zfcAxiomCode at h
    split_ifs at h with h13 hsep hwf1 hrep hwf2
    · have ht : tag < 13 := by simpa using h13
      have hlen : constZFCAxioms.length = 13 := rfl
      have hget : constZFCCodes[tag]? = some (encClosed constZFCAxioms[tag]) := by
        rw [List.getElem?_eq_getElem (by simp [constZFCCodes, hlen, ht])]
        simp only [constZFCCodes, List.getElem_map]
        rfl
      rw [hget] at h
      cases h
      exact ⟨constZFCAxioms[tag], constZFCAxioms_mem_zfc (by omega), rfl⟩
    · obtain ⟨ψ, rfl⟩ := (wfForm_iff 1 φ).mp hwf1
      cases h
      exact ⟨Axiom.separationSchema ψ, Or.inl (ZermeloFraenkel.axiom_of_separation ψ),
        (codeSepBody_encForm ψ).symm⟩
    · obtain ⟨ψ, rfl⟩ := (wfForm_iff 2 φ).mp hwf2
      cases h
      exact ⟨Axiom.replacementSchema ψ, Or.inl (ZermeloFraenkel.axiom_of_replacement ψ),
        (codeRepBody_encForm ψ).symm⟩
  · rintro ⟨ψ, hψ, rfl⟩
    rcases hψ with hzf | hac
    · cases hzf with
      | axiom_of_equality _ heq =>
        cases heq with
        | refl => exact ⟨0, 0, rfl⟩
        | symm => exact ⟨1, 0, rfl⟩
        | trans => exact ⟨2, 0, rfl⟩
        | funcExt f => exact (f : Empty).elim
        | relExt r =>
          cases r with
          | eq => exact ⟨3, 0, rfl⟩
          | mem => exact ⟨4, 0, rfl⟩
      | axiom_of_empty_set => exact ⟨5, 0, rfl⟩
      | axiom_of_extentionality => exact ⟨6, 0, rfl⟩
      | axiom_of_pairing => exact ⟨7, 0, rfl⟩
      | axiom_of_union => exact ⟨8, 0, rfl⟩
      | axiom_of_power_set => exact ⟨9, 0, rfl⟩
      | axiom_of_infinity => exact ⟨10, 0, rfl⟩
      | axiom_of_foundation => exact ⟨11, 0, rfl⟩
      | axiom_of_separation φ =>
        refine ⟨13, encForm φ, ?_⟩
        have hwf : wfForm (1, encForm φ) = true := (wfForm_iff 1 _).mpr ⟨φ, rfl⟩
        simp [zfcAxiomCode, hwf, codeSepBody_encForm]
      | axiom_of_replacement φ =>
        refine ⟨14, encForm φ, ?_⟩
        have hwf : wfForm (2, encForm φ) = true := (wfForm_iff 2 _).mpr ⟨φ, rfl⟩
        simp [zfcAxiomCode, hwf, codeRepBody_encForm]
    · have heq : ψ = Axiom.choice := Set.mem_singleton_iff.mp hac
      subst heq
      exact ⟨12, 0, rfl⟩

/-
## Part C: Primitive-Recursive LK Proof Checker (`checkProof`) and `REPred`
-/

def codeShiftForm (c : ℕ) : ℕ := codeRew (([], [], 1), c)
def codeFreeForm (c : ℕ) : ℕ := codeRew (([Nat.pair 1 0], [], 1), c)
def codeSubst0 (t c : ℕ) : ℕ := codeRew (([t], [], 0), c)

lemma codeShiftForm_primrec : Primrec codeShiftForm :=
  codeRew_primrec.comp (Primrec.pair (Primrec.const ([], [], 1)) Primrec.id)

lemma codeFreeForm_primrec : Primrec codeFreeForm :=
  codeRew_primrec.comp (Primrec.pair (Primrec.const ([Nat.pair 1 0], [], 1)) Primrec.id)

lemma codeSubst0_primrec : Primrec₂ codeSubst0 :=
  Primrec.to₂ <| codeRew_primrec.comp <|
    Primrec.pair
      (Primrec.pair (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) (Primrec.const ([], 0)))
      Primrec.snd

lemma codeShiftForm_encForm (φ : Proposition ℒₛₑₜ) :
    codeShiftForm (encForm φ) = encForm (Rewriting.shift φ) := by
  have hm : RewMatches (Rew.shift : Rew ℒₛₑₜ ℕ 0 ℕ 0) [] [] 1 := by
    refine ⟨fun i => i.elim0, fun x => ?_⟩
    have hx : (Rew.shift : Rew ℒₛₑₜ ℕ 0 ℕ 0) &x = &(x + 1) := rfl
    rw [hx]; simp [applyTerm, encTerm]
  exact codeRew_encForm φ Rew.shift [] [] 1 rfl hm

lemma codeFreeForm_encForm (φ : Semiproposition ℒₛₑₜ 1) :
    codeFreeForm (encForm φ) = encForm φ.free := by
  have hm : RewMatches (Rew.free : Rew ℒₛₑₜ ℕ 1 ℕ 0) [Nat.pair 1 0] [] 1 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      change applyTerm [Nat.pair 1 0] [] 1 (Nat.pair 0 0) = encTerm ((Rew.free : Rew ℒₛₑₜ ℕ 1 ℕ 0) #0)
      have h0 : (Rew.free : Rew ℒₛₑₜ ℕ 1 ℕ 0) #0 = &0 := rfl
      rw [h0]; simp [applyTerm, encTerm]
    · have hx : (Rew.free : Rew ℒₛₑₜ ℕ 1 ℕ 0) &x = &(x + 1) := rfl
      rw [hx]; simp [applyTerm, encTerm]
  exact codeRew_encForm φ Rew.free [Nat.pair 1 0] [] 1 rfl hm

lemma codeSubst0_encForm (φ : Semiproposition ℒₛₑₜ 1) (t : Semiterm ℒₛₑₜ ℕ 0) :
    codeSubst0 (encTerm t) (encForm φ) = encForm (φ/[t]) := by
  let v : Fin 1 → Semiterm ℒₛₑₜ ℕ 0 := ![t]
  have hm : RewMatches (Rew.subst v) [encTerm t] [] 0 := by
    refine ⟨fun i => ?_, fun x => ?_⟩
    · fin_cases i
      change applyTerm [encTerm t] [] 0 (encTerm (#0 : Semiterm ℒₛₑₜ ℕ 1)) =
        encTerm ((Rew.subst v) (#0 : Semiterm ℒₛₑₜ ℕ 1))
      have h0 : (Rew.subst v) (#0 : Semiterm ℒₛₑₜ ℕ 1) = t := rfl
      rw [h0]; simp [applyTerm, encTerm]
    · have hx : (Rew.subst v) &x = &x := rfl
      rw [hx]; simp [applyTerm, encTerm]
  exact codeRew_encForm φ (Rew.subst v) [encTerm t] [] 0 rfl hm

/- ### C.1. The 8 LK Rule Checkers -/

def getStepSeq (steps : List ℕ) (i : ℕ) : List ℕ :=
  decList (steps.getD i 0).unpair.1

lemma getStepSeq_primrec : Primrec₂ getStepSeq :=
  Primrec.to₂ <| decList_primrec.comp <| Primrec.fst.comp <|
    Primrec.unpair.comp ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd)

def checkRule0 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let rarg := step.unpair.2.unpair.2
  let rb := rarg.unpair.1
  let t0 := rarg.unpair.2.unpair.1
  let t1 := rarg.unpair.2.unpair.2
  decide (rb < 2) && wfTerm 0 t0 && wfTerm 0 t1 &&
    decide (seq = [Nat.pair (2 + rb) (Nat.pair t0 t1), Nat.pair (4 + rb) (Nat.pair t0 t1)])

def checkRule1 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  decide (decList step.unpair.1 = [Nat.pair 0 0])

def checkRule2 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let i := step.unpair.2.unpair.2
  decide (i < p.2) && seq.all (fun c => wfForm (0, c)) &&
    (getStepSeq p.1 i).all (fun c => seq.any (fun d => decide (d = c)))

def checkRule3 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let rarg := step.unpair.2.unpair.2
  let i := rarg.unpair.1
  let j := rarg.unpair.2.unpair.1
  let phi := rarg.unpair.2.unpair.2
  let sI := getStepSeq p.1 i
  let sJ := getStepSeq p.1 j
  decide (i < p.2) && decide (j < p.2) && wfForm (0, phi) &&
    decide (sI.head? = some phi) && decide (sJ.head? = some (codeNeg phi)) &&
    decide (seq = sI.tail ++ sJ.tail)

def checkRule4 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let rarg := step.unpair.2.unpair.2
  let i := rarg.unpair.1
  let phi := rarg.unpair.2.unpair.1
  let psi := rarg.unpair.2.unpair.2
  let sI := getStepSeq p.1 i
  decide (i < p.2) && wfForm (0, phi) && wfForm (0, psi) &&
    decide (sI.head? = some phi) && decide (sI.tail.head? = some psi) &&
    decide (seq = codeOr phi psi :: sI.tail.tail)

def checkRule5 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let rarg := step.unpair.2.unpair.2
  let i := rarg.unpair.1
  let j := rarg.unpair.2.unpair.1
  let phi := rarg.unpair.2.unpair.2.unpair.1
  let psi := rarg.unpair.2.unpair.2.unpair.2
  let sI := getStepSeq p.1 i
  let sJ := getStepSeq p.1 j
  decide (i < p.2) && decide (j < p.2) && wfForm (0, phi) && wfForm (0, psi) &&
    decide (sI.head? = some phi) && decide (sJ.head? = some psi) &&
    decide (sI.tail = sJ.tail) && decide (seq = codeAnd phi psi :: sI.tail)

def checkRule6 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let rarg := step.unpair.2.unpair.2
  let i := rarg.unpair.1
  let phi := rarg.unpair.2
  let sI := getStepSeq p.1 i
  decide (i < p.2) && wfForm (1, phi) &&
    decide (seq.head? = some (codeAll phi)) &&
    seq.tail.all (fun c => wfForm (0, c)) &&
    decide (sI = codeFreeForm phi :: seq.tail.map codeShiftForm)

def checkRule7 (p : List ℕ × ℕ) : Bool :=
  let step := p.1.getD p.2 0
  let seq := decList step.unpair.1
  let rarg := step.unpair.2.unpair.2
  let i := rarg.unpair.1
  let phi := rarg.unpair.2.unpair.1
  let t := rarg.unpair.2.unpair.2
  let sI := getStepSeq p.1 i
  decide (i < p.2) && wfForm (1, phi) && wfTerm 0 t &&
    decide (sI.head? = some (codeSubst0 t phi)) &&
    decide (seq = codeExs phi :: sI.tail)

def checkStep (steps : List ℕ) (idx : ℕ) : Bool :=
  let rtag := (steps.getD idx 0).unpair.2.unpair.1
  if rtag == 0 then checkRule0 (steps, idx)
  else if rtag == 1 then checkRule1 (steps, idx)
  else if rtag == 2 then checkRule2 (steps, idx)
  else if rtag == 3 then checkRule3 (steps, idx)
  else if rtag == 4 then checkRule4 (steps, idx)
  else if rtag == 5 then checkRule5 (steps, idx)
  else if rtag == 6 then checkRule6 (steps, idx)
  else if rtag == 7 then checkRule7 (steps, idx)
  else false

/- ### C.2. Primrec Proofs for `checkRule0 .. checkRule7`, `checkStep`, `checkProof` -/

private lemma checkRule0_primrec : Primrec checkRule0 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq : Primrec (fun p : List ℕ × ℕ => decList (p.1.getD p.2 0).unpair.1) :=
    decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hrarg : Primrec (fun p : List ℕ × ℕ => (p.1.getD p.2 0).unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hrb := Primrec.fst.comp (Primrec.unpair.comp hrarg)
  have ht0 := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have ht1 := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have hrel := primrec_natPair.comp (Primrec.nat_add.comp (Primrec.const 2) hrb) (primrec_natPair.comp ht0 ht1)
  have hnrel := primrec_natPair.comp (Primrec.nat_add.comp (Primrec.const 4) hrb) (primrec_natPair.comp ht0 ht1)
  have hexp := Primrec.list_cons.comp hrel (Primrec.list_cons.comp hnrel (Primrec.const []))
  exact primrec_boolAnd
    (primrec_boolAnd
      (primrec_boolAnd ((Primrec.nat_lt.comp hrb (Primrec.const 2)).decide)
        (wfTerm_primrec.comp (Primrec.const 0) ht0))
      (wfTerm_primrec.comp (Primrec.const 0) ht1))
    (primrec_eqDecide hseq hexp)

private lemma checkRule1_primrec : Primrec checkRule1 :=
  primrec_eqDecide (getStepSeq_primrec.comp Primrec.fst Primrec.snd) (Primrec.const [Nat.pair 0 0])

private lemma checkRule2_primrec : Primrec checkRule2 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq : Primrec (fun p : List ℕ × ℕ => decList (p.1.getD p.2 0).unpair.1) :=
    decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hi : Primrec (fun p : List ℕ × ℕ => (p.1.getD p.2 0).unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hsI : Primrec (fun p : List ℕ × ℕ => getStepSeq p.1 (p.1.getD p.2 0).unpair.2.unpair.2) :=
    getStepSeq_primrec.comp Primrec.fst hi
  have hwf : Primrec (fun p : List ℕ × ℕ => (decList (p.1.getD p.2 0).unpair.1).all (fun c => wfForm (0, c))) :=
    primrec_listAll hseq (Primrec.to₂ <| wfForm_primrec.comp (Primrec.pair (Primrec.const 0) Primrec.snd))
  have hmem : Primrec₂ (fun (seq : List ℕ) (c : ℕ) => seq.any (fun d => decide (d = c))) :=
    Primrec.to₂ <| primrec_listAny Primrec.fst
      (Primrec.to₂ <| primrec_eqDecide Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hsub : Primrec (fun p : List ℕ × ℕ =>
      (getStepSeq p.1 (p.1.getD p.2 0).unpair.2.unpair.2).all
        (fun c => (decList (p.1.getD p.2 0).unpair.1).any (fun d => decide (d = c)))) :=
    primrec_listAll hsI (Primrec.to₂ <| hmem.comp (hseq.comp Primrec.fst) Primrec.snd)
  exact primrec_boolAnd (primrec_boolAnd ((Primrec.nat_lt.comp hi Primrec.snd).decide) hwf) hsub

private lemma checkRule3_primrec : Primrec checkRule3 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq := decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hrarg := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hi := Primrec.fst.comp (Primrec.unpair.comp hrarg)
  have hj := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have hphi := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have hsI := getStepSeq_primrec.comp Primrec.fst hi
  have hsJ := getStepSeq_primrec.comp Primrec.fst hj
  exact primrec_boolAnd
    (primrec_boolAnd
      (primrec_boolAnd
        (primrec_boolAnd
          (primrec_boolAnd ((Primrec.nat_lt.comp hi Primrec.snd).decide)
            ((Primrec.nat_lt.comp hj Primrec.snd).decide))
          (wfForm_primrec.comp (Primrec.pair (Primrec.const 0) hphi)))
        (primrec_eqDecide (primrec_listHead?.comp hsI) (Primrec.option_some.comp hphi)))
      (primrec_eqDecide (primrec_listHead?.comp hsJ) (Primrec.option_some.comp (codeNeg_primrec.comp hphi))))
    (primrec_eqDecide hseq (Primrec.list_append.comp (primrec_listTail.comp hsI) (primrec_listTail.comp hsJ)))

private lemma checkRule4_primrec : Primrec checkRule4 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq := decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hrarg := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hi := Primrec.fst.comp (Primrec.unpair.comp hrarg)
  have hphi := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have hpsi := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have hsI := getStepSeq_primrec.comp Primrec.fst hi
  exact primrec_boolAnd
    (primrec_boolAnd
      (primrec_boolAnd
        (primrec_boolAnd
          (primrec_boolAnd ((Primrec.nat_lt.comp hi Primrec.snd).decide)
            (wfForm_primrec.comp (Primrec.pair (Primrec.const 0) hphi)))
          (wfForm_primrec.comp (Primrec.pair (Primrec.const 0) hpsi)))
        (primrec_eqDecide (primrec_listHead?.comp hsI) (Primrec.option_some.comp hphi)))
      (primrec_eqDecide (primrec_listHead?.comp (primrec_listTail.comp hsI)) (Primrec.option_some.comp hpsi)))
    (primrec_eqDecide hseq (Primrec.list_cons.comp (codeOr_primrec.comp hphi hpsi)
      (primrec_listTail.comp (primrec_listTail.comp hsI))))

private lemma checkRule5_primrec : Primrec checkRule5 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq := decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hrarg := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hi := Primrec.fst.comp (Primrec.unpair.comp hrarg)
  have hr1 := Primrec.snd.comp (Primrec.unpair.comp hrarg)
  have hj := Primrec.fst.comp (Primrec.unpair.comp hr1)
  have hr2 := Primrec.snd.comp (Primrec.unpair.comp hr1)
  have hphi := Primrec.fst.comp (Primrec.unpair.comp hr2)
  have hpsi := Primrec.snd.comp (Primrec.unpair.comp hr2)
  have hsI := getStepSeq_primrec.comp Primrec.fst hi
  have hsJ := getStepSeq_primrec.comp Primrec.fst hj
  exact primrec_boolAnd
    (primrec_boolAnd
      (primrec_boolAnd
        (primrec_boolAnd
          (primrec_boolAnd
            (primrec_boolAnd
              (primrec_boolAnd ((Primrec.nat_lt.comp hi Primrec.snd).decide)
                ((Primrec.nat_lt.comp hj Primrec.snd).decide))
              (wfForm_primrec.comp (Primrec.pair (Primrec.const 0) hphi)))
            (wfForm_primrec.comp (Primrec.pair (Primrec.const 0) hpsi)))
          (primrec_eqDecide (primrec_listHead?.comp hsI) (Primrec.option_some.comp hphi)))
        (primrec_eqDecide (primrec_listHead?.comp hsJ) (Primrec.option_some.comp hpsi)))
      (primrec_eqDecide (primrec_listTail.comp hsI) (primrec_listTail.comp hsJ)))
    (primrec_eqDecide hseq (Primrec.list_cons.comp (codeAnd_primrec.comp hphi hpsi) (primrec_listTail.comp hsI)))

private lemma checkRule6_primrec : Primrec checkRule6 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq := decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hrarg := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hi := Primrec.fst.comp (Primrec.unpair.comp hrarg)
  have hphi := Primrec.snd.comp (Primrec.unpair.comp hrarg)
  have hsI := getStepSeq_primrec.comp Primrec.fst hi
  have htail := primrec_listTail.comp hseq
  have hwfTail := primrec_listAll htail
    (Primrec.to₂ <| wfForm_primrec.comp (Primrec.pair (Primrec.const 0) Primrec.snd))
  have hshTail := Primrec.list_map htail (codeShiftForm_primrec.comp Primrec.snd).to₂
  exact primrec_boolAnd
    (primrec_boolAnd
      (primrec_boolAnd
        (primrec_boolAnd ((Primrec.nat_lt.comp hi Primrec.snd).decide)
          (wfForm_primrec.comp (Primrec.pair (Primrec.const 1) hphi)))
        (primrec_eqDecide (primrec_listHead?.comp hseq) (Primrec.option_some.comp (codeAll_primrec.comp hphi))))
      hwfTail)
    (primrec_eqDecide hsI (Primrec.list_cons.comp (codeFreeForm_primrec.comp hphi) hshTail))

private lemma checkRule7_primrec : Primrec checkRule7 := by
  have hstep : Primrec (fun p : List ℕ × ℕ => p.1.getD p.2 0) :=
    (Primrec.list_getD 0).comp Primrec.fst Primrec.snd
  have hseq := decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp hstep))
  have hrarg := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hstep)))
  have hi := Primrec.fst.comp (Primrec.unpair.comp hrarg)
  have hphi := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hrarg)))
  have hsI := getStepSeq_primrec.comp Primrec.fst hi
  exact primrec_boolAnd
    (primrec_boolAnd
      (primrec_boolAnd
        (primrec_boolAnd ((Primrec.nat_lt.comp hi Primrec.snd).decide)
          (wfForm_primrec.comp (Primrec.pair (Primrec.const 1) hphi)))
        (wfTerm_primrec.comp (Primrec.const 0) ht))
      (primrec_eqDecide (primrec_listHead?.comp hsI) (Primrec.option_some.comp (codeSubst0_primrec.comp ht hphi))))
    (primrec_eqDecide hseq (Primrec.list_cons.comp (codeExs_primrec.comp hphi) (primrec_listTail.comp hsI)))

lemma checkStep_primrec : Primrec₂ checkStep := by
  have hrtag : Primrec (fun p : List ℕ × ℕ => (p.1.getD p.2 0).unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd))))
  exact Primrec.to₂ <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 0)) checkRule0_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 1)) checkRule1_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 2)) checkRule2_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 3)) checkRule3_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 4)) checkRule4_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 5)) checkRule5_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 6)) checkRule6_primrec <|
    primrec_iteBool (Primrec.beq.comp hrtag (Primrec.const 7)) checkRule7_primrec <|
      Primrec.const false

def checkProof (targetCode w : ℕ) : Bool :=
  let axList := decList w.unpair.1
  let steps := decList w.unpair.2
  let allAxOk := axList.all (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).isSome)
  let axCodes := axList.map (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0)
  let allStepsOk := (List.range steps.length).all (fun idx => checkStep steps idx)
  let lastOk := decide (0 < steps.length) &&
    decide (getStepSeq steps (steps.length - 1) = targetCode :: axCodes.map codeNeg)
  allAxOk && allStepsOk && lastOk

lemma checkProof_primrec : Primrec₂ checkProof := by
  have haxList : Primrec (fun p : ℕ × ℕ => decList p.2.unpair.1) :=
    decList_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hsteps : Primrec (fun p : ℕ × ℕ => decList p.2.unpair.2) :=
    decList_primrec.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have haxOpt : Primrec (fun e : ℕ => zfcAxiomCode e.unpair.1 e.unpair.2) :=
    zfcAxiomCode_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hallAxOk : Primrec (fun p : ℕ × ℕ =>
      (decList p.2.unpair.1).all (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).isSome)) :=
    primrec_listAll haxList (Primrec.to₂ <| primrec_optionIsSome (haxOpt.comp Primrec.snd))
  have haxCodes : Primrec (fun p : ℕ × ℕ =>
      (decList p.2.unpair.1).map (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0)) :=
    Primrec.list_map haxList (Primrec.to₂ <| primrec_optionGetD (haxOpt.comp Primrec.snd) 0)
  have hlen : Primrec (fun p : ℕ × ℕ => (decList p.2.unpair.2).length) :=
    Primrec.list_length.comp hsteps
  have hallStepsOk : Primrec (fun p : ℕ × ℕ =>
      (List.range (decList p.2.unpair.2).length).all (fun idx => checkStep (decList p.2.unpair.2) idx)) :=
    primrec_listAll (Primrec.list_range.comp hlen)
      (Primrec.to₂ <| checkStep_primrec.comp (hsteps.comp Primrec.fst) Primrec.snd)
  have hlastSeq : Primrec (fun p : ℕ × ℕ =>
      getStepSeq (decList p.2.unpair.2) ((decList p.2.unpair.2).length - 1)) :=
    getStepSeq_primrec.comp hsteps (Primrec.nat_sub.comp hlen (Primrec.const 1))
  have hexpSeq : Primrec (fun p : ℕ × ℕ =>
      p.1 :: ((decList p.2.unpair.1).map (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0)).map codeNeg) :=
    Primrec.list_cons.comp Primrec.fst
      (Primrec.list_map haxCodes (codeNeg_primrec.comp Primrec.snd).to₂)
  have hlastOk : Primrec (fun p : ℕ × ℕ =>
      decide (0 < (decList p.2.unpair.2).length) &&
        decide (getStepSeq (decList p.2.unpair.2) ((decList p.2.unpair.2).length - 1) =
          p.1 :: ((decList p.2.unpair.1).map (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0)).map codeNeg)) :=
    primrec_boolAnd ((Primrec.nat_lt.comp (Primrec.const 0) hlen).decide)
      (primrec_eqDecide hlastSeq hexpSeq)
  exact Primrec.to₂ <| primrec_boolAnd (primrec_boolAnd hallAxOk hallStepsOk) hlastOk

/- ### C.3. Soundness of `checkProof` -/

private lemma list_of_wfForm_all {cs : List ℕ} (h : ∀ c ∈ cs, wfForm (0, c) = true) :
    ∃ L : List (Proposition ℒₛₑₜ), L.map encForm = cs := by
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    obtain ⟨φ, hφ⟩ := (wfForm_iff 0 c).mp (h c (by simp))
    obtain ⟨L, hL⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨φ :: L, by simp [hφ, hL]⟩

private lemma multiset_ofList_cons_eq_add_atom {α : Type*} (a : α) (L : List α) :
    Multiset.ofList (a :: L) = Multiset.ofList L + Multiset.atom a := by
  change a ::ₘ Multiset.ofList L = Multiset.ofList L + {a}
  rw [add_comm]; rfl

private lemma multiset_ofList_cons2_eq_add_atoms {α : Type*} (a b : α) (L : List α) :
    Multiset.ofList (a :: b :: L) = Multiset.ofList L + (Multiset.atom a + Multiset.atom b) := by
  change a ::ₘ b ::ₘ Multiset.ofList L = Multiset.ofList L + ({a} + {b})
  rw [add_comm (Multiset.ofList L), add_assoc, Multiset.singleton_add, Multiset.singleton_add]

private lemma checkStep_sound (steps : List ℕ)
    (hall : ∀ idx < steps.length, checkStep steps idx = true) :
    ∀ idx < steps.length,
      ∃ L : List (Proposition ℒₛₑₜ), L.map encForm = getStepSeq steps idx ∧
        Nonempty (Derivation (Multiset.ofList L)) := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | h idx ih =>
    intro hidx
    have hstep := hall idx hidx
    unfold checkStep at hstep
    dsimp only at hstep
    split_ifs at hstep with h0 h1 h2 h3 h4 h5 h6 h7
    · -- Rule 0: identity
      simp only [checkRule0, Bool.and_eq_true, decide_eq_true_eq] at hstep
      rcases hstep with ⟨⟨⟨hrb, ht0⟩, ht1⟩, hseq⟩
      obtain ⟨u0, hu0⟩ := (wfTerm_iff 0 _).mp ht0
      obtain ⟨u1, hu1⟩ := (wfTerm_iff 0 _).mp ht1
      interval_cases hr : ((steps.getD idx 0).unpair.2.unpair.2).unpair.1
      · refine ⟨[Semiformula.rel Language.Set.Rel.eq ![u0, u1],
            Semiformula.nrel Language.Set.Rel.eq ![u0, u1]], ?_, ?_⟩
        · change [encForm _, encForm _] = getStepSeq steps idx
          rw [getStepSeq, hseq]; simp [encForm, hu0, hu1]
        · exact ⟨by
            have h := Derivation.identity Language.Set.Rel.eq ![u0, u1]
            have heq : Multiset.ofList [Semiformula.rel Language.Set.Rel.eq ![u0, u1],
                Semiformula.nrel Language.Set.Rel.eq ![u0, u1]] =
              ⦃Semiformula.rel Language.Set.Rel.eq ![u0, u1],
                Semiformula.nrel Language.Set.Rel.eq ![u0, u1]⦄ := by
              simp only [Multiset.atom, Multiset.singleton_add]; rfl
            rw [heq]; exact h⟩
      · refine ⟨[Semiformula.rel Language.Set.Rel.mem ![u0, u1],
            Semiformula.nrel Language.Set.Rel.mem ![u0, u1]], ?_, ?_⟩
        · change [encForm _, encForm _] = getStepSeq steps idx
          rw [getStepSeq, hseq]; simp [encForm, hu0, hu1]
        · exact ⟨by
            have h := Derivation.identity Language.Set.Rel.mem ![u0, u1]
            have heq : Multiset.ofList [Semiformula.rel Language.Set.Rel.mem ![u0, u1],
                Semiformula.nrel Language.Set.Rel.mem ![u0, u1]] =
              ⦃Semiformula.rel Language.Set.Rel.mem ![u0, u1],
                Semiformula.nrel Language.Set.Rel.mem ![u0, u1]⦄ := by
              simp only [Multiset.atom, Multiset.singleton_add]; rfl
            rw [heq]; exact h⟩
    · -- Rule 1: verum
      simp only [checkRule1, decide_eq_true_eq] at hstep
      refine ⟨[Semiformula.verum], ?_, ⟨by
        have heq : Multiset.ofList [Semiformula.verum] = (⦃⊤⦄ : Sequent ℒₛₑₜ) := rfl
        rw [heq]; exact Derivation.verum⟩⟩
      change [Nat.pair 0 0] = getStepSeq steps idx
      rw [getStepSeq, hstep]
    · -- Rule 2: contraction
      simp only [checkRule2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hstep
      rcases hstep with ⟨⟨hi, hwf⟩, hsub⟩
      obtain ⟨Lprev, hLprev, ⟨dprev⟩⟩ := ih _ hi (by omega)
      obtain ⟨L, hL⟩ := list_of_wfForm_all hwf
      refine ⟨L, hL, ⟨Derivation.contraction dprev ?_⟩⟩
      intro a ha
      have ha' : a ∈ Lprev := by simpa using ha
      have hmemPrev : encForm a ∈ getStepSeq steps ((steps.getD idx 0).unpair.2.unpair.2) := by
        rw [← hLprev]; exact List.mem_map_of_mem ha'
      obtain ⟨d, hd, hda⟩ := hsub (encForm a) hmemPrev
      rw [← hL] at hd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
      have hab : b = a := encForm_inj hda
      subst hab
      simpa using hb
    · -- Rule 3: cut
      simp only [checkRule3, Bool.and_eq_true, decide_eq_true_eq] at hstep
      rcases hstep with ⟨⟨⟨⟨⟨hi, hj⟩, hwf⟩, hheadI⟩, hheadJ⟩, hseq⟩
      obtain ⟨φ, hφ⟩ := (wfForm_iff 0 _).mp hwf
      obtain ⟨LI, hLI, ⟨dI⟩⟩ := ih _ hi (by omega)
      obtain ⟨LJ, hLJ, ⟨dJ⟩⟩ := ih _ hj (by omega)
      cases LI with
      | nil => rw [← hLI] at hheadI; simp at hheadI
      | cons a LA =>
        cases LJ with
        | nil => rw [← hLJ] at hheadJ; simp at hheadJ
        | cons b LB =>
          rw [← hLI] at hheadI; simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hheadI
          rw [← hLJ] at hheadJ; simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hheadJ
          have ha : a = φ := encForm_inj (hheadI.trans hφ.symm)
          have hb : b = ∼φ := encForm_inj (hheadJ.trans (by rw [← hφ, codeNeg_encForm]))
          subst ha hb
          refine ⟨LA ++ LB, ?_, ⟨?_⟩⟩
          · rw [getStepSeq, hseq, ← hLI, ← hLJ]; simp
          · rw [multiset_ofList_cons_eq_add_atom] at dI dJ
            have hd := Derivation.cut dI dJ
            simpa [Multiset.coe_add] using hd
    · -- Rule 4: or
      simp only [checkRule4, Bool.and_eq_true, decide_eq_true_eq] at hstep
      rcases hstep with ⟨⟨⟨⟨⟨hi, hwf1⟩, hwf2⟩, hhead1⟩, hhead2⟩, hseq⟩
      obtain ⟨φ, hφ⟩ := (wfForm_iff 0 _).mp hwf1
      obtain ⟨ψ, hψ⟩ := (wfForm_iff 0 _).mp hwf2
      obtain ⟨LI, hLI, ⟨dI⟩⟩ := ih _ hi (by omega)
      cases LI with
      | nil => rw [← hLI] at hhead1; simp at hhead1
      | cons a LI' =>
        cases LI' with
        | nil => rw [← hLI] at hhead2; simp at hhead2
        | cons b rest =>
          rw [← hLI] at hhead1 hhead2
          simp only [List.map_cons, List.head?_cons, List.tail_cons, Option.some.injEq] at hhead1 hhead2
          have ha : a = φ := encForm_inj (hhead1.trans hφ.symm)
          have hb : b = ψ := encForm_inj (hhead2.trans hψ.symm)
          subst a b
          refine ⟨(φ ⋎ ψ) :: rest, ?_, ⟨?_⟩⟩
          · change encForm (φ ⋎ ψ) :: rest.map encForm = getStepSeq steps idx
            rw [getStepSeq, hseq, ← hLI]; simp only [List.map_cons, List.tail_cons, encForm_or, codeOr, hφ, hψ]
          · rw [multiset_ofList_cons2_eq_add_atoms] at dI
            rw [multiset_ofList_cons_eq_add_atom]
            exact Derivation.or dI
    · -- Rule 5: and
      simp only [checkRule5, Bool.and_eq_true, decide_eq_true_eq] at hstep
      rcases hstep with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, hwf1⟩, hwf2⟩, hheadI⟩, hheadJ⟩, htailEq⟩, hseq⟩
      obtain ⟨φ, hφ⟩ := (wfForm_iff 0 _).mp hwf1
      obtain ⟨ψ, hψ⟩ := (wfForm_iff 0 _).mp hwf2
      obtain ⟨LI, hLI, ⟨dI⟩⟩ := ih _ hi (by omega)
      obtain ⟨LJ, hLJ, ⟨dJ⟩⟩ := ih _ hj (by omega)
      cases LI with
      | nil => rw [← hLI] at hheadI; simp at hheadI
      | cons a LA =>
        cases LJ with
        | nil => rw [← hLJ] at hheadJ; simp at hheadJ
        | cons b LB =>
          rw [← hLI] at hheadI htailEq
          rw [← hLJ] at hheadJ htailEq
          simp only [List.map_cons, List.head?_cons, List.tail_cons, Option.some.injEq] at hheadI hheadJ htailEq
          have ha : a = φ := encForm_inj (hheadI.trans hφ.symm)
          have hb : b = ψ := encForm_inj (hheadJ.trans hψ.symm)
          have hAB : LA = LB := List.map_injective_iff.mpr encForm_inj htailEq
          subst a b LB
          refine ⟨(φ ⋏ ψ) :: LA, ?_, ⟨?_⟩⟩
          · change encForm (φ ⋏ ψ) :: LA.map encForm = getStepSeq steps idx
            rw [getStepSeq, hseq, ← hLI]; simp only [List.map_cons, List.tail_cons, encForm_and, codeAnd, hφ, hψ]
          · rw [multiset_ofList_cons_eq_add_atom] at dI dJ
            rw [multiset_ofList_cons_eq_add_atom]
            exact Derivation.and dI dJ
    · -- Rule 6: all
      simp only [checkRule6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hstep
      rcases hstep with ⟨⟨⟨⟨hi, hwf1⟩, hheadSeq⟩, hwfTail⟩, hsIeq⟩
      obtain ⟨φ, hφ⟩ := (wfForm_iff 1 _).mp hwf1
      obtain ⟨LI, hLI, ⟨dI⟩⟩ := ih _ hi (by omega)
      obtain ⟨LTail, hLTail⟩ := list_of_wfForm_all hwfTail
      have hseqEq : getStepSeq steps idx = codeAll (encForm φ) :: LTail.map encForm := by
        rw [getStepSeq, hLTail, hφ]
        cases hs : decList (steps.getD idx 0).unpair.1 with
        | nil => rw [hs] at hheadSeq; simp at hheadSeq
        | cons x xs =>
          rw [hs] at hheadSeq
          simp only [List.head?_cons, Option.some.injEq] at hheadSeq
          simp [hheadSeq]
      have hLI_eq : LI = φ.free :: LTail.map Rewriting.shift := by
        apply List.map_injective_iff.mpr encForm_inj
        rw [hLI, hsIeq, ← hLTail, ← hφ, codeFreeForm_encForm]
        simp only [List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left fun ψ _ => codeShiftForm_encForm ψ
      subst hLI_eq
      refine ⟨(∀¹ φ) :: LTail, ?_, ⟨?_⟩⟩
      · rw [hseqEq]; rfl
      · rw [multiset_ofList_cons_eq_add_atom] at dI
        have hsh : Multiset.ofList (LTail.map Rewriting.shift) = (Multiset.ofList LTail)⁺ := rfl
        rw [hsh] at dI
        rw [multiset_ofList_cons_eq_add_atom]
        exact Derivation.all dI
    · -- Rule 7: exs
      simp only [checkRule7, Bool.and_eq_true, decide_eq_true_eq] at hstep
      rcases hstep with ⟨⟨⟨⟨hi, hwf1⟩, hwft⟩, hheadI⟩, hseq⟩
      obtain ⟨φ, hφ⟩ := (wfForm_iff 1 _).mp hwf1
      obtain ⟨t, ht⟩ := (wfTerm_iff 0 _).mp hwft
      obtain ⟨LI, hLI, ⟨dI⟩⟩ := ih _ hi (by omega)
      cases LI with
      | nil => rw [← hLI] at hheadI; simp at hheadI
      | cons a LA =>
        rw [← hLI] at hheadI
        simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hheadI
        have ha : a = φ/[t] := encForm_inj (hheadI.trans (by rw [← hφ, ← ht, codeSubst0_encForm]))
        subst ha
        refine ⟨(∃¹ φ) :: LA, ?_, ⟨?_⟩⟩
        · change encForm (∃¹ φ) :: LA.map encForm = getStepSeq steps idx
          rw [getStepSeq, hseq, ← hLI]; simp [encForm, codeExs, hφ]
        · rw [multiset_ofList_cons_eq_add_atom] at dI
          rw [multiset_ofList_cons_eq_add_atom]
          exact Derivation.exs dI

lemma checkProof_sound (σ : SetTheorySentence) (w : ℕ)
    (h : checkProof (encClosed σ) w = true) :
    FFL.Entailment.Provable 𝗭𝗙𝗖 σ := by
  unfold checkProof at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rcases h with ⟨⟨hallAx, hallSteps⟩, ⟨hlenPos, hlast⟩⟩
  set axList := decList w.unpair.1
  set steps := decList w.unpair.2
  have haxEx : ∀ e ∈ axList, ∃ ψ ∈ 𝗭𝗙𝗖, encClosed ψ = (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0 := by
    intro e he
    have hisSome := hallAx e he
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hisSome
    have hmem : ∃ ψ ∈ 𝗭𝗙𝗖, encClosed ψ = c := (zfcAxiomCode_iff c).mp ⟨e.unpair.1, e.unpair.2, hc⟩
    simpa [hc] using hmem
  have haxListEx : ∀ l : List ℕ,
      (∀ e ∈ l, ∃ ψ ∈ 𝗭𝗙𝗖, encClosed ψ = (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0) →
      ∃ Ψ : List SetTheorySentence, (∀ ψ ∈ Ψ, ψ ∈ 𝗭𝗙𝗖) ∧
        Ψ.map encClosed = l.map (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0) := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], by simp, rfl⟩
    | cons e es ih =>
      intro he
      obtain ⟨ψ, hψZ, hψC⟩ := he e (by simp)
      obtain ⟨Ψ, hΨZ, hΨC⟩ := ih (fun x hx => he x (by simp [hx]))
      exact ⟨ψ :: Ψ, by intro x hx; rcases List.mem_cons.mp hx with rfl | hx'; exacts [hψZ, hΨZ x hx'],
        by simp [hψC, hΨC]⟩
  obtain ⟨Ψ, hΨZ, hΨC⟩ := haxListEx axList haxEx
  obtain ⟨L, hL, ⟨d⟩⟩ := checkStep_sound steps hallSteps (steps.length - 1) (by omega)
  have hLeq : L = (Rewriting.emb σ : Proposition ℒₛₑₜ) ::
      Ψ.map (fun ψ => (Rewriting.emb (∼ψ) : Proposition ℒₛₑₜ)) := by
    apply List.map_injective_iff.mpr encForm_inj
    rw [hL, hlast, ← hΨC]
    simp only [List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun ψ _ => ?_
    change codeNeg (encForm (Rewriting.emb ψ)) = encForm (Rewriting.emb (∼ψ))
    rw [emb_neg, codeNeg_encForm]
  subst hLeq
  have hseqEq : Multiset.ofList ((Rewriting.emb σ : Proposition ℒₛₑₜ) ::
        Ψ.map (fun ψ => (Rewriting.emb (∼ψ) : Proposition ℒₛₑₜ))) =
      (⦃σ⦄ + ∼Multiset.ofList Ψ).map Rewriting.emb := by
    change (Rewriting.emb σ : Proposition ℒₛₑₜ) ::ₘ
        Multiset.ofList (Ψ.map (fun ψ => (Rewriting.emb (∼ψ) : Proposition ℒₛₑₜ))) =
      ({σ} + (Multiset.ofList Ψ).map (∼·)).map Rewriting.emb
    rw [Multiset.map_add, Multiset.map_singleton, Multiset.singleton_add]
    congr 1
    simp [List.map_map, Function.comp_def]
  rw [hseqEq] at d
  exact ⟨⟨Multiset.ofList Ψ, fun ψ hψ => hΨZ ψ (by simpa using hψ), d⟩⟩

/- ### C.4. Completeness of `checkProof` -/

private def shiftRule (k rule : ℕ) : ℕ :=
  let rtag := rule.unpair.1
  let rarg := rule.unpair.2
  if rtag == 2 then Nat.pair 2 (k + rarg)
  else if rtag == 3 then
    Nat.pair 3 (Nat.pair (k + rarg.unpair.1) (Nat.pair (k + rarg.unpair.2.unpair.1) rarg.unpair.2.unpair.2))
  else if rtag == 4 then
    Nat.pair 4 (Nat.pair (k + rarg.unpair.1) rarg.unpair.2)
  else if rtag == 5 then
    Nat.pair 5 (Nat.pair (k + rarg.unpair.1) (Nat.pair (k + rarg.unpair.2.unpair.1) rarg.unpair.2.unpair.2))
  else if rtag == 6 then
    Nat.pair 6 (Nat.pair (k + rarg.unpair.1) rarg.unpair.2)
  else if rtag == 7 then
    Nat.pair 7 (Nat.pair (k + rarg.unpair.1) rarg.unpair.2)
  else rule

private def shiftStep (k st : ℕ) : ℕ :=
  Nat.pair st.unpair.1 (shiftRule k st.unpair.2)

private lemma getStepSeq_append_left (s1 s2 : List ℕ) {i : ℕ} (hi : i < s1.length) :
    getStepSeq (s1 ++ s2) i = getStepSeq s1 i := by
  unfold getStepSeq
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hi,
    ← List.getD_eq_getElem _ _ hi]

private lemma getStepSeq_append_shift (s1 s2 : List ℕ) {i : ℕ} (hi : i < s2.length) :
    getStepSeq (s1 ++ s2.map (shiftStep s1.length)) (s1.length + i) = getStepSeq s2 i := by
  unfold getStepSeq
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem_map, shiftStep, Nat.unpair_pair]
  rw [← List.getD_eq_getElem _ _ hi]

private lemma checkStep_append_left (s1 s2 : List ℕ) {idx : ℕ} (hidx : idx < s1.length)
    (h : checkStep s1 idx = true) : checkStep (s1 ++ s2) idx = true := by
  have hget : (s1 ++ s2).getD idx 0 = s1.getD idx 0 := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hidx,
      ← List.getD_eq_getElem _ _ hidx]
  unfold checkStep at h ⊢
  dsimp only at h ⊢
  rw [hget]
  split_ifs at h ⊢ with h0 h1 h2 h3 h4 h5 h6 h7
  · simpa only [checkRule0, hget] using h
  · simpa only [checkRule1, hget] using h
  · simp only [checkRule2, hget, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨hi, hwf⟩, hsub⟩
    rw [getStepSeq_append_left s1 s2 (by omega)]
    exact ⟨⟨hi, hwf⟩, hsub⟩
  · simp only [checkRule3, hget, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, hj⟩, hwf⟩, h1'⟩, h2'⟩, h3'⟩
    rw [getStepSeq_append_left s1 s2 (by omega), getStepSeq_append_left s1 s2 (by omega)]
    exact ⟨⟨⟨⟨⟨hi, hj⟩, hwf⟩, h1'⟩, h2'⟩, h3'⟩
  · simp only [checkRule4, hget, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩
    rw [getStepSeq_append_left s1 s2 (by omega)]
    exact ⟨⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩
  · simp only [checkRule5, hget, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩
    rw [getStepSeq_append_left s1 s2 (by omega), getStepSeq_append_left s1 s2 (by omega)]
    exact ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩
  · simp only [checkRule6, hget, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩
    rw [getStepSeq_append_left s1 s2 (by omega)]
    exact ⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩
  · simp only [checkRule7, hget, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩
    rw [getStepSeq_append_left s1 s2 (by omega)]
    exact ⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩

private lemma checkStep_append_right (s1 s2 : List ℕ) {idx : ℕ} (hidx : idx < s2.length)
    (h : checkStep s2 idx = true) :
    checkStep (s1 ++ s2.map (shiftStep s1.length)) (s1.length + idx) = true := by
  have hget : (s1 ++ s2.map (shiftStep s1.length)).getD (s1.length + idx) 0 =
      shiftStep s1.length (s2.getD idx 0) := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, List.getElem_map]
    rw [← List.getD_eq_getElem _ _ hidx]
  set st := s2.getD idx 0 with hst
  have hst' : s2.getD idx 0 = st := rfl
  have htag_eq : (shiftStep s1.length st).unpair.2.unpair.1 = st.unpair.2.unpair.1 := by
    unfold shiftStep shiftRule
    simp only [Nat.unpair_pair]
    split_ifs with g2 g3 g4 g5 g6 g7
    · simp only [Nat.unpair_pair]; exact (beq_iff_eq.mp g2).symm
    · simp only [Nat.unpair_pair]; exact (beq_iff_eq.mp g3).symm
    · simp only [Nat.unpair_pair]; exact (beq_iff_eq.mp g4).symm
    · simp only [Nat.unpair_pair]; exact (beq_iff_eq.mp g5).symm
    · simp only [Nat.unpair_pair]; exact (beq_iff_eq.mp g6).symm
    · simp only [Nat.unpair_pair]; exact (beq_iff_eq.mp g7).symm
    · rfl
  unfold checkStep at h ⊢
  dsimp only at h ⊢
  rw [hget, htag_eq]
  split_ifs at h ⊢ with h0 h1 h2 h3 h4 h5 h6 h7
  · have hrule : shiftRule s1.length st.unpair.2 = st.unpair.2 := by
      have : st.unpair.2.unpair.1 = 0 := by simpa using h0
      simp [shiftRule, this]
    simpa only [checkRule0, hget, hst', shiftStep, Nat.unpair_pair, hrule] using h
  · simpa only [checkRule1, hget, hst', shiftStep, Nat.unpair_pair] using h
  · have htag : st.unpair.2.unpair.1 = 2 := by simpa using h2
    have hrule : shiftRule s1.length st.unpair.2 = Nat.pair 2 (s1.length + st.unpair.2.unpair.2) := by
      unfold shiftRule; simp [htag]
    simp only [checkRule2, hget, hst', shiftStep, hrule, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨hi, hwf⟩, hsub⟩
    rw [getStepSeq_append_shift s1 s2 (by omega)]
    exact ⟨⟨by omega, hwf⟩, hsub⟩
  · have htag : st.unpair.2.unpair.1 = 3 := by simpa using h3
    have hrule : shiftRule s1.length st.unpair.2 =
        Nat.pair 3 (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.1)
          (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.2.unpair.1)
            st.unpair.2.unpair.2.unpair.2.unpair.2)) := by
      unfold shiftRule; simp [htag]
    simp only [checkRule3, hget, hst', shiftStep, hrule, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, hj⟩, hwf⟩, h1'⟩, h2'⟩, h3'⟩
    rw [getStepSeq_append_shift s1 s2 (by omega), getStepSeq_append_shift s1 s2 (by omega)]
    exact ⟨⟨⟨⟨⟨by omega, by omega⟩, hwf⟩, h1'⟩, h2'⟩, h3'⟩
  · have htag : st.unpair.2.unpair.1 = 4 := by simpa using h4
    have hrule : shiftRule s1.length st.unpair.2 =
        Nat.pair 4 (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.1)
          st.unpair.2.unpair.2.unpair.2) := by
      unfold shiftRule; simp [htag]
    simp only [checkRule4, hget, hst', shiftStep, hrule, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩
    rw [getStepSeq_append_shift s1 s2 (by omega)]
    exact ⟨⟨⟨⟨⟨by omega, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩
  · have htag : st.unpair.2.unpair.1 = 5 := by simpa using h5
    have hrule : shiftRule s1.length st.unpair.2 =
        Nat.pair 5 (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.1)
          (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.2.unpair.1)
            st.unpair.2.unpair.2.unpair.2.unpair.2)) := by
      unfold shiftRule; simp [htag]
    simp only [checkRule5, hget, hst', shiftStep, hrule, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨⟨⟨⟨hi, hj⟩, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩
    rw [getStepSeq_append_shift s1 s2 (by omega), getStepSeq_append_shift s1 s2 (by omega)]
    exact ⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, h1'⟩, h2'⟩, h3'⟩, h4'⟩, h5'⟩, h6'⟩
  · have htag : st.unpair.2.unpair.1 = 6 := by simpa using h6
    have hrule : shiftRule s1.length st.unpair.2 =
        Nat.pair 6 (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.1)
          st.unpair.2.unpair.2.unpair.2) := by
      unfold shiftRule; simp [htag]
    simp only [checkRule6, hget, hst', shiftStep, hrule, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩
    rw [getStepSeq_append_shift s1 s2 (by omega)]
    exact ⟨⟨⟨⟨by omega, h1'⟩, h2'⟩, h3'⟩, h4'⟩
  · have htag : st.unpair.2.unpair.1 = 7 := by simpa using h7
    have hrule : shiftRule s1.length st.unpair.2 =
        Nat.pair 7 (Nat.pair (s1.length + st.unpair.2.unpair.2.unpair.1)
          st.unpair.2.unpair.2.unpair.2) := by
      unfold shiftRule; simp [htag]
    simp only [checkRule7, hget, hst', shiftStep, hrule, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    rcases h with ⟨⟨⟨⟨hi, h1'⟩, h2'⟩, h3'⟩, h4'⟩
    rw [getStepSeq_append_shift s1 s2 (by omega)]
    exact ⟨⟨⟨⟨by omega, h1'⟩, h2'⟩, h3'⟩, h4'⟩

private lemma decList_encode (l : List ℕ) : decList (Encodable.encode l) = l := by
  simp only [decList, Encodable.encodek, Option.getD_some]

private lemma append_contraction (s : List ℕ) (L L' : List (Proposition ℒₛₑₜ))
    (hsPos : 0 < s.length)
    (hsOk : ∀ idx < s.length, checkStep s idx = true)
    (hlast : getStepSeq s (s.length - 1) = L.map encForm)
    (hsub : Multiset.ofList L ⊆ Multiset.ofList L') :
    ∃ s' : List ℕ, 0 < s'.length ∧ (∀ idx < s'.length, checkStep s' idx = true) ∧
      getStepSeq s' (s'.length - 1) = L'.map encForm := by
  let newStep := Nat.pair (Encodable.encode (L'.map encForm)) (Nat.pair 2 (s.length - 1))
  refine ⟨s ++ [newStep], by simp, ?_, ?_⟩
  · intro idx hidx
    simp only [List.length_append, List.length_singleton] at hidx
    by_cases hlt : idx < s.length
    · exact checkStep_append_left s [newStep] hlt (hsOk idx hlt)
    · have heq : idx = s.length := by omega
      subst heq
      have hget : (s ++ [newStep]).getD s.length 0 = newStep := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
        simp
      have hprev : getStepSeq (s ++ [newStep]) (s.length - 1) = L.map encForm := by
        rw [getStepSeq_append_left s [newStep] (by omega), hlast]
      have hcr : checkStep (s ++ [newStep]) s.length = checkRule2 (s ++ [newStep], s.length) := by
        unfold checkStep; rw [hget]; simp [newStep]
      rw [hcr]
      simp only [checkRule2, hget, newStep, Nat.unpair_pair, decList_encode, hprev,
        Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · intro c hc
        obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hc
        exact (wfForm_iff 0 _).mpr ⟨φ, rfl⟩
      · intro c hc
        obtain ⟨φ, hφL, rfl⟩ := List.mem_map.mp hc
        have hφL' : φ ∈ L' := by
          have : φ ∈ Multiset.ofList L := by simpa using hφL
          simpa using hsub this
        exact ⟨encForm φ, List.mem_map_of_mem hφL', rfl⟩
  · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    unfold getStepSeq
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
    simp only [Nat.sub_self, List.getElem_singleton, newStep, Nat.unpair_pair, decList_encode]

private lemma derivation_complete {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    ∀ L : List (Proposition ℒₛₑₜ), Multiset.ofList L = Γ →
      ∃ s : List ℕ, 0 < s.length ∧ (∀ idx < s.length, checkStep s idx = true) ∧
        getStepSeq s (s.length - 1) = L.map encForm := by
  induction d with
  | identity r v =>
    intro L hL
    cases r with
    | eq =>
      let L0 : List (Proposition ℒₛₑₜ) :=
        [Semiformula.rel Language.Set.Rel.eq v, Semiformula.nrel Language.Set.Rel.eq v]
      let st := Nat.pair (Encodable.encode (L0.map encForm))
        (Nat.pair 0 (Nat.pair 0 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))))
      have h0 : checkStep [st] 0 = true := by
        have hcr : checkStep [st] 0 = checkRule0 ([st], 0) := by
          unfold checkStep; simp [st]
        rw [hcr]
        have hwf0 : wfTerm 0 (encTerm (v 0)) = true := (wfTerm_iff 0 _).mpr ⟨v 0, rfl⟩
        have hwf1 : wfTerm 0 (encTerm (v 1)) = true := (wfTerm_iff 0 _).mpr ⟨v 1, rfl⟩
        simp only [checkRule0, List.getD_cons_zero, st, Nat.unpair_pair, decList_encode,
          hwf0, hwf1, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨by decide, trivial⟩, trivial⟩, rfl⟩
      have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
        rw [hL]
        intro a ha
        simp only [L0, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> simp [Multiset.atom]
      exact append_contraction [st] L0 L (by simp) (fun idx hi => by
        have : idx = 0 := by simp at hi; omega
        subst this; exact h0)
        (by simp only [List.length_singleton, Nat.sub_self, getStepSeq, List.getD_cons_zero,
          st, Nat.unpair_pair, decList_encode]) hsub
    | mem =>
      let L0 : List (Proposition ℒₛₑₜ) :=
        [Semiformula.rel Language.Set.Rel.mem v, Semiformula.nrel Language.Set.Rel.mem v]
      let st := Nat.pair (Encodable.encode (L0.map encForm))
        (Nat.pair 0 (Nat.pair 1 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))))
      have h0 : checkStep [st] 0 = true := by
        have hcr : checkStep [st] 0 = checkRule0 ([st], 0) := by
          unfold checkStep; simp [st]
        rw [hcr]
        have hwf0 : wfTerm 0 (encTerm (v 0)) = true := (wfTerm_iff 0 _).mpr ⟨v 0, rfl⟩
        have hwf1 : wfTerm 0 (encTerm (v 1)) = true := (wfTerm_iff 0 _).mpr ⟨v 1, rfl⟩
        simp only [checkRule0, List.getD_cons_zero, st, Nat.unpair_pair, decList_encode,
          hwf0, hwf1, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨by decide, trivial⟩, trivial⟩, rfl⟩
      have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
        rw [hL]
        intro a ha
        simp only [L0, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> simp [Multiset.atom]
      exact append_contraction [st] L0 L (by simp) (fun idx hi => by
        have : idx = 0 := by simp at hi; omega
        subst this; exact h0)
        (by simp only [List.length_singleton, Nat.sub_self, getStepSeq, List.getD_cons_zero,
          st, Nat.unpair_pair, decList_encode]) hsub
  | verum =>
    intro L hL
    let L0 : List (Proposition ℒₛₑₜ) := [⊤]
    let st := Nat.pair (Encodable.encode (L0.map encForm)) (Nat.pair 1 0)
    have h0 : checkStep [st] 0 = true := by
      have hcr : checkStep [st] 0 = checkRule1 ([st], 0) := by
        unfold checkStep; simp [st]
      rw [hcr]
      simp only [checkRule1, List.getD_cons_zero, st, Nat.unpair_pair, decList_encode,
        decide_eq_true_eq]
      rfl
    have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
      rw [hL]; intro a ha; simpa [L0, Multiset.atom] using ha
    exact append_contraction [st] L0 L (by simp) (fun idx hi => by
      have : idx = 0 := by simp at hi; omega
      subst this; exact h0)
      (by simp only [List.length_singleton, Nat.sub_self, getStepSeq, List.getD_cons_zero,
        st, Nat.unpair_pair, decList_encode]) hsub
  | @contraction Δ Γ _ hsub ih =>
    intro L hL
    rcases Quotient.exists_rep Δ with ⟨LΔ, rfl⟩
    obtain ⟨s, hsPos, hsOk, hlast⟩ := ih LΔ rfl
    have hsub' : Multiset.ofList LΔ ⊆ Multiset.ofList L := by rw [hL]; exact hsub
    exact append_contraction s LΔ L hsPos hsOk hlast hsub'
  | @cut Γ φ Δ _ _ ih1 ih2 =>
    intro L hL
    rcases Quotient.exists_rep Γ with ⟨LΓ, rfl⟩
    rcases Quotient.exists_rep Δ with ⟨LΔ, rfl⟩
    obtain ⟨s1, hs1Pos, hs1Ok, hlast1⟩ := ih1 (φ :: LΓ) (multiset_ofList_cons_eq_add_atom φ LΓ)
    obtain ⟨s2, hs2Pos, hs2Ok, hlast2⟩ := ih2 ((∼φ) :: LΔ) (multiset_ofList_cons_eq_add_atom (∼φ) LΔ)
    let s12 := s1 ++ s2.map (shiftStep s1.length)
    let i1 := s1.length - 1
    let i2 := s1.length + (s2.length - 1)
    let newStep := Nat.pair (Encodable.encode ((LΓ ++ LΔ).map encForm))
      (Nat.pair 3 (Nat.pair i1 (Nat.pair i2 (encForm φ))))
    let s := s12 ++ [newStep]
    have hsOk : ∀ idx < s.length, checkStep s idx = true := by
      intro idx hidx
      simp only [s, s12, List.length_append, List.length_map, List.length_singleton] at hidx
      by_cases h1 : idx < s1.length
      · have h1' := checkStep_append_left s1 (s2.map (shiftStep s1.length)) h1 (hs1Ok idx h1)
        exact checkStep_append_left s12 [newStep] (by simp [s12]; omega) h1'
      · by_cases h2 : idx < s1.length + s2.length
        · have hk : idx - s1.length < s2.length := by omega
          have h2' := checkStep_append_right s1 s2 hk (hs2Ok (idx - s1.length) hk)
          have hidxEq : s1.length + (idx - s1.length) = idx := by omega
          rw [hidxEq] at h2'
          exact checkStep_append_left s12 [newStep] (by simp [s12]; omega) h2'
        · have heq : idx = s12.length := by simp [s12]; omega
          subst heq
          have hget : s.getD s12.length 0 = newStep := by
            simp only [s]
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]; simp
          have hg1 : getStepSeq s i1 = encForm φ :: LΓ.map encForm := by
            simp only [s]
            rw [getStepSeq_append_left s12 [newStep] (by simp [s12, i1]; omega),
              getStepSeq_append_left s1 _ (by omega), hlast1]; rfl
          have hg2 : getStepSeq s i2 = codeNeg (encForm φ) :: LΔ.map encForm := by
            simp only [s]
            rw [getStepSeq_append_left s12 [newStep] (by simp [s12, i2]; omega),
              getStepSeq_append_shift s1 s2 (by omega), hlast2, List.map_cons, codeNeg_encForm]
          have hwf : wfForm (0, encForm φ) = true := (wfForm_iff 0 _).mpr ⟨φ, rfl⟩
          have hcr : checkStep s s12.length = checkRule3 (s, s12.length) := by
            unfold checkStep; rw [hget]; simp [newStep]
          rw [hcr]
          simp only [checkRule3, hget, newStep, Nat.unpair_pair, decList_encode, hg1, hg2, hwf,
            Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨⟨⟨by simp [s12, i1]; omega, by simp [s12, i2]; omega⟩, trivial⟩, rfl⟩, rfl⟩, ?_⟩
          simp
    have hlast : getStepSeq s (s.length - 1) = (LΓ ++ LΔ).map encForm := by
      simp only [s, List.length_append, List.length_singleton, Nat.add_sub_cancel]
      unfold getStepSeq
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, newStep, Nat.unpair_pair, decList_encode]
    have hsub : Multiset.ofList (LΓ ++ LΔ) ⊆ Multiset.ofList L := by
      rw [← Multiset.coe_add, hL]
      exact Multiset.Subset.refl _
    exact append_contraction s (LΓ ++ LΔ) L (by simp [s]) hsOk hlast hsub
  | @or Γ φ ψ _ ih =>
    intro L hL
    rcases Quotient.exists_rep Γ with ⟨LΓ, rfl⟩
    obtain ⟨s1, hs1Pos, hs1Ok, hlast1⟩ := ih (φ :: ψ :: LΓ) (multiset_ofList_cons2_eq_add_atoms φ ψ LΓ)
    let i1 := s1.length - 1
    let L0 := (φ ⋎ ψ) :: LΓ
    let newStep := Nat.pair (Encodable.encode (L0.map encForm))
      (Nat.pair 4 (Nat.pair i1 (Nat.pair (encForm φ) (encForm ψ))))
    let s := s1 ++ [newStep]
    have hsOk : ∀ idx < s.length, checkStep s idx = true := by
      intro idx hidx
      simp only [s, List.length_append, List.length_singleton] at hidx
      by_cases h1 : idx < s1.length
      · exact checkStep_append_left s1 [newStep] h1 (hs1Ok idx h1)
      · have heq : idx = s1.length := by omega
        subst heq
        have hget : s.getD s1.length 0 = newStep := by
          simp only [s]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]; simp
        have hg1 : getStepSeq s i1 = encForm φ :: encForm ψ :: LΓ.map encForm := by
          simp only [s]
          rw [getStepSeq_append_left s1 [newStep] (by omega), hlast1]; rfl
        have hwf1 : wfForm (0, encForm φ) = true := (wfForm_iff 0 _).mpr ⟨φ, rfl⟩
        have hwf2 : wfForm (0, encForm ψ) = true := (wfForm_iff 0 _).mpr ⟨ψ, rfl⟩
        have hcr : checkStep s s1.length = checkRule4 (s, s1.length) := by
          unfold checkStep; rw [hget]; simp [newStep]
        rw [hcr]
        simp only [checkRule4, hget, newStep, Nat.unpair_pair, decList_encode, hg1, hwf1, hwf2,
          Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨⟨⟨⟨by simp [i1]; omega, trivial⟩, trivial⟩, rfl⟩, rfl⟩, ?_⟩
        simp [L0, encForm_or, codeOr]
    have hlast : getStepSeq s (s.length - 1) = L0.map encForm := by
      simp only [s, List.length_append, List.length_singleton, Nat.add_sub_cancel]
      unfold getStepSeq
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, newStep, Nat.unpair_pair, decList_encode]
    have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
      rw [multiset_ofList_cons_eq_add_atom, hL]
      exact Multiset.Subset.refl _
    exact append_contraction s L0 L (by simp [s]) hsOk hlast hsub
  | @and Γ φ ψ _ _ ih1 ih2 =>
    intro L hL
    rcases Quotient.exists_rep Γ with ⟨LΓ, rfl⟩
    obtain ⟨s1, hs1Pos, hs1Ok, hlast1⟩ := ih1 (φ :: LΓ) (multiset_ofList_cons_eq_add_atom φ LΓ)
    obtain ⟨s2, hs2Pos, hs2Ok, hlast2⟩ := ih2 (ψ :: LΓ) (multiset_ofList_cons_eq_add_atom ψ LΓ)
    let s12 := s1 ++ s2.map (shiftStep s1.length)
    let i1 := s1.length - 1
    let i2 := s1.length + (s2.length - 1)
    let L0 := (φ ⋏ ψ) :: LΓ
    let newStep := Nat.pair (Encodable.encode (L0.map encForm))
      (Nat.pair 5 (Nat.pair i1 (Nat.pair i2 (Nat.pair (encForm φ) (encForm ψ)))))
    let s := s12 ++ [newStep]
    have hsOk : ∀ idx < s.length, checkStep s idx = true := by
      intro idx hidx
      simp only [s, s12, List.length_append, List.length_map, List.length_singleton] at hidx
      by_cases h1 : idx < s1.length
      · have h1' := checkStep_append_left s1 (s2.map (shiftStep s1.length)) h1 (hs1Ok idx h1)
        exact checkStep_append_left s12 [newStep] (by simp [s12]; omega) h1'
      · by_cases h2 : idx < s1.length + s2.length
        · have hk : idx - s1.length < s2.length := by omega
          have h2' := checkStep_append_right s1 s2 hk (hs2Ok (idx - s1.length) hk)
          have hidxEq : s1.length + (idx - s1.length) = idx := by omega
          rw [hidxEq] at h2'
          exact checkStep_append_left s12 [newStep] (by simp [s12]; omega) h2'
        · have heq : idx = s12.length := by simp [s12]; omega
          subst heq
          have hget : s.getD s12.length 0 = newStep := by
            simp only [s]
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]; simp
          have hg1 : getStepSeq s i1 = encForm φ :: LΓ.map encForm := by
            simp only [s]
            rw [getStepSeq_append_left s12 [newStep] (by simp [s12, i1]; omega),
              getStepSeq_append_left s1 _ (by omega), hlast1]; rfl
          have hg2 : getStepSeq s i2 = encForm ψ :: LΓ.map encForm := by
            simp only [s]
            rw [getStepSeq_append_left s12 [newStep] (by simp [s12, i2]; omega),
              getStepSeq_append_shift s1 s2 (by omega), hlast2]; rfl
          have hwf1 : wfForm (0, encForm φ) = true := (wfForm_iff 0 _).mpr ⟨φ, rfl⟩
          have hwf2 : wfForm (0, encForm ψ) = true := (wfForm_iff 0 _).mpr ⟨ψ, rfl⟩
          have hcr : checkStep s s12.length = checkRule5 (s, s12.length) := by
            unfold checkStep; rw [hget]; simp [newStep]
          rw [hcr]
          simp only [checkRule5, hget, newStep, Nat.unpair_pair, decList_encode, hg1, hg2,
            hwf1, hwf2, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨⟨⟨⟨⟨by simp [s12, i1]; omega, by simp [s12, i2]; omega⟩, trivial⟩, trivial⟩, rfl⟩, rfl⟩, rfl⟩, ?_⟩
          simp [L0, encForm_and, codeAnd]
    have hlast : getStepSeq s (s.length - 1) = L0.map encForm := by
      simp only [s, List.length_append, List.length_singleton, Nat.add_sub_cancel]
      unfold getStepSeq
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, newStep, Nat.unpair_pair, decList_encode]
    have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
      rw [multiset_ofList_cons_eq_add_atom, hL]
      exact Multiset.Subset.refl _
    exact append_contraction s L0 L (by simp [s]) hsOk hlast hsub
  | @all Γ φ _ ih =>
    intro L hL
    rcases Quotient.exists_rep Γ with ⟨LΓ, rfl⟩
    obtain ⟨s1, hs1Pos, hs1Ok, hlast1⟩ := ih (φ.free :: LΓ.map Rewriting.shift)
      (by rw [multiset_ofList_cons_eq_add_atom]; rfl)
    let i1 := s1.length - 1
    let L0 := (∀¹ φ) :: LΓ
    let newStep := Nat.pair (Encodable.encode (L0.map encForm)) (Nat.pair 6 (Nat.pair i1 (encForm φ)))
    let s := s1 ++ [newStep]
    have hsOk : ∀ idx < s.length, checkStep s idx = true := by
      intro idx hidx
      simp only [s, List.length_append, List.length_singleton] at hidx
      by_cases h1 : idx < s1.length
      · exact checkStep_append_left s1 [newStep] h1 (hs1Ok idx h1)
      · have heq : idx = s1.length := by omega
        subst heq
        have hget : s.getD s1.length 0 = newStep := by
          simp only [s]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]; simp
        have hg1 : getStepSeq s i1 = codeFreeForm (encForm φ) :: (LΓ.map encForm).map codeShiftForm := by
          simp only [s]
          rw [getStepSeq_append_left s1 [newStep] (by omega), hlast1, List.map_cons, codeFreeForm_encForm]
          congr 1
          simp only [List.map_map]
          refine List.map_congr_left fun ψ _ => (codeShiftForm_encForm ψ).symm
        have hwf1 : wfForm (1, encForm φ) = true := (wfForm_iff 1 _).mpr ⟨φ, rfl⟩
        have hcr : checkStep s s1.length = checkRule6 (s, s1.length) := by
          unfold checkStep; rw [hget]; simp [newStep]
        rw [hcr]
        simp only [checkRule6, hget, newStep, Nat.unpair_pair, decList_encode, hg1, hwf1,
          Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        refine ⟨⟨⟨⟨by simp [i1]; omega, trivial⟩, rfl⟩, ?_⟩, rfl⟩
        intro c hc
        simp only [L0, List.map_cons, List.tail_cons] at hc
        obtain ⟨ψ, _, rfl⟩ := List.mem_map.mp hc
        exact (wfForm_iff 0 _).mpr ⟨ψ, rfl⟩
    have hlast : getStepSeq s (s.length - 1) = L0.map encForm := by
      simp only [s, List.length_append, List.length_singleton, Nat.add_sub_cancel]
      unfold getStepSeq
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, newStep, Nat.unpair_pair, decList_encode]
    have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
      rw [multiset_ofList_cons_eq_add_atom, hL]
      exact Multiset.Subset.refl _
    exact append_contraction s L0 L (by simp [s]) hsOk hlast hsub
  | @exs Γ φ t _ ih =>
    intro L hL
    rcases Quotient.exists_rep Γ with ⟨LΓ, rfl⟩
    obtain ⟨s1, hs1Pos, hs1Ok, hlast1⟩ := ih ((φ/[t]) :: LΓ) (multiset_ofList_cons_eq_add_atom (φ/[t]) LΓ)
    let i1 := s1.length - 1
    let L0 := (∃¹ φ) :: LΓ
    let newStep := Nat.pair (Encodable.encode (L0.map encForm))
      (Nat.pair 7 (Nat.pair i1 (Nat.pair (encForm φ) (encTerm t))))
    let s := s1 ++ [newStep]
    have hsOk : ∀ idx < s.length, checkStep s idx = true := by
      intro idx hidx
      simp only [s, List.length_append, List.length_singleton] at hidx
      by_cases h1 : idx < s1.length
      · exact checkStep_append_left s1 [newStep] h1 (hs1Ok idx h1)
      · have heq : idx = s1.length := by omega
        subst heq
        have hget : s.getD s1.length 0 = newStep := by
          simp only [s]
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]; simp
        have hg1 : getStepSeq s i1 = codeSubst0 (encTerm t) (encForm φ) :: LΓ.map encForm := by
          simp only [s]
          rw [getStepSeq_append_left s1 [newStep] (by omega), hlast1, List.map_cons, codeSubst0_encForm]
        have hwf1 : wfForm (1, encForm φ) = true := (wfForm_iff 1 _).mpr ⟨φ, rfl⟩
        have hwft : wfTerm 0 (encTerm t) = true := (wfTerm_iff 0 _).mpr ⟨t, rfl⟩
        have hcr : checkStep s s1.length = checkRule7 (s, s1.length) := by
          unfold checkStep; rw [hget]; simp [newStep]
        rw [hcr]
        simp only [checkRule7, hget, newStep, Nat.unpair_pair, decList_encode, hg1, hwf1, hwft,
          Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨⟨⟨by simp [i1]; omega, trivial⟩, trivial⟩, rfl⟩, ?_⟩
        simp [L0, encForm, codeExs]
    have hlast : getStepSeq s (s.length - 1) = L0.map encForm := by
      simp only [s, List.length_append, List.length_singleton, Nat.add_sub_cancel]
      unfold getStepSeq
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, newStep, Nat.unpair_pair, decList_encode]
    have hsub : Multiset.ofList L0 ⊆ Multiset.ofList L := by
      rw [multiset_ofList_cons_eq_add_atom, hL]
      exact Multiset.Subset.refl _
    exact append_contraction s L0 L (by simp [s]) hsOk hlast hsub

lemma checkProof_complete (σ : SetTheorySentence) (h : FFL.Entailment.Provable 𝗭𝗙𝗖 σ) :
    ∃ w : ℕ, checkProof (encClosed σ) w = true := by
  obtain ⟨⟨ax, hax_mem, hderiv⟩⟩ := h
  rcases Quotient.exists_rep ax with ⟨Ψ, rfl⟩
  have hΨZ : ∀ ψ ∈ Ψ, ψ ∈ 𝗭𝗙𝗖 := fun ψ hψ => hax_mem ψ (by simpa using hψ)
  have haxEnc : ∀ l : List SetTheorySentence, (∀ ψ ∈ l, ψ ∈ 𝗭𝗙𝗖) →
      ∃ axList : List ℕ,
        (∀ e ∈ axList, (zfcAxiomCode e.unpair.1 e.unpair.2).isSome = true) ∧
        axList.map (fun e => (zfcAxiomCode e.unpair.1 e.unpair.2).getD 0) = l.map encClosed := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], by simp, rfl⟩
    | cons ψ ψs ih =>
      intro hl
      obtain ⟨tag, φ, htag⟩ := (zfcAxiomCode_iff (encClosed ψ)).mpr ⟨ψ, hl ψ (by simp), rfl⟩
      obtain ⟨axL, hok, hmap⟩ := ih (fun x hx => hl x (by simp [hx]))
      refine ⟨Nat.pair tag φ :: axL, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · simp [htag]
        · exact hok e he'
      · simp [htag, hmap]
  obtain ⟨axList, haxOk, haxMap⟩ := haxEnc Ψ hΨZ
  let L : List (Proposition ℒₛₑₜ) :=
    (Rewriting.emb σ : Proposition ℒₛₑₜ) :: Ψ.map (fun ψ => (Rewriting.emb (∼ψ) : Proposition ℒₛₑₜ))
  have hLeq : Multiset.ofList L = (⦃σ⦄ + ∼Multiset.ofList Ψ).map Rewriting.emb := by
    change (Rewriting.emb σ : Proposition ℒₛₑₜ) ::ₘ
        Multiset.ofList (Ψ.map (fun ψ => (Rewriting.emb (∼ψ) : Proposition ℒₛₑₜ))) =
      ({σ} + (Multiset.ofList Ψ).map (∼·)).map Rewriting.emb
    rw [Multiset.map_add, Multiset.map_singleton, Multiset.singleton_add]
    congr 1
    simp [List.map_map, Function.comp_def]
  obtain ⟨steps, hPos, hOk, hLast⟩ := derivation_complete hderiv L hLeq
  refine ⟨Nat.pair (Encodable.encode axList) (Encodable.encode steps), ?_⟩
  unfold checkProof
  simp only [Nat.unpair_pair, decList_encode, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨haxOk, hOk⟩, ⟨hPos, ?_⟩⟩
  rw [hLast, haxMap]
  simp only [L, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun ψ _ => ?_
  change encForm (Rewriting.emb (∼ψ)) = codeNeg (encForm (Rewriting.emb ψ))
  rw [emb_neg, codeNeg_encForm]

lemma checkProof_iff (σ : SetTheorySentence) :
    (∃ w : ℕ, checkProof (encClosed σ) w = true) ↔ FFL.Entailment.Provable 𝗭𝗙𝗖 σ :=
  ⟨fun ⟨w, hw⟩ => checkProof_sound σ w hw, checkProof_complete σ⟩

/- ### C.5. Main RE Theorem for `∼Constant14.halts (prependMachine (inputBits ...) U)` -/

theorem rePred_provable_not_halts {N_U : ℕ} [NeZero N_U] (U : Machine (Fin 2) (Fin N_U))
    (B_head B_bit0 B_bit1 : List Bool) :
    REPred (fun c : Nat.Partrec.Code =>
      FFL.Entailment.Provable 𝗭𝗙𝗖
        (∼Constant14.halts (C14H4TM.prependMachine
          (C14H4TM.inputBits B_head B_bit0 B_bit1 (Encodable.encode c)) U))) := by
  let f : Nat.Partrec.Code → ℕ := fun c =>
    codeNotHaltsPrepend N_U (uTransOf U)
      (C14H4TM.inputBits B_head B_bit0 B_bit1 (Encodable.encode c))
  have hf : Primrec f :=
    (codeNotHaltsPrepend_primrec N_U (uTransOf U)).comp
      ((C14H4TM.inputBits_primrec B_head B_bit0 B_bit1).comp Primrec.encode)
  have hpred : Primrec₂ (fun (c : Nat.Partrec.Code) (w : ℕ) => checkProof (f c) w) :=
    Primrec.to₂ <| checkProof_primrec.comp (hf.comp Primrec.fst) Primrec.snd
  let p : Nat.Partrec.Code → ℕ →. Bool := fun c w => Part.some (checkProof (f c) w)
  have hpart : Partrec₂ p := hpred.to_comp.partrec₂
  have hre : REPred (fun c : Nat.Partrec.Code => (Nat.rfind (p c)).Dom) :=
    (Partrec.rfind hpart).dom_re
  refine REPred.of_eq hre fun c => ?_
  rw [Nat.rfind_dom]
  have hdom : (∃ w, true ∈ p c w ∧ ∀ {m : ℕ}, m < w → (p c m).Dom) ↔
      ∃ w, checkProof (f c) w = true := by
    constructor
    · rintro ⟨w, hw, _⟩
      exact ⟨w, by rcases hw with ⟨_, hget⟩; simpa [p] using hget⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, by simp [p, hw], fun _ => trivial⟩
  rw [hdom]
  have hfc : f c = encClosed (∼Constant14.halts
      (C14H4TM.prependMachine (C14H4TM.inputBits B_head B_bit0 B_bit1 (Encodable.encode c)) U)) :=
    codeNotHaltsPrepend_encClosed U _
  rw [hfc]
  exact checkProof_iff _

end C14H4RE

theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1.H4 := by
  by_contra hnot
  obtain ⟨N_U, hNeU, U, B_head, B_bit0, B_bit1, hU⟩ := C14H4TM.exists_universal_bb
  have hre := C14H4RE.rePred_provable_not_halts U B_head B_bit0 B_bit1
  have hreNotDom : REPred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) := by
    refine REPred.of_eq hre fun c => ?_
    let L := C14H4TM.inputBits B_head B_bit0 B_bit1 (Encodable.encode c)
    let M := C14H4TM.prependMachine L U
    have hM : M.IsHalting ↔ (c.eval 0).Dom := hU c
    have hNeM : NeZero (L.length + 1 + N_U) :=
      ⟨by have := Nat.pos_of_ne_zero (NeZero.ne N_U); omega⟩
    constructor
    · intro hprov hdom
      exact C14H4Sound.not_provable_not_halts_of_isHalting M (hM.mpr hdom) hprov
    · intro hndom
      by_contra hnp
      exact hnot ⟨L.length + 1 + N_U, hNeM, M, fun h => hndom (hM.mp h), hnp⟩
  exact ComputablePred.halting_problem_not_re 0 hreNotDom
