import OMAReductions.R_Constant14_c14_le_432_R1_H1_R1
import Mathlib.Tactic

/-!
# Two-Way Absoluteness of `Constant14.halts M` (`V ⊨ halts M ↔ L ⊨ halts M`)

We prove that for any normal model `(V, mem) ⊨ 𝗭𝗙` (possibly nonstandard!) and any transitive
subclass `P : V → Prop` whose restriction `L = ({x // P x}, mem|_P)` satisfies `𝗭𝗙`, for every
two-symbol Turing machine `M` with `n` states (`[NeZero n]`):

  `V ⊨ Constant14.halts M ↔ L ⊨ Constant14.halts M`.

Proof outline (pure `𝗭𝗙` — zero `Axiom.choice`, zero `Axiom.replacement`, zero Shoenfield):
1. `ZFModel` semantic toolkit evaluating all set-theoretic definitions in `Constant14.halts M`
   on arbitrary (possibly nonstandard) models (adapted from `proofs/Constant14.c14_ge_4.R1.H1.lean`,
   credit `@KevinBigham`).
2. Transitive absoluteness of finite constructors, `ω^L = ω^V` (via `D = ω^L \ ω^V` + `Foundation`
   in `V` + `vnOmegaV_zero_or_succ` in `L`), `ℤ^L = ℤ^V`, `emptyTape^L = emptyTape^V`,
   `initCfg^L = initCfg^V`, and `stepCfg^V(ι z) = ι(stepCfg^L(z))`.
3. **Downward direction (`O^V ⊆ ι(O^L)`):** `ι(O^L)` contains `initCfg^V` and is closed under
   `nextStep^V`, hence contains `O^V`.
4. **Upward direction (`ι(O^L) ⊆ O^V`):** Inside `L`, separate the least closed step relation
   `F ⊆ ω^L × cfgSet^L(n + 1)` containing `⟨0, initCfg^L⟩` and closed under
   `⟨k, y⟩ ↦ ⟨k⁺, nextStep^L(y)⟩`. Then `O^L ⊆ range(F)` and (by a single inversion separation
   `R_1 ⊆ F`) every `p ∈ F` is either `⟨0, initCfg^L⟩` or `⟨m⁺, nextStep^L(y)⟩` for some
   `⟨m, y⟩ ∈ F`. Given any closed `A ∈ V`, separating `I_V = {k ∈ ω^V | ∀ z ∈ C^V, ⟨k, z⟩ ∈ ι(F) → z ∈ A}`
   yields an inductive subset of `ω^V` (using `ω^L = ω^V` + `succV_inj`), so `ω^V ⊆ I_V` and
   hence `ι(O^L) ⊆ A`. Thus `ι(O^L) = O^V` and `V ⊨ halts M ↔ L ⊨ halts M`.

Credit: @Narden91, @KevinBigham
-/

namespace C14HaltsIffAbs

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open scoped Classical

/- ## 1. Direct Tarski semantics on arbitrary `(V, req, rmem)` -/

def tvRaw {V : Type} {ξ : Type*} {n : ℕ} (e : Fin n → V) (ε : ξ → V) :
    Semiterm ℒₛₑₜ ξ n → V
  | Semiterm.bvar i => e i
  | Semiterm.fvar x => ε x
  | Semiterm.func f _ => (f : Empty).elim

def evalRaw {V : Type} (req rmem : V → V → Prop) {ξ : Type*} :
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

abbrev evalM {V : Type} (mem : V → V → Prop) {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n) : Prop :=
  evalRaw (V := V) Eq mem e ε φ

lemma evalRaw_neg {V : Type} (req rmem : V → V → Prop) {ξ : Type*} :
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

lemma tvRaw_rew {V : Type} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    tvRaw e ε (ω t) = tvRaw (fun i => tvRaw e ε (ω #i)) (fun x => tvRaw e ε (ω &x)) t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

lemma tvRaw_bShift {V : Type} {ξ : Type*} {n : ℕ} (d : V) (e : Fin n → V) (ε : ξ → V)
    (t : Semiterm ℒₛₑₜ ξ n) :
    tvRaw (d :> e) ε (Rew.bShift t) = tvRaw e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f _ => exact (f : Empty).elim

lemma evalRaw_congr {V : Type} (req rmem : V → V → Prop) {ξ : Type*} :
    ∀ {n : ℕ} {e₁ e₂ : Fin n → V} {ε₁ ε₂ : ξ → V} (φ : Semiformula ℒₛₑₜ ξ n),
      e₁ = e₂ → ε₁ = ε₂ → (evalRaw req rmem e₁ ε₁ φ ↔ evalRaw req rmem e₂ ε₂ φ) := by
  intro n e₁ e₂ ε₁ ε₂ φ he hε
  subst he hε; rfl

lemma evalRaw_rew {V : Type} (req rmem : V → V → Prop) {ξ₁ ξ₂ : Type*} :
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

/- ## Section 1: `evalM` Connective Rules and `univCl` Elimination -/

lemma evalM_top {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    evalM mem e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True := Iff.rfl

lemma evalM_bot {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    evalM mem e ε (⊥ : Semiformula ℒₛₑₜ ξ n) ↔ False := Iff.rfl

lemma evalM_eq {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    evalM mem e ε (op(=).operator ![t₁, t₂]) ↔ tvRaw e ε t₁ = tvRaw e ε t₂ := Iff.rfl

lemma evalM_mem {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t₁ t₂ : Semiterm ℒₛₑₜ ξ n) :
    evalM mem e ε (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔
      mem (tvRaw e ε t₁) (tvRaw e ε t₂) := Iff.rfl

lemma evalM_not {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (∼φ) ↔ ¬ evalM mem e ε φ :=
  evalRaw_neg Eq mem e ε φ

lemma evalM_and {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ ⋏ ψ) ↔ evalM mem e ε φ ∧ evalM mem e ε ψ := Iff.rfl

lemma evalM_or {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ ⋎ ψ) ↔ evalM mem e ε φ ∨ evalM mem e ε ψ := Iff.rfl

lemma evalM_imp {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ 🡒 ψ) ↔ (evalM mem e ε φ → evalM mem e ε ψ) := by
  change evalM mem e ε (∼φ) ∨ evalM mem e ε ψ ↔ _
  rw [evalM_not, imp_iff_not_or]

lemma evalM_iff {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    evalM mem e ε (φ 🡘 ψ) ↔ (evalM mem e ε φ ↔ evalM mem e ε ψ) := by
  change evalM mem e ε (φ 🡒 ψ) ∧ evalM mem e ε (ψ 🡒 φ) ↔ _
  rw [evalM_imp, evalM_imp]
  exact iff_iff_implies_and_implies.symm

lemma evalM_all {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∀¹ φ) ↔ ∀ d : V, evalM mem (d :> e) ε φ := Iff.rfl

lemma evalM_exs {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (∃¹ φ) ↔ ∃ d : V, evalM mem (d :> e) ε φ := Iff.rfl

lemma evalM_ballMem {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (Semiformula.ballMem t φ) ↔
      ∀ d : V, mem d (tvRaw e ε t) → evalM mem (d :> e) ε φ := by
  change (∀ d : V, evalM mem (d :> e) ε
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] 🡒 φ)) ↔ _
  refine forall_congr' fun d => ?_
  rw [evalM_imp, evalM_mem]
  change (mem d (tvRaw (d :> e) ε (Rew.bShift t)) → _) ↔ _
  rw [tvRaw_bShift]

lemma evalM_bexsMem {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    evalM mem e ε (Semiformula.bexsMem t φ) ↔
      ∃ d : V, mem d (tvRaw e ε t) ∧ evalM mem (d :> e) ε φ := by
  change (∃ d : V, evalM mem (d :> e) ε
    (Semiformula.Operator.Mem.mem.operator ![#0, Rew.bShift t] ⋏ φ)) ↔ _
  refine exists_congr fun d => ?_
  rw [evalM_and, evalM_mem]
  change (mem d (tvRaw (d :> e) ε (Rew.bShift t)) ∧ _) ↔ _
  rw [tvRaw_bShift]

lemma evalM_subst {V : Type} {mem : V → V → Prop} {ξ : Type*} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ → V) (v : Fin n₁ → Semiterm ℒₛₑₜ ξ n₂)
    (φ : Semiformula ℒₛₑₜ ξ n₁) :
    evalM mem e ε (φ ⇜ v) ↔ evalM mem (fun i => tvRaw e ε (v i)) ε φ := by
  exact evalRaw_rew Eq mem e ε (Rew.subst v) φ

lemma evalM_emb {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semisentence ℒₛₑₜ n) :
    evalM mem e ε (Rewriting.emb φ) ↔ evalM mem e Empty.elim φ := by
  refine (evalRaw_rew Eq mem e ε Rew.emb φ).trans ?_
  exact evalRaw_congr Eq mem φ rfl (funext fun x => x.elim)

lemma evalM_existsUnique {V : Type} {mem : V → V → Prop} {ξ : Type*} {n : ℕ}
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

lemma tvRaw_toEmpty {V : Type} {n : ℕ} (e : Fin n → V) (ε : ℕ → V) (ε0 : Empty → V)
    (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    tvRaw e ε0 (t.toEmpty h) = tvRaw e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => exact absurd h (by simp [Semiterm.freeVariables])
  | func f _ => exact (f : Empty).elim

lemma evalM_toEmpty {V : Type} {mem : V → V → Prop} :
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

lemma evalM_allClosure_elim {V : Type} {mem : V → V → Prop} :
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

lemma evalM_univCl_elim {V : Type} {mem : V → V → Prop} (ψ : Proposition ℒₛₑₜ)
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

structure ZFModel where
  V : Type
  mem : V → V → Prop
  sat : ∀ ψ ∈ 𝗭𝗙, evalM mem Fin.elim0 Empty.elim ψ

section WithModel

variable (M0 : ZFModel)

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
    M0.sat Axiom.extentionality (ZermeloFraenkel.axiom_of_extentionality)
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
    M0.sat Axiom.empty (ZermeloFraenkel.axiom_of_empty_set)
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
    M0.sat Axiom.pairing (ZermeloFraenkel.axiom_of_pairing)
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
    M0.sat Axiom.union (ZermeloFraenkel.axiom_of_union)
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
    M0.sat Axiom.power (ZermeloFraenkel.axiom_of_power_set)
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
    M0.sat Axiom.foundation (ZermeloFraenkel.axiom_of_foundation)
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
  have hax := M0.sat (Axiom.separationSchema φ) (ZermeloFraenkel.axiom_of_separation φ)
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
    M0.sat Axiom.infinity (ZermeloFraenkel.axiom_of_infinity)
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



/- ## Section 5: General (Possibly Nonstandard) `intSuccV`, `intPredV`, `stepCfgV`, and `orbitV` -/

lemma vnOmegaV_succ {y : M0.V} (hy : M0.mem y (vnOmegaV M0)) :
    M0.mem (insertV M0 y y) (vnOmegaV M0) := by
  rw [mem_vnOmegaV_iff]
  intro I hI
  exact hI.2 y ((mem_vnOmegaV_iff M0).mp hy I hI)

lemma vnOmegaV_zero_or_succ {u : M0.V} (hu : M0.mem u (vnOmegaV M0)) :
    u = emptyV M0 ∨ ∃ w : M0.V, M0.mem w (vnOmegaV M0) ∧ u = insertV M0 w w := by
  let φ : SetTheorySemiproposition 1 :=
    (Rew.subst ![#0] ▹ Rewriting.emb SetTheory.isEmpty) ⋎
      Semiformula.bexsMem (&0) (Rew.subst ![#1, #0] ▹ Rewriting.emb SetTheory.succ.dfn)
  obtain ⟨J, hJ⟩ := sepV M0 (vnOmegaV M0) φ (fun _ => vnOmegaV M0)
  have hφ : ∀ z : M0.V, evalM M0.mem ![z] (fun _ => vnOmegaV M0) φ ↔
      z = emptyV M0 ∨ ∃ w : M0.V, M0.mem w (vnOmegaV M0) ∧ z = insertV M0 w w := by
    intro z
    dsimp only [φ]
    rw [evalM_or]
    refine or_congr ?_ ?_
    · change evalM M0.mem ![z] (fun _ => vnOmegaV M0)
        ((Rewriting.emb SetTheory.isEmpty) ⇜ ![#0]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.isEmpty ?_ rfl).trans (ev_isEmpty M0 z)
      funext i; fin_cases i; rfl
    · rw [evalM_bexsMem]
      refine exists_congr fun w => and_congr Iff.rfl ?_
      change evalM M0.mem (w :> z :> ![]) (fun _ => vnOmegaV M0)
        ((Rewriting.emb SetTheory.succ.dfn) ⇜ ![#1, #0]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.succ.dfn ?_ rfl).trans (ev_succ M0 z w)
      funext i; fin_cases i <;> rfl
  have hJ_ind : M0.mem (emptyV M0) J ∧ ∀ y : M0.V, M0.mem y J → M0.mem (insertV M0 y y) J := by
    refine ⟨(hJ _).mpr ⟨vnNatV_mem_vnOmegaV M0 0, (hφ _).mpr (Or.inl rfl)⟩, fun y hy => ?_⟩
    have hyω : M0.mem y (vnOmegaV M0) := ((hJ y).mp hy).1
    exact (hJ _).mpr ⟨vnOmegaV_succ M0 hyω, (hφ _).mpr (Or.inr ⟨y, hyω, rfl⟩)⟩
  exact (hφ u).mp ((hJ u).mp ((mem_vnOmegaV_iff M0).mp hu J hJ_ind)).2

noncomputable def omegaPredV (r : M0.V) : M0.V :=
  if h : ∃ w : M0.V, M0.mem w (vnOmegaV M0) ∧ r = insertV M0 w w then h.choose else emptyV M0

lemma omegaPredV_spec {r : M0.V} (hr : M0.mem r (vnOmegaV M0)) (hne : r ≠ emptyV M0) :
    M0.mem (omegaPredV M0 r) (vnOmegaV M0) ∧ r = insertV M0 (omegaPredV M0 r) (omegaPredV M0 r) := by
  have hex : ∃ w : M0.V, M0.mem w (vnOmegaV M0) ∧ r = insertV M0 w w :=
    (vnOmegaV_zero_or_succ M0 hr).resolve_left hne
  unfold omegaPredV
  rw [dif_pos hex]
  exact hex.choose_spec

lemma omegaPredV_succ {w : M0.V} (hw : M0.mem w (vnOmegaV M0)) :
    omegaPredV M0 (insertV M0 w w) = w := by
  have hex : ∃ w' : M0.V, M0.mem w' (vnOmegaV M0) ∧ insertV M0 w w = insertV M0 w' w' :=
    ⟨w, hw, rfl⟩
  unfold omegaPredV
  rw [dif_pos hex]
  exact (succV_inj M0 hex.choose_spec.2).symm

lemma insertV_ne_zero (w : M0.V) : insertV M0 w w ≠ vnNatV M0 0 := by
  intro h
  change insertV M0 w w = emptyV M0 at h
  exact not_mem_emptyV M0 w (h ▸ (mem_insertV M0).mpr (Or.inl rfl))

lemma mem_intSetV_decomp {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) :
    ∃ r : M0.V, M0.mem r (vnOmegaV M0) ∧
      (pos = kpairV M0 (vnNatV M0 0) r ∨ pos = kpairV M0 (vnNatV M0 1) r) := by
  obtain ⟨s, hs, r, hr, rfl⟩ := (mem_prodV M0).mp hpos
  obtain ⟨k, hk, rfl⟩ := (mem_vnNatV_iff M0).mp hs
  refine ⟨r, hr, ?_⟩
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable def intSuccV (pos : M0.V) : M0.V :=
  if pi1V M0 pos = vnNatV M0 0 then
    kpairV M0 (vnNatV M0 0) (insertV M0 (pi2V M0 pos) (pi2V M0 pos))
  else if pi2V M0 pos = vnNatV M0 0 then
    encodeIntV M0 0
  else
    kpairV M0 (vnNatV M0 1) (omegaPredV M0 (pi2V M0 pos))

noncomputable def intPredV (pos : M0.V) : M0.V :=
  if pi1V M0 pos = vnNatV M0 1 then
    kpairV M0 (vnNatV M0 1) (insertV M0 (pi2V M0 pos) (pi2V M0 pos))
  else if pi2V M0 pos = vnNatV M0 0 then
    kpairV M0 (vnNatV M0 1) (vnNatV M0 0)
  else
    kpairV M0 (vnNatV M0 0) (omegaPredV M0 (pi2V M0 pos))

lemma intSuccV_mem {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) :
    M0.mem (intSuccV M0 pos) (intSetV M0) := by
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp M0 hpos
  · unfold intSuccV intSetV
    rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl]
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), vnOmegaV_succ M0 hr⟩
  · have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
    unfold intSuccV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h10]
    by_cases hr0 : r = vnNatV M0 0
    · rw [if_pos hr0]; exact encodeIntV_mem M0 0
    · rw [if_neg hr0]
      exact (kpairV_mem_prodV M0).mpr
        ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), (omegaPredV_spec M0 hr hr0).1⟩

lemma intPredV_mem {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) :
    M0.mem (intPredV M0 pos) (intSetV M0) := by
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp M0 hpos
  · have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
    unfold intPredV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h01]
    by_cases hr0 : r = vnNatV M0 0
    · rw [if_pos hr0]
      exact (kpairV_mem_prodV M0).mpr
        ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), vnNatV_mem_vnOmegaV M0 0⟩
    · rw [if_neg hr0]
      exact (kpairV_mem_prodV M0).mpr
        ⟨vnNatV_lt_mem M0 (by decide : 0 < 2), (omegaPredV_spec M0 hr hr0).1⟩
  · unfold intPredV intSetV
    rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl]
    exact (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 (by decide : 1 < 2), vnOmegaV_succ M0 hr⟩

lemma intSuccV_intPredV {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) :
    intSuccV M0 (intPredV M0 pos) = pos := by
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := h01.symm
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp M0 hpos
  · unfold intPredV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h01]
    by_cases hr0 : r = vnNatV M0 0
    · rw [if_pos hr0, hr0]
      unfold intSuccV
      rw [pi1V_kpairV, pi2V_kpairV, if_neg h10, if_pos rfl]
      rfl
    · rw [if_neg hr0]
      unfold intSuccV
      rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl, ← (omegaPredV_spec M0 hr hr0).2]
  · unfold intPredV
    rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl]
    unfold intSuccV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h10, if_neg (insertV_ne_zero M0 r), omegaPredV_succ M0 hr]

lemma intPredV_intSuccV {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) :
    intPredV M0 (intSuccV M0 pos) = pos := by
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := h01.symm
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp M0 hpos
  · unfold intSuccV
    rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl]
    unfold intPredV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h01, if_neg (insertV_ne_zero M0 r), omegaPredV_succ M0 hr]
  · unfold intSuccV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h10]
    by_cases hr0 : r = vnNatV M0 0
    · rw [if_pos hr0, hr0]
      unfold intPredV encodeIntV
      rw [pi1V_kpairV, pi2V_kpairV, if_neg h01, if_pos rfl]
    · rw [if_neg hr0]
      unfold intPredV
      rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl, ← (omegaPredV_spec M0 hr hr0).2]

lemma ev_integerSucc_all {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) (w' : M0.V) :
    mEv M0 ![w', pos] Constant14.integerSucc.dfn ↔ w' = intSuccV M0 pos := by
  have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
  have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := h01.symm
  rw [ev_integerSucc_of_mem M0 hpos]
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp M0 hpos
  · unfold intSuccV
    simp only [pi1V_kpairV, pi2V_kpairV, h01, false_and, or_false, true_and, ↓reduceIte]
  · unfold intSuccV
    simp only [pi1V_kpairV, pi2V_kpairV, h10, false_and, false_or, true_and, ↓reduceIte]
    by_cases hr0 : r = vnNatV M0 0
    · rw [if_pos hr0, hr0]
      have hno : ¬ ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
          vnNatV M0 0 = insertV M0 m m ∧ w' = kpairV M0 (vnNatV M0 1) m := by
        rintro ⟨m, _, hm, _⟩
        exact insertV_ne_zero M0 m hm.symm
      simp only [true_and, hno, or_false]
    · rw [if_neg hr0]
      simp only [hr0, false_and, false_or]
      obtain ⟨hpmem, hpeq⟩ := omegaPredV_spec M0 hr hr0
      constructor
      · rintro ⟨m, _, hm, rfl⟩
        have hmeq : m = omegaPredV M0 r := succV_inj M0 (hm.symm.trans hpeq)
        rw [hmeq]
      · rintro rfl
        exact ⟨omegaPredV M0 r, hpmem, hpeq, rfl⟩

lemma ev_integerPred_all {pos : M0.V} (hpos : M0.mem pos (intSetV M0)) (w' : M0.V) :
    mEv M0 ![w', pos] Constant14.integerPred.dfn ↔ w' = intPredV M0 pos := by
  unfold Constant14.integerPred.dfn
  rw [mEv_or, mEv_and, mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 w' pos _) (et_const0 M0 (dc_integers M0) _),
      ev_faf_mem M0 (et_bvar1 M0 w' _) (et_const0 M0 (dc_integers M0) _),
      ev_nest2 M0 Constant14.integerSucc.dfn (et_bvar2 M0 w' pos _) (et_bvar1 M0 w' _),
      ev_faf_notMem M0 (et_bvar2 M0 w' pos _) (et_const0 M0 (dc_integers M0) _)]
  simp only [hpos, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw', hsucc⟩
    rw [ev_integerSucc_all M0 hw' pos] at hsucc
    calc w' = intPredV M0 (intSuccV M0 w') := (intPredV_intSuccV M0 hw').symm
      _ = intPredV M0 pos := by rw [← hsucc]
  · rintro rfl
    refine ⟨intPredV_mem M0 hpos, ?_⟩
    rw [ev_integerSucc_all M0 (intPredV_mem M0 hpos) pos, intSuccV_intPredV M0 hpos]

noncomputable def decodeNatV (N : ℕ) (x : M0.V) : ℕ :=
  if h : ∃ k < N, x = vnNatV M0 k then h.choose else 0

lemma decodeNatV_spec {N : ℕ} {x : M0.V} (hx : M0.mem x (vnNatV M0 N)) :
    decodeNatV M0 N x < N ∧ x = vnNatV M0 (decodeNatV M0 N x) := by
  have hex : ∃ k < N, x = vnNatV M0 k := (mem_vnNatV_iff M0).mp hx
  unfold decodeNatV
  rw [dif_pos hex]
  exact hex.choose_spec

lemma decodeNatV_vnNatV {N k : ℕ} (hk : k < N) : decodeNatV M0 N (vnNatV M0 k) = k := by
  have hex : ∃ j < N, vnNatV M0 k = vnNatV M0 j := ⟨k, hk, rfl⟩
  unfold decodeNatV
  rw [dif_pos hex]
  exact (vnNatV_inj M0 hex.choose_spec.2).symm

noncomputable def stepCfgV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (z : M0.V) : M0.V :=
  let qCode := decodeNatV M0 (n + 1) (pi1V M0 z)
  let pos := pi1V M0 (pi2V M0 z)
  let g := pi2V M0 (pi2V M0 z)
  let symCode := decodeNatV M0 2 (zfcAppV M0 g pos)
  let o := transLookup M qCode symCode
  let pos' := if o.2.2 = 0 then intPredV M0 pos else if o.2.2 = 1 then pos else intSuccV M0 pos
  let g' := updateTapeV M0 g pos (vnNatV M0 o.2.1)
  kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' g')

lemma transLookup_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode symCode : ℕ) (hs : symCode < 2) :
    let o := transLookup M qCode symCode
    o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
  dsimp only [transLookup]
  by_cases hqn : qCode < n
  · rw [dif_pos hqn, dif_pos hs]
    exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
  · rw [dif_neg hqn]
    dsimp only
    exact ⟨Nat.lt_succ_self n, hs, by decide⟩

lemma stepCfgV_mem {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V}
    (hz : M0.mem z (cfgSetV M0 (n + 1))) :
    M0.mem (stepCfgV M0 M z) (cfgSetV M0 (n + 1)) := by
  obtain ⟨q, hq, tail, htail, rfl⟩ := (mem_prodV M0).mp hz
  obtain ⟨pos, hpos, g, hg, rfl⟩ := (mem_prodV M0).mp htail
  have hsym_mem : M0.mem (zfcAppV M0 g pos) (vnNatV M0 2) := zfcAppV_mem_codomain M0 hg hpos
  have hs : decodeNatV M0 2 (zfcAppV M0 g pos) < 2 := (decodeNatV_spec M0 hsym_mem).1
  have hob := transLookup_bounds M (decodeNatV M0 (n + 1) q) (decodeNatV M0 2 (zfcAppV M0 g pos)) hs
  unfold stepCfgV cfgSetV
  rw [pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV]
  refine (kpairV_mem_prodV M0).mpr ⟨vnNatV_lt_mem M0 hob.1, (kpairV_mem_prodV M0).mpr ⟨?_, ?_⟩⟩
  · split_ifs
    · exact intPredV_mem M0 hpos
    · exact hpos
    · exact intSuccV_mem M0 hpos
  · exact updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 hob.2.1)

lemma ev_nextConfig_all {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V}
    (hz : M0.mem z (cfgSetV M0 (n + 1))) (z' : M0.V) :
    mEv M0 ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z' = stepCfgV M0 M z := by
  obtain ⟨q, hq, tail, htail, hz_eq⟩ := (mem_prodV M0).mp hz
  obtain ⟨pos, hpos, g, hg, htail_eq⟩ := (mem_prodV M0).mp htail
  have hzeq : z = kpairV M0 q (kpairV M0 pos g) := by rw [hz_eq, htail_eq]
  have hq_spec := decodeNatV_spec M0 hq
  let qCode := decodeNatV M0 (n + 1) q
  have hsym_mem : M0.mem (zfcAppV M0 g pos) (vnNatV M0 2) := zfcAppV_mem_codomain M0 hg hpos
  have hs_spec := decodeNatV_spec M0 hsym_mem
  let symCode := decodeNatV M0 2 (zfcAppV M0 g pos)
  let o := transLookup M qCode symCode
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := transLookup_bounds M qCode symCode hs_spec.1
  let tVal := kpairV M0 (vnNatV M0 o.1) (kpairV M0 (vnNatV M0 o.2.1) (vnNatV M0 o.2.2))
  have htVal_eq : zfcAppV M0 (instrTableV M0 M)
      (kpairV M0 (pi1V M0 z) (zfcAppV M0 (pi2V M0 (pi2V M0 z)) (pi1V M0 (pi2V M0 z)))) = tVal := by
    rw [hzeq, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, hq_spec.2, hs_spec.2]
    exact instrTableV_app M0 M qCode symCode hq_spec.1 hs_spec.1
  let pos' := if o.2.2 = 0 then intPredV M0 pos else if o.2.2 = 1 then pos else intSuccV M0 pos
  let g' := updateTapeV M0 g pos (vnNatV M0 o.2.1)
  have hstep_eq : stepCfgV M0 M z = kpairV M0 (vnNatV M0 o.1) (kpairV M0 pos' g') := by
    unfold stepCfgV
    rw [hzeq, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV]
  have hg'_mem : M0.mem g' (funsV M0 (intSetV M0) (vnNatV M0 2)) :=
    updateTapeV_mem_funs M0 hg hpos (vnNatV_lt_mem M0 hob.2.1)
  have hstep_mem : M0.mem (stepCfgV M0 M z) (cfgSetV M0 (n + 1)) := stepCfgV_mem M0 M hz
  unfold Constant14.nextConfig
  rw [mEv_and, mEv_and]
  rw [ev_faf_mem M0 (et_bvar2 M0 z' z _) (et_const0 M0 (dc_configSet M0 (n + 1)) _),
      ev_faf_mem M0 (et_bvar1 M0 z' _) (et_const0 M0 (dc_configSet M0 (n + 1)) _)]
  simp only [hz, true_and]
  rw [mEv_exs]
  refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
      (t = tVal ∧
       pi1V M0 z' = pi1V M0 t ∧
       ((pi2V M0 (pi2V M0 t) = vnNatV M0 0 ∧
           mEv M0 ![pi1V M0 (pi2V M0 z'), pi1V M0 (pi2V M0 z)] Constant14.integerPred.dfn) ∨
         (pi2V M0 (pi2V M0 t) = vnNatV M0 1 ∧ pi1V M0 (pi2V M0 z') = pi1V M0 (pi2V M0 z)) ∨
         (pi2V M0 (pi2V M0 t) = vnNatV M0 2 ∧
           mEv M0 ![pi1V M0 (pi2V M0 z'), pi1V M0 (pi2V M0 z)] Constant14.integerSucc.dfn)) ∧
       zfcAppV M0 (pi2V M0 (pi2V M0 z')) (pi1V M0 (pi2V M0 z)) = pi1V M0 (pi2V M0 t) ∧
       ∀ u : M0.V, M0.mem u (intSetV M0) → u ≠ pi1V M0 (pi2V M0 z) →
         zfcAppV M0 (pi2V M0 (pi2V M0 z')) u = zfcAppV M0 (pi2V M0 (pi2V M0 z)) u)))).trans ?_
  · rw [mEv_and, mEv_and, mEv_and, mEv_and]
    refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
    · rw [ev_faf_eq M0 (et_bvar1 M0 t _)
        (et_comp2 M0 (ev_value M0) (et_const0 M0 (dc_instructionTable M0 M) _)
          (et_comp2 M0 (ev_kpair M0)
            (et_comp1 M0 (ev_pi1 M0) (et_bvar4 M0 _ t z' z _))
            (et_comp2 M0 (ev_value M0)
              (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z _)))))),
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
            (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z _)))))
        (or_congr
          (and_congr
            (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
              (et_const0 M0 (dc_numeral M0 1) _))
            (ev_faf_eq M0
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 _ t z' z _)))))
          (and_congr
            (ev_faf_eq M0 (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar1 M0 t _)))
              (et_const0 M0 (dc_numeral M0 2) _))
            (ev_nest2 M0 Constant14.integerSucc.dfn
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
              (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z _))))))
    · exact ev_faf_eq M0
        (et_comp2 M0 (ev_value M0)
          (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 t z' _)))
          (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar3 M0 t z' z _))))
        (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar2 M0 _ t _)))
    · rw [ev_faf_ball M0 (et_const0 M0 (dc_integers M0) _)]
      refine forall₂_congr fun u _ => ?_
      rw [mEv_imp]
      exact imp_congr
        (ev_faf_ne M0 (et_bvar1 M0 u _)
          (et_comp1 M0 (ev_pi1 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar6 M0 _ u (intSetV M0) t z' z _))))
        (ev_faf_eq M0
          (et_comp2 M0 (ev_value M0)
            (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar4 M0 u (intSetV M0) t z' _)))
            (et_bvar1 M0 u _))
          (et_comp2 M0 (ev_value M0)
            (et_comp1 M0 (ev_pi2 M0) (et_comp1 M0 (ev_pi2 M0) (et_bvar6 M0 _ u (intSetV M0) t z' z _)))
            (et_bvar2 M0 _ u _)))
  · constructor
    · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
      obtain ⟨s2, _, p_tail, hp_tail, rfl⟩ := (mem_prodV M0).mp hz'
      obtain ⟨p2, _, g2, hg2, rfl⟩ := (mem_prodV M0).mp hp_tail
      rw [hzeq] at hdir hwr hrest
      dsimp only [tVal] at hq_eq hdir hwr
      rw [pi1V_kpairV, pi1V_kpairV] at hq_eq
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hdir
      rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV] at hwr
      simp only [pi2V_kpairV, pi1V_kpairV] at hrest
      rw [hstep_eq, hq_eq]
      congr 1; congr 1
      · have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · have h01 : vnNatV M0 0 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h02 : vnNatV M0 0 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h01, h02, false_and, or_false] at hdir
          rw [ev_integerPred_all M0 hpos] at hdir
          simpa [pos', hdv] using hdir
        · have h10 : vnNatV M0 1 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h12 : vnNatV M0 1 ≠ vnNatV M0 2 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
          simpa [pos', hdv] using hdir
        · have h20 : vnNatV M0 2 ≠ vnNatV M0 0 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          have h21 : vnNatV M0 2 ≠ vnNatV M0 1 := fun h => absurd (vnNatV_inj M0 h) (by decide)
          simp only [true_and, h20, h21, false_and, false_or] at hdir
          rw [ev_integerSucc_all M0 hpos] at hdir
          simpa [pos', hdv] using hdir
      · refine funsV_ext M0 hg2 hg'_mem fun u hu => ?_
        rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 hob.2.1) hu]
        by_cases hup : u = pos
        · subst hup; rw [if_pos rfl, hwr]
        · rw [if_neg hup, hrest u hu hup]
    · rintro rfl
      refine ⟨hstep_mem, tVal, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hstep_eq]; dsimp only [tVal]; rw [pi1V_kpairV, pi1V_kpairV]
      · rw [hstep_eq, hzeq]; dsimp only [tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        have hd2 := hob.2.2
        interval_cases hdv : o.2.2
        · left; refine ⟨rfl, ?_⟩
          rw [ev_integerPred_all M0 hpos]; simp [pos', hdv]
        · right; left; refine ⟨rfl, ?_⟩
          simp [pos', hdv]
        · right; right; refine ⟨rfl, ?_⟩
          rw [ev_integerSucc_all M0 hpos]; simp [pos', hdv]
      · rw [hstep_eq, hzeq]; dsimp only [tVal]
        rw [pi2V_kpairV, pi2V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV, pi1V_kpairV]
        rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 hob.2.1) hpos, if_pos rfl]
      · intro u hu hne
        rw [hzeq, pi2V_kpairV, pi1V_kpairV] at hne
        rw [hstep_eq, hzeq]
        simp only [pi2V_kpairV]
        rw [updateTapeV_app M0 hg hpos (vnNatV_lt_mem M0 hob.2.1) hu, if_neg hne]

lemma zfcAppV_nextStepV_all {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V}
    (hz : M0.mem z (cfgSetV M0 (n + 1))) :
    zfcAppV M0 (nextStepV M0 M) z = stepCfgV M0 M z := by
  apply zfcAppV_of_unique M0
  intro y
  rw [mem_nextStepV]
  constructor
  · rintro ⟨z0, _, z', _, heq, hnc⟩
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact (ev_nextConfig_all M0 M hz y).mp hnc
  · rintro rfl
    exact ⟨z, hz, stepCfgV M0 M z, stepCfgV_mem M0 M hz, rfl,
      (ev_nextConfig_all M0 M hz (stepCfgV M0 M z)).mpr rfl⟩

lemma nextStepV_mem_funs {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    M0.mem (nextStepV M0 M) (funsV M0 (cfgSetV M0 (n + 1)) (cfgSetV M0 (n + 1))) := by
  rw [mem_funsV]
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨z, hz, z', hz', rfl, _⟩ := (mem_nextStepV M0 M).mp hp
    exact (kpairV_mem_prodV M0).mpr ⟨hz, hz'⟩
  · intro z hz
    refine ⟨stepCfgV M0 M z,
      (mem_nextStepV M0 M).mpr ⟨z, hz, stepCfgV M0 M z, stepCfgV_mem M0 M hz, rfl,
        (ev_nextConfig_all M0 M hz _).mpr rfl⟩,
      fun y hy => ?_⟩
    obtain ⟨z0, _, z', _, heq, hnc⟩ := (mem_nextStepV M0 M).mp hy
    obtain ⟨rfl, rfl⟩ := kpairV_inj M0 heq
    exact (ev_nextConfig_all M0 M hz y).mp hnc

noncomputable def initCfgV : M0.V :=
  kpairV M0 (vnNatV M0 0) (kpairV M0 (encodeIntV M0 0) (emptyTapeV M0))

lemma initCfgV_mem {n : ℕ} [NeZero n] : M0.mem (initCfgV M0) (cfgSetV M0 (n + 1)) := by
  unfold initCfgV cfgSetV
  exact (kpairV_mem_prodV M0).mpr
    ⟨vnNatV_lt_mem M0 (Nat.zero_lt_succ n),
      (kpairV_mem_prodV M0).mpr ⟨encodeIntV_mem M0 0, emptyTapeV_mem_funs M0⟩⟩

lemma dc_initialConfigV : DefinesConst M0 Constant14.initialConfig (initCfgV M0) := by
  intro z
  unfold Constant14.initialConfig initCfgV
  exact ev_faf_eq M0 (et_bvar1 M0 z _)
    (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 0) _)
      (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_integerZero M0) _)
        (et_const0 M0 (dc_emptyTape M0) _)))

lemma ev_IsFunction (f : M0.V) :
    mEv M0 ![f] SetTheory.IsFunction.dfn ↔ ∃ X Y : M0.V, M0.mem f (funsV M0 X Y) := by
  unfold SetTheory.IsFunction.dfn
  rw [mEv_exs]
  refine exists_congr fun X => ?_
  rw [mEv_exs]
  refine exists_congr fun Y => ?_
  exact ev_faf_mem M0 (et_bvar3 M0 Y X f _)
    (et_comp2 M0 (ev_function M0) (et_bvar2 M0 _ Y _) (et_bvar3 M0 _ Y X _))

lemma exists_orbitV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ O : M0.V, ∀ z : M0.V, M0.mem z O ↔
      M0.mem z (cfgSetV M0 (n + 1)) ∧
      ∀ A : M0.V,
        (M0.mem (initCfgV M0) A ∧
          ∀ y : M0.V, M0.mem y A → M0.mem (zfcAppV M0 (nextStepV M0 M) y) A) →
        M0.mem z A := by
  let φ : SetTheorySemiproposition 1 :=
    ∀¹ ((Semiformula.rel Language.Set.Rel.mem ![&1, #0] ⋏
      Semiformula.ballMem (#0)
        (∀¹ ((Rew.subst ![#0, &0, #1] ▹ Rewriting.emb SetTheory.value.dfn) 🡒
          Semiformula.rel Language.Set.Rel.mem ![#0, #2]))) 🡒
      Semiformula.rel Language.Set.Rel.mem ![#1, #0])
  let ε : ℕ → M0.V := fun k => if k = 0 then nextStepV M0 M else initCfgV M0
  obtain ⟨O, hO⟩ := sepV M0 (cfgSetV M0 (n + 1)) φ ε
  refine ⟨O, fun z => ?_⟩
  rw [hO z]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_all]
  refine forall_congr' fun A => ?_
  rw [evalM_imp, evalM_and]
  refine imp_congr (and_congr Iff.rfl ?_) Iff.rfl
  rw [evalM_ballMem]
  refine forall₂_congr fun y _ => ?_
  rw [evalM_all]
  refine (?_ : _ ↔ ∀ v : M0.V, v = zfcAppV M0 (nextStepV M0 M) y → M0.mem v A).trans
    ⟨fun h => h _ rfl, fun h v hv => hv ▸ h⟩
  refine forall_congr' fun v => ?_
  rw [evalM_imp]
  refine imp_congr ?_ Iff.rfl
  change evalM M0.mem (v :> y :> A :> z :> ![]) ε
    ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, &0, #1]) ↔ _
  rw [evalM_subst, evalM_emb]
  refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).trans
    (ev_value M0 v (nextStepV M0 M) y)
  funext i; fin_cases i <;> rfl

noncomputable def orbitV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : M0.V :=
  (exists_orbitV M0 M).choose

lemma mem_orbitV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V} :
    M0.mem z (orbitV M0 M) ↔
      M0.mem z (cfgSetV M0 (n + 1)) ∧
      ∀ A : M0.V,
        (M0.mem (initCfgV M0) A ∧
          ∀ y : M0.V, M0.mem y A → M0.mem (zfcAppV M0 (nextStepV M0 M) y) A) →
        M0.mem z A :=
  (exists_orbitV M0 M).choose_spec z

lemma mem_orbitV_iff {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V} :
    M0.mem z (orbitV M0 M) ↔
      ∀ A : M0.V,
        (M0.mem (initCfgV M0) A ∧
          ∀ y : M0.V, M0.mem y A → M0.mem (zfcAppV M0 (nextStepV M0 M) y) A) →
        M0.mem z A := by
  rw [mem_orbitV]
  refine ⟨And.right, fun hall => ⟨hall (cfgSetV M0 (n + 1)) ⟨initCfgV_mem M0, fun y hy => ?_⟩, hall⟩⟩
  rw [zfcAppV_nextStepV_all M0 M hy]
  exact stepCfgV_mem M0 M hy

lemma orbitV_subset_cfgSet {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V}
    (hz : M0.mem z (orbitV M0 M)) : M0.mem z (cfgSetV M0 (n + 1)) :=
  ((mem_orbitV M0 M).mp hz).1

lemma initCfgV_mem_orbitV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    M0.mem (initCfgV M0) (orbitV M0 M) :=
  (mem_orbitV_iff M0 M).mpr fun _ hA => hA.1

lemma nextStepV_mem_orbitV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {y : M0.V}
    (hy : M0.mem y (orbitV M0 M)) : M0.mem (zfcAppV M0 (nextStepV M0 M) y) (orbitV M0 M) :=
  (mem_orbitV_iff M0 M).mpr fun A hA => hA.2 y ((mem_orbitV_iff M0 M).mp hy A hA)

lemma ev_orbit_nextStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (O : M0.V) :
    mEv M0 ![O, nextStepV M0 M, initCfgV M0] Constant14.orbit ↔ O = orbitV M0 M := by
  unfold Constant14.orbit
  rw [mEv_and]
  have hfun : mEv M0 ![O, nextStepV M0 M, initCfgV M0]
      (Semiformula.nestFormulae SetTheory.IsFunction.dfn ![op(=).operator (#0 :> #2 :> ![])]) := by
    rw [ev_nest1 M0 SetTheory.IsFunction.dfn (et_bvar2 M0 O (nextStepV M0 M) _), ev_IsFunction]
    exact ⟨cfgSetV M0 (n + 1), cfgSetV M0 (n + 1), nextStepV_mem_funs M0 M⟩
  simp only [hfun, true_and]
  rw [mEv_all]
  refine (?_ : _ ↔ ∀ z : M0.V, M0.mem z O ↔ M0.mem z (orbitV M0 M)).trans
    ⟨fun h => extV M0 h, fun h z => by rw [h]⟩
  refine forall_congr' fun z => ?_
  rw [mEv_iff, mem_orbitV_iff]
  refine iff_congr (ev_faf_mem M0 (et_bvar1 M0 z _) (et_bvar3 M0 _ z O _)) ?_
  rw [mEv_all]
  refine forall_congr' fun A => ?_
  rw [mEv_imp, mEv_and]
  refine imp_congr (and_congr ?_ ?_) (ev_faf_mem M0 (et_bvar2 M0 A z _) (et_bvar2 M0 _ A _))
  · exact ev_faf_mem M0 (et_bvar5 M0 A z O (nextStepV M0 M) (initCfgV M0) _) (et_bvar2 M0 _ A _)
  · rw [ev_faf_ball M0 (et_bvar1 M0 A _)]
    refine forall₂_congr fun y _ => ?_
    exact ev_faf_mem M0
      (et_comp2 M0 (ev_value M0) (et_bvar6 M0 y A A z O (nextStepV M0 M) _) (et_bvar1 M0 y _))
      (et_bvar4 M0 _ y A A _)

lemma ev_halts_iff {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    evalM M0.mem Fin.elim0 Empty.elim (Constant14.halts M) ↔
      ∃ m : M0.V, M0.mem m (intSetV M0) ∧
      ∃ g : M0.V, M0.mem g (funsV M0 (intSetV M0) (vnNatV M0 2)) ∧
        M0.mem (kpairV M0 (vnNatV M0 n) (kpairV M0 m g)) (orbitV M0 M) := by
  change mEv M0 (Fin.elim0 : Fin 0 → M0.V) (Constant14.halts M) ↔ _
  rw [mEv_e0 M0 (Fin.elim0 : Fin 0 → M0.V) ![]]
  unfold Constant14.halts
  rw [ev_faf_bexs M0 (et_const0 M0 (dc_integers M0) ![])]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  rw [ev_faf_bexs M0
    (et_comp2 M0 (ev_function M0) (et_const0 M0 (dc_numeral M0 2) _) (et_const0 M0 (dc_integers M0) _))]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  exact ev_faf_mem M0
    (et_comp2 M0 (ev_kpair M0) (et_const0 M0 (dc_numeral M0 n) _)
      (et_comp2 M0 (ev_kpair M0) (et_bvar3 M0 g _ m _) (et_bvar1 M0 g _)))
    (fun O => (ev_nestFunc2_raw M0 Constant14.orbit
      (et_const0 M0 (dc_nextStep M0 M) _) (et_const0 M0 (dc_initialConfigV M0) _) O).trans
      (ev_orbit_nextStep M0 M O))


/- ### Least closed step relation `stepRelV ⊆ ω × cfgSet (n + 1)` (Dedekind recursion, pure Separation) -/

lemma exists_stepRelV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ F : M0.V, ∀ p : M0.V, M0.mem p F ↔
      M0.mem p (prodV M0 (vnOmegaV M0) (cfgSetV M0 (n + 1))) ∧
      ∀ R : M0.V,
        (M0.mem (kpairV M0 (vnNatV M0 0) (initCfgV M0)) R ∧
          ∀ k : M0.V, M0.mem k (vnOmegaV M0) →
            ∀ y : M0.V, M0.mem y (cfgSetV M0 (n + 1)) →
              M0.mem (kpairV M0 k y) R →
                M0.mem (kpairV M0 (insertV M0 k k) (zfcAppV M0 (nextStepV M0 M) y)) R) →
        M0.mem p R := by
  let p0 := kpairV M0 (vnNatV M0 0) (initCfgV M0)
  let φ : SetTheorySemiproposition 1 :=
    ∀¹ ((Semiformula.rel Language.Set.Rel.mem ![&3, #0] ⋏
      Semiformula.ballMem (&0)
        (Semiformula.ballMem (&1)
          (∀¹ ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) 🡒
            Semiformula.rel Language.Set.Rel.mem ![#0, #3] 🡒
            ∀¹ ((Rew.subst ![#0, #3] ▹ Rewriting.emb SetTheory.succ.dfn) 🡒
              ∀¹ ((Rew.subst ![#0, &2, #3] ▹ Rewriting.emb SetTheory.value.dfn) 🡒
                ∀¹ ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) 🡒
                  Semiformula.rel Language.Set.Rel.mem ![#0, #6]))))))) 🡒
      Semiformula.rel Language.Set.Rel.mem ![#1, #0])
  let ε : ℕ → M0.V := fun i =>
    if i = 0 then vnOmegaV M0
    else if i = 1 then cfgSetV M0 (n + 1)
    else if i = 2 then nextStepV M0 M
    else p0
  obtain ⟨F, hF⟩ := sepV M0 (prodV M0 (vnOmegaV M0) (cfgSetV M0 (n + 1))) φ ε
  refine ⟨F, fun p => ?_⟩
  rw [hF p]
  refine and_congr Iff.rfl ?_
  dsimp only [φ]
  rw [evalM_all]
  refine forall_congr' fun R => ?_
  rw [evalM_imp, evalM_and]
  refine imp_congr (and_congr Iff.rfl ?_) Iff.rfl
  rw [evalM_ballMem]
  refine forall₂_congr fun k _ => ?_
  rw [evalM_ballMem]
  refine forall₂_congr fun y _ => ?_
  rw [evalM_all]
  refine (?_ : _ ↔ ∀ q : M0.V, q = kpairV M0 k y → M0.mem q R →
      M0.mem (kpairV M0 (insertV M0 k k) (zfcAppV M0 (nextStepV M0 M) y)) R).trans
    ⟨fun h hmem => h _ rfl hmem, fun h q hq hmem => h (hq ▸ hmem)⟩
  refine forall_congr' fun q => ?_
  rw [evalM_imp, evalM_imp]
  refine imp_congr ?_ (imp_congr Iff.rfl ?_)
  · change evalM M0.mem (q :> y :> k :> R :> p :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 q k y)
    funext i; fin_cases i <;> rfl
  · rw [evalM_all]
    refine (?_ : _ ↔ ∀ k' : M0.V, k' = insertV M0 k k →
        M0.mem (kpairV M0 k' (zfcAppV M0 (nextStepV M0 M) y)) R).trans
      ⟨fun h => h _ rfl, fun h k' hk' => hk' ▸ h⟩
    refine forall_congr' fun k' => ?_
    rw [evalM_imp]
    refine imp_congr ?_ ?_
    · change evalM M0.mem (k' :> q :> y :> k :> R :> p :> ![]) ε
        ((Rewriting.emb SetTheory.succ.dfn) ⇜ ![#0, #3]) ↔ _
      rw [evalM_subst, evalM_emb]
      refine (evalRaw_congr Eq M0.mem SetTheory.succ.dfn ?_ rfl).trans (ev_succ M0 k' k)
      funext i; fin_cases i <;> rfl
    · rw [evalM_all]
      refine (?_ : _ ↔ ∀ y' : M0.V, y' = zfcAppV M0 (nextStepV M0 M) y →
          M0.mem (kpairV M0 k' y') R).trans
        ⟨fun h => h _ rfl, fun h y' hy' => hy' ▸ h⟩
      refine forall_congr' fun y' => ?_
      rw [evalM_imp]
      refine imp_congr ?_ ?_
      · change evalM M0.mem (y' :> k' :> q :> y :> k :> R :> p :> ![]) ε
          ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, &2, #3]) ↔ _
        rw [evalM_subst, evalM_emb]
        refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).trans
          (ev_value M0 y' (nextStepV M0 M) y)
        funext i; fin_cases i <;> rfl
      · rw [evalM_all]
        refine (?_ : _ ↔ ∀ q' : M0.V, q' = kpairV M0 k' y' → M0.mem q' R).trans
          ⟨fun h => h _ rfl, fun h q' hq' => hq' ▸ h⟩
        refine forall_congr' fun q' => ?_
        rw [evalM_imp]
        refine imp_congr ?_ Iff.rfl
        change evalM M0.mem (q' :> y' :> k' :> q :> y :> k :> R :> p :> ![]) ε
          ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) ↔ _
        rw [evalM_subst, evalM_emb]
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair M0 q' k' y')
        funext i; fin_cases i <;> rfl

noncomputable def stepRelV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : M0.V :=
  (exists_stepRelV M0 M).choose

lemma mem_stepRelV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {p : M0.V} :
    M0.mem p (stepRelV M0 M) ↔
      M0.mem p (prodV M0 (vnOmegaV M0) (cfgSetV M0 (n + 1))) ∧
      ∀ R : M0.V,
        (M0.mem (kpairV M0 (vnNatV M0 0) (initCfgV M0)) R ∧
          ∀ k : M0.V, M0.mem k (vnOmegaV M0) →
            ∀ y : M0.V, M0.mem y (cfgSetV M0 (n + 1)) →
              M0.mem (kpairV M0 k y) R →
                M0.mem (kpairV M0 (insertV M0 k k) (zfcAppV M0 (nextStepV M0 M) y)) R) →
        M0.mem p R :=
  (exists_stepRelV M0 M).choose_spec p

lemma stepRelV_base {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    M0.mem (kpairV M0 (vnNatV M0 0) (initCfgV M0)) (stepRelV M0 M) :=
  (mem_stepRelV M0 M).mpr
    ⟨(kpairV_mem_prodV M0).mpr ⟨vnNatV_mem_vnOmegaV M0 0, initCfgV_mem M0⟩, fun _ hR => hR.1⟩

lemma stepRelV_step {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {k y : M0.V}
    (hk : M0.mem k (vnOmegaV M0)) (hy : M0.mem y (cfgSetV M0 (n + 1)))
    (hky : M0.mem (kpairV M0 k y) (stepRelV M0 M)) :
    M0.mem (kpairV M0 (insertV M0 k k) (zfcAppV M0 (nextStepV M0 M) y)) (stepRelV M0 M) :=
  (mem_stepRelV M0 M).mpr
    ⟨(kpairV_mem_prodV M0).mpr
        ⟨vnOmegaV_succ M0 hk, by rw [zfcAppV_nextStepV_all M0 M hy]; exact stepCfgV_mem M0 M hy⟩,
     fun R hR => hR.2 k hk y hy (((mem_stepRelV M0 M).mp hky).2 R hR)⟩

lemma orbitV_subset_relRange_stepRelV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : M0.V}
    (hz : M0.mem z (orbitV M0 M)) :
    M0.mem z (relRangeV M0 (stepRelV M0 M)) := by
  refine (mem_orbitV_iff M0 M).mp hz (relRangeV M0 (stepRelV M0 M)) ⟨?_, ?_⟩
  · exact (mem_relRangeV M0).mpr ⟨vnNatV M0 0, stepRelV_base M0 M⟩
  · intro y hy
    obtain ⟨k, hky⟩ := (mem_relRangeV M0).mp hy
    obtain ⟨hk, hyC⟩ := (kpairV_mem_prodV M0).mp ((mem_stepRelV M0 M).mp hky).1
    exact (mem_relRangeV M0).mpr ⟨insertV M0 k k, stepRelV_step M0 M hk hyC hky⟩

lemma stepRelV_inv {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {p : M0.V}
    (hp : M0.mem p (stepRelV M0 M)) :
    p = kpairV M0 (vnNatV M0 0) (initCfgV M0) ∨
      ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
        ∃ y : M0.V, M0.mem y (cfgSetV M0 (n + 1)) ∧
          M0.mem (kpairV M0 m y) (stepRelV M0 M) ∧
          p = kpairV M0 (insertV M0 m m) (zfcAppV M0 (nextStepV M0 M) y) := by
  let p0 := kpairV M0 (vnNatV M0 0) (initCfgV M0)
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.rel Language.Set.Rel.eq ![#0, &3] ⋎
      Semiformula.bexsMem (&0)
        (Semiformula.bexsMem (&1)
          ((∃¹ ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) ⋏
              Semiformula.rel Language.Set.Rel.mem ![#0, &4])) ⋏
            (∃¹ ((Rew.subst ![#0, #2] ▹ Rewriting.emb SetTheory.succ.dfn) ⋏
              (∃¹ ((Rew.subst ![#0, &2, #2] ▹ Rewriting.emb SetTheory.value.dfn) ⋏
                (Rew.subst ![#4, #1, #0] ▹ Rewriting.emb SetTheory.kpair.dfn)))))))
  let ε : ℕ → M0.V := fun i =>
    if i = 0 then vnOmegaV M0
    else if i = 1 then cfgSetV M0 (n + 1)
    else if i = 2 then nextStepV M0 M
    else if i = 3 then p0
    else stepRelV M0 M
  obtain ⟨R1, hR1⟩ := sepV M0 (stepRelV M0 M) φ ε
  have hφ : ∀ q : M0.V, evalM M0.mem ![q] ε φ ↔
      q = p0 ∨
        ∃ m : M0.V, M0.mem m (vnOmegaV M0) ∧
          ∃ y : M0.V, M0.mem y (cfgSetV M0 (n + 1)) ∧
            M0.mem (kpairV M0 m y) (stepRelV M0 M) ∧
            q = kpairV M0 (insertV M0 m m) (zfcAppV M0 (nextStepV M0 M) y) := by
    intro q
    dsimp only [φ]
    rw [evalM_or]
    refine or_congr Iff.rfl ?_
    rw [evalM_bexsMem]
    refine exists_congr fun m => and_congr Iff.rfl ?_
    rw [evalM_bexsMem]
    refine exists_congr fun y => and_congr Iff.rfl ?_
    rw [evalM_and]
    refine and_congr ?_ ?_
    · rw [evalM_exs]
      constructor
      · rintro ⟨w, hw1, hw2⟩
        change evalM M0.mem (w :> y :> m :> q :> ![]) ε
          ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) at hw1
        rw [evalM_subst, evalM_emb] at hw1
        have hweq : w = kpairV M0 m y := (ev_kpair M0 w m y).mp (by
          refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hw1
          funext i; fin_cases i <;> rfl)
        exact hweq ▸ hw2
      · intro hmy
        refine ⟨kpairV M0 m y, ?_, hmy⟩
        change evalM M0.mem (kpairV M0 m y :> y :> m :> q :> ![]) ε
          ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1])
        rw [evalM_subst, evalM_emb]
        refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 _ m y).mpr rfl)
        funext i; fin_cases i <;> rfl
    · rw [evalM_exs]
      constructor
      · rintro ⟨m', hm', y', hy', hq'⟩
        change evalM M0.mem (m' :> y :> m :> q :> ![]) ε
          ((Rewriting.emb SetTheory.succ.dfn) ⇜ ![#0, #2]) at hm'
        rw [evalM_subst, evalM_emb] at hm'
        have hm'eq : m' = insertV M0 m m := (ev_succ M0 m' m).mp (by
          refine (evalRaw_congr Eq M0.mem SetTheory.succ.dfn ?_ rfl).mp hm'
          funext i; fin_cases i <;> rfl)
        change evalM M0.mem (y' :> m' :> y :> m :> q :> ![]) ε
          ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, &2, #2]) at hy'
        rw [evalM_subst, evalM_emb] at hy'
        have hy'eq : y' = zfcAppV M0 (nextStepV M0 M) y := (ev_value M0 y' (nextStepV M0 M) y).mp (by
          refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mp hy'
          funext i; fin_cases i <;> rfl)
        change evalM M0.mem (y' :> m' :> y :> m :> q :> ![]) ε
          ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#4, #1, #0]) at hq'
        rw [evalM_subst, evalM_emb] at hq'
        have hqeq : q = kpairV M0 m' y' := (ev_kpair M0 q m' y').mp (by
          refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mp hq'
          funext i; fin_cases i <;> rfl)
        rw [hqeq, hm'eq, hy'eq]
      · intro hqeq
        refine ⟨insertV M0 m m, ?_, zfcAppV M0 (nextStepV M0 M) y, ?_, ?_⟩
        · change evalM M0.mem (insertV M0 m m :> y :> m :> q :> ![]) ε
            ((Rewriting.emb SetTheory.succ.dfn) ⇜ ![#0, #2])
          rw [evalM_subst, evalM_emb]
          refine (evalRaw_congr Eq M0.mem SetTheory.succ.dfn ?_ rfl).mpr ((ev_succ M0 _ m).mpr rfl)
          funext i; fin_cases i <;> rfl
        · change evalM M0.mem (zfcAppV M0 (nextStepV M0 M) y :> insertV M0 m m :> y :> m :> q :> ![]) ε
            ((Rewriting.emb SetTheory.value.dfn) ⇜ ![#0, &2, #2])
          rw [evalM_subst, evalM_emb]
          refine (evalRaw_congr Eq M0.mem SetTheory.value.dfn ?_ rfl).mpr
            ((ev_value M0 _ (nextStepV M0 M) y).mpr rfl)
          funext i; fin_cases i <;> rfl
        · change evalM M0.mem (zfcAppV M0 (nextStepV M0 M) y :> insertV M0 m m :> y :> m :> q :> ![]) ε
            ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#4, #1, #0])
          rw [evalM_subst, evalM_emb]
          refine (evalRaw_congr Eq M0.mem SetTheory.kpair.dfn ?_ rfl).mpr ((ev_kpair M0 q _ _).mpr hqeq)
          funext i; fin_cases i <;> rfl
  have hR1_closed : M0.mem p0 R1 ∧
      ∀ k : M0.V, M0.mem k (vnOmegaV M0) →
        ∀ y : M0.V, M0.mem y (cfgSetV M0 (n + 1)) →
          M0.mem (kpairV M0 k y) R1 →
            M0.mem (kpairV M0 (insertV M0 k k) (zfcAppV M0 (nextStepV M0 M) y)) R1 := by
    refine ⟨(hR1 p0).mpr ⟨stepRelV_base M0 M, (hφ p0).mpr (Or.inl rfl)⟩, fun k hk y hy hky => ?_⟩
    have hkyF : M0.mem (kpairV M0 k y) (stepRelV M0 M) := ((hR1 _).mp hky).1
    exact (hR1 _).mpr ⟨stepRelV_step M0 M hk hy hkyF, (hφ _).mpr (Or.inr ⟨k, hk, y, hy, hkyF, rfl⟩)⟩
  have hpR1 : M0.mem p R1 := ((mem_stepRelV M0 M).mp hp).2 R1 hR1_closed
  exact (hφ p).mp ((hR1 p).mp hpR1).2

end WithModel

section TransitiveInner

variable (MV : ZFModel) (P : MV.V → Prop)
  (hTrans : ∀ x y : MV.V, P y → MV.mem x y → P x)
  (hL : ∀ ψ ∈ 𝗭𝗙, evalM (fun a b : {x // P x} => MV.mem a.1 b.1) Fin.elim0 Empty.elim ψ)

private abbrev ML : ZFModel := ⟨{x // P x}, fun a b => MV.mem a.1 b.1, hL⟩

include hTrans

lemma sub_of_mem {z : MV.V} {b : (ML MV P hL).V} (h : MV.mem z b.1) : P z :=
  hTrans z b.1 b.2 h

lemma kpair_sub_left {a b : MV.V} (hp : P (kpairV MV a b)) : P a :=
  hTrans a (singletonV MV a)
    (hTrans _ _ hp ((mem_doubletonV MV).mpr (Or.inl rfl)))
    ((mem_singletonV MV).mpr rfl)

lemma kpair_sub_right {a b : MV.V} (hp : P (kpairV MV a b)) : P b :=
  hTrans b (doubletonV MV a b)
    (hTrans _ _ hp ((mem_doubletonV MV).mpr (Or.inr rfl)))
    ((mem_doubletonV MV).mpr (Or.inr rfl))

lemma val_eq_of_mem {a : (ML MV P hL).V} {v : MV.V}
    (hsub : ∀ z : MV.V, MV.mem z v → P z)
    (hiff : ∀ u : (ML MV P hL).V, (ML MV P hL).mem u a ↔ MV.mem u.1 v) :
    a.1 = v := by
  apply extV MV
  intro z
  constructor
  · intro hz
    exact (hiff ⟨z, hTrans z a.1 a.2 hz⟩).mp hz
  · intro hz
    exact (hiff ⟨z, hsub z hz⟩).mpr hz

lemma val_emptyV : (emptyV (ML MV P hL)).1 = emptyV MV :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => (not_mem_emptyV MV z hz).elim)
    (fun u => ⟨fun h => (not_mem_emptyV (ML MV P hL) u h).elim,
      fun h => (not_mem_emptyV MV u.1 h).elim⟩)

lemma val_doubletonV (a b : (ML MV P hL).V) :
    (doubletonV (ML MV P hL) a b).1 = doubletonV MV a.1 b.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => by
      rcases (mem_doubletonV MV).mp hz with rfl | rfl
      · exact a.2
      · exact b.2)
    (fun u => by
      rw [mem_doubletonV, mem_doubletonV]
      exact ⟨fun h => h.imp (congrArg Subtype.val) (congrArg Subtype.val),
        fun h => h.imp Subtype.ext Subtype.ext⟩)

lemma val_singletonV (a : (ML MV P hL).V) :
    (singletonV (ML MV P hL) a).1 = singletonV MV a.1 :=
  val_doubletonV MV P hTrans hL a a

lemma val_sUnionV (a : (ML MV P hL).V) :
    (sUnionV (ML MV P hL) a).1 = sUnionV MV a.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => by
      obtain ⟨w, hwa, hzw⟩ := (mem_sUnionV MV).mp hz
      exact hTrans z w (hTrans w a.1 a.2 hwa) hzw)
    (fun u => by
      rw [mem_sUnionV, mem_sUnionV]
      constructor
      · rintro ⟨w, hwa, huw⟩; exact ⟨w.1, hwa, huw⟩
      · rintro ⟨w, hwa, huw⟩; exact ⟨⟨w, hTrans w a.1 a.2 hwa⟩, hwa, huw⟩)

lemma val_unionV (a b : (ML MV P hL).V) :
    (unionV (ML MV P hL) a b).1 = unionV MV a.1 b.1 := by
  unfold unionV
  rw [val_sUnionV MV P hTrans hL, val_doubletonV MV P hTrans hL]

lemma val_insertV (a b : (ML MV P hL).V) :
    (insertV (ML MV P hL) a b).1 = insertV MV a.1 b.1 := by
  unfold insertV
  rw [val_unionV MV P hTrans hL, val_singletonV MV P hTrans hL]

lemma val_kpairV (a b : (ML MV P hL).V) :
    (kpairV (ML MV P hL) a b).1 = kpairV MV a.1 b.1 := by
  unfold kpairV
  rw [val_doubletonV MV P hTrans hL, val_singletonV MV P hTrans hL, val_doubletonV MV P hTrans hL]

lemma val_sInterV (a : (ML MV P hL).V) :
    (sInterV (ML MV P hL) a).1 = sInterV MV a.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => by
      obtain ⟨⟨y, hya⟩, hall⟩ := (mem_sInterV MV).mp hz
      exact hTrans z y (hTrans y a.1 a.2 hya) (hall y hya))
    (fun u => by
      rw [mem_sInterV, mem_sInterV]
      constructor
      · rintro ⟨⟨y, hya⟩, hall⟩
        refine ⟨⟨y.1, hya⟩, fun y' hy' => hall ⟨y', hTrans y' a.1 a.2 hy'⟩ hy'⟩
      · rintro ⟨⟨y', hy'⟩, hall⟩
        refine ⟨⟨⟨y', hTrans y' a.1 a.2 hy'⟩, hy'⟩, fun y hya => hall y.1 hya⟩)

lemma val_pi1V (w : (ML MV P hL).V) : (pi1V (ML MV P hL) w).1 = pi1V MV w.1 := by
  unfold pi1V
  rw [val_sUnionV MV P hTrans hL, val_sInterV MV P hTrans hL]

lemma val_pi2SepV (w : (ML MV P hL).V) : (pi2SepV (ML MV P hL) w).1 = pi2SepV MV w.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => by
      have hzu := ((mem_pi2SepV MV).mp hz).1
      rw [← val_sUnionV MV P hTrans hL w] at hzu
      exact hTrans z _ (sUnionV (ML MV P hL) w).2 hzu)
    (fun u => by
      rw [mem_pi2SepV, mem_pi2SepV]
      have h1 : MV.mem u.1 (sUnionV MV w.1) ↔ (ML MV P hL).mem u (sUnionV (ML MV P hL) w) := by
        rw [← val_sUnionV MV P hTrans hL w]
      have h2 : MV.mem u.1 (sInterV MV w.1) ↔ (ML MV P hL).mem u (sInterV (ML MV P hL) w) := by
        rw [← val_sInterV MV P hTrans hL w]
      have h3 : sUnionV MV w.1 = sInterV MV w.1 ↔ sUnionV (ML MV P hL) w = sInterV (ML MV P hL) w := by
        rw [← val_sUnionV MV P hTrans hL w, ← val_sInterV MV P hTrans hL w]
        exact ⟨Subtype.ext, congrArg Subtype.val⟩
      rw [h1, h2, h3])

lemma val_pi2V (w : (ML MV P hL).V) : (pi2V (ML MV P hL) w).1 = pi2V MV w.1 := by
  unfold pi2V
  rw [val_sUnionV MV P hTrans hL, val_pi2SepV MV P hTrans hL]

lemma val_prodV (X Y : (ML MV P hL).V) :
    (prodV (ML MV P hL) X Y).1 = prodV MV X.1 Y.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => by
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_prodV MV).mp hz
      let x' : (ML MV P hL).V := ⟨x, hTrans x X.1 X.2 hx⟩
      let y' : (ML MV P hL).V := ⟨y, hTrans y Y.1 Y.2 hy⟩
      have heq : kpairV MV x y = (kpairV (ML MV P hL) x' y').1 :=
        (val_kpairV MV P hTrans hL x' y').symm
      rw [heq]; exact (kpairV (ML MV P hL) x' y').2)
    (fun u => by
      rw [mem_prodV, mem_prodV]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨x.1, hx, y.1, hy, val_kpairV MV P hTrans hL x y⟩
      · rintro ⟨x, hx, y, hy, heq⟩
        let x' : (ML MV P hL).V := ⟨x, hTrans x X.1 X.2 hx⟩
        let y' : (ML MV P hL).V := ⟨y, hTrans y Y.1 Y.2 hy⟩
        refine ⟨x', hx, y', hy, Subtype.ext ?_⟩
        rw [val_kpairV MV P hTrans hL x' y']; exact heq)

lemma val_vnNatV (k : ℕ) : (vnNatV (ML MV P hL) k).1 = vnNatV MV k := by
  induction k with
  | zero => exact val_emptyV MV P hTrans hL
  | succ k ih =>
    change (insertV (ML MV P hL) (vnNatV (ML MV P hL) k) (vnNatV (ML MV P hL) k)).1 = _
    rw [val_insertV MV P hTrans hL, ih]
    rfl

lemma val_vnOmegaV : (vnOmegaV (ML MV P hL)).1 = vnOmegaV MV := by
  have hωV_sub : ∀ z : MV.V, MV.mem z (vnOmegaV MV) → MV.mem z (vnOmegaV (ML MV P hL)).1 := by
    intro z hz
    refine (mem_vnOmegaV_iff MV).mp hz (vnOmegaV (ML MV P hL)).1 ⟨?_, ?_⟩
    · rw [← val_emptyV MV P hTrans hL]
      exact vnNatV_mem_vnOmegaV (ML MV P hL) 0
    · intro y hy
      let u : (ML MV P hL).V := ⟨y, hTrans y _ (vnOmegaV (ML MV P hL)).2 hy⟩
      have hsucc : (ML MV P hL).mem (insertV (ML MV P hL) u u) (vnOmegaV (ML MV P hL)) :=
        vnOmegaV_succ (ML MV P hL) hy
      rwa [← val_insertV MV P hTrans hL u u]
  have hωL_sub : ∀ x : MV.V, MV.mem x (vnOmegaV (ML MV P hL)).1 → MV.mem x (vnOmegaV MV) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨x₀, hx₀L, hx₀nV⟩ := hnot
    let φ : SetTheorySemiproposition 1 :=
      ∼(Semiformula.rel Language.Set.Rel.mem ![#0, &0])
    obtain ⟨D, hD⟩ := sepV MV (vnOmegaV (ML MV P hL)).1 φ (fun _ => vnOmegaV MV)
    have hD_iff : ∀ z : MV.V, MV.mem z D ↔
        MV.mem z (vnOmegaV (ML MV P hL)).1 ∧ ¬ MV.mem z (vnOmegaV MV) := by
      intro z
      rw [hD z]
      refine and_congr Iff.rfl ?_
      dsimp only [φ]
      rw [evalM_not]
      rfl
    have hx₀D : MV.mem x₀ D := (hD_iff x₀).mpr ⟨hx₀L, hx₀nV⟩
    obtain ⟨y₀, hy₀D, hy₀min⟩ := foundationV MV D ⟨x₀, hx₀D⟩
    obtain ⟨hy₀L, hy₀nV⟩ := (hD_iff y₀).mp hy₀D
    let u : (ML MV P hL).V := ⟨y₀, hTrans y₀ _ (vnOmegaV (ML MV P hL)).2 hy₀L⟩
    rcases vnOmegaV_zero_or_succ (ML MV P hL) (u := u) hy₀L with hu0 | ⟨w, hw, huw⟩
    · have hy0 : y₀ = emptyV MV := by
        calc y₀ = u.1 := rfl
          _ = (emptyV (ML MV P hL)).1 := congrArg Subtype.val hu0
          _ = emptyV MV := val_emptyV MV P hTrans hL
      exact hy₀nV (hy0 ▸ vnNatV_mem_vnOmegaV MV 0)
    · have hw_mem_y0 : MV.mem w.1 y₀ := by
        have h1 : (ML MV P hL).mem w (insertV (ML MV P hL) w w) :=
          (mem_insertV (ML MV P hL)).mpr (Or.inl rfl)
        rw [← huw] at h1
        exact h1
      have hwnD : ¬ MV.mem w.1 D := fun hwD => hy₀min w.1 hwD hw_mem_y0
      have hwV : MV.mem w.1 (vnOmegaV MV) := by
        by_contra hwnV
        exact hwnD ((hD_iff w.1).mpr ⟨hw, hwnV⟩)
      have hy0_eq : y₀ = insertV MV w.1 w.1 := by
        calc y₀ = u.1 := rfl
          _ = (insertV (ML MV P hL) w w).1 := congrArg Subtype.val huw
          _ = insertV MV w.1 w.1 := val_insertV MV P hTrans hL w w
      exact hy₀nV (hy0_eq ▸ vnOmegaV_succ MV hwV)
  exact extV MV fun z => ⟨hωL_sub z, hωV_sub z⟩

lemma val_intSetV : (intSetV (ML MV P hL)).1 = intSetV MV := by
  unfold intSetV
  rw [val_prodV MV P hTrans hL, val_vnNatV MV P hTrans hL, val_vnOmegaV MV P hTrans hL]

lemma val_relRangeV (R : (ML MV P hL).V) : (relRangeV (ML MV P hL) R).1 = relRangeV MV R.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun y hy => by
      obtain ⟨x, hx⟩ := (mem_relRangeV MV).mp hy
      exact kpair_sub_right MV P hTrans (hTrans _ R.1 R.2 hx))
    (fun u => by
      rw [mem_relRangeV, mem_relRangeV]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x.1, ?_⟩
        rw [← val_kpairV MV P hTrans hL x u]; exact hx
      · rintro ⟨x, hx⟩
        have hpx : P x := kpair_sub_left MV P hTrans (hTrans _ R.1 R.2 hx)
        let x' : (ML MV P hL).V := ⟨x, hpx⟩
        refine ⟨x', ?_⟩
        show MV.mem (kpairV (ML MV P hL) x' u).1 R.1
        rw [val_kpairV MV P hTrans hL x' u]; exact hx)

lemma val_zfcAppV (f x : (ML MV P hL).V) : (zfcAppV (ML MV P hL) f x).1 = zfcAppV MV f.1 x.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun z hz => by
      obtain ⟨_, y, hzy, hxy⟩ := (mem_zfcAppV MV).mp hz
      exact hTrans z y (kpair_sub_right MV P hTrans (hTrans _ f.1 f.2 hxy)) hzy)
    (fun u => by
      rw [mem_zfcAppV, mem_zfcAppV]
      have hs : MV.mem u.1 (sUnionV MV (relRangeV MV f.1)) ↔
          (ML MV P hL).mem u (sUnionV (ML MV P hL) (relRangeV (ML MV P hL) f)) := by
        rw [← val_relRangeV MV P hTrans hL f, ← val_sUnionV MV P hTrans hL]
      rw [hs]
      refine and_congr Iff.rfl ?_
      constructor
      · rintro ⟨y, huy, hxy⟩
        refine ⟨y.1, huy, ?_⟩
        rw [← val_kpairV MV P hTrans hL x y]; exact hxy
      · rintro ⟨y, huy, hxy⟩
        have hpy : P y := kpair_sub_right MV P hTrans (hTrans _ f.1 f.2 hxy)
        let y' : (ML MV P hL).V := ⟨y, hpy⟩
        refine ⟨y', huy, ?_⟩
        show MV.mem (kpairV (ML MV P hL) x y').1 f.1
        rw [val_kpairV MV P hTrans hL x y']; exact hxy)

lemma mem_funsV_iff (X Y f : (ML MV P hL).V) :
    (ML MV P hL).mem f (funsV (ML MV P hL) X Y) ↔ MV.mem f.1 (funsV MV X.1 Y.1) := by
  rw [mem_funsV, mem_funsV]
  refine and_congr ?_ ?_
  · constructor
    · intro h p hp
      let p' : (ML MV P hL).V := ⟨p, hTrans p f.1 f.2 hp⟩
      have := h p' hp
      rwa [← val_prodV MV P hTrans hL X Y]
    · intro h p hp
      have := h p.1 hp
      rwa [← val_prodV MV P hTrans hL X Y] at this
  · constructor
    · intro h x hx
      let x' : (ML MV P hL).V := ⟨x, hTrans x X.1 X.2 hx⟩
      obtain ⟨y, hy, huniq⟩ := h x' hx
      refine ⟨y.1, ?_, fun y2 hy2 => ?_⟩
      · change MV.mem (kpairV MV x'.1 y.1) f.1
        rw [← val_kpairV MV P hTrans hL x' y]; exact hy
      · have hpy2 : P y2 := kpair_sub_right MV P hTrans (hTrans _ f.1 f.2 hy2)
        let y2' : (ML MV P hL).V := ⟨y2, hpy2⟩
        have hmem2 : (ML MV P hL).mem (kpairV (ML MV P hL) x' y2') f := by
          show MV.mem (kpairV (ML MV P hL) x' y2').1 f.1
          rw [val_kpairV MV P hTrans hL x' y2']; exact hy2
        exact congrArg Subtype.val (huniq y2' hmem2)
    · intro h x hx
      obtain ⟨y, hy, huniq⟩ := h x.1 hx
      have hpy : P y := kpair_sub_right MV P hTrans (hTrans _ f.1 f.2 hy)
      let y' : (ML MV P hL).V := ⟨y, hpy⟩
      refine ⟨y', ?_, fun y2 hy2 => Subtype.ext ?_⟩
      · show MV.mem (kpairV (ML MV P hL) x y').1 f.1
        rw [val_kpairV MV P hTrans hL x y']; exact hy
      · exact huniq y2.1 (by dsimp only; rw [← val_kpairV MV P hTrans hL x y2]; exact hy2)

lemma val_emptyTapeV : (emptyTapeV (ML MV P hL)).1 = emptyTapeV MV :=
  val_eq_of_mem MV P hTrans hL
    (fun p hp => by
      obtain ⟨u, hu, rfl⟩ := (mem_emptyTapeV MV).mp hp
      rw [← val_intSetV MV P hTrans hL] at hu
      let u' : (ML MV P hL).V := ⟨u, hTrans u _ (intSetV (ML MV P hL)).2 hu⟩
      have heq : kpairV MV u (vnNatV MV 0) = (kpairV (ML MV P hL) u' (vnNatV (ML MV P hL) 0)).1 := by
        rw [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL]
      rw [heq]; exact (kpairV (ML MV P hL) u' (vnNatV (ML MV P hL) 0)).2)
    (fun p => by
      rw [mem_emptyTapeV, mem_emptyTapeV]
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u.1, ?_, ?_⟩
        · rw [← val_intSetV MV P hTrans hL]; exact hu
        · rw [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL]
      · rintro ⟨u, hu, heq⟩
        rw [← val_intSetV MV P hTrans hL] at hu
        let u' : (ML MV P hL).V := ⟨u, hTrans u _ (intSetV (ML MV P hL)).2 hu⟩
        refine ⟨u', hu, Subtype.ext ?_⟩
        rw [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL]; exact heq)

lemma val_initCfgV : (initCfgV (ML MV P hL)).1 = initCfgV MV := by
  unfold initCfgV encodeIntV
  rw [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, val_kpairV MV P hTrans hL,
    val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, val_emptyTapeV MV P hTrans hL]

lemma val_omegaPredV {r : (ML MV P hL).V} (hr : (ML MV P hL).mem r (vnOmegaV (ML MV P hL)))
    (hne : r ≠ emptyV (ML MV P hL)) :
    (omegaPredV (ML MV P hL) r).1 = omegaPredV MV r.1 := by
  obtain ⟨hpmem, hpeq⟩ := omegaPredV_spec (ML MV P hL) hr hne
  have hpeqV : r.1 = insertV MV (omegaPredV (ML MV P hL) r).1 (omegaPredV (ML MV P hL) r).1 := by
    calc r.1 = (insertV (ML MV P hL) (omegaPredV (ML MV P hL) r) (omegaPredV (ML MV P hL) r)).1 :=
          congrArg Subtype.val hpeq
      _ = insertV MV (omegaPredV (ML MV P hL) r).1 (omegaPredV (ML MV P hL) r).1 :=
          val_insertV MV P hTrans hL _ _
  have hpmemV : MV.mem (omegaPredV (ML MV P hL) r).1 (vnOmegaV MV) := by
    rw [← val_vnOmegaV MV P hTrans hL]; exact hpmem
  rw [hpeqV, omegaPredV_succ MV hpmemV]

lemma val_intSuccV {pos : (ML MV P hL).V} (hpos : (ML MV P hL).mem pos (intSetV (ML MV P hL))) :
    (intSuccV (ML MV P hL) pos).1 = intSuccV MV pos.1 := by
  have h01 : vnNatV MV 0 ≠ vnNatV MV 1 := fun h => absurd (vnNatV_inj MV h) (by decide)
  have h10 : vnNatV MV 1 ≠ vnNatV MV 0 := h01.symm
  have h10L : vnNatV (ML MV P hL) 1 ≠ vnNatV (ML MV P hL) 0 :=
    fun h => absurd (vnNatV_inj (ML MV P hL) h) (by decide)
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp (ML MV P hL) hpos
  · unfold intSuccV
    rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl,
      val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, val_kpairV MV P hTrans hL,
      val_vnNatV MV P hTrans hL, pi1V_kpairV, pi2V_kpairV, if_pos rfl, val_insertV MV P hTrans hL]
  · unfold intSuccV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h10L,
      val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, pi1V_kpairV, pi2V_kpairV, if_neg h10]
    by_cases hr0 : r = vnNatV (ML MV P hL) 0
    · have hr0V : r.1 = vnNatV MV 0 := by rw [hr0, val_vnNatV MV P hTrans hL]
      rw [if_pos hr0, if_pos hr0V]
      unfold encodeIntV
      rw [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL]
    · have hr0V : r.1 ≠ vnNatV MV 0 := fun h => hr0 (Subtype.ext (h.trans (val_vnNatV MV P hTrans hL 0).symm))
      rw [if_neg hr0, if_neg hr0V, val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL,
        val_omegaPredV MV P hTrans hL hr hr0]

lemma val_intPredV {pos : (ML MV P hL).V} (hpos : (ML MV P hL).mem pos (intSetV (ML MV P hL))) :
    (intPredV (ML MV P hL) pos).1 = intPredV MV pos.1 := by
  have h01 : vnNatV MV 0 ≠ vnNatV MV 1 := fun h => absurd (vnNatV_inj MV h) (by decide)
  have h01L : vnNatV (ML MV P hL) 0 ≠ vnNatV (ML MV P hL) 1 :=
    fun h => absurd (vnNatV_inj (ML MV P hL) h) (by decide)
  obtain ⟨r, hr, rfl | rfl⟩ := mem_intSetV_decomp (ML MV P hL) hpos
  · unfold intPredV
    rw [pi1V_kpairV, pi2V_kpairV, if_neg h01L,
      val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, pi1V_kpairV, pi2V_kpairV, if_neg h01]
    by_cases hr0 : r = vnNatV (ML MV P hL) 0
    · have hr0V : r.1 = vnNatV MV 0 := by rw [hr0, val_vnNatV MV P hTrans hL]
      rw [if_pos hr0, if_pos hr0V, val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL,
        val_vnNatV MV P hTrans hL]
    · have hr0V : r.1 ≠ vnNatV MV 0 := fun h => hr0 (Subtype.ext (h.trans (val_vnNatV MV P hTrans hL 0).symm))
      rw [if_neg hr0, if_neg hr0V, val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL,
        val_omegaPredV MV P hTrans hL hr hr0]
  · unfold intPredV
    rw [pi1V_kpairV, pi2V_kpairV, if_pos rfl,
      val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, val_kpairV MV P hTrans hL,
      val_vnNatV MV P hTrans hL, pi1V_kpairV, pi2V_kpairV, if_pos rfl, val_insertV MV P hTrans hL]

lemma val_updateTapeV (g pos val : (ML MV P hL).V) :
    (updateTapeV (ML MV P hL) g pos val).1 = updateTapeV MV g.1 pos.1 val.1 :=
  val_eq_of_mem MV P hTrans hL
    (fun p hp => by
      have hp_prod := ((mem_updateTapeV MV).mp hp).1
      rw [← val_intSetV MV P hTrans hL, ← val_vnNatV MV P hTrans hL 2,
        ← val_prodV MV P hTrans hL] at hp_prod
      exact hTrans p _ (prodV (ML MV P hL) (intSetV (ML MV P hL)) (vnNatV (ML MV P hL) 2)).2 hp_prod)
    (fun p => by
      rw [mem_updateTapeV, mem_updateTapeV]
      have hprod : MV.mem p.1 (prodV MV (intSetV MV) (vnNatV MV 2)) ↔
          (ML MV P hL).mem p (prodV (ML MV P hL) (intSetV (ML MV P hL)) (vnNatV (ML MV P hL) 2)) := by
        rw [← val_intSetV MV P hTrans hL, ← val_vnNatV MV P hTrans hL 2,
          ← val_prodV MV P hTrans hL]
      rw [hprod]
      refine and_congr Iff.rfl (or_congr ?_ (and_congr Iff.rfl ?_))
      · rw [← val_kpairV MV P hTrans hL pos val]
        exact ⟨congrArg Subtype.val, Subtype.ext⟩
      · constructor
        · intro h v hv
          have hpv : P v := kpair_sub_right MV P hTrans (hv ▸ p.2)
          let v' : (ML MV P hL).V := ⟨v, hpv⟩
          exact h v' (Subtype.ext (by rw [val_kpairV MV P hTrans hL pos v']; exact hv))
        · intro h v hv
          exact h v.1 (by rw [← val_kpairV MV P hTrans hL pos v]; exact congrArg Subtype.val hv))

lemma decodeNatV_val {N : ℕ} {x : (ML MV P hL).V} (hx : (ML MV P hL).mem x (vnNatV (ML MV P hL) N)) :
    decodeNatV MV N x.1 = decodeNatV (ML MV P hL) N x := by
  obtain ⟨hk, heq⟩ := decodeNatV_spec (ML MV P hL) hx
  have hxV : x.1 = vnNatV MV (decodeNatV (ML MV P hL) N x) := by
    calc x.1 = (vnNatV (ML MV P hL) (decodeNatV (ML MV P hL) N x)).1 := congrArg Subtype.val heq
      _ = vnNatV MV (decodeNatV (ML MV P hL) N x) := val_vnNatV MV P hTrans hL _
  rw [hxV, decodeNatV_vnNatV MV hk]

lemma mem_cfgSetV_of_val {N : ℕ} {z : (ML MV P hL).V}
    (hz : (ML MV P hL).mem z (cfgSetV (ML MV P hL) N)) :
    MV.mem z.1 (cfgSetV MV N) := by
  obtain ⟨q, hq, tail, htail, rfl⟩ := (mem_prodV (ML MV P hL)).mp hz
  obtain ⟨pos, hpos, g, hg, rfl⟩ := (mem_prodV (ML MV P hL)).mp htail
  unfold cfgSetV
  rw [val_kpairV MV P hTrans hL, val_kpairV MV P hTrans hL]
  refine (kpairV_mem_prodV MV).mpr ⟨?_, (kpairV_mem_prodV MV).mpr ⟨?_, ?_⟩⟩
  · rw [← val_vnNatV MV P hTrans hL N]; exact hq
  · rw [← val_intSetV MV P hTrans hL]; exact hpos
  · rw [← val_intSetV MV P hTrans hL, ← val_vnNatV MV P hTrans hL 2]
    exact (mem_funsV_iff MV P hTrans hL _ _ _).mp hg

lemma val_stepCfgV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : (ML MV P hL).V}
    (hz : (ML MV P hL).mem z (cfgSetV (ML MV P hL) (n + 1))) :
    (stepCfgV (ML MV P hL) M z).1 = stepCfgV MV M z.1 := by
  obtain ⟨q, hq, tail, htail, rfl⟩ := (mem_prodV (ML MV P hL)).mp hz
  obtain ⟨pos, hpos, g, hg, rfl⟩ := (mem_prodV (ML MV P hL)).mp htail
  have hsymL : (ML MV P hL).mem (zfcAppV (ML MV P hL) g pos) (vnNatV (ML MV P hL) 2) :=
    zfcAppV_mem_codomain (ML MV P hL) hg hpos
  have hq_val : (kpairV (ML MV P hL) q (kpairV (ML MV P hL) pos g)).1 =
      kpairV MV q.1 (kpairV MV pos.1 g.1) := by
    rw [val_kpairV MV P hTrans hL, val_kpairV MV P hTrans hL]
  rw [hq_val]
  unfold stepCfgV
  dsimp only
  rw [pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV,
    pi1V_kpairV, pi2V_kpairV, pi1V_kpairV, pi2V_kpairV,
    ← val_zfcAppV MV P hTrans hL g pos,
    decodeNatV_val MV P hTrans hL hq,
    decodeNatV_val MV P hTrans hL hsymL,
    val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL,
    val_kpairV MV P hTrans hL, val_updateTapeV MV P hTrans hL, val_vnNatV MV P hTrans hL]
  congr 2
  split_ifs
  · exact val_intPredV MV P hTrans hL hpos
  · rfl
  · exact val_intSuccV MV P hTrans hL hpos

lemma val_zfcAppV_nextStepV {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) {z : (ML MV P hL).V}
    (hz : (ML MV P hL).mem z (cfgSetV (ML MV P hL) (n + 1))) :
    (zfcAppV (ML MV P hL) (nextStepV (ML MV P hL) M) z).1 = zfcAppV MV (nextStepV MV M) z.1 := by
  rw [zfcAppV_nextStepV_all (ML MV P hL) M hz,
    zfcAppV_nextStepV_all MV M (mem_cfgSetV_of_val MV P hTrans hL hz)]
  exact val_stepCfgV MV P hTrans hL M hz

lemma orbitV_subset_val {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ z : MV.V, MV.mem z (orbitV MV M) → MV.mem z (orbitV (ML MV P hL) M).1 := by
  intro z hz
  refine (mem_orbitV_iff MV M).mp hz (orbitV (ML MV P hL) M).1 ⟨?_, ?_⟩
  · rw [← val_initCfgV MV P hTrans hL]
    exact initCfgV_mem_orbitV (ML MV P hL) M
  · intro y hy
    let yL : (ML MV P hL).V := ⟨y, hTrans y _ (orbitV (ML MV P hL) M).2 hy⟩
    have hy_cfg : (ML MV P hL).mem yL (cfgSetV (ML MV P hL) (n + 1)) :=
      orbitV_subset_cfgSet (ML MV P hL) M hy
    rw [← val_zfcAppV_nextStepV MV P hTrans hL M hy_cfg]
    exact nextStepV_mem_orbitV (ML MV P hL) M hy

theorem halts_downward_abs {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hHaltsV : evalM MV.mem Fin.elim0 Empty.elim (Constant14.halts M)) :
    evalM (ML MV P hL).mem Fin.elim0 Empty.elim (Constant14.halts M) := by
  obtain ⟨m', _, g', _, hmemV⟩ := (ev_halts_iff MV M).mp hHaltsV
  have hmemL_val : MV.mem (kpairV MV (vnNatV MV n) (kpairV MV m' g')) (orbitV (ML MV P hL) M).1 :=
    orbitV_subset_val MV P hTrans hL M _ hmemV
  let zL : (ML MV P hL).V := ⟨kpairV MV (vnNatV MV n) (kpairV MV m' g'),
    hTrans _ _ (orbitV (ML MV P hL) M).2 hmemL_val⟩
  have hzL_cfg : (ML MV P hL).mem zL (cfgSetV (ML MV P hL) (n + 1)) :=
    orbitV_subset_cfgSet (ML MV P hL) M hmemL_val
  obtain ⟨qL, _, tailL, htailL, hzL_eq⟩ := (mem_prodV (ML MV P hL)).mp hzL_cfg
  obtain ⟨mL, hmL, gL, hgL, htailL_eq⟩ := (mem_prodV (ML MV P hL)).mp htailL
  have hzeqV : kpairV MV (vnNatV MV n) (kpairV MV m' g') =
      kpairV MV qL.1 (kpairV MV mL.1 gL.1) := by
    calc kpairV MV (vnNatV MV n) (kpairV MV m' g') = zL.1 := rfl
      _ = (kpairV (ML MV P hL) qL (kpairV (ML MV P hL) mL gL)).1 := by
          rw [hzL_eq, htailL_eq]
      _ = kpairV MV qL.1 (kpairV MV mL.1 gL.1) := by
          rw [val_kpairV MV P hTrans hL, val_kpairV MV P hTrans hL]
  have hqL_eq : qL = vnNatV (ML MV P hL) n := Subtype.ext (by
    rw [val_vnNatV MV P hTrans hL n]
    exact (kpairV_inj MV hzeqV).1.symm)
  have hzL_halting : zL = kpairV (ML MV P hL) (vnNatV (ML MV P hL) n) (kpairV (ML MV P hL) mL gL) := by
    rw [hzL_eq, htailL_eq, hqL_eq]
  refine (ev_halts_iff (ML MV P hL) M).mpr ⟨mL, hmL, gL, hgL, ?_⟩
  rw [← hzL_halting]
  exact hmemL_val


lemma val_orbitV_subset {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ z : (ML MV P hL).V, (ML MV P hL).mem z (orbitV (ML MV P hL) M) →
      MV.mem z.1 (orbitV MV M) := by
  intro zL hzL
  have hrange : (ML MV P hL).mem zL (relRangeV (ML MV P hL) (stepRelV (ML MV P hL) M)) :=
    orbitV_subset_relRange_stepRelV (ML MV P hL) M hzL
  obtain ⟨kL, hkLzL⟩ := (mem_relRangeV (ML MV P hL)).mp hrange
  obtain ⟨hkLω, hzLC⟩ := (kpairV_mem_prodV (ML MV P hL)).mp ((mem_stepRelV (ML MV P hL) M).mp hkLzL).1
  refine (mem_orbitV_iff MV M).mpr fun A ⟨hA0, hAstep⟩ => ?_
  let φ : SetTheorySemiproposition 1 :=
    Semiformula.ballMem (&0)
      (∀¹ ((Rew.subst ![#0, #2, #1] ▹ Rewriting.emb SetTheory.kpair.dfn) 🡒
        Semiformula.rel Language.Set.Rel.mem ![#0, &1] 🡒
        Semiformula.rel Language.Set.Rel.mem ![#1, &2]))
  let ε : ℕ → MV.V := fun i =>
    if i = 0 then cfgSetV MV (n + 1)
    else if i = 1 then (stepRelV (ML MV P hL) M).1
    else A
  obtain ⟨I, hI⟩ := sepV MV (vnOmegaV MV) φ ε
  have hI_iff : ∀ k : MV.V, MV.mem k I ↔
      MV.mem k (vnOmegaV MV) ∧
        ∀ z : MV.V, MV.mem z (cfgSetV MV (n + 1)) →
          MV.mem (kpairV MV k z) (stepRelV (ML MV P hL) M).1 → MV.mem z A := by
    intro k
    rw [hI k]
    refine and_congr Iff.rfl ?_
    dsimp only [φ]
    rw [evalM_ballMem]
    refine forall₂_congr fun z _ => ?_
    rw [evalM_all]
    refine (?_ : _ ↔ ∀ q : MV.V, q = kpairV MV k z →
        MV.mem q (stepRelV (ML MV P hL) M).1 → MV.mem z A).trans
      ⟨fun h hq => h _ rfl hq, fun h q hq hmem => h (hq ▸ hmem)⟩
    refine forall_congr' fun q => ?_
    rw [evalM_imp, evalM_imp]
    refine imp_congr ?_ (imp_congr Iff.rfl Iff.rfl)
    change evalM MV.mem (q :> z :> k :> ![]) ε
      ((Rewriting.emb SetTheory.kpair.dfn) ⇜ ![#0, #2, #1]) ↔ _
    rw [evalM_subst, evalM_emb]
    refine (evalRaw_congr Eq MV.mem SetTheory.kpair.dfn ?_ rfl).trans (ev_kpair MV q k z)
    funext i; fin_cases i <;> rfl
  have hI_ind : MV.mem (emptyV MV) I ∧ ∀ k : MV.V, MV.mem k I → MV.mem (insertV MV k k) I := by
    constructor
    · refine (hI_iff (emptyV MV)).mpr ⟨vnNatV_mem_vnOmegaV MV 0, fun z _ hq => ?_⟩
      have hpz : P z := kpair_sub_right MV P hTrans (hTrans _ _ (stepRelV (ML MV P hL) M).2 hq)
      let z' : (ML MV P hL).V := ⟨z, hpz⟩
      have hqL : (ML MV P hL).mem (kpairV (ML MV P hL) (vnNatV (ML MV P hL) 0) z')
          (stepRelV (ML MV P hL) M) := by
        show MV.mem (kpairV (ML MV P hL) (vnNatV (ML MV P hL) 0) z').1 (stepRelV (ML MV P hL) M).1
        rw [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL 0]
        exact hq
      rcases stepRelV_inv (ML MV P hL) M hqL with heq0 | ⟨m, _, y, _, _, heqs⟩
      · have hz'eq : z' = initCfgV (ML MV P hL) := (kpairV_inj (ML MV P hL) heq0).2
        have hzV : z = initCfgV MV := by
          calc z = z'.1 := rfl
            _ = (initCfgV (ML MV P hL)).1 := congrArg Subtype.val hz'eq
            _ = initCfgV MV := val_initCfgV MV P hTrans hL
        exact hzV ▸ hA0
      · exact (insertV_ne_zero (ML MV P hL) m (kpairV_inj (ML MV P hL) heqs).1.symm).elim
    · intro k hk
      obtain ⟨hkω, hk_all⟩ := (hI_iff k).mp hk
      refine (hI_iff (insertV MV k k)).mpr ⟨vnOmegaV_succ MV hkω, fun z _ hq => ?_⟩
      have hkLω' : MV.mem k (vnOmegaV (ML MV P hL)).1 := by
        rw [val_vnOmegaV MV P hTrans hL]; exact hkω
      let k' : (ML MV P hL).V := ⟨k, hTrans k _ (vnOmegaV (ML MV P hL)).2 hkLω'⟩
      have hpz : P z := kpair_sub_right MV P hTrans (hTrans _ _ (stepRelV (ML MV P hL) M).2 hq)
      let z' : (ML MV P hL).V := ⟨z, hpz⟩
      have hqL : (ML MV P hL).mem (kpairV (ML MV P hL) (insertV (ML MV P hL) k' k') z')
          (stepRelV (ML MV P hL) M) := by
        show MV.mem (kpairV (ML MV P hL) (insertV (ML MV P hL) k' k') z').1
          (stepRelV (ML MV P hL) M).1
        rw [val_kpairV MV P hTrans hL, val_insertV MV P hTrans hL]
        exact hq
      rcases stepRelV_inv (ML MV P hL) M hqL with heq0 | ⟨m, _, y, hyC, hmyF, heqs⟩
      · exact (insertV_ne_zero (ML MV P hL) k' (kpairV_inj (ML MV P hL) heq0).1).elim
      · obtain ⟨hsucc_eq, hz'_eq⟩ := kpairV_inj (ML MV P hL) heqs
        have hkm : k' = m := succV_inj (ML MV P hL) hsucc_eq
        subst hkm
        have hyA : MV.mem y.1 A := by
          refine hk_all y.1 (mem_cfgSetV_of_val MV P hTrans hL hyC) ?_
          change MV.mem (kpairV MV k'.1 y.1) (stepRelV (ML MV P hL) M).1
          rw [← val_kpairV MV P hTrans hL k' y]
          exact hmyF
        have hstepA : MV.mem (zfcAppV MV (nextStepV MV M) y.1) A := hAstep y.1 hyA
        have hzV : z = zfcAppV MV (nextStepV MV M) y.1 := by
          calc z = z'.1 := rfl
            _ = (zfcAppV (ML MV P hL) (nextStepV (ML MV P hL) M) y).1 := congrArg Subtype.val hz'_eq
            _ = zfcAppV MV (nextStepV MV M) y.1 := val_zfcAppV_nextStepV MV P hTrans hL M hyC
        exact hzV ▸ hstepA
  have hkLV : MV.mem kL.1 (vnOmegaV MV) := by
    rw [← val_vnOmegaV MV P hTrans hL]; exact hkLω
  have hkLI : MV.mem kL.1 I := (mem_vnOmegaV_iff MV).mp hkLV I hI_ind
  refine ((hI_iff kL.1).mp hkLI).2 zL.1 (mem_cfgSetV_of_val MV P hTrans hL hzLC) ?_
  rw [← val_kpairV MV P hTrans hL kL zL]
  exact hkLzL

theorem halts_upward_abs {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hHaltsL : evalM (ML MV P hL).mem Fin.elim0 Empty.elim (Constant14.halts M)) :
    evalM MV.mem Fin.elim0 Empty.elim (Constant14.halts M) := by
  obtain ⟨mL, hmL, gL, hgL, hmemL⟩ := (ev_halts_iff (ML MV P hL) M).mp hHaltsL
  refine (ev_halts_iff MV M).mpr ⟨mL.1, ?_, gL.1, ?_, ?_⟩
  · rw [← val_intSetV MV P hTrans hL]; exact hmL
  · rw [← val_intSetV MV P hTrans hL, ← val_vnNatV MV P hTrans hL 2]
    exact (mem_funsV_iff MV P hTrans hL _ _ _).mp hgL
  · have hval := val_orbitV_subset MV P hTrans hL M _ hmemL
    rwa [val_kpairV MV P hTrans hL, val_vnNatV MV P hTrans hL, val_kpairV MV P hTrans hL] at hval

theorem halts_iff_abs {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    evalM MV.mem Fin.elim0 Empty.elim (Constant14.halts M) ↔
      evalM (ML MV P hL).mem Fin.elim0 Empty.elim (Constant14.halts M) :=
  ⟨halts_downward_abs MV P hTrans hL M, halts_upward_abs MV P hTrans hL M⟩

end TransitiveInner

/- ## Section 7: Bridge from inline `sat` in `H2` to `evalM` -/

lemma sat_iff_evalM {V : Type} (mem : V → V → Prop) :
    ∀ {m : ℕ} (φ : Semiformula ℒₛₑₜ Empty m) (e : Fin m → V),
      (let tv {k : ℕ} (e' : Fin k → V) : Semiterm ℒₛₑₜ Empty k → V :=
         @Semiterm.rec ℒₛₑₜ Empty k (fun _ => V) e' Empty.elim (fun {_} f _ _ => f.elim)
       @Semiformula.rec ℒₛₑₜ Empty (fun k _ => (Fin k → V) → Prop)
         (fun _ => True) (fun _ => False)
         (fun r v e' => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
           (fun w => tv e' (w 0) = tv e' (w 1)) (fun w => mem (tv e' (w 0)) (tv e' (w 1))) _ r v)
         (fun r v e' => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
           (fun w => tv e' (w 0) = tv e' (w 1)) (fun w => mem (tv e' (w 0)) (tv e' (w 1))) _ r v)
         (fun _ _ a b e' => a e' ∧ b e') (fun _ _ a b e' => a e' ∨ b e')
         (fun _ a e' => ∀ d, a (d :> e')) (fun _ a e' => ∃ d, a (d :> e')) m φ e) ↔
      evalM mem e Empty.elim φ := by
  have htv : ∀ {k : ℕ} (e' : Fin k → V) (t : Semiterm ℒₛₑₜ Empty k),
      @Semiterm.rec ℒₛₑₜ Empty k (fun _ => V) e' Empty.elim (fun {_} f _ _ => f.elim) t =
        tvRaw e' Empty.elim t := by
    intro k e' t
    cases t with
    | bvar i => rfl
    | fvar x => exact x.elim
    | func f _ => exact f.elim
  intro m φ
  induction φ with
  | verum => intro _; exact Iff.rfl
  | falsum => intro _; exact Iff.rfl
  | rel r v =>
    intro e
    cases r with
    | eq => simp only [evalM, evalRaw, htv]
    | mem => simp only [evalM, evalRaw, htv]
  | nrel r v =>
    intro e
    cases r with
    | eq => simp only [evalM, evalRaw, htv]
    | mem => simp only [evalM, evalRaw, htv]
  | and φ ψ ih1 ih2 => intro e; exact and_congr (ih1 e) (ih2 e)
  | or φ ψ ih1 ih2 => intro e; exact or_congr (ih1 e) (ih2 e)
  | all φ ih => intro e; exact forall_congr' fun d => ih (d :> e)
  | exs φ ih => intro e; exact exists_congr fun d => ih (d :> e)

end C14HaltsIffAbs

theorem OMA.solution : OMA.R_Constant14_c14_le_432_R1_H1_R1.H2 := by
  intro V mem P hV hTrans hL n _ M
  have hMV : ∀ ψ ∈ FFL.FirstOrder.SetTheory.ZermeloFraenkel,
      C14HaltsIffAbs.evalM mem Fin.elim0 Empty.elim ψ :=
    fun ψ hψ => (C14HaltsIffAbs.sat_iff_evalM mem ψ Fin.elim0).mp (hV ψ hψ)
  have hML : ∀ ψ ∈ FFL.FirstOrder.SetTheory.ZermeloFraenkel,
      C14HaltsIffAbs.evalM (fun a b : {x // P x} => mem a.1 b.1) Fin.elim0 Empty.elim ψ :=
    fun ψ hψ =>
      (C14HaltsIffAbs.sat_iff_evalM (fun a b : {x // P x} => mem a.1 b.1) ψ Fin.elim0).mp (hL ψ hψ)
  have hIff := C14HaltsIffAbs.halts_iff_abs ⟨V, mem, hMV⟩ P hTrans hML M
  generalize Constant14.halts M = σ at hIff ⊢
  exact (C14HaltsIffAbs.sat_iff_evalM mem σ Fin.elim0).trans
    (hIff.trans (C14HaltsIffAbs.sat_iff_evalM (fun a b : {x // P x} => mem a.1 b.1) σ Fin.elim0).symm)
