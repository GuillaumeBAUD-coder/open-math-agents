import OMAReductions.R_Constant14_c14_ge_4_R1
import Mathlib.Tactic
import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Proof of `Constant14.c14_ge_4.R1.H4`

We prove Gödel-Turing incompleteness for Busy Beaver machines in `𝗭𝗙𝗖`:
there exists a non-halting two-symbol Turing machine `M` such that `𝗭𝗙𝗖 ⊬ ∼Constant14.halts M`.

Architecture (pure computability / diagonalization, no Gödel numbering inside ZFC):
1. **Soundness in `ZFSet`:** Adapting the `ZFSet` evaluation layer of `Constant14.c14_ge_4.R1.H3`
   (by Pedro Bessa, PR #4646), we prove `M.IsHalting → stdEv ![] (Constant14.halts M)`.
   Combined with `OMA.R_Constant14_c14_ge_4_R1.sound_theory zfsetModel`, this yields
   `M.IsHalting → ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)`.
2. **Computable enumerability (`REPred`):** External proof certificates for `FFL.FirstOrder.Derivation`
   and `𝗭𝗙𝗖` axioms give `REPred` for `Provable 𝗭𝗙𝗖 (∼Constant14.halts M)`.
3. **Universal blank-tape reduction:** Fix one universal `Turing.ToPartrec.Code` via Mathlib
   (`PartrecToTM2 → TM2to1 → TM1to1 Bool → TM1to0 → BusyBeaver.Machine`), prepend a computable
   input-writing prefix for `Encodable.encode c`, and close via `ComputablePred.halting_problem_not_re 0`.
-/

namespace C14H4Proof

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver
open OMA.R_Constant14_c14_ge_4_R1
open scoped Classical

/- ## Section 1: Uniqueness of Tarski Truth Valuations on Closed Set-Theory Formulas -/

private noncomputable def stdTv {m : ℕ} (e : Fin m → ZFSet.{0})
    (t : Semiterm ℒₛₑₜ Empty m) : ZFSet.{0} :=
  exTv.choose e (Empty.elim : Empty → ZFSet.{0}) t

private def stdEv {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ m) : Prop :=
  exEv.choose e (Empty.elim : Empty → ZFSet.{0}) φ

private lemma stdEv_and {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ ⋏ ψ) ↔ stdEv e φ ∧ stdEv e ψ :=
  ev_and' e Empty.elim φ ψ

private lemma stdEv_or {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ ⋎ ψ) ↔ stdEv e φ ∨ stdEv e ψ :=
  ev_or' e Empty.elim φ ψ

private lemma stdEv_imp {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ 🡒 ψ) ↔ (stdEv e φ → stdEv e ψ) :=
  ev_imp' e Empty.elim φ ψ

private lemma stdEv_iff {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m) :
    stdEv e (φ 🡘 ψ) ↔ (stdEv e φ ↔ stdEv e ψ) :=
  ev_iff' e Empty.elim φ ψ

private lemma stdEv_all {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (∀¹ φ) ↔ ∀ d : ZFSet.{0}, stdEv (d :> e) φ :=
  ev_all' e Empty.elim φ

private lemma stdEv_exs {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (∃¹ φ) ↔ ∃ d : ZFSet.{0}, stdEv (d :> e) φ :=
  ev_exs' e Empty.elim φ

private lemma stdEv_eq {m : ℕ} (e : Fin m → ZFSet.{0}) (t₁ t₂ : Semiterm ℒₛₑₜ Empty m) :
    stdEv e (op(=).operator ![t₁, t₂]) ↔ stdTv e t₁ = stdTv e t₂ :=
  ev_eq' e Empty.elim t₁ t₂

private lemma stdEv_mem {m : ℕ} (e : Fin m → ZFSet.{0}) (t₁ t₂ : Semiterm ℒₛₑₜ Empty m) :
    stdEv e (Semiformula.Operator.Mem.mem.operator ![t₁, t₂]) ↔ stdTv e t₁ ∈ stdTv e t₂ :=
  ev_mem' e Empty.elim t₁ t₂

private lemma stdEv_ballMem {m : ℕ} (e : Fin m → ZFSet.{0}) (t : Semiterm ℒₛₑₜ Empty m)
    (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (Semiformula.ballMem t φ) ↔ ∀ d ∈ stdTv e t, stdEv (d :> e) φ :=
  ev_ballMem e Empty.elim t φ

private lemma stdEv_bexsMem {m : ℕ} (e : Fin m → ZFSet.{0}) (t : Semiterm ℒₛₑₜ Empty m)
    (φ : Semisentence ℒₛₑₜ (m + 1)) :
    stdEv e (Semiformula.bexsMem t φ) ↔ ∃ d ∈ stdTv e t, stdEv (d :> e) φ :=
  ev_bexsMem e Empty.elim t φ

private lemma stdTv_bvar {m : ℕ} (e : Fin m → ZFSet.{0}) (i : Fin m) :
    stdTv e (#i) = e i :=
  tval_bvar e Empty.elim i

private lemma stdEv_subst1 {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 1)
    (i₀ : Fin m) :
    stdEv e (φ ⇜ ![#i₀]) ↔ stdEv ![e i₀] φ := by
  unfold stdEv
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k; simp

private lemma stdEv_subst2 {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 2)
    (i₀ i₁ : Fin m) :
    stdEv e (φ ⇜ ![#i₀, #i₁]) ↔ stdEv ![e i₀, e i₁] φ := by
  unfold stdEv
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k <;> simp

private lemma stdEv_subst3 {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence 3)
    (i₀ i₁ i₂ : Fin m) :
    stdEv e (φ ⇜ ![#i₀, #i₁, #i₂]) ↔ stdEv ![e i₀, e i₁, e i₂] φ := by
  unfold stdEv
  rw [ev_subst']
  refine ev_congr φ ?_ rfl
  funext k; fin_cases k <;> simp


/- ## Section 2: `EvalTermAt` Combinators for Formula-as-Function Expressions -/

private def EvalTermAt {m : ℕ} (e : Fin m → ZFSet.{0}) (Ψ : SetTheorySemisentence (m + 1))
    (val : ZFSet.{0}) : Prop :=
  ∀ y : ZFSet.{0}, stdEv (y :> e) Ψ ↔ y = val

private def DefinesConst (Ψ : SetTheorySemisentence 1) (c : ZFSet.{0}) : Prop :=
  ∀ y : ZFSet.{0}, stdEv ![y] Ψ ↔ y = c

private lemma stdEv_e0 (e1 e2 : Fin 0 → ZFSet.{0}) (φ : SetTheorySemisentence 0) :
    stdEv e1 φ ↔ stdEv e2 φ := by
  rw [Subsingleton.elim e1 e2]

private lemma stdEv_e1 (y : ZFSet.{0}) (e : Fin 0 → ZFSet.{0}) (φ : SetTheorySemisentence 1) :
    stdEv (y :> e) φ ↔ stdEv ![y] φ := by
  rw [Subsingleton.elim e ![]]

private lemma et_bvar_succ {m : ℕ} (e : Fin m → ZFSet.{0}) (i : Fin m) :
    EvalTermAt e (op(=).operator (#0 :> #(i.succ) :> ![])) (e i) := by
  intro y
  unfold stdEv
  rw [ev_eq']
  simp [tval_bvar]

private lemma et_bvar1 {m : ℕ} (a : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> e) (op(=).operator (#0 :> #1 :> ![])) a :=
  et_bvar_succ (a :> e) 0

private lemma et_bvar2 {m : ℕ} (a b : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> e) (op(=).operator (#0 :> #2 :> ![])) b :=
  et_bvar_succ (a :> b :> e) 1

private lemma et_bvar3 {m : ℕ} (a b c : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> e) (op(=).operator (#0 :> #3 :> ![])) c :=
  et_bvar_succ (a :> b :> c :> e) 2

private lemma et_bvar4 {m : ℕ} (a b c d : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> d :> e) (op(=).operator (#0 :> #4 :> ![])) d :=
  et_bvar_succ (a :> b :> c :> d :> e) 3

private lemma et_bvar5 {m : ℕ} (a b c d f : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> d :> f :> e) (op(=).operator (#0 :> #5 :> ![])) f :=
  et_bvar_succ (a :> b :> c :> d :> f :> e) 4

private lemma et_bvar6 {m : ℕ} (a b c d f g : ZFSet.{0}) (e : Fin m → ZFSet.{0}) :
    EvalTermAt (a :> b :> c :> d :> f :> g :> e) (op(=).operator (#0 :> #6 :> ![])) g :=
  et_bvar_succ (a :> b :> c :> d :> f :> g :> e) 5

private lemma ev_nestFunc0_raw {m : ℕ} (φ : SetTheorySemisentence 1) (y : ZFSet.{0})
    (e : Fin m → ZFSet.{0}) :
    stdEv (y :> e) (Semiformula.nestFormulaeFunc φ ![]) ↔ stdEv ![y] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_imp', ev_top', ev_subst']
  simp only [true_imp_iff]
  refine ev_congr φ ?_ rfl
  funext i
  fin_cases i
  simp [Fin.addNat, tval_bvar]

private lemma et_const0 {m : ℕ} {Ψ : SetTheorySemisentence 1} {c : ZFSet.{0}}
    (hΨ : DefinesConst Ψ c) (e : Fin m → ZFSet.{0}) :
    EvalTermAt e (Semiformula.nestFormulaeFunc Ψ ![]) c := by
  intro y
  rw [ev_nestFunc0_raw]
  exact hΨ y

private lemma ev_nestFunc1_raw {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (y : ZFSet.{0}) :
    stdEv (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀]) ↔ stdEv ![y, v₀] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₀ : ZFSet.{0}, d₀ = v₀ → stdEv ![y, d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [ev_imp', ev_and', ev_top', and_true, ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin 1).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he1 : (fun k : Fin 2 =>
      exTv.choose (d₀ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 1) :> fun i : Fin 1 => #(i.addCast m.succ)) k)) =
      ![y, d₀] := by
    funext k
    fin_cases k <;> simp [Fin.addNat, Fin.addCast, tval_bvar]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma et_comp1 {m : ℕ} {φ : SetTheorySemisentence 2} {G : ZFSet.{0} → ZFSet.{0}}
    (hφ : ∀ y x₀, stdEv ![y, x₀] φ ↔ y = G x₀)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) :
    EvalTermAt e (Semiformula.nestFormulaeFunc φ ![Ψ₀]) (G v₀) := by
  intro y
  rw [ev_nestFunc1_raw φ h₀ y, hφ y v₀]

private lemma ev_nestFunc2_raw {m : ℕ} (φ : SetTheorySemisentence 3)
    {e : Fin m → ZFSet.{0}}
    {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (h₁ : EvalTermAt e Ψ₁ v₁) (y : ZFSet.{0}) :
    stdEv (y :> e) (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) ↔ stdEv ![y, v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulaeFunc, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₁ d₀ : ZFSet.{0}, (d₀ = v₀ ∧ d₁ = v₁) → stdEv ![y, d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [ev_all']
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ev_imp', ev_and', ev_and', ev_top', and_true, ev_subst', ev_subst', ev_subst']
  have he_psi0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he_psi1 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((1 : Fin 2).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he_phi : (fun k : Fin 3 =>
      exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim
        ((#((0 : Fin (m + 1)).addNat 2) :> fun i : Fin 2 => #(i.addCast m.succ)) k)) =
      ![y, d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m.succ) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · simp [Fin.addNat, tval_bvar]
    · simp [Fin.addCast, tval_bvar]
    · change exTv.choose (d₀ :> d₁ :> y :> e) Empty.elim (#((1 : Fin 2).addCast m.succ)) = d₁
      simp [h1, tval_bvar]
  rw [he_psi0, he_psi1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma et_comp2 {m : ℕ} {φ : SetTheorySemisentence 3}
    {G : ZFSet.{0} → ZFSet.{0} → ZFSet.{0}}
    (hφ : ∀ y x₀ x₁, stdEv ![y, x₀, x₁] φ ↔ y = G x₀ x₁)
    {e : Fin m → ZFSet.{0}} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (h₁ : EvalTermAt e Ψ₁ v₁) :
    EvalTermAt e (Semiformula.nestFormulaeFunc φ ![Ψ₀, Ψ₁]) (G v₀ v₁) := by
  intro y
  rw [ev_nestFunc2_raw φ h₀ h₁ y, hφ y v₀ v₁]

private lemma ev_nest1 {m : ℕ} (φ : SetTheorySemisentence 1)
    {e : Fin m → ZFSet.{0}} {Ψ₀ : SetTheorySemisentence (m + 1)} {v₀ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) :
    stdEv e (Semiformula.nestFormulae φ ![Ψ₀]) ↔ stdEv ![v₀] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₀ : ZFSet.{0}, d₀ = v₀ → stdEv ![d₀] φ).trans
    ⟨fun h => h v₀ rfl, fun h d₀ hd => hd ▸ h⟩
  refine forall_congr' fun d₀ => ?_
  rw [ev_imp', ev_and', ev_top', and_true, ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> e) Empty.elim
        ((#((0 : Fin 1).addCast m) :> fun j : Fin m => #(j.addNat 1)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he1 : (fun k : Fin 1 =>
      exTv.choose (d₀ :> e) Empty.elim (#(k.addCast m))) = ![d₀] := by
    funext k
    fin_cases k
    simp [Fin.addCast, tval_bvar]
  rw [he0, he1]
  exact imp_congr (h₀ d₀) Iff.rfl

private lemma ev_nest2 {m : ℕ} (φ : SetTheorySemisentence 2)
    {e : Fin m → ZFSet.{0}} {Ψ₀ Ψ₁ : SetTheorySemisentence (m + 1)} {v₀ v₁ : ZFSet.{0}}
    (h₀ : EvalTermAt e Ψ₀ v₀) (h₁ : EvalTermAt e Ψ₁ v₁) :
    stdEv e (Semiformula.nestFormulae φ ![Ψ₀, Ψ₁]) ↔ stdEv ![v₀, v₁] φ := by
  dsimp only [Semiformula.nestFormulae, FFL.FirstOrder.allItr, Matrix.conj, stdEv]
  rw [ev_all']
  refine (?_ : _ ↔ ∀ d₁ d₀ : ZFSet.{0}, (d₀ = v₀ ∧ d₁ = v₁) → stdEv ![d₀, d₁] φ).trans
    ⟨fun h => h v₁ v₀ ⟨rfl, rfl⟩, fun h d₁ d₀ ⟨hd0, hd1⟩ => by subst hd0 hd1; exact h⟩
  refine forall_congr' fun d₁ => ?_
  rw [ev_all']
  refine forall_congr' fun d₀ => ?_
  dsimp only [Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ev_imp', ev_and', ev_and', ev_top', and_true, ev_subst', ev_subst', ev_subst']
  have he0 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim
        ((#((0 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₀ :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Fin.addCast, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he1 : (fun k : Fin (m + 1) =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim
        ((#((1 : Fin 2).addCast m) :> fun j : Fin m => #(j.addNat 2)) k)) =
      (d₁ :> e) := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [h1, tval_bvar]
    · simp [Fin.addNat, tval_bvar]
  have he_phi : (fun k : Fin 2 =>
      exTv.choose (d₀ :> d₁ :> e) Empty.elim (#(k.addCast m))) = ![d₀, d₁] := by
    have h1 : ((1 : Fin 2).addCast m) = Fin.succ 0 := Fin.ext (by simp [Fin.addCast])
    funext k
    fin_cases k
    · simp [Fin.addCast, tval_bvar]
    · change exTv.choose (d₀ :> d₁ :> e) Empty.elim (#((1 : Fin 2).addCast m)) = d₁
      simp [h1, tval_bvar]
  rw [he0, he1, he_phi]
  exact imp_congr (and_congr (h₀ d₀) (h₁ d₁)) Iff.rfl

private lemma ev_faf_eq {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ = v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_eq'] at hv2
    simpa [tval_bvar] using hv2
  · intro heq d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_eq']
    simpa [tval_bvar] using heq

private lemma ev_faf_ne {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼op(=).operator (#1 :> #0 :> ![])))) ↔ v₁ ≠ v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_not', ev_eq'] at hv2
    simpa [tval_bvar] using hv2
  · intro hne d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_not', ev_eq']
    simpa [tval_bvar] using hne

private lemma ev_faf_mem {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      v₁ ∈ v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_mem'] at hv2
    simpa [tval_bvar] using hv2
  · intro hmem d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_mem']
    simpa [tval_bvar] using hmem

private lemma ev_faf_notMem {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {T₂ : SetTheorySemisentence (m + 2)}
    {v₁ v₂ : ZFSet.{0}} (h₁ : EvalTermAt e T₁ v₁) (h₂ : EvalTermAt (v₁ :> e) T₂ v₂) :
    stdEv e (∀¹ (T₁ 🡒 ∀¹ (T₂ 🡒 ∼Semiformula.Operator.Mem.mem.operator (#1 :> #0 :> ![])))) ↔
      v₁ ∉ v₂ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_all'] at hv1
    have hv2 := (ev_imp' _ _ _ _).mp (hv1 v₂) ((h₂ v₂).mpr rfl)
    rw [ev_not', ev_mem'] at hv2
    simpa [tval_bvar] using hv2
  · intro hnm d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_all']
    intro d₂
    rw [ev_imp']
    intro hd2
    have rfl2 : d₂ = v₂ := (h₂ d₂).mp hd2
    subst rfl2
    rw [ev_not', ev_mem']
    simpa [tval_bvar] using hnm

private lemma ev_faf_ball {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ZFSet.{0}}
    (h₁ : EvalTermAt e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    stdEv e (∀¹ (T₁ 🡒 Semiformula.ballMem (#0) φ)) ↔
      ∀ x ∈ v₁, stdEv (x :> v₁ :> e) φ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h x hx
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_ballMem, tval_bvar] at hv1
    exact hv1 x hx
  · intro h d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_ballMem, tval_bvar]
    exact h

private lemma ev_faf_bexs {m : ℕ} {e : Fin m → ZFSet.{0}}
    {T₁ : SetTheorySemisentence (m + 1)} {v₁ : ZFSet.{0}}
    (h₁ : EvalTermAt e T₁ v₁) (φ : SetTheorySemisentence (m + 2)) :
    stdEv e (∀¹ (T₁ 🡒 Semiformula.bexsMem (#0) φ)) ↔
      ∃ x ∈ v₁, stdEv (x :> v₁ :> e) φ := by
  unfold stdEv
  rw [ev_all']
  constructor
  · intro h
    have hv1 := (ev_imp' _ _ _ _).mp (h v₁) ((h₁ v₁).mpr rfl)
    rw [ev_bexsMem, tval_bvar] at hv1
    exact hv1
  · intro h d₁
    rw [ev_imp']
    intro hd1
    have rfl1 : d₁ = v₁ := (h₁ d₁).mp hd1
    subst rfl1
    rw [ev_bexsMem, tval_bvar]
    exact h

private lemma ev_existsUnique {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : SetTheorySemisentence (m + 1)) :
    stdEv e (∃¹! φ) ↔ ∃! y, stdEv (y :> e) φ := by
  unfold Semiformula.existsUnique stdEv ExistsUnique
  rw [ev_exs']
  refine exists_congr fun y => ?_
  rw [ev_and', ev_subst', ev_all']
  have he1 : (fun k : Fin (m + 1) =>
      exTv.choose (y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 1)) k)) = (y :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [tval_bvar]
    · simp [BinderNotation.finSuccItr, tval_bvar]
  rw [he1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [ev_imp', ev_subst', ev_eq']
  have he2 : (fun k : Fin (m + 1) =>
      exTv.choose (z :> y :> e) Empty.elim
        ((#0 :> fun x : Fin m => #(BinderNotation.finSuccItr x 2)) k)) = (z :> e) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [tval_bvar]
    · simp [BinderNotation.finSuccItr, tval_bvar]
  rw [he2]
  simp [tval_bvar]

/- ## Section 3: Von Neumann Ordinals, Pairs, Projections, Functions, and Encoded Integers -/

private def vnNat : ℕ → ZFSet.{0}
  | 0 => ∅
  | k + 1 => insert (vnNat k) (vnNat k)

private noncomputable def vnOmega : ZFSet.{0} := ZFSet.range vnNat

private lemma mem_vnNat_iff {x : ZFSet.{0}} {m : ℕ} :
    x ∈ vnNat m ↔ ∃ k < m, x = vnNat k := by
  induction m with
  | zero =>
    simp [vnNat]
  | succ m ih =>
    simp only [vnNat, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hlt, rfl⟩

private lemma vnNat_lt_mem {a b : ℕ} (h : a < b) : vnNat a ∈ vnNat b :=
  mem_vnNat_iff.mpr ⟨a, h, rfl⟩

private lemma vnNat_injective : Function.Injective vnNat := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm : vnNat a ∈ vnNat b := vnNat_lt_mem hlt
    rw [← hab] at hm
    exact False.elim (ZFSet.mem_irrefl _ hm)
  · rfl
  · have hm : vnNat b ∈ vnNat a := vnNat_lt_mem hgt
    rw [hab] at hm
    exact False.elim (ZFSet.mem_irrefl _ hm)

private lemma mem_vnOmega_iff_inductive (x : ZFSet.{0}) :
    x ∈ vnOmega ↔ ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I := by
  unfold vnOmega
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨k, rfl⟩ I ⟨h0, hsucc⟩
    induction k with
    | zero => exact h0
    | succ k ih => exact hsucc (vnNat k) ih
  · intro h
    apply ZFSet.mem_range.mp
    refine h (ZFSet.range vnNat) ⟨⟨0, rfl⟩ |> ZFSet.mem_range.mpr, ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
    exact ZFSet.mem_range.mpr ⟨k + 1, rfl⟩

/- Basic `SetTheory` definitions -/

private lemma ev_isEmpty (x : ZFSet.{0}) : stdEv ![x] SetTheory.isEmpty ↔ x = ∅ := by
  unfold SetTheory.isEmpty stdEv
  simp [ZFSet.eq_empty]

private lemma ev_isNonempty (x : ZFSet.{0}) : stdEv ![x] SetTheory.isNonempty ↔ x.Nonempty := by
  unfold SetTheory.isNonempty stdEv
  rw [ev_exs']
  refine exists_congr fun y => ?_
  rw [ev_mem']
  simp

private lemma ev_isSubsetOf (x y : ZFSet.{0}) : stdEv ![x, y] SetTheory.isSubsetOf ↔ x ⊆ y := by
  unfold SetTheory.isSubsetOf stdEv
  simp [ZFSet.subset_def]

private lemma ev_doubleton (p x y : ZFSet.{0}) :
    stdEv ![p, x, y] SetTheory.doubleton.dfn ↔ p = ({x, y} : ZFSet.{0}) := by
  unfold SetTheory.doubleton.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ p ↔ z = x ∨ z = y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_or, stdEv_eq, stdEv_eq]
    simp only [stdTv_bvar]
    rfl
  · constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    · rintro rfl z
      rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]

private lemma ev_singleton (p x : ZFSet.{0}) :
    stdEv ![p, x] SetTheory.singleton.dfn ↔ p = ({x} : ZFSet.{0}) := by
  unfold SetTheory.singleton.dfn
  exact (stdEv_subst3 _ _ _ _ _).trans
    ((ev_doubleton p x x).trans (by rw [ZFSet.pair_eq_singleton]))

private lemma ev_sUnion (u x : ZFSet.{0}) :
    stdEv ![u, x] SetTheory.sUnion.dfn ↔ u = ZFSet.sUnion x := by
  unfold SetTheory.sUnion.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ u ↔ ∃ y ∈ x, z ∈ y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_bexsMem]
    simp only [stdTv_bvar]
    exact iff_congr Iff.rfl (exists_congr fun y => and_congr_right fun _ => by
      rw [stdEv_mem]; simp only [stdTv_bvar]; rfl)
  · constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_sUnion]
    · rintro rfl z
      rw [ZFSet.mem_sUnion]

private lemma ev_union (u x y : ZFSet.{0}) :
    stdEv ![u, x, y] SetTheory.union.dfn ↔ u = x ∪ y := by
  unfold SetTheory.union.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ d : ZFSet.{0}, d = ({x, y} : ZFSet.{0}) → u = ZFSet.sUnion d).trans ?_
  · refine forall_congr' fun d => ?_
    rw [stdEv_imp]
    exact imp_congr
      ((stdEv_subst3 _ _ _ _ _).trans (ev_doubleton d x y))
      ((stdEv_subst2 _ _ _ _).trans (ev_sUnion u d))
  · rw [← ZFSet.sUnion_pair]
    exact ⟨fun h => h ({x, y} : ZFSet.{0}) rfl, fun h d hd => hd ▸ h⟩

private lemma ev_insert (u x y : ZFSet.{0}) :
    stdEv ![u, x, y] SetTheory.insert.dfn ↔ u = insert x y := by
  unfold SetTheory.insert.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ s : ZFSet.{0}, s = ({x} : ZFSet.{0}) → u = s ∪ y).trans ?_
  · refine forall_congr' fun s => ?_
    rw [stdEv_imp]
    exact imp_congr
      ((stdEv_subst2 _ _ _ _).trans (ev_singleton s x))
      ((stdEv_subst3 _ _ _ _ _).trans (ev_union u s y))
  · rw [ZFSet.insert_eq]
    exact ⟨fun h => h ({x} : ZFSet.{0}) rfl, fun h s hs => hs ▸ h⟩

private lemma ev_sInter (u x : ZFSet.{0}) :
    stdEv ![u, x] SetTheory.sInter.dfn ↔ u = ZFSet.sInter x := by
  unfold SetTheory.sInter.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ u ↔ x.Nonempty ∧ ∀ y ∈ x, z ∈ y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_and, stdEv_ballMem]
    simp only [stdTv_bvar]
    refine iff_congr Iff.rfl (and_congr ((stdEv_subst1 _ _ _).trans (ev_isNonempty x)) ?_)
    exact forall₂_congr fun y _ => by rw [stdEv_mem]; simp only [stdTv_bvar]; rfl
  · rcases ZFSet.eq_empty_or_nonempty x with rfl | hne
    · simp only [ZFSet.not_nonempty_empty, false_and, iff_false, ZFSet.sInter_empty, ZFSet.eq_empty]
    · constructor
      · intro h
        ext z
        rw [h z, ZFSet.mem_sInter hne]
        exact ⟨And.right, fun hall => ⟨hne, hall⟩⟩
      · rintro rfl z
        rw [ZFSet.mem_sInter hne]
        exact ⟨fun hall => ⟨hne, hall⟩, And.right⟩

private lemma ev_kpair (k x y : ZFSet.{0}) :
    stdEv ![k, x, y] SetTheory.kpair.dfn ↔ k = ZFSet.pair x y := by
  unfold SetTheory.kpair.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ x' : ZFSet.{0}, x' = ({x} : ZFSet.{0}) →
      ∀ z : ZFSet.{0}, z = ({x, y} : ZFSet.{0}) → k = ({x', z} : ZFSet.{0})).trans ?_
  · refine forall_congr' fun x' => ?_
    rw [stdEv_imp, stdEv_all]
    refine imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_singleton x' x)) (forall_congr' fun z => ?_)
    rw [stdEv_imp]
    exact imp_congr
      ((stdEv_subst3 _ _ _ _ _).trans (ev_doubleton z x y))
      ((stdEv_subst3 _ _ _ _ _).trans (ev_doubleton k x' z))
  · unfold ZFSet.pair
    exact ⟨fun h => h ({x} : ZFSet.{0}) rfl ({x, y} : ZFSet.{0}) rfl,
      fun h x' hx' z hz => by subst hx' hz; exact h⟩

private def pi1Val (w : ZFSet.{0}) : ZFSet.{0} := ZFSet.sUnion (ZFSet.sInter w)

private def pi2Val (w : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sUnion ((ZFSet.sUnion w).sep (fun z => z ∈ ZFSet.sInter w → ZFSet.sUnion w = ZFSet.sInter w))

private lemma sInter_kpair (a b : ZFSet.{0}) :
    ZFSet.sInter (ZFSet.pair a b) = ({a} : ZFSet.{0}) := by
  have hne : (ZFSet.pair a b).Nonempty := ⟨({a} : ZFSet.{0}), by simp [ZFSet.pair]⟩
  ext z
  rw [ZFSet.mem_sInter hne, ZFSet.mem_singleton]
  constructor
  · intro h
    exact ZFSet.mem_singleton.mp (h ({a} : ZFSet.{0}) (by simp [ZFSet.pair]))
  · intro hza y hy
    subst hza
    have hy' : y = ({z} : ZFSet.{0}) ∨ y = ({z, b} : ZFSet.{0}) := by
      simpa [ZFSet.pair] using hy
    rcases hy' with rfl | rfl <;> simp

private lemma sUnion_kpair (a b : ZFSet.{0}) :
    ZFSet.sUnion (ZFSet.pair a b) = ({a, b} : ZFSet.{0}) := by
  ext z
  simp only [ZFSet.pair, ZFSet.mem_sUnion, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
  constructor
  · rintro ⟨w, (rfl | rfl), hz⟩
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · simpa [ZFSet.mem_insert_iff, ZFSet.mem_singleton] using hz
  · rintro (hza | hzb)
    · subst hza
      exact ⟨({z} : ZFSet.{0}), Or.inl rfl, ZFSet.mem_singleton.mpr rfl⟩
    · subst hzb
      exact ⟨({a, z} : ZFSet.{0}), Or.inr rfl, by simp⟩

private lemma pi1Val_pair (a b : ZFSet.{0}) : pi1Val (ZFSet.pair a b) = a := by
  unfold pi1Val
  rw [sInter_kpair, ZFSet.sUnion_singleton]

private lemma pi2Val_pair (a b : ZFSet.{0}) : pi2Val (ZFSet.pair a b) = b := by
  unfold pi2Val
  rw [sUnion_kpair, sInter_kpair]
  by_cases hab : a = b
  · subst hab
    have hsep : ({a, a} : ZFSet.{0}).sep
        (fun z => z ∈ ({a} : ZFSet.{0}) → ({a, a} : ZFSet.{0}) = ({a} : ZFSet.{0})) =
        ({a} : ZFSet.{0}) := by
      ext z
      simp [ZFSet.pair_eq_singleton]
    rw [hsep, ZFSet.sUnion_singleton]
  · have hne_ui : ({a, b} : ZFSet.{0}) ≠ ({a} : ZFSet.{0}) := by
      intro heq
      have hb : b ∈ ({a} : ZFSet.{0}) := heq ▸ (by simp : b ∈ ({a, b} : ZFSet.{0}))
      exact hab (ZFSet.mem_singleton.mp hb).symm
    have hsep : ({a, b} : ZFSet.{0}).sep
        (fun z => z ∈ ({a} : ZFSet.{0}) → ({a, b} : ZFSet.{0}) = ({a} : ZFSet.{0})) =
        ({b} : ZFSet.{0}) := by
      ext z
      simp only [ZFSet.mem_sep, ZFSet.mem_insert_iff, ZFSet.mem_singleton, hne_ui, imp_false]
      exact ⟨fun ⟨h1, h2⟩ => h1.resolve_left h2,
        fun hz => ⟨Or.inr hz, fun hza => hab (hza.symm.trans hz)⟩⟩
    rw [hsep, ZFSet.sUnion_singleton]

private lemma ev_pi1 (p w : ZFSet.{0}) :
    stdEv ![p, w] SetTheory.kpair.π₁.dfn ↔ p = pi1Val w := by
  unfold SetTheory.kpair.π₁.dfn pi1Val
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ i : ZFSet.{0}, i = ZFSet.sInter w → p = ZFSet.sUnion i).trans
    ⟨fun h => h (ZFSet.sInter w) rfl, fun h i hi => hi ▸ h⟩
  refine forall_congr' fun i => ?_
  rw [stdEv_imp]
  exact imp_congr
    ((stdEv_subst2 _ _ _ _).trans (ev_sInter i w))
    ((stdEv_subst2 _ _ _ _).trans (ev_sUnion p i))

private lemma ev_pi2 (p w : ZFSet.{0}) :
    stdEv ![p, w] SetTheory.kpair.π₂.dfn ↔ p = pi2Val w := by
  unfold SetTheory.kpair.π₂.dfn pi2Val
  rw [stdEv_all]
  let u0 := ZFSet.sUnion w
  let i0 := ZFSet.sInter w
  let s0 := u0.sep (fun z => z ∈ i0 → u0 = i0)
  refine (?_ : _ ↔ ∀ u : ZFSet.{0}, u = u0 → ∀ i : ZFSet.{0}, i = i0 →
      ∀ s : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) →
        p = ZFSet.sUnion s).trans ?_
  · refine forall_congr' fun u => ?_
    rw [stdEv_imp, stdEv_all]
    refine imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_sUnion u w)) (forall_congr' fun i => ?_)
    rw [stdEv_imp, stdEv_all]
    refine imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_sInter i w)) (forall_congr' fun s => ?_)
    rw [stdEv_imp, stdEv_all]
    refine imp_congr (forall_congr' fun z => ?_) ((stdEv_subst2 _ _ _ _).trans (ev_sUnion p s))
    rw [stdEv_iff, stdEv_mem, stdEv_and, stdEv_mem, stdEv_imp, stdEv_mem, stdEv_eq]
    simp only [stdTv_bvar]
    rfl
  · constructor
    · intro h
      exact h u0 rfl i0 rfl s0 (fun z => ZFSet.mem_sep)
    · intro hp u hu i hi s hs
      subst hu hi
      have hseq : s = s0 := by
        ext z
        rw [hs z, ZFSet.mem_sep]
      rw [hseq, hp]

private lemma ev_prod (p X Y : ZFSet.{0}) :
    stdEv ![p, X, Y] SetTheory.prod.dfn ↔ p = ZFSet.prod X Y := by
  unfold SetTheory.prod.dfn
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ZFSet.pair x y).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_bexsMem]
    simp only [stdTv_bvar]
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ => ?_)
    rw [stdEv_bexsMem]
    simp only [stdTv_bvar]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    exact (stdEv_subst3 _ _ _ _ _).trans (ev_kpair z x y)
  · simp_rw [← ZFSet.mem_prod]
    exact ⟨fun h => ZFSet.ext h, fun h z => by rw [h]⟩

private lemma ev_succ (y x : ZFSet.{0}) :
    stdEv ![y, x] SetTheory.succ.dfn ↔ y = insert x x := by
  unfold SetTheory.succ.dfn SetTheory.isSucc
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0}, z ∈ y ↔ z = x ∨ z ∈ x).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_or, stdEv_eq, stdEv_mem]
    simp only [stdTv_bvar]
    rfl
  · constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_insert_iff]
    · rintro rfl z
      rw [ZFSet.mem_insert_iff]

private lemma ev_IsInductive (I : ZFSet.{0}) :
    stdEv ![I] SetTheory.IsInductive.dfn ↔ (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) := by
  unfold SetTheory.IsInductive.dfn
  rw [stdEv_and, stdEv_all, stdEv_ballMem]
  simp only [stdTv_bvar]
  refine and_congr ?_ ?_
  · refine (?_ : _ ↔ ∀ e : ZFSet.{0}, e = ∅ → e ∈ I).trans
      ⟨fun h => h ∅ rfl, fun h e he => he.symm ▸ h⟩
    refine forall_congr' fun e => ?_
    rw [stdEv_imp, stdEv_mem]
    simp only [stdTv_bvar]
    exact imp_congr ((stdEv_subst1 _ _ _).trans (ev_isEmpty e)) Iff.rfl
  · refine forall₂_congr fun y _ => ?_
    rw [stdEv_all]
    refine (?_ : _ ↔ ∀ y' : ZFSet.{0}, y' = insert y y → y' ∈ I).trans
      ⟨fun h => h (insert y y) rfl, fun h y' hy' => hy'.symm ▸ h⟩
    refine forall_congr' fun y' => ?_
    rw [stdEv_imp, stdEv_mem]
    simp only [stdTv_bvar]
    exact imp_congr ((stdEv_subst2 _ _ _ _).trans (ev_succ y' y)) Iff.rfl

private lemma dc_isω : DefinesConst SetTheory.isω vnOmega := by
  intro w
  unfold SetTheory.isω
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ x : ZFSet.{0},
      x ∈ w ↔ ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I).trans ?_
  · refine forall_congr' fun x => ?_
    rw [stdEv_iff, stdEv_mem, stdEv_all]
    simp only [stdTv_bvar]
    refine iff_congr Iff.rfl (forall_congr' fun I => ?_)
    rw [stdEv_imp, stdEv_mem]
    simp only [stdTv_bvar]
    exact imp_congr ((stdEv_subst1 _ _ _).trans (ev_IsInductive I)) Iff.rfl
  · simp_rw [← mem_vnOmega_iff_inductive]
    exact ⟨fun h => ZFSet.ext h, fun h x => by rw [h]⟩

/- `range.dfn`, `function.dfn`, `IsFunction.dfn`, `value.dfn` -/

private def relRange (R : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.sUnion (ZFSet.sUnion R)).sep (fun y => ∃ x, ZFSet.pair x y ∈ R)

private lemma mem_relRange {R y : ZFSet.{0}} :
    y ∈ relRange R ↔ ∃ x, ZFSet.pair x y ∈ R := by
  unfold relRange
  rw [ZFSet.mem_sep]
  refine ⟨And.right, fun ⟨x, hx⟩ => ⟨?_, x, hx⟩⟩
  rw [ZFSet.mem_sUnion]
  refine ⟨({x, y} : ZFSet.{0}), ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, hx, by simp [ZFSet.pair]⟩

private lemma ev_range (r R : ZFSet.{0}) :
    stdEv ![r, R] SetTheory.range.dfn ↔ r = relRange R := by
  unfold SetTheory.range.dfn
  change stdEv ![r, R] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ y : ZFSet.{0}, y ∈ r ↔ ∃ x, ZFSet.pair x y ∈ R).trans ?_
  · refine forall_congr' fun y => ?_
    rw [stdEv_iff]
    refine iff_congr ?_ ?_
    · exact ev_faf_mem (et_bvar1 y _) (et_bvar3 _ y r _)
    · rw [stdEv_exs]
      refine exists_congr fun x => ?_
      exact ev_faf_mem
        (et_comp2 ev_kpair (et_bvar1 x _) (et_bvar2 x y _))
        (et_bvar5 _ x y r R _)
  · simp_rw [← mem_relRange]
    exact ⟨fun h => ZFSet.ext h, fun h y => by rw [h]⟩

private lemma ev_function (F Y X : ZFSet.{0}) :
    stdEv ![F, Y, X] SetTheory.function.dfn ↔ F = ZFSet.funs X Y := by
  unfold SetTheory.function.dfn
  change stdEv ![F, Y, X] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ f : ZFSet.{0}, f ∈ F ↔ f ∈ ZFSet.funs X Y).trans
    ⟨fun h => ZFSet.ext h, fun h f => by rw [h]⟩
  refine forall_congr' fun f => ?_
  rw [stdEv_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 f _) (et_bvar3 _ f F _)) ?_
  rw [stdEv_and, ZFSet.mem_funs, ZFSet.IsFunc]
  refine and_congr ?_ ?_
  · rw [ev_nest2 SetTheory.isSubsetOf (et_bvar1 f _)
      (et_comp2 ev_prod (et_bvar4 f F Y X _) (et_bvar3 f F Y _)), ev_isSubsetOf]
  · rw [ev_faf_ball (et_bvar4 f F Y X _)]
    refine forall₂_congr fun x _ => ?_
    rw [ev_existsUnique]
    refine existsUnique_congr fun y => ?_
    exact ev_faf_mem
      (et_comp2 ev_kpair (et_bvar2 y x _) (et_bvar1 y _))
      (et_bvar5 _ y x _ f _)

private lemma ev_IsFunction (f : ZFSet.{0}) :
    stdEv ![f] SetTheory.IsFunction.dfn ↔ ∃ X Y : ZFSet.{0}, f ∈ ZFSet.funs X Y := by
  unfold SetTheory.IsFunction.dfn
  change stdEv ![f] (∃¹ ∃¹ _) ↔ _
  rw [stdEv_exs]
  refine exists_congr fun X => ?_
  rw [stdEv_exs]
  refine exists_congr fun Y => ?_
  exact ev_faf_mem (et_bvar3 Y X f _)
    (et_comp2 ev_function (et_bvar2 _ Y _) (et_bvar3 _ Y X _))

private def zfcApp (f x : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.sUnion (relRange f)).sep (fun z => ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f)

private lemma ev_value (v f x : ZFSet.{0}) :
    stdEv ![v, f, x] SetTheory.value.dfn ↔ v = zfcApp f x := by
  unfold SetTheory.value.dfn
  change stdEv ![v, f, x] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ z : ZFSet.{0},
      z ∈ v ↔ z ∈ ZFSet.sUnion (relRange f) ∧ ∃ y, z ∈ y ∧ ZFSet.pair x y ∈ f).trans ?_
  · refine forall_congr' fun z => ?_
    rw [stdEv_iff]
    refine iff_congr (ev_faf_mem (et_bvar1 z _) (et_bvar3 _ z v _)) ?_
    rw [stdEv_and]
    refine and_congr ?_ ?_
    · exact ev_faf_mem (et_bvar1 z _)
        (et_comp1 ev_sUnion (et_comp1 ev_range (et_bvar4 _ z v f _)))
    · rw [stdEv_exs]
      refine exists_congr fun y => ?_
      rw [stdEv_and]
      refine and_congr
        (ev_faf_mem (et_bvar2 y z _) (et_bvar2 _ y _))
        (ev_faf_mem (et_comp2 ev_kpair (et_bvar5 y z v f x _) (et_bvar1 y _))
          (et_bvar5 _ y z v f _))
  · unfold zfcApp
    constructor
    · intro h
      ext z
      rw [h z, ZFSet.mem_sep]
    · rintro rfl z
      rw [ZFSet.mem_sep]

private lemma zfcApp_of_mem_funs {X Y f x y : ZFSet.{0}}
    (hf : f ∈ ZFSet.funs X Y) (_hx : x ∈ X) (hpair : ZFSet.pair x y ∈ f) :
    zfcApp f x = y := by
  rw [ZFSet.mem_funs] at hf
  obtain ⟨_, huniq⟩ := hf
  obtain ⟨y0, hy0_mem, hy0_eq⟩ := huniq x _hx
  have hy_eq : y = y0 := hy0_eq y hpair
  subst hy_eq
  ext z
  unfold zfcApp
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y', hz', hp'⟩
    have rfl' : y' = y := hy0_eq y' hp'
    rwa [← rfl']
  · intro hz
    refine ⟨?_, y, hz, hy0_mem⟩
    rw [ZFSet.mem_sUnion]
    exact ⟨y, mem_relRange.mpr ⟨x, hy0_mem⟩, hz⟩

private lemma zfcApp_mem_codomain {X Y f x : ZFSet.{0}}
    (hf : f ∈ ZFSet.funs X Y) (hx : x ∈ X) :
    zfcApp f x ∈ Y := by
  have hf' := ZFSet.mem_funs.mp hf
  obtain ⟨y, hy, _⟩ := hf'.2 x hx
  rw [zfcApp_of_mem_funs hf hx hy]
  exact (ZFSet.pair_mem_prod.mp (hf'.1 hy)).2

private lemma funs_ext {X Y f1 f2 : ZFSet.{0}}
    (hf1 : f1 ∈ ZFSet.funs X Y) (hf2 : f2 ∈ ZFSet.funs X Y)
    (heq : ∀ x ∈ X, zfcApp f1 x = zfcApp f2 x) : f1 = f2 := by
  obtain ⟨hsub1, huniq1⟩ := ZFSet.mem_funs.mp hf1
  obtain ⟨hsub2, huniq2⟩ := ZFSet.mem_funs.mp hf2
  ext p
  constructor
  · intro hp1
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hsub1 hp1)
    have ha1 := zfcApp_of_mem_funs hf1 hx hp1
    obtain ⟨y2, hy2, _⟩ := huniq2 x hx
    have ha2 := zfcApp_of_mem_funs hf2 hx hy2
    have hy_eq : y = y2 := by rw [← ha1, heq x hx, ha2]
    rwa [hy_eq]
  · intro hp2
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hsub2 hp2)
    have ha2 := zfcApp_of_mem_funs hf2 hx hp2
    obtain ⟨y1, hy1, _⟩ := huniq1 x hx
    have ha1 := zfcApp_of_mem_funs hf1 hx hy1
    have hy_eq : y = y1 := by rw [← ha2, ← heq x hx, ha1]
    rwa [hy_eq]

/- `Constant14` numerals, finite sets, and encoded integers -/

private lemma dc_zero : DefinesConst Constant14.zero ∅ := by
  intro z
  unfold Constant14.zero
  exact (stdEv_subst1 _ _ _).trans (ev_isEmpty z)

private lemma dc_numeral (k : ℕ) : DefinesConst (Constant14.numeral k) (vnNat k) := by
  induction k with
  | zero => exact dc_zero
  | succ k ih =>
    intro y
    unfold Constant14.numeral vnNat
    exact et_comp1 ev_succ ih y

private lemma dc_setPair {Ψ₁ Ψ₂ : SetTheorySemisentence 1} {v₁ v₂ : ZFSet.{0}}
    (h₁ : DefinesConst Ψ₁ v₁) (h₂ : DefinesConst Ψ₂ v₂) :
    DefinesConst (Constant14.setPair Ψ₁ Ψ₂) (ZFSet.pair v₁ v₂) := by
  intro y
  unfold Constant14.setPair
  have h := et_comp2 ev_kpair (h₁ ·) (h₂ ·) y
  rwa [stdEv_e1] at h

private lemma dc_setTriple {Ψ₁ Ψ₂ Ψ₃ : SetTheorySemisentence 1} {v₁ v₂ v₃ : ZFSet.{0}}
    (h₁ : DefinesConst Ψ₁ v₁) (h₂ : DefinesConst Ψ₂ v₂) (h₃ : DefinesConst Ψ₃ v₃) :
    DefinesConst (Constant14.setTriple Ψ₁ Ψ₂ Ψ₃) (ZFSet.pair v₁ (ZFSet.pair v₂ v₃)) :=
  dc_setPair h₁ (dc_setPair h₂ h₃)

private def listToZFSet : List ZFSet.{0} → ZFSet.{0}
  | [] => ∅
  | x :: xs => insert x (listToZFSet xs)

private lemma mem_listToZFSet {z : ZFSet.{0}} {xs : List ZFSet.{0}} :
    z ∈ listToZFSet xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [listToZFSet]
  | cons x xs ih => simp [listToZFSet, ih]

private lemma dc_finiteSet_map {α : Type*} (l : List α)
    (fForm : α → SetTheorySemisentence 1) (fVal : α → ZFSet.{0})
    (hf : ∀ a, DefinesConst (fForm a) (fVal a)) :
    DefinesConst (Constant14.finiteSet (l.map fForm)) (listToZFSet (l.map fVal)) := by
  induction l with
  | nil => exact dc_zero
  | cons a as ih =>
    intro y
    simp only [List.map_cons, Constant14.finiteSet, listToZFSet]
    have h := et_comp2 ev_insert (hf a ·) (ih ·) y
    rwa [stdEv_e1] at h

private noncomputable def intSet : ZFSet.{0} := ZFSet.prod (vnNat 2) vnOmega

private lemma dc_integers : DefinesConst Constant14.integers intSet := by
  intro y
  unfold Constant14.integers intSet
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_prod (et_const0 (dc_numeral 2) _) (et_const0 dc_isω _))

private def encodeInt : ℤ → ZFSet.{0}
  | Int.ofNat k => ZFSet.pair (vnNat 0) (vnNat k)
  | Int.negSucc k => ZFSet.pair (vnNat 1) (vnNat k)

private lemma encodeInt_mem (z : ℤ) : encodeInt z ∈ intSet := by
  unfold intSet
  cases z with
  | ofNat k =>
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem (by decide : 0 < 2), ZFSet.mem_range.mpr ⟨k, rfl⟩⟩
  | negSucc k =>
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem (by decide : 1 < 2), ZFSet.mem_range.mpr ⟨k, rfl⟩⟩

private lemma mem_intSet_iff {w : ZFSet.{0}} :
    w ∈ intSet ↔ ∃ z : ℤ, w = encodeInt z := by
  refine ⟨?_, fun ⟨z, hz⟩ => hz ▸ encodeInt_mem z⟩
  unfold intSet vnOmega
  intro hw
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hw
  obtain ⟨s, hs, rfl⟩ := mem_vnNat_iff.mp ha
  obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hb
  interval_cases s
  · exact ⟨Int.ofNat k, rfl⟩
  · exact ⟨Int.negSucc k, rfl⟩

private lemma encodeInt_injective : Function.Injective encodeInt := by
  intro z1 z2 heq
  cases z1 <;> cases z2 <;> simp only [encodeInt, ZFSet.pair_inj] at heq
  · rw [vnNat_injective heq.2]
  · exfalso; exact absurd (vnNat_injective heq.1) (by decide)
  · exfalso; exact absurd (vnNat_injective heq.1) (by decide)
  · rw [vnNat_injective heq.2]

private lemma dc_integerZero : DefinesConst Constant14.integerZero (encodeInt 0) := by
  intro y
  unfold Constant14.integerZero
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _) (et_const0 (dc_numeral 0) _))

private lemma ev_integerSucc_encode (z : ℤ) (w' : ZFSet.{0}) :
    stdEv ![w', encodeInt z] Constant14.integerSucc.dfn ↔ w' = encodeInt (z + 1) := by
  unfold Constant14.integerSucc.dfn
  rw [stdEv_or, stdEv_and, stdEv_and]
  rw [ev_faf_mem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _),
      ev_faf_notMem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _)]
  simp only [encodeInt_mem z, not_true_eq_false, false_and, or_false, true_and]
  refine (?_ : _ ↔
      ((pi1Val (encodeInt z) = vnNat 0 ∧
          w' = ZFSet.pair (vnNat 0) (insert (pi2Val (encodeInt z)) (pi2Val (encodeInt z)))) ∨
        (pi1Val (encodeInt z) = vnNat 1 ∧
          ((pi2Val (encodeInt z) = vnNat 0 ∧ w' = encodeInt 0) ∨
            ∃ m ∈ vnOmega, pi2Val (encodeInt z) = insert m m ∧
              w' = ZFSet.pair (vnNat 1) m)))).trans ?_
  · rw [stdEv_or, stdEv_and, stdEv_and, stdEv_or, stdEv_and]
    refine or_congr
      (and_congr
        (ev_faf_eq (et_comp1 ev_pi1 (et_bvar2 w' (encodeInt z) _)) (et_const0 (dc_numeral 0) _))
        (ev_faf_eq (et_bvar1 w' _)
          (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _)
            (et_comp1 ev_succ (et_comp1 ev_pi2 (et_bvar3 _ w' (encodeInt z) _))))))
      (and_congr
        (ev_faf_eq (et_comp1 ev_pi1 (et_bvar2 w' (encodeInt z) _)) (et_const0 (dc_numeral 1) _))
        (or_congr
          (and_congr
            (ev_faf_eq (et_comp1 ev_pi2 (et_bvar2 w' (encodeInt z) _)) (et_const0 (dc_numeral 0) _))
            (ev_faf_eq (et_bvar1 w' _) (et_const0 dc_integerZero _)))
          ?_))
    rw [ev_faf_bexs (et_const0 dc_isω _)]
    refine exists_congr fun m => and_congr_right fun _ => ?_
    rw [stdEv_and]
    exact and_congr
      (ev_faf_eq (et_comp1 ev_pi2 (et_bvar4 m vnOmega w' (encodeInt z) _))
        (et_comp1 ev_succ (et_bvar2 _ m _)))
      (ev_faf_eq (et_bvar3 m vnOmega w' _)
        (et_comp2 ev_kpair (et_const0 (dc_numeral 1) _) (et_bvar2 _ m _)))
  · have h01 : vnNat 0 ≠ vnNat 1 := fun h => absurd (vnNat_injective h) (by decide)
    have h10 : vnNat 1 ≠ vnNat 0 := h01.symm
    cases z with
    | ofNat k =>
      simp only [encodeInt, pi1Val_pair, pi2Val_pair, h01, false_and, or_false, true_and]
      rfl
    | negSucc k =>
      simp only [encodeInt, pi1Val_pair, pi2Val_pair, h10, false_and, false_or, true_and]
      cases k with
      | zero =>
        have hno_pred : ¬ ∃ m ∈ vnOmega, vnNat 0 = insert m m ∧ w' = ZFSet.pair (vnNat 1) m := by
          rintro ⟨m, _, hm, _⟩
          have : m ∈ vnNat 0 := hm ▸ ZFSet.mem_insert m m
          exact ZFSet.notMem_empty m this
        simp only [true_and, hno_pred, or_false]
        rfl
      | succ k =>
        have hne0 : vnNat (k + 1) ≠ vnNat 0 := fun h => absurd (vnNat_injective h) (by omega)
        simp only [hne0, false_and, false_or]
        constructor
        · rintro ⟨m, hm, hsucc, rfl⟩
          obtain ⟨r, rfl⟩ := ZFSet.mem_range.mp hm
          have hr : k + 1 = r + 1 := vnNat_injective hsucc
          have hk : r = k := by omega
          subst hk
          rfl
        · rintro rfl
          exact ⟨vnNat k, ZFSet.mem_range.mpr ⟨k, rfl⟩, rfl, rfl⟩

private lemma ev_integerPred_encode (z : ℤ) (w' : ZFSet.{0}) :
    stdEv ![w', encodeInt z] Constant14.integerPred.dfn ↔ w' = encodeInt (z - 1) := by
  unfold Constant14.integerPred.dfn
  rw [stdEv_or, stdEv_and, stdEv_and, stdEv_and]
  rw [ev_faf_mem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _),
      ev_faf_mem (et_bvar1 w' _) (et_const0 dc_integers _),
      ev_nest2 Constant14.integerSucc.dfn (et_bvar2 w' (encodeInt z) _) (et_bvar1 w' _),
      ev_faf_notMem (et_bvar2 w' (encodeInt z) _) (et_const0 dc_integers _)]
  simp only [encodeInt_mem z, not_true_eq_false, false_and, or_false, true_and]
  constructor
  · rintro ⟨hw', hsucc⟩
    obtain ⟨u, rfl⟩ := mem_intSet_iff.mp hw'
    rw [ev_integerSucc_encode u (encodeInt z)] at hsucc
    have hzu : z = u + 1 := encodeInt_injective hsucc
    have hu : u = z - 1 := by omega
    rw [hu]
  · rintro rfl
    refine ⟨encodeInt_mem (z - 1), ?_⟩
    rw [ev_integerSucc_encode (z - 1) (encodeInt z)]
    congr 1
    omega

/- ## Section 4: Instruction Table, Configurations, `nextStep`, `orbit`, and `halts` -/

private noncomputable def cfgSetVal (N : ℕ) : ZFSet.{0} :=
  ZFSet.prod (vnNat N) (ZFSet.prod intSet (ZFSet.funs intSet (vnNat 2)))

private lemma dc_configSet (N : ℕ) : DefinesConst (Constant14.configSet N) (cfgSetVal N) := by
  intro y
  unfold Constant14.configSet cfgSetVal
  exact ev_faf_eq (et_bvar1 y _)
    (et_comp2 ev_prod (et_const0 (dc_numeral N) _)
      (et_comp2 ev_prod (et_const0 dc_integers _)
        (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _))))

private lemma mem_cfgSetVal_iff {N : ℕ} {z : ZFSet.{0}} :
    z ∈ cfgSetVal N ↔
      ∃ (qCode : ℕ) (pos : ℤ) (g : ZFSet.{0}),
        qCode < N ∧ g ∈ ZFSet.funs intSet (vnNat 2) ∧
          z = ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g) := by
  unfold cfgSetVal
  constructor
  · intro hz
    obtain ⟨s, hs, p, hp, rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨qCode, hq, rfl⟩ := mem_vnNat_iff.mp hs
    obtain ⟨w, hw, g, hg, rfl⟩ := ZFSet.mem_prod.mp hp
    obtain ⟨pos, rfl⟩ := mem_intSet_iff.mp hw
    exact ⟨qCode, pos, g, hq, hg, rfl⟩
  · rintro ⟨qCode, pos, g, hq, hg, rfl⟩
    exact ZFSet.pair_mem_prod.mpr
      ⟨vnNat_lt_mem hq, ZFSet.pair_mem_prod.mpr ⟨encodeInt_mem pos, hg⟩⟩

private def entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) : SetTheorySemisentence 1 :=
  Constant14.transitionEntry t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

private def entryVal (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ZFSet.{0} :=
  ZFSet.pair (ZFSet.pair (vnNat t.1) (vnNat t.2.1))
    (ZFSet.pair (vnNat t.2.2.1) (ZFSet.pair (vnNat t.2.2.2.1) (vnNat t.2.2.2.2)))

private lemma dc_entryForm (t : ℕ × ℕ × ℕ × ℕ × ℕ) :
    DefinesConst (entryForm t) (entryVal t) := by
  unfold entryForm Constant14.transitionEntry entryVal
  exact dc_setPair (dc_setPair (dc_numeral _) (dc_numeral _))
    (dc_setTriple (dc_numeral _) (dc_numeral _) (dc_numeral _))

private def transTuples {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.ofFn fun q : Fin n =>
    List.ofFn fun sym : Fin 2 =>
      let o := Constant14.transitionCode M q sym
      (q.val, sym.val, o.1, o.2.1, o.2.2)).flatten ++
  List.ofFn fun sym : Fin 2 =>
    (n, sym.val, n, sym.val, Constant14.directionCode none)

private def instrTableVal {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ZFSet.{0} :=
  listToZFSet ((transTuples M).map entryVal)

private lemma dc_instructionTable {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst (Constant14.instructionTable M) (instrTableVal M) := by
  unfold Constant14.instructionTable instrTableVal
  have hmap : (transTuples M).map entryForm = Constant14.transitionEntries M := by
    simp [transTuples, Constant14.transitionEntries, entryForm, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  rw [← hmap]
  exact dc_finiteSet_map (transTuples M) entryForm entryVal dc_entryForm

private def transLookup {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode symCode : ℕ) : ℕ × ℕ × ℕ :=
  if hq : qCode < n then
    if hs : symCode < 2 then
      Constant14.transitionCode M ⟨qCode, hq⟩ ⟨symCode, hs⟩
    else (n, 0, 1)
  else (n, symCode, 1)

private lemma transitionCode_bounds {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
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

private lemma instrTableVal_funs_and_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    instrTableVal M ∈ ZFSet.funs
        (ZFSet.prod (vnNat (n + 1)) (vnNat 2))
        (ZFSet.prod (vnNat (n + 1)) (ZFSet.prod (vnNat 2) (vnNat 3))) ∧
      ∀ (qCode symCode : ℕ), qCode < n + 1 → symCode < 2 →
        zfcApp (instrTableVal M) (ZFSet.pair (vnNat qCode) (vnNat symCode)) =
          let o := transLookup M qCode symCode
          ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2)) := by
  have hmem_iff : ∀ p : ZFSet.{0}, p ∈ instrTableVal M ↔
      (∃ (q : Fin n) (sym : Fin 2),
        let o := Constant14.transitionCode M q sym
        p = entryVal (q.val, sym.val, o.1, o.2.1, o.2.2)) ∨
      (∃ sym : Fin 2, p = entryVal (n, sym.val, n, sym.val, 1)) := by
    intro p
    unfold instrTableVal
    rw [mem_listToZFSet, List.mem_map]
    simp only [transTuples, List.mem_append, List.mem_flatten, List.mem_ofFn,
      Constant14.directionCode]
    constructor
    · rintro ⟨t, (⟨l, ⟨q, rfl⟩, ht⟩ | ⟨sym, rfl⟩), rfl⟩
      · obtain ⟨sym, rfl⟩ := List.mem_ofFn.mp ht
        exact Or.inl ⟨q, sym, rfl⟩
      · exact Or.inr ⟨sym, rfl⟩
    · rintro (⟨q, sym, rfl⟩ | ⟨sym, rfl⟩)
      · refine ⟨_, Or.inl ⟨_, ⟨q, rfl⟩, List.mem_ofFn.mpr ⟨sym, rfl⟩⟩, rfl⟩
      · exact ⟨_, Or.inr ⟨sym, rfl⟩, rfl⟩
  have hfuns : instrTableVal M ∈ ZFSet.funs
      (ZFSet.prod (vnNat (n + 1)) (vnNat 2))
      (ZFSet.prod (vnNat (n + 1)) (ZFSet.prod (vnNat 2) (vnNat 3))) := by
    rw [ZFSet.mem_funs, ZFSet.IsFunc]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases (hmem_iff p).mp hp with ⟨q, sym, rfl⟩ | ⟨sym, rfl⟩
      · obtain ⟨hb1, hb2, hb3⟩ := transitionCode_bounds M q sym
        exact ZFSet.pair_mem_prod.mpr
          ⟨ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_of_lt q.isLt), vnNat_lt_mem sym.isLt⟩,
           ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hb1,
             ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hb2, vnNat_lt_mem hb3⟩⟩⟩
      · exact ZFSet.pair_mem_prod.mpr
          ⟨ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_self n), vnNat_lt_mem sym.isLt⟩,
           ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem (Nat.lt_succ_self n),
             ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem sym.isLt, vnNat_lt_mem (by decide : 1 < 3)⟩⟩⟩
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hx
      obtain ⟨qCode, hq, rfl⟩ := mem_vnNat_iff.mp ha
      obtain ⟨symCode, hs, rfl⟩ := mem_vnNat_iff.mp hb
      let o := transLookup M qCode symCode
      refine ⟨ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2)), ?_, ?_⟩
      · dsimp only
        rw [hmem_iff]
        by_cases hqn : qCode < n
        · left
          refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
          dsimp only [o, transLookup]; rw [dif_pos hqn, dif_pos hs]; rfl
        · have hqe : qCode = n := by omega
          subst qCode
          right
          refine ⟨⟨symCode, hs⟩, ?_⟩
          dsimp only [o, transLookup]; rw [dif_neg (Nat.lt_irrefl n)]; rfl
      · intro y hy
        rcases (hmem_iff _).mp hy with ⟨q, sym, heq⟩ | ⟨sym, heq⟩
        · obtain ⟨h1, rfl⟩ := ZFSet.pair_injective heq
          obtain ⟨hq1, hs1⟩ := ZFSet.pair_injective h1
          have hqc : qCode = q.val := vnNat_injective hq1
          have hsc : symCode = sym.val := vnNat_injective hs1
          subst qCode symCode
          dsimp only [o, transLookup]
          rw [dif_pos q.isLt, dif_pos sym.isLt]
        · obtain ⟨h1, rfl⟩ := ZFSet.pair_injective heq
          obtain ⟨hq1, hs1⟩ := ZFSet.pair_injective h1
          have hqc : qCode = n := vnNat_injective hq1
          have hsc : symCode = sym.val := vnNat_injective hs1
          subst qCode symCode
          dsimp only [o, transLookup]
          rw [dif_neg (Nat.lt_irrefl n)]
  refine ⟨hfuns, fun qCode symCode hq hs => ?_⟩
  have hx : ZFSet.pair (vnNat qCode) (vnNat symCode) ∈ ZFSet.prod (vnNat (n + 1)) (vnNat 2) :=
    ZFSet.pair_mem_prod.mpr ⟨vnNat_lt_mem hq, vnNat_lt_mem hs⟩
  let o := transLookup M qCode symCode
  have hmem_pair : ZFSet.pair (ZFSet.pair (vnNat qCode) (vnNat symCode))
      (ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2))) ∈ instrTableVal M := by
    rw [hmem_iff]
    by_cases hqn : qCode < n
    · left; refine ⟨⟨qCode, hqn⟩, ⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]; rw [dif_pos hqn, dif_pos hs]; rfl
    · have hqe : qCode = n := by omega
      subst qCode
      right; refine ⟨⟨symCode, hs⟩, ?_⟩
      dsimp only [o, transLookup]; rw [dif_neg (Nat.lt_irrefl n)]; rfl
  exact zfcApp_of_mem_funs hfuns hx hmem_pair

/- ZFC-level one-step configuration function `zfcStepFn` -/

private noncomputable def zfcUpdateTape (g posSet valSet : ZFSet.{0}) : ZFSet.{0} :=
  letI : ZFSet.Definable₁ (fun w => if w = posSet then valSet else zfcApp g w) :=
    Classical.allZFSetDefinable _
  ZFSet.map (fun w => if w = posSet then valSet else zfcApp g w) intSet

private lemma zfcUpdateTape_mem_funs {g posSet valSet : ZFSet.{0}}
    (hg : g ∈ ZFSet.funs intSet (vnNat 2)) (hval : valSet ∈ vnNat 2) :
    zfcUpdateTape g posSet valSet ∈ ZFSet.funs intSet (vnNat 2) := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => if w = posSet then valSet else zfcApp g w
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  change ZFSet.map fn intSet ∈ ZFSet.funs intSet (vnNat 2)
  rw [ZFSet.mem_funs, ZFSet.map_isFunc]
  intro w hw
  dsimp [fn]
  split_ifs
  · exact hval
  · exact zfcApp_mem_codomain hg hw

private lemma zfcUpdateTape_app {g posSet valSet w : ZFSet.{0}}
    (hg : g ∈ ZFSet.funs intSet (vnNat 2)) (hval : valSet ∈ vnNat 2) (hw : w ∈ intSet) :
    zfcApp (zfcUpdateTape g posSet valSet) w =
      if w = posSet then valSet else zfcApp g w := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun u => if u = posSet then valSet else zfcApp g u
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  have hfuns : zfcUpdateTape g posSet valSet ∈ ZFSet.funs intSet (vnNat 2) :=
    zfcUpdateTape_mem_funs hg hval
  have hmem : ZFSet.pair w (fn w) ∈ zfcUpdateTape g posSet valSet := by
    change ZFSet.pair w (fn w) ∈ ZFSet.map fn intSet
    exact ZFSet.mem_map.mpr ⟨w, hw, rfl⟩
  exact zfcApp_of_mem_funs hfuns hw hmem

private noncomputable def decodePos (w : ZFSet.{0}) : ℤ :=
  if hw : w ∈ intSet then Classical.choose (mem_intSet_iff.mp hw) else 0

private lemma decodePos_encodeInt (p : ℤ) : decodePos (encodeInt p) = p := by
  unfold decodePos
  rw [dif_pos (encodeInt_mem p)]
  exact encodeInt_injective (Classical.choose_spec (mem_intSet_iff.mp (encodeInt_mem p))).symm

private noncomputable def zfcStepFn {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (z : ZFSet.{0}) : ZFSet.{0} :=
  if z ∈ cfgSetVal (n + 1) then
    let qSet := pi1Val z
    let posSet := pi1Val (pi2Val z)
    let g := pi2Val (pi2Val z)
    let symSet := zfcApp g posSet
    let t := zfcApp (instrTableVal M) (ZFSet.pair qSet symSet)
    let qNext := pi1Val t
    let wrSet := pi1Val (pi2Val t)
    let dirSet := pi2Val (pi2Val t)
    let posVal := decodePos posSet
    let posNext : ZFSet.{0} :=
      if dirSet = vnNat 0 then encodeInt (posVal - 1)
      else if dirSet = vnNat 1 then encodeInt posVal
      else encodeInt (posVal + 1)
    let gNext := zfcUpdateTape g posSet wrSet
    ZFSet.pair qNext (ZFSet.pair posNext gNext)
  else ∅

private lemma zfcStepFn_of_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (qCode : ℕ) (pos : ℤ) (g : ZFSet.{0})
    (hq : qCode < n + 1) (hg : g ∈ ZFSet.funs intSet (vnNat 2))
    (symCode : ℕ) (hs : symCode < 2) (hsym : zfcApp g (encodeInt pos) = vnNat symCode) :
    let o := transLookup M qCode symCode
    let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
    zfcStepFn M (ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g)) =
      ZFSet.pair (vnNat o.1)
        (ZFSet.pair (encodeInt pos') (zfcUpdateTape g (encodeInt pos) (vnNat o.2.1))) := by
  let z := ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g)
  have hz : z ∈ cfgSetVal (n + 1) := mem_cfgSetVal_iff.mpr ⟨qCode, pos, g, hq, hg, rfl⟩
  unfold zfcStepFn
  rw [if_pos hz]
  dsimp only
  have hp1 : pi1Val z = vnNat qCode := pi1Val_pair _ _
  have hp2 : pi2Val z = ZFSet.pair (encodeInt pos) g := pi2Val_pair _ _
  have hpos : pi1Val (pi2Val z) = encodeInt pos := by rw [hp2, pi1Val_pair]
  have hgv : pi2Val (pi2Val z) = g := by rw [hp2, pi2Val_pair]
  obtain ⟨_, happ⟩ := instrTableVal_funs_and_app M
  let o := transLookup M qCode symCode
  have ht : zfcApp (instrTableVal M)
      (ZFSet.pair (pi1Val z) (zfcApp (pi2Val (pi2Val z)) (pi1Val (pi2Val z)))) =
      ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2)) := by
    rw [hp1, hgv, hpos, hsym]
    exact happ qCode symCode hq hs
  rw [ht, pi1Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, hpos, hgv, decodePos_encodeInt]
  congr 1; congr 1
  have hd0 : (vnNat o.2.2 = vnNat 0) ↔ (o.2.2 = 0) := vnNat_injective.eq_iff
  have hd1 : (vnNat o.2.2 = vnNat 1) ↔ (o.2.2 = 1) := vnNat_injective.eq_iff
  simp only [hd0, hd1]
  dsimp only [o]
  split_ifs <;> rfl

private lemma zfcStepFn_mem_cfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    {z : ZFSet.{0}} (hz : z ∈ cfgSetVal (n + 1)) :
    zfcStepFn M z ∈ cfgSetVal (n + 1) := by
  obtain ⟨qCode, pos, g, hq, hg, rfl⟩ := mem_cfgSetVal_iff.mp hz
  have hsym_mem : zfcApp g (encodeInt pos) ∈ vnNat 2 :=
    zfcApp_mem_codomain hg (encodeInt_mem pos)
  obtain ⟨symCode, hs, hsym⟩ := mem_vnNat_iff.mp hsym_mem
  rw [zfcStepFn_of_cfg M qCode pos g hq hg symCode hs hsym]
  let o := transLookup M qCode symCode
  have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
    dsimp only [o, transLookup]
    by_cases hqn : qCode < n
    · rw [dif_pos hqn, dif_pos hs]
      exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
    · rw [dif_neg hqn]
      dsimp only
      exact ⟨Nat.lt_succ_self n, hs, by decide⟩
  exact mem_cfgSetVal_iff.mpr
    ⟨o.1, if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1,
     zfcUpdateTape g (encodeInt pos) (vnNat o.2.1),
     hob.1, zfcUpdateTape_mem_funs hg (vnNat_lt_mem hob.2.1), rfl⟩

private lemma ev_nextConfig_iff {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (z' z : ZFSet.{0}) :
    stdEv ![z', z] (Constant14.nextConfig (n + 1) (Constant14.instructionTable M)) ↔
      z ∈ cfgSetVal (n + 1) ∧ z' = zfcStepFn M z := by
  unfold Constant14.nextConfig
  rw [stdEv_and, stdEv_and]
  rw [ev_faf_mem (et_bvar2 z' z _) (et_const0 (dc_configSet (n + 1)) _),
      ev_faf_mem (et_bvar1 z' _) (et_const0 (dc_configSet (n + 1)) _)]
  by_cases hz : z ∈ cfgSetVal (n + 1)
  · simp only [hz, true_and]
    obtain ⟨qCode, pos, g, hq, hg, rfl⟩ := mem_cfgSetVal_iff.mp hz
    let z0 := ZFSet.pair (vnNat qCode) (ZFSet.pair (encodeInt pos) g)
    have hsym_mem : zfcApp g (encodeInt pos) ∈ vnNat 2 :=
      zfcApp_mem_codomain hg (encodeInt_mem pos)
    obtain ⟨symCode, hs, hsym⟩ := mem_vnNat_iff.mp hsym_mem
    let o := transLookup M qCode symCode
    have hob : o.1 < n + 1 ∧ o.2.1 < 2 ∧ o.2.2 < 3 := by
      dsimp only [o, transLookup]
      by_cases hqn : qCode < n
      · rw [dif_pos hqn, dif_pos hs]
        exact transitionCode_bounds M ⟨qCode, hqn⟩ ⟨symCode, hs⟩
      · rw [dif_neg hqn]
        dsimp only
        exact ⟨Nat.lt_succ_self n, hs, by decide⟩
    let tVal := ZFSet.pair (vnNat o.1) (ZFSet.pair (vnNat o.2.1) (vnNat o.2.2))
    let pos' : ℤ := if o.2.2 = 0 then pos - 1 else if o.2.2 = 1 then pos else pos + 1
    have hstep_val := zfcStepFn_of_cfg M qCode pos g hq hg symCode hs hsym
    change zfcStepFn M z0 = ZFSet.pair (vnNat o.1)
      (ZFSet.pair (encodeInt pos') (zfcUpdateTape g (encodeInt pos) (vnNat o.2.1))) at hstep_val
    obtain ⟨_, happ⟩ := instrTableVal_funs_and_app M
    have htVal_eq : zfcApp (instrTableVal M)
        (ZFSet.pair (pi1Val z0) (zfcApp (pi2Val (pi2Val z0)) (pi1Val (pi2Val z0)))) = tVal := by
      dsimp [z0, tVal]
      rw [pi1Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, hsym]
      exact happ qCode symCode hq hs
    rw [stdEv_exs]
    refine (and_congr Iff.rfl (exists_congr fun t => (?_ : _ ↔
        (t = tVal ∧
         pi1Val z' = pi1Val t ∧
         ((pi2Val (pi2Val t) = vnNat 0 ∧
             stdEv ![pi1Val (pi2Val z'), pi1Val (pi2Val z0)] Constant14.integerPred.dfn) ∨
           (pi2Val (pi2Val t) = vnNat 1 ∧ pi1Val (pi2Val z') = pi1Val (pi2Val z0)) ∨
           (pi2Val (pi2Val t) = vnNat 2 ∧
             stdEv ![pi1Val (pi2Val z'), pi1Val (pi2Val z0)] Constant14.integerSucc.dfn)) ∧
         zfcApp (pi2Val (pi2Val z')) (pi1Val (pi2Val z0)) = pi1Val (pi2Val t) ∧
         ∀ k ∈ intSet, k ≠ pi1Val (pi2Val z0) →
           zfcApp (pi2Val (pi2Val z')) k = zfcApp (pi2Val (pi2Val z0)) k)))).trans ?_
    · rw [stdEv_and, stdEv_and, stdEv_and, stdEv_and]
      refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
      · rw [ev_faf_eq (et_bvar1 t _)
          (et_comp2 ev_value (et_const0 (dc_instructionTable M) _)
            (et_comp2 ev_kpair
              (et_comp1 ev_pi1 (et_bvar4 _ t z' z0 _))
              (et_comp2 ev_value
                (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))))),
          htVal_eq]
      · exact ev_faf_eq
          (et_comp1 ev_pi1 (et_bvar2 t z' _))
          (et_comp1 ev_pi1 (et_bvar2 _ t _))
      · rw [stdEv_or, stdEv_or, stdEv_and, stdEv_and, stdEv_and]
        refine or_congr
          (and_congr
            (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
              (et_const0 (dc_numeral 0) _))
            (ev_nest2 Constant14.integerPred.dfn
              (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
              (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _)))))
          (or_congr
            (and_congr
              (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
                (et_const0 (dc_numeral 1) _))
              (ev_faf_eq
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar4 _ t z' z0 _)))))
            (and_congr
              (ev_faf_eq (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar1 t _)))
                (et_const0 (dc_numeral 2) _))
              (ev_nest2 Constant14.integerSucc.dfn
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
                (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _))))))
      · exact ev_faf_eq
          (et_comp2 ev_value
            (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar2 t z' _)))
            (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar3 t z' z0 _))))
          (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar2 _ t _)))
      · rw [ev_faf_ball (et_const0 dc_integers _)]
        refine forall₂_congr fun k _ => ?_
        rw [stdEv_imp]
        exact imp_congr
          (ev_faf_ne (et_bvar1 k _)
            (et_comp1 ev_pi1 (et_comp1 ev_pi2 (et_bvar6 _ k intSet t z' z0 _))))
          (ev_faf_eq
            (et_comp2 ev_value
              (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar4 k intSet t z' _)))
              (et_bvar1 k _))
            (et_comp2 ev_value
              (et_comp1 ev_pi2 (et_comp1 ev_pi2 (et_bvar6 _ k intSet t z' z0 _)))
              (et_bvar2 _ k _)))
    · constructor
      · rintro ⟨hz', t, rfl, hq_eq, hdir, hwr, hrest⟩
        obtain ⟨q2, pos2, g2, _, hg2, rfl⟩ := mem_cfgSetVal_iff.mp hz'
        dsimp [z0, tVal] at hq_eq hdir hwr hrest
        rw [pi1Val_pair, pi1Val_pair] at hq_eq
        rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair] at hdir
        rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair] at hwr
        simp only [pi2Val_pair, pi1Val_pair] at hrest
        rw [hstep_val, hq_eq]
        congr 1; congr 1
        · have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · have h01 : vnNat 0 ≠ vnNat 1 := fun h => absurd (vnNat_injective h) (by decide)
            have h02 : vnNat 0 ≠ vnNat 2 := fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h01, h02, false_and, or_false] at hdir
            rw [ev_integerPred_encode] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
          · have h10 : vnNat 1 ≠ vnNat 0 := fun h => absurd (vnNat_injective h) (by decide)
            have h12 : vnNat 1 ≠ vnNat 2 := fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h10, h12, false_and, false_or, or_false] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
          · have h20 : vnNat 2 ≠ vnNat 0 := fun h => absurd (vnNat_injective h) (by decide)
            have h21 : vnNat 2 ≠ vnNat 1 := fun h => absurd (vnNat_injective h) (by decide)
            simp only [true_and, h20, h21, false_and, false_or] at hdir
            rw [ev_integerSucc_encode] at hdir
            dsimp [pos']; rw [hdv]; simpa using hdir
        · refine funs_ext hg2 (zfcUpdateTape_mem_funs hg (vnNat_lt_mem hob.2.1)) fun k hk => ?_
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) hk]
          by_cases hkp : k = encodeInt pos
          · rw [if_pos hkp, hkp, hwr]
          · rw [if_neg hkp, hrest k hk hkp]
      · rintro rfl
        refine ⟨zfcStepFn_mem_cfg M hz, tVal, rfl, ?_, ?_, ?_, ?_⟩
        · rw [hstep_val]; dsimp [tVal]; rw [pi1Val_pair, pi1Val_pair]
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair]
          have hd2 := hob.2.2
          interval_cases hdv : o.2.2
          · left; refine ⟨rfl, ?_⟩
            rw [ev_integerPred_encode]; dsimp [pos']; rw [hdv]; rfl
          · right; left; refine ⟨rfl, ?_⟩
            dsimp [pos']; rw [hdv]; rfl
          · right; right; refine ⟨rfl, ?_⟩
            rw [ev_integerSucc_encode]; dsimp [pos']; rw [hdv]; rfl
        · rw [hstep_val]; dsimp [z0, tVal]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi1Val_pair, pi2Val_pair, pi1Val_pair]
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) (encodeInt_mem pos), if_pos rfl]
        · intro k hk hne
          dsimp [z0] at hne
          rw [pi2Val_pair, pi1Val_pair] at hne
          rw [hstep_val]; dsimp [z0]
          rw [pi2Val_pair, pi2Val_pair, pi2Val_pair, pi2Val_pair]
          rw [zfcUpdateTape_app hg (vnNat_lt_mem hob.2.1) hk, if_neg hne]
  · simp [hz]

private noncomputable def nextStepVal {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ZFSet.{0} :=
  letI : ZFSet.Definable₁ (zfcStepFn M) := Classical.allZFSetDefinable _
  ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1))

private lemma nextStepVal_funs_and_app {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    nextStepVal M ∈ ZFSet.funs (cfgSetVal (n + 1)) (cfgSetVal (n + 1)) ∧
      ∀ z ∈ cfgSetVal (n + 1), zfcApp (nextStepVal M) z = zfcStepFn M z := by
  let _ : ZFSet.Definable₁ (zfcStepFn M) := Classical.allZFSetDefinable _
  have hfuns : nextStepVal M ∈ ZFSet.funs (cfgSetVal (n + 1)) (cfgSetVal (n + 1)) := by
    change ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1)) ∈ _
    rw [ZFSet.mem_funs, ZFSet.map_isFunc]
    exact fun _ hz => zfcStepFn_mem_cfg M hz
  refine ⟨hfuns, fun z hz => ?_⟩
  have hmem : ZFSet.pair z (zfcStepFn M z) ∈ nextStepVal M := by
    change ZFSet.pair z (zfcStepFn M z) ∈ ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1))
    exact ZFSet.mem_map.mpr ⟨z, hz, rfl⟩
  exact zfcApp_of_mem_funs hfuns hz hmem

private lemma dc_nextStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    DefinesConst (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) (nextStepVal M) := by
  let _ : ZFSet.Definable₁ (zfcStepFn M) := Classical.allZFSetDefinable _
  intro p
  unfold Constant14.nextStep
  change stdEv ![p] (∀¹ _) ↔ _
  rw [stdEv_all]
  refine (?_ : _ ↔ ∀ e : ZFSet.{0}, e ∈ p ↔ e ∈ nextStepVal M).trans
    ⟨fun h => ZFSet.ext h, fun h e => by rw [h]⟩
  refine forall_congr' fun e => ?_
  rw [stdEv_iff]
  refine iff_congr (ev_faf_mem (et_bvar1 e _) (et_bvar3 _ e p _)) ?_
  rw [ev_faf_bexs (et_const0 (dc_configSet (n + 1)) _)]
  refine (?_ : _ ↔ ∃ z ∈ cfgSetVal (n + 1),
      ∃ z' ∈ cfgSetVal (n + 1), e = ZFSet.pair z z' ∧ z' = zfcStepFn M z).trans ?_
  · refine exists_congr fun z => and_congr_right fun hz => ?_
    rw [ev_faf_bexs (et_const0 (dc_configSet (n + 1)) _)]
    refine exists_congr fun z' => and_congr_right fun _ => ?_
    rw [stdEv_and]
    rw [ev_faf_eq (et_bvar5 z' _ z _ e _)
          (et_comp2 ev_kpair (et_bvar4 _ z' _ z _) (et_bvar2 _ z' _)),
        ev_nest2 (Constant14.nextConfig (n + 1) (Constant14.instructionTable M))
          (et_bvar1 z' _) (et_bvar3 z' _ z _),
        ev_nextConfig_iff M z' z]
    exact and_congr Iff.rfl ⟨And.right, fun h => ⟨hz, h⟩⟩
  · change _ ↔ e ∈ ZFSet.map (zfcStepFn M) (cfgSetVal (n + 1))
    rw [ZFSet.mem_map]
    constructor
    · rintro ⟨z, hz, z', _, rfl, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, zfcStepFn M z, zfcStepFn_mem_cfg M hz, rfl, rfl⟩

/- ## Section 5: Encoded Lean Configurations, `orbit`, and Final Contradiction -/

private noncomputable def encodeTape (T : Tape (Fin 2)) (pos : ℤ) : ZFSet.{0} :=
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => vnNat (T.nth (decodePos w - pos)).val
  letI : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  ZFSet.map fn intSet

private lemma encodeTape_funs_and_app (T : Tape (Fin 2)) (pos : ℤ) :
    encodeTape T pos ∈ ZFSet.funs intSet (vnNat 2) ∧
      ∀ m : ℤ, zfcApp (encodeTape T pos) (encodeInt m) = vnNat (T.nth (m - pos)).val := by
  let fn : ZFSet.{0} → ZFSet.{0} := fun w => vnNat (T.nth (decodePos w - pos)).val
  let _ : ZFSet.Definable₁ fn := Classical.allZFSetDefinable _
  have hfn_eq (m : ℤ) : fn (encodeInt m) = vnNat (T.nth (m - pos)).val := by
    dsimp [fn]
    rw [decodePos_encodeInt]
  have hfuns : encodeTape T pos ∈ ZFSet.funs intSet (vnNat 2) := by
    change ZFSet.map fn intSet ∈ ZFSet.funs intSet (vnNat 2)
    rw [ZFSet.mem_funs, ZFSet.map_isFunc]
    intro w hw
    obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
    rw [hfn_eq m]
    exact vnNat_lt_mem (T.nth (m - pos)).isLt
  refine ⟨hfuns, fun m => ?_⟩
  have hmem : ZFSet.pair (encodeInt m) (fn (encodeInt m)) ∈ encodeTape T pos := by
    change ZFSet.pair (encodeInt m) (fn (encodeInt m)) ∈ ZFSet.map fn intSet
    exact ZFSet.mem_map.mpr ⟨encodeInt m, encodeInt_mem m, rfl⟩
  rw [zfcApp_of_mem_funs hfuns (encodeInt_mem m) hmem, hfn_eq m]

private lemma blank_tape_nth (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  cases i with
  | ofNat k =>
    cases k <;> simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]
  | negSucc k =>
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', Fin.default_eq_zero]

private lemma dc_emptyTape :
    DefinesConst Constant14.emptyTape (encodeTape (Tape.mk₁ []) 0) := by
  intro f
  unfold Constant14.emptyTape
  rw [stdEv_and]
  rw [ev_faf_mem (et_bvar1 f _)
        (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _)),
      ev_faf_ball (et_const0 dc_integers _)]
  refine (and_congr Iff.rfl (forall₂_congr fun i _ =>
      (?_ : _ ↔ zfcApp f i = vnNat 0))).trans ?_
  · exact ev_faf_eq
      (et_comp2 ev_value (et_bvar3 i intSet f _) (et_bvar1 i _))
      (et_const0 (dc_numeral 0) _)
  · obtain ⟨he_funs, he_app⟩ := encodeTape_funs_and_app (Tape.mk₁ []) 0
    constructor
    · rintro ⟨hf, hall⟩
      refine funs_ext hf he_funs fun w hw => ?_
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [hall (encodeInt m) hw, he_app m, blank_tape_nth]
      rfl
    · rintro rfl
      refine ⟨he_funs, fun w hw => ?_⟩
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [he_app m, blank_tape_nth]
      rfl

private abbrev ExtCfg (n : ℕ) := Option (Fin n) × ℤ × Tape (Fin 2)

private def extInit (n : ℕ) [NeZero n] : ExtCfg n :=
  (some 0, 0, Tape.mk₁ [])

private def extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) : ExtCfg n → ExtCfg n
  | (none, pos, T) => (none, pos, T)
  | (some q, pos, T) =>
    match M q T.head with
    | none => (none, pos, T)
    | some (q', Stmt.write sym d) =>
      let pos' := match d with
        | Dir.left => pos - 1
        | Dir.right => pos + 1
      (q', pos', (T.write sym).move d)

private noncomputable def encodeExtCfg {n : ℕ} (c : ExtCfg n) : ZFSet.{0} :=
  ZFSet.pair (vnNat (Constant14.stateCode c.1))
    (ZFSet.pair (encodeInt c.2.1) (encodeTape c.2.2 c.2.1))

private lemma encodeExtCfg_mem {n : ℕ} (c : ExtCfg n) :
    encodeExtCfg c ∈ cfgSetVal (n + 1) := by
  refine mem_cfgSetVal_iff.mpr ⟨Constant14.stateCode c.1, c.2.1, encodeTape c.2.2 c.2.1, ?_,
    (encodeTape_funs_and_app c.2.2 c.2.1).1, rfl⟩
  cases c.1 with
  | none => exact Nat.lt_succ_self n
  | some q => exact Nat.lt_succ_of_lt q.isLt

private lemma dc_initialConfig (n : ℕ) [NeZero n] :
    DefinesConst Constant14.initialConfig (encodeExtCfg (extInit n)) := by
  intro z
  unfold Constant14.initialConfig
  rw [ev_faf_eq (et_bvar1 z _)
    (et_comp2 ev_kpair (et_const0 (dc_numeral 0) _)
      (et_comp2 ev_kpair (et_const0 dc_integerZero _) (et_const0 dc_emptyTape _)))]
  rfl

private lemma zfcStepFn_encodeExtCfg {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (c : ExtCfg n) :
    zfcStepFn M (encodeExtCfg c) = encodeExtCfg (extStep M c) := by
  rcases c with ⟨qOpt, pos, T⟩
  obtain ⟨hg, happ⟩ := encodeTape_funs_and_app T pos
  have hsym : zfcApp (encodeTape T pos) (encodeInt pos) = vnNat T.head.val := by
    have h := happ pos
    rw [sub_self] at h
    exact h
  cases qOpt with
  | none =>
    have hstep := zfcStepFn_of_cfg M n pos (encodeTape T pos) (Nat.lt_succ_self n) hg
      T.head.val T.head.isLt hsym
    dsimp only [encodeExtCfg, Constant14.stateCode] at hstep
    dsimp only [encodeExtCfg, extStep, Constant14.stateCode]
    rw [hstep]
    have hlu : transLookup M n T.head.val = (n, T.head.val, 1) := by
      unfold transLookup; rw [dif_neg (Nat.lt_irrefl n)]
    rw [hlu]
    have h10 : (1 : ℕ) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    congr 1; congr 1
    refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem T.head.isLt)) hg fun w hw => ?_
    obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
    rw [zfcUpdateTape_app hg (vnNat_lt_mem T.head.isLt) hw]
    by_cases hmp : m = pos
    · subst hmp
      rw [if_pos rfl, happ m, sub_self]; rfl
    · have hne : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
      rw [if_neg hne]
  | some q =>
    have hstep := zfcStepFn_of_cfg M q.val pos (encodeTape T pos) (Nat.lt_succ_of_lt q.isLt) hg
      T.head.val T.head.isLt hsym
    dsimp only [encodeExtCfg, Constant14.stateCode] at hstep
    change zfcStepFn M (ZFSet.pair (vnNat q.val) (ZFSet.pair (encodeInt pos) (encodeTape T pos))) =
      encodeExtCfg (extStep M (some q, pos, T))
    rw [hstep]
    have hlu : transLookup M q.val T.head.val = Constant14.transitionCode M q T.head := by
      unfold transLookup
      rw [dif_pos q.isLt, dif_pos T.head.isLt]
    rw [hlu]
    cases hM : M q T.head with
    | none =>
      rw [Constant14.transitionCode, extStep, hM]
      dsimp only [encodeExtCfg, Constant14.directionCode, Constant14.stateCode]
      refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
      refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem T.head.isLt)) hg fun w hw => ?_
      obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
      rw [zfcUpdateTape_app hg (vnNat_lt_mem T.head.isLt) hw]
      by_cases hmp : m = pos
      · subst hmp; rw [if_pos rfl, happ m, sub_self]; rfl
      · have hne : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
        rw [if_neg hne]
    | some pairOut =>
      rcases pairOut with ⟨q', ⟨sym, d⟩⟩
      cases d with
      | left =>
        rw [Constant14.transitionCode, extStep, hM]
        dsimp only [encodeExtCfg, Constant14.directionCode]
        refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
        obtain ⟨hg', happ'⟩ := encodeTape_funs_and_app ((T.write sym).move Dir.left) (pos - 1)
        refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem sym.isLt)) hg' fun w hw => ?_
        obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
        rw [zfcUpdateTape_app hg (vnNat_lt_mem sym.isLt) hw, happ' m, Tape.move_left_nth]
        have hidx : m - (pos - 1) - 1 = m - pos := by omega
        rw [hidx, Tape.write_nth]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
        · have hne1 : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
          have hne2 : m - pos ≠ 0 := by omega
          rw [if_neg hne1, if_neg hne2, happ m]
      | right =>
        rw [Constant14.transitionCode, extStep, hM]
        dsimp only [encodeExtCfg, Constant14.directionCode]
        refine congrArg (ZFSet.pair _) (congrArg₂ ZFSet.pair rfl ?_)
        obtain ⟨hg', happ'⟩ := encodeTape_funs_and_app ((T.write sym).move Dir.right) (pos + 1)
        refine funs_ext (zfcUpdateTape_mem_funs hg (vnNat_lt_mem sym.isLt)) hg' fun w hw => ?_
        obtain ⟨m, rfl⟩ := mem_intSet_iff.mp hw
        rw [zfcUpdateTape_app hg (vnNat_lt_mem sym.isLt) hw, happ' m, Tape.move_right_nth]
        have hidx : m - (pos + 1) + 1 = m - pos := by omega
        rw [hidx, Tape.write_nth]
        by_cases hmp : m = pos
        · subst hmp; rw [if_pos rfl, sub_self, if_pos rfl]
        · have hne1 : encodeInt m ≠ encodeInt pos := fun h => hmp (encodeInt_injective h)
          have hne2 : m - pos ≠ 0 := by omega
          rw [if_neg hne1, if_neg hne2, happ m]

private lemma iterate_nextStepVal_eq {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (k : ℕ) :
    (zfcApp (nextStepVal M))^[k] (encodeExtCfg (extInit n)) =
      encodeExtCfg ((extStep M)^[k] (extInit n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    obtain ⟨_, happ⟩ := nextStepVal_funs_and_app M
    rw [happ _ (encodeExtCfg_mem _), zfcStepFn_encodeExtCfg]

private lemma ev_orbit_range {f x0 : ZFSet.{0}}
    (hfunc : ∃ X Y : ZFSet.{0}, f ∈ ZFSet.funs X Y) :
    stdEv ![ZFSet.range (fun k : ℕ => (zfcApp f)^[k] x0), f, x0] Constant14.orbit := by
  let O := ZFSet.range (fun k : ℕ => (zfcApp f)^[k] x0)
  unfold Constant14.orbit
  rw [stdEv_and]
  refine ⟨?_, ?_⟩
  · rw [ev_nest1 SetTheory.IsFunction.dfn (et_bvar2 O f _), ev_IsFunction]
    exact hfunc
  · rw [stdEv_all]
    intro z
    rw [stdEv_iff]
    rw [ev_faf_mem (et_bvar1 z _) (et_bvar3 _ z O _)]
    rw [stdEv_all]
    have hO_iff : z ∈ O ↔ ∀ A : ZFSet.{0}, (x0 ∈ A ∧ ∀ y ∈ A, zfcApp f y ∈ A) → z ∈ A := by
      constructor
      · intro hzO A ⟨hx0, hclosed⟩
        obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hzO
        clear hzO
        induction k with
        | zero => exact hx0
        | succ k ih =>
          rw [Function.iterate_succ_apply']
          exact hclosed _ ih
      · intro hall
        refine hall O ⟨ZFSet.mem_range.mpr ⟨0, rfl⟩, ?_⟩
        intro y hy
        obtain ⟨k, rfl⟩ := ZFSet.mem_range.mp hy
        exact ZFSet.mem_range.mpr ⟨k + 1, Function.iterate_succ_apply' _ k x0⟩
    rw [hO_iff]
    symm
    refine forall_congr' fun A => ?_
    rw [stdEv_imp, stdEv_and]
    refine imp_congr (and_congr ?_ ?_)
      (ev_faf_mem (et_bvar2 A z _) (et_bvar2 _ A _))
    · exact ev_faf_mem (et_bvar5 A z O f x0 _) (et_bvar2 _ A _)
    · rw [ev_faf_ball (et_bvar1 A _)]
      refine forall₂_congr fun y _ => ?_
      exact ev_faf_mem
        (et_comp2 ev_value (et_bvar6 y A A z O f _) (et_bvar1 y _))
        (et_bvar4 _ y A A _)

private lemma multiStep_agrees_with_extStep {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∀ (k : ℕ) (qk : Fin n) (Tk : Tape (Fin 2)),
      M.multiStep (Machine.init []) k = some ⟨some qk, Tk⟩ →
        ((extStep M)^[k] (extInit n)).1 = some qk ∧
          ((extStep M)^[k] (extInit n)).2.2 = Tk := by
  intro k
  induction k with
  | zero =>
    intro qk Tk h0
    simp only [Machine.multiStep_zero, Machine.init, Fin.default_eq_zero, Option.some.injEq,
      Cfg.mk.injEq] at h0
    rcases h0 with ⟨hq, hT⟩
    subst hq hT
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro qk1 Tk1 hsucc
    rw [Machine.multiStep_succ] at hsucc
    cases hmk : M.multiStep (Machine.init []) k with
    | none =>
      rw [hmk] at hsucc; simp at hsucc
    | some cfg =>
      rw [hmk, Option.bind_some] at hsucc
      rcases cfg with ⟨qOpt, Tk⟩
      cases qOpt with
      | none =>
        simp [Machine.step] at hsucc
      | some qk =>
        obtain ⟨hq_ih, hT_ih⟩ := ih qk Tk hmk
        simp only [Machine.step] at hsucc
        cases hMq : M qk Tk.head with
        | none =>
          rw [hMq] at hsucc; simp at hsucc
        | some out =>
          rw [hMq, Option.map_some, Option.some.injEq] at hsucc
          rcases out with ⟨qNext, ⟨sym, d⟩⟩
          injection hsucc with hqN hTN
          subst hqN hTN
          rw [Function.iterate_succ_apply']
          rcases hext : (extStep M)^[k] (extInit n) with ⟨c1, posk, cT⟩
          rw [hext] at hq_ih hT_ih
          dsimp only at hq_ih hT_ih
          subst hq_ih hT_ih
          simp [extStep, hMq]


private lemma exists_extStep_none_of_isHalting {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hM : M.IsHalting) : ∃ k : ℕ, ((extStep M)^[k] (extInit n)).1 = none := by
  obtain ⟨m, hm⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hM
  -- Find the least `k` such that `M.HaltsAfter (Machine.init []) k`
  let k := Nat.find (⟨m, hm⟩ : ∃ t, M.HaltsAfter (Machine.init []) t)
  have hk : M.HaltsAfter (Machine.init []) k := Nat.find_spec (⟨m, hm⟩ : ∃ t, M.HaltsAfter (Machine.init []) t)
  by_cases hk0 : k = 0
  · rw [hk0, Machine.haltsAfter_zero_iff] at hk
    refine ⟨1, ?_⟩
    simp only [Function.iterate_one, extInit, extStep]
    simp only [Machine.init, Fin.default_eq_zero, Machine.step] at hk
    cases hMq : M 0 (Tape.mk₁ []).head with
    | none => rfl
    | some out =>
      rw [hMq] at hk
      simp at hk
  · have hprev : ¬ M.HaltsAfter (Machine.init []) (k - 1) :=
      Nat.find_min (⟨m, hm⟩ : ∃ t, M.HaltsAfter (Machine.init []) t) (by omega)
    obtain ⟨qprev, Tprev, hms⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) (k - 1) hprev
    obtain ⟨hq_ext, hT_ext⟩ := multiStep_agrees_with_extStep M (k - 1) qprev Tprev hms
    have hk_eq : k - 1 + 1 = k := by omega
    -- At step `k - 1`, `M.multiStep (k - 1) = some ⟨some qprev, Tprev⟩`, and `M.multiStep (k + 1) = none`.
    -- Look at `M qprev Tprev.head`:
    cases hMq : M qprev Tprev.head with
    | none =>
      refine ⟨k, ?_⟩
      rw [← hk_eq, Function.iterate_succ_apply']
      rcases hext : (extStep M)^[k - 1] (extInit n) with ⟨c1, posk, cT⟩
      rw [hext] at hq_ext hT_ext
      dsimp only at hq_ext hT_ext
      subst hq_ext hT_ext
      simp [extStep, hMq]
    | some out =>
      rcases out with ⟨qNext, ⟨sym, d⟩⟩
      cases qNext with
      | none =>
        refine ⟨k, ?_⟩
        rw [← hk_eq, Function.iterate_succ_apply']
        rcases hext : (extStep M)^[k - 1] (extInit n) with ⟨c1, posk, cT⟩
        rw [hext] at hq_ext hT_ext
        dsimp only at hq_ext hT_ext
        subst hq_ext hT_ext
        simp [extStep, hMq]
      | some qNext' =>
        -- Then `M.multiStep k = some ⟨some qNext', _⟩`, so `M.multiStep (k+1) = none` means `M qNext' _ = none`!
        have hmk : M.multiStep (Machine.init []) k = some ⟨some qNext', (Tprev.write sym).move d⟩ := by
          rw [← hk_eq, Machine.multiStep_succ, hms, Option.bind_some, Machine.step, hMq]
          rfl
        have hstepk : M.step ⟨some qNext', (Tprev.write sym).move d⟩ = none := by
          have hk' := hk
          rw [Machine.HaltsAfter, Machine.multiStep_succ, hmk, Option.bind_some] at hk'
          exact hk'
        have hMq2 : M qNext' ((Tprev.write sym).move d).head = none := by
          simp only [Machine.step] at hstepk
          cases h2 : M qNext' ((Tprev.write sym).move d).head with
          | none => rfl
          | some _ => rw [h2] at hstepk; simp at hstepk
        obtain ⟨hq_k, hT_k⟩ := multiStep_agrees_with_extStep M k qNext' ((Tprev.write sym).move d) hmk
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply']
        rcases hext : (extStep M)^[k] (extInit n) with ⟨c1, posk, cT⟩
        rw [hext] at hq_k hT_k
        dsimp only at hq_k hT_k
        subst hq_k hT_k
        simp [extStep, hMq2]

private lemma stdEv_halts_of_isHalting {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hM : M.IsHalting) :
    stdEv (Fin.elim0 : Fin 0 → ZFSet.{0}) (Constant14.halts M) := by
  obtain ⟨k, hk⟩ := exists_extStep_none_of_isHalting M hM
  rcases hck : (extStep M)^[k] (extInit n) with ⟨qOpt, pos, T⟩
  rw [hck] at hk
  dsimp only at hk
  subst hk
  rw [stdEv_e0 (Fin.elim0 : Fin 0 → ZFSet.{0}) ![]]
  unfold Constant14.halts
  rw [ev_faf_bexs (et_const0 dc_integers ![])]
  refine ⟨encodeInt pos, mem_intSet_iff.mpr ⟨pos, rfl⟩, ?_⟩
  rw [ev_faf_bexs
    (et_comp2 ev_function (et_const0 (dc_numeral 2) _) (et_const0 dc_integers _))]
  refine ⟨encodeTape T pos, (encodeTape_funs_and_app T pos).1, ?_⟩
  let target := ZFSet.pair (vnNat n) (ZFSet.pair (encodeInt pos) (encodeTape T pos))
  have htarget : EvalTermAt (encodeTape T pos :> ZFSet.funs intSet (vnNat 2) :> encodeInt pos :> intSet :> ![])
      (Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
        (Semiformula.nestFormulaeFunc (Constant14.numeral n) ![] :>
          Semiformula.nestFormulaeFunc SetTheory.kpair.dfn
            (op(=).operator (#0 :> #3 :> ![]) :> op(=).operator (#0 :> #1 :> ![]) :> ![]) :> ![]))
      target :=
    et_comp2 ev_kpair (et_const0 (dc_numeral n) _)
      (et_comp2 ev_kpair (et_bvar3 (encodeTape T pos) _ (encodeInt pos) _) (et_bvar1 (encodeTape T pos) _))
  unfold stdEv
  rw [ev_all']
  intro x1
  rw [ev_imp']
  intro hx1
  have hx1_eq : x1 = target := (htarget x1).mp hx1
  subst hx1_eq
  rw [ev_all']
  intro O
  rw [ev_imp']
  intro hO
  rw [ev_mem', tv_bvar, tv_bvar]
  change target ∈ O
  have hO' : stdEv ![O, nextStepVal M, encodeExtCfg (extInit n)] Constant14.orbit := by
    have h := (ev_nestFunc2_raw Constant14.orbit
      (et_const0 (dc_nextStep M) _) (et_const0 (dc_initialConfig n) _) O).mp hO
    exact h
  -- Extract the universal characterization of `O` from `orbit`
  unfold Constant14.orbit at hO'
  rw [stdEv_and] at hO'
  have hO_mem := (stdEv_all _ _).mp hO'.2 target
  rw [stdEv_iff, ev_faf_mem (et_bvar1 target _) (et_bvar3 _ target O _)] at hO_mem
  rw [hO_mem]
  rw [stdEv_all]
  intro A
  rw [stdEv_imp, stdEv_and]
  intro hA
  rw [ev_faf_mem (et_bvar2 A target _) (et_bvar2 _ A _)]
  have hx0A : encodeExtCfg (extInit n) ∈ A := by
    have h1 := hA.1
    rw [ev_faf_mem (et_bvar5 A target O (nextStepVal M) (encodeExtCfg (extInit n)) _) (et_bvar2 _ A _)] at h1
    exact h1
  have hclosedA : ∀ y ∈ A, zfcApp (nextStepVal M) y ∈ A := by
    have h2 := hA.2
    rw [ev_faf_ball (et_bvar1 A _)] at h2
    intro y hy
    have hy' := h2 y hy
    rw [ev_faf_mem
      (et_comp2 ev_value (et_bvar6 y A A target O (nextStepVal M) _) (et_bvar1 y _))
      (et_bvar4 _ y A A _)] at hy'
    exact hy'
  have hiter : (zfcApp (nextStepVal M))^[k] (encodeExtCfg (extInit n)) ∈ A := by
    clear hck hO' hO_mem hA
    induction k with
    | zero => exact hx0A
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hclosedA _ ih
  rw [iterate_nextStepVal_eq M k, hck] at hiter
  exact hiter

lemma not_provable_neg_halts_of_isHalting {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (hM : M.IsHalting) :
    ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
  intro hprov
  have hsat := sound_theory zfsetModel hprov
  have hneg : ¬ exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Constant14.halts M) := (ev_neg _ _ _).mp hsat
  exact hneg (stdEv_halts_of_isHalting M hM)

end C14H4Proof

namespace C14H4Part3

open Turing BusyBeaver StateTransition Relation

/- ## Step 3A: Binary `TM0.Machine Bool (Fin m)` → `BusyBeaver.Machine (Fin 2) (Fin (2 * m))` -/

def boolToFin2 : Bool → Fin 2
  | false => 0
  | true => 1

def fin2ToBool (x : Fin 2) : Bool := x.val == 1

@[simp] lemma boolToFin2_default : boolToFin2 default = default := rfl

@[simp] lemma fin2ToBool_boolToFin2 (b : Bool) : fin2ToBool (boolToFin2 b) = b := by
  cases b <;> rfl

@[simp] lemma boolToFin2_fin2ToBool (x : Fin 2) : boolToFin2 (fin2ToBool x) = x := by
  fin_cases x <;> rfl

def boolToFin2Hom : PointedMap Bool (Fin 2) := ⟨boolToFin2, rfl⟩

def mapTape (T : Tape Bool) : Tape (Fin 2) :=
  Tape.mk' (T.left.map boolToFin2Hom) (T.right₀.map boolToFin2Hom)

lemma mapTape_head (T : Tape Bool) : (mapTape T).head = boolToFin2 T.head := by
  obtain ⟨L, R, rfl⟩ := T.exists_mk'
  obtain ⟨a, R, rfl⟩ := R.exists_cons
  simp only [mapTape, Tape.mk'_left, Tape.mk'_right₀, Tape.mk'_head,
    ListBlank.map_cons, ListBlank.head_cons]
  rfl

lemma mapTape_write (T : Tape Bool) (b : Bool) :
    mapTape (T.write b) = (mapTape T).write (boolToFin2 b) := by
  obtain ⟨L, R, rfl⟩ := T.exists_mk'
  obtain ⟨a, R, rfl⟩ := R.exists_cons
  simp only [mapTape, Tape.mk'_left, Tape.mk'_right₀, Tape.write_mk',
    ListBlank.tail_cons, ListBlank.map_cons]
  rfl

lemma mapTape_move (T : Tape Bool) (d : Dir) :
    mapTape (T.move d) = (mapTape T).move d := by
  obtain ⟨L, R, rfl⟩ := T.exists_mk'
  cases d with
  | left =>
    obtain ⟨a, L, rfl⟩ := L.exists_cons
    simp only [mapTape, Tape.move_left_mk', Tape.mk'_left, Tape.mk'_right₀,
      ListBlank.head_cons, ListBlank.tail_cons, ListBlank.map_cons]
  | right =>
    obtain ⟨a, R, rfl⟩ := R.exists_cons
    simp only [mapTape, Tape.move_right_mk', Tape.mk'_left, Tape.mk'_right₀,
      ListBlank.head_cons, ListBlank.tail_cons, ListBlank.map_cons]

private lemma listBlank_map_mk (l : List Bool) :
    (ListBlank.mk l).map boolToFin2Hom = ListBlank.mk (l.map boolToFin2) := by
  induction l with
  | nil =>
    change (default : ListBlank Bool).map boolToFin2Hom = default
    ext n; rw [ListBlank.nth_map]; rfl
  | cons a l ih =>
    rw [← ListBlank.cons_mk, ListBlank.map_cons, ih, List.map_cons, ListBlank.cons_mk]
    rfl

lemma mapTape_mk₁ (l : List Bool) :
    mapTape (Tape.mk₁ l) = Tape.mk₁ (l.map boolToFin2) := by
  simp only [mapTape, Tape.mk₁, Tape.mk₂, Tape.mk'_left, Tape.mk'_right₀, listBlank_map_mk,
    List.map_nil]

local instance instNeZeroTwoMul (m : ℕ) [NeZero m] : NeZero (2 * m) :=
  ⟨by have := NeZero.ne m; omega⟩

local instance instNeZeroAddRight (a k : ℕ) [NeZero k] : NeZero (a + k) :=
  ⟨by have := NeZero.ne k; omega⟩

def tm0ToBB {m : ℕ} [NeZero m] (T : TM0.Machine Bool (Fin m)) :
    BusyBeaver.Machine (Fin 2) (Fin (2 * m)) :=
  fun s sym =>
    if hs : s.val % 2 = 0 then
      let q : Fin m := ⟨s.val / 2, by omega⟩
      match T q (fin2ToBool sym) with
      | none => none
      | some (q', TM0.Stmt.move d) =>
        some (some ⟨2 * q'.val, by omega⟩, ⟨sym, d⟩)
      | some (q', TM0.Stmt.write b') =>
        some (some ⟨2 * q'.val + 1, by omega⟩, ⟨boolToFin2 b', Dir.right⟩)
    else
      let q : Fin m := ⟨s.val / 2, by omega⟩
      some (some ⟨2 * q.val, by omega⟩, ⟨sym, Dir.left⟩)

private def tm0ToBBCfg {m : ℕ} (c : TM0.Cfg Bool (Fin m)) :
    BusyBeaver.Cfg (Fin 2) (Fin (2 * m)) :=
  ⟨some ⟨2 * c.q.val, by have := c.q.isLt; omega⟩, mapTape c.Tape⟩

lemma tm0ToBB_respects {m : ℕ} [NeZero m] (T : TM0.Machine Bool (Fin m)) :
    Respects (TM0.step T) (tm0ToBB T).step
      (fun c₁ c₂ => tm0ToBBCfg c₁ = c₂) := by
  refine fun_respects.mpr fun ⟨q, tape⟩ => ?_
  have hqlt : q.val < m := q.isLt
  have h2q : 2 * q.val < 2 * m := by omega
  have hq_div : (⟨(2 * q.val) / 2, by omega⟩ : Fin m) = q := Fin.ext (by dsimp; omega)
  simp only [TM0.step, FRespects, tm0ToBBCfg]
  cases hT : T q tape.head with
  | none =>
    simp only [Option.map_none]
    change (tm0ToBB T).step ⟨some ⟨2 * q.val, h2q⟩, mapTape tape⟩ = none
    simp only [Machine.step, tm0ToBB, mapTape_head, fin2ToBool_boolToFin2]
    have hmod : (2 * q.val) % 2 = 0 := by omega
    rw [dif_pos hmod, hq_div, hT]
    rfl
  | some p =>
    rcases p with ⟨q', st⟩
    have hq'lt : q'.val < m := q'.isLt
    have h2q' : 2 * q'.val < 2 * m := by omega
    have h2q'1 : 2 * q'.val + 1 < 2 * m := by omega
    simp only [Option.map_some]
    cases st with
    | move d =>
      refine TransGen.single ?_
      change (tm0ToBB T).step ⟨some ⟨2 * q.val, h2q⟩, mapTape tape⟩ =
        some ⟨some ⟨2 * q'.val, h2q'⟩, mapTape (tape.move d)⟩
      simp only [Machine.step, tm0ToBB, mapTape_head, fin2ToBool_boolToFin2]
      have hmod : (2 * q.val) % 2 = 0 := by omega
      rw [dif_pos hmod, hq_div, hT]
      simp only [Option.map_some, Option.some.injEq, Cfg.mk.injEq, true_and]
      rw [← mapTape_head, Tape.write_self, mapTape_move]
    | write b' =>
      have h1 : (tm0ToBB T).step ⟨some ⟨2 * q.val, h2q⟩, mapTape tape⟩ =
          some ⟨some ⟨2 * q'.val + 1, h2q'1⟩, ((mapTape tape).write (boolToFin2 b')).move Dir.right⟩ := by
        simp only [Machine.step, tm0ToBB, mapTape_head, fin2ToBool_boolToFin2]
        have hmod : (2 * q.val) % 2 = 0 := by omega
        rw [dif_pos hmod, hq_div, hT]
        rfl
      have h2 : (tm0ToBB T).step ⟨some ⟨2 * q'.val + 1, h2q'1⟩,
            ((mapTape tape).write (boolToFin2 b')).move Dir.right⟩ =
          some ⟨some ⟨2 * q'.val, h2q'⟩, mapTape (tape.write b')⟩ := by
        simp only [Machine.step, tm0ToBB]
        have hmod : ¬ ((2 * q'.val + 1) % 2 = 0) := by omega
        have hdiv : (2 * q'.val + 1) / 2 = q'.val := by omega
        rw [dif_neg hmod]
        simp only [Option.map_some, Option.some.injEq, Cfg.mk.injEq, Option.some.injEq]
        refine ⟨Fin.ext (by dsimp; omega), ?_⟩
        rw [Tape.write_self, Tape.move_right_left, mapTape_write]
      exact TransGen.head h1 (TransGen.single h2)

lemma tm0ToBB_eval_dom_iff {m : ℕ} [NeZero m] (T : TM0.Machine Bool (Fin m)) (l : List Bool) :
    (TM0.eval T l).Dom ↔ (tm0ToBB T).IsHaltingInput (l.map boolToFin2) := by
  have htr := tr_eval' (TM0.step T) (tm0ToBB T).step tm0ToBBCfg (tm0ToBB_respects T)
    (TM0.init (Λ := Fin m) l)
  have hinit : tm0ToBBCfg (TM0.init (Λ := Fin m) l) =
      Machine.init (Λ := Fin (2 * m)) (l.map boolToFin2) := by
    simp only [tm0ToBBCfg, TM0.init, Machine.init, Fin.default_eq_zero, Fin.val_zero, mul_zero,
      mapTape_mk₁]
    rfl
  rw [hinit] at htr
  change (Part.map _ (StateTransition.eval (TM0.step T) (TM0.init l))).Dom ↔
    (Part.map _ (StateTransition.eval (tm0ToBB T).step (Machine.init (l.map boolToFin2)))).Dom
  rw [htr]
  simp

/- ## Step 3B: Prepending a blank-tape input writer `prependBits` -/

def prependBits {k : ℕ} [NeZero k] (bits : List (Fin 2)) (B : BusyBeaver.Machine (Fin 2) (Fin k)) :
    BusyBeaver.Machine (Fin 2) (Fin (2 * bits.length + k)) :=
  fun s sym =>
    if h1 : s.val < bits.length then
      some (some ⟨s.val + 1, by have := NeZero.pos k; omega⟩, ⟨bits[s.val]'h1, Dir.right⟩)
    else if h2 : s.val < 2 * bits.length then
      some (some ⟨s.val + 1, by have := NeZero.pos k; omega⟩, ⟨sym, Dir.left⟩)
    else
      match B ⟨s.val - 2 * bits.length, by omega⟩ sym with
      | none => none
      | some (none, st) => some (none, st)
      | some (some q', st) => some (some ⟨2 * bits.length + q'.val, by omega⟩, st)

private lemma listBlank_mk_nil {Γ : Type*} [Inhabited Γ] :
    (ListBlank.mk ([] : List Γ)) = default := rfl

private lemma listBlank_tail_default {Γ : Type*} [Inhabited Γ] :
    (default : ListBlank Γ).tail = default := by
  change (ListBlank.mk ([] : List Γ)).tail = ListBlank.mk []
  simp [ListBlank.tail_mk]

private lemma prependBits_write_phase {k : ℕ} [NeZero k] (bits : List (Fin 2))
    (B : BusyBeaver.Machine (Fin 2) (Fin k)) (i : ℕ) (hi : i ≤ bits.length) :
    Reaches (prependBits bits B).step
      (Machine.init [])
      ⟨some ⟨i, by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk (bits.take i).reverse) default⟩ := by
  induction i with
  | zero =>
    simp only [List.take_zero, List.reverse_nil]
    exact ReflTransGen.refl
  | succ i ih =>
    have hi' : i < bits.length := by omega
    refine (ih (by omega)).tail ?_
    change (prependBits bits B).step
      ⟨some ⟨i, by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk (bits.take i).reverse) default⟩ =
      some ⟨some ⟨i + 1, by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk (bits.take (i + 1)).reverse) default⟩
    simp only [Machine.step, prependBits, dif_pos hi', Option.map_some, Option.some.injEq,
      Cfg.mk.injEq, true_and]
    rw [List.take_succ_eq_append_getElem hi', List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    rw [Tape.write_mk', Tape.move_right_mk']
    simp only [ListBlank.head_cons, ListBlank.tail_cons, listBlank_tail_default,
      ListBlank.cons_mk]

private lemma prependBits_return_phase {k : ℕ} [NeZero k] (bits : List (Fin 2))
    (B : BusyBeaver.Machine (Fin 2) (Fin k)) (j : ℕ) (hj : j ≤ bits.length) :
    Reaches (prependBits bits B).step
      ⟨some ⟨bits.length, by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk bits.reverse) default⟩
      ⟨some ⟨bits.length + j, by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk (bits.take (bits.length - j)).reverse)
          (ListBlank.mk (bits.drop (bits.length - j)))⟩ := by
  induction j with
  | zero =>
    simp only [add_zero, Nat.sub_zero, List.take_length, List.drop_length, listBlank_mk_nil]
    exact ReflTransGen.refl
  | succ j ih =>
    have hj' : j < bits.length := by omega
    refine (ih (by omega)).tail ?_
    change (prependBits bits B).step
      ⟨some ⟨bits.length + j, by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk (bits.take (bits.length - j)).reverse)
          (ListBlank.mk (bits.drop (bits.length - j)))⟩ =
      some ⟨some ⟨bits.length + (j + 1), by have := NeZero.pos k; omega⟩,
        Tape.mk' (ListBlank.mk (bits.take (bits.length - (j + 1))).reverse)
          (ListBlank.mk (bits.drop (bits.length - (j + 1))))⟩
    have hnot1 : ¬ (bits.length + j < bits.length) := by omega
    have hlt2 : bits.length + j < 2 * bits.length := by omega
    simp only [Machine.step, prependBits, dif_neg hnot1, dif_pos hlt2, Option.map_some,
      Option.some.injEq, Cfg.mk.injEq]
    refine ⟨by apply Fin.ext; dsimp; omega, ?_⟩
    rw [Tape.write_self, Tape.move_left_mk']
    set idx := bits.length - (j + 1) with hidx
    have hidx_lt : idx < bits.length := by omega
    have hidx_succ : bits.length - j = idx + 1 := by omega
    rw [hidx_succ, List.take_succ_eq_append_getElem hidx_lt, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    rw [← ListBlank.cons_mk]
    simp only [ListBlank.head_cons, ListBlank.tail_cons]
    congr 1
    rw [ListBlank.cons_mk, List.cons_getElem_drop_succ (h := hidx_lt)]

private def shiftCfg {k : ℕ} (L : ℕ) (c : BusyBeaver.Cfg (Fin 2) (Fin k)) :
    BusyBeaver.Cfg (Fin 2) (Fin (2 * L + k)) :=
  ⟨c.q.map fun q => ⟨2 * L + q.val, by have := q.isLt; omega⟩, c.tape⟩

private lemma prependBits_respects {k : ℕ} [NeZero k] (bits : List (Fin 2))
    (B : BusyBeaver.Machine (Fin 2) (Fin k)) :
    Respects B.step (prependBits bits B).step
      (fun c₁ c₂ => shiftCfg bits.length c₁ = c₂) := by
  refine fun_respects.mpr fun ⟨qOpt, tape⟩ => ?_
  cases qOpt with
  | none =>
    simp [Machine.step, FRespects, shiftCfg]
  | some q =>
    have hqlt : q.val < k := q.isLt
    have h2q : 2 * bits.length + q.val < 2 * bits.length + k := by omega
    have hsub : 2 * bits.length + q.val - 2 * bits.length < k := by omega
    have hq : (⟨2 * bits.length + q.val - 2 * bits.length, hsub⟩ : Fin k) = q :=
      Fin.ext (by dsimp; omega)
    simp only [Machine.step, FRespects, shiftCfg, Option.map_some]
    have hnot1 : ¬ (2 * bits.length + q.val < bits.length) := by omega
    have hnot2 : ¬ (2 * bits.length + q.val < 2 * bits.length) := by omega
    cases hB : B q tape.head with
    | none =>
      simp only [Option.map_none]
      change (prependBits bits B).step ⟨some ⟨2 * bits.length + q.val, h2q⟩, tape⟩ = none
      simp only [Machine.step, prependBits, dif_neg hnot1, dif_neg hnot2, hq, hB]
      rfl
    | some out =>
      rcases out with ⟨q', ⟨sym, d⟩⟩
      simp only [Option.map_some]
      refine TransGen.single ?_
      change (prependBits bits B).step ⟨some ⟨2 * bits.length + q.val, h2q⟩, tape⟩ =
        some (shiftCfg bits.length ⟨q', (tape.write sym).move d⟩)
      simp only [Machine.step, prependBits, dif_neg hnot1, dif_neg hnot2, hq, hB]
      cases q' <;> rfl

lemma prependBits_isHalting_iff {k : ℕ} [NeZero k] (bits : List (Fin 2))
    (B : BusyBeaver.Machine (Fin 2) (Fin k)) :
    (prependBits bits B).IsHalting ↔ B.IsHaltingInput bits := by
  have h1 := prependBits_write_phase bits B bits.length le_rfl
  rw [List.take_length] at h1
  have h2 := prependBits_return_phase bits B bits.length le_rfl
  rw [Nat.sub_self, List.take_zero, List.reverse_nil, listBlank_mk_nil, List.drop_zero] at h2
  have hreach : Reaches (prependBits bits B).step (Machine.init [])
      (shiftCfg bits.length (Machine.init bits)) := by
    have heq : (⟨some ⟨bits.length + bits.length, by have := NeZero.pos k; omega⟩,
        Tape.mk' default (ListBlank.mk bits)⟩ :
        BusyBeaver.Cfg (Fin 2) (Fin (2 * bits.length + k))) =
        shiftCfg bits.length (Machine.init bits) := by
      simp only [shiftCfg, Machine.init, Fin.default_eq_zero, Fin.val_zero, add_zero,
        Option.map_some, Tape.mk₁]
      congr 2; apply Fin.ext; dsimp; omega
    rw [← heq]
    exact h1.trans h2
  have heval := reaches_eval hreach
  have htr := tr_eval' B.step (prependBits bits B).step (shiftCfg bits.length)
    (prependBits_respects bits B) (Machine.init bits)
  have hdom : (StateTransition.eval (prependBits bits B).step (Machine.init [])).Dom ↔
      (StateTransition.eval B.step (Machine.init bits)).Dom := by
    rw [heval, htr]
    simp
  exact ⟨fun h => hdom.mp (by simpa [Machine.IsHaltingInput, Machine.eval] using h.halts),
         fun h => ⟨by simpa [Machine.IsHaltingInput, Machine.eval] using hdom.mpr h⟩⟩

/- ## Step 3C: Fixed universal `BusyBeaver.Machine` + computable input-bits encoder -/

open scoped Classical

private lemma exists_universal_toPartrec :
    ∃ u : Turing.ToPartrec.Code, ∀ c : Nat.Partrec.Code,
      (u.eval [Encodable.encode c]).Dom ↔ (c.eval 0).Dom := by
  let f : ℕ →. ℕ := fun n =>
    (Encodable.decode (α := Nat.Partrec.Code) n : Part Nat.Partrec.Code).bind (fun c => c.eval 0)
  have hf : Partrec f :=
    Partrec.bind (Computable.decode (α := Nat.Partrec.Code)).ofOption
      (Nat.Partrec.Code.eval_part.comp Computable.snd (Computable.const 0)).to₂
  have hf' : Nat.Partrec' (fun v : List.Vector ℕ 1 => f v.head) :=
    Nat.Partrec'.part_iff₁.mpr hf
  obtain ⟨u, hu⟩ := Turing.ToPartrec.Code.exists_code hf'
  refine ⟨u, fun c => ?_⟩
  have h := hu ⟨[Encodable.encode c], rfl⟩
  have hhead : List.Vector.head (⟨[Encodable.encode c], rfl⟩ : List.Vector ℕ 1) = Encodable.encode c := rfl
  rw [hhead] at h
  simp only [f, Encodable.encodek] at h
  change (u.eval [Encodable.encode c]).Dom ↔ (c.eval 0).Dom
  rw [h]
  simp

private def natToBitsVec (w : ℕ) (n : ℕ) : List.Vector Bool w :=
  List.Vector.ofFn fun i : Fin w => n.testBit i.val

private def bitsVecToNat {w : ℕ} (v : List.Vector Bool w) : ℕ :=
  ∑ i : Fin w, if v.get i then 2 ^ i.val else 0

private lemma natToBitsVec_zero (w : ℕ) :
    natToBitsVec w 0 = List.Vector.replicate w false := by
  ext i
  simp [natToBitsVec]

private lemma bitsVecToNat_natToBitsVec {w n : ℕ} (hn : n < 2 ^ w) :
    bitsVecToNat (natToBitsVec w n) = n := by
  unfold bitsVecToNat natToBitsVec
  have hsum : ∀ (k m : ℕ), m < 2 ^ k →
      (∑ i : Fin k, if m.testBit i.val then 2 ^ i.val else 0) = m := by
    intro k
    induction k with
    | zero => intro m hm; simp only [pow_zero] at hm; simp [show m = 0 by omega]
    | succ k ih =>
      intro m hm
      rw [Fin.sum_univ_succ]
      have hdiv : m / 2 < 2 ^ k := Nat.div_lt_of_lt_mul (by rwa [pow_succ'] at hm)
      have hrest : (∑ i : Fin k, if m.testBit i.succ.val then 2 ^ i.succ.val else 0) =
          2 * (∑ i : Fin k, if (m / 2).testBit i.val then 2 ^ i.val else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Fin.val_succ, Nat.testBit_succ, pow_succ']
        split_ifs <;> ring
      rw [hrest, ih (m / 2) hdiv]
      simp only [Fin.val_zero, pow_zero, Nat.testBit_zero]
      by_cases hm2 : m % 2 = 1
      · simp [hm2]; omega
      · simp [hm2]; omega
  simpa using hsum w n hn

private lemma exists_fintype_bool_encoding (Γ : Type*) [Fintype Γ] [Inhabited Γ] :
    ∃ (w : ℕ) (enc : Γ → List.Vector Bool w) (dec : List.Vector Bool w → Γ),
      enc default = List.Vector.replicate w false ∧ ∀ a, dec (enc a) = a := by
  let e0 := Fintype.equivFin Γ
  let m := Fintype.card Γ
  have hm : 0 < m := Fintype.card_pos
  let e : Γ ≃ Fin m := e0.trans (Equiv.swap (e0 default) ⟨0, hm⟩)
  have he0 : e default = ⟨0, hm⟩ := by simp [e]
  let w := m
  have hlt : ∀ a : Γ, (e a).val < 2 ^ w := fun a =>
    lt_trans (e a).isLt Nat.lt_two_pow_self
  let enc : Γ → List.Vector Bool w := fun a => natToBitsVec w (e a).val
  let dec : List.Vector Bool w → Γ := fun v =>
    if h : bitsVecToNat v < m then e.symm ⟨bitsVecToNat v, h⟩ else default
  refine ⟨w, enc, dec, ?_, ?_⟩
  · simp [enc, he0, natToBitsVec_zero]
  · intro a
    simp only [dec, enc, bitsVecToNat_natToBitsVec (hlt a), (e a).isLt, ↓reduceDIte,
      Fin.eta, Equiv.symm_apply_apply]

/- ### Computability of `trNat` and `TM1to1.trTape` on `Tape.mk₁` -/

private def natBitsRec : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let k := n + 1
    (k % 2 == 1) :: natBitsRec (k / 2)

private lemma natBitsRec_eq_trNat (n : ℕ) :
    (natBitsRec n).map (fun b => if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) =
      PartrecToTM2.trNat n := by
  have hpos : ∀ p : PosNum,
      (natBitsRec (p : ℕ)).map
        (fun b => if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) =
        PartrecToTM2.trPosNum p := by
    intro p
    induction p with
    | one =>
      change (natBitsRec 1).map _ = [PartrecToTM2.Γ'.bit1]
      simp [natBitsRec]
    | bit0 p ihp =>
      have hv : ((PosNum.bit0 p : PosNum) : ℕ) = 2 * (p : ℕ) := by
        simp [PosNum.cast_bit0, two_mul]
      have hne0 : (p : ℕ) ≠ 0 := (PosNum.cast_pos p).ne'
      have hne2 : 2 * (p : ℕ) ≠ 0 := by omega
      have hmod : (2 * (p : ℕ)) % 2 = 0 := by omega
      have hdiv2 : (2 * (p : ℕ)) / 2 = (p : ℕ) := by omega
      have hrec : natBitsRec (2 * (p : ℕ)) =
          ((2 * (p : ℕ)) % 2 == 1) :: natBitsRec ((2 * (p : ℕ)) / 2) := by
        rcases Nat.exists_eq_succ_of_ne_zero hne2 with ⟨r, hr⟩
        rw [hr]; simp [natBitsRec]
      rw [hv, hrec, List.map_cons, hmod, hdiv2, ihp]
      simp [PartrecToTM2.trPosNum]
    | bit1 p ihp =>
      have hv : ((PosNum.bit1 p : PosNum) : ℕ) = 2 * (p : ℕ) + 1 := by
        simp [PosNum.cast_bit1, two_mul]
      have hmod : (2 * (p : ℕ) + 1) % 2 = 1 := by omega
      have hdiv2 : (2 * (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
      have hrec : natBitsRec (2 * (p : ℕ) + 1) =
          ((2 * (p : ℕ) + 1) % 2 == 1) :: natBitsRec ((2 * (p : ℕ) + 1) / 2) := by
        simp [natBitsRec]
      rw [hv, hrec, List.map_cons, hmod, hdiv2, ihp]
      simp [PartrecToTM2.trPosNum]
  have hnum : ∀ x : Num,
      (natBitsRec (x : ℕ)).map
        (fun b => if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) =
        PartrecToTM2.trNum x := by
    intro x
    cases x with
    | zero =>
      change (natBitsRec 0).map _ = []
      simp [natBitsRec]
    | pos p => exact hpos p
  have h := hnum (n : Num)
  simpa [PartrecToTM2.trNat] using h

private lemma computable_natBitsRec : Computable natBitsRec := by
  have hprim : Primrec natBitsRec := by
    let stepPair : ℕ × List Bool → ℕ × List Bool := fun p =>
      if p.1 = 0 then p else (p.1 / 2, (p.1 % 2 == 1) :: p.2)
    have hstep_prim : Primrec stepPair := by
      refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id ?_
      refine Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2)) ?_
      refine Primrec.list_cons.comp ?_ Primrec.snd
      refine (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
          (Primrec.const 1)) (Primrec.const true) (Primrec.const false)).of_eq fun p => ?_
      cases h : (p.1 % 2 == 1)
      · have hne : p.1 % 2 ≠ 1 := beq_eq_false_iff_ne.mp h
        simp [hne]
      · have heq : p.1 % 2 = 1 := beq_iff_eq.mp h
        simp [heq]
    have hiter : ∀ (fuel n : ℕ) (acc : List Bool), n ≤ fuel →
        (stepPair^[fuel] (n, acc)).2 = (natBitsRec n).reverse ++ acc := by
      intro fuel
      induction fuel with
      | zero =>
        intro n acc hn
        have hn0 : n = 0 := by omega
        subst hn0; simp [natBitsRec]
      | succ fuel ih =>
        intro n acc hn
        rw [Function.iterate_succ_apply]
        cases n with
        | zero =>
          simp only [stepPair, ↓reduceIte]
          simpa [natBitsRec] using ih 0 acc (by omega)
        | succ m =>
          have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
          simp only [stepPair, hne, ↓reduceIte]
          rw [ih ((m + 1) / 2) (((m + 1) % 2 == 1) :: acc) (by omega)]
          simp [natBitsRec]
    have hrev : Primrec (fun n : ℕ => (stepPair^[n] (n, [])).2.reverse) := by
      refine Primrec.list_reverse.comp (Primrec.snd.comp ?_)
      have hrec : Primrec (fun n : ℕ =>
          Nat.rec (motive := fun _ => ℕ × List Bool) (n, []) (fun _ y => stepPair y) n) :=
        (Primrec.nat_rec (Primrec.pair Primrec.id (Primrec.const []))
          (hstep_prim.comp (Primrec.snd.comp Primrec.snd)).to₂).comp Primrec.id Primrec.id
      exact hrec.of_eq fun n => by
        have : ∀ k x, (Nat.rec (motive := fun _ => ℕ × List Bool) x (fun _ y => stepPair y) k) =
            stepPair^[k] x := by
          intro k; induction k with
          | zero => intro x; rfl
          | succ k ih => intro x; rw [Function.iterate_succ_apply']; exact congrArg stepPair (ih x)
        exact this n (n, [])
    exact hrev.of_eq fun n => by
      rw [hiter n n [] le_rfl, List.append_nil, List.reverse_reverse]
  exact hprim.to_comp

private lemma listBlank_flatMap_default {Γ : Type*} [Inhabited Γ]
    (f : Γ → List Bool) (hf : ∃ n, f default = List.replicate n default) :
    (default : ListBlank Γ).flatMap f hf = default := by
  change (ListBlank.mk ([] : List Γ)).flatMap f hf = ListBlank.mk []
  rfl

private lemma trTape_mk₁ {Γ : Type*} [Inhabited Γ] {w : ℕ}
    {enc : Γ → List.Vector Bool w} (enc0 : enc default = List.Vector.replicate w false)
    (L : List Γ) :
    TM1to1.trTape enc0 (Tape.mk₁ L) = Tape.mk₁ (L.flatMap fun x => (enc x).toList) := by
  have hflat : ∀ (xs : List Γ),
      (ListBlank.mk xs).flatMap (fun x => (enc x).toList)
        ⟨w, by simp [enc0, List.Vector.replicate, Bool.default_bool]⟩ =
      ListBlank.mk (xs.flatMap fun x => (enc x).toList) := by
    intro xs
    induction xs with
    | nil => exact listBlank_flatMap_default _ _
    | cons a xs ih =>
      rw [← ListBlank.cons_mk, ListBlank.cons_flatMap, ih, List.flatMap_cons, ListBlank.append_mk]
  unfold TM1to1.trTape TM1to1.trTape' Tape.mk₁ Tape.mk₂
  rw [Tape.mk'_left, Tape.mk'_right₀, hflat L]
  have hL : (ListBlank.mk ([] : List Γ)).flatMap (fun x => (enc x).toList.reverse)
      ⟨w, by simp [enc0, List.Vector.replicate, Bool.default_bool]⟩ = ListBlank.mk [] :=
    listBlank_flatMap_default _ _
  rw [hL]

/- ### Main theorem of Part 3: Universal `BusyBeaver.Machine` with computable input bits -/

theorem exists_universal_bb :
    ∃ (k : ℕ) (_ : NeZero k) (B₀ : BusyBeaver.Machine (Fin 2) (Fin k))
      (bitsOfCode : Nat.Partrec.Code → List (Fin 2)),
      Computable bitsOfCode ∧
      ∀ c : Nat.Partrec.Code, (prependBits (bitsOfCode c) B₀).IsHalting ↔ (c.eval 0).Dom := by
  obtain ⟨u, hu⟩ := exists_universal_toPartrec
  -- Layer 1: TM2 with default state = `trNormal u Cont'.halt`
  let : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal u PartrecToTM2.Cont'.halt⟩
  let M2 := PartrecToTM2.tr
  have hS2 : TM2.Supports M2 (PartrecToTM2.codeSupp u PartrecToTM2.Cont'.halt) :=
    PartrecToTM2.tr_supports u PartrecToTM2.Cont'.halt
  -- Layer 2: TM1 over finite alphabet `Γ1 := TM2to1.Γ' PartrecToTM2.K' PartrecToTM2.Γ`
  let M1 := TM2to1.tr M2
  have hS1 : TM1.Supports M1 (TM2to1.trSupp M2 (PartrecToTM2.codeSupp u PartrecToTM2.Cont'.halt)) :=
    TM2to1.tr_supports M2 hS2
  -- Layer 3: TM1 over `Bool` via finite-alphabet block encoding
  let eK' : PartrecToTM2.K' ≃ Fin 4 :=
    { toFun := fun k => match k with | .main => 0 | .rev => 1 | .aux => 2 | .stack => 3
      invFun := fun i => match i.val with | 0 => .main | 1 => .rev | 2 => .aux | _ => .stack
      left_inv := fun k => by cases k <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  let eΓ' : PartrecToTM2.Γ' ≃ Fin 4 :=
    { toFun := fun g => match g with | .cons => 0 | .bit0 => 1 | .bit1 => 2 | .consₗ => 3
      invFun := fun i => match i.val with | 0 => .cons | 1 => .bit0 | 2 => .bit1 | _ => .consₗ
      left_inv := fun g => by cases g <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  let : Fintype PartrecToTM2.K' := Fintype.ofEquiv (Fin 4) eK'.symm
  let : Fintype PartrecToTM2.Γ' := Fintype.ofEquiv (Fin 4) eΓ'.symm
  let Γ1 := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
  obtain ⟨w, enc, dec, henc0, hencdec⟩ := exists_fintype_bool_encoding Γ1
  let M1b := TM1to1.tr enc dec M1
  have hS1b : TM1.Supports M1b (TM1to1.trSupp M1 (TM2to1.trSupp M2 (PartrecToTM2.codeSupp u PartrecToTM2.Cont'.halt))) :=
    TM1to1.tr_supports enc dec M1 hS1
  -- Layer 4: TM0 over `Bool` with finite support `S0`
  let M0 := TM1to0.tr M1b
  let S0 := TM1to0.trStmts M1b (TM1to1.trSupp M1 (TM2to1.trSupp M2 (PartrecToTM2.codeSupp u PartrecToTM2.Cont'.halt)))
  have hS0 : TM0.Supports M0 ↑S0 := TM1to0.tr_supports M1b hS1b
  -- Layer 5: Relabel `S0` to `Fin m` with `default ↦ 0`
  let m := S0.card
  have hm_pos : 0 < m := Finset.card_pos.mpr ⟨default, hS0.1⟩
  have : NeZero m := ⟨hm_pos.ne'⟩
  let e0 : S0 ≃ Fin m := S0.equivFin
  let e : S0 ≃ Fin m := e0.trans (Equiv.swap (e0 ⟨default, hS0.1⟩) 0)
  have he_def : e ⟨default, hS0.1⟩ = 0 := by simp [e]
  let g₁ : PointedMap (TM1to0.Λ' M1b) (Fin m) :=
    ⟨fun q => if h : q ∈ S0 then e ⟨q, h⟩ else 0, by simp [hS0.1, he_def]⟩
  let g₂ : Fin m → TM1to0.Λ' M1b := fun i => (e.symm i).val
  have hg₂₁ : ∀ q ∈ (S0 : Set (TM1to0.Λ' M1b)), g₂ (g₁ q) = q := by
    intro q hq
    have hqm : q ∈ S0 := hq
    simp [g₁, g₂, hqm]
  let idPM : PointedMap Bool Bool := ⟨id, rfl⟩
  let T₀ : TM0.Machine Bool (Fin m) := M0.map idPM idPM g₁ g₂
  -- Layer 6: Binary BusyBeaver machine `B₀ := tm0ToBB T₀`
  let B₀ : BusyBeaver.Machine (Fin 2) (Fin (2 * m)) := tm0ToBB T₀
  -- Input bits for `c : Nat.Partrec.Code`
  let encSym : PartrecToTM2.Γ' → List (Fin 2) := fun x =>
    (enc (false, Function.update (fun _ => none) PartrecToTM2.K'.main (some x))).toList.map boolToFin2
  let encSymTop : PartrecToTM2.Γ' → List (Fin 2) := fun x =>
    (enc (true, Function.update (fun _ => none) PartrecToTM2.K'.main (some x))).toList.map boolToFin2
  let bitsOfNat : ℕ → List (Fin 2) := fun n =>
    encSymTop PartrecToTM2.Γ'.cons ++
      ((natBitsRec n).reverse.flatMap fun b =>
        encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0))
  let bitsOfCode : Nat.Partrec.Code → List (Fin 2) := fun c => bitsOfNat (Encodable.encode c)
  have hbits_eq : ∀ c : Nat.Partrec.Code,
      bitsOfCode c =
        ((TM2to1.trInit (Γ := fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
            PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode c])).flatMap
          fun x => (enc x).toList).map boolToFin2 := by
    intro c
    set n := Encodable.encode c
    have htr : PartrecToTM2.trList [n] =
        (natBitsRec n).map (fun b => if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ++
          [PartrecToTM2.Γ'.cons] := by
      simp [PartrecToTM2.trList, natBitsRec_eq_trNat]
    have htrInit : ∀ (a : PartrecToTM2.Γ') (l : List PartrecToTM2.Γ'),
        TM2to1.trInit (Γ := fun _ : PartrecToTM2.K' => PartrecToTM2.Γ') PartrecToTM2.K'.main (l ++ [a]) =
          (true, Function.update (fun _ => none) PartrecToTM2.K'.main (some a)) ::
            l.reverse.map (fun x => (false, Function.update (fun _ => none) PartrecToTM2.K'.main (some x))) := by
      intro a l
      unfold TM2to1.trInit
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      rfl
    have hflat_eq : ∀ l : List Bool,
        (l.flatMap fun b => encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0)) =
          ((l.map fun b => (false, Function.update (fun _ => none) PartrecToTM2.K'.main
            (some (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0)))).flatMap
            fun x => (enc x).toList).map boolToFin2 := by
      intro l; induction l with
      | nil => rfl
      | cons b l ih =>
        calc
          ((b :: l).flatMap fun b => encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0))
              = encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ++
                  (l.flatMap fun b => encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0)) := rfl
          _ = encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ++
                  ((l.map fun b => (false, Function.update (fun _ => none) PartrecToTM2.K'.main
                    (some (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0)))).flatMap
                    fun x => (enc x).toList).map boolToFin2 := by rw [ih]
          _ = (((b :: l).map fun b => (false, Function.update (fun _ => none) PartrecToTM2.K'.main
                (some (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0)))).flatMap
                fun x => (enc x).toList).map boolToFin2 := by
                change _ = ((enc _).toList ++ _).map boolToFin2
                rw [List.map_append]
                rfl
    rw [htr, htrInit]
    change encSymTop PartrecToTM2.Γ'.cons ++ _ =
      ((enc (true, Function.update (fun _ => none) PartrecToTM2.K'.main (some PartrecToTM2.Γ'.cons))).toList ++
        _).map boolToFin2
    rw [List.map_append]
    congr 1
    rw [← List.map_reverse, List.map_map]
    exact hflat_eq (natBitsRec n).reverse
  have hcomp : Computable bitsOfCode := by
    have hcomp_nat : Computable bitsOfNat := by
      have hflat : Primrec (fun l : List Bool =>
          l.flatMap fun b =>
            encSym (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0)) := by
        have hstep : Primrec (fun p : Bool × List (Fin 2) =>
            (if p.1 then encSym PartrecToTM2.Γ'.bit1 else encSym PartrecToTM2.Γ'.bit0) ++ p.2) :=
          Primrec.list_append.comp
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true))
              (Primrec.const (encSym PartrecToTM2.Γ'.bit1))
              (Primrec.const (encSym PartrecToTM2.Γ'.bit0)) |>.of_eq fun p => by cases p.1 <;> rfl)
            Primrec.snd
        exact (Primrec.list_foldr Primrec.id (Primrec.const ([] : List (Fin 2)))
          (hstep.comp (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun l => by
            induction l with
            | nil => rfl
            | cons b l ih =>
              simp only [id_eq, List.foldr_cons, List.flatMap_cons] at ih ⊢
              rw [ih]
              cases b <;> rfl
      refine Computable.list_append.comp (Computable.const _) ?_
      exact hflat.to_comp.comp (Primrec.list_reverse.to_comp.comp computable_natBitsRec)
    exact hcomp_nat.comp Computable.encode
  refine ⟨2 * m, inferInstance, B₀, bitsOfCode, hcomp, fun c => ?_⟩
  rw [prependBits_isHalting_iff, hbits_eq c, ← tm0ToBB_eval_dom_iff]
  set L1 := TM2to1.trInit (Γ := fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
    PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode c])
  set Lb := L1.flatMap fun x => (enc x).toList
  have hT0 : (TM0.eval T₀ Lb).Dom ↔ (TM0.eval M0 Lb).Dom := by
    have hresp := TM0.Machine.map_respects (M := M0) (f₁ := idPM) (f₂ := idPM) g₁ g₂
      hS0 (fun _ => rfl) hg₂₁
    have hinit : (TM0.init Lb).q ∈ (S0 : Set (TM1to0.Λ' M1b)) ∧
        TM0.Cfg.map idPM g₁ (TM0.init Lb) = TM0.init Lb := by
      refine ⟨hS0.1, ?_⟩
      simpa [idPM] using TM0.map_init (f₁ := idPM) g₁ Lb
    have hdom := StateTransition.tr_eval_dom hresp hinit
    simpa [TM0.eval] using hdom
  have hM0 : (TM0.eval M0 Lb).Dom ↔ (TM1.eval M1b Lb).Dom := by
    rw [TM1to0.tr_eval]
  have hM1b : (TM1.eval M1b Lb).Dom ↔ (TM1.eval M1 L1).Dom := by
    have hresp := TM1to1.tr_respects (enc := enc) (dec := dec) (enc0 := henc0) hencdec (M := M1)
    have hinit : TM1to1.trCfg enc henc0
        (TM1.init (Λ := TM2to1.Λ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ' (Option PartrecToTM2.Γ'))
          (σ := Option PartrecToTM2.Γ') L1) =
        TM1.init (Λ := TM1to1.Λ' Γ1 (TM2to1.Λ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ' (Option PartrecToTM2.Γ'))
          (Option PartrecToTM2.Γ')) (σ := Option PartrecToTM2.Γ') Lb :=
      congrArg (TM1.Cfg.mk (some default) default) (trTape_mk₁ henc0 L1)
    have hdom := StateTransition.tr_eval_dom hresp hinit
    simpa [TM1.eval] using hdom
  have hM1 : (TM1.eval M1 L1).Dom ↔
      (TM2.eval M2 PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode c])).Dom :=
    TM2to1.tr_eval_dom M2 PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode c])
  have hM2 : (TM2.eval M2 PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode c])).Dom ↔
      (u.eval [Encodable.encode c]).Dom := by
    have hinit_eq : TM2.init (Γ := fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
        (Λ := PartrecToTM2.Λ') (σ := Option PartrecToTM2.Γ')
        PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode c]) =
        PartrecToTM2.init u [Encodable.encode c] := by
      unfold TM2.init PartrecToTM2.init
      congr 1
      funext k
      cases k <;> simp [Function.update, PartrecToTM2.K'.elim]
    have hev := PartrecToTM2.tr_eval u [Encodable.encode c]
    change (Part.map _ (StateTransition.eval (TM2.step M2) (TM2.init _ _))).Dom ↔ _
    rw [hinit_eq, hev]
    simp [Part.map]
  rw [hT0, hM0, hM1b, hM1, hM2, hu c]

end C14H4Part3

namespace C14H4Part2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/- ## Section 2A: Raw `ℕ`-encoding of `ℒₛₑₜ` terms and formulas -/

/-- Encode a `Semiterm ℒₛₑₜ ℕ n` into `ℕ`: `#i ↦ 2 * i`, `&x ↦ 2 * x + 1`. -/
def encTerm {n : ℕ} : Semiterm ℒₛₑₜ ℕ n → ℕ
  | .bvar i => 2 * i.val
  | .fvar x => 2 * x + 1
  | .func f _ => f.elim

@[simp] lemma encTerm_bvar {n : ℕ} (i : Fin n) : encTerm (#i : Semiterm ℒₛₑₜ ℕ n) = 2 * i.val := rfl
@[simp] lemma encTerm_fvar {n : ℕ} (x : ℕ) : encTerm (&x : Semiterm ℒₛₑₜ ℕ n) = 2 * x + 1 := rfl

/-- Encode a `Semiformula ℒₛₑₜ ℕ n` into `ℕ`.
    Tags:
    0: verum, 1: falsum,
    2: rel eq, 3: rel mem, 4: nrel eq, 5: nrel mem,
    6: and, 7: or, 8: all, 9: exs.
    Note: for all compound tags `t ≥ 6`, every child code is strictly `< parent`. -/
def encForm : {n : ℕ} → Semiformula ℒₛₑₜ ℕ n → ℕ
  | _, .verum => Nat.pair 0 0
  | _, .falsum => Nat.pair 1 0
  | _, .rel .eq v => Nat.pair 2 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | _, .rel .mem v => Nat.pair 3 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | _, .nrel .eq v => Nat.pair 4 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | _, .nrel .mem v => Nat.pair 5 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
  | _, .and φ ψ => Nat.pair 6 (Nat.pair (encForm φ) (encForm ψ))
  | _, .or φ ψ => Nat.pair 7 (Nat.pair (encForm φ) (encForm ψ))
  | _, .all φ => Nat.pair 8 (encForm φ)
  | _, .exs φ => Nat.pair 9 (encForm φ)

def encSent {n : ℕ} (σ : Semisentence ℒₛₑₜ n) : ℕ :=
  encForm (Rewriting.emb σ : Semiproposition ℒₛₑₜ n)

lemma encTerm_inj {n : ℕ} {t₁ t₂ : Semiterm ℒₛₑₜ ℕ n} (h : encTerm t₁ = encTerm t₂) : t₁ = t₂ := by
  cases t₁ with
  | bvar i =>
    cases t₂ with
    | bvar j =>
      simp only [encTerm] at h
      exact congrArg Semiterm.bvar (Fin.ext (by omega))
    | fvar x => simp only [encTerm] at h; omega
    | func f _ => exact f.elim
  | fvar x =>
    cases t₂ with
    | bvar j => simp only [encTerm] at h; omega
    | fvar y =>
      simp only [encTerm] at h
      exact congrArg Semiterm.fvar (by omega)
    | func f _ => exact f.elim
  | func f _ => exact f.elim

lemma encForm_inj : ∀ {n : ℕ} {φ ψ : Semiformula ℒₛₑₜ ℕ n}, encForm φ = encForm ψ → φ = ψ
  | _, .verum, .verum, _ => rfl
  | _, .falsum, .falsum, _ => rfl
  | _, .rel .eq v₁, .rel .eq v₂, h => by
    have h2 := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
    congr 1; funext i; fin_cases i
    · exact encTerm_inj h2.1
    · exact encTerm_inj h2.2
  | _, .rel .mem v₁, .rel .mem v₂, h => by
    have h2 := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
    congr 1; funext i; fin_cases i
    · exact encTerm_inj h2.1
    · exact encTerm_inj h2.2
  | _, .nrel .eq v₁, .nrel .eq v₂, h => by
    have h2 := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
    congr 1; funext i; fin_cases i
    · exact encTerm_inj h2.1
    · exact encTerm_inj h2.2
  | _, .nrel .mem v₁, .nrel .mem v₂, h => by
    have h2 := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
    congr 1; funext i; fin_cases i
    · exact encTerm_inj h2.1
    · exact encTerm_inj h2.2
  | _, .and φ₁ ψ₁, .and φ₂ ψ₂, h => by
    have h2 := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
    rw [encForm_inj h2.1, encForm_inj h2.2]
  | _, .or φ₁ ψ₁, .or φ₂ ψ₂, h => by
    have h2 := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp h).2
    rw [encForm_inj h2.1, encForm_inj h2.2]
  | _, .all φ₁, .all φ₂, h => by
    rw [encForm_inj (Nat.pair_eq_pair.mp h).2]
  | _, .exs φ₁, .exs φ₂, h => by
    rw [encForm_inj (Nat.pair_eq_pair.mp h).2]
  | _, .verum, .falsum, h | _, .verum, .rel .eq _, h | _, .verum, .rel .mem _, h
  | _, .verum, .nrel .eq _, h | _, .verum, .nrel .mem _, h | _, .verum, .and _ _, h
  | _, .verum, .or _ _, h | _, .verum, .all _, h | _, .verum, .exs _, h
  | _, .falsum, .verum, h | _, .falsum, .rel .eq _, h | _, .falsum, .rel .mem _, h
  | _, .falsum, .nrel .eq _, h | _, .falsum, .nrel .mem _, h | _, .falsum, .and _ _, h
  | _, .falsum, .or _ _, h | _, .falsum, .all _, h | _, .falsum, .exs _, h
  | _, .rel .eq _, .verum, h | _, .rel .eq _, .falsum, h | _, .rel .eq _, .rel .mem _, h
  | _, .rel .eq _, .nrel .eq _, h | _, .rel .eq _, .nrel .mem _, h | _, .rel .eq _, .and _ _, h
  | _, .rel .eq _, .or _ _, h | _, .rel .eq _, .all _, h | _, .rel .eq _, .exs _, h
  | _, .rel .mem _, .verum, h | _, .rel .mem _, .falsum, h | _, .rel .mem _, .rel .eq _, h
  | _, .rel .mem _, .nrel .eq _, h | _, .rel .mem _, .nrel .mem _, h | _, .rel .mem _, .and _ _, h
  | _, .rel .mem _, .or _ _, h | _, .rel .mem _, .all _, h | _, .rel .mem _, .exs _, h
  | _, .nrel .eq _, .verum, h | _, .nrel .eq _, .falsum, h | _, .nrel .eq _, .rel .eq _, h
  | _, .nrel .eq _, .rel .mem _, h | _, .nrel .eq _, .nrel .mem _, h | _, .nrel .eq _, .and _ _, h
  | _, .nrel .eq _, .or _ _, h | _, .nrel .eq _, .all _, h | _, .nrel .eq _, .exs _, h
  | _, .nrel .mem _, .verum, h | _, .nrel .mem _, .falsum, h | _, .nrel .mem _, .rel .eq _, h
  | _, .nrel .mem _, .rel .mem _, h | _, .nrel .mem _, .nrel .eq _, h | _, .nrel .mem _, .and _ _, h
  | _, .nrel .mem _, .or _ _, h | _, .nrel .mem _, .all _, h | _, .nrel .mem _, .exs _, h
  | _, .and _ _, .verum, h | _, .and _ _, .falsum, h | _, .and _ _, .rel .eq _, h
  | _, .and _ _, .rel .mem _, h | _, .and _ _, .nrel .eq _, h | _, .and _ _, .nrel .mem _, h
  | _, .and _ _, .or _ _, h | _, .and _ _, .all _, h | _, .and _ _, .exs _, h
  | _, .or _ _, .verum, h | _, .or _ _, .falsum, h | _, .or _ _, .rel .eq _, h
  | _, .or _ _, .rel .mem _, h | _, .or _ _, .nrel .eq _, h | _, .or _ _, .nrel .mem _, h
  | _, .or _ _, .and _ _, h | _, .or _ _, .all _, h | _, .or _ _, .exs _, h
  | _, .all _, .verum, h | _, .all _, .falsum, h | _, .all _, .rel .eq _, h
  | _, .all _, .rel .mem _, h | _, .all _, .nrel .eq _, h | _, .all _, .nrel .mem _, h
  | _, .all _, .and _ _, h | _, .all _, .or _ _, h | _, .all _, .exs _, h
  | _, .exs _, .verum, h | _, .exs _, .falsum, h | _, .exs _, .rel .eq _, h
  | _, .exs _, .rel .mem _, h | _, .exs _, .nrel .eq _, h | _, .exs _, .nrel .mem _, h
  | _, .exs _, .and _ _, h | _, .exs _, .or _ _, h | _, .exs _, .all _, h =>
    absurd (Nat.pair_eq_pair.mp h).1 (by decide)

/- ## Section 2B: Generic `Primrec` strong-recursion combinator on `ℕ` -/

lemma lt_pair_of_pos_left {a b : ℕ} (ha : 1 ≤ a) : b < Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · nlinarith
  · nlinarith

lemma pair_lt_of_ge_two_left {t a b : ℕ} (ht : 2 ≤ t) :
    a < Nat.pair t (Nat.pair a b) ∧ b < Nat.pair t (Nat.pair a b) := by
  have h1 : Nat.pair a b < Nat.pair t (Nat.pair a b) := lt_pair_of_pos_left (by omega)
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair a b) h1, lt_of_le_of_lt (Nat.right_le_pair a b) h1⟩

/-- Bottom-up table builder: given `step : α → ℕ → List β → β` (where `tbl[i]` holds `f a i` for `i < k`),
    computes `[f a 0, f a 1, ..., f a (n - 1)]`. -/
def buildTable {α β : Type*} (step : α → ℕ → List β → β) (a : α) : ℕ → List β
  | 0 => []
  | n + 1 =>
    let tbl := buildTable step a n
    tbl ++ [step a n tbl]

lemma buildTable_length {α β : Type*} (step : α → ℕ → List β → β) (a : α) (n : ℕ) :
    (buildTable step a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildTable, ih]

lemma buildTable_getD {α β : Type*} [Inhabited β] (step : α → ℕ → List β → β) (a : α) :
    ∀ (n i : ℕ), i < n → (buildTable step a n).getD i default =
      step a i (buildTable step a i) := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [buildTable]
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [buildTable_length]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      exact ih i hlt
    · have heq : i = n := by omega
      subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [buildTable_length])]
      simp [buildTable_length]

lemma primrec_buildTable {α β : Type*} [Primcodable α] [Primcodable β]
    {step : α → ℕ → List β → β}
    (hstep : Primrec fun p : α × ℕ × List β => step p.1 p.2.1 p.2.2) :
    Primrec₂ (buildTable step) := by
  have hrec : Primrec₂ (fun a n =>
      Nat.rec (motive := fun _ => List β) ([] : List β) (fun k tbl => tbl ++ [step a k tbl]) n) :=
    Primrec.nat_rec (Primrec.const ([] : List β))
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp hstep (Primrec.const []))).to₂
  exact hrec.of_eq fun a n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [buildTable, ← ih]

/-- Evaluate a course-of-values recursive function `f : α → ℕ → β` defined by `step`! -/
def strongRecEval {α β : Type*} [Inhabited β] (step : α → ℕ → List β → β) (a : α) (n : ℕ) : β :=
  (buildTable step a (n + 1)).getD n default

lemma primrec_natPair : Primrec₂ Nat.pair := by
  exact (Primrec.encode (α := ℕ × ℕ)).to₂

lemma primrec_strongRecEval {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    {step : α → ℕ → List β → β}
    (hstep : Primrec fun p : α × ℕ × List β => step p.1 p.2.1 p.2.2) :
    Primrec₂ (strongRecEval step) := by
  have h1 : Primrec₂ (fun a n => GetElem?.getElem? (buildTable step a (n + 1)) n) :=
    Primrec.list_getElem?.comp ((primrec_buildTable hstep).comp Primrec.fst
      (Primrec.succ.comp Primrec.snd)) Primrec.snd
  have h2 : Primrec (fun o : Option β => o.getD default) :=
    Primrec.option_casesOn Primrec.id (Primrec.const default) Primrec₂.right |>.of_eq fun o => by
      cases o <;> rfl
  exact (h2.comp h1).of_eq fun p => by
    simp [strongRecEval, List.getD_eq_getElem?_getD]

lemma strongRecEval_eq {α β : Type*} [Inhabited β] (step : α → ℕ → List β → β) (a : α) (n : ℕ) :
    strongRecEval step a n = step a n (buildTable step a n) :=
  buildTable_getD step a (n + 1) n (Nat.lt_succ_self n)

lemma buildTable_getD_eq_strongRecEval {α β : Type*} [Inhabited β]
    (step : α → ℕ → List β → β) (a : α) {n i : ℕ} (hi : i < n) :
    (buildTable step a n).getD i default = strongRecEval step a i := by
  rw [buildTable_getD step a n i hi, strongRecEval_eq]

lemma buildTable_getD_zero_eq {α : Type*}
    (step : α → ℕ → List ℕ → ℕ) (a : α) {n i : ℕ} (hi : i < n) :
    (buildTable step a n).getD i 0 = strongRecEval step a i :=
  buildTable_getD_eq_strongRecEval step a hi

/- ## Section 2C: `Primrec` syntactic operations (`cNeg`, `cMapTerm`, `cShift`, `cFree`, `cSubst0`, `cFvSup`, `cFixitr`) -/

private def negStep (_ : Unit) (k : ℕ) (tbl : List ℕ) : ℕ :=
  let t := k.unpair.1
  let a := k.unpair.2
  if t = 0 then Nat.pair 1 0
  else if t = 1 then Nat.pair 0 0
  else if t = 2 then Nat.pair 4 a
  else if t = 3 then Nat.pair 5 a
  else if t = 4 then Nat.pair 2 a
  else if t = 5 then Nat.pair 3 a
  else if t = 6 then Nat.pair 7 (Nat.pair (tbl.getD a.unpair.1 0) (tbl.getD a.unpair.2 0))
  else if t = 7 then Nat.pair 6 (Nat.pair (tbl.getD a.unpair.1 0) (tbl.getD a.unpair.2 0))
  else if t = 8 then Nat.pair 9 (tbl.getD a 0)
  else if t = 9 then Nat.pair 8 (tbl.getD a 0)
  else 0

def cNeg (c : ℕ) : ℕ := strongRecEval negStep () c

lemma primrec_getD_nat : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l.getD i 0) :=
  (Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const 0) Primrec₂.right).of_eq fun p => by
    cases h : p.1[p.2]? <;> simp [List.getD_eq_getElem?_getD, h]

lemma primrec_cNeg : Primrec cNeg := by
  have hstep : Primrec (fun p : Unit × ℕ × List ℕ => negStep p.1 p.2.1 p.2.2) := by
    have ht : Primrec (fun p : Unit × ℕ × List ℕ => p.2.1.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have ha : Primrec (fun p : Unit × ℕ × List ℕ => p.2.1.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have htbl : Primrec (fun p : Unit × ℕ × List ℕ => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    have ha1 : Primrec (fun p : Unit × ℕ × List ℕ => p.2.1.unpair.2.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp ha)
    have ha2 : Primrec (fun p : Unit × ℕ × List ℕ => p.2.1.unpair.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp ha)
    unfold negStep
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) (primrec_natPair.comp (Primrec.const 4) ha) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) (primrec_natPair.comp (Primrec.const 5) ha) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) (primrec_natPair.comp (Primrec.const 2) ha) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 5)) (primrec_natPair.comp (Primrec.const 3) ha) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 6))
      (primrec_natPair.comp (Primrec.const 7) (primrec_natPair.comp (primrec_getD_nat.comp htbl ha1) (primrec_getD_nat.comp htbl ha2))) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 7))
      (primrec_natPair.comp (Primrec.const 6) (primrec_natPair.comp (primrec_getD_nat.comp htbl ha1) (primrec_getD_nat.comp htbl ha2))) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 8))
      (primrec_natPair.comp (Primrec.const 9) (primrec_getD_nat.comp htbl ha)) ?_
    refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 9))
      (primrec_natPair.comp (Primrec.const 8) (primrec_getD_nat.comp htbl ha)) (Primrec.const 0)
  exact (primrec_strongRecEval hstep).comp (Primrec.const ()) Primrec.id

lemma cNeg_encForm : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n), cNeg (encForm φ) = encForm (∼φ)
  | _, .verum => by
    change strongRecEval negStep () (Nat.pair 0 0) = Nat.pair 1 0
    rw [strongRecEval_eq]; simp [negStep]
  | _, .falsum => by
    change strongRecEval negStep () (Nat.pair 1 0) = Nat.pair 0 0
    rw [strongRecEval_eq]; simp [negStep]
  | _, .rel .eq v => by
    change strongRecEval negStep () (Nat.pair 2 _) = Nat.pair 4 _
    rw [strongRecEval_eq]; simp [negStep]
  | _, .rel .mem v => by
    change strongRecEval negStep () (Nat.pair 3 _) = Nat.pair 5 _
    rw [strongRecEval_eq]; simp [negStep]
  | _, .nrel .eq v => by
    change strongRecEval negStep () (Nat.pair 4 _) = Nat.pair 2 _
    rw [strongRecEval_eq]; simp [negStep]
  | _, .nrel .mem v => by
    change strongRecEval negStep () (Nat.pair 5 _) = Nat.pair 3 _
    rw [strongRecEval_eq]; simp [negStep]
  | _, .and φ ψ => by
    have hlt := pair_lt_of_ge_two_left (t := 6) (a := encForm φ) (b := encForm ψ) (by decide)
    rw [cNeg, strongRecEval_eq]
    simp only [negStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero, ↓reduceIte,
      show (6 : ℕ) ≠ 1 by decide, show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide,
      show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide]
    rw [buildTable_getD_zero_eq _ _ hlt.1, buildTable_getD_zero_eq _ _ hlt.2]
    change Nat.pair 7 (Nat.pair (cNeg (encForm φ)) (cNeg (encForm ψ))) = _
    rw [cNeg_encForm φ, cNeg_encForm ψ]
    rfl
  | _, .or φ ψ => by
    have hlt := pair_lt_of_ge_two_left (t := 7) (a := encForm φ) (b := encForm ψ) (by decide)
    rw [cNeg, strongRecEval_eq]
    simp only [negStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero, ↓reduceIte,
      show (7 : ℕ) ≠ 1 by decide, show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide,
      show (7 : ℕ) ≠ 4 by decide, show (7 : ℕ) ≠ 5 by decide, show (7 : ℕ) ≠ 6 by decide]
    rw [buildTable_getD_zero_eq _ _ hlt.1, buildTable_getD_zero_eq _ _ hlt.2]
    change Nat.pair 6 (Nat.pair (cNeg (encForm φ)) (cNeg (encForm ψ))) = _
    rw [cNeg_encForm φ, cNeg_encForm ψ]
    rfl
  | _, .all φ => by
    have hlt : encForm φ < Nat.pair 8 (encForm φ) := lt_pair_of_pos_left (by decide)
    rw [cNeg, strongRecEval_eq]
    simp only [negStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero, ↓reduceIte,
      show (8 : ℕ) ≠ 1 by decide, show (8 : ℕ) ≠ 2 by decide, show (8 : ℕ) ≠ 3 by decide,
      show (8 : ℕ) ≠ 4 by decide, show (8 : ℕ) ≠ 5 by decide, show (8 : ℕ) ≠ 6 by decide,
      show (8 : ℕ) ≠ 7 by decide]
    rw [buildTable_getD_zero_eq _ _ hlt]
    change Nat.pair 9 (cNeg (encForm φ)) = _
    rw [cNeg_encForm φ]
    rfl
  | _, .exs φ => by
    have hlt : encForm φ < Nat.pair 9 (encForm φ) := lt_pair_of_pos_left (by decide)
    rw [cNeg, strongRecEval_eq]
    simp only [negStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero, ↓reduceIte,
      show (9 : ℕ) ≠ 1 by decide, show (9 : ℕ) ≠ 2 by decide, show (9 : ℕ) ≠ 3 by decide,
      show (9 : ℕ) ≠ 4 by decide, show (9 : ℕ) ≠ 5 by decide, show (9 : ℕ) ≠ 6 by decide,
      show (9 : ℕ) ≠ 7 by decide, show (9 : ℕ) ≠ 8 by decide]
    rw [buildTable_getD_zero_eq _ _ hlt]
    change Nat.pair 8 (cNeg (encForm φ)) = _
    rw [cNeg_encForm φ]
    rfl

/- ## Section 2D: Generic `Primrec` rewriting (`cRew`), `cFvSup`, `cIsWf`, `cUnivCl` -/

lemma primrec_list_range : Primrec List.range := by
  have hrec : Primrec₂ (fun (_ : Unit) (n : ℕ) =>
      Nat.rec (motive := fun _ => List ℕ) ([] : List ℕ) (fun k ih => ih ++ [k]) n) :=
    Primrec.nat_rec (Primrec.const ([] : List ℕ))
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const ([] : List ℕ)))).to₂
  exact (hrec.comp (Primrec.const ()) Primrec.id).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [id_eq] at ih ⊢
      simp [List.range_succ, ih]

lemma primrec_getD_listNat : Primrec₂ (fun (l : List (List ℕ)) (i : ℕ) => l.getD i []) :=
  (Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const ([] : List ℕ)) Primrec₂.right).of_eq fun p => by
    cases h : p.1[p.2]? <;> simp [List.getD_eq_getElem?_getD, h]

lemma primrec_mod : Primrec₂ (· % · : ℕ → ℕ → ℕ) := Primrec.nat_mod
lemma primrec_div : Primrec₂ (· / · : ℕ → ℕ → ℕ) := Primrec.nat_div

def cBShiftN (d u : ℕ) : ℕ := if u % 2 = 0 then u + 2 * d else u

lemma primrec_cBShiftN : Primrec₂ cBShiftN := by
  unfold cBShiftN
  refine Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    (Primrec.nat_add.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))
    Primrec.snd

lemma cBShiftN_zero (u : ℕ) : cBShiftN 0 u = u := by
  simp [cBShiftN]

lemma cBShiftN_add (d₁ d₂ u : ℕ) : cBShiftN d₁ (cBShiftN d₂ u) = cBShiftN (d₁ + d₂) u := by
  unfold cBShiftN
  split_ifs with h1 h2 h3 <;> omega

@[simp] lemma rew_bind_bvar {n₁ n₂ : ℕ} (b : Fin n₁ → Semiterm ℒₛₑₜ ℕ n₂) (e : ℕ → Semiterm ℒₛₑₜ ℕ n₂)
    (i : Fin n₁) : Rew.bind b e (#i) = b i := rfl

@[simp] lemma rew_bind_fvar {n₁ n₂ : ℕ} (b : Fin n₁ → Semiterm ℒₛₑₜ ℕ n₂) (e : ℕ → Semiterm ℒₛₑₜ ℕ n₂)
    (x : ℕ) : Rew.bind b e (&x) = e x := rfl

lemma encTerm_bShift {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) :
    encTerm (Rew.bShift t) = cBShiftN 1 (encTerm t) := by
  cases t with
  | bvar i =>
    change 2 * (i.val + 1) = cBShiftN 1 (2 * i.val)
    unfold cBShiftN
    split_ifs <;> omega
  | fvar x =>
    change 2 * x + 1 = cBShiftN 1 (2 * x + 1)
    unfold cBShiftN
    split_ifs <;> omega
  | func f _ => exact Empty.elim f

def cRewTerm {α : Type*} (fb ff : α → ℕ → ℕ) (a : α) (d u : ℕ) : ℕ :=
  if u % 2 = 0 then
    if u / 2 < d then u else cBShiftN d (fb a (u / 2 - d))
  else
    cBShiftN d (ff a (u / 2))

lemma primrec_cRewTerm {α : Type*} [Primcodable α] {fb ff : α → ℕ → ℕ}
    (hfb : Primrec₂ fb) (hff : Primrec₂ ff) :
    Primrec (fun p : α × ℕ × ℕ => cRewTerm fb ff p.1 p.2.1 p.2.2) := by
  have ha : Primrec (fun p : α × ℕ × ℕ => p.1) := Primrec.fst
  have hd : Primrec (fun p : α × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hu : Primrec (fun p : α × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hu2 : Primrec (fun p : α × ℕ × ℕ => p.2.2 / 2) := Primrec.nat_div.comp hu (Primrec.const 2)
  unfold cRewTerm
  refine Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hu (Primrec.const 2)) (Primrec.const 0)) ?_ ?_
  · refine Primrec.ite (Primrec.nat_lt.comp hu2 hd) hu
      (primrec_cBShiftN.comp hd (hfb.comp ha (Primrec.nat_sub.comp hu2 hd)))
  · exact primrec_cBShiftN.comp hd (hff.comp ha hu2)

lemma cRewTerm_q {α : Type*} {fb ff : α → ℕ → ℕ} {a : α} {n₁ n₂ d : ℕ}
    {ω : Rew ℒₛₑₜ ℕ n₁ ℕ n₂}
    (hω : ∀ t : Semiterm ℒₛₑₜ ℕ n₁, encTerm (ω t) = cRewTerm fb ff a d (encTerm t)) :
    ∀ t : Semiterm ℒₛₑₜ ℕ (n₁ + 1), encTerm (ω.q t) = cRewTerm fb ff a (d + 1) (encTerm t) := by
  intro t
  cases t with
  | bvar i =>
    cases i using Fin.cases with
    | zero =>
      change 0 = cRewTerm fb ff a (d + 1) 0
      simp [cRewTerm]
    | succ j =>
      have hj := hω (#j)
      have hqj : ω.q (#j.succ) = Rew.bShift (ω #j) := rfl
      rw [hqj, encTerm_bShift, hj]
      simp only [encTerm, cRewTerm, Fin.val_succ]
      have hmod1 : 2 * j.val % 2 = 0 := by omega
      have hmod2 : 2 * (j.val + 1) % 2 = 0 := by omega
      have hdiv1 : 2 * j.val / 2 = j.val := by omega
      have hdiv2 : 2 * (j.val + 1) / 2 = j.val + 1 := by omega
      simp only [hmod1, hmod2, hdiv1, hdiv2, ↓reduceIte]
      by_cases hjd : j.val < d
      · have hjd' : j.val + 1 < d + 1 := by omega
        rw [if_pos hjd, if_pos hjd']
        unfold cBShiftN
        rw [if_pos hmod1]
        omega
      · have hjd' : ¬ j.val + 1 < d + 1 := by omega
        rw [if_neg hjd, if_neg hjd', cBShiftN_add]
        have hsub : j.val + 1 - (d + 1) = j.val - d := by omega
        have hadd : 1 + d = d + 1 := by omega
        rw [hsub, hadd]
  | fvar x =>
    have hx := hω (&x)
    have hqx : ω.q (&x) = Rew.bShift (ω &x) := rfl
    rw [hqx, encTerm_bShift, hx]
    change cBShiftN 1 (cRewTerm fb ff a d (2 * x + 1)) = cRewTerm fb ff a (d + 1) (2 * x + 1)
    unfold cRewTerm
    have hmod : (2 * x + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * x + 1) / 2 = x := by omega
    rw [if_neg hmod, if_neg hmod, hdiv, cBShiftN_add, Nat.add_comm 1 d]
  | func f _ => exact Empty.elim f

private def rewStep {α : Type*} (fb ff : α → ℕ → ℕ) (p : α × ℕ) (k : ℕ)
    (tbl : List (List ℕ)) : List ℕ :=
  let a := p.1
  let M := p.2
  let t := k.unpair.1
  let arg := k.unpair.2
  (List.range (M + 1)).map fun d =>
    if t = 0 then Nat.pair 0 0
    else if t = 1 then Nat.pair 1 0
    else if t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 then
      Nat.pair t (Nat.pair (cRewTerm fb ff a d arg.unpair.1) (cRewTerm fb ff a d arg.unpair.2))
    else if t = 6 ∨ t = 7 then
      Nat.pair t (Nat.pair ((tbl.getD arg.unpair.1 []).getD d 0) ((tbl.getD arg.unpair.2 []).getD d 0))
    else if t = 8 ∨ t = 9 then
      Nat.pair t ((tbl.getD arg []).getD (d + 1) 0)
    else 0

def cRewAt {α : Type*} (fb ff : α → ℕ → ℕ) (a : α) (M c d : ℕ) : ℕ :=
  (strongRecEval (rewStep fb ff) (a, M) c).getD d 0

def cRew {α : Type*} (fb ff : α → ℕ → ℕ) (a : α) (c : ℕ) : ℕ :=
  cRewAt fb ff a c c 0

lemma primrec_cRewAt {α : Type*} [Primcodable α] {fb ff : α → ℕ → ℕ}
    (hfb : Primrec₂ fb) (hff : Primrec₂ ff) :
    Primrec (fun q : (α × ℕ) × ℕ × ℕ => cRewAt fb ff q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hstep : Primrec (fun p : (α × ℕ) × ℕ × List (List ℕ) => rewStep fb ff p.1 p.2.1 p.2.2) := by
    let P := (α × ℕ) × ℕ × List (List ℕ)
    have hbody : Primrec₂ (fun (p : P) (d : ℕ) =>
        let a := p.1.1
        let t := p.2.1.unpair.1
        let arg := p.2.1.unpair.2
        let tbl := p.2.2
        if t = 0 then Nat.pair 0 0
        else if t = 1 then Nat.pair 1 0
        else if t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 then
          Nat.pair t (Nat.pair (cRewTerm fb ff a d arg.unpair.1) (cRewTerm fb ff a d arg.unpair.2))
        else if t = 6 ∨ t = 7 then
          Nat.pair t (Nat.pair ((tbl.getD arg.unpair.1 []).getD d 0) ((tbl.getD arg.unpair.2 []).getD d 0))
        else if t = 8 ∨ t = 9 then
          Nat.pair t ((tbl.getD arg []).getD (d + 1) 0)
        else 0) := by
      have ha : Primrec (fun q : P × ℕ => q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
      have hd : Primrec (fun q : P × ℕ => q.2) := Primrec.snd
      have ht : Primrec (fun q : P × ℕ => q.1.2.1.unpair.1) :=
        Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      have harg : Primrec (fun q : P × ℕ => q.1.2.1.unpair.2) :=
        Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      have ha1 : Primrec (fun q : P × ℕ => q.1.2.1.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp harg)
      have ha2 : Primrec (fun q : P × ℕ => q.1.2.1.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp harg)
      have htbl : Primrec (fun q : P × ℕ => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      have hrt := primrec_cRewTerm hfb hff
      refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (Primrec.const _) ?_
      refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) (Primrec.const _) ?_
      have h25 : PrimrecPred (fun q : P × ℕ =>
          q.1.2.1.unpair.1 = 2 ∨ q.1.2.1.unpair.1 = 3 ∨ q.1.2.1.unpair.1 = 4 ∨ q.1.2.1.unpair.1 = 5) :=
        (Primrec.eq.comp ht (Primrec.const 2)).or
          ((Primrec.eq.comp ht (Primrec.const 3)).or
            ((Primrec.eq.comp ht (Primrec.const 4)).or (Primrec.eq.comp ht (Primrec.const 5))))
      refine Primrec.ite h25
        (primrec_natPair.comp ht (primrec_natPair.comp
          (hrt.comp (Primrec.pair ha (Primrec.pair hd ha1)))
          (hrt.comp (Primrec.pair ha (Primrec.pair hd ha2))))) ?_
      have h67 : PrimrecPred (fun q : P × ℕ => q.1.2.1.unpair.1 = 6 ∨ q.1.2.1.unpair.1 = 7) :=
        (Primrec.eq.comp ht (Primrec.const 6)).or (Primrec.eq.comp ht (Primrec.const 7))
      refine Primrec.ite h67
        (primrec_natPair.comp ht (primrec_natPair.comp
          (primrec_getD_nat.comp (primrec_getD_listNat.comp htbl ha1) hd)
          (primrec_getD_nat.comp (primrec_getD_listNat.comp htbl ha2) hd))) ?_
      have h89 : PrimrecPred (fun q : P × ℕ => q.1.2.1.unpair.1 = 8 ∨ q.1.2.1.unpair.1 = 9) :=
        (Primrec.eq.comp ht (Primrec.const 8)).or (Primrec.eq.comp ht (Primrec.const 9))
      refine Primrec.ite h89
        (primrec_natPair.comp ht
          (primrec_getD_nat.comp (primrec_getD_listNat.comp htbl harg) (Primrec.succ.comp hd)))
        (Primrec.const 0)
    exact Primrec.list_map
      (primrec_list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)))
      hbody
  exact primrec_getD_nat.comp
    ((primrec_strongRecEval hstep).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

lemma primrec_cRew {α : Type*} [Primcodable α] {fb ff : α → ℕ → ℕ}
    (hfb : Primrec₂ fb) (hff : Primrec₂ ff) : Primrec₂ (cRew fb ff) := by
  exact (primrec_cRewAt hfb hff).comp
    (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd) (Primrec.pair Primrec.snd (Primrec.const 0)))

lemma cRewAt_encForm {α : Type*} {fb ff : α → ℕ → ℕ} {a : α} {M : ℕ} :
    ∀ {n₁ n₂ : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n₁) (ω : Rew ℒₛₑₜ ℕ n₁ ℕ n₂) (d : ℕ),
      d + encForm φ ≤ M →
      (∀ t : Semiterm ℒₛₑₜ ℕ n₁, encTerm (ω t) = cRewTerm fb ff a d (encTerm t)) →
      cRewAt fb ff a M (encForm φ) d = encForm (Semiformula.rewAux ω φ)
  | _, _, .verum, ω, d, hM, _ => by
    rw [cRewAt, strongRecEval_eq]
    have hd : d < M + 1 := by omega
    simp [rewStep, encForm, Semiformula.rewAux, List.getD_eq_getElem?_getD, hd]
  | _, _, .falsum, ω, d, hM, _ => by
    rw [cRewAt, strongRecEval_eq]
    have hd : d < M + 1 := by omega
    simp [rewStep, encForm, Semiformula.rewAux, List.getD_eq_getElem?_getD, hd]
  | _, _, .rel .eq v, ω, d, hM, hω => by
    rw [cRewAt, strongRecEval_eq]
    have hd : d < M + 1 := by omega
    simp [rewStep, encForm, Semiformula.rewAux, List.getD_eq_getElem?_getD, hd, hω]
  | _, _, .rel .mem v, ω, d, hM, hω => by
    rw [cRewAt, strongRecEval_eq]
    have hd : d < M + 1 := by omega
    simp [rewStep, encForm, Semiformula.rewAux, List.getD_eq_getElem?_getD, hd, hω]
  | _, _, .nrel .eq v, ω, d, hM, hω => by
    rw [cRewAt, strongRecEval_eq]
    have hd : d < M + 1 := by omega
    simp [rewStep, encForm, Semiformula.rewAux, List.getD_eq_getElem?_getD, hd, hω]
  | _, _, .nrel .mem v, ω, d, hM, hω => by
    rw [cRewAt, strongRecEval_eq]
    have hd : d < M + 1 := by omega
    simp [rewStep, encForm, Semiformula.rewAux, List.getD_eq_getElem?_getD, hd, hω]
  | _, _, .and φ ψ, ω, d, hM, hω => by
    have hlt := pair_lt_of_ge_two_left (t := 6) (a := encForm φ) (b := encForm ψ) (by decide)
    have hd : d < M + 1 := by omega
    rw [cRewAt, strongRecEval_eq]
    simp only [rewStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hd, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (6 : ℕ) ≠ 1 by decide, show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide,
      or_self, true_or, ↓reduceIte]
    change Nat.pair 6 (Nat.pair (((buildTable (rewStep fb ff) (a, M) _).getD (encForm φ) default).getD d 0)
      (((buildTable (rewStep fb ff) (a, M) _).getD (encForm ψ) default).getD d 0)) = _
    rw [buildTable_getD_eq_strongRecEval (rewStep fb ff) (a, M) hlt.1,
        buildTable_getD_eq_strongRecEval (rewStep fb ff) (a, M) hlt.2]
    change Nat.pair 6 (Nat.pair (cRewAt fb ff a M (encForm φ) d) (cRewAt fb ff a M (encForm ψ) d)) = _
    rw [cRewAt_encForm φ ω d (by simp only [encForm] at hM; omega) hω,
        cRewAt_encForm ψ ω d (by simp only [encForm] at hM; omega) hω]
    rfl
  | _, _, .or φ ψ, ω, d, hM, hω => by
    have hlt := pair_lt_of_ge_two_left (t := 7) (a := encForm φ) (b := encForm ψ) (by decide)
    have hd : d < M + 1 := by omega
    rw [cRewAt, strongRecEval_eq]
    simp only [rewStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hd, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (7 : ℕ) ≠ 1 by decide, show (7 : ℕ) ≠ 2 by decide,
      show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 4 by decide, show (7 : ℕ) ≠ 5 by decide,
      show (7 : ℕ) ≠ 6 by decide, or_self, or_true, ↓reduceIte]
    change Nat.pair 7 (Nat.pair (((buildTable (rewStep fb ff) (a, M) _).getD (encForm φ) default).getD d 0)
      (((buildTable (rewStep fb ff) (a, M) _).getD (encForm ψ) default).getD d 0)) = _
    rw [buildTable_getD_eq_strongRecEval (rewStep fb ff) (a, M) hlt.1,
        buildTable_getD_eq_strongRecEval (rewStep fb ff) (a, M) hlt.2]
    change Nat.pair 7 (Nat.pair (cRewAt fb ff a M (encForm φ) d) (cRewAt fb ff a M (encForm ψ) d)) = _
    rw [cRewAt_encForm φ ω d (by simp only [encForm] at hM; omega) hω,
        cRewAt_encForm ψ ω d (by simp only [encForm] at hM; omega) hω]
    rfl
  | _, _, .all φ, ω, d, hM, hω => by
    have hlt : encForm φ < Nat.pair 8 (encForm φ) := lt_pair_of_pos_left (by decide)
    have hd : d < M + 1 := by omega
    rw [cRewAt, strongRecEval_eq]
    simp only [rewStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hd, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (8 : ℕ) ≠ 1 by decide, show (8 : ℕ) ≠ 2 by decide,
      show (8 : ℕ) ≠ 3 by decide, show (8 : ℕ) ≠ 4 by decide, show (8 : ℕ) ≠ 5 by decide,
      show (8 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 7 by decide, or_self, true_or, ↓reduceIte]
    change Nat.pair 8 (((buildTable (rewStep fb ff) (a, M) _).getD (encForm φ) default).getD (d + 1) 0) = _
    rw [buildTable_getD_eq_strongRecEval (rewStep fb ff) (a, M) hlt]
    change Nat.pair 8 (cRewAt fb ff a M (encForm φ) (d + 1)) = _
    rw [cRewAt_encForm φ ω.q (d + 1) (by simp only [encForm] at hM; omega) (cRewTerm_q hω)]
    rfl
  | _, _, .exs φ, ω, d, hM, hω => by
    have hlt : encForm φ < Nat.pair 9 (encForm φ) := lt_pair_of_pos_left (by decide)
    have hd : d < M + 1 := by omega
    rw [cRewAt, strongRecEval_eq]
    simp only [rewStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hd, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (9 : ℕ) ≠ 1 by decide, show (9 : ℕ) ≠ 2 by decide,
      show (9 : ℕ) ≠ 3 by decide, show (9 : ℕ) ≠ 4 by decide, show (9 : ℕ) ≠ 5 by decide,
      show (9 : ℕ) ≠ 6 by decide, show (9 : ℕ) ≠ 7 by decide, show (9 : ℕ) ≠ 8 by decide,
      or_self, or_true, ↓reduceIte]
    change Nat.pair 9 (((buildTable (rewStep fb ff) (a, M) _).getD (encForm φ) default).getD (d + 1) 0) = _
    rw [buildTable_getD_eq_strongRecEval (rewStep fb ff) (a, M) hlt]
    change Nat.pair 9 (cRewAt fb ff a M (encForm φ) (d + 1)) = _
    rw [cRewAt_encForm φ ω.q (d + 1) (by simp only [encForm] at hM; omega) (cRewTerm_q hω)]
    rfl

lemma cRew_encForm {α : Type*} {fb ff : α → ℕ → ℕ} {a : α} {n₁ n₂ : ℕ}
    (φ : Semiformula ℒₛₑₜ ℕ n₁) (ω : Rew ℒₛₑₜ ℕ n₁ ℕ n₂)
    (hb : ∀ i : Fin n₁, encTerm (ω #i) = fb a i.val)
    (hf : ∀ x : ℕ, encTerm (ω &x) = ff a x) :
    cRew fb ff a (encForm φ) = encForm (ω ▹ φ) := by
  refine cRewAt_encForm φ ω 0 (by omega) fun t => ?_
  cases t with
  | bvar i =>
    simp only [encTerm, cRewTerm, cBShiftN_zero]
    have hmod : 2 * (i : ℕ) % 2 = 0 := by omega
    have hdiv : 2 * (i : ℕ) / 2 = (i : ℕ) := by omega
    rw [if_pos hmod, if_neg (Nat.not_lt_zero _), hdiv, Nat.sub_zero]
    exact hb i
  | fvar x =>
    simp only [encTerm, cRewTerm, cBShiftN_zero]
    have hmod : (2 * x + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * x + 1) / 2 = x := by omega
    rw [if_neg hmod, hdiv]
    exact hf x
  | func f _ => exact Empty.elim f

/- Specializations of `cRew`: `cShift`, `cFree`, `cSubst0`, `cFix`, `cFixitr`, `cSubstList` -/

def cShift (c : ℕ) : ℕ := cRew (fun (_ : Unit) i => 2 * i) (fun (_ : Unit) x => 2 * (x + 1) + 1) () c

lemma primrec_cShift : Primrec cShift :=
  Primrec₂.comp
    (primrec_cRew
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp Primrec.snd))))
    (Primrec.const ()) Primrec.id

lemma cShift_encForm {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    cShift (encForm φ) = encForm (Rewriting.shift φ) :=
  cRew_encForm φ Rew.shift
    (fun _ => by simp only [Rew.shift, Rew.map, rew_bind_bvar]; simp [encTerm])
    (fun _ => by simp only [Rew.shift, Rew.map, rew_bind_fvar]; simp [encTerm])

def cFree (c : ℕ) : ℕ :=
  cRew (fun (_ : Unit) _ => 1) (fun (_ : Unit) x => 2 * (x + 1) + 1) () c

lemma primrec_cFree : Primrec cFree :=
  Primrec₂.comp
    (primrec_cRew
      (Primrec.const 1)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp Primrec.snd))))
    (Primrec.const ()) Primrec.id

lemma cFree_encForm (φ : Semiproposition ℒₛₑₜ 1) :
    cFree (encForm φ) = encForm (Semiformula.free φ) :=
  cRew_encForm φ Rew.free
    (fun i => by fin_cases i; simp only [Rew.free, rew_bind_bvar]; rfl)
    (fun _ => by simp only [Rew.free, rew_bind_fvar, encTerm_fvar])

def cSubst0 (x c : ℕ) : ℕ :=
  cRew (fun (x : ℕ) _ => 2 * x + 1) (fun (_ : ℕ) y => 2 * y + 1) x c

lemma primrec_cSubst0 : Primrec₂ cSubst0 :=
  primrec_cRew
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))

lemma cSubst0_encForm (φ : Semiproposition ℒₛₑₜ 1) (x : ℕ) :
    cSubst0 x (encForm φ) = encForm (φ/[(&x : Semiterm ℒₛₑₜ ℕ 0)]) :=
  cRew_encForm φ (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 1) (n' := 0) (![(&x : Semiterm ℒₛₑₜ ℕ 0)]))
    (fun i => by fin_cases i; simp only [Rew.subst, rew_bind_bvar]; simp)
    (fun _ => by simp only [Rew.subst, rew_bind_fvar, encTerm_fvar])

def cFix (n c : ℕ) : ℕ :=
  cRew (fun (_ : ℕ) i => 2 * i) (fun (n : ℕ) x => if x = 0 then 2 * n else 2 * (x - 1) + 1) n c

lemma primrec_cFix : Primrec₂ cFix :=
  primrec_cRew
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))))

lemma cFix_encForm {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) :
    cFix n (encForm φ) = encForm (Rew.fix ▹ φ) :=
  cRew_encForm φ Rew.fix
    (fun _ => by simp only [Rew.fix, rew_bind_bvar, encTerm_bvar, Fin.val_castSucc])
    (fun x => by
      cases x with
      | zero => simp only [Rew.fix, rew_bind_fvar]; rfl
      | succ y => simp only [Rew.fix, rew_bind_fvar]; rfl)

def cFixitr (n m c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) c (fun k acc => cFix (n + k) acc) m

lemma primrec_cFixitr : Primrec (fun p : ℕ × ℕ × ℕ => cFixitr p.1 p.2.1 p.2.2) := by
  have hrec : Primrec₂ (fun (a : ℕ × ℕ) (m : ℕ) =>
      Nat.rec (motive := fun _ => ℕ) a.2 (fun k acc => cFix (a.1 + k) acc) m) :=
    Primrec.nat_rec Primrec.snd
      (primrec_cFix.comp
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  exact hrec.comp (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd)

lemma rew_ext {n₁ n₂ : ℕ} {ω₁ ω₂ : Rew ℒₛₑₜ ℕ n₁ ℕ n₂}
    (hb : ∀ i : Fin n₁, ω₁ #i = ω₂ #i) (hf : ∀ x : ℕ, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  apply DFunLike.coe_injective
  funext t
  cases t with
  | bvar i => exact hb i
  | fvar x => exact hf x
  | func f _ => exact Empty.elim f

lemma rewAux_id_eq : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n),
    Semiformula.rewAux Rew.id φ = φ
  | _, .verum => rfl
  | _, .falsum => rfl
  | _, .rel _ _ => rfl
  | _, .nrel _ _ => rfl
  | _, .and φ ψ => by
    change Semiformula.and (Semiformula.rewAux Rew.id φ) (Semiformula.rewAux Rew.id ψ) = Semiformula.and φ ψ
    rw [rewAux_id_eq φ, rewAux_id_eq ψ]
  | _, .or φ ψ => by
    change Semiformula.or (Semiformula.rewAux Rew.id φ) (Semiformula.rewAux Rew.id ψ) = Semiformula.or φ ψ
    rw [rewAux_id_eq φ, rewAux_id_eq ψ]
  | n, .all φ => by
    change Semiformula.all (Semiformula.rewAux Rew.id.q φ) = Semiformula.all φ
    have hq : (Rew.id (L := ℒₛₑₜ) (ξ := ℕ) (n := n)).q = Rew.id :=
      rew_ext
        (fun i => by
          cases i using Fin.cases with
          | zero => simp only [Rew.q, rew_bind_bvar, Matrix.cons_val_zero]; rfl
          | succ j => simp only [Rew.q, rew_bind_bvar, Matrix.cons_val_succ, Function.comp_apply]; rfl)
        (fun _ => by simp only [Rew.q, rew_bind_fvar, Function.comp_apply]; rfl)
    rw [hq, rewAux_id_eq φ]
  | n, .exs φ => by
    change Semiformula.exs (Semiformula.rewAux Rew.id.q φ) = Semiformula.exs φ
    have hq : (Rew.id (L := ℒₛₑₜ) (ξ := ℕ) (n := n)).q = Rew.id :=
      rew_ext
        (fun i => by
          cases i using Fin.cases with
          | zero => simp only [Rew.q, rew_bind_bvar, Matrix.cons_val_zero]; rfl
          | succ j => simp only [Rew.q, rew_bind_bvar, Matrix.cons_val_succ, Function.comp_apply]; rfl)
        (fun _ => by simp only [Rew.q, rew_bind_fvar, Function.comp_apply]; rfl)
    rw [hq, rewAux_id_eq φ]

lemma rewAux_comp_eq {n₁ n₂ n₃ : ℕ} (ω₂ : Rew ℒₛₑₜ ℕ n₂ ℕ n₃) (ω₁ : Rew ℒₛₑₜ ℕ n₁ ℕ n₂) :
    ∀ (φ : Semiformula ℒₛₑₜ ℕ n₁),
      Semiformula.rewAux ω₂ (Semiformula.rewAux ω₁ φ) = Semiformula.rewAux (ω₂.comp ω₁) φ
  | .verum => rfl
  | .falsum => rfl
  | .rel _ _ => rfl
  | .nrel _ _ => rfl
  | .and φ ψ => by
    change Semiformula.and _ _ = Semiformula.and _ _
    rw [rewAux_comp_eq ω₂ ω₁ φ, rewAux_comp_eq ω₂ ω₁ ψ]
  | .or φ ψ => by
    change Semiformula.or _ _ = Semiformula.or _ _
    rw [rewAux_comp_eq ω₂ ω₁ φ, rewAux_comp_eq ω₂ ω₁ ψ]
  | .all φ => by
    change Semiformula.all _ = Semiformula.all _
    have hq : ω₂.q.comp ω₁.q = (ω₂.comp ω₁).q :=
      rew_ext
        (fun i => by
          cases i using Fin.cases with
          | zero => rfl
          | succ j =>
            change ω₂.q (Rew.bShift (ω₁ #j)) = Rew.bShift (ω₂ (ω₁ #j))
            cases ω₁ #j with
            | bvar _ => rfl | fvar _ => rfl | func f _ => exact Empty.elim f)
        (fun x => by
          change ω₂.q (Rew.bShift (ω₁ &x)) = Rew.bShift (ω₂ (ω₁ &x))
          cases ω₁ &x with
          | bvar _ => rfl | fvar _ => rfl | func f _ => exact Empty.elim f)
    rw [rewAux_comp_eq ω₂.q ω₁.q φ, hq]
  | .exs φ => by
    change Semiformula.exs _ = Semiformula.exs _
    have hq : ω₂.q.comp ω₁.q = (ω₂.comp ω₁).q :=
      rew_ext
        (fun i => by
          cases i using Fin.cases with
          | zero => rfl
          | succ j =>
            change ω₂.q (Rew.bShift (ω₁ #j)) = Rew.bShift (ω₂ (ω₁ #j))
            cases ω₁ #j with
            | bvar _ => rfl | fvar _ => rfl | func f _ => exact Empty.elim f)
        (fun x => by
          change ω₂.q (Rew.bShift (ω₁ &x)) = Rew.bShift (ω₂ (ω₁ &x))
          cases ω₁ &x with
          | bvar _ => rfl | fvar _ => rfl | func f _ => exact Empty.elim f)
    rw [rewAux_comp_eq ω₂.q ω₁.q φ, hq]

lemma cFixitr_encForm {n : ℕ} (m : ℕ) (φ : Semiproposition ℒₛₑₜ n) :
    cFixitr n m (encForm φ) = encForm (Rew.fixitr n m ▹ φ) := by
  induction m with
  | zero =>
    change encForm φ = encForm (Semiformula.rewAux Rew.id φ)
    rw [rewAux_id_eq]
  | succ m ih =>
    change cFix (n + m) (cFixitr n m (encForm φ)) = encForm (Semiformula.rewAux (Rew.fix.comp (Rew.fixitr n m)) φ)
    rw [ih, cFix_encForm]
    change encForm (Semiformula.rewAux Rew.fix (Semiformula.rewAux (Rew.fixitr n m) φ)) = _
    rw [rewAux_comp_eq]

def cSubstList (v : List ℕ) (c : ℕ) : ℕ :=
  cRew (fun (v : List ℕ) i => v.getD i 0) (fun (_ : List ℕ) x => 2 * x + 1) v c

lemma primrec_cSubstList : Primrec₂ cSubstList :=
  primrec_cRew primrec_getD_nat
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))

lemma cSubstList_encForm {n₁ n₂ : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n₁) (v : Fin n₁ → Semiterm ℒₛₑₜ ℕ n₂) :
    cSubstList (List.ofFn fun i => encTerm (v i)) (encForm φ) = encForm (Rew.subst v ▹ φ) :=
  cRew_encForm φ (Rew.subst v)
    (fun i => by simp only [Rew.subst, rew_bind_bvar]; simp [List.getD_eq_getElem?_getD, i.isLt])
    (fun _ => by simp only [Rew.subst, rew_bind_fvar]; simp [encTerm])

end C14H4Part2

namespace C14H4Part2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/- ## Section 2E: `cFvSup`, `cIsWf`, `cUnivCl`, `cZFCAxiomOf`, `cCheckTrace`, `rePred_provable_sent` -/

lemma primrec_max : Primrec₂ (max : ℕ → ℕ → ℕ) :=
  Primrec.ite (Primrec.nat_le.comp Primrec.fst Primrec.snd) Primrec.snd Primrec.fst

private def fvSupStep (_ : Unit) (k : ℕ) (tbl : List ℕ) : ℕ :=
  let t := k.unpair.1
  let arg := k.unpair.2
  if t = 0 ∨ t = 1 then 0
  else if t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 then
    let u1 := arg.unpair.1
    let u2 := arg.unpair.2
    max (if u1 % 2 = 1 then u1 / 2 + 1 else 0) (if u2 % 2 = 1 then u2 / 2 + 1 else 0)
  else if t = 6 ∨ t = 7 then
    max (tbl.getD arg.unpair.1 0) (tbl.getD arg.unpair.2 0)
  else if t = 8 ∨ t = 9 then
    tbl.getD arg 0
  else 0

def cFvSup (c : ℕ) : ℕ := strongRecEval fvSupStep () c

lemma primrec_cFvSup : Primrec cFvSup := by
  have hstep : Primrec (fun p : Unit × ℕ × List ℕ => fvSupStep p.1 p.2.1 p.2.2) := by
    let P := Unit × ℕ × List ℕ
    have ht : Primrec (fun p : P => p.2.1.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have harg : Primrec (fun p : P => p.2.1.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have ha1 : Primrec (fun p : P => p.2.1.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp harg)
    have ha2 : Primrec (fun p : P => p.2.1.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp harg)
    have htbl : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
    unfold fvSupStep
    refine Primrec.ite ((Primrec.eq.comp ht (Primrec.const 0)).or (Primrec.eq.comp ht (Primrec.const 1)))
      (Primrec.const 0) ?_
    refine Primrec.ite
      ((Primrec.eq.comp ht (Primrec.const 2)).or
        ((Primrec.eq.comp ht (Primrec.const 3)).or
          ((Primrec.eq.comp ht (Primrec.const 4)).or (Primrec.eq.comp ht (Primrec.const 5)))))
      (primrec_max.comp
        (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp ha1 (Primrec.const 2)) (Primrec.const 1))
          (Primrec.succ.comp (Primrec.nat_div.comp ha1 (Primrec.const 2))) (Primrec.const 0))
        (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp ha2 (Primrec.const 2)) (Primrec.const 1))
          (Primrec.succ.comp (Primrec.nat_div.comp ha2 (Primrec.const 2))) (Primrec.const 0))) ?_
    refine Primrec.ite ((Primrec.eq.comp ht (Primrec.const 6)).or (Primrec.eq.comp ht (Primrec.const 7)))
      (primrec_max.comp (primrec_getD_nat.comp htbl ha1) (primrec_getD_nat.comp htbl ha2)) ?_
    refine Primrec.ite ((Primrec.eq.comp ht (Primrec.const 8)).or (Primrec.eq.comp ht (Primrec.const 9)))
      (primrec_getD_nat.comp htbl harg) (Primrec.const 0)
  exact (primrec_strongRecEval hstep).comp (Primrec.const ()) Primrec.id

lemma primrec_decide {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (hp : PrimrecPred p) : Primrec (fun a => decide (p a)) :=
  (Primrec.ite hp (Primrec.const true) (Primrec.const false)).of_eq fun a => by
    by_cases h : p a <;> simp [h]

private lemma recBotCoe_sup (x y : WithBot ℕ) :
    WithBot.recBotCoe (C := fun _ => ℕ) 0 Nat.succ (x ⊔ y) =
      max (WithBot.recBotCoe (C := fun _ => ℕ) 0 Nat.succ x)
          (WithBot.recBotCoe (C := fun _ => ℕ) 0 Nat.succ y) := by
  cases x with
  | bot => cases y <;> rfl
  | coe a =>
    cases y with
    | bot => rfl
    | coe b =>
      change max a b + 1 = max (a + 1) (b + 1)
      omega

private lemma recBotCoe_max_union (s₁ s₂ : Finset ℕ) :
    WithBot.recBotCoe (C := fun _ => ℕ) 0 Nat.succ (s₁ ∪ s₂).max =
      max (WithBot.recBotCoe (C := fun _ => ℕ) 0 Nat.succ s₁.max)
          (WithBot.recBotCoe (C := fun _ => ℕ) 0 Nat.succ s₂.max) := by
  rw [Finset.max_union]
  exact recBotCoe_sup _ _

private lemma term_fvSup_eq {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) :
    (t.freeVariables.max).recBotCoe 0 Nat.succ =
      if encTerm t % 2 = 1 then encTerm t / 2 + 1 else 0 := by
  cases t with
  | bvar i =>
    change 0 = if (2 * i.val) % 2 = 1 then (2 * i.val) / 2 + 1 else 0
    split_ifs <;> omega
  | fvar x =>
    change x + 1 = if (2 * x + 1) % 2 = 1 then (2 * x + 1) / 2 + 1 else 0
    split_ifs <;> omega
  | func f _ => exact Empty.elim f

private lemma rel_fv_eq {n : ℕ} (v : Fin 2 → Semiterm ℒₛₑₜ ℕ n) :
    (Finset.univ.biUnion fun i => (v i).freeVariables) =
      (v 0).freeVariables ∪ (v 1).freeVariables := by
  ext x; simp [Fin.exists_fin_two]

lemma cFvSup_encForm : ∀ {n : ℕ} (φ : Semiproposition ℒₛₑₜ n),
    cFvSup (encForm φ) = φ.fvSup
  | _, .verum => by rw [cFvSup, strongRecEval_eq]; rfl
  | _, .falsum => by
    rw [cFvSup, strongRecEval_eq]
    simp [fvSupStep, encForm, Semiformula.fvSup, Semiformula.freeVariables]
  | _, .rel .eq v => by
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (2 : ℕ) ≠ 1 by decide, or_self, true_or, ↓reduceIte,
      Semiformula.fvSup, Semiformula.freeVariables, rel_fv_eq, recBotCoe_max_union, term_fvSup_eq]
  | _, .rel .mem v => by
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, or_self, true_or, or_true, ↓reduceIte,
      Semiformula.fvSup, Semiformula.freeVariables, rel_fv_eq, recBotCoe_max_union, term_fvSup_eq]
  | _, .nrel .eq v => by
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide,
      or_self, true_or, or_true, ↓reduceIte,
      Semiformula.fvSup, Semiformula.freeVariables, rel_fv_eq, recBotCoe_max_union, term_fvSup_eq]
  | _, .nrel .mem v => by
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (5 : ℕ) ≠ 1 by decide, show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide,
      show (5 : ℕ) ≠ 4 by decide, or_self, or_true, ↓reduceIte,
      Semiformula.fvSup, Semiformula.freeVariables, rel_fv_eq, recBotCoe_max_union, term_fvSup_eq]
  | _, .and φ ψ => by
    have hlt := pair_lt_of_ge_two_left (t := 6) (a := encForm φ) (b := encForm ψ) (by decide)
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (6 : ℕ) ≠ 1 by decide, show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide,
      show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide, or_self, true_or, ↓reduceIte]
    rw [buildTable_getD_zero_eq _ _ hlt.1, buildTable_getD_zero_eq _ _ hlt.2]
    change max (cFvSup (encForm φ)) (cFvSup (encForm ψ)) = _
    rw [cFvSup_encForm φ, cFvSup_encForm ψ]
    simp [Semiformula.fvSup, Semiformula.freeVariables, recBotCoe_max_union]
  | _, .or φ ψ => by
    have hlt := pair_lt_of_ge_two_left (t := 7) (a := encForm φ) (b := encForm ψ) (by decide)
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (7 : ℕ) ≠ 1 by decide, show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide,
      show (7 : ℕ) ≠ 4 by decide, show (7 : ℕ) ≠ 5 by decide, show (7 : ℕ) ≠ 6 by decide,
      or_self, or_true, ↓reduceIte]
    rw [buildTable_getD_zero_eq _ _ hlt.1, buildTable_getD_zero_eq _ _ hlt.2]
    change max (cFvSup (encForm φ)) (cFvSup (encForm ψ)) = _
    rw [cFvSup_encForm φ, cFvSup_encForm ψ]
    simp [Semiformula.fvSup, Semiformula.freeVariables, recBotCoe_max_union]
  | _, .all φ => by
    have hlt : encForm φ < Nat.pair 8 (encForm φ) := lt_pair_of_pos_left (by decide)
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (8 : ℕ) ≠ 1 by decide, show (8 : ℕ) ≠ 2 by decide, show (8 : ℕ) ≠ 3 by decide,
      show (8 : ℕ) ≠ 4 by decide, show (8 : ℕ) ≠ 5 by decide, show (8 : ℕ) ≠ 6 by decide,
      show (8 : ℕ) ≠ 7 by decide, or_self, true_or, ↓reduceIte]
    rw [buildTable_getD_zero_eq _ _ hlt]
    exact cFvSup_encForm φ
  | _, .exs φ => by
    have hlt : encForm φ < Nat.pair 9 (encForm φ) := lt_pair_of_pos_left (by decide)
    rw [cFvSup, strongRecEval_eq]
    simp only [fvSupStep, encForm, Nat.unpair_pair, OfNat.ofNat_ne_zero,
      show (9 : ℕ) ≠ 1 by decide, show (9 : ℕ) ≠ 2 by decide, show (9 : ℕ) ≠ 3 by decide,
      show (9 : ℕ) ≠ 4 by decide, show (9 : ℕ) ≠ 5 by decide, show (9 : ℕ) ≠ 6 by decide,
      show (9 : ℕ) ≠ 7 by decide, show (9 : ℕ) ≠ 8 by decide, or_self, or_true, ↓reduceIte]
    rw [buildTable_getD_zero_eq _ _ hlt]
    exact cFvSup_encForm φ

/- `cIsWf`: well-formedness predicate for `encForm` of `Semiformula ℒₛₑₜ ℕ n` -/

private def wfStep (M : ℕ) (k : ℕ) (tbl : List (List ℕ)) : List ℕ :=
  let t := k.unpair.1
  let arg := k.unpair.2
  (List.range (M + 1)).map fun n =>
    if t = 0 ∨ t = 1 then
      if arg = 0 then 1 else 0
    else if t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 then
      let u1 := arg.unpair.1
      let u2 := arg.unpair.2
      if (u1 % 2 = 1 ∨ u1 / 2 < n) ∧ (u2 % 2 = 1 ∨ u2 / 2 < n) then 1 else 0
    else if t = 6 ∨ t = 7 then
      if (tbl.getD arg.unpair.1 []).getD n 0 = 1 ∧ (tbl.getD arg.unpair.2 []).getD n 0 = 1 then 1 else 0
    else if t = 8 ∨ t = 9 then
      (tbl.getD arg []).getD (n + 1) 0
    else 0

def cIsWfAt (M n c : ℕ) : Bool :=
  decide ((strongRecEval wfStep M c).getD n 0 = 1)

def cIsWf (n c : ℕ) : Bool := cIsWfAt (n + c) n c

lemma primrec_cIsWf : Primrec₂ cIsWf := by
  have hstep : Primrec (fun p : ℕ × ℕ × List (List ℕ) => wfStep p.1 p.2.1 p.2.2) := by
    let P := ℕ × ℕ × List (List ℕ)
    have hbody : Primrec₂ (fun (p : P) (n : ℕ) =>
        let t := p.2.1.unpair.1
        let arg := p.2.1.unpair.2
        let tbl := p.2.2
        if t = 0 ∨ t = 1 then
          if arg = 0 then 1 else 0
        else if t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 then
          let u1 := arg.unpair.1
          let u2 := arg.unpair.2
          if (u1 % 2 = 1 ∨ u1 / 2 < n) ∧ (u2 % 2 = 1 ∨ u2 / 2 < n) then 1 else 0
        else if t = 6 ∨ t = 7 then
          if (tbl.getD arg.unpair.1 []).getD n 0 = 1 ∧ (tbl.getD arg.unpair.2 []).getD n 0 = 1 then 1 else 0
        else if t = 8 ∨ t = 9 then
          (tbl.getD arg []).getD (n + 1) 0
        else 0) := by
      have hn : Primrec (fun q : P × ℕ => q.2) := Primrec.snd
      have ht : Primrec (fun q : P × ℕ => q.1.2.1.unpair.1) :=
        Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      have harg : Primrec (fun q : P × ℕ => q.1.2.1.unpair.2) :=
        Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      have ha1 : Primrec (fun q : P × ℕ => q.1.2.1.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp harg)
      have ha2 : Primrec (fun q : P × ℕ => q.1.2.1.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp harg)
      have htbl : Primrec (fun q : P × ℕ => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      refine Primrec.ite ((Primrec.eq.comp ht (Primrec.const 0)).or (Primrec.eq.comp ht (Primrec.const 1)))
        (Primrec.ite (Primrec.eq.comp harg (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0)) ?_
      have h25 : PrimrecPred (fun q : P × ℕ =>
          q.1.2.1.unpair.1 = 2 ∨ q.1.2.1.unpair.1 = 3 ∨ q.1.2.1.unpair.1 = 4 ∨ q.1.2.1.unpair.1 = 5) :=
        (Primrec.eq.comp ht (Primrec.const 2)).or
          ((Primrec.eq.comp ht (Primrec.const 3)).or
            ((Primrec.eq.comp ht (Primrec.const 4)).or (Primrec.eq.comp ht (Primrec.const 5))))
      refine Primrec.ite h25
        (Primrec.ite
          (((Primrec.eq.comp (Primrec.nat_mod.comp ha1 (Primrec.const 2)) (Primrec.const 1)).or
              (Primrec.nat_lt.comp (Primrec.nat_div.comp ha1 (Primrec.const 2)) hn)).and
            ((Primrec.eq.comp (Primrec.nat_mod.comp ha2 (Primrec.const 2)) (Primrec.const 1)).or
              (Primrec.nat_lt.comp (Primrec.nat_div.comp ha2 (Primrec.const 2)) hn)))
          (Primrec.const 1) (Primrec.const 0)) ?_
      refine Primrec.ite ((Primrec.eq.comp ht (Primrec.const 6)).or (Primrec.eq.comp ht (Primrec.const 7)))
        (Primrec.ite
          ((Primrec.eq.comp (primrec_getD_nat.comp (primrec_getD_listNat.comp htbl ha1) hn) (Primrec.const 1)).and
            (Primrec.eq.comp (primrec_getD_nat.comp (primrec_getD_listNat.comp htbl ha2) hn) (Primrec.const 1)))
          (Primrec.const 1) (Primrec.const 0)) ?_
      refine Primrec.ite ((Primrec.eq.comp ht (Primrec.const 8)).or (Primrec.eq.comp ht (Primrec.const 9)))
        (primrec_getD_nat.comp (primrec_getD_listNat.comp htbl harg) (Primrec.succ.comp hn))
        (Primrec.const 0)
    exact Primrec.list_map (primrec_list_range.comp (Primrec.succ.comp Primrec.fst)) hbody
  have hAt : Primrec (fun q : (ℕ × ℕ) × ℕ => cIsWfAt q.1.1 q.1.2 q.2) :=
    primrec_decide (Primrec.eq.comp
      (primrec_getD_nat.comp
        ((primrec_strongRecEval hstep).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
      (Primrec.const 1))
  exact hAt.comp (Primrec.pair (Primrec.pair (Primrec.nat_add.comp Primrec.fst Primrec.snd) Primrec.fst) Primrec.snd)

private lemma encTerm_wf {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) :
    encTerm t % 2 = 1 ∨ encTerm t / 2 < n := by
  cases t with
  | bvar i => right; simp only [encTerm]; omega
  | fvar x => left; simp only [encTerm]; omega
  | func f _ => exact Empty.elim f

private lemma exists_encTerm_of_wf {n u : ℕ} (h : u % 2 = 1 ∨ u / 2 < n) :
    ∃ t : Semiterm ℒₛₑₜ ℕ n, encTerm t = u := by
  by_cases hmod : u % 2 = 1
  · refine ⟨&(u / 2), ?_⟩; simp only [encTerm]; omega
  · have hlt : u / 2 < n := h.resolve_left hmod
    refine ⟨#⟨u / 2, hlt⟩, ?_⟩; simp only [encTerm]; omega

lemma cIsWfAt_encForm {M : ℕ} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n),
    n + encForm φ ≤ M → cIsWfAt M n (encForm φ) = true
  | n, .verum, hM => by
    have hn : n < M + 1 := by omega
    simp [cIsWfAt, strongRecEval_eq, wfStep, encForm, List.getD_eq_getElem?_getD, hn]
  | n, .falsum, hM => by
    have hn : n < M + 1 := by omega
    simp [cIsWfAt, strongRecEval_eq, wfStep, encForm, List.getD_eq_getElem?_getD, hn]
  | n, .rel .eq v, hM => by
    have hn : n < M + 1 := by omega
    simp [cIsWfAt, strongRecEval_eq, wfStep, encForm, List.getD_eq_getElem?_getD, hn,
      encTerm_wf (v 0), encTerm_wf (v 1)]
  | n, .rel .mem v, hM => by
    have hn : n < M + 1 := by omega
    simp [cIsWfAt, strongRecEval_eq, wfStep, encForm, List.getD_eq_getElem?_getD, hn,
      encTerm_wf (v 0), encTerm_wf (v 1)]
  | n, .nrel .eq v, hM => by
    have hn : n < M + 1 := by omega
    simp [cIsWfAt, strongRecEval_eq, wfStep, encForm, List.getD_eq_getElem?_getD, hn,
      encTerm_wf (v 0), encTerm_wf (v 1)]
  | n, .nrel .mem v, hM => by
    have hn : n < M + 1 := by omega
    simp [cIsWfAt, strongRecEval_eq, wfStep, encForm, List.getD_eq_getElem?_getD, hn,
      encTerm_wf (v 0), encTerm_wf (v 1)]
  | n, .and φ ψ, hM => by
    have hlt := pair_lt_of_ge_two_left (t := 6) (a := encForm φ) (b := encForm ψ) (by decide)
    have hM' : n + Nat.pair 6 (Nat.pair (encForm φ) (encForm ψ)) ≤ M := hM
    have hn : n < M + 1 := by omega
    have h1 := cIsWfAt_encForm (M := M) (n := n) φ (by have := hlt.1; omega)
    have h2 := cIsWfAt_encForm (M := M) (n := n) ψ (by have := hlt.2; omega)
    simp only [cIsWfAt, decide_eq_true_eq] at h1 h2 ⊢
    rw [strongRecEval_eq]
    simp only [wfStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hn, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (6 : ℕ) ≠ 1 by decide, show (6 : ℕ) ≠ 2 by decide,
      show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide,
      or_self, true_or, ↓reduceIte]
    change (if (((buildTable wfStep M _).getD (encForm φ) default).getD n 0 = 1 ∧
      ((buildTable wfStep M _).getD (encForm ψ) default).getD n 0 = 1) then 1 else 0) = 1
    rw [buildTable_getD_eq_strongRecEval wfStep M hlt.1,
        buildTable_getD_eq_strongRecEval wfStep M hlt.2, h1, h2]
    simp
  | n, .or φ ψ, hM => by
    have hlt := pair_lt_of_ge_two_left (t := 7) (a := encForm φ) (b := encForm ψ) (by decide)
    have hM' : n + Nat.pair 7 (Nat.pair (encForm φ) (encForm ψ)) ≤ M := hM
    have hn : n < M + 1 := by omega
    have h1 := cIsWfAt_encForm (M := M) (n := n) φ (by have := hlt.1; omega)
    have h2 := cIsWfAt_encForm (M := M) (n := n) ψ (by have := hlt.2; omega)
    simp only [cIsWfAt, decide_eq_true_eq] at h1 h2 ⊢
    rw [strongRecEval_eq]
    simp only [wfStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hn, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (7 : ℕ) ≠ 1 by decide, show (7 : ℕ) ≠ 2 by decide,
      show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 4 by decide, show (7 : ℕ) ≠ 5 by decide,
      show (7 : ℕ) ≠ 6 by decide, or_self, or_true, ↓reduceIte]
    change (if (((buildTable wfStep M _).getD (encForm φ) default).getD n 0 = 1 ∧
      ((buildTable wfStep M _).getD (encForm ψ) default).getD n 0 = 1) then 1 else 0) = 1
    rw [buildTable_getD_eq_strongRecEval wfStep M hlt.1,
        buildTable_getD_eq_strongRecEval wfStep M hlt.2, h1, h2]
    simp
  | n, .all φ, hM => by
    have hlt : encForm φ < Nat.pair 8 (encForm φ) := lt_pair_of_pos_left (by decide)
    have hM' : n + Nat.pair 8 (encForm φ) ≤ M := hM
    have hn : n < M + 1 := by omega
    have h1 := cIsWfAt_encForm (M := M) (n := n + 1) φ (by omega)
    simp only [cIsWfAt, decide_eq_true_eq] at h1 ⊢
    rw [strongRecEval_eq]
    simp only [wfStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hn, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (8 : ℕ) ≠ 1 by decide, show (8 : ℕ) ≠ 2 by decide,
      show (8 : ℕ) ≠ 3 by decide, show (8 : ℕ) ≠ 4 by decide, show (8 : ℕ) ≠ 5 by decide,
      show (8 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 7 by decide, or_self, true_or, ↓reduceIte]
    change ((buildTable wfStep M _).getD (encForm φ) default).getD (n + 1) 0 = 1
    rw [buildTable_getD_eq_strongRecEval wfStep M hlt]
    exact h1
  | n, .exs φ, hM => by
    have hlt : encForm φ < Nat.pair 9 (encForm φ) := lt_pair_of_pos_left (by decide)
    have hM' : n + Nat.pair 9 (encForm φ) ≤ M := hM
    have hn : n < M + 1 := by omega
    have h1 := cIsWfAt_encForm (M := M) (n := n + 1) φ (by omega)
    simp only [cIsWfAt, decide_eq_true_eq] at h1 ⊢
    rw [strongRecEval_eq]
    simp only [wfStep, encForm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hn, Option.map_some, Option.getD_some, Nat.unpair_pair,
      OfNat.ofNat_ne_zero, show (9 : ℕ) ≠ 1 by decide, show (9 : ℕ) ≠ 2 by decide,
      show (9 : ℕ) ≠ 3 by decide, show (9 : ℕ) ≠ 4 by decide, show (9 : ℕ) ≠ 5 by decide,
      show (9 : ℕ) ≠ 6 by decide, show (9 : ℕ) ≠ 7 by decide, show (9 : ℕ) ≠ 8 by decide,
      or_self, or_true, ↓reduceIte]
    change ((buildTable wfStep M _).getD (encForm φ) default).getD (n + 1) 0 = 1
    rw [buildTable_getD_eq_strongRecEval wfStep M hlt]
    exact h1

lemma cIsWf_encForm {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) : cIsWf n (encForm φ) = true :=
  cIsWfAt_encForm φ le_rfl

lemma exists_encForm_of_cIsWfAt {M : ℕ} : ∀ (c n : ℕ), cIsWfAt M n c = true →
    ∃ φ : Semiformula ℒₛₑₜ ℕ n, encForm φ = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro n hc
    simp only [cIsWfAt, decide_eq_true_eq, strongRecEval_eq, wfStep, List.getD_eq_getElem?_getD,
      List.getElem?_map] at hc
    by_cases hn : n < M + 1
    · simp only [List.getElem?_range hn, Option.map_some, Option.getD_some] at hc
      set t := c.unpair.1
      set arg := c.unpair.2
      have hpair : Nat.pair t arg = c := Nat.pair_unpair c
      by_cases ht0 : t = 0 ∨ t = 1
      · rw [if_pos ht0] at hc
        have harg : arg = 0 := by by_contra hne; rw [if_neg hne] at hc; omega
        rcases ht0 with ht0 | ht0
        · exact ⟨.verum, by rw [← hpair, ht0, harg]; rfl⟩
        · exact ⟨.falsum, by rw [← hpair, ht0, harg]; rfl⟩
      · rw [if_neg ht0] at hc
        by_cases ht25 : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5
        · rw [if_pos ht25] at hc
          have hwf : (arg.unpair.1 % 2 = 1 ∨ arg.unpair.1 / 2 < n) ∧
              (arg.unpair.2 % 2 = 1 ∨ arg.unpair.2 / 2 < n) := by
            by_contra hne; rw [if_neg hne] at hc; omega
          obtain ⟨t1, ht1⟩ := exists_encTerm_of_wf hwf.1
          obtain ⟨t2, ht2⟩ := exists_encTerm_of_wf hwf.2
          have harg_eq : Nat.pair (encTerm t1) (encTerm t2) = arg := by
            rw [ht1, ht2, Nat.pair_unpair]
          rcases ht25 with ht25 | ht25 | ht25 | ht25
          · exact ⟨.rel .eq ![t1, t2], by simp [encForm, harg_eq, ← ht25, hpair]⟩
          · exact ⟨.rel .mem ![t1, t2], by simp [encForm, harg_eq, ← ht25, hpair]⟩
          · exact ⟨.nrel .eq ![t1, t2], by simp [encForm, harg_eq, ← ht25, hpair]⟩
          · exact ⟨.nrel .mem ![t1, t2], by simp [encForm, harg_eq, ← ht25, hpair]⟩
        · rw [if_neg ht25] at hc
          by_cases ht67 : t = 6 ∨ t = 7
          · rw [if_pos ht67] at hc
            have htge : 2 ≤ t := by omega
            have hlt := pair_lt_of_ge_two_left (t := t) (a := arg.unpair.1) (b := arg.unpair.2) htge
            rw [Nat.pair_unpair arg, hpair] at hlt
            split_ifs at hc with h12
            have hb1 : (buildTable wfStep M c).getD arg.unpair.1 [] = strongRecEval wfStep M arg.unpair.1 :=
              buildTable_getD_eq_strongRecEval wfStep M hlt.1
            have hb2 : (buildTable wfStep M c).getD arg.unpair.2 [] = strongRecEval wfStep M arg.unpair.2 :=
              buildTable_getD_eq_strongRecEval wfStep M hlt.2
            have h1' : (strongRecEval wfStep M arg.unpair.1).getD n 0 = 1 := by rw [← hb1]; exact h12.1
            have h2' : (strongRecEval wfStep M arg.unpair.2).getD n 0 = 1 := by rw [← hb2]; exact h12.2
            obtain ⟨φ, hφ⟩ := ih arg.unpair.1 hlt.1 n (by unfold cIsWfAt; rw [h1']; rfl)
            obtain ⟨ψ, hψ⟩ := ih arg.unpair.2 hlt.2 n (by unfold cIsWfAt; rw [h2']; rfl)
            have harg_eq : Nat.pair (encForm φ) (encForm ψ) = arg := by
              rw [hφ, hψ, Nat.pair_unpair]
            rcases ht67 with ht67 | ht67
            · exact ⟨.and φ ψ, by simp [encForm, harg_eq, ← ht67, hpair]⟩
            · exact ⟨.or φ ψ, by simp [encForm, harg_eq, ← ht67, hpair]⟩
          · rw [if_neg ht67] at hc
            by_cases ht89 : t = 8 ∨ t = 9
            · rw [if_pos ht89] at hc
              have htpos : 0 < t := by omega
              have hlt : arg < c := by
                have := lt_pair_of_pos_left (a := t) (b := arg) htpos
                rwa [hpair] at this
              have hb1 : (buildTable wfStep M c).getD arg [] = strongRecEval wfStep M arg :=
                buildTable_getD_eq_strongRecEval wfStep M hlt
              have h1' : (strongRecEval wfStep M arg).getD (n + 1) 0 = 1 := by rw [← hb1]; exact hc
              obtain ⟨φ, hφ⟩ := ih arg hlt (n + 1) (by unfold cIsWfAt; rw [h1']; rfl)
              rcases ht89 with ht89 | ht89
              · exact ⟨.all φ, by simp [encForm, hφ, ← ht89, hpair]⟩
              · exact ⟨.exs φ, by simp [encForm, hφ, ← ht89, hpair]⟩
            · rw [if_neg ht89] at hc; omega
    · simp [List.getElem?_range, hn] at hc

lemma exists_encForm_of_cIsWf {n c : ℕ} (h : cIsWf n c = true) :
    ∃ φ : Semiformula ℒₛₑₜ ℕ n, encForm φ = c :=
  exists_encForm_of_cIsWfAt c n h

/- `cAllItr` and `cUnivCl` -/

def cAllItr (m c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) c (fun _ acc => Nat.pair 8 acc) m

lemma primrec_cAllItr : Primrec₂ cAllItr := by
  have hrec : Primrec₂ (fun (c m : ℕ) =>
      Nat.rec (motive := fun _ => ℕ) c (fun _ acc => Nat.pair 8 acc) m) :=
    Primrec.nat_rec Primrec.id
      (primrec_natPair.comp (Primrec.const 8) (Primrec.snd.comp Primrec.snd)).to₂
  exact hrec.comp Primrec.snd Primrec.fst

private lemma cAllItr_succ (k c : ℕ) : cAllItr (k + 1) c = cAllItr k (Nat.pair 8 c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.pair 8 (cAllItr (k + 1) c) = Nat.pair 8 (cAllItr k (Nat.pair 8 c))
    rw [ih]

lemma cAllItr_encForm : ∀ {n : ℕ} (k : ℕ) (φ : Semiproposition ℒₛₑₜ (n + k)),
    cAllItr k (encForm φ) = encForm (∀¹^[k] φ)
  | _, 0, _ => rfl
  | _, k + 1, φ => by
    rw [cAllItr_succ]
    exact cAllItr_encForm k (∀¹ φ)

private lemma cAllItr_allClosure : ∀ (k : ℕ) (φ : Semiproposition ℒₛₑₜ k),
    cAllItr k (encForm φ) = encForm (∀¹* φ)
  | 0, _ => rfl
  | k + 1, φ => by
    rw [cAllItr_succ]
    exact cAllItr_allClosure k (∀¹ φ)

private lemma encTerm_emb_toEmpty {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    encTerm (Rew.emb (t.toEmpty h) : Semiterm ℒₛₑₜ ℕ n) = encTerm t := by
  cases t with
  | bvar _ => rfl
  | fvar x => simp [Semiterm.freeVariables] at h
  | func f _ => exact Empty.elim f

private lemma encForm_emb_toEmpty : ∀ {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) (h : φ.freeVariables = ∅),
    encSent (φ.toEmpty h) = encForm φ
  | _, .verum, _ => rfl
  | _, .falsum, _ => rfl
  | _, .rel .eq v, h => by
    change Nat.pair 2 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
      Nat.pair 2 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
    rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
  | _, .rel .mem v, h => by
    change Nat.pair 3 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
      Nat.pair 3 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
    rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
  | _, .nrel .eq v, h => by
    change Nat.pair 4 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
      Nat.pair 4 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
    rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
  | _, .nrel .mem v, h => by
    change Nat.pair 5 (Nat.pair (encTerm (Rew.emb ((v 0).toEmpty _))) (encTerm (Rew.emb ((v 1).toEmpty _)))) =
      Nat.pair 5 (Nat.pair (encTerm (v 0)) (encTerm (v 1)))
    rw [encTerm_emb_toEmpty, encTerm_emb_toEmpty]
  | _, .and φ ψ, h => by
    simp only [encSent, Semiformula.toEmpty, Rewriting.emb, Semiformula.rew, Semiformula.rewAux, encForm]
    rw [← encForm_emb_toEmpty φ (Finset.union_eq_empty.mp h).1,
        ← encForm_emb_toEmpty ψ (Finset.union_eq_empty.mp h).2]
    rfl
  | _, .or φ ψ, h => by
    simp only [encSent, Semiformula.toEmpty, Rewriting.emb, Semiformula.rew, Semiformula.rewAux, encForm]
    rw [← encForm_emb_toEmpty φ (Finset.union_eq_empty.mp h).1,
        ← encForm_emb_toEmpty ψ (Finset.union_eq_empty.mp h).2]
    rfl
  | n, .all φ, h => by
    have hq : (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := n)).q = Rew.emb := by
      apply DFunLike.coe_injective; funext t
      cases t with
      | bvar i => cases i using Fin.cases <;> rfl
      | fvar e => exact Empty.elim e
      | func f _ => exact Empty.elim f
    change Nat.pair 8 (encForm (Semiformula.rewAux Rew.emb.q (φ.toEmpty h))) = Nat.pair 8 (encForm φ)
    rw [hq]
    exact congrArg (Nat.pair 8) (encForm_emb_toEmpty φ h)
  | n, .exs φ, h => by
    have hq : (Rew.emb (L := ℒₛₑₜ) (o := Empty) (ξ := ℕ) (n := n)).q = Rew.emb := by
      apply DFunLike.coe_injective; funext t
      cases t with
      | bvar i => cases i using Fin.cases <;> rfl
      | fvar e => exact Empty.elim e
      | func f _ => exact Empty.elim f
    change Nat.pair 9 (encForm (Semiformula.rewAux Rew.emb.q (φ.toEmpty h))) = Nat.pair 9 (encForm φ)
    rw [hq]
    exact congrArg (Nat.pair 9) (encForm_emb_toEmpty φ h)

def cUnivCl (c : ℕ) : ℕ := cAllItr (cFvSup c) (cFixitr 0 (cFvSup c) c)

lemma primrec_cUnivCl : Primrec cUnivCl :=
  primrec_cAllItr.comp primrec_cFvSup
    (primrec_cFixitr.comp (Primrec.pair (Primrec.const 0) (Primrec.pair primrec_cFvSup Primrec.id)))

lemma cUnivCl_encForm (φ : Proposition ℒₛₑₜ) :
    cUnivCl (encForm φ) = encSent (Semiformula.univCl φ) := by
  unfold cUnivCl Semiformula.univCl
  rw [encForm_emb_toEmpty]
  unfold Semiformula.univCl'
  rw [cFvSup_encForm, cFixitr_encForm]
  simpa [Nat.zero_add] using cAllItr_allClosure (0 + φ.fvSup) (Rew.fixitr 0 φ.fvSup ▹ φ)

end C14H4Part2

namespace C14H4Part2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/- ## Section 2F: ZFC axioms, flat proof-trace checker `cCheckTrace`, and `rePred_provable_sent` -/

def cImp (a b : ℕ) : ℕ := Nat.pair 7 (Nat.pair (cNeg a) b)
def cIff (a b : ℕ) : ℕ := Nat.pair 6 (Nat.pair (cImp a b) (cImp b a))

lemma primrec_cImp : Primrec₂ cImp :=
  primrec_natPair.comp (Primrec.const 7)
    (primrec_natPair.comp (primrec_cNeg.comp Primrec.fst) Primrec.snd)

lemma primrec_cIff : Primrec₂ cIff :=
  primrec_natPair.comp (Primrec.const 6)
    (primrec_natPair.comp primrec_cImp (primrec_cImp.comp Primrec.snd Primrec.fst))

lemma cImp_encForm {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ℕ n) :
    cImp (encForm φ) (encForm ψ) = encForm (φ 🡒 ψ) := by
  change Nat.pair 7 (Nat.pair (cNeg (encForm φ)) (encForm ψ)) = Nat.pair 7 (Nat.pair (encForm (∼φ)) (encForm ψ))
  rw [cNeg_encForm]

lemma cIff_encForm {n : ℕ} (φ ψ : Semiformula ℒₛₑₜ ℕ n) :
    cIff (encForm φ) (encForm ψ) = encForm (φ 🡘 ψ) := by
  change Nat.pair 6 (Nat.pair (cImp (encForm φ) (encForm ψ)) (cImp (encForm ψ) (encForm φ))) =
    Nat.pair 6 (Nat.pair (encForm (φ 🡒 ψ)) (encForm (ψ 🡒 φ)))
  rw [cImp_encForm, cImp_encForm]

/-- Code of `Axiom.separationSchema φ` from `c = encForm φ`. -/
def cSepSchema (c : ℕ) : ℕ :=
  let mem01 := Nat.pair 3 (Nat.pair 0 2)
  let mem02 := Nat.pair 3 (Nat.pair 0 4)
  let body := cIff mem01 (Nat.pair 6 (Nat.pair mem02 (cSubstList [0] c)))
  cUnivCl (Nat.pair 8 (Nat.pair 9 (Nat.pair 8 body)))

lemma primrec_cSepSchema : Primrec cSepSchema := by
  unfold cSepSchema
  refine primrec_cUnivCl.comp (primrec_natPair.comp (Primrec.const 8)
    (primrec_natPair.comp (Primrec.const 9)
      (primrec_natPair.comp (Primrec.const 8)
        (primrec_cIff.comp (Primrec.const _)
          (primrec_natPair.comp (Primrec.const 6)
            (primrec_natPair.comp (Primrec.const _)
              (primrec_cSubstList.comp (Primrec.const [0]) Primrec.id)))))))

lemma cSepSchema_encForm (φ : SetTheorySemiproposition 1) :
    cSepSchema (encForm φ) = encSent (Axiom.separationSchema φ) := by
  unfold cSepSchema Axiom.separationSchema
  rw [← cUnivCl_encForm]
  apply congrArg cUnivCl
  have hsub : cSubstList [0] (encForm φ) = encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 1) (n' := 3) ![#0] ▹ φ) := by
    simpa [List.ofFn_succ, encTerm] using cSubstList_encForm φ (![(#0 : Semiterm ℒₛₑₜ ℕ 3)])
  rw [hsub]
  have hm01 : Nat.pair 3 (Nat.pair 0 2) = encForm (Semiformula.rel Language.Set.Rel.mem ![#0, #1] : Semiproposition ℒₛₑₜ 3) := rfl
  have hm02 : Nat.pair 3 (Nat.pair 0 4) = encForm (Semiformula.rel Language.Set.Rel.mem ![#0, #2] : Semiproposition ℒₛₑₜ 3) := rfl
  have hand : Nat.pair 6 (Nat.pair (encForm (Semiformula.rel Language.Set.Rel.mem ![#0, #2] : Semiproposition ℒₛₑₜ 3))
      (encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 1) (n' := 3) ![#0] ▹ φ))) =
      encForm ((Semiformula.rel Language.Set.Rel.mem ![#0, #2] : Semiproposition ℒₛₑₜ 3) ⋏
        (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 1) (n' := 3) ![#0] ▹ φ)) := rfl
  rw [hm01, hm02, hand, cIff_encForm]
  rfl

/-- Code of `Axiom.replacementSchema φ` from `c = encForm φ`. -/
def cRepSchema (c : ℕ) : ℕ :=
  let lhs := Nat.pair 8 (Nat.pair 9 (Nat.pair 6 (Nat.pair
    (cSubstList [2, 0] c)
    (Nat.pair 8 (cImp (cSubstList [4, 0] c) (Nat.pair 2 (Nat.pair 0 2)))))))
  let rhs := Nat.pair 8 (Nat.pair 9 (Nat.pair 8
    (cIff (Nat.pair 3 (Nat.pair 0 2))
      (Nat.pair 9 (Nat.pair 6 (Nat.pair (Nat.pair 3 (Nat.pair 0 6)) (cSubstList [0, 2] c)))))))
  cUnivCl (cImp lhs rhs)

lemma primrec_cRepSchema : Primrec cRepSchema := by
  unfold cRepSchema
  have hlhs : Primrec (fun c => Nat.pair 8 (Nat.pair 9 (Nat.pair 6 (Nat.pair
      (cSubstList [2, 0] c)
      (Nat.pair 8 (cImp (cSubstList [4, 0] c) (Nat.pair 2 (Nat.pair 0 2)))))))) :=
    primrec_natPair.comp (Primrec.const 8)
      (primrec_natPair.comp (Primrec.const 9)
        (primrec_natPair.comp (Primrec.const 6)
          (primrec_natPair.comp
            (primrec_cSubstList.comp (Primrec.const [2, 0]) Primrec.id)
            (primrec_natPair.comp (Primrec.const 8)
              (primrec_cImp.comp (primrec_cSubstList.comp (Primrec.const [4, 0]) Primrec.id)
                (Primrec.const _))))))
  have hrhs : Primrec (fun c => Nat.pair 8 (Nat.pair 9 (Nat.pair 8
      (cIff (Nat.pair 3 (Nat.pair 0 2))
        (Nat.pair 9 (Nat.pair 6 (Nat.pair (Nat.pair 3 (Nat.pair 0 6)) (cSubstList [0, 2] c)))))))) :=
    primrec_natPair.comp (Primrec.const 8)
      (primrec_natPair.comp (Primrec.const 9)
        (primrec_natPair.comp (Primrec.const 8)
          (primrec_cIff.comp (Primrec.const _)
            (primrec_natPair.comp (Primrec.const 9)
              (primrec_natPair.comp (Primrec.const 6)
                (primrec_natPair.comp (Primrec.const _)
                  (primrec_cSubstList.comp (Primrec.const [0, 2]) Primrec.id)))))))
  exact primrec_cUnivCl.comp (primrec_cImp.comp hlhs hrhs)

lemma cRepSchema_encForm (φ : SetTheorySemiproposition 2) :
    cRepSchema (encForm φ) = encSent (Axiom.replacementSchema φ) := by
  unfold cRepSchema Axiom.replacementSchema
  rw [← cUnivCl_encForm]
  apply congrArg cUnivCl
  have h1 : cSubstList [2, 0] (encForm φ) =
      encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 2) ![#1, #0] ▹ φ) := by
    simpa [List.ofFn_succ, encTerm] using cSubstList_encForm φ (![(#1 : Semiterm ℒₛₑₜ ℕ 2), #0])
  have h2 : cSubstList [4, 0] (encForm φ) =
      encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 3) ![#2, #0] ▹ φ) := by
    simpa [List.ofFn_succ, encTerm] using cSubstList_encForm φ (![(#2 : Semiterm ℒₛₑₜ ℕ 3), #0])
  have h3 : cSubstList [0, 2] (encForm φ) =
      encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 4) ![#0, #1] ▹ φ) := by
    simpa [List.ofFn_succ, encTerm] using cSubstList_encForm φ (![(#0 : Semiterm ℒₛₑₜ ℕ 4), #1])
  rw [h1, h2, h3]
  have heq1 : ((Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 2) ![#1, #0] ▹ φ) ⇜
      (#0 :> fun x : Fin 1 => #(BinderNotation.finSuccItr x 1))) =
      Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 2) ![#1, #0] ▹ φ := by
    change Semiformula.rewAux _ (Semiformula.rewAux _ φ) = _
    rw [rewAux_comp_eq]; congr 1
    exact rew_ext (fun i => by fin_cases i <;> rfl) (fun _ => rfl)
  have heq2 : ((Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 2) ![#1, #0] ▹ φ) ⇜
      (#0 :> fun x : Fin 1 => #(BinderNotation.finSuccItr x 2))) =
      Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 3) ![#2, #0] ▹ φ := by
    change Semiformula.rewAux _ (Semiformula.rewAux _ φ) = _
    rw [rewAux_comp_eq]; congr 1
    exact rew_ext (fun i => by fin_cases i <;> rfl) (fun _ => rfl)
  have heq01 : Nat.pair 2 (Nat.pair 0 2) = encForm (Semiformula.rel Language.Set.Rel.eq ![#0, #1] : Semiproposition ℒₛₑₜ 3) := rfl
  have hm01 : Nat.pair 3 (Nat.pair 0 2) = encForm (Semiformula.rel Language.Set.Rel.mem ![#0, #1] : Semiproposition ℒₛₑₜ 3) := rfl
  have hm03 : Nat.pair 3 (Nat.pair 0 6) = encForm (Semiformula.rel Language.Set.Rel.mem ![#0, #3] : Semiproposition ℒₛₑₜ 4) := rfl
  rw [heq01, hm01, hm03, cImp_encForm]
  have hlhs_eq : Nat.pair 8 (Nat.pair 9 (Nat.pair 6 (Nat.pair
      (encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 2) ![#1, #0] ▹ φ))
      (Nat.pair 8 (encForm ((Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 3) ![#2, #0] ▹ φ) 🡒
        (Semiformula.rel Language.Set.Rel.eq ![#0, #1]))))))) =
      encForm (∀¹ (∃¹ ((Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 2) ![#1, #0] ▹ φ) ⋏
        (∀¹ ((Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 3) ![#2, #0] ▹ φ) 🡒
          (Semiformula.rel Language.Set.Rel.eq ![#0, #1])))))) := rfl
  have hex_eq : Nat.pair 9 (Nat.pair 6 (Nat.pair
      (encForm (Semiformula.rel Language.Set.Rel.mem ![#0, #3] : Semiproposition ℒₛₑₜ 4))
      (encForm (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 4) ![#0, #1] ▹ φ)))) =
      encForm (∃¹ ((Semiformula.rel Language.Set.Rel.mem ![#0, #3] : Semiproposition ℒₛₑₜ 4) ⋏
        (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 4) ![#0, #1] ▹ φ))) := rfl
  rw [hlhs_eq, hex_eq, cIff_encForm]
  have hrhs_eq : Nat.pair 8 (Nat.pair 9 (Nat.pair 8
      (encForm ((Semiformula.rel Language.Set.Rel.mem ![#0, #1] : Semiproposition ℒₛₑₜ 3) 🡘
        (∃¹ ((Semiformula.rel Language.Set.Rel.mem ![#0, #3] : Semiproposition ℒₛₑₜ 4) ⋏
          (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 4) ![#0, #1] ▹ φ))))))) =
      encForm (∀¹ (∃¹ (∀¹ ((Semiformula.rel Language.Set.Rel.mem ![#0, #1] : Semiproposition ℒₛₑₜ 3) 🡘
        (∃¹ ((Semiformula.rel Language.Set.Rel.mem ![#0, #3] : Semiproposition ℒₛₑₜ 4) ⋏
          (Rew.subst (L := ℒₛₑₜ) (ξ := ℕ) (n := 2) (n' := 4) ![#0, #1] ▹ φ))))))) := rfl
  rw [hrhs_eq, cImp_encForm]
  apply congrArg encForm
  simp only [Semiformula.existsUnique, Semiformula.bexsMem, heq1, heq2]
  rfl

/-- Encode a ZFC axiom from a witness `(kind, φ_code)`. -/
def cZFCAxiomOf (w : ℕ × ℕ) : ℕ :=
  match w.1 with
  | 0 => encSent (Theory.Eq.refl ℒₛₑₜ)
  | 1 => encSent (Theory.Eq.symm ℒₛₑₜ)
  | 2 => encSent (Theory.Eq.trans ℒₛₑₜ)
  | 3 => encSent (Theory.Eq.relExt Language.Set.Rel.eq)
  | 4 => encSent (Theory.Eq.relExt Language.Set.Rel.mem)
  | 5 => encSent Axiom.empty
  | 6 => encSent Axiom.extentionality
  | 7 => encSent Axiom.pairing
  | 8 => encSent Axiom.union
  | 9 => encSent Axiom.power
  | 10 => encSent Axiom.infinity
  | 11 => encSent Axiom.foundation
  | 12 => encSent Axiom.choice
  | 13 => cSepSchema w.2
  | _ => cRepSchema w.2

def cValidZFCWitness (w : ℕ × ℕ) : Bool :=
  match w.1 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => true
  | 13 => cIsWf 1 w.2
  | 14 => cIsWf 2 w.2
  | _ => false

lemma primrec_cZFCAxiomOf : Primrec cZFCAxiomOf := by
  have h : Primrec (fun w : ℕ × ℕ =>
      if w.1 = 0 then encSent (Theory.Eq.refl ℒₛₑₜ)
      else if w.1 = 1 then encSent (Theory.Eq.symm ℒₛₑₜ)
      else if w.1 = 2 then encSent (Theory.Eq.trans ℒₛₑₜ)
      else if w.1 = 3 then encSent (Theory.Eq.relExt Language.Set.Rel.eq)
      else if w.1 = 4 then encSent (Theory.Eq.relExt Language.Set.Rel.mem)
      else if w.1 = 5 then encSent Axiom.empty
      else if w.1 = 6 then encSent Axiom.extentionality
      else if w.1 = 7 then encSent Axiom.pairing
      else if w.1 = 8 then encSent Axiom.union
      else if w.1 = 9 then encSent Axiom.power
      else if w.1 = 10 then encSent Axiom.infinity
      else if w.1 = 11 then encSent Axiom.foundation
      else if w.1 = 12 then encSent Axiom.choice
      else if w.1 = 13 then cSepSchema w.2
      else cRepSchema w.2) := by
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 8)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 9)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 10)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 11)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 12)) (Primrec.const _) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 13))
      (primrec_cSepSchema.comp Primrec.snd) (primrec_cRepSchema.comp Primrec.snd)
  exact h.of_eq fun ⟨k, c⟩ => by
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 =>
      simp only [cZFCAxiomOf, Nat.reduceEqDiff, ↓reduceIte]
    | k + 14 =>
      unfold cZFCAxiomOf
      simp only [show k + 14 ≠ 0 by omega, show k + 14 ≠ 1 by omega, show k + 14 ≠ 2 by omega,
        show k + 14 ≠ 3 by omega, show k + 14 ≠ 4 by omega, show k + 14 ≠ 5 by omega,
        show k + 14 ≠ 6 by omega, show k + 14 ≠ 7 by omega, show k + 14 ≠ 8 by omega,
        show k + 14 ≠ 9 by omega, show k + 14 ≠ 10 by omega, show k + 14 ≠ 11 by omega,
        show k + 14 ≠ 12 by omega, show k + 14 ≠ 13 by omega, ↓reduceIte]

lemma primrec_cValidZFCWitness : Primrec cValidZFCWitness := by
  have h : Primrec (fun w : ℕ × ℕ =>
      if w.1 ≤ 12 then true
      else if w.1 = 13 then cIsWf 1 w.2
      else if w.1 = 14 then cIsWf 2 w.2
      else false) := by
    refine Primrec.ite (Primrec.nat_le.comp Primrec.fst (Primrec.const 12)) (Primrec.const true) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 13))
      (primrec_cIsWf.comp (Primrec.const 1) Primrec.snd) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 14))
      (primrec_cIsWf.comp (Primrec.const 2) Primrec.snd) (Primrec.const false)
  exact h.of_eq fun ⟨k, c⟩ => by
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => rfl
    | k + 15 => simp [cValidZFCWitness]

lemma exists_zfc_of_cValidZFCWitness {w : ℕ × ℕ} (hw : cValidZFCWitness w = true) :
    ∃ ψ : Sentence ℒₛₑₜ, ψ ∈ 𝗭𝗙𝗖 ∧ encSent ψ = cZFCAxiomOf w := by
  rcases w with ⟨k, c⟩
  match k with
  | 0 => exact ⟨Theory.Eq.refl ℒₛₑₜ, Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.refl), rfl⟩
  | 1 => exact ⟨Theory.Eq.symm ℒₛₑₜ, Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.symm), rfl⟩
  | 2 => exact ⟨Theory.Eq.trans ℒₛₑₜ, Or.inl (ZermeloFraenkel.axiom_of_equality _ Theory.eqAxiom.trans), rfl⟩
  | 3 => exact ⟨Theory.Eq.relExt Language.Set.Rel.eq, Or.inl (ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt _)), rfl⟩
  | 4 => exact ⟨Theory.Eq.relExt Language.Set.Rel.mem, Or.inl (ZermeloFraenkel.axiom_of_equality _ (Theory.eqAxiom.relExt _)), rfl⟩
  | 5 => exact ⟨Axiom.empty, Or.inl ZermeloFraenkel.axiom_of_empty_set, rfl⟩
  | 6 => exact ⟨Axiom.extentionality, Or.inl ZermeloFraenkel.axiom_of_extentionality, rfl⟩
  | 7 => exact ⟨Axiom.pairing, Or.inl ZermeloFraenkel.axiom_of_pairing, rfl⟩
  | 8 => exact ⟨Axiom.union, Or.inl ZermeloFraenkel.axiom_of_union, rfl⟩
  | 9 => exact ⟨Axiom.power, Or.inl ZermeloFraenkel.axiom_of_power_set, rfl⟩
  | 10 => exact ⟨Axiom.infinity, Or.inl ZermeloFraenkel.axiom_of_infinity, rfl⟩
  | 11 => exact ⟨Axiom.foundation, Or.inl ZermeloFraenkel.axiom_of_foundation, rfl⟩
  | 12 => exact ⟨Axiom.choice, Or.inr rfl, rfl⟩
  | 13 =>
    have hc : cIsWf 1 c = true := hw
    obtain ⟨φ, rfl⟩ := exists_encForm_of_cIsWf hc
    exact ⟨Axiom.separationSchema φ, Or.inl (ZermeloFraenkel.axiom_of_separation φ), (cSepSchema_encForm φ).symm⟩
  | 14 =>
    have hc : cIsWf 2 c = true := hw
    obtain ⟨φ, rfl⟩ := exists_encForm_of_cIsWf hc
    exact ⟨Axiom.replacementSchema φ, Or.inl (ZermeloFraenkel.axiom_of_replacement φ), (cRepSchema_encForm φ).symm⟩
  | k + 15 => cases hw

lemma exists_cValidZFCWitness_of_mem {ψ : Sentence ℒₛₑₜ} (hψ : ψ ∈ 𝗭𝗙𝗖) :
    ∃ w : ℕ × ℕ, cValidZFCWitness w = true ∧ cZFCAxiomOf w = encSent ψ := by
  rcases hψ with hzf | hac
  · cases hzf with
    | axiom_of_equality _ heq =>
      cases heq with
      | refl => exact ⟨(0, 0), rfl, rfl⟩
      | symm => exact ⟨(1, 0), rfl, rfl⟩
      | trans => exact ⟨(2, 0), rfl, rfl⟩
      | funcExt f => exact Empty.elim f
      | relExt r => cases r with
        | eq => exact ⟨(3, 0), rfl, rfl⟩
        | mem => exact ⟨(4, 0), rfl, rfl⟩
    | axiom_of_empty_set => exact ⟨(5, 0), rfl, rfl⟩
    | axiom_of_extentionality => exact ⟨(6, 0), rfl, rfl⟩
    | axiom_of_pairing => exact ⟨(7, 0), rfl, rfl⟩
    | axiom_of_union => exact ⟨(8, 0), rfl, rfl⟩
    | axiom_of_power_set => exact ⟨(9, 0), rfl, rfl⟩
    | axiom_of_infinity => exact ⟨(10, 0), rfl, rfl⟩
    | axiom_of_foundation => exact ⟨(11, 0), rfl, rfl⟩
    | axiom_of_separation φ => exact ⟨(13, encForm φ), by simp [cValidZFCWitness, cIsWf_encForm], cSepSchema_encForm φ⟩
    | axiom_of_replacement φ => exact ⟨(14, encForm φ), by simp [cValidZFCWitness, cIsWf_encForm], cRepSchema_encForm φ⟩
  · cases hac; exact ⟨(12, 0), rfl, rfl⟩

/- Multiset equality and subset on `List ℕ` -/

def cListCount (l : List ℕ) (x : ℕ) : ℕ := l.count x

lemma primrec_cListCount : Primrec₂ cListCount := by
  have hstep : Primrec (fun p : (List ℕ × ℕ) × ℕ × ℕ => if p.2.1 = p.1.2 then p.2.2 + 1 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.fst (Primrec.const 0) hstep.to₂).of_eq fun p => by
    rcases p with ⟨l, x⟩
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.foldr_cons, cListCount, List.count_cons] at ih ⊢
      rw [ih]
      by_cases h : a = x <;> simp [h, beq_iff_eq]

lemma primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec (fun a => (f a).all (p a)) := by
  have hstep : Primrec (fun q : α × β × Bool => p q.1 q.2.1 && q.2.2) :=
    Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr hf (Primrec.const true) hstep.to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons b l ih => simp [List.foldr_cons, List.all_cons, ih]

def cMSetLe (l₁ l₂ : List ℕ) : Bool :=
  l₁.all fun x => decide (cListCount l₁ x ≤ cListCount l₂ x)

def cMSetEq (l₁ l₂ : List ℕ) : Bool := cMSetLe l₁ l₂ && cMSetLe l₂ l₁

def cMSetSubset (l₁ l₂ : List ℕ) : Bool :=
  l₁.all fun x => decide (1 ≤ cListCount l₂ x)

lemma primrec_cMSetLe : Primrec₂ cMSetLe :=
  primrec_list_all Primrec.fst
    (primrec_decide (Primrec.nat_le.comp
      (primrec_cListCount.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (primrec_cListCount.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂

lemma primrec_cMSetEq : Primrec₂ cMSetEq :=
  Primrec.and.comp primrec_cMSetLe (primrec_cMSetLe.comp Primrec.snd Primrec.fst)

lemma primrec_cMSetSubset : Primrec₂ cMSetSubset :=
  primrec_list_all Primrec.fst
    (primrec_decide (Primrec.nat_le.comp (Primrec.const 1)
      (primrec_cListCount.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂

lemma cMSetLe_iff (l₁ l₂ : List ℕ) :
    cMSetLe l₁ l₂ = true ↔ (l₁ : Multiset ℕ) ≤ (l₂ : Multiset ℕ) := by
  rw [Multiset.le_iff_count]
  simp only [cMSetLe, List.all_eq_true, cListCount, Multiset.coe_count]
  constructor
  · intro h x
    by_cases hx : x ∈ l₁
    · exact of_decide_eq_true (h x hx)
    · simp [List.count_eq_zero.mpr hx]
  · intro h x _
    exact decide_eq_true (h x)

lemma cMSetEq_iff (l₁ l₂ : List ℕ) :
    cMSetEq l₁ l₂ = true ↔ (l₁ : Multiset ℕ) = (l₂ : Multiset ℕ) := by
  simp only [cMSetEq, Bool.and_eq_true, cMSetLe_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩

lemma cMSetSubset_iff (l₁ l₂ : List ℕ) :
    cMSetSubset l₁ l₂ = true ↔ (l₁ : Multiset ℕ) ⊆ (l₂ : Multiset ℕ) := by
  simp only [cMSetSubset, List.all_eq_true, decide_eq_true_eq, cListCount,
    Multiset.subset_iff, Multiset.mem_coe, Nat.one_le_iff_ne_zero, ne_eq, List.count_eq_zero, not_not]

/- Flat proof-trace checker for `Derivation` -/

abbrev TraceStep := List ℕ × ℕ × List ℕ × List ℕ

def cGetSeq (tr : List TraceStep) (i : ℕ) : List ℕ :=
  (tr.getD i ([], 0, [], [])).1

lemma primrec_cGetSeq : Primrec₂ cGetSeq :=
  Primrec.fst.comp
    ((Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const (([], 0, [], []) : TraceStep)) Primrec₂.right).of_eq fun p => by
        cases h : p.1[p.2]? <;> simp [List.getD_eq_getElem?_getD, h])

def cCheckStep (tr : List TraceStep) (k : ℕ) : Bool :=
  let st := tr.getD k ([], 0, [], [])
  let seq := st.1
  let hint := st.2.1
  let Γ := st.2.2.1
  let Δ := st.2.2.2
  let tag := hint.unpair.1
  let arg := hint.unpair.2
  seq.all (cIsWf 0) &&
  if tag = 0 then
    -- identity: arg = pair r (pair x y) with r ≤ 1
    let r := arg.unpair.1
    let xy := arg.unpair.2
    let x := xy.unpair.1
    let y := xy.unpair.2
    decide (r ≤ 1) &&
      cMSetEq seq [Nat.pair (2 + r) (Nat.pair (2 * x + 1) (2 * y + 1)),
                   Nat.pair (4 + r) (Nat.pair (2 * x + 1) (2 * y + 1))]
  else if tag = 1 then
    -- verum
    cMSetEq seq [Nat.pair 0 0]
  else if tag = 2 then
    -- contraction: arg = i < k
    decide (arg < k) && cMSetSubset (cGetSeq tr arg) seq
  else if tag = 3 then
    -- cut: arg = pair i (pair j φ)
    let i := arg.unpair.1
    let j := arg.unpair.2.unpair.1
    let φ := arg.unpair.2.unpair.2
    decide (i < k) && decide (j < k) && cIsWf 0 φ &&
      cMSetEq (cGetSeq tr i) (φ :: Γ) &&
      cMSetEq (cGetSeq tr j) (cNeg φ :: Δ) &&
      cMSetEq seq (Γ ++ Δ)
  else if tag = 4 then
    -- or: arg = pair i (pair φ ψ)
    let i := arg.unpair.1
    let φ := arg.unpair.2.unpair.1
    let ψ := arg.unpair.2.unpair.2
    decide (i < k) && cIsWf 0 φ && cIsWf 0 ψ &&
      cMSetEq (cGetSeq tr i) (φ :: ψ :: Γ) &&
      cMSetEq seq (Nat.pair 7 (Nat.pair φ ψ) :: Γ)
  else if tag = 5 then
    -- and: arg = pair i (pair j (pair φ ψ))
    let i := arg.unpair.1
    let j := arg.unpair.2.unpair.1
    let φ := arg.unpair.2.unpair.2.unpair.1
    let ψ := arg.unpair.2.unpair.2.unpair.2
    decide (i < k) && decide (j < k) && cIsWf 0 φ && cIsWf 0 ψ &&
      cMSetEq (cGetSeq tr i) (φ :: Γ) &&
      cMSetEq (cGetSeq tr j) (ψ :: Γ) &&
      cMSetEq seq (Nat.pair 6 (Nat.pair φ ψ) :: Γ)
  else if tag = 6 then
    -- all: arg = pair i φ
    let i := arg.unpair.1
    let φ := arg.unpair.2
    decide (i < k) && cIsWf 1 φ &&
      cMSetEq (cGetSeq tr i) (cFree φ :: Γ.map cShift) &&
      cMSetEq seq (Nat.pair 8 φ :: Γ)
  else if tag = 7 then
    -- exs: arg = pair i (pair x φ)
    let i := arg.unpair.1
    let x := arg.unpair.2.unpair.1
    let φ := arg.unpair.2.unpair.2
    decide (i < k) && cIsWf 1 φ &&
      cMSetEq (cGetSeq tr i) (cSubst0 x φ :: Γ) &&
      cMSetEq seq (Nat.pair 9 φ :: Γ)
  else false

def cCheckTrace (tr : List TraceStep) : Bool :=
  (List.range tr.length).all (cCheckStep tr)

lemma primrec_cCheckStep : Primrec₂ cCheckStep := by
  let P := List TraceStep × ℕ
  have htr : Primrec (fun p : P => p.1) := Primrec.fst
  have hk : Primrec (fun p : P => p.2) := Primrec.snd
  have hst : Primrec (fun p : P => p.1.getD p.2 ([], 0, [], [])) :=
    (Primrec.option_casesOn (Primrec.list_getElem?.comp htr hk)
      (Primrec.const (([], 0, [], []) : TraceStep)) Primrec₂.right).of_eq fun p => by
        cases h : p.1[p.2]? <;> simp [List.getD_eq_getElem?_getD, h]
  have hseq : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).1) := Primrec.fst.comp hst
  have hhint : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1) := Primrec.fst.comp (Primrec.snd.comp hst)
  have hΓ : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have hΔ : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have htag : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hhint)
  have harg : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hhint)
  have ha1 : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp harg)
  have ha2 : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp harg)
  have ha21 : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp ha2)
  have ha22 : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp ha2)
  have ha221 : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp ha22)
  have ha222 : Primrec (fun p : P => (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp ha22)
  unfold cCheckStep
  refine Primrec.and.comp (primrec_list_all hseq (primrec_cIsWf.comp (Primrec.const 0) Primrec.snd).to₂) ?_
  -- tag 0
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) ?_ ?_
  · have h2x : Primrec (fun p : P => 2 * (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2.unpair.1 + 1) :=
      Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) ha21)
    have h2y : Primrec (fun p : P => 2 * (p.1.getD p.2 ([], 0, [], [])).2.1.unpair.2.unpair.2.unpair.2 + 1) :=
      Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) ha22)
    have hxy := primrec_natPair.comp h2x h2y
    exact Primrec.and.comp (primrec_decide (Primrec.nat_le.comp ha1 (Primrec.const 1)))
      (primrec_cMSetEq.comp hseq
        (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.nat_add.comp (Primrec.const 2) ha1) hxy)
          (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.nat_add.comp (Primrec.const 4) ha1) hxy)
            (Primrec.const []))))
  -- tag 1
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
    (primrec_cMSetEq.comp hseq (Primrec.const [Nat.pair 0 0])) ?_
  -- tag 2
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2))
    (Primrec.and.comp (primrec_decide (Primrec.nat_lt.comp harg hk))
      (primrec_cMSetSubset.comp (primrec_cGetSeq.comp htr harg) hseq)) ?_
  -- tag 3
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3))
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp
          (Primrec.and.comp
            (Primrec.and.comp (primrec_decide (Primrec.nat_lt.comp ha1 hk))
              (primrec_decide (Primrec.nat_lt.comp ha21 hk)))
            (primrec_cIsWf.comp (Primrec.const 0) ha22))
          (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha1) (Primrec.list_cons.comp ha22 hΓ)))
        (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha21)
          (Primrec.list_cons.comp (primrec_cNeg.comp ha22) hΔ)))
      (primrec_cMSetEq.comp hseq (Primrec.list_append.comp hΓ hΔ))) ?_
  -- tag 4
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 4))
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp
          (Primrec.and.comp (primrec_decide (Primrec.nat_lt.comp ha1 hk))
            (primrec_cIsWf.comp (Primrec.const 0) ha21))
          (primrec_cIsWf.comp (Primrec.const 0) ha22))
        (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha1)
          (Primrec.list_cons.comp ha21 (Primrec.list_cons.comp ha22 hΓ))))
      (primrec_cMSetEq.comp hseq
        (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 7) (primrec_natPair.comp ha21 ha22)) hΓ))) ?_
  -- tag 5
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 5))
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp
          (Primrec.and.comp
            (Primrec.and.comp
              (Primrec.and.comp (primrec_decide (Primrec.nat_lt.comp ha1 hk))
                (primrec_decide (Primrec.nat_lt.comp ha21 hk)))
              (primrec_cIsWf.comp (Primrec.const 0) ha221))
            (primrec_cIsWf.comp (Primrec.const 0) ha222))
          (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha1) (Primrec.list_cons.comp ha221 hΓ)))
        (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha21) (Primrec.list_cons.comp ha222 hΓ)))
      (primrec_cMSetEq.comp hseq
        (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 6) (primrec_natPair.comp ha221 ha222)) hΓ))) ?_
  -- tag 6
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 6))
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp (primrec_decide (Primrec.nat_lt.comp ha1 hk))
          (primrec_cIsWf.comp (Primrec.const 1) ha2))
        (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha1)
          (Primrec.list_cons.comp (primrec_cFree.comp ha2)
            (Primrec.list_map hΓ (primrec_cShift.comp Primrec.snd).to₂))))
      (primrec_cMSetEq.comp hseq
        (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 8) ha2) hΓ))) ?_
  -- tag 7
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 7))
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp (primrec_decide (Primrec.nat_lt.comp ha1 hk))
          (primrec_cIsWf.comp (Primrec.const 1) ha22))
        (primrec_cMSetEq.comp (primrec_cGetSeq.comp htr ha1)
          (Primrec.list_cons.comp (primrec_cSubst0.comp ha21 ha22) hΓ)))
      (primrec_cMSetEq.comp hseq
        (Primrec.list_cons.comp (primrec_natPair.comp (Primrec.const 9) ha22) hΓ)))
    (Primrec.const false)

lemma primrec_cCheckTrace : Primrec cCheckTrace :=
  primrec_list_all (primrec_list_range.comp Primrec.list_length) primrec_cCheckStep

/- Soundness & Completeness of `cCheckTrace` -/

private lemma exists_list_encForm_of_all_wf {l : List ℕ} (h : ∀ c ∈ l, cIsWf 0 c = true) :
    ∃ L : List (Proposition ℒₛₑₜ), L.map encForm = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons c l ih =>
    obtain ⟨φ, hφ⟩ := exists_encForm_of_cIsWf (h c (by simp))
    obtain ⟨L, hL⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨φ :: L, by simp [hφ, hL]⟩

private lemma multiset_eq_of_map_encForm_eq {Γ₁ Γ₂ : Sequent ℒₛₑₜ}
    (h : Γ₁.map encForm = Γ₂.map encForm) : Γ₁ = Γ₂ := by
  classical
  have hinj : Function.Injective (encForm (n := 0)) := fun _ _ he => encForm_inj he
  have hcnt : ∀ (Γ : Sequent ℒₛₑₜ) (φ : Proposition ℒₛₑₜ),
      Multiset.count (encForm φ) (Γ.map encForm) = Multiset.count φ Γ := by
    intro Γ φ
    refine Multiset.induction_on Γ (by simp) fun a s ih => ?_
    rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons, ih]
    simp [hinj.eq_iff]
  apply Multiset.ext.mpr
  intro φ
  have hc := congrArg (fun m => Multiset.count (encForm φ) m) h
  rwa [hcnt Γ₁ φ, hcnt Γ₂ φ] at hc

private lemma mset_cons_eq_add_singleton (a : ℕ) (l : List ℕ) :
    ((a :: l : List ℕ) : Multiset ℕ) = (l : Multiset ℕ) + {a} := by
  change a ::ₘ (l : Multiset ℕ) = (l : Multiset ℕ) + {a}
  rw [← Multiset.singleton_add, add_comm]

private lemma multiset_subset_of_map_encForm_subset {Γ₁ Γ₂ : Sequent ℒₛₑₜ}
    (h : Γ₁.map encForm ⊆ Γ₂.map encForm) : Γ₁ ⊆ Γ₂ := by
  intro φ hφ
  have hm : encForm φ ∈ Γ₂.map encForm := h (Multiset.mem_map_of_mem encForm hφ)
  obtain ⟨ψ, hψ, heq⟩ := Multiset.mem_map.mp hm
  rwa [encForm_inj heq] at hψ

lemma derivation_of_cCheckTrace {tr : List TraceStep} (htr : cCheckTrace tr = true) :
    ∀ k < tr.length, ∃ Γ : Sequent ℒₛₑₜ,
      Γ.map encForm = (cGetSeq tr k : Multiset ℕ) ∧ Nonempty (Derivation Γ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hstep : cCheckStep tr k = true := by
      simp only [cCheckTrace, List.all_eq_true, List.mem_range] at htr
      exact htr k hk
    unfold cCheckStep at hstep
    simp only [Bool.and_eq_true] at hstep
    set st := tr.getD k ([], 0, [], [])
    have hseq_eq : cGetSeq tr k = st.1 := rfl
    have hwf_seq : ∀ c ∈ st.1, cIsWf 0 c = true := by
      simpa [List.all_eq_true] using hstep.1
    obtain ⟨Lseq, hLseq⟩ := exists_list_encForm_of_all_wf hwf_seq
    set Γseq : Sequent ℒₛₑₜ := (Lseq : Multiset (Proposition ℒₛₑₜ))
    have hΓseq_map : Γseq.map encForm = (st.1 : Multiset ℕ) := by
      rw [Multiset.map_coe, hLseq]
    refine ⟨Γseq, hΓseq_map, ?_⟩
    have hbody := hstep.2
    set tag := st.2.1.unpair.1
    set arg := st.2.1.unpair.2
    set Γl := st.2.2.1
    set Δl := st.2.2.2
    by_cases ht0 : tag = 0
    · rw [if_pos ht0] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetEq_iff] at hbody
      set r := arg.unpair.1
      set x := arg.unpair.2.unpair.1
      set y := arg.unpair.2.unpair.2
      have hrel : ∃ R : (ℒₛₑₜ).Rel 2,
          Γseq = ⦃Semiformula.rel R ![&x, &y], Semiformula.nrel R ![&x, &y]⦄ := by
        by_cases hr : r = 0
        · refine ⟨Language.Set.Rel.eq, multiset_eq_of_map_encForm_eq ?_⟩
          rw [hΓseq_map, hbody.2, hr]; rfl
        · have hr1 : r = 1 := by omega
          refine ⟨Language.Set.Rel.mem, multiset_eq_of_map_encForm_eq ?_⟩
          rw [hΓseq_map, hbody.2, hr1]; rfl
      obtain ⟨R, hR⟩ := hrel
      rw [hR]
      exact ⟨Derivation.identity R ![&x, &y]⟩
    rw [if_neg ht0] at hbody
    by_cases ht1 : tag = 1
    · rw [if_pos ht1] at hbody
      rw [cMSetEq_iff] at hbody
      have hΓ : Γseq = ⦃⊤⦄ := multiset_eq_of_map_encForm_eq (by rw [hΓseq_map, hbody]; rfl)
      rw [hΓ]; exact ⟨Derivation.verum⟩
    rw [if_neg ht1] at hbody
    by_cases ht2 : tag = 2
    · rw [if_pos ht2] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetSubset_iff] at hbody
      obtain ⟨Γi, hΓi, ⟨di⟩⟩ := ih arg hbody.1 (lt_trans hbody.1 hk)
      have hsub : Γi ⊆ Γseq := multiset_subset_of_map_encForm_subset (by rw [hΓi, hΓseq_map]; exact hbody.2)
      exact ⟨Derivation.contraction di hsub⟩
    rw [if_neg ht2] at hbody
    by_cases ht3 : tag = 3
    · rw [if_pos ht3] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetEq_iff] at hbody
      set i := arg.unpair.1
      set j := arg.unpair.2.unpair.1
      set φc := arg.unpair.2.unpair.2
      obtain ⟨Γi, hΓi, ⟨di⟩⟩ := ih i hbody.1.1.1.1.1 (lt_trans hbody.1.1.1.1.1 hk)
      obtain ⟨Γj, hΓj, ⟨dj⟩⟩ := ih j hbody.1.1.1.1.2 (lt_trans hbody.1.1.1.1.2 hk)
      obtain ⟨φ, hφ⟩ := exists_encForm_of_cIsWf hbody.1.1.1.2
      have hΓl_wf : ∀ c ∈ Γl, cIsWf 0 c = true := by
        intro c hc
        have hm : c ∈ (st.1 : Multiset ℕ) := by
          rw [hbody.2]; exact Multiset.mem_coe.mpr (List.mem_append_left Δl hc)
        exact hwf_seq c (Multiset.mem_coe.mp hm)
      have hΔl_wf : ∀ c ∈ Δl, cIsWf 0 c = true := by
        intro c hc
        have hm : c ∈ (st.1 : Multiset ℕ) := by
          rw [hbody.2]; exact Multiset.mem_coe.mpr (List.mem_append_right Γl hc)
        exact hwf_seq c (Multiset.mem_coe.mp hm)
      obtain ⟨LΓ, hLΓ⟩ := exists_list_encForm_of_all_wf hΓl_wf
      obtain ⟨LΔ, hLΔ⟩ := exists_list_encForm_of_all_wf hΔl_wf
      set MΓ : Sequent ℒₛₑₜ := (LΓ : Multiset (Proposition ℒₛₑₜ))
      set MΔ : Sequent ℒₛₑₜ := (LΔ : Multiset (Proposition ℒₛₑₜ))
      have hMΓ : MΓ.map encForm = (Γl : Multiset ℕ) := by rw [Multiset.map_coe, hLΓ]
      have hMΔ : MΔ.map encForm = (Δl : Multiset ℕ) := by rw [Multiset.map_coe, hLΔ]
      have h1 : Γi = MΓ + ⦃φ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓi, hbody.1.1.2, ← hφ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      have h2 : Γj = MΔ + ⦃∼φ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓj, hbody.1.2, ← hφ, Multiset.map_add, hMΔ, cNeg_encForm, mset_cons_eq_add_singleton]; rfl)
      have h3 : Γseq = MΓ + MΔ := multiset_eq_of_map_encForm_eq (by
        rw [hΓseq_map, hbody.2, Multiset.map_add, hMΓ, hMΔ]; rfl)
      rw [h1] at di; rw [h2] at dj; rw [h3]
      exact ⟨Derivation.cut di dj⟩
    rw [if_neg ht3] at hbody
    by_cases ht4 : tag = 4
    · rw [if_pos ht4] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetEq_iff] at hbody
      set i := arg.unpair.1
      set φc := arg.unpair.2.unpair.1
      set ψc := arg.unpair.2.unpair.2
      obtain ⟨Γi, hΓi, ⟨di⟩⟩ := ih i hbody.1.1.1.1 (lt_trans hbody.1.1.1.1 hk)
      obtain ⟨φ, hφ⟩ := exists_encForm_of_cIsWf hbody.1.1.1.2
      obtain ⟨ψ, hψ⟩ := exists_encForm_of_cIsWf hbody.1.1.2
      have hΓl_wf : ∀ c ∈ Γl, cIsWf 0 c = true := by
        intro c hc
        have hm : c ∈ (st.1 : Multiset ℕ) := by rw [hbody.2]; simp [hc]
        exact hwf_seq c (Multiset.mem_coe.mp hm)
      obtain ⟨LΓ, hLΓ⟩ := exists_list_encForm_of_all_wf hΓl_wf
      set MΓ : Sequent ℒₛₑₜ := (LΓ : Multiset (Proposition ℒₛₑₜ))
      have hMΓ : MΓ.map encForm = (Γl : Multiset ℕ) := by rw [Multiset.map_coe, hLΓ]
      have h1 : Γi = MΓ + ⦃φ, ψ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓi, hbody.1.2, ← hφ, ← hψ, Multiset.map_add, hMΓ,
            mset_cons_eq_add_singleton, mset_cons_eq_add_singleton]
        change (Γl : Multiset ℕ) + {encForm ψ} + {encForm φ} = (Γl : Multiset ℕ) + (encForm φ ::ₘ {encForm ψ})
        rw [← Multiset.singleton_add, add_assoc, add_comm ({encForm ψ} : Multiset ℕ) {encForm φ}])
      have h2 : Γseq = MΓ + ⦃φ ⋎ ψ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓseq_map, hbody.2, ← hφ, ← hψ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      rw [h1] at di; rw [h2]
      exact ⟨Derivation.or di⟩
    rw [if_neg ht4] at hbody
    by_cases ht5 : tag = 5
    · rw [if_pos ht5] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetEq_iff] at hbody
      set i := arg.unpair.1
      set j := arg.unpair.2.unpair.1
      set φc := arg.unpair.2.unpair.2.unpair.1
      set ψc := arg.unpair.2.unpair.2.unpair.2
      obtain ⟨Γi, hΓi, ⟨di⟩⟩ := ih i hbody.1.1.1.1.1.1 (lt_trans hbody.1.1.1.1.1.1 hk)
      obtain ⟨Γj, hΓj, ⟨dj⟩⟩ := ih j hbody.1.1.1.1.1.2 (lt_trans hbody.1.1.1.1.1.2 hk)
      obtain ⟨φ, hφ⟩ := exists_encForm_of_cIsWf hbody.1.1.1.1.2
      obtain ⟨ψ, hψ⟩ := exists_encForm_of_cIsWf hbody.1.1.1.2
      have hΓl_wf : ∀ c ∈ Γl, cIsWf 0 c = true := by
        intro c hc
        have hm : c ∈ (st.1 : Multiset ℕ) := by rw [hbody.2]; simp [hc]
        exact hwf_seq c (Multiset.mem_coe.mp hm)
      obtain ⟨LΓ, hLΓ⟩ := exists_list_encForm_of_all_wf hΓl_wf
      set MΓ : Sequent ℒₛₑₜ := (LΓ : Multiset (Proposition ℒₛₑₜ))
      have hMΓ : MΓ.map encForm = (Γl : Multiset ℕ) := by rw [Multiset.map_coe, hLΓ]
      have h1 : Γi = MΓ + ⦃φ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓi, hbody.1.1.2, ← hφ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      have h2 : Γj = MΓ + ⦃ψ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓj, hbody.1.2, ← hψ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      have h3 : Γseq = MΓ + ⦃φ ⋏ ψ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓseq_map, hbody.2, ← hφ, ← hψ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      rw [h1] at di; rw [h2] at dj; rw [h3]
      exact ⟨Derivation.and di dj⟩
    rw [if_neg ht5] at hbody
    by_cases ht6 : tag = 6
    · rw [if_pos ht6] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetEq_iff] at hbody
      set i := arg.unpair.1
      set φc := arg.unpair.2
      obtain ⟨Γi, hΓi, ⟨di⟩⟩ := ih i hbody.1.1.1 (lt_trans hbody.1.1.1 hk)
      obtain ⟨φ, hφ⟩ := exists_encForm_of_cIsWf hbody.1.1.2
      have hΓl_wf : ∀ c ∈ Γl, cIsWf 0 c = true := by
        intro c hc
        have hm : c ∈ (st.1 : Multiset ℕ) := by rw [hbody.2]; simp [hc]
        exact hwf_seq c (Multiset.mem_coe.mp hm)
      obtain ⟨LΓ, hLΓ⟩ := exists_list_encForm_of_all_wf hΓl_wf
      set MΓ : Sequent ℒₛₑₜ := (LΓ : Multiset (Proposition ℒₛₑₜ))
      have hMΓ : MΓ.map encForm = (Γl : Multiset ℕ) := by rw [Multiset.map_coe, hLΓ]
      have hshift_map : (MΓ⁺).map encForm = ((Γl.map cShift) : Multiset ℕ) := by
        rw [Rewriting.shifts, Multiset.map_map, ← hLΓ, Multiset.map_coe, List.map_map]
        apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
        apply List.map_congr_left
        intro χ _
        exact (cShift_encForm χ).symm
      have h1 : Γi = MΓ⁺ + ⦃φ.free⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓi, hbody.1.2, ← hφ, Multiset.map_add, hshift_map, cFree_encForm, mset_cons_eq_add_singleton]; rfl)
      have h2 : Γseq = MΓ + ⦃∀¹ φ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓseq_map, hbody.2, ← hφ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      rw [h1] at di; rw [h2]
      exact ⟨Derivation.all di⟩
    rw [if_neg ht6] at hbody
    by_cases ht7 : tag = 7
    · rw [if_pos ht7] at hbody
      simp only [Bool.and_eq_true, decide_eq_true_eq, cMSetEq_iff] at hbody
      set i := arg.unpair.1
      set x := arg.unpair.2.unpair.1
      set φc := arg.unpair.2.unpair.2
      obtain ⟨Γi, hΓi, ⟨di⟩⟩ := ih i hbody.1.1.1 (lt_trans hbody.1.1.1 hk)
      obtain ⟨φ, hφ⟩ := exists_encForm_of_cIsWf hbody.1.1.2
      have hΓl_wf : ∀ c ∈ Γl, cIsWf 0 c = true := by
        intro c hc
        have hm : c ∈ (st.1 : Multiset ℕ) := by rw [hbody.2]; simp [hc]
        exact hwf_seq c (Multiset.mem_coe.mp hm)
      obtain ⟨LΓ, hLΓ⟩ := exists_list_encForm_of_all_wf hΓl_wf
      set MΓ : Sequent ℒₛₑₜ := (LΓ : Multiset (Proposition ℒₛₑₜ))
      have hMΓ : MΓ.map encForm = (Γl : Multiset ℕ) := by rw [Multiset.map_coe, hLΓ]
      have h1 : Γi = MΓ + ⦃φ/[(&x : Semiterm ℒₛₑₜ ℕ 0)]⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓi, hbody.1.2, ← hφ, Multiset.map_add, hMΓ, cSubst0_encForm, mset_cons_eq_add_singleton]; rfl)
      have h2 : Γseq = MΓ + ⦃∃¹ φ⦄ := multiset_eq_of_map_encForm_eq (by
        rw [hΓseq_map, hbody.2, ← hφ, Multiset.map_add, hMΓ, mset_cons_eq_add_singleton]; rfl)
      rw [h1] at di; rw [h2]
      exact ⟨Derivation.exs di⟩
    rw [if_neg ht7] at hbody
    simp at hbody

/- Helper for completeness: shifting trace indices when concatenating two traces -/

private def shiftHint (off : ℕ) (hint : ℕ) : ℕ :=
  let tag := hint.unpair.1
  let arg := hint.unpair.2
  if tag = 0 ∨ tag = 1 then hint
  else if tag = 2 then Nat.pair 2 (arg + off)
  else if tag = 3 then Nat.pair 3 (Nat.pair (arg.unpair.1 + off) (Nat.pair (arg.unpair.2.unpair.1 + off) arg.unpair.2.unpair.2))
  else if tag = 4 then Nat.pair 4 (Nat.pair (arg.unpair.1 + off) arg.unpair.2)
  else if tag = 5 then Nat.pair 5 (Nat.pair (arg.unpair.1 + off) (Nat.pair (arg.unpair.2.unpair.1 + off) arg.unpair.2.unpair.2))
  else if tag = 6 then Nat.pair 6 (Nat.pair (arg.unpair.1 + off) arg.unpair.2)
  else if tag = 7 then Nat.pair 7 (Nat.pair (arg.unpair.1 + off) arg.unpair.2)
  else hint

private def shiftTrace (off : ℕ) (tr : List TraceStep) : List TraceStep :=
  tr.map fun st => (st.1, shiftHint off st.2.1, st.2.2.1, st.2.2.2)

private lemma cCheckStep_append_left {tr₁ tr₂ : List TraceStep} {k : ℕ} (hk : k < tr₁.length)
    (h : cCheckStep tr₁ k = true) : cCheckStep (tr₁ ++ tr₂) k = true := by
  have hget : ∀ j < tr₁.length, (tr₁ ++ tr₂).getD j ([], 0, [], []) = tr₁.getD j ([], 0, [], []) := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have hseq : ∀ j < k, cGetSeq (tr₁ ++ tr₂) j = cGetSeq tr₁ j := fun j hj => by
    unfold cGetSeq; rw [hget j (lt_trans hj hk)]
  unfold cCheckStep at h ⊢
  rw [hget k hk]
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have hb := h.2
  set st := tr₁.getD k ([], 0, [], [])
  set tag := st.2.1.unpair.1
  set arg := st.2.1.unpair.2
  by_cases ht0 : tag = 0; · rwa [if_pos ht0] at hb ⊢
  rw [if_neg ht0] at hb ⊢
  by_cases ht1 : tag = 1; · rwa [if_pos ht1] at hb ⊢
  rw [if_neg ht1] at hb ⊢
  by_cases ht2 : tag = 2
  · rw [if_pos ht2] at hb ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, by rw [hseq arg hb.1]; exact hb.2⟩
  rw [if_neg ht2] at hb ⊢
  by_cases ht3 : tag = 3
  · rw [if_pos ht3] at hb ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    rw [hseq arg.unpair.1 hb.1.1.1.1.1, hseq arg.unpair.2.unpair.1 hb.1.1.1.1.2]
    exact hb
  rw [if_neg ht3] at hb ⊢
  by_cases ht4 : tag = 4
  · rw [if_pos ht4] at hb ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    rw [hseq arg.unpair.1 hb.1.1.1.1]
    exact hb
  rw [if_neg ht4] at hb ⊢
  by_cases ht5 : tag = 5
  · rw [if_pos ht5] at hb ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    rw [hseq arg.unpair.1 hb.1.1.1.1.1.1, hseq arg.unpair.2.unpair.1 hb.1.1.1.1.1.2]
    exact hb
  rw [if_neg ht5] at hb ⊢
  by_cases ht6 : tag = 6
  · rw [if_pos ht6] at hb ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    rw [hseq arg.unpair.1 hb.1.1.1]
    exact hb
  rw [if_neg ht6] at hb ⊢
  by_cases ht7 : tag = 7
  · rw [if_pos ht7] at hb ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    rw [hseq arg.unpair.1 hb.1.1.1]
    exact hb
  rw [if_neg ht7] at hb ⊢; exact hb

private lemma cCheckStep_append_right {tr₁ tr₂ : List TraceStep} {k : ℕ} (hk : k < tr₂.length)
    (h : cCheckStep tr₂ k = true) :
    cCheckStep (tr₁ ++ shiftTrace tr₁.length tr₂) (tr₁.length + k) = true := by
  have hget : ∀ j < tr₂.length,
      (tr₁ ++ shiftTrace tr₁.length tr₂).getD (tr₁.length + j) ([], 0, [], []) =
        ((tr₂.getD j ([], 0, [], [])).1, shiftHint tr₁.length (tr₂.getD j ([], 0, [], [])).2.1,
          (tr₂.getD j ([], 0, [], [])).2.2.1, (tr₂.getD j ([], 0, [], [])).2.2.2) := by
    intro j hj
    simp only [shiftTrace, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
  have hseq : ∀ j < tr₂.length, cGetSeq (tr₁ ++ shiftTrace tr₁.length tr₂) (tr₁.length + j) = cGetSeq tr₂ j := by
    intro j hj; unfold cGetSeq; rw [hget j hj]
  unfold cCheckStep at h ⊢
  rw [hget k hk]
  dsimp only
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have hb := h.2
  set st := tr₂.getD k ([], 0, [], [])
  set tag := st.2.1.unpair.1
  set arg := st.2.1.unpair.2
  by_cases ht0 : tag = 0
  · have hs : shiftHint tr₁.length st.2.1 = st.2.1 := by unfold shiftHint; rw [if_pos (Or.inl ht0)]
    rw [hs]; rwa [if_pos ht0] at hb ⊢
  rw [if_neg ht0] at hb
  by_cases ht1 : tag = 1
  · have hs : shiftHint tr₁.length st.2.1 = st.2.1 := by unfold shiftHint; rw [if_pos (Or.inr ht1)]
    rw [hs, if_neg ht0]; rwa [if_pos ht1] at hb ⊢
  rw [if_neg ht1] at hb
  by_cases ht2 : tag = 2
  · have hs : shiftHint tr₁.length st.2.1 = Nat.pair 2 (arg + tr₁.length) := by
      unfold shiftHint; rw [if_neg (by omega), if_pos ht2]
    rw [hs]
    simp only [Nat.unpair_pair, OfNat.ofNat_ne_zero, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ht2] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [Nat.add_comm arg tr₁.length, hseq arg (lt_trans hb.1 hk)]
    exact ⟨by omega, hb.2⟩
  rw [if_neg ht2] at hb
  by_cases ht3 : tag = 3
  · have hs : shiftHint tr₁.length st.2.1 =
        Nat.pair 3 (Nat.pair (arg.unpair.1 + tr₁.length)
          (Nat.pair (arg.unpair.2.unpair.1 + tr₁.length) arg.unpair.2.unpair.2)) := by
      unfold shiftHint; rw [if_neg (by omega), if_neg ht2, if_pos ht3]
    rw [hs]
    simp only [Nat.unpair_pair, OfNat.ofNat_ne_zero, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ht3] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [Nat.add_comm arg.unpair.1 tr₁.length, hseq arg.unpair.1 (lt_trans hb.1.1.1.1.1 hk),
        Nat.add_comm arg.unpair.2.unpair.1 tr₁.length, hseq arg.unpair.2.unpair.1 (lt_trans hb.1.1.1.1.2 hk)]
    exact ⟨⟨⟨⟨⟨by omega, by omega⟩, hb.1.1.1.2⟩, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  rw [if_neg ht3] at hb
  by_cases ht4 : tag = 4
  · have hs : shiftHint tr₁.length st.2.1 = Nat.pair 4 (Nat.pair (arg.unpair.1 + tr₁.length) arg.unpair.2) := by
      unfold shiftHint; rw [if_neg (by omega), if_neg ht2, if_neg ht3, if_pos ht4]
    rw [hs]
    simp only [Nat.unpair_pair, OfNat.ofNat_ne_zero, show (4 : ℕ) ≠ 1 by decide,
      show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ht4] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [Nat.add_comm arg.unpair.1 tr₁.length, hseq arg.unpair.1 (lt_trans hb.1.1.1.1 hk)]
    exact ⟨⟨⟨⟨by omega, hb.1.1.1.2⟩, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  rw [if_neg ht4] at hb
  by_cases ht5 : tag = 5
  · have hs : shiftHint tr₁.length st.2.1 =
        Nat.pair 5 (Nat.pair (arg.unpair.1 + tr₁.length)
          (Nat.pair (arg.unpair.2.unpair.1 + tr₁.length) arg.unpair.2.unpair.2)) := by
      unfold shiftHint; rw [if_neg (by omega), if_neg ht2, if_neg ht3, if_neg ht4, if_pos ht5]
    rw [hs]
    simp only [Nat.unpair_pair, OfNat.ofNat_ne_zero, show (5 : ℕ) ≠ 1 by decide,
      show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ht5] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [Nat.add_comm arg.unpair.1 tr₁.length, hseq arg.unpair.1 (lt_trans hb.1.1.1.1.1.1 hk),
        Nat.add_comm arg.unpair.2.unpair.1 tr₁.length, hseq arg.unpair.2.unpair.1 (lt_trans hb.1.1.1.1.1.2 hk)]
    exact ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, hb.1.1.1.1.2⟩, hb.1.1.1.2⟩, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  rw [if_neg ht5] at hb
  by_cases ht6 : tag = 6
  · have hs : shiftHint tr₁.length st.2.1 = Nat.pair 6 (Nat.pair (arg.unpair.1 + tr₁.length) arg.unpair.2) := by
      unfold shiftHint; rw [if_neg (by omega), if_neg ht2, if_neg ht3, if_neg ht4, if_neg ht5, if_pos ht6]
    rw [hs]
    simp only [Nat.unpair_pair, OfNat.ofNat_ne_zero, show (6 : ℕ) ≠ 1 by decide,
      show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide,
      show (6 : ℕ) ≠ 5 by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ht6] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [Nat.add_comm arg.unpair.1 tr₁.length, hseq arg.unpair.1 (lt_trans hb.1.1.1 hk)]
    exact ⟨⟨⟨by omega, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  rw [if_neg ht6] at hb
  by_cases ht7 : tag = 7
  · have hs : shiftHint tr₁.length st.2.1 = Nat.pair 7 (Nat.pair (arg.unpair.1 + tr₁.length) arg.unpair.2) := by
      unfold shiftHint; rw [if_neg (by omega), if_neg ht2, if_neg ht3, if_neg ht4, if_neg ht5, if_neg ht6, if_pos ht7]
    rw [hs]
    simp only [Nat.unpair_pair, OfNat.ofNat_ne_zero, show (7 : ℕ) ≠ 1 by decide,
      show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 4 by decide,
      show (7 : ℕ) ≠ 5 by decide, show (7 : ℕ) ≠ 6 by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_pos ht7] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [Nat.add_comm arg.unpair.1 tr₁.length, hseq arg.unpair.1 (lt_trans hb.1.1.1 hk)]
    exact ⟨⟨⟨by omega, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  rw [if_neg ht7] at hb; simp at hb

private lemma cCheckTrace_append_shift {tr₁ tr₂ : List TraceStep}
    (h1 : cCheckTrace tr₁ = true) (h2 : cCheckTrace tr₂ = true) :
    cCheckTrace (tr₁ ++ shiftTrace tr₁.length tr₂) = true := by
  simp only [cCheckTrace, List.all_eq_true, List.mem_range, List.length_append, shiftTrace, List.length_map] at h1 h2 ⊢
  intro k hk
  by_cases hlt : k < tr₁.length
  · exact cCheckStep_append_left hlt (h1 k hlt)
  · have hk2 : k - tr₁.length < tr₂.length := by omega
    have heq : k = tr₁.length + (k - tr₁.length) := by omega
    rw [heq]
    exact cCheckStep_append_right hk2 (h2 (k - tr₁.length) hk2)

private lemma cCheckTrace_snoc {tr : List TraceStep} {st : TraceStep}
    (htr : cCheckTrace tr = true) (hst : cCheckStep (tr ++ [st]) tr.length = true) :
    cCheckTrace (tr ++ [st]) = true := by
  simp only [cCheckTrace, List.all_eq_true, List.mem_range, List.length_append, List.length_singleton] at htr ⊢
  intro k hk
  by_cases hlt : k < tr.length
  · exact cCheckStep_append_left hlt (htr k hlt)
  · have heq : k = tr.length := by omega
    rwa [heq]

private lemma term_zero_eq_fvar (t : Semiterm ℒₛₑₜ ℕ 0) : ∃ x : ℕ, t = &x := by
  cases t with
  | bvar i => exact Fin.elim0 i
  | fvar x => exact ⟨x, rfl⟩
  | func f _ => exact Empty.elim f

lemma exists_trace_of_derivation {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    ∃ tr : List TraceStep, 0 < tr.length ∧ cCheckTrace tr = true ∧
      (cGetSeq tr (tr.length - 1) : Multiset ℕ) = Γ.map encForm := by
  induction d with
  | identity r v =>
    cases r with
    | eq =>
      obtain ⟨x, hx⟩ := term_zero_eq_fvar (v 0)
      obtain ⟨y, hy⟩ := term_zero_eq_fvar (v 1)
      let seq := [Nat.pair 2 (Nat.pair (2 * x + 1) (2 * y + 1)),
                  Nat.pair 4 (Nat.pair (2 * x + 1) (2 * y + 1))]
      refine ⟨[(seq, Nat.pair 0 (Nat.pair 0 (Nat.pair x y)), [], [])], by simp, ?_, ?_⟩
      · simp only [cCheckTrace, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true]
        unfold cCheckStep
        simp only [List.getD_cons_zero, seq, Nat.unpair_pair, ↓reduceIte, Bool.and_eq_true,
          decide_eq_true_eq, List.all_cons, List.all_nil, Bool.and_true, cMSetEq_iff]
        refine ⟨⟨?_, ?_⟩, by omega, trivial⟩
        · simpa [encForm] using cIsWf_encForm (Semiformula.rel (L := ℒₛₑₜ) (ξ := ℕ) (n := 0) Language.Set.Rel.eq ![&x, &y])
        · simpa [encForm] using cIsWf_encForm (Semiformula.nrel (L := ℒₛₑₜ) (ξ := ℕ) (n := 0) Language.Set.Rel.eq ![&x, &y])
      · simp only [cGetSeq, List.length_singleton, Nat.sub_self, List.getD_cons_zero, seq,
          Multiset.map_add, Multiset.atom, Multiset.map_singleton, encForm, hx, hy, encTerm_fvar]
        rw [mset_cons_eq_add_singleton, add_comm]
        rfl
    | mem =>
      obtain ⟨x, hx⟩ := term_zero_eq_fvar (v 0)
      obtain ⟨y, hy⟩ := term_zero_eq_fvar (v 1)
      let seq := [Nat.pair 3 (Nat.pair (2 * x + 1) (2 * y + 1)),
                  Nat.pair 5 (Nat.pair (2 * x + 1) (2 * y + 1))]
      refine ⟨[(seq, Nat.pair 0 (Nat.pair 1 (Nat.pair x y)), [], [])], by simp, ?_, ?_⟩
      · simp only [cCheckTrace, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true]
        unfold cCheckStep
        simp only [List.getD_cons_zero, seq, Nat.unpair_pair, ↓reduceIte, Bool.and_eq_true,
          decide_eq_true_eq, List.all_cons, List.all_nil, Bool.and_true, cMSetEq_iff]
        refine ⟨⟨?_, ?_⟩, by omega, trivial⟩
        · simpa [encForm] using cIsWf_encForm (Semiformula.rel (L := ℒₛₑₜ) (ξ := ℕ) (n := 0) Language.Set.Rel.mem ![&x, &y])
        · simpa [encForm] using cIsWf_encForm (Semiformula.nrel (L := ℒₛₑₜ) (ξ := ℕ) (n := 0) Language.Set.Rel.mem ![&x, &y])
      · simp only [cGetSeq, List.length_singleton, Nat.sub_self, List.getD_cons_zero, seq,
          Multiset.map_add, Multiset.atom, Multiset.map_singleton, encForm, hx, hy, encTerm_fvar]
        rw [mset_cons_eq_add_singleton, add_comm]
        rfl
  | verum =>
    refine ⟨[([Nat.pair 0 0], Nat.pair 1 0, [], [])], by simp, ?_, ?_⟩
    · simp only [cCheckTrace, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true]
      unfold cCheckStep
      simp only [List.getD_cons_zero, Nat.unpair_pair, OfNat.ofNat_ne_zero, ↓reduceIte,
        Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, cMSetEq_iff]
      exact ⟨by simpa [encForm] using cIsWf_encForm (Semiformula.verum : Proposition ℒₛₑₜ), rfl⟩
    · simp only [cGetSeq, List.length_singleton, Nat.sub_self, List.getD_cons_zero,
        Multiset.map_singleton, encForm]
      rfl
  | @contraction Δ Γ d hsub ih =>
    obtain ⟨tr, hpos, hchk, hlast⟩ := ih
    obtain ⟨LΓ, hLΓ⟩ := Quotient.exists_rep Γ
    rw [Multiset.quot_mk_to_coe] at hLΓ; subst hLΓ
    let seq := LΓ.map encForm
    let st : TraceStep := (seq, Nat.pair 2 (tr.length - 1), [], [])
    refine ⟨tr ++ [st], by simp, cCheckTrace_snoc hchk ?_, ?_⟩
    · unfold cCheckStep
      have hget : (tr ++ [st]).getD tr.length ([], 0, [], []) = st := by
        simp [List.getD_eq_getElem?_getD]
      have hprev : cGetSeq (tr ++ [st]) (tr.length - 1) = cGetSeq tr (tr.length - 1) := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega : tr.length - 1 < tr.length)]
      rw [hget]
      simp only [st, Nat.unpair_pair, OfNat.ofNat_ne_zero, show (2 : ℕ) ≠ 1 by decide,
        ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        cMSetSubset_iff]
      rw [hprev]
      refine ⟨fun c hc => by obtain ⟨χ, _, rfl⟩ := List.mem_map.mp hc; exact cIsWf_encForm χ, by omega, ?_⟩
      rw [hlast]
      change Δ.map encForm ⊆ (LΓ.map encForm : Multiset ℕ)
      rw [← Multiset.map_coe]
      exact Multiset.map_subset_map hsub
    · simp [cGetSeq, st, seq, List.getD_eq_getElem?_getD]
  | @cut Γ φ Δ d₁ d₂ ih₁ ih₂ =>
    obtain ⟨tr₁, hpos₁, hchk₁, hlast₁⟩ := ih₁
    obtain ⟨tr₂, hpos₂, hchk₂, hlast₂⟩ := ih₂
    obtain ⟨LΓ, hLΓ⟩ := Quotient.exists_rep Γ
    rw [Multiset.quot_mk_to_coe] at hLΓ; subst hLΓ
    obtain ⟨LΔ, hLΔ⟩ := Quotient.exists_rep Δ
    rw [Multiset.quot_mk_to_coe] at hLΔ; subst hLΔ
    let tr12 := tr₁ ++ shiftTrace tr₁.length tr₂
    let i := tr₁.length - 1
    let j := tr₁.length + (tr₂.length - 1)
    let Γl := LΓ.map encForm
    let Δl := LΔ.map encForm
    let seq := Γl ++ Δl
    let st : TraceStep := (seq, Nat.pair 3 (Nat.pair i (Nat.pair j (encForm φ))), Γl, Δl)
    refine ⟨tr12 ++ [st], by simp, cCheckTrace_snoc (cCheckTrace_append_shift hchk₁ hchk₂) ?_, ?_⟩
    · unfold cCheckStep
      have hget : (tr12 ++ [st]).getD tr12.length ([], 0, [], []) = st := by
        simp [List.getD_eq_getElem?_getD]
      have hi : cGetSeq (tr12 ++ [st]) i = cGetSeq tr₁ i := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [tr12, shiftTrace, i]; omega),
            List.getElem?_append_left (by simp [i]; omega)]
      have hj : cGetSeq (tr12 ++ [st]) j = cGetSeq tr₂ (tr₂.length - 1) := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [tr12, shiftTrace, j]; omega),
            List.getElem?_append_right (Nat.le_add_right _ _)]
        simp [j, shiftTrace, show tr₂.length - 1 < tr₂.length by omega]
      rw [hget]
      simp only [st, Nat.unpair_pair, OfNat.ofNat_ne_zero, show (3 : ℕ) ≠ 1 by decide,
        show (3 : ℕ) ≠ 2 by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, cMSetEq_iff]
      rw [hi, hj]
      refine ⟨?_, ⟨⟨⟨⟨⟨by simp [tr12, shiftTrace, i]; omega, by simp [tr12, shiftTrace, j]; omega⟩,
        cIsWf_encForm φ⟩, ?_⟩, ?_⟩, rfl⟩⟩
      · intro c hc
        rcases List.mem_append.mp hc with h | h
        · obtain ⟨χ, _, rfl⟩ := List.mem_map.mp h; exact cIsWf_encForm χ
        · obtain ⟨χ, _, rfl⟩ := List.mem_map.mp h; exact cIsWf_encForm χ
      · rw [hlast₁, mset_cons_eq_add_singleton]; simp [Γl, Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]
      · rw [hlast₂, cNeg_encForm, mset_cons_eq_add_singleton]; simp [Δl, Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]
    · simp [cGetSeq, st, seq, Γl, Δl, List.getD_eq_getElem?_getD, Multiset.map_add, Multiset.map_coe]
  | @or Γ φ ψ d ih =>
    obtain ⟨tr, hpos, hchk, hlast⟩ := ih
    obtain ⟨LΓ, hLΓ⟩ := Quotient.exists_rep Γ
    rw [Multiset.quot_mk_to_coe] at hLΓ; subst hLΓ
    let Γl := LΓ.map encForm
    let seq := Nat.pair 7 (Nat.pair (encForm φ) (encForm ψ)) :: Γl
    let st : TraceStep := (seq, Nat.pair 4 (Nat.pair (tr.length - 1) (Nat.pair (encForm φ) (encForm ψ))), Γl, [])
    refine ⟨tr ++ [st], by simp, cCheckTrace_snoc hchk ?_, ?_⟩
    · unfold cCheckStep
      have hget : (tr ++ [st]).getD tr.length ([], 0, [], []) = st := by simp [List.getD_eq_getElem?_getD]
      have hi : cGetSeq (tr ++ [st]) (tr.length - 1) = cGetSeq tr (tr.length - 1) := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega : tr.length - 1 < tr.length)]
      rw [hget]
      simp only [st, Nat.unpair_pair, OfNat.ofNat_ne_zero, show (4 : ℕ) ≠ 1 by decide,
        show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ↓reduceIte,
        Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, cMSetEq_iff]
      rw [hi]
      refine ⟨?_, ⟨⟨⟨⟨by omega, cIsWf_encForm φ⟩, cIsWf_encForm ψ⟩, ?_⟩, rfl⟩⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | h
        · exact cIsWf_encForm (φ ⋎ ψ)
        · obtain ⟨χ, _, rfl⟩ := List.mem_map.mp h; exact cIsWf_encForm χ
      · rw [hlast, mset_cons_eq_add_singleton, mset_cons_eq_add_singleton]
        simp only [Γl, Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]
        ac_rfl
    · simp [cGetSeq, st, seq, Γl, List.getD_eq_getElem?_getD, mset_cons_eq_add_singleton,
        Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]; rfl
  | @and Γ φ ψ d₁ d₂ ih₁ ih₂ =>
    obtain ⟨tr₁, hpos₁, hchk₁, hlast₁⟩ := ih₁
    obtain ⟨tr₂, hpos₂, hchk₂, hlast₂⟩ := ih₂
    obtain ⟨LΓ, hLΓ⟩ := Quotient.exists_rep Γ
    rw [Multiset.quot_mk_to_coe] at hLΓ; subst hLΓ
    let tr12 := tr₁ ++ shiftTrace tr₁.length tr₂
    let i := tr₁.length - 1
    let j := tr₁.length + (tr₂.length - 1)
    let Γl := LΓ.map encForm
    let seq := Nat.pair 6 (Nat.pair (encForm φ) (encForm ψ)) :: Γl
    let st : TraceStep := (seq, Nat.pair 5 (Nat.pair i (Nat.pair j (Nat.pair (encForm φ) (encForm ψ)))), Γl, [])
    refine ⟨tr12 ++ [st], by simp, cCheckTrace_snoc (cCheckTrace_append_shift hchk₁ hchk₂) ?_, ?_⟩
    · unfold cCheckStep
      have hget : (tr12 ++ [st]).getD tr12.length ([], 0, [], []) = st := by simp [List.getD_eq_getElem?_getD]
      have hi : cGetSeq (tr12 ++ [st]) i = cGetSeq tr₁ i := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [tr12, shiftTrace, i]; omega),
            List.getElem?_append_left (by simp [i]; omega)]
      have hj : cGetSeq (tr12 ++ [st]) j = cGetSeq tr₂ (tr₂.length - 1) := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simp [tr12, shiftTrace, j]; omega),
            List.getElem?_append_right (Nat.le_add_right _ _)]
        simp [j, shiftTrace, show tr₂.length - 1 < tr₂.length by omega]
      rw [hget]
      simp only [st, Nat.unpair_pair, OfNat.ofNat_ne_zero, show (5 : ℕ) ≠ 1 by decide,
        show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
        ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, cMSetEq_iff]
      rw [hi, hj]
      refine ⟨?_, ⟨⟨⟨⟨⟨⟨by simp [tr12, shiftTrace, i]; omega, by simp [tr12, shiftTrace, j]; omega⟩,
        cIsWf_encForm φ⟩, cIsWf_encForm ψ⟩, ?_⟩, ?_⟩, rfl⟩⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | h
        · exact cIsWf_encForm (φ ⋏ ψ)
        · obtain ⟨χ, _, rfl⟩ := List.mem_map.mp h; exact cIsWf_encForm χ
      · rw [hlast₁, mset_cons_eq_add_singleton]; simp [Γl, Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]
      · rw [hlast₂, mset_cons_eq_add_singleton]; simp [Γl, Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]
    · simp [cGetSeq, st, seq, Γl, List.getD_eq_getElem?_getD, mset_cons_eq_add_singleton,
        Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]; rfl
  | @all Γ φ d ih =>
    obtain ⟨tr, hpos, hchk, hlast⟩ := ih
    obtain ⟨LΓ, hLΓ⟩ := Quotient.exists_rep Γ
    rw [Multiset.quot_mk_to_coe] at hLΓ; subst hLΓ
    let Γl := LΓ.map encForm
    let seq := Nat.pair 8 (encForm φ) :: Γl
    let st : TraceStep := (seq, Nat.pair 6 (Nat.pair (tr.length - 1) (encForm φ)), Γl, [])
    refine ⟨tr ++ [st], by simp, cCheckTrace_snoc hchk ?_, ?_⟩
    · unfold cCheckStep
      have hget : (tr ++ [st]).getD tr.length ([], 0, [], []) = st := by simp [List.getD_eq_getElem?_getD]
      have hi : cGetSeq (tr ++ [st]) (tr.length - 1) = cGetSeq tr (tr.length - 1) := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega : tr.length - 1 < tr.length)]
      rw [hget]
      simp only [st, Nat.unpair_pair, OfNat.ofNat_ne_zero, show (6 : ℕ) ≠ 1 by decide,
        show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide,
        show (6 : ℕ) ≠ 5 by decide, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, cMSetEq_iff]
      rw [hi]
      refine ⟨?_, ⟨⟨⟨by omega, cIsWf_encForm φ⟩, ?_⟩, rfl⟩⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | h
        · exact cIsWf_encForm (∀¹ φ)
        · obtain ⟨χ, _, rfl⟩ := List.mem_map.mp h; exact cIsWf_encForm χ
      · rw [hlast, cFree_encForm, mset_cons_eq_add_singleton]
        have hsh : ((LΓ : Multiset (Proposition ℒₛₑₜ))⁺).map encForm = ((Γl.map cShift) : Multiset ℕ) := by
          rw [Rewriting.shifts, Multiset.map_map, Multiset.map_coe, List.map_map]
          apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
          apply List.map_congr_left
          intro χ _
          exact (cShift_encForm χ).symm
        simp [hsh, Multiset.atom, Multiset.map_add, Multiset.map_singleton]
    · simp [cGetSeq, st, seq, Γl, List.getD_eq_getElem?_getD, mset_cons_eq_add_singleton,
        Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]; rfl
  | @exs Γ φ t d ih =>
    obtain ⟨tr, hpos, hchk, hlast⟩ := ih
    obtain ⟨x, rfl⟩ := term_zero_eq_fvar t
    obtain ⟨LΓ, hLΓ⟩ := Quotient.exists_rep Γ
    rw [Multiset.quot_mk_to_coe] at hLΓ; subst hLΓ
    let Γl := LΓ.map encForm
    let seq := Nat.pair 9 (encForm φ) :: Γl
    let st : TraceStep := (seq, Nat.pair 7 (Nat.pair (tr.length - 1) (Nat.pair x (encForm φ))), Γl, [])
    refine ⟨tr ++ [st], by simp, cCheckTrace_snoc hchk ?_, ?_⟩
    · unfold cCheckStep
      have hget : (tr ++ [st]).getD tr.length ([], 0, [], []) = st := by simp [List.getD_eq_getElem?_getD]
      have hi : cGetSeq (tr ++ [st]) (tr.length - 1) = cGetSeq tr (tr.length - 1) := by
        unfold cGetSeq
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega : tr.length - 1 < tr.length)]
      rw [hget]
      simp only [st, Nat.unpair_pair, OfNat.ofNat_ne_zero, show (7 : ℕ) ≠ 1 by decide,
        show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 4 by decide,
        show (7 : ℕ) ≠ 5 by decide, show (7 : ℕ) ≠ 6 by decide, ↓reduceIte,
        Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, cMSetEq_iff]
      rw [hi]
      refine ⟨?_, ⟨⟨⟨by omega, cIsWf_encForm φ⟩, ?_⟩, rfl⟩⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | h
        · exact cIsWf_encForm (∃¹ φ)
        · obtain ⟨χ, _, rfl⟩ := List.mem_map.mp h; exact cIsWf_encForm χ
      · rw [hlast, cSubst0_encForm, mset_cons_eq_add_singleton]; simp [Γl, Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]
    · simp [cGetSeq, st, seq, Γl, List.getD_eq_getElem?_getD, mset_cons_eq_add_singleton,
        Multiset.atom, Multiset.map_add, Multiset.map_coe, Multiset.map_singleton]; rfl

/- Main Part 2E theorem: `REPred` of ZFC-provable sentence codes! -/

def cValidZFCProof (s : ℕ) (p : List (ℕ × ℕ) × List TraceStep) : Bool :=
  let axs := p.1
  let tr := p.2
  decide (0 < tr.length) &&
  axs.all cValidZFCWitness &&
  cCheckTrace tr &&
  cMSetEq (cGetSeq tr (tr.length - 1)) (s :: axs.map (fun w => cNeg (cZFCAxiomOf w)))

lemma primrec_cValidZFCProof : Primrec₂ cValidZFCProof := by
  unfold cValidZFCProof
  have haxs : Primrec (fun q : ℕ × (List (ℕ × ℕ) × List TraceStep) => q.2.1) := Primrec.fst.comp Primrec.snd
  have htr : Primrec (fun q : ℕ × (List (ℕ × ℕ) × List TraceStep) => q.2.2) := Primrec.snd.comp Primrec.snd
  refine Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp
        (primrec_decide (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp htr)))
        (primrec_list_all haxs (primrec_cValidZFCWitness.comp Primrec.snd).to₂))
      (primrec_cCheckTrace.comp htr))
    (primrec_cMSetEq.comp
      (primrec_cGetSeq.comp htr (Primrec.nat_sub.comp (Primrec.list_length.comp htr) (Primrec.const 1)))
      (Primrec.list_cons.comp Primrec.fst
        (Primrec.list_map haxs (primrec_cNeg.comp (primrec_cZFCAxiomOf.comp Primrec.snd)).to₂)))

private lemma rewAux_neg {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    Semiformula.rewAux ω (∼φ) = ∼(Semiformula.rewAux ω φ) := by
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel r v => rfl
  | nrel r v => rfl
  | and φ ψ ih₁ ih₂ => exact congrArg₂ (· ⋎ ·) (ih₁ ω) (ih₂ ω)
  | or φ ψ ih₁ ih₂ => exact congrArg₂ (· ⋏ ·) (ih₁ ω) (ih₂ ω)
  | all φ ih => exact congrArg (∃¹ ·) (ih ω.q)
  | exs φ ih => exact congrArg (∀¹ ·) (ih ω.q)

lemma provable_iff_exists_cValidZFCProof (σ : Sentence ℒₛₑₜ) :
    FFL.Entailment.Provable 𝗭𝗙𝗖 σ ↔ ∃ p, cValidZFCProof (encSent σ) p = true := by
  constructor
  · rintro ⟨⟨axs, haxs, d⟩⟩
    obtain ⟨Laxs, hLaxs⟩ := Quotient.exists_rep axs
    rw [Multiset.quot_mk_to_coe] at hLaxs; subst hLaxs
    have hL : ∀ ψ ∈ Laxs, ∃ w : ℕ × ℕ, cValidZFCWitness w = true ∧ cZFCAxiomOf w = encSent ψ :=
      fun ψ hψ => exists_cValidZFCWitness_of_mem (haxs ψ (Multiset.mem_coe.mpr hψ))
    choose f hf1 hf2 using fun (ψ : {x // x ∈ Laxs}) => hL ψ.1 ψ.2
    let ws : List (ℕ × ℕ) := Laxs.attach.map f
    obtain ⟨tr, hpos, hchk, hlast⟩ := exists_trace_of_derivation d
    refine ⟨(ws, tr), ?_⟩
    simp only [cValidZFCProof, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, cMSetEq_iff]
    refine ⟨⟨⟨hpos, ?_⟩, hchk⟩, ?_⟩
    · intro w hw
      obtain ⟨ψ, _, rfl⟩ := List.mem_map.mp hw
      exact hf1 ψ
    · rw [hlast]
      have hws : ws.map (fun w => cNeg (cZFCAxiomOf w)) = Laxs.map (fun ψ => encForm (∼(Rewriting.emb ψ : Proposition ℒₛₑₜ))) := by
        apply List.ext_getElem
        · simp [ws]
        · intro i h1 h2
          simp only [ws, List.getElem_map, List.getElem_attach, hf2, encSent, cNeg_encForm]
      simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map, Function.comp_def]
      rw [mset_cons_eq_add_singleton, hws]
      have hneg_map : ((∼(Laxs : Multiset (Sentence ℒₛₑₜ))).map (fun x => encForm (Rewriting.emb x : Proposition ℒₛₑₜ))) =
          ((Laxs.map (fun ψ => encForm (∼(Rewriting.emb ψ : Proposition ℒₛₑₜ)))) : Multiset ℕ) := by
        change ((Laxs : Multiset (Sentence ℒₛₑₜ)).map (∼·)).map _ = _
        rw [Multiset.map_map, Multiset.map_coe]
        apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
        apply List.map_congr_left
        intro ψ _
        exact congrArg encForm (rewAux_neg Rew.emb ψ)
      rw [hneg_map, add_comm]
      rfl
  · rintro ⟨⟨ws, tr⟩, hp⟩
    simp only [cValidZFCProof, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, cMSetEq_iff] at hp
    obtain ⟨⟨⟨hpos, hws⟩, hchk⟩, hlast⟩ := hp
    have hψ : ∀ w ∈ ws, ∃ ψ : Sentence ℒₛₑₜ, ψ ∈ 𝗭𝗙𝗖 ∧ encSent ψ = cZFCAxiomOf w :=
      fun w hw => exists_zfc_of_cValidZFCWitness (hws w hw)
    choose g hg1 hg2 using fun (w : {x // x ∈ ws}) => hψ w.1 w.2
    let Laxs : List (Sentence ℒₛₑₜ) := ws.attach.map g
    obtain ⟨Γ, hΓ, ⟨d⟩⟩ := derivation_of_cCheckTrace hchk (tr.length - 1) (by omega)
    have hΓeq : Γ = ((⦃σ⦄ + ∼(Laxs : Multiset (Sentence ℒₛₑₜ))).map Rewriting.emb) := by
      apply multiset_eq_of_map_encForm_eq
      rw [hΓ, hlast]
      have hmap : ws.map (fun w => cNeg (cZFCAxiomOf w)) =
          Laxs.map (fun ψ => encForm (∼(Rewriting.emb ψ : Proposition ℒₛₑₜ))) := by
        apply List.ext_getElem
        · simp [Laxs]
        · intro i h1 h2
          have hi : i < ws.length := by simpa using h1
          simp only [Laxs, List.getElem_map, List.getElem_attach]
          rw [← hg2 ⟨ws[i]'hi, List.getElem_mem hi⟩, encSent, cNeg_encForm]
      rw [mset_cons_eq_add_singleton, hmap]
      simp only [Multiset.map_add, Multiset.map_map, Function.comp_def]
      have hneg_map : ((∼(Laxs : Multiset (Sentence ℒₛₑₜ))).map (fun x => encForm (Rewriting.emb x : Proposition ℒₛₑₜ))) =
          ((Laxs.map (fun ψ => encForm (∼(Rewriting.emb ψ : Proposition ℒₛₑₜ)))) : Multiset ℕ) := by
        change ((Laxs : Multiset (Sentence ℒₛₑₜ)).map (∼·)).map _ = _
        rw [Multiset.map_map, Multiset.map_coe]
        apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
        apply List.map_congr_left
        intro ψ _
        exact congrArg encForm (rewAux_neg Rew.emb ψ)
      rw [hneg_map, add_comm]
      rfl
    rw [hΓeq] at d
    exact ⟨⟨(Laxs : Multiset (Sentence ℒₛₑₜ)), fun ψ hψ => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hψ)
      exact hg1 w, d⟩⟩

lemma rePred_provable_of_primrec {α : Type*} [Primcodable α]
    {f : α → Sentence ℒₛₑₜ} {c : α → ℕ}
    (hc : Primrec c) (hcf : ∀ a, c a = encSent (f a)) :
    REPred (fun a => FFL.Entailment.Provable 𝗭𝗙𝗖 (f a)) := by
  let P : α × ℕ → Bool := fun q =>
    Option.casesOn (Encodable.decode (α := List (ℕ × ℕ) × List TraceStep) q.2) false
      (fun p => cValidZFCProof (c q.1) p)
  have hP : Computable P := by
    have hdec : Computable (fun q : α × ℕ => Encodable.decode (α := List (ℕ × ℕ) × List TraceStep) q.2) :=
      Computable.decode.comp Computable.snd
    have hstep : Computable₂ (fun (q : α × ℕ) (p : List (ℕ × ℕ) × List TraceStep) => cValidZFCProof (c q.1) p) :=
      (primrec_cValidZFCProof.comp (hc.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp
    exact Computable.option_casesOn hdec (Computable.const false) hstep
  have hP2 : Computable₂ (fun a n => P (a, n)) := hP
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (P (a, n)))) :=
    Partrec.rfind hP2.partrec
  have hre : REPred (fun a => ∃ n : ℕ, P (a, n) = true) := by
    refine hr.dom_re.of_eq fun a => ?_
    have hdom : (Nat.rfind (fun n => Part.some (P (a, n)))).Dom ↔
        ∃ n, true ∈ Part.some (P (a, n)) ∧ ∀ m < n, (Part.some (P (a, m))).Dom :=
      Nat.rfind_dom
    simpa using hdom
  refine hre.of_eq fun a => ?_
  rw [provable_iff_exists_cValidZFCProof, ← hcf a]
  constructor
  · rintro ⟨n, hn⟩
    simp [P] at hn
    exact ⟨_, hn⟩
  · rintro ⟨p, hp⟩
    refine ⟨Encodable.encode p, ?_⟩
    dsimp only [P]
    rw [Encodable.encodek]
    exact hp

end C14H4Part2

namespace C14H4Part2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver

/- ## Section 2G: `Primrec` encoder for `∼Constant14.halts (prependBits bits B₀)` -/

def cConjList : List ℕ → ℕ
  | [] => Nat.pair 0 0
  | x :: xs => Nat.pair 6 (Nat.pair x (cConjList xs))

lemma primrec_cConjList : Primrec cConjList := by
  have hstep : Primrec (fun p : List ℕ × ℕ × ℕ => Nat.pair 6 (Nat.pair p.2.1 p.2.2)) :=
    primrec_natPair.comp (Primrec.const 6)
      (primrec_natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id (Primrec.const (Nat.pair 0 0)) hstep.to₂).of_eq fun l => by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      dsimp only [id_eq] at ih ⊢
      simp only [cConjList, List.foldr_cons, ih]

lemma cConjList_ofFn : ∀ {k : ℕ} (v : Fin k → Semiproposition ℒₛₑₜ m),
    cConjList (List.ofFn fun i => encForm (v i)) = encForm (Matrix.conj v)
  | 0, _ => rfl
  | k + 1, v => by
    simp only [List.ofFn_succ, cConjList, Matrix.conj, encForm]
    congr 2
    exact cConjList_ofFn (Matrix.vecTail v)

def cNestFormulae (m : ℕ) (cφ : ℕ) (cΨs : List ℕ) : ℕ :=
  let n := cΨs.length
  let tail := (List.range m).map fun j => 2 * (j + n)
  let args := (List.range n).map fun i => cSubstList (2 * i :: tail) (cΨs.getD i 0)
  let lhs := cConjList args
  let rhs := cSubstList ((List.range n).map fun i => 2 * i) cφ
  cAllItr n (cImp lhs rhs)

def cNestFormulaeFunc (m : ℕ) (cφ : ℕ) (cΨs : List ℕ) : ℕ :=
  let n := cΨs.length
  let tail := (List.range m).map fun j => 2 * (j + 1 + n)
  let args := (List.range n).map fun i => cSubstList (2 * i :: tail) (cΨs.getD i 0)
  let lhs := cConjList args
  let rhs := cSubstList (2 * n :: (List.range n).map fun i => 2 * i) cφ
  cAllItr n (cImp lhs rhs)

lemma primrec_cNestFormulae : Primrec₂ (fun (mc : ℕ) (cΨs : List ℕ) =>
    cNestFormulae mc.unpair.1 mc.unpair.2 cΨs) := by
  let P := ℕ × List ℕ
  have hm : Primrec (fun p : P => p.1.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hcφ : Primrec (fun p : P => p.1.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hcΨ : Primrec (fun p : P => p.2) := Primrec.snd
  have hn : Primrec (fun p : P => p.2.length) := Primrec.list_length.comp hcΨ
  have htail : Primrec (fun p : P => (List.range p.1.unpair.1).map fun j => 2 * (j + p.2.length)) :=
    Primrec.list_map (primrec_list_range.comp hm)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp Primrec.snd (hn.comp Primrec.fst))).to₂
  have hargs : Primrec (fun p : P => (List.range p.2.length).map fun i =>
      cSubstList (2 * i :: (List.range p.1.unpair.1).map fun j => 2 * (j + p.2.length)) (p.2.getD i 0)) :=
    Primrec.list_map (primrec_list_range.comp hn)
      (primrec_cSubstList.comp
        (Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (htail.comp Primrec.fst))
        (primrec_getD_nat.comp (hcΨ.comp Primrec.fst) Primrec.snd)).to₂
  have hlhs : Primrec (fun p : P => cConjList ((List.range p.2.length).map fun i =>
      cSubstList (2 * i :: (List.range p.1.unpair.1).map fun j => 2 * (j + p.2.length)) (p.2.getD i 0))) :=
    primrec_cConjList.comp hargs
  have hrhs : Primrec (fun p : P => cSubstList ((List.range p.2.length).map fun i => 2 * i) p.1.unpair.2) :=
    primrec_cSubstList.comp
      (Primrec.list_map (primrec_list_range.comp hn)
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂)
      hcφ
  exact primrec_cAllItr.comp hn (primrec_cImp.comp hlhs hrhs)

lemma primrec_cNestFormulaeFunc : Primrec₂ (fun (mc : ℕ) (cΨs : List ℕ) =>
    cNestFormulaeFunc mc.unpair.1 mc.unpair.2 cΨs) := by
  let P := ℕ × List ℕ
  have hm : Primrec (fun p : P => p.1.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hcφ : Primrec (fun p : P => p.1.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hcΨ : Primrec (fun p : P => p.2) := Primrec.snd
  have hn : Primrec (fun p : P => p.2.length) := Primrec.list_length.comp hcΨ
  have htail : Primrec (fun p : P => (List.range p.1.unpair.1).map fun j => 2 * (j + 1 + p.2.length)) :=
    Primrec.list_map (primrec_list_range.comp hm)
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.succ.comp Primrec.snd) (hn.comp Primrec.fst))).to₂
  have hargs : Primrec (fun p : P => (List.range p.2.length).map fun i =>
      cSubstList (2 * i :: (List.range p.1.unpair.1).map fun j => 2 * (j + 1 + p.2.length)) (p.2.getD i 0)) :=
    Primrec.list_map (primrec_list_range.comp hn)
      (primrec_cSubstList.comp
        (Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (htail.comp Primrec.fst))
        (primrec_getD_nat.comp (hcΨ.comp Primrec.fst) Primrec.snd)).to₂
  have hlhs : Primrec (fun p : P => cConjList ((List.range p.2.length).map fun i =>
      cSubstList (2 * i :: (List.range p.1.unpair.1).map fun j => 2 * (j + 1 + p.2.length)) (p.2.getD i 0))) :=
    primrec_cConjList.comp hargs
  have hrhs : Primrec (fun p : P =>
      cSubstList (2 * p.2.length :: (List.range p.2.length).map fun i => 2 * i) p.1.unpair.2) :=
    primrec_cSubstList.comp
      (Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) hn)
        (Primrec.list_map (primrec_list_range.comp hn)
          (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂))
      hcφ
  exact primrec_cAllItr.comp hn (primrec_cImp.comp hlhs hrhs)

private lemma primrec_cNestFormulaeFunc_const {α : Type} [Primcodable α]
    (m cφ : ℕ) {f : α → List ℕ} (hf : Primrec f) :
    Primrec (fun a => cNestFormulaeFunc m cφ (f a)) :=
  (primrec_cNestFormulaeFunc.comp (Primrec.const (Nat.pair m cφ)) hf).of_eq fun a => by
    simp only [Nat.unpair_pair]

private lemma primrec_cNestFormulaeFunc_var {α : Type} [Primcodable α]
    (m : ℕ) {g : α → ℕ} {f : α → List ℕ} (hg : Primrec g) (hf : Primrec f) :
    Primrec (fun a => cNestFormulaeFunc m (g a) (f a)) :=
  (primrec_cNestFormulaeFunc.comp (primrec_natPair.comp (Primrec.const m) hg) hf).of_eq fun a => by
    simp only [Nat.unpair_pair]

private lemma primrec_cNestFormulae_var {α : Type} [Primcodable α]
    (m : ℕ) {g : α → ℕ} {f : α → List ℕ} (hg : Primrec g) (hf : Primrec f) :
    Primrec (fun a => cNestFormulae m (g a) (f a)) :=
  (primrec_cNestFormulae.comp (primrec_natPair.comp (Primrec.const m) hg) hf).of_eq fun a => by
    simp only [Nat.unpair_pair]

private lemma rew_emb_q_eq {n : ℕ} :
    (Rew.emb : Rew ℒₛₑₜ Empty n ℕ n).q = (Rew.emb : Rew ℒₛₑₜ Empty (n + 1) ℕ (n + 1)) := by
  apply DFunLike.coe_injective; funext t
  cases t with
  | bvar i => cases i using Fin.cases <;> rfl
  | fvar e => exact Empty.elim e
  | func f _ => exact Empty.elim f

private lemma rewAux_neg_g {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    Semiformula.rewAux ω (∼φ) = ∼(Semiformula.rewAux ω φ) := by
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel r v => rfl
  | nrel r v => rfl
  | and φ ψ ih₁ ih₂ => exact congrArg₂ (· ⋎ ·) (ih₁ ω) (ih₂ ω)
  | or φ ψ ih₁ ih₂ => exact congrArg₂ (· ⋏ ·) (ih₁ ω) (ih₂ ω)
  | all φ ih => exact congrArg (∃¹ ·) (ih ω.q)
  | exs φ ih => exact congrArg (∀¹ ·) (ih ω.q)

private lemma emb_rewAux {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ Empty n₁ Empty n₂)
    (ω' : Rew ℒₛₑₜ ℕ n₁ ℕ n₂)
    (hb : ∀ i : Fin n₁, Rew.emb (ω #i) = ω' #i) :
    ∀ (φ : Semisentence ℒₛₑₜ n₁),
      Semiformula.rewAux Rew.emb (Semiformula.rewAux ω φ) =
        Semiformula.rewAux ω' (Semiformula.rewAux Rew.emb φ) := by
  intro φ
  induction φ generalizing n₂ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
    change Semiformula.rel r _ = Semiformula.rel r _
    congr 1; funext i
    cases hv : v i with
    | bvar j => simp only [Function.comp_apply, hv]; exact hb j
    | fvar e => exact Empty.elim e
    | func f _ => exact Empty.elim f
  | nrel r v =>
    change Semiformula.nrel r _ = Semiformula.nrel r _
    congr 1; funext i
    cases hv : v i with
    | bvar j => simp only [Function.comp_apply, hv]; exact hb j
    | fvar e => exact Empty.elim e
    | func f _ => exact Empty.elim f
  | and φ ψ ih₁ ih₂ =>
    change Semiformula.and _ _ = Semiformula.and _ _
    rw [ih₁ ω ω' hb, ih₂ ω ω' hb]
  | or φ ψ ih₁ ih₂ =>
    change Semiformula.or _ _ = Semiformula.or _ _
    rw [ih₁ ω ω' hb, ih₂ ω ω' hb]
  | all φ ih =>
    change Semiformula.all (Semiformula.rewAux Rew.emb.q _) = Semiformula.all (Semiformula.rewAux ω'.q (Semiformula.rewAux Rew.emb.q _))
    simp only [rew_emb_q_eq]
    congr 1
    refine ih ω.q ω'.q fun i => ?_
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      change Rew.emb (Rew.bShift (ω #j)) = Rew.bShift (ω' #j)
      rw [← hb j]
      cases ω #j with
      | bvar _ => rfl | fvar e => exact Empty.elim e | func f _ => exact Empty.elim f
  | exs φ ih =>
    change Semiformula.exs (Semiformula.rewAux Rew.emb.q _) = Semiformula.exs (Semiformula.rewAux ω'.q (Semiformula.rewAux Rew.emb.q _))
    simp only [rew_emb_q_eq]
    congr 1
    refine ih ω.q ω'.q fun i => ?_
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      change Rew.emb (Rew.bShift (ω #j)) = Rew.bShift (ω' #j)
      rw [← hb j]
      cases ω #j with
      | bvar _ => rfl | fvar e => exact Empty.elim e | func f _ => exact Empty.elim f

private lemma emb_imp {n : ℕ} (φ ψ : Semisentence ℒₛₑₜ n) :
    (Rewriting.emb (φ 🡒 ψ) : Semiproposition ℒₛₑₜ n) = Rewriting.emb φ 🡒 Rewriting.emb ψ := by
  change Semiformula.or (Semiformula.rewAux Rew.emb (∼φ)) (Semiformula.rewAux Rew.emb ψ) =
    Semiformula.or (∼Semiformula.rewAux Rew.emb φ) (Semiformula.rewAux Rew.emb ψ)
  rw [rewAux_neg_g]

private lemma emb_iff {n : ℕ} (φ ψ : Semisentence ℒₛₑₜ n) :
    (Rewriting.emb (φ 🡘 ψ) : Semiproposition ℒₛₑₜ n) = Rewriting.emb φ 🡘 Rewriting.emb ψ := by
  change Semiformula.and (Rewriting.emb (φ 🡒 ψ)) (Rewriting.emb (ψ 🡒 φ)) =
    Semiformula.and (Rewriting.emb φ 🡒 Rewriting.emb ψ) (Rewriting.emb ψ 🡒 Rewriting.emb φ)
  rw [emb_imp, emb_imp]

private lemma encSent_and {n : ℕ} (φ ψ : Semisentence ℒₛₑₜ n) :
    encSent (φ ⋏ ψ) = Nat.pair 6 (Nat.pair (encSent φ) (encSent ψ)) := rfl

private lemma encSent_all {n : ℕ} (φ : Semisentence ℒₛₑₜ (n + 1)) :
    encSent (∀¹ φ) = Nat.pair 8 (encSent φ) := by
  change Nat.pair 8 (encForm (Semiformula.rewAux Rew.emb.q φ)) = Nat.pair 8 (encForm (Semiformula.rewAux Rew.emb φ))
  rw [rew_emb_q_eq]

private lemma encSent_exs {n : ℕ} (φ : Semisentence ℒₛₑₜ (n + 1)) :
    encSent (∃¹ φ) = Nat.pair 9 (encSent φ) := by
  change Nat.pair 9 (encForm (Semiformula.rewAux Rew.emb.q φ)) = Nat.pair 9 (encForm (Semiformula.rewAux Rew.emb φ))
  rw [rew_emb_q_eq]

private lemma encSent_imp {n : ℕ} (φ ψ : Semisentence ℒₛₑₜ n) :
    encSent (φ 🡒 ψ) = cImp (encSent φ) (encSent ψ) := by
  simp only [encSent, emb_imp, cImp_encForm]

private lemma encSent_iff {n : ℕ} (φ ψ : Semisentence ℒₛₑₜ n) :
    encSent (φ 🡘 ψ) = cIff (encSent φ) (encSent ψ) := by
  simp only [encSent, emb_iff, cIff_encForm]

private lemma encSent_bexMem {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) (φ : Semisentence ℒₛₑₜ (n + 1)) :
    encSent (Semiformula.bexsMem t φ) =
      Nat.pair 9 (Nat.pair 6 (Nat.pair (encSent (Semiformula.rel Language.Set.Rel.mem ![#0, Rew.bShift t])) (encSent φ))) := by
  rw [Semiformula.bexsMem]
  exact encSent_exs _

private lemma emb_allItr : ∀ {n : ℕ} (k : ℕ) (φ : Semisentence ℒₛₑₜ (n + k)),
    (Rewriting.emb (∀¹^[k] φ) : Semiproposition ℒₛₑₜ n) = ∀¹^[k] (Rewriting.emb φ : Semiproposition ℒₛₑₜ (n + k))
  | _, 0, _ => rfl
  | _, k + 1, φ => by
    change (Rewriting.emb (∀¹^[k] (∀¹ φ)) : Semiproposition ℒₛₑₜ _) = ∀¹^[k] (∀¹ (Rewriting.emb φ))
    rw [emb_allItr k (∀¹ φ)]
    congr 1
    change Semiformula.all (Semiformula.rewAux Rew.emb.q φ) = Semiformula.all (Semiformula.rewAux Rew.emb φ)
    rw [rew_emb_q_eq]

private lemma emb_conj : ∀ {k m : ℕ} (v : Fin k → Semisentence ℒₛₑₜ m),
    (Rewriting.emb (Matrix.conj v) : Semiproposition ℒₛₑₜ m) =
      Matrix.conj (fun i => (Rewriting.emb (v i) : Semiproposition ℒₛₑₜ m))
  | 0, _, _ => rfl
  | _ + 1, _, v => by
    change Semiformula.and (Rewriting.emb (v 0)) (Rewriting.emb (Matrix.conj (Matrix.vecTail v))) =
      Semiformula.and (Rewriting.emb (v 0)) (Matrix.conj (fun i => (Rewriting.emb (Matrix.vecTail v i) : Semiproposition ℒₛₑₜ _)))
    rw [emb_conj (Matrix.vecTail v)]

private lemma list_ofFn_eq_map_range {α : Type*} {n : ℕ} (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

lemma cNestFormulae_encSent {n m : ℕ} (φ : Semisentence ℒₛₑₜ n)
    (Ψ : Fin n → Semisentence ℒₛₑₜ (m + 1)) :
    cNestFormulae m (encSent φ) (List.ofFn fun i => encSent (Ψ i)) =
      encSent (Semiformula.nestFormulae φ Ψ) := by
  unfold cNestFormulae Semiformula.nestFormulae
  simp only [List.length_ofFn]
  have h1 : (List.range n).map (fun i =>
      cSubstList (2 * i :: (List.range m).map fun j => 2 * (j + n))
        ((List.ofFn fun k => encSent (Ψ k)).getD i 0)) =
      List.ofFn (fun i : Fin n => encForm (Rewriting.emb
        (Rewriting.subst (Ψ i) (#(i.addCast m) :> fun j : Fin m => #(j.addNat n))) :
          Semiproposition ℒₛₑₜ (m + n))) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
        List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
      let v : Fin (m + 1) → Semiterm ℒₛₑₜ ℕ (m + n) :=
        #((⟨i, hi⟩ : Fin n).addCast m) :> fun j : Fin m => #(j.addNat n)
      have hv : List.ofFn (fun k : Fin (m + 1) => encTerm (v k)) =
          2 * i :: (List.range m).map (fun j => 2 * (j + n)) := by
        rw [List.ofFn_succ]
        exact congrArg₂ List.cons rfl (list_ofFn_eq_map_range (fun j => 2 * (j + n)))
      rw [← hv, encSent, cSubstList_encForm]
      congr 1
      symm
      exact emb_rewAux (Rew.subst (#((⟨i, hi⟩ : Fin n).addCast m) :> fun j : Fin m => #(j.addNat n)))
        (Rew.subst v) (fun k => by cases k using Fin.cases <;> rfl) (Ψ ⟨i, hi⟩)
  have h2 : cSubstList ((List.range n).map fun i => 2 * i) (encSent φ) =
      encForm (Rewriting.emb (Rewriting.subst φ fun i : Fin n => #(i.addCast m)) :
        Semiproposition ℒₛₑₜ (m + n)) := by
    let v : Fin n → Semiterm ℒₛₑₜ ℕ (m + n) := fun i => #(i.addCast m)
    have hv : List.ofFn (fun i : Fin n => encTerm (v i)) = (List.range n).map (fun i => 2 * i) :=
      list_ofFn_eq_map_range (fun i => 2 * i)
    rw [← hv, encSent, cSubstList_encForm]
    congr 1
    symm
    exact emb_rewAux (Rew.subst fun i : Fin n => #(i.addCast m))
      (Rew.subst v) (fun _ => rfl) φ
  rw [h1, cConjList_ofFn, ← emb_conj, h2, cImp_encForm, ← emb_imp, cAllItr_encForm, ← emb_allItr]
  rfl

lemma cNestFormulaeFunc_encSent {n m : ℕ} (φ : Semisentence ℒₛₑₜ (n + 1))
    (Ψ : Fin n → Semisentence ℒₛₑₜ (m + 1)) :
    cNestFormulaeFunc m (encSent φ) (List.ofFn fun i => encSent (Ψ i)) =
      encSent (Semiformula.nestFormulaeFunc φ Ψ) := by
  unfold cNestFormulaeFunc Semiformula.nestFormulaeFunc
  simp only [List.length_ofFn]
  have h1 : (List.range n).map (fun i =>
      cSubstList (2 * i :: (List.range m).map fun j => 2 * (j + 1 + n))
        ((List.ofFn fun k => encSent (Ψ k)).getD i 0)) =
      List.ofFn (fun i : Fin n => encForm (Rewriting.emb
        (Rewriting.subst (Ψ i) (#(i.addCast m.succ) :> fun j : Fin m => #(j.succ.addNat n))) :
          Semiproposition ℒₛₑₜ ((m + 1) + n))) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
        List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
      let v : Fin (m + 1) → Semiterm ℒₛₑₜ ℕ ((m + 1) + n) :=
        #((⟨i, hi⟩ : Fin n).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat n)
      have hv : List.ofFn (fun k : Fin (m + 1) => encTerm (v k)) =
          2 * i :: (List.range m).map (fun j => 2 * (j + 1 + n)) := by
        rw [List.ofFn_succ]
        exact congrArg₂ List.cons rfl (list_ofFn_eq_map_range (fun j => 2 * (j + 1 + n)))
      rw [← hv, encSent, cSubstList_encForm]
      congr 1
      symm
      exact emb_rewAux (Rew.subst (#((⟨i, hi⟩ : Fin n).addCast m.succ) :> fun j : Fin m => #(j.succ.addNat n)))
        (Rew.subst v) (fun k => by cases k using Fin.cases <;> rfl) (Ψ ⟨i, hi⟩)
  have h2 : cSubstList (2 * n :: (List.range n).map fun i => 2 * i) (encSent φ) =
      encForm (Rewriting.emb (Rewriting.subst φ (#((0 : Fin (m + 1)).addNat n) :> fun i : Fin n => #(i.addCast m.succ))) :
        Semiproposition ℒₛₑₜ ((m + 1) + n)) := by
    let v : Fin (n + 1) → Semiterm ℒₛₑₜ ℕ ((m + 1) + n) :=
      #((0 : Fin (m + 1)).addNat n) :> fun i : Fin n => #(i.addCast m.succ)
    have hv : List.ofFn (fun k : Fin (n + 1) => encTerm (v k)) =
        2 * n :: (List.range n).map (fun i => 2 * i) := by
      rw [List.ofFn_succ]
      exact congrArg₂ List.cons (by simp [v, encTerm]) (list_ofFn_eq_map_range (fun i => 2 * i))
    rw [← hv, encSent, cSubstList_encForm]
    congr 1
    symm
    exact emb_rewAux (Rew.subst (#((0 : Fin (m + 1)).addNat n) :> fun i : Fin n => #(i.addCast m.succ)))
      (Rew.subst v) (fun k => by cases k using Fin.cases <;> rfl) φ
  rw [h1, cConjList_ofFn, ← emb_conj, h2, cImp_encForm, ← emb_imp, cAllItr_encForm, ← emb_allItr]
  rfl

/- Numeral, setPair, setTriple, finiteSet, transitionEntry -/

def cNumeral : ℕ → ℕ
  | 0 => encSent Constant14.zero
  | n + 1 => cNestFormulaeFunc 0 (encSent succ.dfn) [cNumeral n]

lemma primrec_cNumeral : Primrec cNumeral := by
  have hgen : ∀ c0 cS : ℕ, Primrec (fun n : ℕ =>
      Nat.rec (motive := fun _ => ℕ) c0 (fun _ acc => cNestFormulaeFunc 0 cS [acc]) n) := by
    intro c0 cS
    have hstep : Primrec (fun p : Unit × ℕ × ℕ => cNestFormulaeFunc 0 cS [p.2.2]) :=
      primrec_cNestFormulaeFunc_const 0 cS (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    exact (Primrec.nat_rec (Primrec.const c0) hstep.to₂).comp (Primrec.const ()) Primrec.id
  exact (hgen (encSent Constant14.zero) (encSent succ.dfn)).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun x => cNestFormulaeFunc 0 (encSent succ.dfn) [x]) ih

lemma cNumeral_eq (n : ℕ) : cNumeral n = encSent (Constant14.numeral n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cNumeral, Constant14.numeral, ih]
    simpa [List.ofFn_succ] using cNestFormulaeFunc_encSent succ.dfn ![Constant14.numeral n]

def cSetPair (a b : ℕ) : ℕ := cNestFormulaeFunc 0 (encSent kpair.dfn) [a, b]
def cSetTriple (a b c : ℕ) : ℕ := cSetPair a (cSetPair b c)

lemma primrec_cSetPair : Primrec₂ cSetPair :=
  primrec_cNestFormulaeFunc_const 0 (encSent kpair.dfn)
    (Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

lemma cSetPair_eq (x y : SetTheorySemisentence 1) :
    cSetPair (encSent x) (encSent y) = encSent (Constant14.setPair x y) := by
  simpa [cSetPair, Constant14.setPair, List.ofFn_succ] using cNestFormulaeFunc_encSent kpair.dfn ![x, y]

lemma cSetTriple_eq (x y z : SetTheorySemisentence 1) :
    cSetTriple (encSent x) (encSent y) (encSent z) = encSent (Constant14.setTriple x y z) := by
  simp only [cSetTriple, Constant14.setTriple, cSetPair_eq]

def cFiniteSet : List ℕ → ℕ
  | [] => encSent Constant14.zero
  | x :: xs => cNestFormulaeFunc 0 (encSent insert.dfn) [x, cFiniteSet xs]

private lemma primrec_list_foldr_nat {op : ℕ → ℕ → ℕ} (hop : Primrec₂ op) (c0 : ℕ) :
    Primrec (fun l : List ℕ => l.foldr op c0) :=
  Primrec.list_foldr Primrec.id (Primrec.const c0)
    (hop.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private lemma primrec_cFiniteSet_aux (c0 cI : ℕ) :
    Primrec (fun l : List ℕ => l.foldr (fun x acc => cNestFormulaeFunc 0 cI [x, acc]) c0) :=
  primrec_list_foldr_nat
    (primrec_cNestFormulaeFunc_const 0 cI
      (Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))).to₂
    c0

lemma primrec_cFiniteSet : Primrec cFiniteSet :=
  (primrec_cFiniteSet_aux (encSent Constant14.zero) (encSent insert.dfn)).of_eq fun l => by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldr_cons]
      exact congrArg (fun acc => cNestFormulaeFunc 0 (encSent insert.dfn) [x, acc]) ih

lemma cFiniteSet_eq (l : List (SetTheorySemisentence 1)) :
    cFiniteSet (l.map encSent) = encSent (Constant14.finiteSet l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, cFiniteSet, Constant14.finiteSet, ih]
    simpa [List.ofFn_succ] using cNestFormulaeFunc_encSent insert.dfn ![x, Constant14.finiteSet xs]

def cTransitionEntry (q sym q' w d : ℕ) : ℕ :=
  cSetPair (cSetPair (cNumeral q) (cNumeral sym))
    (cSetTriple (cNumeral q') (cNumeral w) (cNumeral d))

lemma cTransitionEntry_eq (q sym q' w d : ℕ) :
    cTransitionEntry q sym q' w d = encSent (Constant14.transitionEntry q sym q' w d) := by
  simp only [cTransitionEntry, Constant14.transitionEntry, cNumeral_eq, cSetPair_eq, cSetTriple_eq]

/- Encoding `Constant14.configSet`, `nextConfig`, `nextStep`, `halts` -/

def cConfigSet (n : ℕ) : ℕ :=
  Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 2))
    (Nat.pair 8 (cImp
      (cNestFormulaeFunc 2 (encSent prod.dfn)
        [cNestFormulaeFunc 2 (cNumeral n) [],
         cNestFormulaeFunc 2 (encSent prod.dfn)
           [cNestFormulaeFunc 2 (encSent Constant14.integers) [],
            cNestFormulaeFunc 2 (encSent function.dfn)
              [cNestFormulaeFunc 2 (cNumeral 2) [],
               cNestFormulaeFunc 2 (encSent Constant14.integers) []]]])
      (Nat.pair 2 (Nat.pair 2 0)))))

lemma primrec_cConfigSet : Primrec cConfigSet := by
  unfold cConfigSet
  have hnum : Primrec (fun n : ℕ => cNestFormulaeFunc 2 (cNumeral n) []) :=
    primrec_cNestFormulaeFunc_var 2 primrec_cNumeral (Primrec.const [])
  have hprod : Primrec (fun n : ℕ => cNestFormulaeFunc 2 (encSent prod.dfn)
      [cNestFormulaeFunc 2 (cNumeral n) [],
       cNestFormulaeFunc 2 (encSent prod.dfn)
         [cNestFormulaeFunc 2 (encSent Constant14.integers) [],
          cNestFormulaeFunc 2 (encSent function.dfn)
            [cNestFormulaeFunc 2 (cNumeral 2) [],
             cNestFormulaeFunc 2 (encSent Constant14.integers) []]]]) :=
    primrec_cNestFormulaeFunc_const 2 (encSent prod.dfn)
      (Primrec.list_cons.comp hnum (Primrec.const _))
  exact primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp (Primrec.const _)
    (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hprod (Primrec.const _))))

lemma cConfigSet_eq (n : ℕ) : cConfigSet n = encSent (Constant14.configSet n) := by
  unfold cConfigSet Constant14.configSet
  have h1 : cNestFormulaeFunc 2 (cNumeral n) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral n) ![]) := by
    rw [cNumeral_eq]
    simpa using cNestFormulaeFunc_encSent (m := 2) (Constant14.numeral n) ![]
  have h2 : cNestFormulaeFunc 2 (encSent Constant14.integers) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]) := by
    simpa using cNestFormulaeFunc_encSent (m := 2) Constant14.integers ![]
  have h3 : cNestFormulaeFunc 2 (cNumeral 2) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![]) := by
    rw [cNumeral_eq]
    simpa using cNestFormulaeFunc_encSent (m := 2) (Constant14.numeral 2) ![]
  have h4 : cNestFormulaeFunc 2 (encSent function.dfn)
        [encSent (Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![]),
         encSent (Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![])] =
      encSent (Semiformula.nestFormulaeFunc (m := 2) function.dfn
        ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
          Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]]) := by
    simpa [List.ofFn_succ] using cNestFormulaeFunc_encSent (m := 2) function.dfn
      ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
        Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]]
  have h5 : cNestFormulaeFunc 2 (encSent prod.dfn)
        [encSent (Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]),
         encSent (Semiformula.nestFormulaeFunc (m := 2) function.dfn
           ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
             Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]])] =
      encSent (Semiformula.nestFormulaeFunc (m := 2) prod.dfn
        ![Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![],
          Semiformula.nestFormulaeFunc (m := 2) function.dfn
            ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
              Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]]]) := by
    simpa [List.ofFn_succ] using cNestFormulaeFunc_encSent (m := 2) prod.dfn
      ![Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![],
        Semiformula.nestFormulaeFunc (m := 2) function.dfn
          ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
            Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]]]
  rw [h1, h2, h3, h4, h5]
  have h6 := cNestFormulaeFunc_encSent (m := 2) prod.dfn
    ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral n) ![],
      Semiformula.nestFormulaeFunc (m := 2) prod.dfn
        ![Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![],
          Semiformula.nestFormulaeFunc (m := 2) function.dfn
            ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
              Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]]]]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h6
  rw [h6]
  simp only [encSent_all, encSent_imp]
  rfl

/- Extract the two constant sub-parts of `nextConfig` that do not depend on `n` or `instructions` -/
private def nextConfigArg2 : SetTheorySemisentence 5 :=
  Semiformula.nestFormulaeFunc (m := 4) kpair.dfn
    ![Semiformula.nestFormulaeFunc (m := 4) kpair.π₁.dfn ![Semiformula.rel Language.Set.Rel.eq ![#0, #4]],
      Semiformula.nestFormulaeFunc (m := 4) value.dfn
        ![Semiformula.nestFormulaeFunc (m := 4) kpair.π₂.dfn
            ![Semiformula.nestFormulaeFunc (m := 4) kpair.π₂.dfn ![Semiformula.rel Language.Set.Rel.eq ![#0, #4]]],
          Semiformula.nestFormulaeFunc (m := 4) kpair.π₁.dfn
            ![Semiformula.nestFormulaeFunc (m := 4) kpair.π₂.dfn ![Semiformula.rel Language.Set.Rel.eq ![#0, #4]]]]]

private def nextConfigRest : SetTheorySemisentence 3 :=
  match Constant14.nextConfig 0 Constant14.zero with
  | .and _ (.and _ (.exs (.and _ rest))) => rest
  | _ => ⊤

private lemma nextConfig_decomp (n : ℕ) (inst : SetTheorySemisentence 1) :
    Constant14.nextConfig n inst =
      (∀¹ (Semiformula.rel Language.Set.Rel.eq ![#0, #2] 🡒
          ∀¹ (Semiformula.nestFormulaeFunc (m := 3) (Constant14.configSet n) ![] 🡒
            Semiformula.rel Language.Set.Rel.mem ![#1, #0]))) ⋏
      (∀¹ (Semiformula.rel Language.Set.Rel.eq ![#0, #1] 🡒
          ∀¹ (Semiformula.nestFormulaeFunc (m := 3) (Constant14.configSet n) ![] 🡒
            Semiformula.rel Language.Set.Rel.mem ![#1, #0]))) ⋏
      (∃¹ ((∀¹ (Semiformula.rel Language.Set.Rel.eq ![#0, #1] 🡒
            ∀¹ (Semiformula.nestFormulaeFunc (m := 4) value.dfn
                ![Semiformula.nestFormulaeFunc (m := 4) inst ![], nextConfigArg2] 🡒
              Semiformula.rel Language.Set.Rel.eq ![#1, #0]))) ⋏
          nextConfigRest)) := rfl

def cNextConfig (n cInst : ℕ) : ℕ :=
  let cCfg := cNestFormulaeFunc 3 (cConfigSet n) []
  let c1 := Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 4))
    (Nat.pair 8 (cImp cCfg (Nat.pair 3 (Nat.pair 2 0)))))
  let c2 := Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 2))
    (Nat.pair 8 (cImp cCfg (Nat.pair 3 (Nat.pair 2 0)))))
  let c3 := Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 2))
    (Nat.pair 8 (cImp
      (cNestFormulaeFunc 4 (encSent value.dfn)
        [cNestFormulaeFunc 4 cInst [], encSent nextConfigArg2])
      (Nat.pair 2 (Nat.pair 2 0)))))
  Nat.pair 6 (Nat.pair c1 (Nat.pair 6 (Nat.pair c2 (Nat.pair 9 (Nat.pair 6 (Nat.pair c3 (encSent nextConfigRest)))))))

lemma primrec_cNextConfig : Primrec₂ cNextConfig := by
  unfold cNextConfig
  have hcfg : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 3 (cConfigSet p.1) []) :=
    primrec_cNestFormulaeFunc_var 3 (primrec_cConfigSet.comp Primrec.fst) (Primrec.const [])
  have hc1 : Primrec (fun p : ℕ × ℕ => Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 4))
      (Nat.pair 8 (cImp (cNestFormulaeFunc 3 (cConfigSet p.1) []) (Nat.pair 3 (Nat.pair 2 0)))))) :=
    primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp (Primrec.const _)
      (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hcfg (Primrec.const _))))
  have hc2 : Primrec (fun p : ℕ × ℕ => Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 2))
      (Nat.pair 8 (cImp (cNestFormulaeFunc 3 (cConfigSet p.1) []) (Nat.pair 3 (Nat.pair 2 0)))))) :=
    primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp (Primrec.const _)
      (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hcfg (Primrec.const _))))
  have hinst4 : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 4 p.2 []) :=
    primrec_cNestFormulaeFunc_var 4 Primrec.snd (Primrec.const [])
  have hval4 : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 4 (encSent value.dfn)
      [cNestFormulaeFunc 4 p.2 [], encSent nextConfigArg2]) :=
    primrec_cNestFormulaeFunc_const 4 (encSent value.dfn)
      (Primrec.list_cons.comp hinst4 (Primrec.const [encSent nextConfigArg2]))
  have hc3 : Primrec (fun p : ℕ × ℕ => Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 2))
      (Nat.pair 8 (cImp (cNestFormulaeFunc 4 (encSent value.dfn)
        [cNestFormulaeFunc 4 p.2 [], encSent nextConfigArg2]) (Nat.pair 2 (Nat.pair 2 0)))))) :=
    primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp (Primrec.const _)
      (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hval4 (Primrec.const _))))
  exact primrec_natPair.comp (Primrec.const 6) (primrec_natPair.comp hc1
    (primrec_natPair.comp (Primrec.const 6) (primrec_natPair.comp hc2
      (primrec_natPair.comp (Primrec.const 9) (primrec_natPair.comp (Primrec.const 6)
        (primrec_natPair.comp hc3 (Primrec.const (encSent nextConfigRest))))))))

lemma cNextConfig_eq (n : ℕ) (inst : SetTheorySemisentence 1) :
    cNextConfig n (encSent inst) = encSent (Constant14.nextConfig n inst) := by
  rw [nextConfig_decomp]
  unfold cNextConfig
  have hcfg : cNestFormulaeFunc 3 (cConfigSet n) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 3) (Constant14.configSet n) ![]) := by
    rw [cConfigSet_eq]
    simpa using cNestFormulaeFunc_encSent (m := 3) (Constant14.configSet n) ![]
  have hinst : cNestFormulaeFunc 4 (encSent inst) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 4) inst ![]) := by
    simpa using cNestFormulaeFunc_encSent (m := 4) inst ![]
  have hval := cNestFormulaeFunc_encSent (m := 4) value.dfn
    ![Semiformula.nestFormulaeFunc (m := 4) inst ![], nextConfigArg2]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at hval
  dsimp only
  rw [hcfg, hinst, hval]
  simp only [encSent_and, encSent_all, encSent_exs, encSent_imp]
  rfl

private def nextStepPairEq : SetTheorySemisentence 6 :=
  ∀¹ (Semiformula.rel Language.Set.Rel.eq ![#0, #5] 🡒
    ∀¹ (Semiformula.nestFormulaeFunc (m := 7) kpair.dfn
        ![Semiformula.rel Language.Set.Rel.eq ![#0, #4],
          Semiformula.rel Language.Set.Rel.eq ![#0, #2]] 🡒
      Semiformula.rel Language.Set.Rel.eq ![#1, #0]))

def cNextStep (n cInst : ℕ) : ℕ :=
  let lhs := Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 2))
    (Nat.pair 8 (cImp (Nat.pair 2 (Nat.pair 0 6)) (Nat.pair 3 (Nat.pair 2 0)))))
  let cCfg2 := cNestFormulaeFunc 2 (cConfigSet n) []
  let cCfg4 := cNestFormulaeFunc 4 (cConfigSet n) []
  let cNC := cNestFormulae 6 (cNextConfig n cInst)
    [Nat.pair 2 (Nat.pair 0 2), Nat.pair 2 (Nat.pair 0 6)]
  let inner := Nat.pair 9 (Nat.pair 6 (Nat.pair (Nat.pair 3 (Nat.pair 0 2))
    (Nat.pair 6 (Nat.pair (encSent nextStepPairEq) cNC))))
  let mid := Nat.pair 8 (cImp cCfg4 inner)
  let outer := Nat.pair 8 (cImp cCfg2
    (Nat.pair 9 (Nat.pair 6 (Nat.pair (Nat.pair 3 (Nat.pair 0 2)) mid))))
  Nat.pair 8 (cIff lhs outer)

lemma primrec_cNextStep : Primrec₂ cNextStep := by
  unfold cNextStep
  have hcfg2 : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 2 (cConfigSet p.1) []) :=
    primrec_cNestFormulaeFunc_var 2 (primrec_cConfigSet.comp Primrec.fst) (Primrec.const [])
  have hcfg4 : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 4 (cConfigSet p.1) []) :=
    primrec_cNestFormulaeFunc_var 4 (primrec_cConfigSet.comp Primrec.fst) (Primrec.const [])
  have hnc : Primrec (fun p : ℕ × ℕ => cNestFormulae 6 (cNextConfig p.1 p.2)
      [Nat.pair 2 (Nat.pair 0 2), Nat.pair 2 (Nat.pair 0 6)]) :=
    primrec_cNestFormulae_var 6 primrec_cNextConfig (Primrec.const _)
  refine primrec_natPair.comp (Primrec.const 8) (primrec_cIff.comp (Primrec.const _)
    (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hcfg2
      (primrec_natPair.comp (Primrec.const 9) (primrec_natPair.comp (Primrec.const 6)
        (primrec_natPair.comp (Primrec.const _)
          (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hcfg4
            (primrec_natPair.comp (Primrec.const 9) (primrec_natPair.comp (Primrec.const 6)
              (primrec_natPair.comp (Primrec.const _)
                (primrec_natPair.comp (Primrec.const 6)
                  (primrec_natPair.comp (Primrec.const _) hnc)))))))))))))

lemma cNextStep_eq (n : ℕ) (inst : SetTheorySemisentence 1) :
    cNextStep n (encSent inst) = encSent (Constant14.nextStep n inst) := by
  unfold cNextStep Constant14.nextStep
  have hc2 : cNestFormulaeFunc 2 (cConfigSet n) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 2) (Constant14.configSet n) ![]) := by
    rw [cConfigSet_eq]; simpa using cNestFormulaeFunc_encSent (m := 2) (Constant14.configSet n) ![]
  have hc4 : cNestFormulaeFunc 4 (cConfigSet n) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 4) (Constant14.configSet n) ![]) := by
    rw [cConfigSet_eq]; simpa using cNestFormulaeFunc_encSent (m := 4) (Constant14.configSet n) ![]
  have hnc : cNestFormulae 6 (cNextConfig n (encSent inst))
        [Nat.pair 2 (Nat.pair 0 2), Nat.pair 2 (Nat.pair 0 6)] =
      encSent (Semiformula.nestFormulae (m := 6) (Constant14.nextConfig n inst)
        ![Semiformula.rel Language.Set.Rel.eq ![#0, #1],
          Semiformula.rel Language.Set.Rel.eq ![#0, #3]]) := by
    rw [cNextConfig_eq]
    have h := cNestFormulae_encSent (m := 6) (Constant14.nextConfig n inst)
      ![Semiformula.rel Language.Set.Rel.eq ![#0, #1],
        Semiformula.rel Language.Set.Rel.eq ![#0, #3]]
    simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h
    exact h
  dsimp only
  rw [hc2, hc4, hnc]
  unfold nextStepPairEq
  simp only [encSent_all, encSent_bexMem, encSent_and, encSent_imp, encSent_iff]
  rfl

private def haltsInnerPair : SetTheorySemisentence 5 :=
  Semiformula.nestFormulaeFunc (m := 4) kpair.dfn
    ![Semiformula.rel Language.Set.Rel.eq ![#0, #3],
      Semiformula.rel Language.Set.Rel.eq ![#0, #1]]

private def haltsFunc2Int : SetTheorySemisentence 3 :=
  Semiformula.nestFormulaeFunc (m := 2) function.dfn
    ![Semiformula.nestFormulaeFunc (m := 2) (Constant14.numeral 2) ![],
      Semiformula.nestFormulaeFunc (m := 2) Constant14.integers ![]]

def cHalts (n cInst : ℕ) : ℕ :=
  let cInt0 := cNestFormulaeFunc 0 (encSent Constant14.integers) []
  let cKpair := cNestFormulaeFunc 4 (encSent kpair.dfn)
    [cNestFormulaeFunc 4 (cNumeral n) [], encSent haltsInnerPair]
  let cOrbit := cNestFormulaeFunc 5 (encSent Constant14.orbit)
    [cNestFormulaeFunc 5 (cNextStep (n + 1) cInst) [],
     cNestFormulaeFunc 5 (encSent Constant14.initialConfig) []]
  Nat.pair 8 (cImp cInt0
    (Nat.pair 9 (Nat.pair 6 (Nat.pair (Nat.pair 3 (Nat.pair 0 2))
      (Nat.pair 8 (cImp (encSent haltsFunc2Int)
        (Nat.pair 9 (Nat.pair 6 (Nat.pair (Nat.pair 3 (Nat.pair 0 2))
          (Nat.pair 8 (cImp cKpair
            (Nat.pair 8 (cImp cOrbit (Nat.pair 3 (Nat.pair 2 0)))))))))))))))

lemma primrec_cHalts : Primrec₂ cHalts := by
  unfold cHalts
  have hnum4 : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 4 (cNumeral p.1) []) :=
    primrec_cNestFormulaeFunc_var 4 (primrec_cNumeral.comp Primrec.fst) (Primrec.const [])
  have hkp : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 4 (encSent kpair.dfn)
      [cNestFormulaeFunc 4 (cNumeral p.1) [], encSent haltsInnerPair]) :=
    primrec_cNestFormulaeFunc_const 4 (encSent kpair.dfn)
      (Primrec.list_cons.comp hnum4 (Primrec.const [encSent haltsInnerPair]))
  have hns5 : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 5 (cNextStep (p.1 + 1) p.2) []) :=
    primrec_cNestFormulaeFunc_var 5
      (primrec_cNextStep.comp (Primrec.succ.comp Primrec.fst) Primrec.snd) (Primrec.const [])
  have horb : Primrec (fun p : ℕ × ℕ => cNestFormulaeFunc 5 (encSent Constant14.orbit)
      [cNestFormulaeFunc 5 (cNextStep (p.1 + 1) p.2) [],
       cNestFormulaeFunc 5 (encSent Constant14.initialConfig) []]) :=
    primrec_cNestFormulaeFunc_const 5 (encSent Constant14.orbit)
      (Primrec.list_cons.comp hns5 (Primrec.const _))
  refine primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp (Primrec.const _)
    (primrec_natPair.comp (Primrec.const 9) (primrec_natPair.comp (Primrec.const 6)
      (primrec_natPair.comp (Primrec.const _)
        (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp (Primrec.const _)
          (primrec_natPair.comp (Primrec.const 9) (primrec_natPair.comp (Primrec.const 6)
            (primrec_natPair.comp (Primrec.const _)
              (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp hkp
                (primrec_natPair.comp (Primrec.const 8) (primrec_cImp.comp horb
                  (Primrec.const _))))))))))))))

lemma cHalts_eq {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    cHalts n (encSent (Constant14.instructionTable M)) = encSent (Constant14.halts M) := by
  unfold cHalts Constant14.halts
  have hi0 : cNestFormulaeFunc 0 (encSent Constant14.integers) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 0) Constant14.integers ![]) := by
    simpa using cNestFormulaeFunc_encSent (m := 0) Constant14.integers ![]
  have hnum : cNestFormulaeFunc 4 (cNumeral n) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 4) (Constant14.numeral n) ![]) := by
    rw [cNumeral_eq]; simpa using cNestFormulaeFunc_encSent (m := 4) (Constant14.numeral n) ![]
  have hkp := cNestFormulaeFunc_encSent (m := 4) kpair.dfn
    ![Semiformula.nestFormulaeFunc (m := 4) (Constant14.numeral n) ![], haltsInnerPair]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at hkp
  have hns : cNestFormulaeFunc 5 (cNextStep (n + 1) (encSent (Constant14.instructionTable M))) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 5) (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![]) := by
    rw [cNextStep_eq]
    simpa using cNestFormulaeFunc_encSent (m := 5) (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![]
  have hic : cNestFormulaeFunc 5 (encSent Constant14.initialConfig) [] =
      encSent (Semiformula.nestFormulaeFunc (m := 5) Constant14.initialConfig ![]) := by
    simpa using cNestFormulaeFunc_encSent (m := 5) Constant14.initialConfig ![]
  have horb := cNestFormulaeFunc_encSent (m := 5) Constant14.orbit
    ![Semiformula.nestFormulaeFunc (m := 5) (Constant14.nextStep (n + 1) (Constant14.instructionTable M)) ![],
      Semiformula.nestFormulaeFunc (m := 5) Constant14.initialConfig ![]]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at horb
  dsimp only
  rw [hi0, hnum, hkp, hns, hic, horb]
  simp only [encSent_all, encSent_bexMem, encSent_and, encSent_imp]
  rfl

/- Computable transition table for `prependBits bits B₀` -/

def cTransPrepend {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m))
    (bits : List (Fin 2)) (q sym : ℕ) : ℕ :=
  let L := bits.length
  let n := 2 * L + m
  if q < L then
    cTransitionEntry q sym (q + 1) ((bits.getD q 0).val) 2
  else if q < 2 * L then
    cTransitionEntry q sym (q + 1) sym 0
  else
    let q0 := q - 2 * L
    let out : ℕ × ℕ × ℕ :=
      if hq : q0 < m then
        if hs : sym < 2 then
          match B₀ ⟨q0, hq⟩ ⟨sym, hs⟩ with
          | none => (n, sym, 1)
          | some (none, st) => (n, st.symbol.val, Constant14.directionCode (some st.dir))
          | some (some q', st) => (2 * L + q'.val, st.symbol.val, Constant14.directionCode (some st.dir))
        else (n, sym, 1)
      else (n, sym, 1)
    cTransitionEntry q sym out.1 out.2.1 out.2.2

def cInstTablePrepend {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m)) (bits : List (Fin 2)) : ℕ :=
  let n := 2 * bits.length + m
  let rows := ((List.range n).map fun q =>
    [cTransPrepend B₀ bits q 0, cTransPrepend B₀ bits q 1]).flatten
  let haltRows := [cTransitionEntry n 0 n 0 1, cTransitionEntry n 1 n 1 1]
  cFiniteSet (rows ++ haltRows)

def cNegHaltsPrepend {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m)) (bits : List (Fin 2)) : ℕ :=
  cNeg (cHalts (2 * bits.length + m) (cInstTablePrepend B₀ bits))

private lemma primrec_cTransitionEntry_app {α : Type} [Primcodable α]
    {f1 f2 f3 f4 f5 : α → ℕ}
    (h1 : Primrec f1) (h2 : Primrec f2) (h3 : Primrec f3) (h4 : Primrec f4) (h5 : Primrec f5) :
    Primrec (fun a => cTransitionEntry (f1 a) (f2 a) (f3 a) (f4 a) (f5 a)) :=
  primrec_cSetPair.comp
    (primrec_cSetPair.comp (primrec_cNumeral.comp h1) (primrec_cNumeral.comp h2))
    (primrec_cSetPair.comp (primrec_cNumeral.comp h3)
      (primrec_cSetPair.comp (primrec_cNumeral.comp h4) (primrec_cNumeral.comp h5)))

private lemma primrec_of_fintype_table {m : ℕ} (f : ℕ → ℕ → ℕ × ℕ × ℕ)
    (hconst : ∀ q s, ¬ (q < m ∧ s < 2) → f q s = (0, 0, 0)) :
    Primrec₂ f := by
  let tbl : List (List (ℕ × ℕ × ℕ)) :=
    (List.range m).map fun q => [f q 0, f q 1]
  have hget : Primrec₂ (fun q s => (tbl.getD q []).getD s (0, 0, 0)) := by
    have h1 : Primrec (fun q => tbl.getD q []) :=
      (Primrec.option_casesOn (Primrec.list_getElem?.comp (Primrec.const tbl) Primrec.id)
        (Primrec.const ([] : List (ℕ × ℕ × ℕ))) Primrec₂.right).of_eq fun q => by
          cases h : tbl[q]? <;> simp [List.getD_eq_getElem?_getD, h]
    exact (Primrec.option_casesOn (Primrec.list_getElem?.comp (h1.comp Primrec.fst) Primrec.snd)
      (Primrec.const ((0, 0, 0) : ℕ × ℕ × ℕ)) Primrec₂.right).of_eq fun p => by
        dsimp only
        generalize tbl.getD p.1 [] = row
        rw [List.getD_eq_getElem?_getD]
        cases row[p.2]? <;> rfl
  exact hget.of_eq fun q s => by
    by_cases hq : q < m
    · by_cases hs : s < 2
      · have hs' : s = 0 ∨ s = 1 := by omega
        rcases hs' with rfl | rfl <;> simp [tbl, List.getD_eq_getElem?_getD, hq]
      · have hs2 : 2 ≤ s := by omega
        simp [tbl, List.getD_eq_getElem?_getD, hq, List.getElem?_eq_none (by simp; omega : [f q 0, f q 1].length ≤ s),
          hconst q s (by omega)]
    · have hqm : m ≤ q := by omega
      simp [tbl, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [tbl]; omega : tbl.length ≤ q),
        hconst q s (by omega)]

lemma primrec_cNegHaltsPrepend {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m)) :
    Primrec (cNegHaltsPrepend B₀) := by
  let raw : ℕ → ℕ → ℕ × ℕ × ℕ := fun q0 sym =>
    if hq : q0 < m then
      if hs : sym < 2 then
        match B₀ ⟨q0, hq⟩ ⟨sym, hs⟩ with
        | none => (0, sym, 1)
        | some (none, st) => (0, st.symbol.val, Constant14.directionCode (some st.dir))
        | some (some q', st) => (q'.val + 1, st.symbol.val, Constant14.directionCode (some st.dir))
      else (0, 0, 0)
    else (0, 0, 0)
  have hraw : Primrec₂ raw := primrec_of_fintype_table raw (fun q s h => by
    by_cases hq : q < m
    · have hs : ¬ s < 2 := fun hs => h ⟨hq, hs⟩
      dsimp only [raw]; rw [dif_pos hq, dif_neg hs]
    · dsimp only [raw]; rw [dif_neg hq])
  have htrans : Primrec₂ (fun (bits : List (Fin 2)) (qs : ℕ) => cTransPrepend B₀ bits qs.unpair.1 qs.unpair.2) := by
    let P := List (Fin 2) × ℕ
    have hbits : Primrec (fun p : P => p.1) := Primrec.fst
    have hq : Primrec (fun p : P => p.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hs : Primrec (fun p : P => p.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
    have hL : Primrec (fun p : P => p.1.length) := Primrec.list_length.comp hbits
    have h2L : Primrec (fun p : P => 2 * p.1.length) := Primrec.nat_mul.comp (Primrec.const 2) hL
    have hn : Primrec (fun p : P => 2 * p.1.length + m) := Primrec.nat_add.comp h2L (Primrec.const m)
    have hgetBit : Primrec (fun p : P => (p.1.getD p.2.unpair.1 0).val) :=
      (Primrec.option_casesOn (Primrec.list_getElem?.comp hbits hq)
        (Primrec.const 0) (Primrec.fin_val.comp Primrec.snd).to₂).of_eq fun p => by
          cases h : p.1[p.2.unpair.1]? <;> simp [List.getD_eq_getElem?_getD, h]
    have hq0 : Primrec (fun p : P => p.2.unpair.1 - 2 * p.1.length) := Primrec.nat_sub.comp hq h2L
    have hr : Primrec (fun p : P => raw (p.2.unpair.1 - 2 * p.1.length) p.2.unpair.2) := hraw.comp hq0 hs
    have hcond : PrimrecPred (fun p : P => p.2.unpair.1 - 2 * p.1.length < m ∧ p.2.unpair.2 < 2) :=
      (Primrec.nat_lt.comp hq0 (Primrec.const m)).and (Primrec.nat_lt.comp hs (Primrec.const 2))
    have hout1 : Primrec (fun p : P =>
        if p.2.unpair.1 - 2 * p.1.length < m ∧ p.2.unpair.2 < 2 then
          if (raw (p.2.unpair.1 - 2 * p.1.length) p.2.unpair.2).1 = 0 then 2 * p.1.length + m
          else 2 * p.1.length + ((raw (p.2.unpair.1 - 2 * p.1.length) p.2.unpair.2).1 - 1)
        else 2 * p.1.length + m) :=
      Primrec.ite hcond
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hr) (Primrec.const 0)) hn
          (Primrec.nat_add.comp h2L (Primrec.nat_sub.comp (Primrec.fst.comp hr) (Primrec.const 1))))
        hn
    have hout2 : Primrec (fun p : P =>
        if p.2.unpair.1 - 2 * p.1.length < m ∧ p.2.unpair.2 < 2 then (raw (p.2.unpair.1 - 2 * p.1.length) p.2.unpair.2).2.1 else p.2.unpair.2) :=
      Primrec.ite hcond (Primrec.fst.comp (Primrec.snd.comp hr)) hs
    have hout3 : Primrec (fun p : P =>
        if p.2.unpair.1 - 2 * p.1.length < m ∧ p.2.unpair.2 < 2 then (raw (p.2.unpair.1 - 2 * p.1.length) p.2.unpair.2).2.2 else 1) :=
      Primrec.ite hcond (Primrec.snd.comp (Primrec.snd.comp hr)) (Primrec.const 1)
    have hbr1 := primrec_cTransitionEntry_app hq hs (Primrec.succ.comp hq) hgetBit (Primrec.const 2)
    have hbr2 := primrec_cTransitionEntry_app hq hs (Primrec.succ.comp hq) hs (Primrec.const 0)
    have hbr3 := primrec_cTransitionEntry_app hq hs hout1 hout2 hout3
    have hfull := Primrec.ite (Primrec.nat_lt.comp hq hL) hbr1
      (Primrec.ite (Primrec.nat_lt.comp hq h2L) hbr2 hbr3)
    exact hfull.of_eq fun p => by
      rcases p with ⟨bits, qs⟩
      dsimp only
      set q := qs.unpair.1
      set sym := qs.unpair.2
      unfold cTransPrepend
      by_cases h1 : q < bits.length
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : q < 2 * bits.length
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          dsimp only
          by_cases hq' : q - 2 * bits.length < m
          · by_cases hs' : sym < 2
            · have hc : q - 2 * bits.length < m ∧ sym < 2 := ⟨hq', hs'⟩
              rw [if_pos hc, if_pos hc, if_pos hc, dif_pos hq', dif_pos hs']
              have hraw_eq : raw (q - 2 * bits.length) sym =
                  match B₀ ⟨q - 2 * bits.length, hq'⟩ ⟨sym, hs'⟩ with
                  | none => (0, sym, 1)
                  | some (none, st) => (0, st.symbol.val, Constant14.directionCode (some st.dir))
                  | some (some q', st) => (q'.val + 1, st.symbol.val, Constant14.directionCode (some st.dir)) := by
                dsimp only [raw]; rw [dif_pos hq', dif_pos hs']
              simp only [hraw_eq]
              cases B₀ ⟨q - 2 * bits.length, hq'⟩ ⟨sym, hs'⟩ with
              | none => rfl
              | some v =>
                rcases v with ⟨o, st⟩
                cases o with
                | none => rfl
                | some q' =>
                  change cTransitionEntry q sym (if q'.val + 1 = 0 then _ else _) _ _ = _
                  rw [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
            · have hc : ¬ (q - 2 * bits.length < m ∧ sym < 2) := fun h => hs' h.2
              rw [if_neg hc, if_neg hc, if_neg hc, dif_pos hq', dif_neg hs']
          · have hc : ¬ (q - 2 * bits.length < m ∧ sym < 2) := fun h => hq' h.1
            rw [if_neg hc, if_neg hc, if_neg hc, dif_neg hq']
  have hflat : Primrec (List.flatten : List (List ℕ) → List ℕ) := by
    exact (Primrec.list_foldr Primrec.id (Primrec.const ([] : List ℕ))
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun l => by
        induction l with
        | nil => rfl
        | cons a l ih =>
          dsimp only [id_eq] at ih ⊢
          simp only [List.flatten_cons, List.foldr_cons, ih]
  have hinst : Primrec (cInstTablePrepend B₀) := by
    unfold cInstTablePrepend
    have hn : Primrec (fun bits : List (Fin 2) => 2 * bits.length + m) :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length) (Primrec.const m)
    have ht0 : Primrec (fun p : List (Fin 2) × ℕ => cTransPrepend B₀ p.1 p.2 0) :=
      (htrans.comp Primrec.fst (primrec_natPair.comp Primrec.snd (Primrec.const 0))).of_eq fun p => by
        simp only [Nat.unpair_pair]
    have ht1 : Primrec (fun p : List (Fin 2) × ℕ => cTransPrepend B₀ p.1 p.2 1) :=
      (htrans.comp Primrec.fst (primrec_natPair.comp Primrec.snd (Primrec.const 1))).of_eq fun p => by
        simp only [Nat.unpair_pair]
    have hrows : Primrec (fun bits : List (Fin 2) =>
        ((List.range (2 * bits.length + m)).map fun q =>
          [cTransPrepend B₀ bits q 0, cTransPrepend B₀ bits q 1]).flatten) :=
      hflat.comp (Primrec.list_map (primrec_list_range.comp hn)
        (Primrec.list_cons.comp ht0 (Primrec.list_cons.comp ht1 (Primrec.const []))).to₂)
    have hhalt : Primrec (fun bits : List (Fin 2) =>
        [cTransitionEntry (2 * bits.length + m) 0 (2 * bits.length + m) 0 1,
         cTransitionEntry (2 * bits.length + m) 1 (2 * bits.length + m) 1 1]) :=
      Primrec.list_cons.comp
        (primrec_cTransitionEntry_app hn (Primrec.const 0) hn (Primrec.const 0) (Primrec.const 1))
        (Primrec.list_cons.comp
          (primrec_cTransitionEntry_app hn (Primrec.const 1) hn (Primrec.const 1) (Primrec.const 1))
          (Primrec.const []))
    exact primrec_cFiniteSet.comp (Primrec.list_append.comp hrows hhalt)
  have hn : Primrec (fun bits : List (Fin 2) => 2 * bits.length + m) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length) (Primrec.const m)
  exact primrec_cNeg.comp (primrec_cHalts.comp hn hinst)

lemma cInstTablePrepend_eq {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m)) (bits : List (Fin 2)) :
    cInstTablePrepend B₀ bits = encSent (Constant14.instructionTable (C14H4Part3.prependBits bits B₀)) := by
  unfold cInstTablePrepend Constant14.instructionTable Constant14.transitionEntries
  dsimp only
  rw [← cFiniteSet_eq]
  apply congrArg cFiniteSet
  rw [List.map_append, List.map_flatten]
  apply congrArg₂ List.append
  · rw [List.map_ofFn]
    have hrow : ∀ q : Fin (2 * bits.length + m),
        [cTransPrepend B₀ bits q.val 0, cTransPrepend B₀ bits q.val 1] =
          (List.ofFn fun symbol : Fin 2 =>
            letI output := Constant14.transitionCode (C14H4Part3.prependBits bits B₀) q symbol
            Constant14.transitionEntry q.val symbol.val output.1 output.2.1 output.2.2).map encSent := by
      intro q
      simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]
      have hsym : ∀ sym : Fin 2,
          cTransPrepend B₀ bits q.val sym.val =
            encSent (letI output := Constant14.transitionCode (C14H4Part3.prependBits bits B₀) q sym
              Constant14.transitionEntry q.val sym.val output.1 output.2.1 output.2.2) := by
        intro sym
        rw [← cTransitionEntry_eq]
        unfold cTransPrepend Constant14.transitionCode C14H4Part3.prependBits
        by_cases h1 : q.val < bits.length
        · simp [h1, Constant14.stateCode, Constant14.directionCode, List.getD_eq_getElem?_getD]
        · by_cases h2 : q.val < 2 * bits.length
          · simp [h1, h2, Constant14.stateCode, Constant14.directionCode]
          · have hq0 : q.val - 2 * bits.length < m := by omega
            simp only [h1, h2, hq0, sym.isLt, ↓reduceIte, ↓reduceDIte]
            cases hB : B₀ ⟨q.val - 2 * bits.length, hq0⟩ sym with
            | none => simp [Constant14.directionCode]
            | some v =>
              rcases v with ⟨o, st⟩
              cases o with
              | none => simp [Constant14.stateCode, Constant14.directionCode]
              | some q' => simp [Constant14.stateCode, Constant14.directionCode]
      exact congrArg₂ List.cons (hsym 0) (congrArg₂ List.cons (hsym 1) rfl)
    rw [← list_ofFn_eq_map_range]
    apply congrArg List.flatten
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, Function.comp_apply]
      exact hrow ⟨i, by simpa using h1⟩
  · simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
      Fin.val_zero, Fin.val_succ, cTransitionEntry_eq, Constant14.directionCode]

lemma cNegHaltsPrepend_eq {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m)) (bits : List (Fin 2)) :
    cNegHaltsPrepend B₀ bits = encSent (∼Constant14.halts (C14H4Part3.prependBits bits B₀)) := by
  unfold cNegHaltsPrepend
  rw [cInstTablePrepend_eq, cHalts_eq, encSent, cNeg_encForm, encSent]
  exact congrArg encForm (rewAux_neg_g Rew.emb _).symm

/-- Main Part 2 Theorem: `REPred` of ZFC refutability of `prependBits bits B₀` halting! -/
theorem rePred_provable_neg_halts_prepend {m : ℕ} [NeZero m] (B₀ : Machine (Fin 2) (Fin m)) :
    REPred (fun bits : List (Fin 2) =>
      FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (C14H4Part3.prependBits bits B₀))) :=
  rePred_provable_of_primrec (primrec_cNegHaltsPrepend B₀) (cNegHaltsPrepend_eq B₀)

end C14H4Part2

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver in
theorem OMA.solution : OMA.R_Constant14_c14_ge_4_R1.H4 := by
  unfold OMA.R_Constant14_c14_ge_4_R1.H4
  by_contra hall
  have hall' : ∀ (n : ℕ) [NeZero n] (M : BusyBeaver.Machine (Fin 2) (Fin n)),
      ¬ M.IsHalting → FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
    intro n hn M hnh
    by_contra hnp
    exact hall ⟨n, hn, M, hnh, hnp⟩
  obtain ⟨k, hk, B₀, bitsOfCode, hcomp, hiff⟩ := C14H4Part3.exists_universal_bb
  haveI : NeZero k := hk
  have hre_bits : REPred (fun bits : List (Fin 2) =>
      FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (C14H4Part3.prependBits bits B₀))) :=
    C14H4Part2.rePred_provable_neg_halts_prepend B₀
  have hre_code : REPred (fun c : Nat.Partrec.Code =>
      FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts (C14H4Part3.prependBits (bitsOfCode c) B₀))) :=
    hre_bits.comp hcomp
  have hre_nonhalt : REPred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) := by
    refine hre_code.of_eq fun c => ?_
    constructor
    · intro hprov hdom
      have hhalt : (C14H4Part3.prependBits (bitsOfCode c) B₀).IsHalting := (hiff c).mpr hdom
      exact C14H4Proof.not_provable_neg_halts_of_isHalting _ hhalt hprov
    · intro hndom
      have hnhalt : ¬ (C14H4Part3.prependBits (bitsOfCode c) B₀).IsHalting := mt (hiff c).mp hndom
      exact hall' (2 * (bitsOfCode c).length + k) (C14H4Part3.prependBits (bitsOfCode c) B₀) hnhalt
  exact ComputablePred.halting_problem_not_re 0 hre_nonhalt
