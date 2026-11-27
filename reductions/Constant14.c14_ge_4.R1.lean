import FormalConjectures.OptimizationConstants.«14»

namespace OMA.R_Constant14_c14_ge_4_R1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver

/-!
Reduction of `4 ≤ C14` to four statements. What `main` itself proves: soundness of the copied
one-sided LK calculus for Tarski semantics, and that `ZFSet` satisfies every axiom of the formalized
ZFC (both schemas included). So a sentence false in `ZFSet` is unprovable, which turns the
proof-theoretic half of the nonemptiness of the defining set into the purely semantic `H3`.
No helper definition is used: the truth predicate is obtained from an existence lemma (`exEv`).

* `H1`: a halting machine with at most 3 states is provably halting (Sigma-1 completeness).
* `H2`: a non-halting machine with at most 3 states is provably non-halting (Lin and Rado, inside ZFC).
* `H3`: in the standard model `ZFSet`, `halts M` is false for every non-halting machine. The truth
  predicate is given by its Tarski clauses, so the statement mentions no proof system.
* `H4`: some non-halting machine has a non-halting statement that ZFC cannot prove (Goedel).
-/

/-- Sigma-1 completeness for machines with at most 3 states. -/
def H1 : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)), n < 4 → M.IsHalting →
    FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M)

/-- ZFC refutes halting for every non-halting machine with at most 3 states. -/
def H2 : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)), n < 4 → ¬ M.IsHalting →
    FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)

/-- Faithfulness in the standard model: for any truth predicate `tr` on `ZFSet` obeying Tarski's
clauses, `halts M` is false whenever `M` does not halt. -/
def H3 : Prop :=
  ∀ tr : ∀ {m : ℕ}, (Fin m → ZFSet.{0}) → Semisentence ℒₛₑₜ m → Prop,
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}), tr e Semiformula.verum) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}), ¬ tr e Semiformula.falsum) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      (tr e (Semiformula.rel Language.Set.Rel.eq ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i = e j)) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      (tr e (Semiformula.rel Language.Set.Rel.mem ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i ∈ e j)) →
    (∀ {m k : ℕ} (e : Fin m → ZFSet.{0}) (r : Language.Set.Rel k) (v : Fin k → Semiterm ℒₛₑₜ Empty m),
      (tr e (Semiformula.nrel r v) ↔ ¬ tr e (Semiformula.rel r v))) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m),
      (tr e (Semiformula.and φ ψ) ↔ tr e φ ∧ tr e ψ)) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m),
      (tr e (Semiformula.or φ ψ) ↔ tr e φ ∨ tr e ψ)) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)),
      (tr e (Semiformula.all φ) ↔ ∀ d, tr (Matrix.vecCons d e) φ)) →
    (∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)),
      (tr e (Semiformula.exs φ) ↔ ∃ d, tr (Matrix.vecCons d e) φ)) →
    ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)), ¬ M.IsHalting →
      ¬ tr (Fin.elim0 : Fin 0 → ZFSet.{0}) (Constant14.halts M)

/-- Incompleteness: a non-halting machine whose non-halting is not provable in ZFC. -/
def H4 : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (M : Machine (Fin 2) (Fin n)),
    ¬ M.IsHalting ∧ ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)

/-- Term evaluation in `ZFSet` (there are no function symbols). -/
lemma exTv : ∃ tv : ∀ {ξ : Type} {n : ℕ}, (Fin n → ZFSet.{0}) → (ξ → ZFSet.{0}) →
      Semiterm ℒₛₑₜ ξ n → ZFSet.{0},
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (i : Fin n),
      tv e ε (Semiterm.bvar i) = e i) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (x : ξ),
      tv e ε (Semiterm.fvar x) = ε x) :=
  ⟨fun {ξ} {n} e ε t => match t with
      | Semiterm.bvar i => e i
      | Semiterm.fvar x => ε x
      | Semiterm.func f _ => (f : Empty).elim,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- A Tarski truth predicate for the structure `ZFSet`, for formulas with free variables in any
type `ξ : Type`. Obtained by recursion on formulas; used below through `exEv.choose`. -/
lemma exEv : ∃ ev : ∀ {ξ : Type} {n : ℕ}, (Fin n → ZFSet.{0}) → (ξ → ZFSet.{0}) →
      Semiformula ℒₛₑₜ ξ n → Prop,
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}),
      (ev e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}),
      (ev e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
        exTv.choose e ε (v 0) = exTv.choose e ε (v 1))) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
        exTv.choose e ε (v 0) ∈ exTv.choose e ε (v 1))) ∧
    (∀ {ξ : Type} {n k : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (r : (ℒₛₑₜ).Rel k)
      (v : Fin k → Semiterm ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.nrel r v) ↔ ¬ ev e ε (Semiformula.rel r v))) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.and φ ψ) ↔ ev e ε φ ∧ ev e ε ψ)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      (ev e ε (Semiformula.or φ ψ) ↔ ev e ε φ ∨ ev e ε ψ)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      (ev e ε (Semiformula.all φ) ↔ ∀ d, ev (Matrix.vecCons d e) ε φ)) ∧
    (∀ {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      (ev e ε (Semiformula.exs φ) ↔ ∃ d, ev (Matrix.vecCons d e) ε φ)) :=
  ⟨fun {ξ} {n} e ε φ =>
      @Semiformula.rec ℒₛₑₜ ξ (fun m _ => (Fin m → ZFSet.{0}) → Prop)
        (fun {m} _ => True)
        (fun {m} _ => False)
        (fun {m k} r v e' =>
          @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => exTv.choose e' ε (w 0) = exTv.choose e' ε (w 1))
            (fun w => exTv.choose e' ε (w 0) ∈ exTv.choose e' ε (w 1)) k r v)
        (fun {m k} r v e' =>
          ¬ @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => exTv.choose e' ε (w 0) = exTv.choose e' ε (w 1))
            (fun w => exTv.choose e' ε (w 0) ∈ exTv.choose e' ε (w 1)) k r v)
        (fun {m} _ _ ih1 ih2 e' => ih1 e' ∧ ih2 e')
        (fun {m} _ _ ih1 ih2 e' => ih1 e' ∨ ih2 e')
        (fun {m} _ ih e' => ∀ d, ih (Matrix.vecCons d e'))
        (fun {m} _ ih e' => ∃ d, ih (Matrix.vecCons d e'))
        n φ e,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl,
    fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

lemma tv_bvar {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (i : Fin n) :
    exTv.choose e ε (Semiterm.bvar i : Semiterm ℒₛₑₜ ξ n) = e i := exTv.choose_spec.1 e ε i

lemma tv_fvar {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (x : ξ) :
    exTv.choose e ε (Semiterm.fvar x : Semiterm ℒₛₑₜ ξ n) = ε x := exTv.choose_spec.2 e ε x

lemma ev_verum_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) :
    exEv.choose e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True := exEv.choose_spec.1 e ε

lemma ev_falsum_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) :
    exEv.choose e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False :=
  exEv.choose_spec.2.1 e ε

lemma ev_rel_eq_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
      exTv.choose e ε (v 0) = exTv.choose e ε (v 1) := exEv.choose_spec.2.2.1 e ε v

lemma ev_rel_mem_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
      exTv.choose e ε (v 0) ∈ exTv.choose e ε (v 1) := exEv.choose_spec.2.2.2.1 e ε v

lemma ev_nrel_c {ξ : Type} {n k : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.nrel r v) ↔ ¬ exEv.choose e ε (Semiformula.rel r v) :=
  exEv.choose_spec.2.2.2.2.1 e ε r v

lemma ev_and_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.and φ ψ) ↔ exEv.choose e ε φ ∧ exEv.choose e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.1 e ε φ ψ

lemma ev_or_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.or φ ψ) ↔ exEv.choose e ε φ ∨ exEv.choose e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.2.1 e ε φ ψ

lemma ev_all_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.all φ) ↔ ∀ d, exEv.choose (Matrix.vecCons d e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.1 e ε φ

lemma ev_exs_c {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.exs φ) ↔ ∃ d, exEv.choose (Matrix.vecCons d e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.2 e ε φ

lemma ev_congr {ξ : Type} {n : ℕ} {e e' : Fin n → ZFSet.{0}} {ε ε' : ξ → ZFSet.{0}}
    (φ : Semiformula ℒₛₑₜ ξ n) (h1 : e = e') (h2 : ε = ε') :
    exEv.choose e ε φ ↔ exEv.choose e' ε' φ := by
  subst h1 h2
  exact Iff.rfl

lemma ev_neg {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.neg φ) ↔ ¬ exEv.choose e ε φ := by
  induction φ with
  | verum => simp [Semiformula.neg, ev_verum_c, ev_falsum_c]
  | falsum => simp [Semiformula.neg, ev_verum_c, ev_falsum_c]
  | rel r v => simp [Semiformula.neg, ev_nrel_c]
  | nrel r v => simp [Semiformula.neg, ev_nrel_c]
  | and φ ψ ih1 ih2 => simp only [Semiformula.neg, ev_and_c, ev_or_c, ih1, ih2]; tauto
  | or φ ψ ih1 ih2 => simp only [Semiformula.neg, ev_and_c, ev_or_c, ih1, ih2]; tauto
  | all φ ih => simp only [Semiformula.neg, ev_all_c, ev_exs_c, ih]; exact not_forall.symm
  | exs φ ih => simp only [Semiformula.neg, ev_all_c, ev_exs_c, ih]; exact not_exists.symm

lemma tval_rew {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (e : Fin n₂ → ZFSet.{0}) (ε : ξ₂ → ZFSet.{0}) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    exTv.choose e ε (ω t) = exTv.choose (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) t := by
  cases t with
  | bvar i =>
    exact (tv_bvar (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) i).symm
  | fvar x =>
    exact (tv_fvar (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) x).symm
  | func f v => exact (f : Empty).elim

lemma tval_bShift {ξ : Type} {n : ℕ} (d : ZFSet.{0}) (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (t : Semiterm ℒₛₑₜ ξ n) :
    exTv.choose (Matrix.vecCons d e) ε (Rew.bShift t) = exTv.choose e ε t := by
  cases t with
  | bvar i =>
    exact (tv_bvar (Matrix.vecCons d e) ε (Fin.succ i)).trans
      ((Matrix.cons_val_succ d e i).trans (tv_bvar e ε i).symm)
  | fvar x => exact (tv_fvar (Matrix.vecCons d e) ε x).trans (tv_fvar e ε x).symm
  | func f v => exact (f : Empty).elim

lemma tval_q {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (d : ZFSet.{0}) (e : Fin n₂ → ZFSet.{0}) (ε : ξ₂ → ZFSet.{0}) :
    (fun i => exTv.choose (Matrix.vecCons d e) ε (ω.q (Semiterm.bvar i))) =
      Matrix.vecCons d (fun i => exTv.choose e ε (ω (Semiterm.bvar i))) ∧
    (fun x => exTv.choose (Matrix.vecCons d e) ε (ω.q (Semiterm.fvar x))) =
      (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) := by
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (tv_bvar (Matrix.vecCons d e) ε 0).trans (Matrix.cons_val_zero d e)
    · exact tval_bShift d e ε (ω (Semiterm.bvar j))
  · funext x
    exact tval_bShift d e ε (ω (Semiterm.fvar x))

lemma ev_rel_congr {ξ₁ ξ₂ : Type} {n₁ n₂ k : ℕ} (r : (ℒₛₑₜ).Rel k)
    (e₁ : Fin n₁ → ZFSet.{0}) (ε₁ : ξ₁ → ZFSet.{0}) (e₂ : Fin n₂ → ZFSet.{0}) (ε₂ : ξ₂ → ZFSet.{0})
    (v₁ : Fin k → Semiterm ℒₛₑₜ ξ₁ n₁) (v₂ : Fin k → Semiterm ℒₛₑₜ ξ₂ n₂)
    (h : ∀ i, exTv.choose e₁ ε₁ (v₁ i) = exTv.choose e₂ ε₂ (v₂ i)) :
    exEv.choose e₁ ε₁ (Semiformula.rel r v₁) ↔ exEv.choose e₂ ε₂ (Semiformula.rel r v₂) := by
  cases r with
  | eq => rw [ev_rel_eq_c, ev_rel_eq_c, h 0, h 1]
  | mem => rw [ev_rel_mem_c, ev_rel_mem_c, h 0, h 1]

lemma ev_rew {ξ₁ ξ₂ : Type} {n₁ : ℕ} (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ∀ {n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (e : Fin n₂ → ZFSet.{0}) (ε : ξ₂ → ZFSet.{0}),
    exEv.choose e ε (Semiformula.rewAux ω φ) ↔
      exEv.choose (fun i => exTv.choose e ε (ω (Semiterm.bvar i)))
        (fun x => exTv.choose e ε (ω (Semiterm.fvar x))) φ := by
  induction φ with
  | verum =>
    intro n₂ ω e ε
    show exEv.choose e ε Semiformula.verum ↔ _
    rw [ev_verum_c, ev_verum_c]
  | falsum =>
    intro n₂ ω e ε
    show exEv.choose e ε Semiformula.falsum ↔ _
    rw [ev_falsum_c, ev_falsum_c]
  | rel r v =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.rel r (fun i => ω (v i))) ↔ _
    exact ev_rel_congr r _ _ _ _ _ _ (fun i => tval_rew ω e ε (v i))
  | nrel r v =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.nrel r (fun i => ω (v i))) ↔ _
    rw [ev_nrel_c, ev_nrel_c]
    exact not_congr (ev_rel_congr r _ _ _ _ _ _ (fun i => tval_rew ω e ε (v i)))
  | and φ ψ ih1 ih2 =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.and (Semiformula.rewAux ω φ) (Semiformula.rewAux ω ψ)) ↔ _
    rw [ev_and_c, ev_and_c]
    exact and_congr (ih1 ω e ε) (ih2 ω e ε)
  | or φ ψ ih1 ih2 =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.or (Semiformula.rewAux ω φ) (Semiformula.rewAux ω ψ)) ↔ _
    rw [ev_or_c, ev_or_c]
    exact or_congr (ih1 ω e ε) (ih2 ω e ε)
  | all φ ih =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.all (Semiformula.rewAux ω.q φ)) ↔ _
    rw [ev_all_c, ev_all_c]
    refine forall_congr' fun d => ?_
    exact (ih ω.q (Matrix.vecCons d e) ε).trans (ev_congr φ (tval_q ω d e ε).1 (tval_q ω d e ε).2)
  | exs φ ih =>
    intro n₂ ω e ε
    show exEv.choose e ε (Semiformula.exs (Semiformula.rewAux ω.q φ)) ↔ _
    rw [ev_exs_c, ev_exs_c]
    refine exists_congr fun d => ?_
    exact (ih ω.q (Matrix.vecCons d e) ε).trans (ev_congr φ (tval_q ω d e ε).1 (tval_q ω d e ε).2)

lemma mem_atom {α : Type*} {a x : α} : x ∈ Multiset.atom a ↔ x = a := Multiset.mem_singleton

lemma ev_e0 {ξ : Type} (e e' : Fin 0 → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ 0) :
    exEv.choose e ε φ ↔ exEv.choose e' ε φ := by
  rw [Subsingleton.elim e e']

lemma ev_shift {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0})
    (φ : Semiproposition ℒₛₑₜ n) :
    exEv.choose e ε (Rewriting.shift φ) ↔ exEv.choose e (fun k => ε (k + 1)) φ := by
  show exEv.choose e ε (Semiformula.rewAux Rew.shift φ) ↔ _
  exact (ev_rew φ Rew.shift e ε).trans
    (ev_congr φ (funext fun i => tv_bvar e ε i) (funext fun x => tv_fvar e ε (x + 1)))

lemma ev_free (e : Fin 0 → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (φ : Semiproposition ℒₛₑₜ (0 + 1)) :
    exEv.choose e ε (Rewriting.free φ) ↔
      exEv.choose (Matrix.vecCons (ε 0) e) (fun k => ε (k + 1)) φ := by
  show exEv.choose e ε (Semiformula.rewAux Rew.free φ) ↔ _
  refine (ev_rew φ Rew.free e ε).trans (ev_congr φ ?_ (funext fun x => tv_fvar e ε (x + 1)))
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  exact tv_fvar e ε 0

lemma ev_subst_gen {ξ : Type} {n m : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ m) (v : Fin m → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⇜ v) ↔ exEv.choose (fun i => exTv.choose e ε (v i)) ε φ := by
  show exEv.choose e ε (Semiformula.rewAux (Rew.subst v) φ) ↔ _
  exact (ev_rew φ (Rew.subst v) e ε).trans (ev_congr φ rfl (funext fun x => tv_fvar e ε x))

lemma ev_subst1 (e : Fin 0 → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (φ : Semiproposition ℒₛₑₜ (0 + 1))
    (t : Semiterm ℒₛₑₜ ℕ 0) :
    exEv.choose e ε (φ ⇜ ![t]) ↔ exEv.choose (Matrix.vecCons (exTv.choose e ε t) e) ε φ := by
  refine (ev_subst_gen e ε φ ![t]).trans (ev_congr φ ?_ rfl)
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

/-- Soundness of the one-sided LK calculus for `ZFSet`. -/
theorem sound {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) :
    ∀ ε : ℕ → ZFSet.{0}, ∃ φ ∈ Γ, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε φ := by
  induction d with
  | identity r v =>
    intro ε
    by_cases h : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε (Semiformula.rel r v)
    · exact ⟨_, Multiset.mem_add.2 (Or.inl (mem_atom.2 rfl)), h⟩
    · exact ⟨Semiformula.nrel r v, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)),
        (ev_nrel_c _ _ r v).2 h⟩
  | cut d1 d2 ih1 ih2 =>
    rename_i Γ φ Δ
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.1 h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.2 (Or.inl h1), e1⟩
    rcases Multiset.mem_add.1 h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.2 (Or.inr h2), e2⟩
    rw [mem_atom] at h1 h2
    subst h1 h2
    exact absurd e1 ((ev_neg _ _ _).1 e2)
  | contraction d hsub ih =>
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    exact ⟨χ, hsub h, e⟩
  | verum =>
    intro ε
    exact ⟨_, mem_atom.2 rfl, (ev_verum_c _ _).2 trivial⟩
  | or d ih =>
    rename_i Γ φ ψ
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.1 h with h | h
    · exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    · refine ⟨φ ⋎ ψ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ?_⟩
      rcases Multiset.mem_add.1 h with h | h
      · rw [mem_atom] at h; subst h; exact (ev_or_c _ _ _ _).2 (Or.inl e)
      · rw [mem_atom] at h; subst h; exact (ev_or_c _ _ _ _).2 (Or.inr e)
  | and d1 d2 ih1 ih2 =>
    rename_i Γ φ ψ
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.1 h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.2 (Or.inl h1), e1⟩
    rcases Multiset.mem_add.1 h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.2 (Or.inl h2), e2⟩
    rw [mem_atom] at h1 h2
    subst h1 h2
    exact ⟨_, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), (ev_and_c _ _ _ _).2 ⟨e1, e2⟩⟩
  | all d ih =>
    rename_i Γ φ
    intro ε
    by_cases hΓ : ∃ χ ∈ Γ, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε χ
    · obtain ⟨χ, h, e⟩ := hΓ
      exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    refine ⟨∀¹ φ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ?_⟩
    refine (ev_all_c _ _ _).2 ?_
    intro x
    let ε' : ℕ → ZFSet.{0} := fun k => Nat.casesOn k x ε
    obtain ⟨χ, h, e⟩ := ih ε'
    rcases Multiset.mem_add.1 h with h | h
    · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.1 h
      exact absurd ⟨ψ, hψ, (ev_shift _ ε' ψ).1 e⟩ hΓ
    · rw [mem_atom] at h
      subst h
      exact (ev_free _ ε' φ).1 e
  | exs d ih =>
    rename_i Γ φ t
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.1 h with h | h
    · exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    · rw [mem_atom] at h
      subst h
      exact ⟨∃¹ φ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)),
        (ev_exs_c _ _ _).2 ⟨exTv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε t,
          (ev_subst1 _ ε φ t).1 e⟩⟩

lemma ev_emb {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (σ : Semisentence ℒₛₑₜ n) :
    exEv.choose e ε (Rewriting.emb σ : Semiproposition ℒₛₑₜ n) ↔
      exEv.choose e (Empty.elim : Empty → ZFSet.{0}) σ := by
  show exEv.choose e ε (Semiformula.rewAux Rew.emb σ) ↔ _
  exact (ev_rew σ Rew.emb e ε).trans
    (ev_congr σ (funext fun i => tv_bvar e ε i) (funext fun x => x.elim))

theorem sound_theory {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hT : ∀ ψ ∈ T, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) ψ)
    (h : FFL.Entailment.Provable T σ) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) σ := by
  obtain ⟨pf⟩ := h
  have hv := sound pf.derivation (fun _ => (∅ : ZFSet.{0}))
  obtain ⟨χ, hχ, he⟩ := hv
  obtain ⟨χ0, h0, rfl⟩ := Multiset.mem_map.1 hχ
  rw [ev_emb] at he
  rcases Multiset.mem_add.1 h0 with h0 | h0
  · rw [mem_atom] at h0
    subst h0
    exact (ev_e0 _ _ _ _).1 he
  · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.1 h0
    have := (ev_neg _ _ ψ).1 he
    exact absurd ((ev_e0 _ _ _ _).1 (hT ψ (pf.axioms_mem ψ hψ))) this

lemma ev_eq {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔
      exTv.choose e ε t = exTv.choose e ε u := by
  show exEv.choose e ε (Semiformula.rel Language.Set.Rel.eq
    (fun i => (Rew.subst ![t, u]) ((Rew.emb : Rew ℒₛₑₜ Empty 2 ξ 2) (Semiterm.bvar i)))) ↔ _
  rw [ev_rel_eq_c]
  exact Iff.rfl

lemma ev_mem {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})
    (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔
      exTv.choose e ε t ∈ exTv.choose e ε u := by
  show exEv.choose e ε (Semiformula.rel Language.Set.Rel.mem
    (fun i => (Rew.subst ![t, u]) ((Rew.emb : Rew ℒₛₑₜ Empty 2 ξ 2) (Semiterm.bvar i)))) ↔ _
  rw [ev_rel_mem_c]
  exact Iff.rfl

section simpset
variable {ξ : Type} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})

@[simp] lemma tval_bvar (i : Fin n) :
    exTv.choose e ε (Semiterm.bvar i : Semiterm ℒₛₑₜ ξ n) = e i := tv_bvar e ε i
@[simp] lemma tval_fvar (x : ξ) :
    exTv.choose e ε (Semiterm.fvar x : Semiterm ℒₛₑₜ ξ n) = ε x := tv_fvar e ε x
@[simp] lemma ev_and' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⋏ ψ) ↔ exEv.choose e ε φ ∧ exEv.choose e ε ψ := ev_and_c e ε φ ψ
@[simp] lemma ev_or' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⋎ ψ) ↔ exEv.choose e ε φ ∨ exEv.choose e ε ψ := ev_or_c e ε φ ψ
@[simp] lemma ev_not' (φ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (∼φ) ↔ ¬ exEv.choose e ε φ := ev_neg e ε φ
@[simp] lemma ev_imp' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ 🡒 ψ) ↔ (exEv.choose e ε φ → exEv.choose e ε ψ) := by
  show exEv.choose e ε (Semiformula.or (Semiformula.neg φ) ψ) ↔ _
  rw [ev_or_c, ev_neg]; tauto
@[simp] lemma ev_iff' (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ 🡘 ψ) ↔ (exEv.choose e ε φ ↔ exEv.choose e ε ψ) := by
  show exEv.choose e ε ((φ 🡒 ψ) ⋏ (ψ 🡒 φ)) ↔ _
  rw [ev_and', ev_imp', ev_imp']; tauto
@[simp] lemma ev_all' (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (∀¹ φ) ↔ ∀ d, exEv.choose (Matrix.vecCons d e) ε φ := ev_all_c e ε φ
@[simp] lemma ev_exs' (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (∃¹ φ) ↔ ∃ d, exEv.choose (Matrix.vecCons d e) ε φ := ev_exs_c e ε φ
@[simp] lemma ev_top' : exEv.choose e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True := ev_verum_c e ε
@[simp] lemma ev_subst' {m : ℕ} (φ : Semiformula ℒₛₑₜ ξ m) (v : Fin m → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (φ ⇜ v) ↔ exEv.choose (fun i => exTv.choose e ε (v i)) ε φ :=
  ev_subst_gen e ε φ v
@[simp] lemma ev_eq' (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔
      exTv.choose e ε t = exTv.choose e ε u :=
  ev_eq e ε t u
@[simp] lemma ev_mem' (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔
      exTv.choose e ε t ∈ exTv.choose e ε u :=
  ev_mem e ε t u
@[simp] lemma ev_ballMem (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.ballMem t φ) ↔
      ∀ d ∈ exTv.choose e ε t, exEv.choose (Matrix.vecCons d e) ε φ := by
  show exEv.choose e ε (∀¹ _) ↔ _
  rw [ev_all']
  refine forall_congr' fun d => ?_
  rw [ev_imp', ev_mem']
  simp [tval_bShift]
@[simp] lemma ev_bexsMem (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose e ε (Semiformula.bexsMem t φ) ↔
      ∃ d ∈ exTv.choose e ε t, exEv.choose (Matrix.vecCons d e) ε φ := by
  show exEv.choose e ε (∃¹ _) ↔ _
  rw [ev_exs']
  refine exists_congr fun d => ?_
  show exEv.choose _ ε (Semiformula.and _ _) ↔ _
  rw [ev_and_c, ev_mem']
  simp [tval_bShift]
@[simp] lemma ev_rel_eq (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
      exTv.choose e ε (v 0) = exTv.choose e ε (v 1) := ev_rel_eq_c e ε v
@[simp] lemma ev_rel_mem (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
      exTv.choose e ε (v 0) ∈ exTv.choose e ε (v 1) := ev_rel_mem_c e ε v
end simpset

lemma sat_empty : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.empty := by
  unfold Axiom.empty
  simp
  exact ⟨∅, fun y => ZFSet.notMem_empty y⟩

lemma sat_ext : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.extentionality := by
  unfold Axiom.extentionality
  simp
  intro x y
  exact ⟨fun h => by simp [h], fun h => ZFSet.ext fun z => h z⟩

lemma sat_pairing : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.pairing := by
  unfold Axiom.pairing
  simp
  intro x y
  exact ⟨{y, x}, fun w => by simp [or_comm]⟩

lemma sat_union : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.union := by
  unfold Axiom.union
  simp
  intro x
  exact ⟨ZFSet.sUnion x, fun z => by simp⟩

lemma sat_power : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.power := by
  unfold Axiom.power
  simp [isSubsetOf]
  intro x
  refine ⟨ZFSet.powerset x, fun z => ?_⟩
  rw [ZFSet.mem_powerset]
  exact ⟨fun h w hw => h hw, fun h w hw => h w hw⟩

lemma sat_infinity : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.infinity := by
  unfold Axiom.infinity
  simp [isEmpty, isSucc]
  refine ⟨ZFSet.omega, fun e he => ?_, fun x hx x' hx' => ?_⟩
  · have : e = ∅ := ZFSet.eq_empty e |>.2 he
    subst this
    exact ZFSet.omega_zero
  · have : x' = insert x x := ZFSet.ext fun z => by rw [hx' z, ZFSet.mem_insert_iff]
    subst this
    exact ZFSet.omega_succ hx

lemma sat_foundation : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
    (Empty.elim : Empty → ZFSet.{0}) Axiom.foundation := by
  unfold Axiom.foundation
  simp [isNonempty]
  intro x y hy
  have hne : x ≠ ∅ := fun h => by rw [h] at hy; exact ZFSet.notMem_empty y hy
  obtain ⟨w, hw, hint⟩ := ZFSet.regularity x hne
  refine ⟨w, hw, fun z hz hzw => ?_⟩
  have : z ∈ x ∩ w := ZFSet.mem_inter.2 ⟨hz, hzw⟩
  rw [hint] at this
  exact ZFSet.notMem_empty z this

lemma sat_eq_refl : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    (Theory.Eq.refl ℒₛₑₜ) := by
  unfold Theory.Eq.refl
  simp

lemma sat_eq_symm : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    (Theory.Eq.symm ℒₛₑₜ) := by
  unfold Theory.Eq.symm
  simp

lemma sat_eq_trans : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    (Theory.Eq.trans ℒₛₑₜ) := by
  unfold Theory.Eq.trans
  simp

lemma sat_funcExt {k : ℕ} (f : (ℒₛₑₜ).Func k) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Theory.Eq.funcExt f) := (f : Empty).elim

lemma sat_relExt_eq : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    (Theory.Eq.relExt (L := ℒₛₑₜ) Language.Set.Rel.eq) := by
  unfold Theory.Eq.relExt
  simp [allClosure, Matrix.conj, Matrix.vecTail, Fin.addCast, Fin.addNat, Fin.castLE]

lemma sat_relExt_mem : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    (Theory.Eq.relExt (L := ℒₛₑₜ) Language.Set.Rel.mem) := by
  unfold Theory.Eq.relExt
  simp [allClosure, Matrix.conj, Matrix.vecTail, Fin.addCast, Fin.addNat, Fin.castLE]

lemma sat_eqAxiom : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ,
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) φ := by
  intro φ h
  cases h with
  | refl => exact sat_eq_refl
  | symm => exact sat_eq_symm
  | trans => exact sat_eq_trans
  | funcExt f => exact sat_funcExt f
  | relExt r =>
    cases r with
    | eq => exact sat_relExt_eq
    | mem => exact sat_relExt_mem

lemma sat_choice : exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
    Axiom.choice := by
  unfold Axiom.choice
  simp [isNonempty, Semiformula.existsUnique]
  intro 𝓧 hne hdis
  refine ⟨ZFSet.sep (fun x => ∃ X ∈ 𝓧, x = Classical.epsilon (fun y => y ∈ X)) (ZFSet.sUnion 𝓧),
    fun X hX => ?_⟩
  have hchX : Classical.epsilon (fun y => y ∈ X) ∈ X := Classical.epsilon_spec (hne X hX)
  refine ⟨Classical.epsilon (fun y => y ∈ X),
    ⟨ZFSet.mem_sep.2 ⟨ZFSet.mem_sUnion.2 ⟨X, hX, hchX⟩, X, hX, rfl⟩, hchX⟩, ?_⟩
  intro z hzC hzX
  obtain ⟨_, X', hX', rfl⟩ := ZFSet.mem_sep.1 hzC
  have hX'mem : Classical.epsilon (fun y => y ∈ X') ∈ X' := Classical.epsilon_spec (hne X' hX')
  have := hdis X hX X' hX' (Classical.epsilon (fun y => y ∈ X')) hzX hX'mem
  subst this
  rfl

lemma tval_toEmpty {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0}) (ε0 : Empty → ZFSet.{0})
    (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    exTv.choose e ε0 (t.toEmpty h) = exTv.choose e ε t := by
  cases t with
  | bvar i => exact (tv_bvar e ε0 i).trans (tv_bvar e ε i).symm
  | fvar x => exact absurd h (by simp [Semiterm.freeVariables])
  | func f v => exact (f : Empty).elim

lemma ev_toEmpty {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    ∀ (h : φ.freeVariables = ∅) (e : Fin n → ZFSet.{0}) (ε : ℕ → ZFSet.{0})
      (ε0 : Empty → ZFSet.{0}),
    exEv.choose e ε0 (φ.toEmpty h) ↔ exEv.choose e ε φ := by
  induction φ with
  | verum =>
    intro h e ε ε0
    show exEv.choose e ε0 Semiformula.verum ↔ _
    rw [ev_verum_c, ev_verum_c]
  | falsum =>
    intro h e ε ε0
    show exEv.choose e ε0 Semiformula.falsum ↔ _
    rw [ev_falsum_c, ev_falsum_c]
  | rel r v =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.rel r _) ↔ _
    exact ev_rel_congr r _ _ _ _ _ _ (fun i => tval_toEmpty e ε ε0 (v i) _)
  | nrel r v =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.nrel r _) ↔ _
    rw [ev_nrel_c, ev_nrel_c]
    exact not_congr (ev_rel_congr r _ _ _ _ _ _ (fun i => tval_toEmpty e ε ε0 (v i) _))
  | and φ ψ ih1 ih2 =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.and (φ.toEmpty _) (ψ.toEmpty _)) ↔ _
    rw [ev_and_c, ev_and_c]
    exact and_congr (ih1 _ e ε ε0) (ih2 _ e ε ε0)
  | or φ ψ ih1 ih2 =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.or (φ.toEmpty _) (ψ.toEmpty _)) ↔ _
    rw [ev_or_c, ev_or_c]
    exact or_congr (ih1 _ e ε ε0) (ih2 _ e ε ε0)
  | all φ ih =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.all (φ.toEmpty _)) ↔ _
    rw [ev_all_c, ev_all_c]
    exact forall_congr' fun d => ih h _ ε ε0
  | exs φ ih =>
    intro h e ε ε0
    show exEv.choose e ε0 (Semiformula.exs (φ.toEmpty _)) ↔ _
    rw [ev_exs_c, ev_exs_c]
    exact exists_congr fun d => ih h _ ε ε0

lemma ev_allClosure : ∀ {m : ℕ} (ψ : Semiformula ℒₛₑₜ ℕ m) (ε : ℕ → ZFSet.{0}),
    (∀ w : Fin m → ZFSet.{0}, exEv.choose w ε ψ) →
      exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε (∀¹* ψ)
  | 0, ψ, ε, h => h _
  | m + 1, ψ, ε, h => ev_allClosure (m := m) (∀¹ ψ) ε
      (fun w => (ev_all_c w ε ψ).2 fun d => h (Matrix.vecCons d w))

lemma fixitr_fvar (n m x : ℕ) :
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

lemma ev_fixitr (m : ℕ) (φ : Semiproposition ℒₛₑₜ 0) (w : Fin (0 + m) → ZFSet.{0})
    (ε : ℕ → ZFSet.{0}) :
    exEv.choose w ε (Rew.fixitr 0 m ▹ φ) ↔
      exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0})
        (fun x => if h : x < m then w ⟨x, by omega⟩ else ε (x - m)) φ := by
  show exEv.choose w ε (Semiformula.rewAux (Rew.fixitr 0 m) φ) ↔ _
  have h1 : (fun x => exTv.choose w ε
      (Rew.fixitr 0 m (Semiterm.fvar x) : Semiterm ℒₛₑₜ ℕ (0 + m))) =
      (fun x => if h : x < m then w ⟨x, by omega⟩ else ε (x - m)) := by
    funext x
    rw [fixitr_fvar]
    by_cases hx : x < m
    · simp only [dif_pos hx, tv_bvar]
      congr 1
      exact Fin.ext (by simp)
    · simp only [dif_neg hx, tv_fvar]
  exact (ev_rew φ (Rew.fixitr 0 m) w ε).trans (ev_congr φ (Subsingleton.elim _ _) h1)

lemma sat_univCl (φ : Proposition ℒₛₑₜ)
    (h : ∀ ε : ℕ → ZFSet.{0}, exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) ε φ) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Semiformula.univCl φ) := by
  unfold Semiformula.univCl
  rw [ev_toEmpty _ _ _ (fun _ => (∅ : ZFSet.{0}))]
  unfold Semiformula.univCl'
  apply ev_allClosure
  intro w
  rw [ev_fixitr]
  exact h _

lemma sat_sep (φ : SetTheorySemiproposition 1) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Axiom.separationSchema φ) := by
  unfold Axiom.separationSchema
  apply sat_univCl
  intro ε
  simp
  exact fun x => ⟨_, fun z => ZFSet.mem_sep⟩

lemma sat_rep (φ : SetTheorySemiproposition 2) :
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0})
      (Axiom.replacementSchema φ) := by
  unfold Axiom.replacementSchema
  apply sat_univCl
  intro ε
  have key : ∀ (a b : ZFSet.{0}) (f : Fin 2 → ZFSet.{0}), f 0 = a → f 1 = b →
      (exEv.choose f ε φ ↔ exEv.choose ![a, b] ε φ) := by
    intro a b f h0 h1
    have : f = ![a, b] := by
      funext i; refine Fin.cases h0 (fun j => ?_) i
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj; exact h1
    rw [this]
  simp only [ev_imp', ev_all', ev_exs', ev_iff', ev_bexsMem, ev_mem', ev_subst', tval_bvar,
    Semiformula.existsUnique, ev_and', ev_eq']
  intro hfun X
  have hfun' : ∀ x, ∃ y, exEv.choose ![x, y] ε φ ∧ ∀ z, exEv.choose ![x, z] ε φ → z = y := by
    intro x
    obtain ⟨y, hy, huniq⟩ := hfun x
    exact ⟨y, (key x y _ (by simp) (by simp)).1 hy,
      fun z hz => huniq z ((key x z _ (by simp) (by simp)).2 hz)⟩
  let F : ZFSet.{0} → ZFSet.{0} := fun x => Classical.choose (hfun' x)
  let _ : ZFSet.Definable₁ F := Classical.allZFSetDefinable _
  refine ⟨ZFSet.image F X, fun y => ?_⟩
  show y ∈ ZFSet.image F X ↔ ∃ d ∈ X, _
  rw [ZFSet.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (key x (F x) _ (by simp) (by simp)).2 (Classical.choose_spec (hfun' x)).1⟩
  · rintro ⟨x, hx, hP⟩
    refine ⟨x, hx, ?_⟩
    exact ((Classical.choose_spec (hfun' x)).2 y ((key x y _ (by simp) (by simp)).1 hP)).symm

/-- `ZFSet` satisfies every axiom of the formalized ZFC. -/
theorem zfsetModel : ∀ ψ ∈ 𝗭𝗙𝗖,
    exEv.choose (Fin.elim0 : Fin 0 → ZFSet.{0}) (Empty.elim : Empty → ZFSet.{0}) ψ := by
  intro ψ h
  rcases h with h | h
  · cases h with
    | axiom_of_equality _ hφ => exact sat_eqAxiom _ hφ
    | axiom_of_empty_set => exact sat_empty
    | axiom_of_extentionality => exact sat_ext
    | axiom_of_pairing => exact sat_pairing
    | axiom_of_union => exact sat_union
    | axiom_of_power_set => exact sat_power
    | axiom_of_infinity => exact sat_infinity
    | axiom_of_foundation => exact sat_foundation
    | axiom_of_separation φ => exact sat_sep φ
    | axiom_of_replacement φ => exact sat_rep φ
  · have h' : ψ = Axiom.choice := h
    subst h'
    exact sat_choice

theorem main : H1 → H2 → H3 → H4 → type_of% @Constant14.c14_ge_4 := by
  intro h1 h2 h3 h4
  have hsound : ∀ (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)), ¬ M.IsHalting →
      ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M) := by
    intro n _ M hM hprov
    have hsat := sound_theory zfsetModel hprov
    refine h3 (fun {m} e φ => exEv.choose e (Empty.elim : Empty → ZFSet.{0}) φ)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ n M hM hsat
    · intro m e
      exact (ev_verum_c e _).2 trivial
    · intro m e h
      exact (ev_falsum_c e _).1 h
    · intro m e i j
      rw [ev_rel_eq_c]
      simp [tv_bvar]
    · intro m e i j
      rw [ev_rel_mem_c]
      simp [tv_bvar]
    · intro m k e r v
      exact ev_nrel_c e _ r v
    · intro m e φ ψ
      exact ev_and_c e _ φ ψ
    · intro m e φ ψ
      exact ev_or_c e _ φ ψ
    · intro m e φ
      exact ev_all_c e _ φ
    · intro m e φ
      exact ev_exs_c e _ φ
  show 4 ≤ sInf {n | ∃ _ : NeZero n, ∃ M : Machine (Fin 2) (Fin n),
    𝗭𝗙𝗖 ⊬ Constant14.halts M ∧ 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M}
  apply le_csInf
  · obtain ⟨n, hn, M, hnh, hnp⟩ := h4
    exact ⟨n, hn, M, hsound n M hnh, hnp⟩
  · rintro n ⟨hn, M, hu1, hu2⟩
    by_contra hlt
    have hlt' : n < 4 := lt_of_not_ge hlt
    by_cases hh : M.IsHalting
    · exact hu1 (h1 n M hlt' hh)
    · exact hu2 (h2 n M hlt' hh)

end OMA.R_Constant14_c14_ge_4_R1
