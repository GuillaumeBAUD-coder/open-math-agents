import OMAReductions.R_Constant14_c14_le_432_R1_H1_R1
import Mathlib.Tactic

/-!
# Reduction `Constant14.c14_le_432.R1.H1.R1.H1.R1`

Reduces `OMA.R_Constant14_c14_le_432_R1_H1_R1.H1` (inner-model existence of Gödel's constructible
universe `L`: every normal model `(V, mem) ⊨ 𝗭𝗙` contains a transitive subclass `P : V → Prop`
whose restriction `({x // P x}, mem|_P)` satisfies `𝗭𝗙𝗖`) to two orthogonal, purely set-theoretic
pillars:

* `H1`: **Existence of a definable cumulative `Def`-closed well-ordered hierarchy** (Gödel's
  constructible hierarchy `L_α` and canonical stage well-orderings `<_α ∈ L`): in every normal
  model `(V, mem) ⊨ 𝗭𝗙`, there is a 1-ary `ℒₛₑₜ`-formula `φS` defining a class `S` of transitive
  sets linearly ordered by `∈`, closed under arbitrary set unions, covering every set `A ⊆ P`
  (where `P x ↔ ∃ X, S X ∧ mem x X`), closed under first-order definability (`Def(X)`), and
  carrying a strict well-ordering `R ∈ P` on each stage `X ∈ S`.
* `H2`: **Lévy–Montague Reflection Principle** for any definable continuous `∈`-linear transitive
  hierarchy `φS` in `(V, mem) ⊨ 𝗭𝗙`: for every `k`-ary `ℒₛₑₜ`-formula `ψ` and starting stage `X₀`,
  there is a stage `Y ⊇ X₀` reflecting `ψ` between `(Y, ∈)` and `(P, ∈)`.

Inside `main` (with zero extra definitions), we unconditionally prove ALL 10 axioms of `𝗭𝗙𝗖` in
`({x // P x}, mem|_P)` from `H1` and `H2`:
1. Equality (`𝗘𝗤`), Extensionality, and Foundation from normality and transitivity of `P`.
2. Empty, stage-membership (`S X → P X`), Pairing, and Union from `H1`'s upward-covering and
   `Def`-closure.
3. Full **Separation Schema** (`Axiom.separationSchema`) from `H2` (Lévy–Montague Reflection) +
   `H1` (`Def`-closure) + syntactic free-variable closure (`Rew.bind`).
4. **Infinity** (`Axiom.infinity`) via the `Δ₀` finite-ordinal predicate `isFinOrd`, `ω^V`-induction
   and Foundation in `V`, upward-covering, and `Def`-closure (showing `ω^V ∈ P`).
5. **Power Set** (`Axiom.power`) via `V`-Power-Set, `V`-Separation with `φP`, upward-covering, and
   `Def`-closure.
6. Full **Replacement Schema** (`Axiom.replacementSchema`) via syntactic relativization to `φP`,
   `V`-Replacement, upward-covering, and `L`-Separation.
7. **Axiom of Choice** (`Axiom.choice`) via absoluteness of Kuratowski pairs (`kpair.dfn`) between
   `L` and `V`, `L`-Union, stage well-ordering `R ∈ P` from `H1`, and `L`-Separation.

Credits: Built by `@Narden91`, reusing the zero-definition Tarski evaluation combinators from
`Constant14.c14_le_432.R1.H1.R1`.
-/

namespace OMA.R_Constant14_c14_le_432_R1_H1_R1_H1_R1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped Classical

/-- Existence of a `𝗭𝗙`-definable cumulative, continuous, `∈`-linear, transitive, `Def`-closed,
well-ordered hierarchy (`L_α` and `<_α ∈ L`) inside every normal model `(V, mem) ⊨ 𝗭𝗙`. -/
def H1 : Prop :=
  let ev (V : Type) (mem : V → V → Prop) {m : ℕ} (e : Fin m → V)
      (φ : SetTheorySemisentence m) : Prop :=
    let tv {n : ℕ} (e : Fin n → V) : Semiterm ℒₛₑₜ Empty n → V :=
      @Semiterm.rec ℒₛₑₜ Empty n (fun _ => V) e Empty.elim (fun {_} f _ _ => f.elim)
    @Semiformula.rec ℒₛₑₜ Empty (fun n _ => (Fin n → V) → Prop)
      (fun _ => True) (fun _ => False)
      (fun r v e => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun r v e => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun _ _ a b e => a e ∧ b e) (fun _ _ a b e => a e ∨ b e)
      (fun _ a e => ∀ d, a (d :> e)) (fun _ a e => ∃ d, a (d :> e)) m φ e
  ∀ (V : Type) (mem : V → V → Prop), (∀ ψ ∈ 𝗭𝗙, ev V mem Fin.elim0 ψ) →
    ∃ φS : SetTheorySemisentence 1,
      let S (X : V) : Prop := ev V mem ![X] φS
      let P (x : V) : Prop := ∃ X, S X ∧ mem x X
      (∀ X, S X → ∀ u v, mem v X → mem u v → mem u X) ∧
      (∀ X Y, S X → S Y → X = Y ∨ mem X Y ∨ mem Y X) ∧
      (∀ C, (∀ X, mem X C → S X) → ∃ U, S U ∧ ∀ z, mem z U ↔ ∃ X, mem X C ∧ mem z X) ∧
      (∀ A, (∀ a, mem a A → P a) → ∃ X, S X ∧ ∀ a, mem a A → mem a X) ∧
      (∀ X, S X → ∀ (k : ℕ) (ψ : SetTheorySemisentence (k + 1)) (p : Fin k → {x // mem x X}),
        ∃ Y, S Y ∧ ∃ Z, mem Z Y ∧ ∀ u, mem u Z ↔
          ∃ hu : mem u X, ev {x // mem x X} (fun a b => mem a.1 b.1) (⟨u, hu⟩ :> p) ψ) ∧
      (∀ X, S X → ∃ R, P R ∧
        (∀ a b, mem a X → mem b X →
          ¬ ((∃ q, mem q R ∧ ev V mem ![q, a, b] kpair.dfn) ∧
             (∃ q, mem q R ∧ ev V mem ![q, b, a] kpair.dfn))) ∧
        ∀ W, (∀ w, mem w W → mem w X) → (∃ w, mem w W) →
          ∃ m, mem m W ∧ ∀ y, mem y W → y ≠ m → ∃ q, mem q R ∧ ev V mem ![q, m, y] kpair.dfn)

/-- Lévy–Montague Reflection Principle for any `𝗭𝗙`-definable continuous `∈`-linear transitive
hierarchy `φS` in a normal model `(V, mem) ⊨ 𝗭𝗙`. -/
def H2 : Prop :=
  let ev (V : Type) (mem : V → V → Prop) {m : ℕ} (e : Fin m → V)
      (φ : SetTheorySemisentence m) : Prop :=
    let tv {n : ℕ} (e : Fin n → V) : Semiterm ℒₛₑₜ Empty n → V :=
      @Semiterm.rec ℒₛₑₜ Empty n (fun _ => V) e Empty.elim (fun {_} f _ _ => f.elim)
    @Semiformula.rec ℒₛₑₜ Empty (fun n _ => (Fin n → V) → Prop)
      (fun _ => True) (fun _ => False)
      (fun r v e => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun r v e => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mem (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun _ _ a b e => a e ∧ b e) (fun _ _ a b e => a e ∨ b e)
      (fun _ a e => ∀ d, a (d :> e)) (fun _ a e => ∃ d, a (d :> e)) m φ e
  ∀ (V : Type) (mem : V → V → Prop), (∀ ψ ∈ 𝗭𝗙, ev V mem Fin.elim0 ψ) →
    ∀ φS : SetTheorySemisentence 1,
      let S (X : V) : Prop := ev V mem ![X] φS
      let P (x : V) : Prop := ∃ X, S X ∧ mem x X
      (∀ X, S X → ∀ u v, mem v X → mem u v → mem u X) →
      (∀ X Y, S X → S Y → X = Y ∨ mem X Y ∨ mem Y X) →
      (∀ C, (∀ X, mem X C → S X) → ∃ U, S U ∧ ∀ z, mem z U ↔ ∃ X, mem X C ∧ mem z X) →
      (∀ A, (∀ a, mem a A → P a) → ∃ X, S X ∧ ∀ a, mem a A → mem a X) →
      ∀ (k : ℕ) (ψ : SetTheorySemisentence k) (X₀ : V), S X₀ →
        ∃ Y, ∃ hY : S Y, (∀ u, mem u X₀ → mem u Y) ∧
          ∀ q : Fin k → {x // mem x Y},
            ev {x // mem x Y} (fun a b => mem a.1 b.1) q ψ ↔
            ev {x // P x} (fun a b => mem a.1 b.1)
              (fun i => ⟨(q i).1, ⟨Y, hY, (q i).2⟩⟩) ψ

section Helpers

/- ## Part 1: Zero-def Tarski Semantics & Structural Combinators -/

private lemma exTv : ∃ tv : ∀ {V : Type} {ξ : Type} {n : ℕ}, (Fin n → V) → (ξ → V) →
      Semiterm ℒₛₑₜ ξ n → V,
    (∀ {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (i : Fin n),
      tv e ε (Semiterm.bvar i) = e i) ∧
    (∀ {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (x : ξ),
      tv e ε (Semiterm.fvar x) = ε x) :=
  ⟨fun {_} {_} {_} e ε t => match t with
      | Semiterm.bvar i => e i
      | Semiterm.fvar x => ε x
      | Semiterm.func f _ => (f : Empty).elim,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private lemma tv_bvar {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (i : Fin n) :
    exTv.choose e ε (Semiterm.bvar i) = e i := exTv.choose_spec.1 e ε i

private lemma tv_fvar {V : Type} {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V) (x : ξ) :
    exTv.choose e ε (Semiterm.fvar x) = ε x := exTv.choose_spec.2 e ε x

private lemma exEv : ∃ ev : ∀ {V : Type}, (V → V → Prop) →
      ∀ {ξ : Type} {n : ℕ}, (Fin n → V) → (ξ → V) → Semiformula ℒₛₑₜ ξ n → Prop,
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V),
      ev mem e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V),
      ev mem e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev mem e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
        exTv.choose e ε (v 0) = exTv.choose e ε (v 1)) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev mem e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
        mem (exTv.choose e ε (v 0)) (exTv.choose e ε (v 1))) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev mem e ε (Semiformula.nrel Language.Set.Rel.eq v) ↔
        exTv.choose e ε (v 0) ≠ exTv.choose e ε (v 1)) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (v : Fin 2 → Semiterm ℒₛₑₜ ξ n),
      ev mem e ε (Semiformula.nrel Language.Set.Rel.mem v) ↔
        ¬ mem (exTv.choose e ε (v 0)) (exTv.choose e ε (v 1))) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      ev mem e ε (Semiformula.and φ ψ) ↔ ev mem e ε φ ∧ ev mem e ε ψ) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ ψ : Semiformula ℒₛₑₜ ξ n),
      ev mem e ε (Semiformula.or φ ψ) ↔ ev mem e ε φ ∨ ev mem e ε ψ) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      ev mem e ε (Semiformula.all φ) ↔ ∀ d : V, ev mem (d :> e) ε φ) ∧
    (∀ {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ} (e : Fin n → V) (ε : ξ → V)
      (φ : Semiformula ℒₛₑₜ ξ (n + 1)),
      ev mem e ε (Semiformula.exs φ) ↔ ∃ d : V, ev mem (d :> e) ε φ) :=
  ⟨fun {V} mem {ξ} {n} e ε φ =>
      @Semiformula.rec ℒₛₑₜ ξ (fun m _ => (Fin m → V) → Prop)
        (fun {_} _ => True)
        (fun {_} _ => False)
        (fun {m k} r v e' =>
          @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => exTv.choose e' ε (w 0) = exTv.choose e' ε (w 1))
            (fun w => mem (exTv.choose e' ε (w 0)) (exTv.choose e' ε (w 1))) k r v)
        (fun {m k} r v e' =>
          ¬ @Language.Set.Rel.rec (fun k' _ => (Fin k' → Semiterm ℒₛₑₜ ξ m) → Prop)
            (fun w => exTv.choose e' ε (w 0) = exTv.choose e' ε (w 1))
            (fun w => mem (exTv.choose e' ε (w 0)) (exTv.choose e' ε (w 1))) k r v)
        (fun {_} _ _ ih1 ih2 e' => ih1 e' ∧ ih2 e')
        (fun {_} _ _ ih1 ih2 e' => ih1 e' ∨ ih2 e')
        (fun {_} _ ih e' => ∀ d : V, ih (d :> e'))
        (fun {_} _ ih e' => ∃ d : V, ih (d :> e'))
        n φ e,
    fun {_} _ {_} {_} _ _ => Iff.rfl, fun {_} _ {_} {_} _ _ => Iff.rfl,
    fun {_} _ {_} {_} _ _ _ => Iff.rfl, fun {_} _ {_} {_} _ _ _ => Iff.rfl,
    fun {_} _ {_} {_} _ _ _ => Iff.rfl, fun {_} _ {_} {_} _ _ _ => Iff.rfl,
    fun {_} _ {_} {_} _ _ _ _ => Iff.rfl, fun {_} _ {_} {_} _ _ _ _ => Iff.rfl,
    fun {_} _ {_} {_} _ _ _ => Iff.rfl, fun {_} _ {_} {_} _ _ _ => Iff.rfl⟩

private lemma ev_verum {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    exEv.choose mem e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True :=
  exEv.choose_spec.1 mem e ε

private lemma ev_verum_raw {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    exEv.choose mem e ε (Semiformula.verum : Semiformula ℒₛₑₜ ξ n) ↔ True :=
  exEv.choose_spec.1 mem e ε

private lemma ev_falsum {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    exEv.choose mem e ε (⊥ : Semiformula ℒₛₑₜ ξ n) ↔ False :=
  exEv.choose_spec.2.1 mem e ε

private lemma ev_falsum_raw {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) :
    exEv.choose mem e ε (Semiformula.falsum : Semiformula ℒₛₑₜ ξ n) ↔ False :=
  exEv.choose_spec.2.1 mem e ε

private lemma ev_rel_eq {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.rel Language.Set.Rel.eq v) ↔
      exTv.choose e ε (v 0) = exTv.choose e ε (v 1) :=
  exEv.choose_spec.2.2.1 mem e ε v

private lemma ev_rel_mem {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.rel Language.Set.Rel.mem v) ↔
      mem (exTv.choose e ε (v 0)) (exTv.choose e ε (v 1)) :=
  exEv.choose_spec.2.2.2.1 mem e ε v

private lemma ev_nrel_eq {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.nrel Language.Set.Rel.eq v) ↔
      exTv.choose e ε (v 0) ≠ exTv.choose e ε (v 1) :=
  exEv.choose_spec.2.2.2.2.1 mem e ε v

private lemma ev_nrel_mem {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.nrel Language.Set.Rel.mem v) ↔
      ¬ mem (exTv.choose e ε (v 0)) (exTv.choose e ε (v 1)) :=
  exEv.choose_spec.2.2.2.2.2.1 mem e ε v

private lemma ev_and {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (φ ⋏ ψ) ↔
      exEv.choose mem e ε φ ∧ exEv.choose mem e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.2.1 mem e ε φ ψ

private lemma ev_and_raw {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.and φ ψ) ↔
      exEv.choose mem e ε φ ∧ exEv.choose mem e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.2.1 mem e ε φ ψ

private lemma ev_or {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (φ ⋎ ψ) ↔
      exEv.choose mem e ε φ ∨ exEv.choose mem e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.2.2.1 mem e ε φ ψ

private lemma ev_or_raw {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.or φ ψ) ↔
      exEv.choose mem e ε φ ∨ exEv.choose mem e ε ψ :=
  exEv.choose_spec.2.2.2.2.2.2.2.1 mem e ε φ ψ

private lemma ev_all {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (∀¹ φ) ↔ ∀ d : V, exEv.choose mem (d :> e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.2.1 mem e ε φ

private lemma ev_all_raw {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (Semiformula.all φ) ↔ ∀ d : V, exEv.choose mem (d :> e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.2.1 mem e ε φ

private lemma ev_exs {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (∃¹ φ) ↔ ∃ d : V, exEv.choose mem (d :> e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.2.2 mem e ε φ

private lemma ev_exs_raw {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (Semiformula.exs φ) ↔ ∃ d : V, exEv.choose mem (d :> e) ε φ :=
  exEv.choose_spec.2.2.2.2.2.2.2.2.2 mem e ε φ

private lemma ev_eq_raw {V : Type} (mem : V → V → Prop) :
    ∀ {m : ℕ} (φ : Semiformula ℒₛₑₜ Empty m) (e : Fin m → V),
      exEv.choose mem e Empty.elim φ ↔
        let tv {n : ℕ} (e' : Fin n → V) : Semiterm ℒₛₑₜ Empty n → V :=
          @Semiterm.rec ℒₛₑₜ Empty n (fun _ => V) e' Empty.elim (fun {_} f _ _ => f.elim)
        @Semiformula.rec ℒₛₑₜ Empty (fun n _ => (Fin n → V) → Prop)
          (fun _ => True) (fun _ => False)
          (fun r v e' => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
            (fun w => tv e' (w 0) = tv e' (w 1)) (fun w => mem (tv e' (w 0)) (tv e' (w 1))) _ r v)
          (fun r v e' => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
            (fun w => tv e' (w 0) = tv e' (w 1)) (fun w => mem (tv e' (w 0)) (tv e' (w 1))) _ r v)
          (fun _ _ a b e' => a e' ∧ b e') (fun _ _ a b e' => a e' ∨ b e')
          (fun _ a e' => ∀ d, a (d :> e')) (fun _ a e' => ∃ d, a (d :> e')) m φ e := by
  have htv : ∀ {k : ℕ} (e' : Fin k → V) (t : Semiterm ℒₛₑₜ Empty k),
      exTv.choose e' Empty.elim t =
        @Semiterm.rec ℒₛₑₜ Empty k (fun _ => V) e' Empty.elim (fun {_} f _ _ => f.elim) t := by
    intro k e' t
    cases t with
    | bvar i => exact tv_bvar e' Empty.elim i
    | fvar x => exact x.elim
    | func f _ => exact f.elim
  intro m φ
  induction φ with
  | verum => intro e; exact ev_verum_raw mem e Empty.elim
  | falsum => intro e; exact ev_falsum_raw mem e Empty.elim
  | rel r v =>
    intro e
    cases r with
    | eq => simp only [ev_rel_eq, htv]
    | mem => simp only [ev_rel_mem, htv]
  | nrel r v =>
    intro e
    cases r with
    | eq => simp only [ev_nrel_eq, htv]
    | mem => simp only [ev_nrel_mem, htv]
  | and φ ψ ih1 ih2 =>
    intro e
    exact (ev_and_raw mem e Empty.elim φ ψ).trans (and_congr (ih1 e) (ih2 e))
  | or φ ψ ih1 ih2 =>
    intro e
    exact (ev_or_raw mem e Empty.elim φ ψ).trans (or_congr (ih1 e) (ih2 e))
  | all φ ih =>
    intro e
    exact (ev_all_raw mem e Empty.elim φ).trans (forall_congr' fun d => ih (d :> e))
  | exs φ ih =>
    intro e
    exact (ev_exs_raw mem e Empty.elim φ).trans (exists_congr fun d => ih (d :> e))

private lemma ev_neg {V : Type} (mem : V → V → Prop) {ξ : Type} :
    ∀ {n : ℕ} (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ n),
      exEv.choose mem e ε (∼φ) ↔ ¬ exEv.choose mem e ε φ
  | _, e, ε, Semiformula.verum => by
      change exEv.choose mem e ε Semiformula.falsum ↔ _
      rw [ev_falsum_raw, ev_verum_raw]; simp
  | _, e, ε, Semiformula.falsum => by
      change exEv.choose mem e ε Semiformula.verum ↔ _
      rw [ev_verum_raw, ev_falsum_raw]; simp
  | _, e, ε, Semiformula.rel Language.Set.Rel.eq v => by
      change exEv.choose mem e ε (Semiformula.nrel Language.Set.Rel.eq v) ↔ _
      rw [ev_nrel_eq, ev_rel_eq]
  | _, e, ε, Semiformula.rel Language.Set.Rel.mem v => by
      change exEv.choose mem e ε (Semiformula.nrel Language.Set.Rel.mem v) ↔ _
      rw [ev_nrel_mem, ev_rel_mem]
  | _, e, ε, Semiformula.nrel Language.Set.Rel.eq v => by
      change exEv.choose mem e ε (Semiformula.rel Language.Set.Rel.eq v) ↔ _
      rw [ev_rel_eq, ev_nrel_eq]; exact not_not.symm
  | _, e, ε, Semiformula.nrel Language.Set.Rel.mem v => by
      change exEv.choose mem e ε (Semiformula.rel Language.Set.Rel.mem v) ↔ _
      rw [ev_rel_mem, ev_nrel_mem]; exact not_not.symm
  | _, e, ε, Semiformula.and φ ψ => by
      change exEv.choose mem e ε (Semiformula.or (∼φ) (∼ψ)) ↔ _
      rw [ev_or_raw, ev_and_raw, ev_neg mem e ε φ, ev_neg mem e ε ψ, not_and_or]
  | _, e, ε, Semiformula.or φ ψ => by
      change exEv.choose mem e ε (Semiformula.and (∼φ) (∼ψ)) ↔ _
      rw [ev_and_raw, ev_or_raw, ev_neg mem e ε φ, ev_neg mem e ε ψ, not_or]
  | _, e, ε, Semiformula.all φ => by
      change exEv.choose mem e ε (Semiformula.exs (∼φ)) ↔ _
      rw [ev_exs_raw, ev_all_raw]
      simp_rw [ev_neg mem _ ε φ]
      exact not_forall.symm
  | _, e, ε, Semiformula.exs φ => by
      change exEv.choose mem e ε (Semiformula.all (∼φ)) ↔ _
      rw [ev_all_raw, ev_exs_raw]
      simp_rw [ev_neg mem _ ε φ]
      exact not_exists.symm

private lemma ev_imp {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (φ 🡒 ψ) ↔ (exEv.choose mem e ε φ → exEv.choose mem e ε ψ) := by
  change exEv.choose mem e ε (∼φ ⋎ ψ) ↔ _
  rw [ev_or, ev_neg, imp_iff_not_or]

private lemma ev_iff {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ ψ : Semiformula ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (φ 🡘 ψ) ↔ (exEv.choose mem e ε φ ↔ exEv.choose mem e ε ψ) := by
  change exEv.choose mem e ε ((φ 🡒 ψ) ⋏ (ψ 🡒 φ)) ↔ _
  rw [ev_and, ev_imp, ev_imp]
  exact iff_iff_implies_and_implies.symm

private lemma tv_rew {V : Type} {ξ₁ ξ₂ : Type} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    exTv.choose e ε (ω t) =
      exTv.choose (fun i => exTv.choose e ε (ω #i)) (fun x => exTv.choose e ε (ω &x)) t := by
  cases t with
  | bvar i => rw [tv_bvar]
  | fvar x => rw [tv_fvar]
  | func f _ => exact (f : Empty).elim

private lemma tv_bShift {V : Type} {ξ : Type} {n : ℕ} (d : V) (e : Fin n → V) (ε : ξ → V)
    (t : Semiterm ℒₛₑₜ ξ n) :
    exTv.choose (d :> e) ε (Rew.bShift t) = exTv.choose e ε t := by
  cases t with
  | bvar i => exact (tv_bvar (d :> e) ε i.succ).trans (tv_bvar e ε i).symm
  | fvar x => exact (tv_fvar (d :> e) ε x).trans (tv_fvar e ε x).symm
  | func f _ => exact (f : Empty).elim

private lemma ev_congr {V : Type} (mem : V → V → Prop) {ξ : Type}
    {n : ℕ} {e₁ e₂ : Fin n → V} {ε₁ ε₂ : ξ → V} (φ : Semiformula ℒₛₑₜ ξ n)
    (he : e₁ = e₂) (hε : ε₁ = ε₂) :
    exEv.choose mem e₁ ε₁ φ ↔ exEv.choose mem e₂ ε₂ φ := by
  subst he hε; rfl

private lemma ev_rew {V : Type} (mem : V → V → Prop) {ξ₁ ξ₂ : Type} :
    ∀ {n₁ n₂ : ℕ} (e : Fin n₂ → V) (ε : ξ₂ → V) (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
      (φ : Semiformula ℒₛₑₜ ξ₁ n₁),
      exEv.choose mem e ε (ω ▹ φ) ↔
        exEv.choose mem (fun i => exTv.choose e ε (ω #i))
          (fun x => exTv.choose e ε (ω &x)) φ
  | _, _, e, ε, _, Semiformula.verum => by
      change exEv.choose mem e ε Semiformula.verum ↔ _
      rw [ev_verum_raw, ev_verum_raw]
  | _, _, e, ε, _, Semiformula.falsum => by
      change exEv.choose mem e ε Semiformula.falsum ↔ _
      rw [ev_falsum_raw, ev_falsum_raw]
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.eq v => by
      change exEv.choose mem e ε (Semiformula.rel Language.Set.Rel.eq (ω ∘ v)) ↔ _
      rw [ev_rel_eq, ev_rel_eq, Function.comp_apply, Function.comp_apply,
        tv_rew e ε ω (v 0), tv_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.rel Language.Set.Rel.mem v => by
      change exEv.choose mem e ε (Semiformula.rel Language.Set.Rel.mem (ω ∘ v)) ↔ _
      rw [ev_rel_mem, ev_rel_mem, Function.comp_apply, Function.comp_apply,
        tv_rew e ε ω (v 0), tv_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.eq v => by
      change exEv.choose mem e ε (Semiformula.nrel Language.Set.Rel.eq (ω ∘ v)) ↔ _
      rw [ev_nrel_eq, ev_nrel_eq, Function.comp_apply, Function.comp_apply,
        tv_rew e ε ω (v 0), tv_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.nrel Language.Set.Rel.mem v => by
      change exEv.choose mem e ε (Semiformula.nrel Language.Set.Rel.mem (ω ∘ v)) ↔ _
      rw [ev_nrel_mem, ev_nrel_mem, Function.comp_apply, Function.comp_apply,
        tv_rew e ε ω (v 0), tv_rew e ε ω (v 1)]
  | _, _, e, ε, ω, Semiformula.and φ ψ => by
      change exEv.choose mem e ε (Semiformula.and (ω ▹ φ) (ω ▹ ψ)) ↔ _
      rw [ev_and_raw, ev_and_raw]
      exact and_congr (ev_rew mem e ε ω φ) (ev_rew mem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.or φ ψ => by
      change exEv.choose mem e ε (Semiformula.or (ω ▹ φ) (ω ▹ ψ)) ↔ _
      rw [ev_or_raw, ev_or_raw]
      exact or_congr (ev_rew mem e ε ω φ) (ev_rew mem e ε ω ψ)
  | _, _, e, ε, ω, Semiformula.all φ => by
      change exEv.choose mem e ε (Semiformula.all (ω.q ▹ φ)) ↔ _
      rw [ev_all_raw, ev_all_raw]
      refine forall_congr' fun d => (ev_rew mem (d :> e) ε ω.q φ).trans ?_
      refine ev_congr mem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => exact tv_bvar (d :> e) ε 0
        | succ i =>
          change exTv.choose (d :> e) ε (Rew.bShift (ω #i)) = exTv.choose e ε (ω #i)
          exact tv_bShift d e ε _
      · funext x
        change exTv.choose (d :> e) ε (Rew.bShift (ω &x)) = exTv.choose e ε (ω &x)
        exact tv_bShift d e ε _
  | _, _, e, ε, ω, Semiformula.exs φ => by
      change exEv.choose mem e ε (Semiformula.exs (ω.q ▹ φ)) ↔ _
      rw [ev_exs_raw, ev_exs_raw]
      refine exists_congr fun d => (ev_rew mem (d :> e) ε ω.q φ).trans ?_
      refine ev_congr mem φ ?_ ?_
      · funext i
        cases i using Fin.cases with
        | zero => exact tv_bvar (d :> e) ε 0
        | succ i =>
          change exTv.choose (d :> e) ε (Rew.bShift (ω #i)) = exTv.choose e ε (ω #i)
          exact tv_bShift d e ε _
      · funext x
        change exTv.choose (d :> e) ε (Rew.bShift (ω &x)) = exTv.choose e ε (ω &x)
        exact tv_bShift d e ε _

private lemma ev_subst {V : Type} (mem : V → V → Prop) {ξ : Type} {n₁ n₂ : ℕ}
    (e : Fin n₂ → V) (ε : ξ → V) (v : Fin n₁ → Semiterm ℒₛₑₜ ξ n₂)
    (φ : Semiformula ℒₛₑₜ ξ n₁) :
    exEv.choose mem e ε (φ ⇜ v) ↔
      exEv.choose mem (fun i => exTv.choose e ε (v i)) ε φ := by
  change exEv.choose mem e ε (Rew.subst v ▹ φ) ↔ _
  rw [ev_rew]
  refine ev_congr mem φ rfl ?_
  funext x
  exact tv_fvar e ε x

private lemma ev_eq_op {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔
      exTv.choose e ε t = exTv.choose e ε u := by
  unfold Semiformula.Operator.operator
  rw [ev_subst, ev_rew]
  change exEv.choose mem _ _ (Semiformula.rel Language.Set.Rel.eq Semiterm.bvar) ↔ _
  rw [ev_rel_eq, tv_bvar, tv_bvar]
  change exTv.choose _ _ (#0) = exTv.choose _ _ (#1) ↔ _
  rw [tv_bvar, tv_bvar]
  rfl

private lemma ev_mem_op {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t u : Semiterm ℒₛₑₜ ξ n) :
    exEv.choose mem e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔
      mem (exTv.choose e ε t) (exTv.choose e ε u) := by
  unfold Semiformula.Operator.operator
  rw [ev_subst, ev_rew]
  change exEv.choose mem _ _ (Semiformula.rel Language.Set.Rel.mem Semiterm.bvar) ↔ _
  rw [ev_rel_mem, tv_bvar, tv_bvar]
  change mem (exTv.choose _ _ (#0)) (exTv.choose _ _ (#1)) ↔ _
  rw [tv_bvar, tv_bvar]
  rfl

private lemma ev_ballMem {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (Semiformula.ballMem t φ) ↔
      ∀ d : V, mem d (exTv.choose e ε t) → exEv.choose mem (d :> e) ε φ := by
  unfold Semiformula.ballMem ball
  rw [ev_all]
  refine forall_congr' fun d => ?_
  rw [ev_imp, ev_mem_op, tv_bvar, tv_bShift]
  rfl

private lemma ev_bexsMem {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (Semiformula.bexsMem t φ) ↔
      ∃ d : V, mem d (exTv.choose e ε t) ∧ exEv.choose mem (d :> e) ε φ := by
  unfold Semiformula.bexsMem bexs
  rw [ev_exs]
  refine exists_congr fun d => ?_
  rw [ev_and, ev_mem_op, tv_bvar, tv_bShift]
  rfl

private lemma ev_existsUnique {V : Type} (mem : V → V → Prop) {ξ : Type} {n : ℕ}
    (e : Fin n → V) (ε : ξ → V) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    exEv.choose mem e ε (∃¹! φ) ↔ ∃! d : V, exEv.choose mem (d :> e) ε φ := by
  unfold Semiformula.existsUnique
  rw [ev_exs]
  refine exists_congr fun y => ?_
  rw [ev_and, ev_subst, ev_all]
  have h1 : (fun i : Fin (n + 1) =>
      exTv.choose (y :> e) ε
        ((#0 :> fun x : Fin n => #(BinderNotation.finSuccItr x 1)) i)) = y :> e := by
    funext i
    cases i using Fin.cases with
    | zero => exact tv_bvar (y :> e) ε 0
    | succ j => exact tv_bvar (y :> e) ε j.succ
  rw [h1]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  rw [ev_imp, ev_subst, ev_eq_op, tv_bvar, tv_bvar]
  have h2 : (fun i : Fin (n + 1) =>
      exTv.choose (z :> y :> e) ε
        ((#0 :> fun x : Fin n => #(BinderNotation.finSuccItr x 2)) i)) = z :> e := by
    funext i
    cases i using Fin.cases with
    | zero => exact tv_bvar (z :> y :> e) ε 0
    | succ j => exact tv_bvar (z :> y :> e) ε j.succ.succ
  rw [h2]
  rfl

private lemma ev_isSubsetOf {V : Type} (mem : V → V → Prop) {n : ℕ}
    (e : Fin n → V) (t u : Semiterm ℒₛₑₜ Empty n) :
    exEv.choose mem e Empty.elim (isSubsetOf ⇜ ![t, u]) ↔
      ∀ z : V, mem z (exTv.choose e Empty.elim t) → mem z (exTv.choose e Empty.elim u) := by
  rw [ev_subst]
  unfold isSubsetOf
  rw [ev_ballMem]
  refine forall_congr' fun z => imp_congr (by rw [tv_bvar]; rfl) ?_
  rw [ev_mem_op, tv_bvar, tv_bvar]
  rfl

private lemma ev_isEmpty {V : Type} (mem : V → V → Prop) {n : ℕ}
    (e : Fin n → V) (t : Semiterm ℒₛₑₜ Empty n) :
    exEv.choose mem e Empty.elim (isEmpty ⇜ ![t]) ↔
      ∀ y : V, ¬ mem y (exTv.choose e Empty.elim t) := by
  rw [ev_subst]
  unfold isEmpty
  rw [ev_all]
  refine forall_congr' fun y => ?_
  rw [ev_neg, ev_mem_op, tv_bvar, tv_bvar]
  rfl

private lemma ev_isNonempty {V : Type} (mem : V → V → Prop) {n : ℕ}
    (e : Fin n → V) (t : Semiterm ℒₛₑₜ Empty n) :
    exEv.choose mem e Empty.elim (isNonempty ⇜ ![t]) ↔
      ∃ y : V, mem y (exTv.choose e Empty.elim t) := by
  rw [ev_subst]
  unfold isNonempty
  rw [ev_exs]
  refine exists_congr fun y => ?_
  rw [ev_mem_op, tv_bvar, tv_bvar]
  rfl

private lemma ev_isSucc {V : Type} (mem : V → V → Prop) {n : ℕ}
    (e : Fin n → V) (t u : Semiterm ℒₛₑₜ Empty n) :
    exEv.choose mem e Empty.elim (isSucc ⇜ ![t, u]) ↔
      ∀ z : V, mem z (exTv.choose e Empty.elim t) ↔
        z = exTv.choose e Empty.elim u ∨ mem z (exTv.choose e Empty.elim u) := by
  rw [ev_subst]
  unfold isSucc
  rw [ev_all]
  refine forall_congr' fun z => ?_
  rw [ev_iff, ev_mem_op, ev_or, ev_eq_op, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
  rfl

private lemma ev_congr_fv {V : Type} (mem : V → V → Prop) :
    ∀ {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) (e : Fin n → V) (ε₁ ε₂ : ℕ → V),
      (∀ x ∈ φ.freeVariables, ε₁ x = ε₂ x) →
      (exEv.choose mem e ε₁ φ ↔ exEv.choose mem e ε₂ φ) := by
  have htv : ∀ {n : ℕ} (t : Semiterm ℒₛₑₜ ℕ n) (e : Fin n → V) (ε₁ ε₂ : ℕ → V),
      (∀ x ∈ t.freeVariables, ε₁ x = ε₂ x) →
      exTv.choose e ε₁ t = exTv.choose e ε₂ t := by
    intro n t e ε₁ ε₂ h
    cases t with
    | bvar i => rw [tv_bvar, tv_bvar]
    | fvar x =>
      rw [tv_fvar, tv_fvar]
      exact h x (by simp [Semiterm.freeVariables])
    | func f _ => exact f.elim
  intro n φ
  induction φ with
  | verum => intro e ε₁ ε₂ _; rw [ev_verum_raw, ev_verum_raw]
  | falsum => intro e ε₁ ε₂ _; rw [ev_falsum_raw, ev_falsum_raw]
  | rel r v =>
    intro e ε₁ ε₂ h
    have hvi : ∀ i, exTv.choose e ε₁ (v i) = exTv.choose e ε₂ (v i) := fun i =>
      htv (v i) e ε₁ ε₂ fun x hx =>
        h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
    cases r with
    | eq => rw [ev_rel_eq, ev_rel_eq, hvi 0, hvi 1]
    | mem => rw [ev_rel_mem, ev_rel_mem, hvi 0, hvi 1]
  | nrel r v =>
    intro e ε₁ ε₂ h
    have hvi : ∀ i, exTv.choose e ε₁ (v i) = exTv.choose e ε₂ (v i) := fun i =>
      htv (v i) e ε₁ ε₂ fun x hx =>
        h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
    cases r with
    | eq => rw [ev_nrel_eq, ev_nrel_eq, hvi 0, hvi 1]
    | mem => rw [ev_nrel_mem, ev_nrel_mem, hvi 0, hvi 1]
  | and φ ψ ih1 ih2 =>
    intro e ε₁ ε₂ h
    rw [ev_and_raw, ev_and_raw]
    exact and_congr
      (ih1 e ε₁ ε₂ fun x hx => h x (Finset.mem_union_left _ hx))
      (ih2 e ε₁ ε₂ fun x hx => h x (Finset.mem_union_right _ hx))
  | or φ ψ ih1 ih2 =>
    intro e ε₁ ε₂ h
    rw [ev_or_raw, ev_or_raw]
    exact or_congr
      (ih1 e ε₁ ε₂ fun x hx => h x (Finset.mem_union_left _ hx))
      (ih2 e ε₁ ε₂ fun x hx => h x (Finset.mem_union_right _ hx))
  | all φ ih =>
    intro e ε₁ ε₂ h
    rw [ev_all_raw, ev_all_raw]
    exact forall_congr' fun d => ih (d :> e) ε₁ ε₂ h
  | exs φ ih =>
    intro e ε₁ ε₂ h
    rw [ev_exs_raw, ev_exs_raw]
    exact exists_congr fun d => ih (d :> e) ε₁ ε₂ h

private lemma lt_fvSup_of_mem {n : ℕ} {φ : Semiproposition ℒₛₑₜ n} {x : ℕ}
    (hx : x ∈ φ.freeVariables) : x < φ.fvSup := by
  obtain ⟨m, hm⟩ := Finset.max_of_mem hx
  simpa only [Semiformula.fvSup, hm, WithBot.recBotCoe_coe] using
    Nat.lt_succ_of_le (Finset.le_max_of_eq hx hm)

private lemma ev_toEmpty {V : Type} (mem : V → V → Prop) :
    ∀ {m : ℕ} (φ : Semiproposition ℒₛₑₜ m) (h : φ.freeVariables = ∅)
      (e : Fin m → V) (ε : ℕ → V),
      exEv.choose mem e Empty.elim (φ.toEmpty h) ↔ exEv.choose mem e ε φ := by
  have htv : ∀ {m : ℕ} (t : Semiterm ℒₛₑₜ ℕ m) (ht : t.freeVariables = ∅)
      (e : Fin m → V) (ε : ℕ → V),
      exTv.choose e Empty.elim (t.toEmpty ht) = exTv.choose e ε t := by
    intro m t ht e ε
    cases t with
    | bvar i => rw [Semiterm.toEmpty, tv_bvar, tv_bvar]
    | fvar x => exact False.elim (by simp [Semiterm.freeVariables] at ht)
    | func f _ => exact f.elim
  intro m φ
  induction φ with
  | verum => intro _ e ε; rw [Semiformula.toEmpty, ev_verum, ev_verum_raw]
  | falsum => intro _ e ε; rw [Semiformula.toEmpty, ev_falsum, ev_falsum_raw]
  | rel r v =>
    intro h e ε
    have hvi : ∀ i, (v i).freeVariables = ∅ := fun i =>
      Finset.subset_empty.mp
        (h ▸ Finset.subset_biUnion_of_mem (fun j => (v j).freeVariables) (Finset.mem_univ i))
    cases r with
    | eq =>
      change exEv.choose mem e Empty.elim (Semiformula.rel Language.Set.Rel.eq _) ↔ _
      rw [ev_rel_eq, ev_rel_eq, htv (v 0) (hvi 0) e ε, htv (v 1) (hvi 1) e ε]
    | mem =>
      change exEv.choose mem e Empty.elim (Semiformula.rel Language.Set.Rel.mem _) ↔ _
      rw [ev_rel_mem, ev_rel_mem, htv (v 0) (hvi 0) e ε, htv (v 1) (hvi 1) e ε]
  | nrel r v =>
    intro h e ε
    have hvi : ∀ i, (v i).freeVariables = ∅ := fun i =>
      Finset.subset_empty.mp
        (h ▸ Finset.subset_biUnion_of_mem (fun j => (v j).freeVariables) (Finset.mem_univ i))
    cases r with
    | eq =>
      change exEv.choose mem e Empty.elim (Semiformula.nrel Language.Set.Rel.eq _) ↔ _
      rw [ev_nrel_eq, ev_nrel_eq, htv (v 0) (hvi 0) e ε, htv (v 1) (hvi 1) e ε]
    | mem =>
      change exEv.choose mem e Empty.elim (Semiformula.nrel Language.Set.Rel.mem _) ↔ _
      rw [ev_nrel_mem, ev_nrel_mem, htv (v 0) (hvi 0) e ε, htv (v 1) (hvi 1) e ε]
  | and φ ψ ih1 ih2 =>
    intro h e ε
    change exEv.choose mem e Empty.elim (Semiformula.and _ _) ↔ _
    rw [ev_and_raw, ev_and_raw]
    exact and_congr (ih1 (Finset.union_eq_empty.mp h).1 e ε) (ih2 (Finset.union_eq_empty.mp h).2 e ε)
  | or φ ψ ih1 ih2 =>
    intro h e ε
    change exEv.choose mem e Empty.elim (Semiformula.or _ _) ↔ _
    rw [ev_or_raw, ev_or_raw]
    exact or_congr (ih1 (Finset.union_eq_empty.mp h).1 e ε) (ih2 (Finset.union_eq_empty.mp h).2 e ε)
  | all φ ih =>
    intro h e ε
    change exEv.choose mem e Empty.elim (Semiformula.all _) ↔ _
    rw [ev_all_raw, ev_all_raw]
    exact forall_congr' fun d => ih h (d :> e) ε
  | exs φ ih =>
    intro h e ε
    change exEv.choose mem e Empty.elim (Semiformula.exs _) ↔ _
    rw [ev_exs_raw, ev_exs_raw]
    exact exists_congr fun d => ih h (d :> e) ε

private lemma ev_allClosure_iff {V : Type} (mem : V → V → Prop) {ξ : Type} :
    ∀ {k : ℕ} (φ : Semiformula ℒₛₑₜ ξ k) (ε : ξ → V),
      exEv.choose mem Fin.elim0 ε (∀¹* φ) ↔ ∀ b : Fin k → V, exEv.choose mem b ε φ
  | 0, φ, ε => by
    constructor
    · intro h b
      have hb : b = Fin.elim0 := funext fun i => i.elim0
      rw [hb]; exact h
    · intro h; exact h Fin.elim0
  | k + 1, φ, ε => by
    change exEv.choose mem Fin.elim0 ε (∀¹* (∀¹ φ)) ↔ _
    rw [ev_allClosure_iff mem (∀¹ φ) ε]
    constructor
    · intro h b
      have hb : b = b 0 :> fun i => b i.succ := by
        funext i; cases i using Fin.cases <;> rfl
      rw [hb]
      exact (ev_all mem (fun i => b i.succ) ε φ).mp (h (fun i => b i.succ)) (b 0)
    · intro h b
      exact (ev_all mem b ε φ).mpr fun d => h (d :> b)

private lemma fixitr_fvar_val (n m x : ℕ) :
    Rew.fixitr (L := ℒₛₑₜ) n m (&x : Semiterm ℒₛₑₜ ℕ n) =
      if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr n m &x) = _
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

private lemma ev_univCl_iff {V : Type} (mem : V → V → Prop) (v0 : V) (φ : Proposition ℒₛₑₜ) :
    exEv.choose mem Fin.elim0 Empty.elim φ.univCl ↔ ∀ ε : ℕ → V, exEv.choose mem Fin.elim0 ε φ := by
  unfold Semiformula.univCl
  rw [ev_toEmpty mem _ _ Fin.elim0 (fun _ => v0)]
  unfold Semiformula.univCl'
  rw [ev_allClosure_iff mem]
  constructor
  · intro h ε
    have hb := h (fun i : Fin (0 + φ.fvSup) => ε i.val)
    rw [ev_rew] at hb
    have hcongr : exEv.choose mem Fin.elim0
        (fun x => exTv.choose (fun i : Fin (0 + φ.fvSup) => ε i.val) (fun _ => v0)
          (Rew.fixitr 0 φ.fvSup &x)) φ ↔
        exEv.choose mem Fin.elim0 ε φ := by
      refine ev_congr_fv mem φ Fin.elim0 _ ε fun x hx => ?_
      have hlt : x < φ.fvSup := lt_fvSup_of_mem hx
      rw [fixitr_fvar_val, dif_pos hlt, tv_bvar]
      exact congrArg ε (Nat.zero_add x)
    exact hcongr.mp ((ev_congr mem φ (funext fun i => i.elim0) rfl).mp hb)
  · intro h b
    rw [ev_rew]
    exact (ev_congr mem φ (funext fun i => i.elim0) rfl).mpr (h _)

private lemma exCloseFvars (φ : SetTheorySemiproposition 1) :
    ∃ (k : ℕ) (ψ : SetTheorySemisentence (k + 1)),
      ∀ (W : Type) (mW : W → W → Prop) (ε : ℕ → W) (z : W),
        exEv.choose mW (z :> fun i : Fin k => ε i.val) Empty.elim ψ ↔
        exEv.choose mW ![z] ε φ := by
  refine ⟨φ.fvSup,
    Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty (φ.fvSup + 1)))
      (fun x : ℕ => if h : x < φ.fvSup then #(Fin.succ ⟨x, h⟩) else #0) ▹ φ, ?_⟩
  intro W mW ε z
  rw [ev_rew]
  have he : (fun i : Fin 1 => exTv.choose (z :> fun i : Fin φ.fvSup => ε i.val) Empty.elim
      (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty (φ.fvSup + 1)))
        (fun x : ℕ => if h : x < φ.fvSup then #(Fin.succ ⟨x, h⟩) else #0) #i)) = ![z] := by
    funext i; fin_cases i; exact tv_bvar _ Empty.elim 0
  rw [he]
  refine ev_congr_fv mW φ ![z] _ ε ?_
  intro x hx
  have hlt : x < φ.fvSup := lt_fvSup_of_mem hx
  change exTv.choose (z :> fun i : Fin φ.fvSup => ε i.val) Empty.elim
    (if h : x < φ.fvSup then #(Fin.succ ⟨x, h⟩) else #0) = ε x
  rw [dif_pos hlt, tv_bvar]
  rfl

/- ## Part 2: Syntactic Relativization to a Definable Subclass `φP` -/

private lemma exRelativize (φP : SetTheorySemisentence 1) :
    ∃ rel : ∀ {ξ : Type} {m : ℕ}, Semiformula ℒₛₑₜ ξ m → Semiformula ℒₛₑₜ ξ m,
      ∀ {V : Type} (mem : V → V → Prop) (P : V → Prop),
        (∀ x : V, P x ↔ exEv.choose mem ![x] Empty.elim φP) →
        ∀ {ξ : Type} {m : ℕ} (e : Fin m → {x // P x}) (ε : ξ → {x // P x})
          (ψ : Semiformula ℒₛₑₜ ξ m),
          exEv.choose mem (fun i => (e i).1) (fun x => (ε x).1) (rel ψ) ↔
          exEv.choose (fun a b : {x // P x} => mem a.1 b.1) e ε ψ := by
  let pAt0 : ∀ {ξ : Type} {m : ℕ}, Semiformula ℒₛₑₜ ξ (m + 1) :=
    fun {ξ} {m} => Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ (m + 1))) Empty.elim ▹ φP
  let rel : ∀ {ξ : Type} {m : ℕ}, Semiformula ℒₛₑₜ ξ m → Semiformula ℒₛₑₜ ξ m :=
    fun {ξ} {m} ψ =>
      @Semiformula.rec ℒₛₑₜ ξ (fun n _ => Semiformula ℒₛₑₜ ξ n)
        Semiformula.verum
        Semiformula.falsum
        (fun r v => Semiformula.rel r v)
        (fun r v => Semiformula.nrel r v)
        (fun _ _ a b => Semiformula.and a b)
        (fun _ _ a b => Semiformula.or a b)
        (fun _ a => Semiformula.all (∼pAt0 ⋎ a))
        (fun _ a => Semiformula.exs (pAt0 ⋏ a)) m ψ
  have htv : ∀ {V : Type} (P : V → Prop) {ξ : Type} {m : ℕ}
      (e : Fin m → {x // P x}) (ε : ξ → {x // P x}) (t : Semiterm ℒₛₑₜ ξ m),
      exTv.choose (fun i => (e i).1) (fun x => (ε x).1) t = (exTv.choose e ε t).1 := by
    intro V P ξ m e ε t
    cases t with
    | bvar i => rw [tv_bvar, tv_bvar]
    | fvar x => rw [tv_fvar, tv_fvar]
    | func f _ => exact f.elim
  refine ⟨rel, ?_⟩
  intro V mem P hP ξ m e ε ψ
  induction ψ with
  | verum =>
    change exEv.choose mem _ _ Semiformula.verum ↔ _
    rw [ev_verum_raw, ev_verum_raw]
  | falsum =>
    change exEv.choose mem _ _ Semiformula.falsum ↔ _
    rw [ev_falsum_raw, ev_falsum_raw]
  | rel r v =>
    cases r with
    | eq =>
      change exEv.choose mem _ _ (Semiformula.rel Language.Set.Rel.eq v) ↔ _
      rw [ev_rel_eq, ev_rel_eq, htv P e ε (v 0), htv P e ε (v 1), Subtype.ext_iff]
    | mem =>
      change exEv.choose mem _ _ (Semiformula.rel Language.Set.Rel.mem v) ↔ _
      rw [ev_rel_mem, ev_rel_mem, htv P e ε (v 0), htv P e ε (v 1)]
  | nrel r v =>
    cases r with
    | eq =>
      change exEv.choose mem _ _ (Semiformula.nrel Language.Set.Rel.eq v) ↔ _
      rw [ev_nrel_eq, ev_nrel_eq, htv P e ε (v 0), htv P e ε (v 1), ne_eq, ne_eq, Subtype.ext_iff]
    | mem =>
      change exEv.choose mem _ _ (Semiformula.nrel Language.Set.Rel.mem v) ↔ _
      rw [ev_nrel_mem, ev_nrel_mem, htv P e ε (v 0), htv P e ε (v 1)]
  | and ψ₁ ψ₂ ih1 ih2 =>
    change exEv.choose mem _ _ (Semiformula.and (rel ψ₁) (rel ψ₂)) ↔ _
    rw [ev_and_raw, ev_and_raw]
    exact and_congr (ih1 e) (ih2 e)
  | or ψ₁ ψ₂ ih1 ih2 =>
    change exEv.choose mem _ _ (Semiformula.or (rel ψ₁) (rel ψ₂)) ↔ _
    rw [ev_or_raw, ev_or_raw]
    exact or_congr (ih1 e) (ih2 e)
  | all ψ₁ ih =>
    change exEv.choose mem _ _ (Semiformula.all (∼pAt0 ⋎ rel ψ₁)) ↔ _
    rw [ev_all_raw, ev_all_raw]
    constructor
    · intro h d
      have hd := (ev_or mem (d.1 :> fun i => (e i).1) (fun x => (ε x).1) _ _).mp (h d.1)
      have hp0 : exEv.choose mem (d.1 :> fun i => (e i).1) (fun x => (ε x).1) pAt0 := by
        dsimp only [pAt0]
        rw [ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose (d.1 :> fun i => (e i).1) (fun x => (ε x).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim #i)) = ![d.1] := by
          funext i; fin_cases i; exact tv_bvar _ _ 0
        have hε1 : (fun x : Empty => exTv.choose (d.1 :> fun i => (e i).1) (fun x => (ε x).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim &x)) = Empty.elim := by
          funext x; exact x.elim
        rw [he1, hε1]
        exact (hP d.1).mp d.2
      rcases hd with hnp | hrel
      · exact False.elim ((ev_neg mem _ _ _).mp hnp hp0)
      · have hcons : (fun i => ((d :> e) i).1) = (d.1 :> fun i => (e i).1) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [← hcons] at hrel
        exact (ih (d :> e)).mp hrel
    · intro h d
      rw [ev_or, ev_neg]
      by_cases hd : P d
      · right
        have hcons : (fun i => ((⟨d, hd⟩ :> e) i).1) = (d :> fun i => (e i).1) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [← hcons]
        exact (ih (⟨d, hd⟩ :> e)).mpr (h ⟨d, hd⟩)
      · left
        intro hp0
        dsimp only [pAt0] at hp0
        rw [ev_rew] at hp0
        have he1 : (fun i : Fin 1 => exTv.choose (d :> fun i => (e i).1) (fun x => (ε x).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim #i)) = ![d] := by
          funext i; fin_cases i; exact tv_bvar _ _ 0
        have hε1 : (fun x : Empty => exTv.choose (d :> fun i => (e i).1) (fun x => (ε x).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim &x)) = Empty.elim := by
          funext x; exact x.elim
        rw [he1, hε1] at hp0
        exact hd ((hP d).mpr hp0)
  | exs ψ₁ ih =>
    change exEv.choose mem _ _ (Semiformula.exs (pAt0 ⋏ rel ψ₁)) ↔ _
    rw [ev_exs_raw, ev_exs_raw]
    constructor
    · rintro ⟨d, hd⟩
      rcases (ev_and mem _ _ _ _).mp hd with ⟨hp0, hrel⟩
      dsimp only [pAt0] at hp0
      rw [ev_rew] at hp0
      have he1 : (fun i : Fin 1 => exTv.choose (d :> fun i => (e i).1) (fun x => (ε x).1)
          (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim #i)) = ![d] := by
        funext i; fin_cases i; exact tv_bvar _ _ 0
      have hε1 : (fun x : Empty => exTv.choose (d :> fun i => (e i).1) (fun x => (ε x).1)
          (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim &x)) = Empty.elim := by
        funext x; exact x.elim
      rw [he1, hε1] at hp0
      have hdP : P d := (hP d).mpr hp0
      refine ⟨⟨d, hdP⟩, ?_⟩
      have hcons : (fun i => ((⟨d, hdP⟩ :> e) i).1) = (d :> fun i => (e i).1) := by
        funext i; cases i using Fin.cases <;> rfl
      rw [← hcons] at hrel
      exact (ih (⟨d, hdP⟩ :> e)).mp hrel
    · rintro ⟨d, hd⟩
      refine ⟨d.1, (ev_and mem _ _ _ _).mpr ⟨?_, ?_⟩⟩
      · dsimp only [pAt0]
        rw [ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose (d.1 :> fun i => (e i).1) (fun x => (ε x).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim #i)) = ![d.1] := by
          funext i; fin_cases i; exact tv_bvar _ _ 0
        have hε1 : (fun x : Empty => exTv.choose (d.1 :> fun i => (e i).1) (fun x => (ε x).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ξ _)) Empty.elim &x)) = Empty.elim := by
          funext x; exact x.elim
        rw [he1, hε1]
        exact (hP d.1).mp d.2
      · have hcons : (fun i => ((d :> e) i).1) = (d.1 :> fun i => (e i).1) := by
          funext i; cases i using Fin.cases <;> rfl
        rw [← hcons]
        exact (ih (d :> e)).mpr hd

/- ## Part 3: Unpacking `𝗭𝗙` Axioms & `Δ₀` Finite Ordinals `isFinOrd` -/

private lemma zf_empty {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∃ e : V, ∀ y : V, ¬ mem y e := by
  have h := hZF Axiom.empty ZermeloFraenkel.axiom_of_empty_set
  unfold Axiom.empty at h
  rw [ev_exs] at h
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun y => ?_⟩
  rw [ev_all] at he
  have hy := he y
  rw [ev_neg, ev_mem_op, tv_bvar, tv_bvar] at hy
  exact hy

private lemma zf_ext {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∀ x y : V, x = y ↔ ∀ z : V, mem z x ↔ mem z y := by
  have h := hZF Axiom.extentionality ZermeloFraenkel.axiom_of_extentionality
  unfold Axiom.extentionality at h
  rw [ev_all] at h
  intro x y
  have hx := h x
  rw [ev_all] at hx
  have hxy := hx y
  rw [ev_iff, ev_eq_op, tv_bvar, tv_bvar, ev_all] at hxy
  refine hxy.trans (forall_congr' fun z => ?_)
  rw [ev_iff, ev_mem_op, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
  rfl

private lemma zf_pair {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∀ x y : V, ∃ z : V, ∀ w : V, mem w z ↔ w = x ∨ w = y := by
  have h := hZF Axiom.pairing ZermeloFraenkel.axiom_of_pairing
  unfold Axiom.pairing at h
  rw [ev_all] at h
  intro x y
  have hx := h x
  rw [ev_all] at hx
  have hxy := hx y
  rw [ev_exs] at hxy
  obtain ⟨z, hz⟩ := hxy
  refine ⟨z, fun w => ?_⟩
  rw [ev_all] at hz
  have hw := hz w
  rw [ev_iff, ev_mem_op, ev_or, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar, tv_bvar] at hw
  exact hw

private lemma zf_union {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∀ x : V, ∃ y : V, ∀ z : V, mem z y ↔ ∃ w : V, mem w x ∧ mem z w := by
  have h := hZF Axiom.union ZermeloFraenkel.axiom_of_union
  unfold Axiom.union at h
  rw [ev_all] at h
  intro x
  have hx := h x
  rw [ev_exs] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, fun z => ?_⟩
  rw [ev_all] at hy
  have hz := hy z
  rw [ev_iff, ev_mem_op, ev_bexsMem, tv_bvar, tv_bvar, tv_bvar] at hz
  refine hz.trans (exists_congr fun w => and_congr Iff.rfl ?_)
  rw [ev_mem_op, tv_bvar, tv_bvar]
  rfl

private lemma zf_power {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∀ x : V, ∃ y : V, ∀ z : V, mem z y ↔ ∀ u : V, mem u z → mem u x := by
  have h := hZF Axiom.power ZermeloFraenkel.axiom_of_power_set
  unfold Axiom.power at h
  rw [ev_all] at h
  intro x
  have hx := h x
  rw [ev_exs] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, fun z => ?_⟩
  rw [ev_all] at hy
  have hz := hy z
  rw [ev_iff, ev_mem_op, ev_isSubsetOf, tv_bvar, tv_bvar, tv_bvar] at hz
  exact hz

private lemma zf_inf {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∃ I : V, (∀ e : V, (∀ y, ¬ mem y e) → mem e I) ∧
      (∀ x : V, mem x I → ∀ x' : V, (∀ z, mem z x' ↔ z = x ∨ mem z x) → mem x' I) := by
  have h := hZF Axiom.infinity ZermeloFraenkel.axiom_of_infinity
  unfold Axiom.infinity at h
  rw [ev_exs] at h
  obtain ⟨I, hI⟩ := h
  rw [ev_and] at hI
  refine ⟨I, ?_, ?_⟩
  · intro e he
    have h1 := hI.1
    rw [ev_all] at h1
    have h1e := h1 e
    rw [ev_imp, ev_isEmpty, ev_mem_op, tv_bvar, tv_bvar] at h1e
    exact h1e he
  · intro x hx x' hx'
    have h2 := hI.2
    rw [ev_ballMem] at h2
    have h2x := h2 x (by rw [tv_bvar]; exact hx)
    rw [ev_all] at h2x
    have h2x' := h2x x'
    rw [ev_imp, ev_isSucc, ev_mem_op, tv_bvar, tv_bvar, tv_bvar] at h2x'
    exact h2x' hx'

private lemma zf_found {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ) :
    ∀ x : V, (∃ y : V, mem y x) → ∃ y : V, mem y x ∧ ∀ z : V, mem z x → ¬ mem z y := by
  have h := hZF Axiom.foundation ZermeloFraenkel.axiom_of_foundation
  unfold Axiom.foundation at h
  rw [ev_all] at h
  intro x hx
  have h1 := h x
  rw [ev_imp, ev_isNonempty, ev_bexsMem, tv_bvar] at h1
  obtain ⟨y, hyx, hymin⟩ := h1 hx
  refine ⟨y, hyx, fun z hz => ?_⟩
  rw [ev_ballMem] at hymin
  have hmin := hymin z (by rw [tv_bvar]; exact hz)
  rw [ev_neg, ev_mem_op, tv_bvar, tv_bvar] at hmin
  exact hmin

private lemma zf_sep {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ)
    (φ : SetTheorySemiproposition 1) (ε : ℕ → V) (x : V) :
    ∃ y : V, ∀ z : V, mem z y ↔ mem z x ∧ exEv.choose mem ![z] ε φ := by
  obtain ⟨v0, _⟩ := zf_empty hZF
  have h := hZF (Axiom.separationSchema φ) (ZermeloFraenkel.axiom_of_separation φ)
  unfold Axiom.separationSchema at h
  have h1 := (ev_univCl_iff mem v0 _).mp h ε
  rw [ev_all] at h1
  have h2 := h1 x
  rw [ev_exs] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨y, fun z => ?_⟩
  rw [ev_all] at hy
  have hz := hy z
  rw [ev_iff, ev_mem_op, ev_and, ev_mem_op, ev_subst, tv_bvar, tv_bvar, tv_bvar] at hz
  refine hz.trans (and_congr Iff.rfl ?_)
  refine ev_congr mem φ ?_ rfl
  funext i; fin_cases i; exact tv_bvar _ _ 0

private lemma zf_rep {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ)
    (φ : SetTheorySemiproposition 2) (ε : ℕ → V)
    (hfunc : ∀ x : V, ∃! y : V, exEv.choose mem ![x, y] ε φ) (X : V) :
    ∃ Y : V, ∀ y : V, mem y Y ↔ ∃ x : V, mem x X ∧ exEv.choose mem ![x, y] ε φ := by
  obtain ⟨v0, _⟩ := zf_empty hZF
  have h := hZF (Axiom.replacementSchema φ) (ZermeloFraenkel.axiom_of_replacement φ)
  unfold Axiom.replacementSchema at h
  have h1 := (ev_univCl_iff mem v0 _).mp h ε
  rw [ev_imp] at h1
  have hdom : exEv.choose mem Fin.elim0 ε “∀ x, ∃! y, !φ x y” := by
    rw [ev_all]
    intro x
    rw [ev_existsUnique]
    obtain ⟨y, hy, huniq⟩ := hfunc x
    refine ⟨y, ?_, fun z hz => ?_⟩
    · dsimp only
      rw [ev_subst]
      refine (ev_congr mem φ ?_ rfl).mpr hy
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    · dsimp only at hz
      rw [ev_subst] at hz
      apply huniq z
      refine (ev_congr mem φ ?_ rfl).mp hz
      funext i; fin_cases i <;> exact tv_bvar _ _ _
  have h2 := h1 hdom
  rw [ev_all] at h2
  have h3 := h2 X
  rw [ev_exs] at h3
  obtain ⟨Y, hY⟩ := h3
  refine ⟨Y, fun y => ?_⟩
  rw [ev_all] at hY
  have hy := hY y
  rw [ev_iff, ev_mem_op, ev_bexsMem, tv_bvar, tv_bvar, tv_bvar] at hy
  refine hy.trans (exists_congr fun x => and_congr Iff.rfl ?_)
  rw [ev_subst]
  refine ev_congr mem φ ?_ rfl
  funext i; fin_cases i <;> exact tv_bvar _ _ _

private lemma v_finset_of_pred {V : Type} {mem : V → V → Prop}
    (hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ)
    {P : V → Prop} {k : ℕ} (p : Fin k → {x // P x}) :
    ∃ A : V, ∀ a : V, mem a A ↔ ∃ i : Fin k, a = (p i).1 := by
  induction k with
  | zero =>
    obtain ⟨e, he⟩ := zf_empty hZF
    exact ⟨e, fun a => ⟨fun h => False.elim (he a h), fun ⟨i, _⟩ => i.elim0⟩⟩
  | succ k ih =>
    obtain ⟨A₀, hA₀⟩ := ih (fun i => p i.succ)
    obtain ⟨s0, hs0⟩ := zf_pair hZF (p 0).1 (p 0).1
    obtain ⟨d, hd⟩ := zf_pair hZF s0 A₀
    obtain ⟨U, hU⟩ := zf_union hZF d
    refine ⟨U, fun a => ?_⟩
    rw [hU]
    constructor
    · rintro ⟨w, hw, haw⟩
      rcases (hd w).mp hw with rfl | rfl
      · rcases (hs0 a).mp haw with rfl | rfl <;> exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := (hA₀ a).mp haw
        exact ⟨i.succ, hi⟩
    · rintro ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact ⟨s0, (hd s0).mpr (Or.inl rfl), (hs0 _).mpr (Or.inl rfl)⟩
      | succ j => exact ⟨A₀, (hd A₀).mpr (Or.inr rfl), (hA₀ _).mpr ⟨j, rfl⟩⟩

private lemma exIsFinOrd :
    ∃ φFO : SetTheorySemisentence 1,
      ∀ (V : Type) (mem : V → V → Prop) (x : V),
        exEv.choose mem ![x] Empty.elim φFO ↔
          ((∀ a, mem a x → ∀ b, mem b a → mem b x) ∧
           (∀ a, mem a x → ∀ b, mem b a → ∀ c, mem c b → mem c a)) ∧
          (((∀ a, ¬ mem a x) ∨
            ∃ y, mem y x ∧ (∀ z, mem z x → z = y ∨ mem z y) ∧ (∀ z, mem z y → mem z x)) ∧
           (∀ u, mem u x →
            (∀ a, ¬ mem a u) ∨
            ∃ y, mem y u ∧ (∀ z, mem z u → z = y ∨ mem z y) ∧ (∀ z, mem z y → mem z u))) := by
  let isTr : SetTheorySemisentence 1 :=
    Semiformula.ballMem #0 (Semiformula.ballMem #0
      (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#0, #2]))
  let isO : SetTheorySemisentence 1 :=
    isTr ⋏
      (Semiformula.ballMem #0
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim ▹ isTr))
  let isZS : SetTheorySemisentence 1 :=
    (Semiformula.ballMem #0 ⊥) ⋎
      (Semiformula.bexsMem #0
        ((Semiformula.ballMem #1
            ((Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![#0, #1]) ⋎
              (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#0, #1]))) ⋏
          (Semiformula.ballMem #0
            (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#0, #2]))))
  let φFO : SetTheorySemisentence 1 :=
    isO ⋏
      (isZS ⋏
        (Semiformula.ballMem #0
          (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim ▹ isZS)))
  have hTr : ∀ (V : Type) (mem : V → V → Prop) (u : V),
      exEv.choose mem ![u] Empty.elim isTr ↔ ∀ a, mem a u → ∀ b, mem b a → mem b u := by
    intro V mem u
    dsimp only [isTr]
    rw [ev_ballMem, tv_bvar]
    refine forall_congr' fun a => imp_congr Iff.rfl ?_
    rw [ev_ballMem, tv_bvar]
    refine forall_congr' fun b => imp_congr Iff.rfl ?_
    rw [ev_mem_op, tv_bvar, tv_bvar]
    rfl
  have hZS : ∀ (V : Type) (mem : V → V → Prop) (u : V),
      exEv.choose mem ![u] Empty.elim isZS ↔
        (∀ a, ¬ mem a u) ∨
        ∃ y, mem y u ∧ (∀ z, mem z u → z = y ∨ mem z y) ∧ (∀ z, mem z y → mem z u) := by
    intro V mem u
    dsimp only [isZS]
    rw [ev_or]
    refine or_congr ?_ ?_
    · rw [ev_ballMem, tv_bvar]
      refine forall_congr' fun a => imp_congr Iff.rfl (ev_falsum mem _ _)
    · rw [ev_bexsMem, tv_bvar]
      refine exists_congr fun y => and_congr Iff.rfl ?_
      rw [ev_and]
      refine and_congr ?_ ?_
      · rw [ev_ballMem, tv_bvar]
        refine forall_congr' fun z => imp_congr Iff.rfl ?_
        rw [ev_or, ev_eq_op, ev_mem_op, tv_bvar, tv_bvar]
        rfl
      · rw [ev_ballMem, tv_bvar]
        refine forall_congr' fun z => imp_congr Iff.rfl ?_
        rw [ev_mem_op, tv_bvar, tv_bvar]
        rfl
  refine ⟨φFO, fun V mem x => ?_⟩
  dsimp only [φFO, isO]
  rw [ev_and, ev_and, ev_and]
  refine and_congr (and_congr (hTr V mem x) ?_) (and_congr (hZS V mem x) ?_)
  · rw [ev_ballMem, tv_bvar]
    refine forall_congr' fun a => imp_congr Iff.rfl ?_
    rw [ev_rew]
    have he1 : (fun i : Fin 1 => exTv.choose (a :> ![x]) Empty.elim
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim #i)) = ![a] := by
      funext i; fin_cases i; exact tv_bvar _ _ 0
    have hε1 : (fun z : Empty => exTv.choose (a :> ![x]) Empty.elim
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim &z)) = Empty.elim := by
      funext z; exact z.elim
    rw [he1, hε1]
    exact hTr V mem a
  · rw [ev_ballMem, tv_bvar]
    refine forall_congr' fun u => imp_congr Iff.rfl ?_
    rw [ev_rew]
    have he1 : (fun i : Fin 1 => exTv.choose (u :> ![x]) Empty.elim
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim #i)) = ![u] := by
      funext i; fin_cases i; exact tv_bvar _ _ 0
    have hε1 : (fun z : Empty => exTv.choose (u :> ![x]) Empty.elim
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim &z)) = Empty.elim := by
      funext z; exact z.elim
    rw [he1, hε1]
    exact hZS V mem u

private lemma isFinOrd_abs_trans {V : Type} {mem : V → V → Prop} (T : V → Prop)
    (hT : ∀ u v, T v → mem u v → T u) (x : V) (hx : T x) :
    exEv.choose (fun a b : {v // T v} => mem a.1 b.1) ![⟨x, hx⟩] Empty.elim exIsFinOrd.choose ↔
    exEv.choose mem ![x] Empty.elim exIsFinOrd.choose := by
  rw [exIsFinOrd.choose_spec {v // T v} (fun a b => mem a.1 b.1) ⟨x, hx⟩,
    exIsFinOrd.choose_spec V mem x]
  have hZS_abs : ∀ (u : V) (hu : T u),
      ((∀ a : {v // T v}, ¬ mem a.1 u) ∨
        ∃ y : {v // T v}, mem y.1 u ∧
          (∀ z : {v // T v}, mem z.1 u → z = y ∨ mem z.1 y.1) ∧
          (∀ z : {v // T v}, mem z.1 y.1 → mem z.1 u)) ↔
      ((∀ a : V, ¬ mem a u) ∨
        ∃ y : V, mem y u ∧
          (∀ z : V, mem z u → z = y ∨ mem z y) ∧
          (∀ z : V, mem z y → mem z u)) := by
    intro u hu
    refine or_congr ?_ ?_
    · exact ⟨fun h a ha => h ⟨a, hT a u hu ha⟩ ha, fun h a ha => h a.1 ha⟩
    · constructor
      · rintro ⟨y, hyu, h1, h2⟩
        refine ⟨y.1, hyu, fun z hz => ?_, fun z hz => h2 ⟨z, hT z y.1 y.2 hz⟩ hz⟩
        rcases h1 ⟨z, hT z u hu hz⟩ hz with hEq | hMem
        · exact Or.inl (congrArg Subtype.val hEq)
        · exact Or.inr hMem
      · rintro ⟨y, hyu, h1, h2⟩
        have hyT : T y := hT y u hu hyu
        refine ⟨⟨y, hyT⟩, hyu, fun z hz => ?_, fun z hz => h2 z.1 hz⟩
        rcases h1 z.1 hz with hEq | hMem
        · exact Or.inl (Subtype.ext hEq)
        · exact Or.inr hMem
  refine and_congr (and_congr ?_ ?_) (and_congr (hZS_abs x hx) ?_)
  · exact ⟨fun h a ha b hb => h ⟨a, hT a x hx ha⟩ ha ⟨b, hT b a (hT a x hx ha) hb⟩ hb,
      fun h a ha b hb => h a.1 ha b.1 hb⟩
  · exact ⟨fun h a ha b hb c hc =>
        have haT := hT a x hx ha
        have hbT := hT b a haT hb
        h ⟨a, haT⟩ ha ⟨b, hbT⟩ hb ⟨c, hT c b hbT hc⟩ hc,
      fun h a ha b hb c hc => h a.1 ha b.1 hb c.1 hc⟩
  · constructor
    · intro h u hu
      exact (hZS_abs u (hT u x hx hu)).mp (h ⟨u, hT u x hx hu⟩ hu)
    · intro h u hu
      exact (hZS_abs u.1 u.2).mpr (h u.1 hu)

private lemma kpair_eval_iff {V : Type} {mem : V → V → Prop}
    (hExt : ∀ x y : V, x = y ↔ ∀ z : V, mem z x ↔ mem z y)
    (hPair : ∀ x y : V, ∃ z : V, ∀ w : V, mem w z ↔ w = x ∨ w = y)
    (p x y : V) :
    exEv.choose mem ![p, x, y] Empty.elim SetTheory.kpair.dfn ↔
      ∃ s d : V, (∀ w, mem w s ↔ w = x) ∧ (∀ w, mem w d ↔ w = x ∨ w = y) ∧
        (∀ w, mem w p ↔ w = s ∨ w = d) := by
  have hDbl : ∀ a b c : V,
      exEv.choose mem ![a, b, c] Empty.elim SetTheory.doubleton.dfn ↔
        ∀ w, mem w a ↔ w = b ∨ w = c := by
    intro a b c
    unfold SetTheory.doubleton.dfn
    rw [ev_all]
    refine forall_congr' fun w => ?_
    rw [ev_iff, ev_mem_op, ev_or, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar, tv_bvar]
    rfl
  have hSng : ∀ a b : V,
      exEv.choose mem ![a, b] Empty.elim SetTheory.singleton.dfn ↔ ∀ w, mem w a ↔ w = b := by
    intro a b
    unfold SetTheory.singleton.dfn
    rw [ev_subst]
    have h1 : (fun i : Fin 3 => exTv.choose ![a, b] Empty.elim ((![#0, #1, #1] : Fin 3 → _) i)) =
        ![a, b, b] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h1, hDbl]
    exact forall_congr' fun w => iff_congr Iff.rfl (or_self_iff)
  unfold SetTheory.kpair.dfn
  rw [ev_all]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := hPair x x
    have hs' : ∀ w, mem w s ↔ w = x := fun w => (hs w).trans (or_self_iff)
    obtain ⟨d, hd⟩ := hPair x y
    have h1 := h s
    rw [ev_imp, ev_subst] at h1
    have h1v : (fun i : Fin 2 => exTv.choose (s :> ![p, x, y]) Empty.elim ((![#0, #2] : Fin 2 → _) i)) =
        ![s, x] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h1v, hSng] at h1
    have h2 := h1 hs'
    rw [ev_all] at h2
    have h3 := h2 d
    rw [ev_imp, ev_subst] at h3
    have h3v : (fun i : Fin 3 => exTv.choose (d :> s :> ![p, x, y]) Empty.elim
        ((![#0, #3, #4] : Fin 3 → _) i)) = ![d, x, y] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h3v, hDbl] at h3
    have h4 := h3 hd
    rw [ev_subst] at h4
    have h4v : (fun i : Fin 3 => exTv.choose (d :> s :> ![p, x, y]) Empty.elim
        ((![#2, #1, #0] : Fin 3 → _) i)) = ![p, s, d] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h4v, hDbl] at h4
    exact ⟨s, d, hs', hd, h4⟩
  · rintro ⟨s, d, hs, hd, hp⟩ s'
    rw [ev_imp, ev_subst]
    have h1v : (fun i : Fin 2 => exTv.choose (s' :> ![p, x, y]) Empty.elim ((![#0, #2] : Fin 2 → _) i)) =
        ![s', x] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h1v, hSng]
    intro hs'
    have hs_eq : s' = s := (hExt s' s).mpr fun w => (hs' w).trans (hs w).symm
    subst hs_eq
    rw [ev_all]
    intro d'
    rw [ev_imp, ev_subst]
    have h3v : (fun i : Fin 3 => exTv.choose (d' :> s' :> ![p, x, y]) Empty.elim
        ((![#0, #3, #4] : Fin 3 → _) i)) = ![d', x, y] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h3v, hDbl]
    intro hd'
    have hd_eq : d' = d := (hExt d' d).mpr fun w => (hd' w).trans (hd w).symm
    subst hd_eq
    rw [ev_subst]
    have h4v : (fun i : Fin 3 => exTv.choose (d' :> s' :> ![p, x, y]) Empty.elim
        ((![#2, #1, #0] : Fin 3 → _) i)) = ![p, s', d'] := by
      funext i; fin_cases i <;> exact tv_bvar _ _ _
    rw [h4v, hDbl]
    exact hp

private lemma kpair_abs {V : Type} {mem : V → V → Prop}
    (hExtV : ∀ x y : V, x = y ↔ ∀ z : V, mem z x ↔ mem z y)
    (hPairV : ∀ x y : V, ∃ z : V, ∀ w : V, mem w z ↔ w = x ∨ w = y)
    (P : V → Prop) (hTrans : ∀ u v, P v → mem u v → P u)
    (hPairL : ∀ x y : {v // P v}, ∃ z : {v // P v}, ∀ w : {v // P v}, mem w.1 z.1 ↔ w = x ∨ w = y)
    (p x y : {v // P v}) :
    exEv.choose (fun a b : {v // P v} => mem a.1 b.1) ![p, x, y] Empty.elim SetTheory.kpair.dfn ↔
    exEv.choose mem ![p.1, x.1, y.1] Empty.elim SetTheory.kpair.dfn := by
  have hExtL : ∀ a b : {v // P v}, a = b ↔ ∀ z : {v // P v}, mem z.1 a.1 ↔ mem z.1 b.1 := by
    intro a b
    refine ⟨fun h => by subst h; intro _; exact Iff.rfl, fun h => Subtype.ext ?_⟩
    exact (hExtV a.1 b.1).mpr fun z =>
      ⟨fun hza => (h ⟨z, hTrans z a.1 a.2 hza⟩).mp hza,
       fun hzb => (h ⟨z, hTrans z b.1 b.2 hzb⟩).mpr hzb⟩
  rw [kpair_eval_iff hExtL hPairL p x y, kpair_eval_iff hExtV hPairV p.1 x.1 y.1]
  constructor
  · rintro ⟨s, d, hs, hd, hp⟩
    refine ⟨s.1, d.1, ?_, ?_, ?_⟩
    · intro w
      exact ⟨fun hw => congrArg Subtype.val ((hs ⟨w, hTrans w s.1 s.2 hw⟩).mp hw),
        fun hw => by subst hw; exact (hs x).mpr rfl⟩
    · intro w
      refine ⟨fun hw => ?_, fun hw => ?_⟩
      · rcases (hd ⟨w, hTrans w d.1 d.2 hw⟩).mp hw with h1 | h2
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h2)
      · rcases hw with rfl | rfl
        · exact (hd x).mpr (Or.inl rfl)
        · exact (hd y).mpr (Or.inr rfl)
    · intro w
      refine ⟨fun hw => ?_, fun hw => ?_⟩
      · rcases (hp ⟨w, hTrans w p.1 p.2 hw⟩).mp hw with h1 | h2
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h2)
      · rcases hw with rfl | rfl
        · exact (hp s).mpr (Or.inl rfl)
        · exact (hp d).mpr (Or.inr rfl)
  · rintro ⟨s, d, hs, hd, hp⟩
    obtain ⟨sL, hsL⟩ := hPairL x x
    have hsEq : sL.1 = s := (hExtV sL.1 s).mpr fun w =>
      ⟨fun hw => by
        rcases (hsL ⟨w, hTrans w sL.1 sL.2 hw⟩).mp hw with h1 | h1 <;>
          exact (hs w).mpr (congrArg Subtype.val h1),
       fun hw => by rw [(hs w).mp hw]; exact (hsL x).mpr (Or.inl rfl)⟩
    obtain ⟨dL, hdL⟩ := hPairL x y
    have hdEq : dL.1 = d := (hExtV dL.1 d).mpr fun w =>
      ⟨fun hw => by
        rcases (hdL ⟨w, hTrans w dL.1 dL.2 hw⟩).mp hw with h1 | h2
        · exact (hd w).mpr (Or.inl (congrArg Subtype.val h1))
        · exact (hd w).mpr (Or.inr (congrArg Subtype.val h2)),
       fun hw => by
        rcases (hd w).mp hw with rfl | rfl
        · exact (hdL x).mpr (Or.inl rfl)
        · exact (hdL y).mpr (Or.inr rfl)⟩
    refine ⟨sL, dL, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hsEq, hs w.1, Subtype.ext_iff]
    · rw [hdEq, hd w.1, Subtype.ext_iff, Subtype.ext_iff]
    · rw [hp w.1, ← hsEq, ← hdEq, Subtype.ext_iff, Subtype.ext_iff]

/- ## Part 4: Verification of `𝗘𝗤` in Any Normal Model `(W, mW)` -/

private lemma normal_eq_axioms {W : Type} (mW : W → W → Prop) :
    ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, exEv.choose mW Fin.elim0 Empty.elim φ := by
  intro φ hφ
  cases hφ with
  | refl =>
    unfold Theory.Eq.refl
    rw [ev_all]
    intro x
    rw [ev_eq_op, tv_bvar]
  | symm =>
    unfold Theory.Eq.symm
    rw [ev_all]; intro x
    rw [ev_all]; intro y
    rw [ev_imp, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar]
    exact Eq.symm
  | trans =>
    unfold Theory.Eq.trans
    rw [ev_all]; intro x
    rw [ev_all]; intro y
    rw [ev_all]; intro z
    rw [ev_imp, ev_imp, ev_eq_op, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar]
    exact Eq.trans
  | funcExt f => exact f.elim
  | relExt r =>
    unfold Theory.Eq.relExt
    rw [ev_allClosure_iff mW]
    intro b
    rw [ev_imp, ev_imp]
    cases r with
    | eq =>
      intro hconj hrel
      rw [ev_rel_eq] at hrel ⊢
      change exEv.choose mW b Empty.elim
        (Semiformula.Operator.operator Semiformula.Operator.Eq.eq
          ![#((0 : Fin 2).addCast 2), #((0 : Fin 2).addNat 2)] ⋏
         (Semiformula.Operator.operator Semiformula.Operator.Eq.eq
          ![#((1 : Fin 2).addCast 2), #((1 : Fin 2).addNat 2)] ⋏ ⊤)) at hconj
      rw [ev_and, ev_and, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar, tv_bvar] at hconj
      rw [tv_bvar, tv_bvar] at hrel ⊢
      have h0 : b ((0 : Fin 2).addCast 2) = b ((0 : Fin 2).addNat 2) := hconj.1
      have h1 : b ((1 : Fin 2).addCast 2) = b ((1 : Fin 2).addNat 2) := hconj.2.1
      rw [← h0, ← h1]
      exact hrel
    | mem =>
      intro hconj hrel
      rw [ev_rel_mem] at hrel ⊢
      change exEv.choose mW b Empty.elim
        (Semiformula.Operator.operator Semiformula.Operator.Eq.eq
          ![#((0 : Fin 2).addCast 2), #((0 : Fin 2).addNat 2)] ⋏
         (Semiformula.Operator.operator Semiformula.Operator.Eq.eq
          ![#((1 : Fin 2).addCast 2), #((1 : Fin 2).addNat 2)] ⋏ ⊤)) at hconj
      rw [ev_and, ev_and, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar, tv_bvar] at hconj
      rw [tv_bvar, tv_bvar] at hrel ⊢
      have h0 : b ((0 : Fin 2).addCast 2) = b ((0 : Fin 2).addNat 2) := hconj.1
      have h1 : b ((1 : Fin 2).addCast 2) = b ((1 : Fin 2).addNat 2) := hconj.2.1
      rw [← h0, ← h1]
      exact hrel

end Helpers

theorem main : H1 → H2 → OMA.R_Constant14_c14_le_432_R1_H1_R1.H1 := by
  intro h1 h2 V mem hZF_sat
  let evRaw (W : Type) (mW : W → W → Prop) {m : ℕ} (e : Fin m → W)
      (φ : SetTheorySemisentence m) : Prop :=
    let tv {n : ℕ} (e : Fin n → W) : Semiterm ℒₛₑₜ Empty n → W :=
      @Semiterm.rec ℒₛₑₜ Empty n (fun _ => W) e Empty.elim (fun {_} f _ _ => f.elim)
    @Semiformula.rec ℒₛₑₜ Empty (fun n _ => (Fin n → W) → Prop)
      (fun _ => True) (fun _ => False)
      (fun r v e => @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mW (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun r v e => ¬ @Language.Set.Rel.rec (fun k _ => (Fin k → Semiterm ℒₛₑₜ Empty _) → Prop)
        (fun w => tv e (w 0) = tv e (w 1)) (fun w => mW (tv e (w 0)) (tv e (w 1))) _ r v)
      (fun _ _ a b e => a e ∧ b e) (fun _ _ a b e => a e ∨ b e)
      (fun _ a e => ∀ d, a (d :> e)) (fun _ a e => ∃ d, a (d :> e)) m φ e
  have hZF : ∀ ψ ∈ 𝗭𝗙, exEv.choose mem Fin.elim0 Empty.elim ψ := fun ψ hψ =>
    (ev_eq_raw mem ψ Fin.elim0).mpr (hZF_sat ψ hψ)
  obtain ⟨φS, hTransS, hSTrich, hSUnion, hCoverS, hSDef, hSWO⟩ := h1 V mem hZF_sat
  let S : V → Prop := fun X => evRaw V mem ![X] φS
  let P : V → Prop := fun x => ∃ X, S X ∧ mem x X
  have hDefS : ∀ X, S X → ∀ (k : ℕ) (ψ : SetTheorySemisentence (k + 1)) (p : Fin k → {x // mem x X}),
      ∃ Y, S Y ∧ ∃ Z, mem Z Y ∧ ∀ u, mem u Z ↔
        ∃ hu : mem u X, exEv.choose (fun a b : {x // mem x X} => mem a.1 b.1) (⟨u, hu⟩ :> p) Empty.elim ψ := by
    intro X hX k ψ p
    obtain ⟨Y, hY, Z, hZY, hZ⟩ := hSDef X hX k ψ p
    refine ⟨Y, hY, Z, hZY, fun u => (hZ u).trans ?_⟩
    exact exists_congr fun hu => (ev_eq_raw (fun a b : {x // mem x X} => mem a.1 b.1) ψ (⟨u, hu⟩ :> p)).symm
  have hReflS : ∀ (k : ℕ) (ψ : SetTheorySemisentence k) (X₀ : V), S X₀ →
      ∃ Y, ∃ hY : S Y, (∀ u, mem u X₀ → mem u Y) ∧
        ∀ q : Fin k → {x // mem x Y},
          exEv.choose (fun a b : {x // mem x Y} => mem a.1 b.1) q Empty.elim ψ ↔
          exEv.choose (fun a b : {x // P x} => mem a.1 b.1)
            (fun i => ⟨(q i).1, ⟨Y, hY, (q i).2⟩⟩) Empty.elim ψ := by
    intro k ψ X₀ hX₀
    obtain ⟨Y, hY, hsub, hrefl⟩ :=
      h2 V mem hZF_sat φS hTransS hSTrich hSUnion hCoverS k ψ X₀ hX₀
    refine ⟨Y, hY, hsub, fun q => ?_⟩
    rw [ev_eq_raw (fun a b : {x // mem x Y} => mem a.1 b.1) ψ q,
        ev_eq_raw (fun a b : {x // P x} => mem a.1 b.1) ψ _]
    exact hrefl q
  have hWOS : ∀ X, S X → ∃ R, P R ∧
      (∀ a b, mem a X → mem b X →
        ¬ ((∃ q, mem q R ∧ exEv.choose mem ![q, a, b] Empty.elim SetTheory.kpair.dfn) ∧
           (∃ q, mem q R ∧ exEv.choose mem ![q, b, a] Empty.elim SetTheory.kpair.dfn))) ∧
      ∀ W, (∀ w, mem w W → mem w X) → (∃ w, mem w W) →
        ∃ m, mem m W ∧ ∀ y, mem y W → y ≠ m →
          ∃ q, mem q R ∧ exEv.choose mem ![q, m, y] Empty.elim SetTheory.kpair.dfn := by
    intro X hX
    obtain ⟨R, hRP, hasym, hmin⟩ := hSWO X hX
    refine ⟨R, hRP, ?_, ?_⟩
    · intro a b ha hb ⟨⟨q1, hq1, hp1⟩, ⟨q2, hq2, hp2⟩⟩
      exact hasym a b ha hb
        ⟨⟨q1, hq1, (ev_eq_raw mem SetTheory.kpair.dfn ![q1, a, b]).mp hp1⟩,
         ⟨q2, hq2, (ev_eq_raw mem SetTheory.kpair.dfn ![q2, b, a]).mp hp2⟩⟩
    · intro W hWX hWne
      obtain ⟨m, hmW, hm⟩ := hmin W hWX hWne
      refine ⟨m, hmW, fun y hy hne => ?_⟩
      obtain ⟨q, hqR, hqp⟩ := hm y hy hne
      exact ⟨q, hqR, (ev_eq_raw mem SetTheory.kpair.dfn ![q, m, y]).mpr hqp⟩
  -- Transitivity of P
  have hPTrans : ∀ x y : V, P y → mem x y → P x := by
    rintro x y ⟨X, hSX, hyX⟩ hxy
    exact ⟨X, hSX, hTransS X hSX x y hyX hxy⟩
  have hExtV := zf_ext hZF
  have hPairV := zf_pair hZF
  have hUnionV := zf_union hZF
  have hPowerV := zf_power hZF
  have hFoundV := zf_found hZF
  -- Formula φP defining P in V
  let φP : SetTheorySemisentence 1 :=
    ∃¹ ((Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim ▹ φS) ⋏
        (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#1, #0]))
  have hφP_iff : ∀ x : V, P x ↔ exEv.choose mem ![x] Empty.elim φP := by
    intro x
    dsimp only [φP, P, S]
    rw [ev_exs]
    refine exists_congr fun X => ?_
    rw [ev_and, ev_rew, ev_mem_op, tv_bvar, tv_bvar]
    have he1 : (fun i : Fin 1 => exTv.choose (X :> ![x]) Empty.elim
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim #i)) = ![X] := by
      funext i; fin_cases i; exact tv_bvar _ _ 0
    have hε1 : (fun z : Empty => exTv.choose (X :> ![x]) Empty.elim
        (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim &z)) = Empty.elim := by
      funext z; exact z.elim
    rw [he1, hε1]
    exact and_congr (ev_eq_raw mem φS ![X]).symm Iff.rfl
  -- Helper: covering any finite tuple of elements of P by a single stage X
  have hCoverFin : ∀ {k : ℕ} (p : Fin k → {x // P x}),
      ∃ X : V, S X ∧ ∀ i : Fin k, mem (p i).1 X := by
    intro k p
    obtain ⟨A, hA⟩ := v_finset_of_pred hZF p
    obtain ⟨X, hSX, hAX⟩ := hCoverS A (fun a ha => let ⟨i, hi⟩ := (hA a).mp ha; hi ▸ (p i).2)
    exact ⟨X, hSX, fun i => hAX (p i).1 ((hA (p i).1).mpr ⟨i, rfl⟩)⟩
  -- Helper: every stage belongs to P
  have hStageInP : ∀ X : V, S X → P X := by
    intro X hSX
    obtain ⟨Y, hSY, Z, hZY, hZ⟩ := hDefS X hSX 0 ⊤ Fin.elim0
    have hZX : Z = X := (hExtV Z X).mpr fun u =>
      (hZ u).trans ⟨fun ⟨hu, _⟩ => hu, fun hu => ⟨hu, (ev_verum _ _ _).mpr trivial⟩⟩
    rw [hZX] at hZY
    exact ⟨Y, hSY, hZY⟩
  -- Abbreviation for inner-model membership
  let memL : {x // P x} → {x // P x} → Prop := fun a b => mem a.1 b.1
  -- 1. Empty set in L
  have hEmptyL : ∃ e : {x // P x}, ∀ y : {x // P x}, ¬ memL y e := by
    obtain ⟨eV, heV⟩ := zf_empty hZF
    obtain ⟨X, hSX, _⟩ := hCoverS eV (fun a ha => False.elim (heV a ha))
    obtain ⟨Y, hSY, Z, hZY, hZ⟩ := hDefS X hSX 0 ⊥ Fin.elim0
    refine ⟨⟨Z, ⟨Y, hSY, hZY⟩⟩, fun y hy => ?_⟩
    obtain ⟨_, hbot⟩ := (hZ y.1).mp hy
    exact (ev_falsum _ _ _).mp hbot
  obtain ⟨eL, heL⟩ := hEmptyL
  have heL_V : ∀ y : V, ¬ mem y eL.1 := fun y hy => heL ⟨y, hPTrans y eL.1 eL.2 hy⟩ hy
  -- 2. Extensionality in L
  have hExtL : ∀ x y : {x // P x}, x = y ↔ ∀ z : {x // P x}, memL z x ↔ memL z y := by
    intro x y
    refine ⟨fun h => by subst h; intro _; exact Iff.rfl, fun h => Subtype.ext ?_⟩
    exact (hExtV x.1 y.1).mpr fun z =>
      ⟨fun hzx => (h ⟨z, hPTrans z x.1 x.2 hzx⟩).mp hzx,
       fun hzy => (h ⟨z, hPTrans z y.1 y.2 hzy⟩).mpr hzy⟩
  -- 3. Pairing in L
  have hPairL : ∀ x y : {x // P x}, ∃ z : {x // P x}, ∀ w : {x // P x}, memL w z ↔ w = x ∨ w = y := by
    intro x y
    obtain ⟨X, hSX, hxyX⟩ := hCoverFin ![x, y]
    let ψPair : SetTheorySemisentence 3 :=
      (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![#0, #1]) ⋎
      (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![#0, #2])
    let p : Fin 2 → {u // mem u X} := ![⟨x.1, hxyX 0⟩, ⟨y.1, hxyX 1⟩]
    obtain ⟨Y, hSY, Z, hZY, hZ⟩ := hDefS X hSX 2 ψPair p
    refine ⟨⟨Z, ⟨Y, hSY, hZY⟩⟩, fun w => ?_⟩
    change mem w.1 Z ↔ w = x ∨ w = y
    rw [hZ w.1]
    constructor
    · rintro ⟨hwX, hdisj⟩
      dsimp only [ψPair] at hdisj
      rw [ev_or, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar] at hdisj
      rcases hdisj with h1 | h2
      · change (⟨w.1, hwX⟩ : {u // mem u X}) = ⟨x.1, hxyX 0⟩ at h1
        exact Or.inl (Subtype.ext (congrArg (fun q : {u // mem u X} => q.1) h1))
      · change (⟨w.1, hwX⟩ : {u // mem u X}) = ⟨y.1, hxyX 1⟩ at h2
        exact Or.inr (Subtype.ext (congrArg (fun q : {u // mem u X} => q.1) h2))
    · rintro (rfl | rfl)
      · refine ⟨hxyX 0, ?_⟩
        dsimp only [ψPair]
        rw [ev_or, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar]
        exact Or.inl rfl
      · refine ⟨hxyX 1, ?_⟩
        dsimp only [ψPair]
        rw [ev_or, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar]
        exact Or.inr rfl
  -- 4. Union in L
  have hUnionL : ∀ x : {x // P x}, ∃ y : {x // P x}, ∀ z : {x // P x},
      memL z y ↔ ∃ w : {x // P x}, memL w x ∧ memL z w := by
    intro x
    obtain ⟨X, hSX, hxX⟩ := x.2
    let ψUn : SetTheorySemisentence 2 :=
      Semiformula.bexsMem #1
        (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#1, #0])
    obtain ⟨Y, hSY, Z, hZY, hZ⟩ := hDefS X hSX 1 ψUn ![⟨x.1, hxX⟩]
    refine ⟨⟨Z, ⟨Y, hSY, hZY⟩⟩, fun z => ?_⟩
    change mem z.1 Z ↔ ∃ w : {x // P x}, mem w.1 x.1 ∧ mem z.1 w.1
    rw [hZ z.1]
    constructor
    · rintro ⟨hzX, hUn⟩
      dsimp only [ψUn] at hUn
      rw [ev_bexsMem, tv_bvar] at hUn
      obtain ⟨w, hwx, hzw⟩ := hUn
      rw [ev_mem_op, tv_bvar, tv_bvar] at hzw
      exact ⟨⟨w.1, ⟨X, hSX, w.2⟩⟩, hwx, hzw⟩
    · rintro ⟨w, hwx, hzw⟩
      have hwX : mem w.1 X := hTransS X hSX w.1 x.1 hxX hwx
      have hzX : mem z.1 X := hTransS X hSX z.1 w.1 hwX hzw
      refine ⟨hzX, ?_⟩
      dsimp only [ψUn]
      rw [ev_bexsMem, tv_bvar]
      refine ⟨⟨w.1, hwX⟩, hwx, ?_⟩
      rw [ev_mem_op, tv_bvar, tv_bvar]
      exact hzw
  -- 5. Separation Schema in L (from H2 Reflection + H1 Def-closure)
  have hSepL : ∀ (φ : SetTheorySemiproposition 1) (ε : ℕ → {x // P x}) (a : {x // P x}),
      ∃ y : {x // P x}, ∀ z : {x // P x}, memL z y ↔ memL z a ∧ exEv.choose memL ![z] ε φ := by
    intro φ ε a
    obtain ⟨k, ψ, hψ⟩ := exCloseFvars φ
    let pP : Fin (k + 1) → {x // P x} := a :> fun i : Fin k => ε i.val
    obtain ⟨X₀, hSX₀, hcov⟩ := hCoverFin pP
    obtain ⟨Y, hSY, hsub, hrefl⟩ := hReflS (k + 1) ψ X₀ hSX₀
    have haY : mem a.1 Y := hsub a.1 (hcov 0)
    have hpY : ∀ i : Fin k, mem (ε i.val).1 Y := fun i => hsub (ε i.val).1 (hcov i.succ)
    let ψ' : SetTheorySemisentence (k + 2) :=
      (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#0, #1]) ⋏
      (Rew.bind (#0 :> fun i : Fin k => (#(i.succ.succ) : Semiterm ℒₛₑₜ Empty (k + 2))) Empty.elim ▹ ψ)
    let paramsY : Fin (k + 1) → {u // mem u Y} := ⟨a.1, haY⟩ :> fun i : Fin k => ⟨(ε i.val).1, hpY i⟩
    obtain ⟨W, hSW, Z, hZW, hZ⟩ := hDefS Y hSY (k + 1) ψ' paramsY
    refine ⟨⟨Z, ⟨W, hSW, hZW⟩⟩, fun z => ?_⟩
    change mem z.1 Z ↔ mem z.1 a.1 ∧ exEv.choose memL ![z] ε φ
    rw [hZ z.1]
    constructor
    · rintro ⟨hzY, hand⟩
      dsimp only [ψ'] at hand
      rw [ev_and, ev_mem_op, tv_bvar, tv_bvar, ev_rew] at hand
      refine ⟨hand.1, ?_⟩
      let qY : Fin (k + 1) → {u // mem u Y} := ⟨z.1, hzY⟩ :> fun j : Fin k => ⟨(ε j.val).1, hpY j⟩
      have harg : (fun i : Fin (k + 1) =>
          exTv.choose (⟨z.1, hzY⟩ :> paramsY) Empty.elim
            (Rew.bind (#0 :> fun j : Fin k => (#(j.succ.succ) : Semiterm ℒₛₑₜ Empty (k + 2))) Empty.elim #i)) =
          qY := by
        funext i
        cases i using Fin.cases with
        | zero => exact tv_bvar _ _ 0
        | succ j => exact tv_bvar _ _ j.succ.succ
      have hε0 : (fun x : Empty =>
          exTv.choose (⟨z.1, hzY⟩ :> paramsY) Empty.elim
            (Rew.bind (#0 :> fun j : Fin k => (#(j.succ.succ) : Semiterm ℒₛₑₜ Empty (k + 2))) Empty.elim &x)) =
          Empty.elim := by funext x; exact x.elim
      rw [harg, hε0] at hand
      have hL := (hrefl qY).mp hand.2
      have hqL : (fun i : Fin (k + 1) =>
          (⟨(qY i).1, ⟨Y, hSY, (qY i).2⟩⟩ : {x // P x})) =
          z :> fun j : Fin k => ε j.val := by
        funext i
        cases i using Fin.cases with
        | zero => exact Subtype.ext rfl
        | succ j => exact Subtype.ext rfl
      rw [hqL] at hL
      exact (hψ {x // P x} memL ε z).mp hL
    · rintro ⟨hza, hφz⟩
      have hzY : mem z.1 Y := hTransS Y hSY z.1 a.1 haY hza
      refine ⟨hzY, ?_⟩
      dsimp only [ψ']
      rw [ev_and, ev_mem_op, tv_bvar, tv_bvar, ev_rew]
      refine ⟨hza, ?_⟩
      let qY : Fin (k + 1) → {u // mem u Y} := ⟨z.1, hzY⟩ :> fun j : Fin k => ⟨(ε j.val).1, hpY j⟩
      have harg : (fun i : Fin (k + 1) =>
          exTv.choose (⟨z.1, hzY⟩ :> paramsY) Empty.elim
            (Rew.bind (#0 :> fun j : Fin k => (#(j.succ.succ) : Semiterm ℒₛₑₜ Empty (k + 2))) Empty.elim #i)) =
          qY := by
        funext i
        cases i using Fin.cases with
        | zero => exact tv_bvar _ _ 0
        | succ j => exact tv_bvar _ _ j.succ.succ
      have hε0 : (fun x : Empty =>
          exTv.choose (⟨z.1, hzY⟩ :> paramsY) Empty.elim
            (Rew.bind (#0 :> fun j : Fin k => (#(j.succ.succ) : Semiterm ℒₛₑₜ Empty (k + 2))) Empty.elim &x)) =
          Empty.elim := by funext x; exact x.elim
      rw [harg, hε0]
      have hL := (hψ {x // P x} memL ε z).mpr hφz
      have hqL : (fun i : Fin (k + 1) =>
          (⟨(qY i).1, ⟨Y, hSY, (qY i).2⟩⟩ : {x // P x})) =
          z :> fun j : Fin k => ε j.val := by
        funext i
        cases i using Fin.cases with
        | zero => exact Subtype.ext rfl
        | succ j => exact Subtype.ext rfl
      rw [← hqL] at hL
      exact (hrefl qY).mpr hL
  -- 6. Infinity in L (via Δ₀ isFinOrd, ω^V-induction, Foundation, upward-covering, Def-closure)
  have hInfL : ∃ I : {x // P x},
      (∀ e : {x // P x}, (∀ y : {x // P x}, ¬ memL y e) → memL e I) ∧
      (∀ x : {x // P x}, memL x I → ∀ x' : {x // P x},
        (∀ z : {x // P x}, memL z x' ↔ z = x ∨ memL z x) → memL x' I) := by
    obtain ⟨I₀, hI₀_emp, hI₀_succ⟩ := zf_inf hZF
    -- Build minimal inductive set ωV inside I₀ via V-Separation on isInω
    let isInω : SetTheorySemisentence 1 :=
      ∀¹ ((Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim ▹ SetTheory.IsInductive.dfn) 🡒
          Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#1, #0])
    obtain ⟨ωV, hωV⟩ := zf_sep hZF (Rew.emb ▹ isInω) (fun _ => eL.1) I₀
    have hω_eval : ∀ x : V,
        exEv.choose mem ![x] (fun _ : ℕ => eL.1) (Rew.emb ▹ isInω) ↔
          ∀ J : V, ((∀ e, (∀ y, ¬ mem y e) → mem e J) ∧
            (∀ u, mem u J → ∀ u', (∀ z, mem z u' ↔ z = u ∨ mem z u) → mem u' J)) → mem x J := by
      intro x
      rw [ev_rew]
      have he1 : (fun i : Fin 1 => exTv.choose ![x] (fun _ : ℕ => eL.1)
          (Rew.emb (#i : Semiterm ℒₛₑₜ Empty 1))) = ![x] := by
        funext i; fin_cases i; exact tv_bvar _ _ 0
      have hε1 : (fun z : Empty => exTv.choose ![x] (fun _ : ℕ => eL.1)
          (Rew.emb (&z : Semiterm ℒₛₑₜ Empty 1))) = Empty.elim := by
        funext z; exact z.elim
      rw [he1, hε1]
      dsimp only [isInω]
      rw [ev_all]
      refine forall_congr' fun J => ?_
      rw [ev_imp, ev_rew, ev_mem_op, tv_bvar, tv_bvar]
      refine imp_congr ?_ Iff.rfl
      have hJ : (fun i : Fin 1 => exTv.choose (J :> ![x]) Empty.elim
          (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim #i)) = ![J] := by
        funext i; fin_cases i; exact tv_bvar _ _ 0
      have hJε : (fun z : Empty => exTv.choose (J :> ![x]) Empty.elim
          (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ Empty 2)) Empty.elim &z)) = Empty.elim := by
        funext z; exact z.elim
      rw [hJ, hJε]
      unfold SetTheory.IsInductive.dfn
      rw [ev_and]
      refine and_congr ?_ ?_
      · rw [ev_all]
        refine forall_congr' fun e => ?_
        rw [ev_imp, ev_isEmpty, ev_mem_op, tv_bvar, tv_bvar]
        rfl
      · rw [ev_ballMem, tv_bvar]
        refine forall_congr' fun u => imp_congr Iff.rfl ?_
        rw [ev_all]
        refine forall_congr' fun u' => ?_
        rw [ev_imp, ev_isSucc, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
        rfl
    have hω_iff : ∀ x : V, mem x ωV ↔
        ∀ J : V, ((∀ e, (∀ y, ¬ mem y e) → mem e J) ∧
          (∀ u, mem u J → ∀ u', (∀ z, mem z u' ↔ z = u ∨ mem z u) → mem u' J)) → mem x J := by
      intro x
      rw [hωV, hω_eval]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h I₀ ⟨hI₀_emp, hI₀_succ⟩, h⟩⟩
    have hω_emp : ∀ e : V, (∀ y, ¬ mem y e) → mem e ωV :=
      fun e he => (hω_iff e).mpr fun J hJ => hJ.1 e he
    have hω_succ : ∀ u : V, mem u ωV → ∀ u' : V, (∀ z, mem z u' ↔ z = u ∨ mem z u) → mem u' ωV :=
      fun u hu u' hu' => (hω_iff u').mpr fun J hJ => hJ.2 u ((hω_iff u).mp hu J hJ) u' hu'
    -- Every element of ωV satisfies P (by ωV-induction using V-Separation on φP)
    have hω_sub_P : ∀ x : V, mem x ωV → P x := by
      obtain ⟨J, hJ⟩ := zf_sep hZF (Rew.emb ▹ φP) (fun _ => eL.1) ωV
      have hJ_iff : ∀ x : V, mem x J ↔ mem x ωV ∧ P x := by
        intro x
        rw [hJ, ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose ![x] (fun _ : ℕ => eL.1)
            (Rew.emb (#i : Semiterm ℒₛₑₜ Empty 1))) = ![x] := by
          funext i; fin_cases i; exact tv_bvar _ _ 0
        have hε1 : (fun z : Empty => exTv.choose ![x] (fun _ : ℕ => eL.1)
            (Rew.emb (&z : Semiterm ℒₛₑₜ Empty 1))) = Empty.elim := by
          funext z; exact z.elim
        rw [he1, hε1, ← hφP_iff x]
      have hJ_ind : (∀ e, (∀ y, ¬ mem y e) → mem e J) ∧
          (∀ u, mem u J → ∀ u', (∀ z, mem z u' ↔ z = u ∨ mem z u) → mem u' J) := by
        refine ⟨fun e he => (hJ_iff e).mpr ⟨hω_emp e he, ?_⟩, fun u hu u' hu' => ?_⟩
        · have heq : e = eL.1 := (hExtV e eL.1).mpr fun z => ⟨fun h => False.elim (he z h), fun h => False.elim (heL_V z h)⟩
          rw [heq]; exact eL.2
        · obtain ⟨huω, huP⟩ := (hJ_iff u).mp hu
          refine (hJ_iff u').mpr ⟨hω_succ u huω u' hu', ?_⟩
          obtain ⟨sL, hsL⟩ := hPairL ⟨u, huP⟩ ⟨u, huP⟩
          obtain ⟨dL, hdL⟩ := hPairL sL ⟨u, huP⟩
          obtain ⟨u'L, hu'L⟩ := hUnionL dL
          have heq : u' = u'L.1 := (hExtV u' u'L.1).mpr fun z => by
            rw [hu' z]
            constructor
            · rintro (rfl | hzu)
              · exact (hu'L ⟨z, huP⟩).mpr ⟨sL, (hdL sL).mpr (Or.inl rfl), (hsL ⟨z, huP⟩).mpr (Or.inl rfl)⟩
              · exact (hu'L ⟨z, hPTrans z u huP hzu⟩).mpr ⟨⟨u, huP⟩, (hdL ⟨u, huP⟩).mpr (Or.inr rfl), hzu⟩
            · intro hz
              obtain ⟨w, hwd, hzw⟩ := (hu'L ⟨z, hPTrans z u'L.1 u'L.2 hz⟩).mp hz
              rcases (hdL w).mp hwd with rfl | rfl
              · rcases (hsL ⟨z, hPTrans z u'L.1 u'L.2 hz⟩).mp hzw with h1 | h1 <;>
                  exact Or.inl (congrArg Subtype.val h1)
              · exact Or.inr hzw
          rw [heq]; exact u'L.2
      intro x hx
      exact ((hJ_iff x).mp ((hω_iff x).mp hx J hJ_ind)).2
    -- Every element of ωV satisfies isFinOrd (by ωV-induction using V-Separation on exIsFinOrd.choose)
    have hω_to_FO : ∀ x : V, mem x ωV → exEv.choose mem ![x] Empty.elim exIsFinOrd.choose := by
      obtain ⟨J, hJ⟩ := zf_sep hZF (Rew.emb ▹ exIsFinOrd.choose) (fun _ => eL.1) ωV
      have hJ_iff : ∀ x : V, mem x J ↔ mem x ωV ∧ exEv.choose mem ![x] Empty.elim exIsFinOrd.choose := by
        intro x
        rw [hJ, ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose ![x] (fun _ : ℕ => eL.1)
            (Rew.emb (#i : Semiterm ℒₛₑₜ Empty 1))) = ![x] := by
          funext i; fin_cases i; exact tv_bvar _ _ 0
        have hε1 : (fun z : Empty => exTv.choose ![x] (fun _ : ℕ => eL.1)
            (Rew.emb (&z : Semiterm ℒₛₑₜ Empty 1))) = Empty.elim := by
          funext z; exact z.elim
        rw [he1, hε1]
      have hJ_ind : (∀ e, (∀ y, ¬ mem y e) → mem e J) ∧
          (∀ u, mem u J → ∀ u', (∀ z, mem z u' ↔ z = u ∨ mem z u) → mem u' J) := by
        refine ⟨fun e he => (hJ_iff e).mpr ⟨hω_emp e he, ?_⟩, fun u hu u' hu' => ?_⟩
        · rw [exIsFinOrd.choose_spec]
          exact ⟨⟨fun a ha => False.elim (he a ha), fun a ha => False.elim (he a ha)⟩,
            ⟨Or.inl he, fun a ha => False.elim (he a ha)⟩⟩
        · obtain ⟨huω, huFO⟩ := (hJ_iff u).mp hu
          refine (hJ_iff u').mpr ⟨hω_succ u huω u' hu', ?_⟩
          rw [exIsFinOrd.choose_spec] at huFO ⊢
          rcases huFO with ⟨⟨hTrU, hElTrU⟩, ⟨hZSU, hElZSU⟩⟩
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
          · intro a ha b hb
            rcases (hu' a).mp ha with rfl | hau
            · exact (hu' b).mpr (Or.inr hb)
            · exact (hu' b).mpr (Or.inr (hTrU a hau b hb))
          · intro a ha b hb c hc
            rcases (hu' a).mp ha with rfl | hau
            · exact hTrU b hb c hc
            · exact hElTrU a hau b hb c hc
          · exact Or.inr ⟨u, (hu' u).mpr (Or.inl rfl), fun z hz => (hu' z).mp hz,
              fun z hz => (hu' z).mpr (Or.inr hz)⟩
          · intro v hv
            rcases (hu' v).mp hv with rfl | hvu
            · exact hZSU
            · exact hElZSU v hvu
      intro x hx
      exact ((hJ_iff x).mp ((hω_iff x).mp hx J hJ_ind)).2
    -- Conversely, every set satisfying isFinOrd belongs to ωV (by Foundation in V!)
    have hFO_to_ω : ∀ x : V, exEv.choose mem ![x] Empty.elim exIsFinOrd.choose → mem x ωV := by
      intro x hxFO
      by_contra hxnω
      obtain ⟨sx, hsx⟩ := hPairV x x
      obtain ⟨dx, hdx⟩ := hPairV sx x
      obtain ⟨x', hx'⟩ := hUnionV dx
      have hx'_iff : ∀ z : V, mem z x' ↔ z = x ∨ mem z x := by
        intro z
        rw [hx']
        constructor
        · rintro ⟨w, hwd, hzw⟩
          rcases (hdx w).mp hwd with rfl | rfl
          · rcases (hsx z).mp hzw with rfl | rfl <;> exact Or.inl rfl
          · exact Or.inr hzw
        · rintro (rfl | hzx)
          · exact ⟨sx, (hdx sx).mpr (Or.inl rfl), (hsx _).mpr (Or.inl rfl)⟩
          · exact ⟨x, (hdx x).mpr (Or.inr rfl), hzx⟩
      obtain ⟨B, hB⟩ := zf_sep hZF (∼(Rew.emb ▹ isInω)) (fun _ => eL.1) x'
      have hB_iff : ∀ u : V, mem u B ↔ (u = x ∨ mem u x) ∧ ¬ mem u ωV := by
        intro u
        rw [hB, hx'_iff, ev_neg, hω_eval, ← hω_iff u]
      have hBne : ∃ u, mem u B := ⟨x, (hB_iff x).mpr ⟨Or.inl rfl, hxnω⟩⟩
      obtain ⟨m, hmB, hmMin⟩ := hFoundV B hBne
      obtain ⟨hmx, hmnω⟩ := (hB_iff m).mp hmB
      rw [exIsFinOrd.choose_spec] at hxFO
      rcases hxFO with ⟨⟨hTrX, _⟩, ⟨hZSX, hElZSX⟩⟩
      have hZSm : (∀ a, ¬ mem a m) ∨
          ∃ y, mem y m ∧ (∀ z, mem z m → z = y ∨ mem z y) ∧ (∀ z, mem z y → mem z m) := by
        rcases hmx with rfl | hmx'
        · exact hZSX
        · exact hElZSX m hmx'
      rcases hZSm with hmEmp | ⟨y, hym, h1, h2⟩
      · exact hmnω (hω_emp m hmEmp)
      · have hyx : mem y x := by
          rcases hmx with rfl | hmx'
          · exact hym
          · exact hTrX m hmx' y hym
        have hyω : mem y ωV := by
          by_contra hynω
          exact hmMin y ((hB_iff y).mpr ⟨Or.inr hyx, hynω⟩) hym
        have hmSucc : ∀ z, mem z m ↔ z = y ∨ mem z y :=
          fun z => ⟨h1 z, fun h => by rcases h with rfl | hzy; exact hym; exact h2 z hzy⟩
        exact hmnω (hω_succ y hyω m hmSucc)
    -- Upward-cover ωV by a stage X, carve out ωV using Def-closure on Δ₀ isFinOrd
    obtain ⟨X, hSX, hωX⟩ := hCoverS ωV hω_sub_P
    obtain ⟨Y, hSY, Z, hZY, hZ⟩ := hDefS X hSX 0 exIsFinOrd.choose Fin.elim0
    have hZω : Z = ωV := (hExtV Z ωV).mpr fun u => by
      rw [hZ u]
      constructor
      · rintro ⟨huX, hFO⟩
        have hFO_V := (isFinOrd_abs_trans (fun v => mem v X) (hTransS X hSX) u huX).mp
          ((ev_congr _ exIsFinOrd.choose (funext fun i => by fin_cases i; rfl) rfl).mp hFO)
        exact hFO_to_ω u hFO_V
      · intro huω
        have huX : mem u X := hωX u huω
        refine ⟨huX, ?_⟩
        have hFO_X := (isFinOrd_abs_trans (fun v => mem v X) (hTransS X hSX) u huX).mpr
          (hω_to_FO u huω)
        exact (ev_congr _ exIsFinOrd.choose (funext fun i => by fin_cases i; rfl) rfl).mpr hFO_X
    rw [hZω] at hZY
    have hωP : P ωV := ⟨Y, hSY, hZY⟩
    refine ⟨⟨ωV, hωP⟩, ?_, ?_⟩
    · intro e he
      exact hω_emp e.1 (fun y hy => he ⟨y, hPTrans y e.1 e.2 hy⟩ hy)
    · intro x hx x' hx'
      refine hω_succ x.1 hx x'.1 fun z => ?_
      constructor
      · intro hzx'
        rcases (hx' ⟨z, hPTrans z x'.1 x'.2 hzx'⟩).mp hzx' with hEq | hMem
        · exact Or.inl (congrArg Subtype.val hEq)
        · exact Or.inr hMem
      · rintro (rfl | hzx)
        · exact (hx' x).mpr (Or.inl rfl)
        · exact (hx' ⟨z, hPTrans z x.1 x.2 hzx⟩).mpr (Or.inr hzx)
  -- 7. Power Set in L
  have hPowerL : ∀ x : {x // P x}, ∃ y : {x // P x},
      ∀ z : {x // P x}, memL z y ↔ ∀ u : {x // P x}, memL u z → memL u x := by
    intro x
    obtain ⟨pV, hpV⟩ := hPowerV x.1
    obtain ⟨A, hA⟩ := zf_sep hZF (Rew.emb ▹ φP) (fun _ => eL.1) pV
    have hA_iff : ∀ z : V, mem z A ↔ (∀ u : V, mem u z → mem u x.1) ∧ P z := by
      intro z
      rw [hA, hpV, ev_rew]
      have he1 : (fun i : Fin 1 => exTv.choose ![z] (fun _ : ℕ => eL.1)
          (Rew.emb (#i : Semiterm ℒₛₑₜ Empty 1))) = ![z] := by
        funext i; fin_cases i; exact tv_bvar _ _ 0
      have hε1 : (fun w : Empty => exTv.choose ![z] (fun _ : ℕ => eL.1)
          (Rew.emb (&w : Semiterm ℒₛₑₜ Empty 1))) = Empty.elim := by
        funext w; exact w.elim
      rw [he1, hε1, ← hφP_iff z]
    obtain ⟨sx, hsx⟩ := hPairV x.1 x.1
    obtain ⟨d, hd⟩ := hPairV sx A
    obtain ⟨Ax, hAx⟩ := hUnionV d
    have hAx_P : ∀ a : V, mem a Ax → P a := by
      intro a ha
      obtain ⟨w, hwd, haw⟩ := (hAx a).mp ha
      rcases (hd w).mp hwd with rfl | rfl
      · rcases (hsx a).mp haw with rfl | rfl <;> exact x.2
      · exact ((hA_iff a).mp haw).2
    obtain ⟨X, hSX, hAxX⟩ := hCoverS Ax hAx_P
    have hxX : mem x.1 X := hAxX x.1 ((hAx x.1).mpr ⟨sx, (hd sx).mpr (Or.inl rfl), (hsx x.1).mpr (Or.inl rfl)⟩)
    obtain ⟨Y, hSY, Z, hZY, hZ⟩ := hDefS X hSX 1 isSubsetOf ![⟨x.1, hxX⟩]
    refine ⟨⟨Z, ⟨Y, hSY, hZY⟩⟩, fun z => ?_⟩
    change mem z.1 Z ↔ ∀ u : {x // P x}, mem u.1 z.1 → mem u.1 x.1
    rw [hZ z.1]
    constructor
    · rintro ⟨hzX, hsub⟩ u huz
      unfold isSubsetOf at hsub
      rw [ev_ballMem, tv_bvar] at hsub
      have h1 := hsub ⟨u.1, hTransS X hSX u.1 z.1 hzX huz⟩ huz
      rw [ev_mem_op, tv_bvar, tv_bvar] at h1
      exact h1
    · intro hsub
      have hsubV : ∀ u : V, mem u z.1 → mem u x.1 := fun u huz => hsub ⟨u, hPTrans u z.1 z.2 huz⟩ huz
      have hzA : mem z.1 A := (hA_iff z.1).mpr ⟨hsubV, z.2⟩
      have hzX : mem z.1 X := hAxX z.1 ((hAx z.1).mpr ⟨A, (hd A).mpr (Or.inr rfl), hzA⟩)
      refine ⟨hzX, ?_⟩
      unfold isSubsetOf
      rw [ev_ballMem, tv_bvar]
      intro u huz
      rw [ev_mem_op, tv_bvar, tv_bvar]
      exact hsubV u.1 huz
  -- 8. Replacement Schema in L (via exRelativize + V-Replacement + upward-covering + L-Separation)
  have hRepL : ∀ (φ : SetTheorySemiproposition 2) (ε : ℕ → {x // P x}),
      (∀ x : {x // P x}, ∃! y : {x // P x}, exEv.choose memL ![x, y] ε φ) →
      ∀ A : {x // P x}, ∃ Y : {x // P x},
        ∀ y : {x // P x}, memL y Y ↔ ∃ x : {x // P x}, memL x A ∧ exEv.choose memL ![x, y] ε φ := by
    obtain ⟨rel, hrel⟩ := exRelativize φP
    intro φ ε hfunc A
    let φP0 : SetTheorySemiproposition 2 :=
      Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim ▹ φP
    let φP1 : SetTheorySemiproposition 2 :=
      Rew.bind (fun _ : Fin 1 => (#1 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim ▹ φP
    let isEmp1 : SetTheorySemiproposition 2 :=
      Rew.bind (fun _ : Fin 1 => (#1 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim ▹ isEmpty
    let ψRep : SetTheorySemiproposition 2 :=
      (φP0 ⋏ (φP1 ⋏ rel φ)) ⋎ ((∼φP0) ⋏ isEmp1)
    have hψRep_iff : ∀ x y : V,
        exEv.choose mem ![x, y] (fun j => (ε j).1) ψRep ↔
          (∃ hx : P x, ∃ hy : P y, exEv.choose memL ![⟨x, hx⟩, ⟨y, hy⟩] ε φ) ∨
          (¬ P x ∧ ∀ z : V, ¬ mem z y) := by
      intro x y
      dsimp only [ψRep]
      rw [ev_or, ev_and, ev_and, ev_and, ev_neg]
      have h0 : exEv.choose mem ![x, y] (fun j => (ε j).1) φP0 ↔ P x := by
        dsimp only [φP0]
        rw [ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose ![x, y] (fun j => (ε j).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim #i)) = ![x] := by
          funext i; fin_cases i; exact tv_bvar _ _ 0
        have hε1 : (fun z : Empty => exTv.choose ![x, y] (fun j => (ε j).1)
            (Rew.bind (fun _ : Fin 1 => (#0 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim &z)) = Empty.elim := by
          funext z; exact z.elim
        rw [he1, hε1, ← hφP_iff x]
      have h1 : exEv.choose mem ![x, y] (fun j => (ε j).1) φP1 ↔ P y := by
        dsimp only [φP1]
        rw [ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose ![x, y] (fun j => (ε j).1)
            (Rew.bind (fun _ : Fin 1 => (#1 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim #i)) = ![y] := by
          funext i; fin_cases i; exact tv_bvar _ _ 1
        have hε1 : (fun z : Empty => exTv.choose ![x, y] (fun j => (ε j).1)
            (Rew.bind (fun _ : Fin 1 => (#1 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim &z)) = Empty.elim := by
          funext z; exact z.elim
        rw [he1, hε1, ← hφP_iff y]
      have hemp : exEv.choose mem ![x, y] (fun j => (ε j).1) isEmp1 ↔ ∀ z : V, ¬ mem z y := by
        dsimp only [isEmp1]
        rw [ev_rew]
        have he1 : (fun i : Fin 1 => exTv.choose ![x, y] (fun j => (ε j).1)
            (Rew.bind (fun _ : Fin 1 => (#1 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim #i)) = ![y] := by
          funext i; fin_cases i; exact tv_bvar _ _ 1
        have hε1 : (fun z : Empty => exTv.choose ![x, y] (fun j => (ε j).1)
            (Rew.bind (fun _ : Fin 1 => (#1 : Semiterm ℒₛₑₜ ℕ 2)) Empty.elim &z)) = Empty.elim := by
          funext z; exact z.elim
        rw [he1, hε1]
        unfold isEmpty
        rw [ev_all]
        refine forall_congr' fun z => ?_
        rw [ev_neg, ev_mem_op, tv_bvar, tv_bvar]
        rfl
      rw [h0, h1, hemp]
      refine or_congr ?_ Iff.rfl
      constructor
      · rintro ⟨hx, hy, hr⟩
        refine ⟨hx, hy, ?_⟩
        have hvec : (fun i : Fin 2 => ((![⟨x, hx⟩, ⟨y, hy⟩] : Fin 2 → {v // P v}) i).1) = ![x, y] := by
          funext i; fin_cases i <;> rfl
        rw [← hvec] at hr
        exact (hrel mem P hφP_iff ![⟨x, hx⟩, ⟨y, hy⟩] ε φ).mp hr
      · rintro ⟨hx, hy, hr⟩
        refine ⟨hx, hy, ?_⟩
        have hvec : (fun i : Fin 2 => ((![⟨x, hx⟩, ⟨y, hy⟩] : Fin 2 → {v // P v}) i).1) = ![x, y] := by
          funext i; fin_cases i <;> rfl
        rw [← hvec]
        exact (hrel mem P hφP_iff ![⟨x, hx⟩, ⟨y, hy⟩] ε φ).mpr hr
    have hfuncV : ∀ x : V, ∃! y : V, exEv.choose mem ![x, y] (fun j => (ε j).1) ψRep := by
      intro x
      by_cases hx : P x
      · obtain ⟨yL, hyL, huniq⟩ := hfunc ⟨x, hx⟩
        refine ⟨yL.1, (hψRep_iff x yL.1).mpr (Or.inl ⟨hx, yL.2, hyL⟩), fun z hz => ?_⟩
        rcases (hψRep_iff x z).mp hz with ⟨_, hzP, hrz⟩ | ⟨hnx, _⟩
        · exact congrArg Subtype.val (huniq ⟨z, hzP⟩ hrz)
        · exact False.elim (hnx hx)
      · refine ⟨eL.1, (hψRep_iff x eL.1).mpr (Or.inr ⟨hx, heL_V⟩), fun z hz => ?_⟩
        rcases (hψRep_iff x z).mp hz with ⟨hx', _, _⟩ | ⟨_, hzEmp⟩
        · exact False.elim (hx hx')
        · exact (hExtV z eL.1).mpr fun w =>
            ⟨fun hw => False.elim (hzEmp w hw), fun hw => False.elim (heL_V w hw)⟩
    obtain ⟨B, hB⟩ := zf_rep hZF ψRep (fun j => (ε j).1) hfuncV A.1
    have hBP : ∀ y : V, mem y B → P y := by
      intro y hy
      obtain ⟨x, hxA, hxy⟩ := (hB y).mp hy
      have hxP : P x := hPTrans x A.1 A.2 hxA
      rcases (hψRep_iff x y).mp hxy with ⟨_, hyP, _⟩ | ⟨hnx, _⟩
      · exact hyP
      · exact False.elim (hnx hxP)
    obtain ⟨X, hSX, hBX⟩ := hCoverS B hBP
    have hXP : P X := hStageInP X hSX
    let K : ℕ := φ.fvSup
    let ε' : ℕ → {x // P x} := fun j => if j = K then A else ε j
    let φImg : SetTheorySemiproposition 1 :=
      Semiformula.bexsMem (&K : Semiterm ℒₛₑₜ ℕ 1) φ
    obtain ⟨Y, hY⟩ := hSepL φImg ε' ⟨X, hXP⟩
    refine ⟨Y, fun y => ?_⟩
    rw [hY y]
    have hImg_iff : exEv.choose memL ![y] ε' φImg ↔
        ∃ x : {x // P x}, memL x A ∧ exEv.choose memL ![x, y] ε φ := by
      dsimp only [φImg]
      rw [ev_bexsMem, tv_fvar]
      have hK : ε' K = A := if_pos rfl
      rw [hK]
      refine exists_congr fun x => and_congr Iff.rfl ?_
      have he2 : (x :> ![y]) = ![x, y] := by funext i; fin_cases i <;> rfl
      rw [he2]
      refine ev_congr_fv memL φ ![x, y] ε' ε fun j hj => ?_
      have hne : j ≠ K := ne_of_lt (lt_fvSup_of_mem hj)
      exact if_neg hne
    rw [hImg_iff]
    constructor
    · exact fun h => h.2
    · rintro ⟨x, hxA, hxy⟩
      have hyB : mem y.1 B :=
        (hB y.1).mpr ⟨x.1, hxA, (hψRep_iff x.1 y.1).mpr (Or.inl ⟨x.2, y.2, hxy⟩)⟩
      exact ⟨hBX y.1 hyB, ⟨x, hxA, hxy⟩⟩
  -- 9. Axiom of Choice in L (via L-Union + stage well-ordering R ∈ P + kpair_abs + L-Separation)
  have hChoiceL : exEv.choose memL Fin.elim0 Empty.elim Axiom.choice := by
    unfold Axiom.choice
    rw [ev_all]
    intro fam
    rw [ev_imp, ev_and]
    rintro ⟨hNeRaw, hDisjRaw⟩
    have hNe : ∀ W : {x // P x}, memL W fam → ∃ y : {x // P x}, memL y W := by
      intro W hW
      rw [ev_ballMem, tv_bvar] at hNeRaw
      have h1 := hNeRaw W hW
      rw [ev_isNonempty, tv_bvar] at h1
      exact h1
    have hDisj : ∀ W₁ W₂ : {x // P x}, memL W₁ fam → memL W₂ fam →
        (∃ z : {x // P x}, memL z W₁ ∧ memL z W₂) → W₁ = W₂ := by
      intro W₁ W₂ hW₁ hW₂ hz
      rw [ev_ballMem, tv_bvar] at hDisjRaw
      have h1 := hDisjRaw W₁ hW₁
      rw [ev_ballMem, tv_bvar] at h1
      have h2 := h1 W₂ hW₂
      rw [ev_imp, ev_exs, ev_eq_op, tv_bvar, tv_bvar] at h2
      apply h2
      obtain ⟨z, hz1, hz2⟩ := hz
      refine ⟨z, ?_⟩
      rw [ev_and, ev_mem_op, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
      exact ⟨hz1, hz2⟩
    obtain ⟨U, hU⟩ := hUnionL fam
    obtain ⟨X, hSX, hUX⟩ := U.2
    obtain ⟨R, hRP, hRasym, hRmin⟩ := hWOS X hSX
    let RL : {x // P x} := ⟨R, hRP⟩
    let εC : ℕ → {x // P x} := fun j => if j = 0 then fam else RL
    -- φC(z): ∃ W ∈ &0, z ∈ W ∧ ∀ y ∈ W, y ≠ z → ∃ q ∈ &1, kpair(q, z, y)
    let φC : SetTheorySemiproposition 1 :=
      Semiformula.bexsMem (&0 : Semiterm ℒₛₑₜ ℕ 1)
        ((Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![#1, #0]) ⋏
          (Semiformula.ballMem #0
            ((Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![#0, #2]) ⋎
              (Semiformula.bexsMem (&1 : Semiterm ℒₛₑₜ ℕ 3)
                (Rew.bind ![#0, #3, #1] Empty.elim ▹ SetTheory.kpair.dfn)))))
    obtain ⟨C, hC⟩ := hSepL φC εC U
    have hC_iff : ∀ z : {x // P x}, memL z C ↔
        memL z U ∧ ∃ W : {x // P x}, memL W fam ∧ memL z W ∧
          ∀ y : {x // P x}, memL y W → y ≠ z →
            ∃ q : {x // P x}, memL q RL ∧
              exEv.choose mem ![q.1, z.1, y.1] Empty.elim SetTheory.kpair.dfn := by
      intro z
      rw [hC z]
      refine and_congr Iff.rfl ?_
      dsimp only [φC]
      rw [ev_bexsMem, tv_fvar]
      have h0 : εC 0 = fam := if_pos rfl
      rw [h0]
      refine exists_congr fun W => and_congr Iff.rfl ?_
      rw [ev_and, ev_mem_op, tv_bvar, tv_bvar]
      refine and_congr Iff.rfl ?_
      rw [ev_ballMem, tv_bvar]
      refine forall_congr' fun y => imp_congr Iff.rfl ?_
      rw [ev_or, ev_eq_op, tv_bvar, tv_bvar]
      change (y = z ∨ _) ↔ _
      have hne_or : ∀ Q : Prop, (y = z ∨ Q) ↔ (y ≠ z → Q) := fun Q => by tauto
      rw [hne_or]
      refine imp_congr Iff.rfl ?_
      rw [ev_bexsMem, tv_fvar]
      have h1 : εC 1 = RL := if_neg (by decide)
      rw [h1]
      refine exists_congr fun q => and_congr Iff.rfl ?_
      rw [ev_rew]
      have he3 : (fun i : Fin 3 => exTv.choose (q :> y :> W :> ![z]) εC
          (Rew.bind ![#0, #3, #1] Empty.elim #i)) = ![q, z, y] := by
        funext i; fin_cases i <;> exact tv_bvar _ _ _
      have hε3 : (fun w : Empty => exTv.choose (q :> y :> W :> ![z]) εC
          (Rew.bind ![#0, #3, #1] Empty.elim &w)) = Empty.elim := by
        funext w; exact w.elim
      rw [he3, hε3]
      exact kpair_abs hExtV hPairV P hPTrans hPairL q z y
    rw [ev_exs]
    refine ⟨C, ?_⟩
    rw [ev_ballMem, tv_bvar]
    intro W hW
    rw [ev_existsUnique]
    have hWX : ∀ w : V, mem w W.1 → mem w X := fun w hw =>
      have hwU : mem w U.1 := (hU ⟨w, hPTrans w W.1 W.2 hw⟩).mpr ⟨W, hW, hw⟩
      hTransS X hSX w U.1 hUX hwU
    obtain ⟨y0, hy0⟩ := hNe W hW
    obtain ⟨m, hmW, hmMin⟩ := hRmin W.1 hWX ⟨y0.1, hy0⟩
    have hmP : P m := hPTrans m W.1 W.2 hmW
    let mL : {x // P x} := ⟨m, hmP⟩
    have hmU : memL mL U := (hU mL).mpr ⟨W, hW, hmW⟩
    have hmC : memL mL C := (hC_iff mL).mpr ⟨hmU, W, hW, hmW, fun y hyW hne => by
      obtain ⟨q, hqR, hqp⟩ := hmMin y.1 hyW (fun h => hne (Subtype.ext h))
      exact ⟨⟨q, hPTrans q R hRP hqR⟩, hqR, hqp⟩⟩
    refine ⟨mL, ?_, fun x hx => ?_⟩
    · dsimp only
      rw [ev_and, ev_mem_op, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
      exact ⟨hmC, hmW⟩
    · dsimp only at hx
      rw [ev_and, ev_mem_op, ev_mem_op, tv_bvar, tv_bvar, tv_bvar] at hx
      obtain ⟨hxC, hxW⟩ := hx
      obtain ⟨_, W', hW'fam, hxW', hxMin⟩ := (hC_iff x).mp hxC
      have hWW' : W' = W := hDisj W' W hW'fam hW ⟨x, hxW', hxW⟩
      subst hWW'
      by_contra hxm
      obtain ⟨q1, hq1, hp1⟩ := hmMin x.1 hxW (fun h => hxm (Subtype.ext h))
      obtain ⟨q2, hq2, hp2⟩ := hxMin mL hmW (Ne.symm hxm)
      exact hRasym m x.1 (hWX m hmW) (hWX x.1 hxW) ⟨⟨q1, hq1, hp1⟩, ⟨q2, hq2, hp2⟩⟩
  -- Assemble P and verify all axioms of ZFC in ({x // P x}, memL)
  refine ⟨P, hPTrans, fun ψ hψ => (ev_eq_raw memL ψ Fin.elim0).mp ?_⟩
  rcases hψ with hψZF | hψAC
  · cases hψZF with
    | axiom_of_equality _ hφ => exact normal_eq_axioms memL ψ hφ
    | axiom_of_empty_set =>
      unfold Axiom.empty
      rw [ev_exs]
      refine ⟨eL, ?_⟩
      rw [ev_all]
      intro y
      rw [ev_neg, ev_mem_op, tv_bvar, tv_bvar]
      exact heL y
    | axiom_of_extentionality =>
      unfold Axiom.extentionality
      rw [ev_all]; intro x
      rw [ev_all]; intro y
      rw [ev_iff, ev_eq_op, tv_bvar, tv_bvar, ev_all]
      refine (hExtL x y).trans (forall_congr' fun z => ?_)
      rw [ev_iff, ev_mem_op, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
      rfl
    | axiom_of_pairing =>
      unfold Axiom.pairing
      rw [ev_all]; intro x
      rw [ev_all]; intro y
      rw [ev_exs]
      obtain ⟨z, hz⟩ := hPairL x y
      refine ⟨z, ?_⟩
      rw [ev_all]; intro w
      rw [ev_iff, ev_mem_op, ev_or, ev_eq_op, ev_eq_op, tv_bvar, tv_bvar, tv_bvar, tv_bvar]
      exact hz w
    | axiom_of_union =>
      unfold Axiom.union
      rw [ev_all]; intro x
      rw [ev_exs]
      obtain ⟨y, hy⟩ := hUnionL x
      refine ⟨y, ?_⟩
      rw [ev_all]; intro z
      rw [ev_iff, ev_mem_op, ev_bexsMem, tv_bvar, tv_bvar, tv_bvar]
      refine (hy z).trans (exists_congr fun w => and_congr Iff.rfl ?_)
      rw [ev_mem_op, tv_bvar, tv_bvar]
      rfl
    | axiom_of_power_set =>
      unfold Axiom.power
      rw [ev_all]; intro x
      rw [ev_exs]
      obtain ⟨y, hy⟩ := hPowerL x
      refine ⟨y, ?_⟩
      rw [ev_all]; intro z
      rw [ev_iff, ev_mem_op, ev_isSubsetOf, tv_bvar, tv_bvar, tv_bvar]
      exact hy z
    | axiom_of_infinity =>
      unfold Axiom.infinity
      rw [ev_exs]
      obtain ⟨I, hIemp, hIsucc⟩ := hInfL
      refine ⟨I, ?_⟩
      rw [ev_and]
      refine ⟨?_, ?_⟩
      · rw [ev_all]; intro e
        rw [ev_imp, ev_isEmpty, ev_mem_op, tv_bvar, tv_bvar]
        exact hIemp e
      · rw [ev_ballMem, tv_bvar]; intro x hx
        rw [ev_all]; intro x'
        rw [ev_imp, ev_isSucc, ev_mem_op, tv_bvar, tv_bvar, tv_bvar]
        exact hIsucc x hx x'
    | axiom_of_foundation =>
      unfold Axiom.foundation
      rw [ev_all]; intro x
      rw [ev_imp, ev_isNonempty, ev_bexsMem, tv_bvar]
      rintro ⟨y0, hy0⟩
      obtain ⟨y, hyx, hymin⟩ := hFoundV x.1 ⟨y0.1, hy0⟩
      refine ⟨⟨y, hPTrans y x.1 x.2 hyx⟩, hyx, ?_⟩
      rw [ev_ballMem, tv_bvar]; intro z hz
      rw [ev_neg, ev_mem_op, tv_bvar, tv_bvar]
      exact hymin z.1 hz
    | axiom_of_separation φ =>
      unfold Axiom.separationSchema
      refine (ev_univCl_iff memL eL _).mpr fun ε => ?_
      rw [ev_all]; intro a
      rw [ev_exs]
      obtain ⟨y, hy⟩ := hSepL φ ε a
      refine ⟨y, ?_⟩
      rw [ev_all]; intro z
      rw [ev_iff, ev_mem_op, ev_and, ev_mem_op, ev_subst, tv_bvar, tv_bvar, tv_bvar]
      refine (hy z).trans (and_congr Iff.rfl ?_)
      refine ev_congr memL φ ?_ rfl
      funext i; fin_cases i; exact (tv_bvar (z :> y :> a :> Fin.elim0) ε 0).symm
    | axiom_of_replacement φ =>
      unfold Axiom.replacementSchema
      refine (ev_univCl_iff memL eL _).mpr fun ε => ?_
      rw [ev_imp]
      intro hdom
      have hfunc : ∀ x : {x // P x}, ∃! y : {x // P x}, exEv.choose memL ![x, y] ε φ := by
        intro x
        rw [ev_all] at hdom
        have hx := hdom x
        rw [ev_existsUnique] at hx
        obtain ⟨y, hy, huniq⟩ := hx
        refine ⟨y, ?_, fun z hz => ?_⟩
        · rw [ev_subst] at hy
          refine (ev_congr memL φ ?_ rfl).mp hy
          funext i; fin_cases i <;> exact tv_bvar _ _ _
        · apply huniq z
          rw [ev_subst]
          refine (ev_congr memL φ ?_ rfl).mpr hz
          funext i; fin_cases i <;> exact tv_bvar _ _ _
      rw [ev_all]; intro A
      rw [ev_exs]
      obtain ⟨Y, hY⟩ := hRepL φ ε hfunc A
      refine ⟨Y, ?_⟩
      rw [ev_all]; intro y
      rw [ev_iff, ev_mem_op, ev_bexsMem, tv_bvar, tv_bvar, tv_bvar]
      refine (hY y).trans (exists_congr fun x => and_congr Iff.rfl ?_)
      rw [ev_subst]
      refine ev_congr memL φ ?_ rfl
      funext i
      fin_cases i
      · exact (tv_bvar (x :> y :> Y :> A :> Fin.elim0) ε 0).symm
      · exact (tv_bvar (x :> y :> Y :> A :> Fin.elim0) ε 1).symm
  · have hEq : ψ = Axiom.choice := hψAC
    rw [hEq]
    exact hChoiceL

end OMA.R_Constant14_c14_le_432_R1_H1_R1_H1_R1
