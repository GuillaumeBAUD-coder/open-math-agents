import FormalConjectures.Paper.ShelahSpencerZeroOneLaw
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic

/-!
# Reduction of `ShelahSpencerZeroOneLaw.zeroOne_rational`

Following S. Shelah and J. Spencer (*Zero-one laws for sparse random graphs*, J. Amer. Math. Soc.
1 (1988), 97–115, Theorem 2), we reduce the failure of the convergence law for $G(n, n^{-\alpha})$
at every rational exponent $\alpha \in (0, 1)$ to two independent classical pillars:
1. `H1`: **Shelah–Spencer sparse random-graph interpretation of truncated arithmetic**: for every
   rational $\alpha = p / q \in (0, 1)$, there exist first-order graph formulas `(param, dom, addF, mulF)`
   with `k` parameters and two unbounded sequences `n₀, n₁ : ℕ → ℕ` such that asymptotically almost
   surely in $G(n_0(j), n_0(j)^{-\alpha})$, `param` is satisfiable and every parameter tuple satisfying
   `param` interprets truncated arithmetic `(Fin M, +, ×)` with `M` in an even exponential-tower band
   `[T r, T (r + 1))`, while along $n_1(j)$ it a.a.s. interprets `(Fin M, +, ×)` with `M` in an odd
   exponential-tower band.
2. `H2`: **First-order definability of exponential-tower band parity in truncated arithmetic**
   (via $\Delta_0$-definability of exponentiation, Bennett 1962 / Paris–Dimitracopoulos 1982 /
   Hájek–Pudlák V.3.7): there is a single sentence `θ` in the relational language of partial
   addition and multiplication such that `(Fin M, +, ×) ⊨ θ` iff `M` lies in an even exponential-tower
   band (for all `M ≥ 1`).

Inside `main`, we prove from scratch:
- Rational decomposition `α = p / q` (`0 < p < q`) from `¬ Irrational α` and `0 < α < 1`.
- Strict monotonicity of the exponential tower `T 0 = 1`, `T (r + 1) = 2 ^ T r` and disjointness of
  even and odd tower bands.
- The full syntactic interpretation/relativization functor translating any `BoundedFormula` of
  relational partial arithmetic into `Language.graph.BoundedFormula (Fin k)` and the semantic
  satisfaction equivalence proved by structural induction on `BoundedFormula`.
- Existential parameter quantification `(param ⊓ translate θ).relabel Sum.inr |>.exs` yielding a
  parameter-free `Language.graph.Sentence` `φ` whose probability in `sparseRandomGraph` tends to
  `1` along `n₀` and to `0` along `n₁`, ruling out `Tendsto ... atTop (𝓝 b)` for every `b : ENNReal`.

Thanks to @SubhanAfz and @MechaNuggan for the Shelah–Spencer truncated-arithmetic interpretation
and oscillation analysis.
Credit: @tkaiman
-/

namespace OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1

open FirstOrder Filter MeasureTheory Topology ShelahSpencerZeroOneLaw

/- ### Step 1: Exponential tower and band disjointness -/

private def tower : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 ^ tower r

private lemma tower_eq_natRec (r : ℕ) :
    tower r = Nat.rec (motive := fun _ => ℕ) 1 (fun _ x => 2 ^ x) r := by
  induction r with
  | zero => rfl
  | succ k ih => simp [tower, ih]

private lemma tower_strictMono : StrictMono tower := by
  refine strictMono_nat_of_lt_succ fun r => ?_
  dsimp [tower]
  exact Nat.lt_two_pow_self

private lemma tower_band_unique {M r₁ r₂ : ℕ}
    (h1 : tower r₁ ≤ M ∧ M < tower (r₁ + 1))
    (h2 : tower r₂ ≤ M ∧ M < tower (r₂ + 1)) : r₁ = r₂ := by
  rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
  · have hle : r₁ + 1 ≤ r₂ := hlt
    have : tower (r₁ + 1) ≤ tower r₂ := tower_strictMono.monotone hle
    omega
  · rfl
  · have hle : r₂ + 1 ≤ r₁ := hgt
    have : tower (r₂ + 1) ≤ tower r₁ := tower_strictMono.monotone hle
    omega

/- ### Step 2: Relational partial-arithmetic language and syntactic interpretation functor -/

private abbrev arithLang : FirstOrder.Language.{0, 0} :=
  { Functions := fun _ => Empty
    Relations := fun
      | 3 => Bool
      | _ => Empty }

private abbrev finArithStruct (M : ℕ) : arithLang.Structure (Fin M) :=
  { funMap := fun f => Empty.elim f
    RelMap := fun {l} r v =>
      match l, r with
      | 3, false => (v 0 : ℕ) + (v 1 : ℕ) = (v 2 : ℕ)
      | 3, true => (v 0 : ℕ) * (v 1 : ℕ) = (v 2 : ℕ)
      | 0, r | 1, r | 2, r | _ + 4, r => Empty.elim r }

private def arithTermIdx {n : ℕ} : arithLang.Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl e) => Empty.elim e
  | .var (.inr i) => i
  | .func f _ => Empty.elim f

private lemma realize_arithTerm {M n : ℕ} (v : Empty → Fin M) (xs : Fin n → Fin M)
    (t : arithLang.Term (Empty ⊕ Fin n)) :
    @FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) (Empty ⊕ Fin n)
      (Sum.elim v xs) t = xs (arithTermIdx t) := by
  cases t with
  | var s =>
    cases s with
    | inl e => exact Empty.elim e
    | inr i => rfl
  | func f _ => exact Empty.elim f

private def interpDom {k n : ℕ} (dom : Language.graph.Formula (Fin k ⊕ Fin 1))
    (i : Fin n) : Language.graph.BoundedFormula (Fin k) n :=
  FirstOrder.Language.BoundedFormula.relabel
    (fun s : Fin k ⊕ Fin 1 => match s with | Sum.inl j => Sum.inl j | Sum.inr _ => Sum.inr i)
    (dom : Language.graph.BoundedFormula (Fin k ⊕ Fin 1) 0)

private def interpRel3 {k n : ℕ} (relF : Language.graph.Formula (Fin k ⊕ Fin 3))
    (i₀ i₁ i₂ : Fin n) : Language.graph.BoundedFormula (Fin k) n :=
  FirstOrder.Language.BoundedFormula.relabel
    (fun s : Fin k ⊕ Fin 3 =>
      match s with
      | Sum.inl j => Sum.inl j
      | Sum.inr idx => Sum.inr (![i₀, i₁, i₂] idx))
    (relF : Language.graph.BoundedFormula (Fin k ⊕ Fin 3) 0)

private def translateBF {k : ℕ}
    (dom : Language.graph.Formula (Fin k ⊕ Fin 1))
    (addF mulF : Language.graph.Formula (Fin k ⊕ Fin 3)) :
    ∀ {n : ℕ}, arithLang.BoundedFormula Empty n → Language.graph.BoundedFormula (Fin k) n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (.var (.inr (arithTermIdx t₁))) (.var (.inr (arithTermIdx t₂)))
  | _, .rel (l := 3) false ts =>
      interpRel3 addF (arithTermIdx (ts 0)) (arithTermIdx (ts 1)) (arithTermIdx (ts 2))
  | _, .rel (l := 3) true ts =>
      interpRel3 mulF (arithTermIdx (ts 0)) (arithTermIdx (ts 1)) (arithTermIdx (ts 2))
  | _, .rel (l := 0) r _ => Empty.elim r
  | _, .rel (l := 1) r _ => Empty.elim r
  | _, .rel (l := 2) r _ => Empty.elim r
  | _, .rel (l := _ + 4) r _ => Empty.elim r
  | _, .imp f₁ f₂ => (translateBF dom addF mulF f₁).imp (translateBF dom addF mulF f₂)
  | n, .all f => ((interpDom dom (Fin.last n)).imp (translateBF dom addF mulF f)).all

private lemma realize_interpDom {V : Type} [Language.graph.Structure V] {k n : ℕ}
    (dom : Language.graph.Formula (Fin k ⊕ Fin 1)) (p : Fin k → V) (xs : Fin n → V) (i : Fin n) :
    (interpDom dom i).Realize p xs ↔ dom.Realize (Sum.elim p ![xs i]) := by
  unfold interpDom
  rw [FirstOrder.Language.BoundedFormula.realize_relabel, FirstOrder.Language.Formula.Realize]
  have h0 : (xs ∘ Fin.natAdd (m := 0) n : Fin 0 → V) = default := Subsingleton.elim _ _
  rw [h0]
  refine iff_of_eq (congrArg (fun f => FirstOrder.Language.BoundedFormula.Realize dom f default) ?_)
  funext s
  cases s with
  | inl j => simp
  | inr idx =>
    fin_cases idx
    simp

private lemma realize_interpRel3 {V : Type} [Language.graph.Structure V] {k n : ℕ}
    (relF : Language.graph.Formula (Fin k ⊕ Fin 3)) (p : Fin k → V) (xs : Fin n → V)
    (i₀ i₁ i₂ : Fin n) :
    (interpRel3 relF i₀ i₁ i₂).Realize p xs ↔ relF.Realize (Sum.elim p ![xs i₀, xs i₁, xs i₂]) := by
  unfold interpRel3
  rw [FirstOrder.Language.BoundedFormula.realize_relabel, FirstOrder.Language.Formula.Realize]
  have h0 : (xs ∘ Fin.natAdd (m := 0) n : Fin 0 → V) = default := Subsingleton.elim _ _
  rw [h0]
  refine iff_of_eq (congrArg (fun f => FirstOrder.Language.BoundedFormula.Realize relF f default) ?_)
  funext s
  cases s with
  | inl j => simp
  | inr idx =>
    fin_cases idx <;> simp

private lemma realize_translateBF {V : Type} [Language.graph.Structure V] {k M : ℕ}
    (dom : Language.graph.Formula (Fin k ⊕ Fin 1))
    (addF mulF : Language.graph.Formula (Fin k ⊕ Fin 3))
    (p : Fin k → V)
    (e : Fin M ≃ {x : V // dom.Realize (Sum.elim p ![x])})
    (hadd : ∀ a b c : Fin M,
      addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔ (a : ℕ) + (b : ℕ) = (c : ℕ))
    (hmul : ∀ a b c : Fin M,
      mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔ (a : ℕ) * (b : ℕ) = (c : ℕ)) :
    ∀ {n : ℕ} (φ : arithLang.BoundedFormula Empty n) (xs : Fin n → Fin M),
      (translateBF dom addF mulF φ).Realize p (fun i => (e (xs i)).1) ↔
        @FirstOrder.Language.BoundedFormula.Realize arithLang (Fin M) (finArithStruct M)
          Empty n φ default xs := by
  intro n φ
  induction φ with
  | falsum =>
    intro xs; rfl
  | equal t₁ t₂ =>
    intro xs
    simp only [translateBF, FirstOrder.Language.BoundedFormula.Realize,
      FirstOrder.Language.Term.realize_var, Sum.elim_inr, realize_arithTerm]
    constructor
    · intro h
      exact e.injective (Subtype.ext h)
    · intro h
      rw [h]
  | @rel n l r ts =>
    intro xs
    match l, r with
    | 0, r => exact Empty.elim r
    | 1, r => exact Empty.elim r
    | 2, r => exact Empty.elim r
    | _ + 4, r => exact Empty.elim r
    | 3, false =>
      dsimp only [translateBF, FirstOrder.Language.BoundedFormula.Realize]
      rw [realize_interpRel3]
      change addF.Realize (Sum.elim p ![(e (xs (arithTermIdx (ts 0)))).1,
          (e (xs (arithTermIdx (ts 1)))).1, (e (xs (arithTermIdx (ts 2)))).1]) ↔
        (@FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) _
            (Sum.elim default xs) (ts 0) : ℕ) +
        (@FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) _
            (Sum.elim default xs) (ts 1) : ℕ) =
        (@FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) _
            (Sum.elim default xs) (ts 2) : ℕ)
      simp only [realize_arithTerm]
      exact hadd (xs (arithTermIdx (ts 0))) (xs (arithTermIdx (ts 1))) (xs (arithTermIdx (ts 2)))
    | 3, true =>
      dsimp only [translateBF, FirstOrder.Language.BoundedFormula.Realize]
      rw [realize_interpRel3]
      change mulF.Realize (Sum.elim p ![(e (xs (arithTermIdx (ts 0)))).1,
          (e (xs (arithTermIdx (ts 1)))).1, (e (xs (arithTermIdx (ts 2)))).1]) ↔
        (@FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) _
            (Sum.elim default xs) (ts 0) : ℕ) *
        (@FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) _
            (Sum.elim default xs) (ts 1) : ℕ) =
        (@FirstOrder.Language.Term.realize arithLang (Fin M) (finArithStruct M) _
            (Sum.elim default xs) (ts 2) : ℕ)
      simp only [realize_arithTerm]
      exact hmul (xs (arithTermIdx (ts 0))) (xs (arithTermIdx (ts 1))) (xs (arithTermIdx (ts 2)))
  | imp f₁ f₂ ih₁ ih₂ =>
    intro xs
    simp only [translateBF, FirstOrder.Language.BoundedFormula.Realize]
    exact imp_congr (ih₁ xs) (ih₂ xs)
  | @all n f ih =>
    intro xs
    simp only [translateBF, FirstOrder.Language.BoundedFormula.Realize]
    constructor
    · intro h x
      have hx_dom : (interpDom dom (Fin.last n)).Realize p (Fin.snoc (fun i => (e (xs i)).1) (e x).1) := by
        rw [realize_interpDom]
        simpa [Fin.snoc_last] using (e x).2
      have hbody := h (e x).1 hx_dom
      have hsnoc : Fin.snoc (fun i => (e (xs i)).1) (e x).1 =
          fun i : Fin (n + 1) => (e ((Fin.snoc xs x : Fin (n + 1) → Fin M) i)).1 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.snoc_last]
        · simp [Fin.snoc_castSucc]
      rw [hsnoc] at hbody
      exact (ih (Fin.snoc xs x)).mp hbody
    · intro h v hv
      have hv_dom : dom.Realize (Sum.elim p ![v]) := by
        have := (realize_interpDom dom p (Fin.snoc (fun i => (e (xs i)).1) v) (Fin.last n)).mp hv
        simpa [Fin.snoc_last] using this
      let x : Fin M := e.symm ⟨v, hv_dom⟩
      have hvx : (e x).1 = v := by simp [x]
      have hsnoc : Fin.snoc (fun i => (e (xs i)).1) v =
          fun i : Fin (n + 1) => (e ((Fin.snoc xs x : Fin (n + 1) → Fin M) i)).1 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.snoc_last, hvx]
        · simp [Fin.snoc_castSucc]
      rw [hsnoc]
      exact (ih (Fin.snoc xs x)).mpr (h x)

private lemma measurableSet_simpleGraph_fin {n : ℕ} (S : Set (SimpleGraph (Fin n))) :
    MeasurableSet S := by
  have hsing : ∀ G₀ : SimpleGraph (Fin n), MeasurableSet ({G₀} : Set (SimpleGraph (Fin n))) := by
    intro G₀
    have heq : ({G₀} : Set (SimpleGraph (Fin n))) =
        ⋂ u : Fin n, ⋂ v : Fin n, {G : SimpleGraph (Fin n) | G.Adj u v ↔ G₀.Adj u v} := by
      ext G
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SimpleGraph.ext_iff,
        funext_iff, eq_iff_iff]
      rfl
    rw [heq]
    refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => ?_
    have hm : Measurable (fun G : SimpleGraph (Fin n) => G.Adj u v) :=
      (measurable_pi_apply v).comp ((measurable_pi_apply u).comp SimpleGraph.measurable_adj)
    exact hm (MeasurableSet.of_discrete (s := {p : Prop | p ↔ G₀.Adj u v}))
  have hunion : S = ⋃ G₀ ∈ S, ({G₀} : Set (SimpleGraph (Fin n))) := by simp
  rw [hunion]
  exact Set.Finite.measurableSet_biUnion (Set.toFinite S) fun G₀ _ => hsing G₀

/- ### Hypotheses and main reduction theorem -/

/-- **Shelah–Spencer sparse random-graph interpretation of truncated arithmetic** (1988):
for every rational `α = p / q ∈ (0, 1)`, there exist first-order graph formulas
`(param, dom, addF, mulF)` with `k` parameters and two unbounded sequences `n₀, n₁ : ℕ → ℕ` such
that in `G(n, n^{-α})`:
- along `n₀`, with probability tending to `1`, `param` is satisfiable and every parameter tuple
  satisfying `param` interprets truncated arithmetic `(Fin M, +, ×)` with `M` in an even
  exponential-tower band `[T r, T (r + 1))`;
- along `n₁`, with probability tending to `1`, `param` is satisfiable and every parameter tuple
  satisfying `param` interprets `(Fin M, +, ×)` with `M` in an odd exponential-tower band. -/
def H1 : Prop :=
  let T : ℕ → ℕ := fun r => Nat.rec (motive := fun _ => ℕ) 1 (fun _ x => 2 ^ x) r
  ∀ (α : ℝ) (hα : 0 < α ∧ α < 1), (∃ p q : ℕ, 0 < p ∧ p < q ∧ α = (p : ℝ) / (q : ℝ)) →
    ∃ (k : ℕ)
      (param : Language.graph.Formula (Fin k))
      (dom : Language.graph.Formula (Fin k ⊕ Fin 1))
      (addF mulF : Language.graph.Formula (Fin k ⊕ Fin 3))
      (n₀ n₁ : ℕ → ℕ),
      let Good (P : ℕ → Prop) (n : ℕ) : Set (SimpleGraph (Fin n)) :=
        {G | letI := G.structure
          (∃ p : Fin k → Fin n, param.Realize p) ∧
          (∀ p : Fin k → Fin n, param.Realize p →
            ∃ M : ℕ, (∃ r : ℕ, P r ∧ T r ≤ M ∧ M < T (r + 1)) ∧
              ∃ e : Fin M ≃ {x : Fin n // dom.Realize (Sum.elim p ![x])},
                (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
                (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) * (b : ℕ) = (c : ℕ)))}
      Tendsto n₀ atTop atTop ∧ Tendsto n₁ atTop atTop ∧
      Tendsto (fun j : ℕ => sparseRandomGraph (n₀ j) α hα.1 (Good Even (n₀ j))) atTop (𝓝 1) ∧
      Tendsto (fun j : ℕ => sparseRandomGraph (n₁ j) α hα.1 (Good Odd (n₁ j))) atTop (𝓝 1)

/-- **First-order definability of exponential-tower band parity in truncated arithmetic**
(via `Δ₀`-definability of exponentiation, Bennett 1962 / Paris–Dimitracopoulos 1982):
there exists a single sentence `θ` in the relational language of partial addition and
multiplication such that for every `M ≥ 1`, `(Fin M, +, ×) ⊨ θ` holds if and only if `M` lies in
an even exponential-tower band `[T r, T (r + 1))`. -/
def H2 : Prop :=
  let L : FirstOrder.Language.{0, 0} :=
    { Functions := fun _ => Empty
      Relations := fun | 3 => Bool | _ => Empty }
  let T : ℕ → ℕ := fun r => Nat.rec (motive := fun _ => ℕ) 1 (fun _ x => 2 ^ x) r
  ∃ θ : L.Sentence,
    ∀ M : ℕ, 1 ≤ M →
      letI : L.Structure (Fin M) :=
        { funMap := fun f => Empty.elim f
          RelMap := fun {l} r v =>
            match l, r with
            | 3, false => (v 0 : ℕ) + (v 1 : ℕ) = (v 2 : ℕ)
            | 3, true => (v 0 : ℕ) * (v 1 : ℕ) = (v 2 : ℕ)
            | 0, r | 1, r | 2, r | _ + 4, r => Empty.elim r }
      θ.Realize (M := Fin M) ↔ ∃ r : ℕ, Even r ∧ T r ≤ M ∧ M < T (r + 1)

theorem main : H1 → H2 → type_of% @ShelahSpencerZeroOneLaw.zeroOne_rational := by
  intro h1 h2 α hα hrat
  have hrat_pq : ∃ p q : ℕ, 0 < p ∧ p < q ∧ α = (p : ℝ) / (q : ℝ) := by
    rw [Irrational, not_not] at hrat
    obtain ⟨q₀, hq₀⟩ := hrat
    have hq₀_pos : (0 : ℚ) < q₀ := by
      have : ((0 : ℚ) : ℝ) < (q₀ : ℝ) := by simpa [hq₀] using hα.1
      exact_mod_cast this
    have hq₀_lt1 : q₀ < 1 := by
      have : (q₀ : ℝ) < ((1 : ℚ) : ℝ) := by simpa [hq₀] using hα.2
      exact_mod_cast this
    have hnum_pos : 0 < q₀.num := Rat.num_pos.mpr hq₀_pos
    refine ⟨q₀.num.toNat, q₀.den, ?_, ?_, ?_⟩
    · omega
    · have hden_pos : (0 : ℚ) < (q₀.den : ℚ) := by exact_mod_cast q₀.den_pos
      have hnum_lt : (q₀.num : ℚ) < (q₀.den : ℚ) := by
        have h1 := (div_lt_one hden_pos).mp (by rwa [Rat.num_div_den])
        exact h1
      have hnum_ltZ : q₀.num < (q₀.den : ℤ) := by exact_mod_cast hnum_lt
      omega
    · have hq0R : (q₀ : ℝ) = (q₀.num : ℝ) / (q₀.den : ℝ) := by
        have h := Rat.num_div_den q₀
        have hR : ((q₀.num : ℚ) / (q₀.den : ℚ) : ℝ) = (q₀ : ℝ) := by exact_mod_cast h
        simpa using hR.symm
      have hcast : ((q₀.num.toNat : ℕ) : ℝ) = (q₀.num : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnum_pos.le
      rw [← hq₀, hq0R, hcast]
  obtain ⟨k, param, dom, addF, mulF, n₀, n₁, hn₀_top, hn₁_top, hprob₀, hprob₁⟩ := h1 α hα hrat_pq
  obtain ⟨θ, hθ⟩ := h2
  -- Build parameter-free graph sentence φ := ∃ p : Fin k, param(p) ∧ translate(θ)(p)
  let body : Language.graph.Formula (Fin k) := param ⊓ translateBF dom addF mulF θ
  let φ : Language.graph.Sentence :=
    (FirstOrder.Language.BoundedFormula.relabel (Sum.inr : Fin k → Empty ⊕ Fin k)
      (body : Language.graph.BoundedFormula (Fin k) 0)).exs
  refine ⟨φ, fun b hb => ?_⟩
  have hrealize_φ : ∀ {V : Type} (G : SimpleGraph V),
      @FirstOrder.Language.Sentence.Realize Language.graph V G.structure φ ↔
        letI := G.structure
        ∃ p : Fin k → V, param.Realize p ∧ (translateBF dom addF mulF θ).Realize p default := by
    intro V G
    let _ := G.structure
    dsimp only [φ, body]
    rw [FirstOrder.Language.Sentence.Realize, FirstOrder.Language.BoundedFormula.realize_exs]
    constructor
    · rintro ⟨p, hp⟩
      rw [FirstOrder.Language.BoundedFormula.realize_relabel] at hp
      have h0 : (p ∘ Fin.natAdd (m := 0) k : Fin 0 → V) = default := Subsingleton.elim _ _
      have hp' : FirstOrder.Language.BoundedFormula.Realize
          (param ⊓ translateBF dom addF mulF θ) p default := by
        simpa [FirstOrder.Language.Formula.Realize, h0] using hp
      exact ⟨p, FirstOrder.Language.BoundedFormula.realize_inf.mp hp'⟩
    · rintro ⟨p, hpar, htr⟩
      refine ⟨p, ?_⟩
      rw [FirstOrder.Language.BoundedFormula.realize_relabel]
      have h0 : (p ∘ Fin.natAdd (m := 0) k : Fin 0 → V) = default := Subsingleton.elim _ _
      have hp' : FirstOrder.Language.BoundedFormula.Realize
          (param ⊓ translateBF dom addF mulF θ) p default :=
        FirstOrder.Language.BoundedFormula.realize_inf.mpr ⟨hpar, htr⟩
      simpa [FirstOrder.Language.Formula.Realize, h0] using hp'
  -- Along n₀, Good₀ ⊆ {G | G ⊨ φ}, so P(G ⊨ φ) → 1
  have hsub₀ : ∀ j : ℕ,
      sparseRandomGraph (n₀ j) α hα.1
        {G : SimpleGraph (Fin (n₀ j)) |
          letI := G.structure
          (∃ p : Fin k → Fin (n₀ j), param.Realize p) ∧
          (∀ p : Fin k → Fin (n₀ j), param.Realize p →
            ∃ M : ℕ, (∃ r : ℕ, Even r ∧ tower r ≤ M ∧ M < tower (r + 1)) ∧
              ∃ e : Fin M ≃ {x : Fin (n₀ j) // dom.Realize (Sum.elim p ![x])},
                (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
                (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) * (b : ℕ) = (c : ℕ)))} ≤
      sparseRandomGraph (n₀ j) α hα.1
        {G : SimpleGraph (Fin (n₀ j)) |
          @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₀ j)) G.structure φ} := by
    intro j
    refine measure_mono fun G hG => ?_
    let _ := G.structure
    obtain ⟨⟨p, hp⟩, hall⟩ := hG
    obtain ⟨M, ⟨r, hr_even, hr_lo, hr_hi⟩, e, hadd, hmul⟩ := hall p hp
    have hM1 : 1 ≤ M := by
      have : 1 ≤ tower r := by
        cases r with
        | zero => simp [tower]
        | succ m => exact Nat.one_le_two_pow
      omega
    have hθM : @FirstOrder.Language.BoundedFormula.Realize arithLang (Fin M) (finArithStruct M)
        Empty 0 θ default (default : Fin 0 → Fin M) :=
      (hθ M hM1).mpr ⟨r, hr_even, by simpa [tower_eq_natRec] using hr_lo,
        by simpa [tower_eq_natRec] using hr_hi⟩
    have htr : (translateBF dom addF mulF θ).Realize p default := by
      have h := (realize_translateBF dom addF mulF p e hadd hmul θ (default : Fin 0 → Fin M)).mpr hθM
      have hfn : (fun i : Fin 0 => (e ((default : Fin 0 → Fin M) i)).1) = default :=
        Subsingleton.elim _ _
      rwa [hfn] at h
    exact (hrealize_φ G).mpr ⟨p, hp, htr⟩
  -- Along n₁, Good₁ ⊆ {G | G ⊨ φ}ᶜ, so P(G ⊨ φ) ≤ 1 - P(Good₁) → 0
  have hsub₁ : ∀ j : ℕ,
      sparseRandomGraph (n₁ j) α hα.1
        {G : SimpleGraph (Fin (n₁ j)) |
          @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₁ j)) G.structure φ} +
      sparseRandomGraph (n₁ j) α hα.1
        {G : SimpleGraph (Fin (n₁ j)) |
          letI := G.structure
          (∃ p : Fin k → Fin (n₁ j), param.Realize p) ∧
          (∀ p : Fin k → Fin (n₁ j), param.Realize p →
            ∃ M : ℕ, (∃ r : ℕ, Odd r ∧ tower r ≤ M ∧ M < tower (r + 1)) ∧
              ∃ e : Fin M ≃ {x : Fin (n₁ j) // dom.Realize (Sum.elim p ![x])},
                (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
                (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) * (b : ℕ) = (c : ℕ)))} ≤ 1 := by
    intro j
    set μ := sparseRandomGraph (n₁ j) α hα.1
    set A : Set (SimpleGraph (Fin (n₁ j))) :=
      {G | @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₁ j)) G.structure φ}
    set B : Set (SimpleGraph (Fin (n₁ j))) :=
      {G | letI := G.structure
        (∃ p : Fin k → Fin (n₁ j), param.Realize p) ∧
        (∀ p : Fin k → Fin (n₁ j), param.Realize p →
          ∃ M : ℕ, (∃ r : ℕ, Odd r ∧ tower r ≤ M ∧ M < tower (r + 1)) ∧
            ∃ e : Fin M ≃ {x : Fin (n₁ j) // dom.Realize (Sum.elim p ![x])},
              (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
              (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                (a : ℕ) * (b : ℕ) = (c : ℕ)))}
    have hdisj : Disjoint A B := by
      rw [Set.disjoint_left]
      intro G hGA hGB
      let _ := G.structure
      obtain ⟨p, hp, htr⟩ := (hrealize_φ G).mp hGA
      obtain ⟨_, hall⟩ := hGB
      obtain ⟨M, ⟨r, hr_odd, hr_lo, hr_hi⟩, e, hadd, hmul⟩ := hall p hp
      have hM1 : 1 ≤ M := by
        have : 1 ≤ tower r := by
          cases r with
          | zero => simp [tower]
          | succ m => exact Nat.one_le_two_pow
        omega
      have hθM : @FirstOrder.Language.Sentence.Realize arithLang (Fin M) (finArithStruct M) θ := by
        have hfn : (fun i : Fin 0 => (e ((default : Fin 0 → Fin M) i)).1) = default :=
          Subsingleton.elim _ _
        have htr' : (translateBF dom addF mulF θ).Realize p
            (fun i : Fin 0 => (e ((default : Fin 0 → Fin M) i)).1) := by
          rwa [hfn]
        exact (realize_translateBF dom addF mulF p e hadd hmul θ (default : Fin 0 → Fin M)).mp htr'
      obtain ⟨r', hr'_even, hr'_lo, hr'_hi⟩ := (hθ M hM1).mp hθM
      have heq_r : r = r' := tower_band_unique ⟨hr_lo, hr_hi⟩
        ⟨by simpa [tower_eq_natRec] using hr'_lo, by simpa [tower_eq_natRec] using hr'_hi⟩
      rw [heq_r] at hr_odd
      exact (Nat.not_odd_iff_even.mpr hr'_even) hr_odd
    have hmeas : MeasurableSet B := measurableSet_simpleGraph_fin B
    have hunion : μ A + μ B = μ (A ∪ B) := (measure_union hdisj hmeas).symm
    rw [hunion]
    have : IsProbabilityMeasure μ := by
      dsimp [μ, sparseRandomGraph]
      infer_instance
    exact prob_le_one
  -- Squeeze along n₀ to get b = 1
  have hb₀ : Tendsto (fun j : ℕ =>
      sparseRandomGraph (n₀ j) α hα.1
        {G | @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₀ j)) G.structure φ})
      atTop (𝓝 b) := hb.comp hn₀_top
  have h1_tendsto : Tendsto (fun j : ℕ =>
      sparseRandomGraph (n₀ j) α hα.1
        {G | @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₀ j)) G.structure φ})
      atTop (𝓝 1) := by
    have hprob₀' : Tendsto (fun j : ℕ =>
        sparseRandomGraph (n₀ j) α hα.1
          {G : SimpleGraph (Fin (n₀ j)) |
            letI := G.structure
            (∃ p : Fin k → Fin (n₀ j), param.Realize p) ∧
            (∀ p : Fin k → Fin (n₀ j), param.Realize p →
              ∃ M : ℕ, (∃ r : ℕ, Even r ∧ tower r ≤ M ∧ M < tower (r + 1)) ∧
                ∃ e : Fin M ≃ {x : Fin (n₀ j) // dom.Realize (Sum.elim p ![x])},
                  (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                    (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
                  (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                    (a : ℕ) * (b : ℕ) = (c : ℕ)))})
        atTop (𝓝 1) := by
      simpa only [tower_eq_natRec] using hprob₀
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hprob₀' tendsto_const_nhds hsub₀ fun j => ?_
    have : IsProbabilityMeasure (sparseRandomGraph (n₀ j) α hα.1) := by
      dsimp [sparseRandomGraph]; infer_instance
    exact prob_le_one
  have hb_eq_1 : b = 1 := tendsto_nhds_unique hb₀ h1_tendsto
  -- Along n₁, b + 1 ≤ 1 in ENNReal, so 1 + 1 ≤ 1, contradiction!
  have hb₁ : Tendsto (fun j : ℕ =>
      sparseRandomGraph (n₁ j) α hα.1
        {G | @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₁ j)) G.structure φ})
      atTop (𝓝 b) := hb.comp hn₁_top
  have hprob₁' : Tendsto (fun j : ℕ =>
      sparseRandomGraph (n₁ j) α hα.1
        {G : SimpleGraph (Fin (n₁ j)) |
          letI := G.structure
          (∃ p : Fin k → Fin (n₁ j), param.Realize p) ∧
          (∀ p : Fin k → Fin (n₁ j), param.Realize p →
            ∃ M : ℕ, (∃ r : ℕ, Odd r ∧ tower r ≤ M ∧ M < tower (r + 1)) ∧
              ∃ e : Fin M ≃ {x : Fin (n₁ j) // dom.Realize (Sum.elim p ![x])},
                (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
                (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) * (b : ℕ) = (c : ℕ)))})
      atTop (𝓝 1) := by
    simpa only [tower_eq_natRec] using hprob₁
  have hsum_lim : Tendsto (fun j : ℕ =>
      sparseRandomGraph (n₁ j) α hα.1
        {G | @FirstOrder.Language.Sentence.Realize Language.graph (Fin (n₁ j)) G.structure φ} +
      sparseRandomGraph (n₁ j) α hα.1
        {G : SimpleGraph (Fin (n₁ j)) |
          letI := G.structure
          (∃ p : Fin k → Fin (n₁ j), param.Realize p) ∧
          (∀ p : Fin k → Fin (n₁ j), param.Realize p →
            ∃ M : ℕ, (∃ r : ℕ, Odd r ∧ tower r ≤ M ∧ M < tower (r + 1)) ∧
              ∃ e : Fin M ≃ {x : Fin (n₁ j) // dom.Realize (Sum.elim p ![x])},
                (∀ a b c : Fin M, addF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) + (b : ℕ) = (c : ℕ)) ∧
                (∀ a b c : Fin M, mulF.Realize (Sum.elim p ![(e a).1, (e b).1, (e c).1]) ↔
                  (a : ℕ) * (b : ℕ) = (c : ℕ)))})
      atTop (𝓝 (b + 1)) := hb₁.add hprob₁'
  have hle1 : b + 1 ≤ 1 := le_of_tendsto hsum_lim (Filter.Eventually.of_forall hsub₁)
  rw [hb_eq_1] at hle1
  simp only [one_add_one_eq_two] at hle1
  exact absurd hle1 (by norm_num)

end OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1
