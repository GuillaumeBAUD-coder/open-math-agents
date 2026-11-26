import FormalConjectures.Wikipedia.SidorenkoConjecture

/-!
# Sidorenko's Inequality for Even Cycles (Graphon Version)

We prove `SidorenkoConjecture.sidorenko_even_cycle_graphon`: for every `k ≥ 1` and every graphon
`W : LimitObjects.Graphon`,
`(graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤ graphonHomDensity (cycleGraph (2 * k)) W`.

1. For `k = 1`, `cycleGraph 2` is a single edge, so both sides equal `graphonEdgeDensity W`.
2. For `k ≥ 2`, `cycleGraph (2 * k)` has `2 * k` edges `{s(i, i + 1)}`. For any `N ≥ 1` and
   `u : Fin N → UnitInterval`, the real symmetric matrix `A(u)_{a,b} = W(u a, u b)` satisfies
   `((1 / N^2) ∑_{a,b} A(u)_{a,b}) ^ (2 * k) ≤ (1 / N^(2*k)) Tr(A(u)^(2*k))` by the matrix
   spectral theorem and discrete Jensen's inequality for `t ↦ t ^ (2 * k)`.
3. Integrating over `u ∈ UnitInterval ^ N` and applying Jensen's inequality on the left gives
   `((1 - 1 / N) * graphonEdgeDensity W) ^ (2 * k) ≤ graphonHomDensity (cycleGraph (2 * k)) W + (2 * k)^2 / N`,
   since injective `2k`-tuples integrate to `graphonHomDensity (cycleGraph (2 * k)) W` and at most
   `(2 * k)^2 * N^(2*k - 1)` tuples are non-injective. Letting `N → ∞` concludes the proof.
-/

-- Problem: Case: `H = C_{2k}` is an even cycle (Sidorenko 1993, graphon version).
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/SidorenkoConjecture.lean:120 (declaration SidorenkoConjecture.sidorenko_even_cycle_graphon)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace SidorenkoEvenCycleGraphonProof

open MeasureTheory Finset SimpleGraph LimitObjects Filter

private abbrev U := LimitObjects.UnitInterval

private noncomputable abbrev piVol (r : ℕ) : Measure (Fin r → U) :=
  Measure.pi (fun _ : Fin r => (volume : Measure U))

private lemma measurePreserving_comp_injective {m N : ℕ} (a : Fin m → Fin N)
    (ha : Function.Injective a) :
    MeasurePreserving (fun u : Fin N → U => u ∘ a) (piVol N) (piVol m) := by
  let R := { j : Fin N // j ∉ Set.range a }
  let e : Fin m ⊕ R ≃ Fin N :=
    ((Equiv.ofInjective a ha).sumCongr (Equiv.refl R)).trans (Equiv.Set.sumCompl (Set.range a))
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => U) e).symm
      (piVol N) (Measure.pi fun _ : Fin m ⊕ R => (volume : Measure U)) :=
    (measurePreserving_piCongrLeft (fun _ : Fin N => (volume : Measure U)) e).symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ R => U))
      (Measure.pi fun _ : Fin m ⊕ R => (volume : Measure U))
      ((piVol m).prod (Measure.pi fun _ : R => (volume : Measure U))) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ R => (volume : Measure U))
  have h3 : MeasurePreserving Prod.fst
      ((piVol m).prod (Measure.pi fun _ : R => (volume : Measure U))) (piVol m) :=
    MeasureTheory.measurePreserving_fst
  have hcomp := h3.comp (h2.comp h1)
  have hfun : (Prod.fst ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ R => U)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => U) e).symm) = (fun u : Fin N → U => u ∘ a) := by
    funext u i
    rfl
  rwa [hfun] at hcomp

private lemma measurePreserving_pair_ne {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    MeasurePreserving (fun u : Fin N → U => (u a, u b)) (piVol N)
      ((volume : Measure U).prod (volume : Measure U)) := by
  let idx : Fin 2 → Fin N := fun i => if i = 0 then a else b
  have hinj : Function.Injective idx := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hab
    · exact absurd hij.symm hab
    · rfl
  have h1 := measurePreserving_comp_injective idx hinj
  have h2 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := U))
      (piVol 2) ((volume : Measure U).prod (volume : Measure U)) :=
    measurePreserving_finTwoArrow (volume : Measure U)
  have hcomp := h2.comp h1
  have hfun : (MeasurableEquiv.finTwoArrow (α := U) ∘ (fun u : Fin N → U => u ∘ idx)) =
      (fun u : Fin N → U => (u a, u b)) := by
    funext u
    simp [MeasurableEquiv.finTwoArrow, idx]
  rwa [hfun] at hcomp

private lemma graphon_entry_measurable (W : Graphon) {N : ℕ} (a b : Fin N) :
    Measurable (fun u : Fin N → U => (W (u a, u b) : ℝ)) :=
  measurable_subtype_coe.comp (W.measurable.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b)))

private lemma graphon_entry_integrable (W : Graphon) {N : ℕ} (a b : Fin N) :
    Integrable (fun u : Fin N → U => (W (u a, u b) : ℝ)) (piVol N) := by
  refine Integrable.of_bound (graphon_entry_measurable W a b).aestronglyMeasurable 1 ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (W (u a, u b)).2.1]
  exact (W (u a, u b)).2.2

private lemma integral_graphon_pair_ne (W : Graphon) {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    ∫ u, (W (u a, u b) : ℝ) ∂(piVol N) = graphonEdgeDensity W := by
  have hmp := measurePreserving_pair_ne hab
  have hmeas : AEStronglyMeasurable (fun p : U × U => (W p : ℝ))
      ((volume : Measure U).prod (volume : Measure U)) :=
    (measurable_subtype_coe.comp W.measurable).aestronglyMeasurable
  unfold graphonEdgeDensity
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rwa [hmp.map_eq])]

private lemma graphonEdgeDensity_nonneg (W : Graphon) : 0 ≤ graphonEdgeDensity W :=
  integral_nonneg fun p => (W p).2.1

private lemma case_k_one (W : Graphon) :
    (graphonEdgeDensity W) ^ (cycleGraph 2).edgeFinset.card ≤
      graphonHomDensity (cycleGraph 2) W := by
  have hedges : (cycleGraph 2).edgeFinset = {s((0 : Fin 2), (1 : Fin 2))} := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_singleton]
      fin_cases u <;> fin_cases v <;> decide
  have hcard : (cycleGraph 2).edgeFinset.card = 1 := by
    rw [hedges, Finset.card_singleton]
  rw [hcard, pow_one]
  have hden : graphonHomDensity (cycleGraph 2) W = graphonEdgeDensity W := by
    unfold graphonHomDensity graphonHomIntegrand graphonEdgeDensity
    have hint : ∀ x : Fin 2 → U,
        (∏ e ∈ (cycleGraph 2).edgeFinset, W.evalEdge x e) = (W (x 0, x 1) : ℝ) := by
      intro x
      rw [hedges, Finset.prod_singleton]
      rfl
    simp_rw [hint]
    have hmp : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := U))
        (piVol 2) ((volume : Measure U).prod (volume : Measure U)) :=
      measurePreserving_finTwoArrow (volume : Measure U)
    have hmeas : AEStronglyMeasurable (fun p : U × U => (W p : ℝ))
        ((volume : Measure U).prod (volume : Measure U)) :=
      (measurable_subtype_coe.comp W.measurable).aestronglyMeasurable
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rwa [hmp.map_eq])]
    rfl
  rw [hden]

private lemma cycleGraph_edgeFinset_eq {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    (cycleGraph m).edgeFinset = Finset.univ.image (fun i : Fin m => s(i, i + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_edgeFinset, mem_edgeSet, cycleGraph_adj, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | h)
      · refine ⟨v, ?_⟩
        have huv : u = v + 1 := by rw [← h]; abel
        rw [huv, Sym2.eq_swap]
      · refine ⟨u, ?_⟩
        have hvu : v = u + 1 := by rw [← h]; abel
        rw [hvu]
    · rintro ⟨i, hi⟩
      rw [Sym2.eq_iff] at hi
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; simp
      · left; simp

private lemma cycleGraph_edgeOf_injective {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    Function.Injective (fun i : Fin m => s(i, i + 1)) := by
  intro i j hij
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have htwo : (1 : Fin m) + 1 = 0 := by
      have h : i + ((1 : Fin m) + 1) = i + 0 := by
        rw [← add_assoc, h2, h1, add_zero]
      exact add_left_cancel h
    have hval : ((1 : Fin m) + 1).val = (0 : Fin m).val := congrArg Fin.val htwo
    have h1val : (1 : Fin m).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [Fin.val_add, h1val, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
    omega

private lemma cycleGraph_card_edgeFinset {m : ℕ} (hm : 3 ≤ m) :
    (cycleGraph m).edgeFinset.card = m := by
  have : NeZero m := ⟨by omega⟩
  rw [cycleGraph_edgeFinset_eq hm,
    Finset.card_image_of_injective _ (cycleGraph_edgeOf_injective hm),
    Finset.card_univ, Fintype.card_fin]

private lemma cycleGraph_homIntegrand {m : ℕ} [NeZero m] (hm : 3 ≤ m) (W : Graphon) (x : Fin m → U) :
    graphonHomIntegrand (cycleGraph m) W x = ∏ i : Fin m, (W (x i, x (i + 1)) : ℝ) := by
  unfold graphonHomIntegrand
  rw [cycleGraph_edgeFinset_eq hm,
    Finset.prod_image (fun a _ b _ h => cycleGraph_edgeOf_injective hm h)]
  rfl

private lemma cycle_prod_integrable {m N : ℕ} [NeZero m] (W : Graphon) (f : Fin m → Fin N) :
    Integrable (fun u : Fin N → U => ∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) (piVol N) := by
  have hmeas : Measurable (fun u : Fin N → U => ∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) :=
    Finset.measurable_prod Finset.univ fun i _ => graphon_entry_measurable W (f i) (f (i + 1))
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards with u
  have hnn : 0 ≤ ∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ) :=
    Finset.prod_nonneg fun i _ => (W (u (f i), u (f (i + 1)))).2.1
  have hle : ∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (W (u (f i), u (f (i + 1)))).2.1)
      (fun i _ => (W (u (f i), u (f (i + 1)))).2.2)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

private lemma integral_cycle_prod_of_injective {m N : ℕ} [NeZero m] (hm : 3 ≤ m) (W : Graphon)
    (f : Fin m → Fin N) (hf : Function.Injective f) :
    ∫ u, (∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N) =
      graphonHomDensity (cycleGraph m) W := by
  have hmp := measurePreserving_comp_injective f hf
  have hFmeas : Measurable (fun x : Fin m → U => ∏ i : Fin m, (W (x i, x (i + 1)) : ℝ)) :=
    Finset.measurable_prod Finset.univ fun i _ => graphon_entry_measurable W i (i + 1)
  unfold graphonHomDensity
  simp_rw [cycleGraph_homIntegrand hm W]
  change ∫ u, (∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N) =
    ∫ x, (∏ i : Fin m, (W (x i, x (i + 1)) : ℝ)) ∂(piVol m)
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hFmeas.aestronglyMeasurable)]
  rfl

private lemma integral_cycle_prod_le_one {m N : ℕ} [NeZero m] (W : Graphon) (f : Fin m → Fin N) :
    ∫ u, (∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N) ≤ 1 := by
  have hle : ∀ u : Fin N → U, (∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) ≤ (1 : ℝ) := by
    intro u
    exact Finset.prod_le_one (fun i _ => (W (u (f i), u (f (i + 1)))).2.1)
      (fun i _ => (W (u (f i), u (f (i + 1)))).2.2)
  calc ∫ u, (∏ i : Fin m, (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N)
      ≤ ∫ _u : Fin N → U, (1 : ℝ) ∂(piVol N) :=
        integral_mono (cycle_prod_integrable W f) (integrable_const 1) hle
    _ = 1 := by simp

private lemma graphonHomDensity_nonneg {m : ℕ} (hm : 3 ≤ m) (W : Graphon) :
    0 ≤ graphonHomDensity (cycleGraph m) W := by
  have : NeZero m := ⟨by omega⟩
  unfold graphonHomDensity
  simp_rw [cycleGraph_homIntegrand hm W]
  exact integral_nonneg fun x => Finset.prod_nonneg fun i _ => (W (x i, x (i + 1))).2.1

private lemma matrix_pow_apply_eq_sum {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ∀ (n : ℕ) (a b : Fin N),
      (A ^ (n + 1)) a b =
        ∑ f : Fin (n + 1) → Fin N,
          if f 0 = a then (∏ i : Fin n, A (f i.castSucc) (f i.succ)) * A (f (Fin.last n)) b else 0 := by
  intro n
  induction n with
  | zero =>
    intro a b
    rw [pow_one]
    let e : (Fin 1 → Fin N) ≃ Fin N := Equiv.funUnique (Fin 1) (Fin N)
    rw [← Equiv.sum_comp e.symm]
    simp [e]
  | succ n ih =>
    intro a b
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    let snocFun (f : Fin (n + 1) → Fin N) (c : Fin N) (i : Fin (n + 2)) : Fin N :=
      if h : i.1 < n + 1 then f ⟨i.1, h⟩ else c
    let e : (Fin (n + 1) → Fin N) × Fin N ≃ (Fin (n + 2) → Fin N) :=
      { toFun := fun p => snocFun p.1 p.2
        invFun := fun g => (fun i => g i.castSucc, g (Fin.last (n + 1)))
        left_inv := fun ⟨f, c⟩ => by
          ext i
          · simp only [snocFun, Fin.val_castSucc, i.2, ↓reduceDIte, Fin.eta]
          · simp only [snocFun, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
        right_inv := fun g => by
          funext i
          by_cases h : i.1 < n + 1
          · simp only [snocFun, h, ↓reduceDIte]
            rfl
          · have hlast : i = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
            rw [hlast]
            simp only [snocFun, Fin.val_last, lt_self_iff_false, ↓reduceDIte] }
    rw [← Equiv.sum_comp e]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    change (if f 0 = a then (∏ i : Fin n, A (f i.castSucc) (f i.succ)) * A (f (Fin.last n)) c else 0) * A c b =
      if snocFun f c 0 = a then
        (∏ i : Fin (n + 1), A (snocFun f c i.castSucc) (snocFun f c i.succ)) *
          A (snocFun f c (Fin.last (n + 1))) b
      else 0
    have h0 : snocFun f c 0 = f 0 := by simp [snocFun]
    have hlast : snocFun f c (Fin.last (n + 1)) = c := by simp [snocFun]
    rw [h0, hlast]
    split_ifs
    · rw [Fin.prod_univ_castSucc]
      congr 1
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h1 : snocFun f c i.castSucc.castSucc = f i.castSucc := by
          simp only [snocFun, Fin.val_castSucc, Nat.lt_succ_of_lt i.2, ↓reduceDIte]
          rfl
        have h2 : snocFun f c i.castSucc.succ = f i.succ := by
          simp only [snocFun, Fin.val_succ, Fin.val_castSucc, Nat.succ_lt_succ i.2, ↓reduceDIte]
          rfl
        rw [h1, h2]
      · congr 1
        · simp only [snocFun, Fin.val_castSucc, Fin.val_last, lt_add_one, ↓reduceDIte]
          rfl
        · simp only [snocFun, Fin.val_succ, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    · simp

private lemma matrix_trace_pow_succ_eq_sum {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    (A ^ (n + 1)).trace = ∑ f : Fin (n + 1) → Fin N, ∏ i : Fin (n + 1), A (f i) (f (i + 1)) := by
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply, matrix_pow_apply_eq_sum A n]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hsucc : (i.castSucc : Fin (n + 1)) + 1 = i.succ := by
      apply Fin.ext
      have hi : i.1 + 1 < n + 1 := Nat.succ_lt_succ i.2
      have h1 : (1 : Fin (n + 1)).val = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [Fin.val_add, h1, Fin.val_castSucc, Fin.val_succ, Nat.mod_eq_of_lt hi]
    rw [hsucc]
  · have hlast : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
      apply Fin.ext
      have h1 : (1 : Fin (n + 1)).val = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [Fin.val_add, h1, Fin.val_last, Fin.val_zero, Nat.mod_self]
    rw [hlast]

private lemma matrix_trace_pow_eq_sum {N m : ℕ} [NeZero m] (A : Matrix (Fin N) (Fin N) ℝ)
    (hm : 2 ≤ m) :
    (A ^ m).trace = ∑ f : Fin m → Fin N, ∏ i : Fin m, A (f i) (f (i + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  convert matrix_trace_pow_succ_eq_sum A n (by omega)

private lemma symmetric_matrix_trace_even_pow_ge {N k : ℕ} (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    ((1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ (2 * k) ≤
      (A ^ (2 * k)).trace := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let U := hA.eigenvectorUnitary
  let ev : Fin N → ℝ := hA.eigenvalues
  have hspec : A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal ev *
      star (U : Matrix (Fin N) (Fin N) ℝ) := by
    have h := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, U, ev] using h
  have hpow : A ^ (2 * k) =
      Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => ev i ^ (2 * k))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    rfl
  have htr : (A ^ (2 * k)).trace = ∑ i : Fin N, ev i ^ (2 * k) := by
    rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    have hUU : star (U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hUU, one_mul, Matrix.trace_diagonal]
  let v : Fin N → ℝ := fun _ => 1 / Real.sqrt (N : ℝ)
  have hvv : v ⬝ᵥ v = 1 := by
    simp only [dotProduct, v]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    field_simp [hsq_ne, ne_of_gt hNpos]
    linarith
  let w : Fin N → ℝ := (star (U : Matrix (Fin N) (Fin N) ℝ)).mulVec v
  have hstar_tr : star (U : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.transpose (U : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hww : ∑ i : Fin N, w i ^ 2 = 1 := by
    have hdot : w ⬝ᵥ w = 1 := by
      dsimp only [w]
      rw [Matrix.dotProduct_mulVec, hstar_tr, Matrix.vecMul_transpose,
        ← hstar_tr, Matrix.mulVec_mulVec]
      have hUU : (U : Matrix (Fin N) (Fin N) ℝ) * star (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
        Unitary.coe_mul_star_self U
      rw [hUU, Matrix.one_mulVec, hvv]
    simpa [dotProduct, sq] using hdot
  have hquad_lhs : v ⬝ᵥ (A.mulVec v) = (1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b := by
    simp only [dotProduct, Matrix.mulVec, v, Finset.mul_sum]
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp [hsq_ne, ne_of_gt hNpos]
    rw [Real.sq_sqrt (le_of_lt hNpos)]
    ring
  have hquad_rhs : v ⬝ᵥ (A.mulVec v) = ∑ i : Fin N, w i ^ 2 * ev i := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have hvU : Matrix.vecMul v (U : Matrix (Fin N) (Fin N) ℝ) = w := by
      dsimp only [w]
      rw [hstar_tr, Matrix.mulVec_transpose]
    rw [hvU]
    change w ⬝ᵥ ((Matrix.diagonal ev).mulVec w) = _
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (even_two_mul k).convexOn_pow
  have hjensen := hconv.map_sum_le (t := Finset.univ) (w := fun i => w i ^ 2) (p := ev)
    (fun i _ => sq_nonneg (w i)) hww (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  have hle_tr : ∑ i : Fin N, w i ^ 2 * ev i ^ (2 * k) ≤ ∑ i : Fin N, ev i ^ (2 * k) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hw_le : w i ^ 2 ≤ 1 := by
      rw [← hww]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    have hev_nn : 0 ≤ ev i ^ (2 * k) := (even_two_mul k).pow_nonneg (ev i)
    nlinarith
  rw [← hquad_lhs, hquad_rhs, htr]
  exact le_trans hjensen hle_tr

private lemma card_nonInjective_le (m N : ℕ) :
    (Finset.univ.filter (fun f : Fin m → Fin N => ¬ Function.Injective f)).card ≤
      m ^ 2 * N ^ (m - 1) := by
  classical
  let nonInj := Finset.univ.filter (fun f : Fin m → Fin N => ¬ Function.Injective f)
  let pairs := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2)
  let badPair (p : Fin m × Fin m) : Finset (Fin m → Fin N) :=
    Finset.univ.filter (fun f => f p.1 = f p.2)
  have hsub : nonInj ⊆ pairs.biUnion badPair := by
    intro f hf
    simp only [nonInj, Finset.mem_filter, Finset.mem_univ, true_and, Function.Injective,
      not_forall] at hf
    rcases hf with ⟨i, j, h⟩
    push Not at h
    refine Finset.mem_biUnion.mpr ⟨(i, j), ?_, ?_⟩
    · simp [pairs, h.2]
    · simp [badPair, h.1]
  have hpair_card : ∀ p ∈ pairs, (badPair p).card ≤ N ^ (m - 1) := by
    intro p hp
    simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let res : (Fin m → Fin N) → ({ r : Fin m // r ≠ p.2 } → Fin N) := fun f r => f r.1
    have hinj : Set.InjOn res (badPair p) := by
      intro f₁ hf₁ f₂ hf₂ heq
      simp only [Finset.mem_coe, badPair, Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
      funext r
      by_cases hr : r = p.2
      · subst hr
        rw [← hf₁, ← hf₂]
        exact congrFun heq ⟨p.1, hp⟩
      · exact congrFun heq ⟨r, hr⟩
    have hle := Finset.card_le_card_of_injOn res (fun _ _ => Finset.mem_univ _) hinj
    have hcard_dom : Fintype.card { r : Fin m // r ≠ p.2 } = m - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard_dom] using hle
  have hpairs_le : pairs.card ≤ m ^ 2 := by
    calc pairs.card
        ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_filter_le _ _
      _ = m ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  calc nonInj.card
      ≤ (pairs.biUnion badPair).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs, (badPair p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, N ^ (m - 1) := Finset.sum_le_sum hpair_card
    _ = pairs.card * N ^ (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ m ^ 2 * N ^ (m - 1) := Nat.mul_le_mul_right _ hpairs_le

private lemma finite_sample_bound {k : ℕ} (hk : 2 ≤ k) (W : Graphon) {N : ℕ} (hN : 1 ≤ N) :
    ((1 - 1 / (N : ℝ)) * graphonEdgeDensity W) ^ (2 * k) ≤
      graphonHomDensity (cycleGraph (2 * k)) W + ((2 * k : ℕ) : ℝ) ^ 2 / (N : ℝ) := by
  classical
  have : NeZero (2 * k) := ⟨by omega⟩
  have hm3 : 3 ≤ 2 * k := by omega
  have hm2 : 2 ≤ 2 * k := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let A (u : Fin N → U) : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun a b => (W (u a, u b) : ℝ)
  have hAherm : ∀ u, (A u).IsHermitian := by
    intro u
    ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial, A, Matrix.of_apply, W.symmetric]
  let avg (u : Fin N → U) : ℝ :=
    (1 / ((N : ℝ) ^ 2)) * ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ)
  let trScaled (u : Fin N → U) : ℝ :=
    (1 / ((N : ℝ) ^ (2 * k))) *
      ∑ f : Fin (2 * k) → Fin N, ∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)
  have hpt : ∀ u : Fin N → U, avg u ^ (2 * k) ≤ trScaled u := by
    intro u
    have hspec := symmetric_matrix_trace_even_pow_ge (k := k) hN (A u) (hAherm u)
    rw [matrix_trace_pow_eq_sum (A u) hm2] at hspec
    have havg : avg u = (1 / (N : ℝ)) * ((1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A u a b) := by
      simp only [avg, A, Matrix.of_apply]
      field_simp [ne_of_gt hNpos]
    rw [havg, mul_pow, one_div_pow]
    dsimp only [trScaled]
    rw [one_div]
    have hnn : (0 : ℝ) ≤ ((N : ℝ) ^ (2 * k))⁻¹ := by positivity
    simpa [A, Matrix.of_apply] using mul_le_mul_of_nonneg_left hspec hnn
  have havg_meas : Measurable avg := by
    refine measurable_const.mul ?_
    refine Finset.measurable_sum Finset.univ fun a _ => ?_
    exact Finset.measurable_sum Finset.univ fun b _ => graphon_entry_measurable W a b
  have havg_int : Integrable avg (piVol N) := by
    refine Integrable.of_bound havg_meas.aestronglyMeasurable 1 ?_
    filter_upwards with u
    have hsum_nn : 0 ≤ ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => (W (u a, u b)).2.1
    have hsum_le : ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ) ≤ (N : ℝ) ^ 2 := by
      calc ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ)
          ≤ ∑ _a : Fin N, ∑ _b : Fin N, (1 : ℝ) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (W (u a, u b)).2.2
        _ = (N : ℝ) ^ 2 := by simp [sq]
    have hnn : 0 ≤ avg u := mul_nonneg (by positivity) hsum_nn
    have hle : avg u ≤ 1 := by
      dsimp only [avg]
      rw [one_div_mul_eq_div, div_le_one (by positivity)]
      exact hsum_le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle
  have havg_pow_int : Integrable (fun u => avg u ^ (2 * k)) (piVol N) := by
    refine Integrable.of_bound (havg_meas.pow_const (2 * k)).aestronglyMeasurable 1 ?_
    filter_upwards with u
    have hsum_nn : 0 ≤ ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => (W (u a, u b)).2.1
    have hsum_le : ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ) ≤ (N : ℝ) ^ 2 := by
      calc ∑ a : Fin N, ∑ b : Fin N, (W (u a, u b) : ℝ)
          ≤ ∑ _a : Fin N, ∑ _b : Fin N, (1 : ℝ) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (W (u a, u b)).2.2
        _ = (N : ℝ) ^ 2 := by simp [sq]
    have hnn : 0 ≤ avg u := mul_nonneg (by positivity) hsum_nn
    have hle : avg u ≤ 1 := by
      dsimp only [avg]
      rw [one_div_mul_eq_div, div_le_one (by positivity)]
      exact hsum_le
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnn _)]
    exact pow_le_one₀ hnn hle
  have htr_int : Integrable trScaled (piVol N) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum Finset.univ fun f _ => cycle_prod_integrable W f
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (even_two_mul k).convexOn_pow
  have hjensen : (∫ u, avg u ∂(piVol N)) ^ (2 * k) ≤ ∫ u, avg u ^ (2 * k) ∂(piVol N) :=
    hconv.map_integral_le (continuous_pow (2 * k)).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) havg_int havg_pow_int
  have hint_mono : ∫ u, avg u ^ (2 * k) ∂(piVol N) ≤ ∫ u, trScaled u ∂(piVol N) :=
    integral_mono havg_pow_int htr_int hpt
  have havg_lb : (1 - 1 / (N : ℝ)) * graphonEdgeDensity W ≤ ∫ u, avg u ∂(piVol N) := by
    have hsum_int : ∫ u, avg u ∂(piVol N) =
        (1 / ((N : ℝ) ^ 2)) * ∑ a : Fin N, ∑ b : Fin N, ∫ u, (W (u a, u b) : ℝ) ∂(piVol N) := by
      dsimp only [avg]
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum Finset.univ fun a _ =>
        integrable_finsetSum Finset.univ fun b _ => graphon_entry_integrable W a b]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact integral_finsetSum Finset.univ fun b _ => graphon_entry_integrable W a b
    rw [hsum_int]
    have hterm_lb : ∀ a b : Fin N,
        (if a = b then (0 : ℝ) else graphonEdgeDensity W) ≤
          ∫ u, (W (u a, u b) : ℝ) ∂(piVol N) := by
      intro a b
      by_cases hab : a = b
      · rw [if_pos hab]
        exact integral_nonneg fun u => (W (u a, u b)).2.1
      · rw [if_neg hab, integral_graphon_pair_ne W hab]
    have hsum_lb : ∑ a : Fin N, ∑ b : Fin N, (if a = b then (0 : ℝ) else graphonEdgeDensity W) =
        ((N : ℝ) ^ 2 - (N : ℝ)) * graphonEdgeDensity W := by
      have hinner : ∀ a : Fin N,
          ∑ b : Fin N, (if a = b then (0 : ℝ) else graphonEdgeDensity W) =
            ((N : ℝ) - 1) * graphonEdgeDensity W := by
        intro a
        have hsplit : ∑ b : Fin N, (if a = b then (0 : ℝ) else graphonEdgeDensity W) +
            graphonEdgeDensity W = ∑ _b : Fin N, graphonEdgeDensity W := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
          rw [add_comm]
          have h0 : ∑ b ∈ Finset.univ.erase a,
              (if a = b then (0 : ℝ) else graphonEdgeDensity W) =
              ∑ _b ∈ Finset.univ.erase a, graphonEdgeDensity W := by
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hb))]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos rfl, zero_add, h0]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsplit
        linarith
      simp_rw [hinner]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hge := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hterm_lb a b
    rw [hsum_lb] at hge
    have hmul := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ 2))
    have heq : (1 / ((N : ℝ) ^ 2)) * (((N : ℝ) ^ 2 - (N : ℝ)) * graphonEdgeDensity W) =
        (1 - 1 / (N : ℝ)) * graphonEdgeDensity W := by
      field_simp [ne_of_gt hNpos]
    rwa [heq] at hmul
  have hlhs : ((1 - 1 / (N : ℝ)) * graphonEdgeDensity W) ^ (2 * k) ≤
      (∫ u, avg u ∂(piVol N)) ^ (2 * k) := by
    have hnn : 0 ≤ (1 - 1 / (N : ℝ)) * graphonEdgeDensity W := by
      refine mul_nonneg ?_ (graphonEdgeDensity_nonneg W)
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have : 1 / (N : ℝ) ≤ 1 := (div_le_one hNpos).mpr h1
      linarith
    exact pow_le_pow_left₀ hnn havg_lb (2 * k)
  have hrhs : ∫ u, trScaled u ∂(piVol N) ≤
      graphonHomDensity (cycleGraph (2 * k)) W + ((2 * k : ℕ) : ℝ) ^ 2 / (N : ℝ) := by
    have htr_eq : ∫ u, trScaled u ∂(piVol N) =
        (1 / ((N : ℝ) ^ (2 * k))) *
          ∑ f : Fin (2 * k) → Fin N,
            ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N) := by
      dsimp only [trScaled]
      rw [integral_const_mul, integral_finsetSum Finset.univ fun f _ => cycle_prod_integrable W f]
    rw [htr_eq]
    let injSet := Finset.univ.filter (fun f : Fin (2 * k) → Fin N => Function.Injective f)
    let nonInjSet := Finset.univ.filter (fun f : Fin (2 * k) → Fin N => ¬ Function.Injective f)
    have hsplit :
        ∑ f : Fin (2 * k) → Fin N,
          ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N) =
        (∑ f ∈ injSet,
          ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N)) +
        (∑ f ∈ nonInjSet,
          ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N)) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun f : Fin (2 * k) → Fin N => Function.Injective f) _).symm
    have hinj_le :
        (∑ f ∈ injSet,
          ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N)) ≤
        ((N : ℝ) ^ (2 * k)) * graphonHomDensity (cycleGraph (2 * k)) W := by
      have heq_sum :
          (∑ f ∈ injSet,
            ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N)) =
          (injSet.card : ℝ) * graphonHomDensity (cycleGraph (2 * k)) W := by
        have hcongr : ∀ f ∈ injSet,
            ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N) =
              graphonHomDensity (cycleGraph (2 * k)) W := by
          intro f hf
          simp only [injSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          exact integral_cycle_prod_of_injective hm3 W f hf
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
      rw [heq_sum]
      have hcard_le : (injSet.card : ℝ) ≤ (N : ℝ) ^ (2 * k) := by
        have hnat : injSet.card ≤ N ^ (2 * k) := by
          calc injSet.card
              ≤ (Finset.univ : Finset (Fin (2 * k) → Fin N)).card := Finset.card_filter_le _ _
            _ = N ^ (2 * k) := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right hcard_le (graphonHomDensity_nonneg hm3 W)
    have hnonInj_le :
        (∑ f ∈ nonInjSet,
          ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N)) ≤
        ((2 * k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (2 * k - 1) := by
      calc (∑ f ∈ nonInjSet,
            ∫ u, (∏ i : Fin (2 * k), (W (u (f i), u (f (i + 1))) : ℝ)) ∂(piVol N))
          ≤ ∑ _f ∈ nonInjSet, (1 : ℝ) :=
            Finset.sum_le_sum fun f _ => integral_cycle_prod_le_one W f
        _ = (nonInjSet.card : ℝ) := by simp
        _ ≤ ((2 * k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (2 * k - 1) := by
            have hnat := card_nonInjective_le (2 * k) N
            exact_mod_cast hnat
    rw [hsplit]
    have htot := add_le_add hinj_le hnonInj_le
    have hmul := mul_le_mul_of_nonneg_left htot (by positivity : (0 : ℝ) ≤ 1 / ((N : ℝ) ^ (2 * k)))
    have hpow_split : (N : ℝ) ^ (2 * k) = (N : ℝ) * (N : ℝ) ^ (2 * k - 1) := by
      have hexp : 2 * k = 1 + (2 * k - 1) := by omega
      conv_lhs => rw [hexp, pow_add, pow_one]
    have hsimp :
        (1 / ((N : ℝ) ^ (2 * k))) *
          (((N : ℝ) ^ (2 * k)) * graphonHomDensity (cycleGraph (2 * k)) W +
            ((2 * k : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (2 * k - 1)) =
        graphonHomDensity (cycleGraph (2 * k)) W + ((2 * k : ℕ) : ℝ) ^ 2 / (N : ℝ) := by
      have hpow_ne : (N : ℝ) ^ (2 * k - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hNpos)
      rw [mul_add, hpow_split]
      field_simp [ne_of_gt hNpos, hpow_ne]
    rwa [hsimp] at hmul
  exact le_trans hlhs (le_trans hjensen (le_trans hint_mono hrhs))

end SidorenkoEvenCycleGraphonProof

theorem OMA.solution : type_of% @SidorenkoConjecture.sidorenko_even_cycle_graphon := by
  intro k hk W
  by_cases hk1 : k = 1
  · subst hk1
    simpa using SidorenkoEvenCycleGraphonProof.case_k_one W
  · have hk2 : 2 ≤ k := by omega
    have hm3 : 3 ≤ 2 * k := by omega
    rw [SidorenkoEvenCycleGraphonProof.cycleGraph_card_edgeFinset hm3]
    have h1 : Filter.Tendsto (fun N : ℕ => ((1 - 1 / (N : ℝ)) * LimitObjects.graphonEdgeDensity W) ^ (2 * k))
        Filter.atTop (nhds ((LimitObjects.graphonEdgeDensity W) ^ (2 * k))) := by
      have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hsub : Filter.Tendsto (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub h0
      have hmul : Filter.Tendsto (fun N : ℕ => (1 - 1 / (N : ℝ)) * LimitObjects.graphonEdgeDensity W)
          Filter.atTop (nhds ((1 - 0) * LimitObjects.graphonEdgeDensity W)) :=
        hsub.mul tendsto_const_nhds
      simpa using hmul.pow (2 * k)
    have h2 : Filter.Tendsto
        (fun N : ℕ => LimitObjects.graphonHomDensity (SimpleGraph.cycleGraph (2 * k)) W +
          ((2 * k : ℕ) : ℝ) ^ 2 / (N : ℝ))
        Filter.atTop (nhds (LimitObjects.graphonHomDensity (SimpleGraph.cycleGraph (2 * k)) W)) := by
      have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hdiv : Filter.Tendsto (fun N : ℕ => ((2 * k : ℕ) : ℝ) ^ 2 * (1 / (N : ℝ)))
          Filter.atTop (nhds (((2 * k : ℕ) : ℝ) ^ 2 * 0)) :=
        tendsto_const_nhds.mul h0
      have hdiv' : Filter.Tendsto (fun N : ℕ => ((2 * k : ℕ) : ℝ) ^ 2 / (N : ℝ))
          Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hdiv
      simpa using tendsto_const_nhds.add hdiv'
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    exact Filter.eventually_atTop.mpr ⟨1, fun N hN =>
      SidorenkoEvenCycleGraphonProof.finite_sample_bound hk2 W hN⟩
