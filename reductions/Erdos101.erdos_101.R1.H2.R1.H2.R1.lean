import OMAReductions.R_Erdos101_erdos_101_R1_H2_R1
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Order.Interval.Set.Infinite

-- Reduction Erdos101.erdos_101.R1.H2.R1.H2.R1 of step Erdos101.erdos_101.R1.H2.R1.H2
-- Credit: @DPS0340

/-!
# Mixed-component Elekes-Szabó curve rigidity reduction

We reduce the mixed-component triple-line estimate
`OMA.R_Erdos101_erdos_101_R1_H2_R1.H2` into two core components of Elekes and Szabó,
*On Triple Lines and Cubic Curves* (Theorem 4.1 and Lemma 2):

1. In `main`, we first eliminate vertical lines (proving at most `S.card` lines in `A`
   contain two points with equal first coordinate, retaining at least `(ε / 2) n^2`
   non-vertical collinear triples on distinct lines).
2. `H1` extracts from a quadratic-density family of non-vertical collinear triples on
   distinct lines across three nonlinear irreducible curves `F, G, H` an affine chart
   `(α, β, γ)` forming a standard system of continuous arcs on `(-r, r)` lying on
   `e(Z(F)), e(Z(G)), e(Z(H))` whose collinearity is governed additively over `ℝ`.
3. `H2` (Elekes-Szabó Lemma 2) asserts that any standard system with additive collinearity
   vanishes on a nonzero cubic polynomial `P` over a nonempty open subinterval `(-r', r')`.
4. In `main`, we pull `F` and `G` back through the affine equivalence `e`, prove via
   Gauss's lemma and clearing denominators in `(FractionRing ℝ[X])[Y]` that an irreducible
   bivariate polynomial sharing an infinite graph arc with `P` must divide `P`, apply this
   to both non-associated factors `φ F` and `φ G` to obtain `φ F * φ G ∣ P`, and derive
   the degree contradiction `4 ≤ deg(φ F) + deg(φ G) ≤ deg P ≤ 3`.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H2_R1_H2_R1

open EuclideanGeometry MvPolynomial
open scoped Classical Polynomial

/-- Mixed-component surface extraction: a quadratic-density family of non-vertical
collinear triples on distinct lines across three nonlinear irreducible plane curves yields
an affine change of coordinates in which three open arcs on the three curves form a standard
system whose collinearity is additive over `ℝ`. -/
def H1 : Prop :=
  ∀ d : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n →
      ∀ F G H : MvPolynomial (Fin 2) ℝ,
        Irreducible F → Irreducible G → Irreducible H →
        2 ≤ F.totalDegree → 2 ≤ G.totalDegree → 2 ≤ H.totalDegree →
        F.totalDegree ≤ d → G.totalDegree ≤ d → H.totalDegree ≤ d →
        ∀ T : Finset (S × S × S), δ * (n : ℝ)^2 ≤ T.card →
          (T : Set (S × S × S)).InjOn (fun t => line[ℝ, (t.1 : ℝ²), (t.2.1 : ℝ²)]) →
          (∀ t ∈ T, eval (fun i => (t.1 : ℝ²) i) F = 0 ∧
            eval (fun i => (t.2.1 : ℝ²) i) G = 0 ∧
            eval (fun i => (t.2.2 : ℝ²) i) H = 0 ∧
            (t.1 : ℝ²) 0 ≠ (t.2.1 : ℝ²) 0 ∧ (t.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
            (t.2.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
            Collinear ℝ ({(t.1 : ℝ²), (t.2.1 : ℝ²), (t.2.2 : ℝ²)} : Set ℝ²)) →
          ∃ (e : ℝ² ≃ᵃ[ℝ] ℝ²) (r : ℝ) (α β γ f₁ f₂ f₃ : ℝ → ℝ),
            0 < r ∧
            let I := Set.Ioo (-r) r
            ContinuousOn α I ∧ ContinuousOn β I ∧ ContinuousOn γ I ∧
            ContinuousOn f₁ I ∧ ContinuousOn f₂ I ∧ ContinuousOn f₃ I ∧
            Set.InjOn f₁ I ∧ Set.InjOn f₂ I ∧ Set.InjOn f₃ I ∧
            (∀ x ∈ I, α x < β x ∧ β x < γ x) ∧
            (∀ x ∈ I,
              eval (fun i => e.symm !₂[x, α x] i) F = 0 ∧
              eval (fun i => e.symm !₂[x, β x] i) G = 0 ∧
              eval (fun i => e.symm !₂[x, γ x] i) H = 0) ∧
            (∀ L : AffineSubspace ℝ ℝ², ∀ p₁ p₂ q : ℝ², p₁ ≠ p₂ → p₁ ∈ L → p₂ ∈ L → q ∈ L →
              ∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ y ∈ I,
                ¬ ((p₁ = !₂[x₁, α x₁] ∧ p₂ = !₂[x₂, α x₂] ∧ (q = !₂[y, β y] ∨ q = !₂[y, γ y])) ∨
                   (p₁ = !₂[x₁, β x₁] ∧ p₂ = !₂[x₂, β x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, γ y])) ∨
                   (p₁ = !₂[x₁, γ x₁] ∧ p₂ = !₂[x₂, γ x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, β y])))) ∧
            (∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ x₃ ∈ I,
              Collinear ℝ ({!₂[x₁, α x₁], !₂[x₂, β x₂], !₂[x₃, γ x₃]} : Set ℝ²) ↔
                f₁ x₁ + f₂ x₂ + f₃ x₃ = 0)

/-- Elekes-Szabó Lemma 2: if collinearity between the graphs of a standard system of
continuous real functions is described additively via continuous injections into `(ℝ, +)`,
then their graphs agree on a nonempty open interval around `0` with a nonzero cubic curve. -/
def H2 : Prop :=
  ∀ (r : ℝ) (α β γ f₁ f₂ f₃ : ℝ → ℝ),
    0 < r →
    let I := Set.Ioo (-r) r
    ContinuousOn α I → ContinuousOn β I → ContinuousOn γ I →
    ContinuousOn f₁ I → ContinuousOn f₂ I → ContinuousOn f₃ I →
    Set.InjOn f₁ I → Set.InjOn f₂ I → Set.InjOn f₃ I →
    (∀ x ∈ I, α x < β x ∧ β x < γ x) →
    (∀ L : AffineSubspace ℝ ℝ², ∀ p₁ p₂ q : ℝ², p₁ ≠ p₂ → p₁ ∈ L → p₂ ∈ L → q ∈ L →
      ∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ y ∈ I,
        ¬ ((p₁ = !₂[x₁, α x₁] ∧ p₂ = !₂[x₂, α x₂] ∧ (q = !₂[y, β y] ∨ q = !₂[y, γ y])) ∨
           (p₁ = !₂[x₁, β x₁] ∧ p₂ = !₂[x₂, β x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, γ y])) ∨
           (p₁ = !₂[x₁, γ x₁] ∧ p₂ = !₂[x₂, γ x₂] ∧ (q = !₂[y, α y] ∨ q = !₂[y, β y])))) →
    (∀ x₁ ∈ I, ∀ x₂ ∈ I, ∀ x₃ ∈ I,
      Collinear ℝ ({!₂[x₁, α x₁], !₂[x₂, β x₂], !₂[x₃, γ x₃]} : Set ℝ²) ↔
        f₁ x₁ + f₂ x₂ + f₃ x₃ = 0) →
    ∃ (r' : ℝ) (P : MvPolynomial (Fin 2) ℝ),
      0 < r' ∧ r' ≤ r ∧ P ≠ 0 ∧ P.totalDegree ≤ 3 ∧
      ∀ x ∈ Set.Ioo (-r') r',
        eval (fun i => (!₂[x, α x] : ℝ²) i) P = 0 ∧
        eval (fun i => (!₂[x, β x] : ℝ²) i) P = 0 ∧
        eval (fun i => (!₂[x, γ x] : ℝ²) i) P = 0

/- ### Vertical line elimination -/

section Helpers

private lemma vertical_line_eq {p q : ℝ²} (hpq : p ≠ q) (h0 : p 0 = q 0) :
    (line[ℝ, p, q] : Set ℝ²) = {u : ℝ² | u 0 = p 0} := by
  ext u
  rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    simp [AffineMap.lineMap_apply_module, h0]
    ring
  · intro hu0
    have h1 : q 1 - p 1 ≠ 0 := by
      intro h
      apply hpq
      ext i
      fin_cases i
      · exact h0
      · change p 1 = q 1; linarith
    refine ⟨(u 1 - p 1) / (q 1 - p 1), ?_⟩
    ext i
    fin_cases i
    · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      change (1 - (u 1 - p 1) / (q 1 - p 1)) * p 0 + ((u 1 - p 1) / (q 1 - p 1)) * q 0 = u 0
      rw [hu0, ← h0]; ring
    · simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      change (1 - (u 1 - p 1) / (q 1 - p 1)) * p 1 + ((u 1 - p 1) / (q 1 - p 1)) * q 1 = u 1
      field_simp [h1]
      ring

private lemma line_eq_of_mem_pair {x y p q : ℝ²} (hxy : x ≠ y) (hpq : p ≠ q)
    (hp : p ∈ line[ℝ, x, y]) (hq : q ∈ line[ℝ, x, y]) :
    line[ℝ, x, y] = line[ℝ, p, q] := by
  have hle : line[ℝ, p, q] ≤ line[ℝ, x, y] := by
    rw [affineSpan_le]
    intro u hu
    rcases hu with rfl | rfl <;> assumption
  have hdim1 : Module.finrank ℝ (line[ℝ, p, q]).direction = 1 := by
    rw [direction_affineSpan]
    have hne : q -ᵥ p ≠ (0 : ℝ²) := vsub_ne_zero.mpr hpq.symm
    have hspan : vectorSpan ℝ ({p, q} : Set ℝ²) = Submodule.span ℝ {q -ᵥ p} := by
      rw [vectorSpan_pair_rev]
    rw [hspan, finrank_span_singleton hne]
  have hdim2 : Module.finrank ℝ (line[ℝ, x, y]).direction = 1 := by
    rw [direction_affineSpan]
    have hne : y -ᵥ x ≠ (0 : ℝ²) := vsub_ne_zero.mpr hxy.symm
    have hspan : vectorSpan ℝ ({x, y} : Set ℝ²) = Submodule.span ℝ {y -ᵥ x} := by
      rw [vectorSpan_pair_rev]
    rw [hspan, finrank_span_singleton hne]
  have hdir : (line[ℝ, p, q]).direction = (line[ℝ, x, y]).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (hdim1.trans hdim2.symm)
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
    ⟨p, left_mem_affineSpan_pair ℝ p q⟩ hle).symm

private lemma card_vertical_lines_le {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hvert : ∀ L ∈ A, ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ line[ℝ, x, y] = L ∧ x 0 = y 0) :
    A.card ≤ S.card := by
  have hex : ∀ L ∈ A, ∃ c ∈ S.image (fun p : ℝ² => p 0), (L : Set ℝ²) = {u : ℝ² | u 0 = c} := by
    intro L hL
    obtain ⟨x, hxS, y, _, hxy, rfl, h0⟩ := hvert L hL
    exact ⟨x 0, Finset.mem_image_of_mem _ hxS, vertical_line_eq hxy h0⟩
  choose! c hcS hcEq using hex
  calc
    A.card ≤ (S.image (fun p : ℝ² => p 0)).card := by
      apply Finset.card_le_card_of_injOn c
      · intro L hL; exact hcS L hL
      · intro L₁ hL₁ L₂ hL₂ hEq
        apply SetLike.ext'
        rw [hcEq L₁ hL₁, hcEq L₂ hL₂, hEq]
    _ ≤ S.card := Finset.card_image_le

/- ### Affine pullback of bivariate polynomials -/

private lemma totalDegree_linear_form (a b c : ℝ) :
    (C c + C a * X (0 : Fin 2) + C b * X (1 : Fin 2)).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · exact (totalDegree_mul _ _).trans (by simp)

private lemma totalDegree_aeval_linear (g : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (Q : MvPolynomial (Fin 2) ℝ) :
    (aeval g Q).totalDegree ≤ Q.totalDegree := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum Q.support _).trans (Finset.sup_le fun s hs => ?_)
  rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    ← C_mul']
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  have hprod : (s.prod fun i e => g i ^ e).totalDegree ≤ s.sum fun _ e => e := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    exact (MvPolynomial.totalDegree_pow (g i) (s i)).trans (by have := hg i; nlinarith)
  exact hprod.trans (MvPolynomial.le_totalDegree hs)

private lemma algEquiv_irreducible {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A ≃ₐ[R] B) {x : A} (hx : Irreducible x) :
    Irreducible (φ x) := by
  refine ⟨fun hu => hx.not_isUnit ?_, fun a b hab => ?_⟩
  · have h := hu.map φ.symm.toRingHom
    simpa using h
  · have hmul : x = φ.symm a * φ.symm b := by
      have := congrArg φ.symm hab
      simpa using this
    rcases hx.isUnit_or_isUnit hmul with ha | hb
    · left; simpa using ha.map φ.toRingHom
    · right; simpa using hb.map φ.toRingHom

private lemma algEquiv_associated {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A ≃ₐ[R] B) {x y : A} (h : Associated (φ x) (φ y)) :
    Associated x y := by
  obtain ⟨u, hu⟩ := h
  refine ⟨Units.map φ.symm.toMonoidHom u, ?_⟩
  have h1 := congrArg φ.symm hu
  simpa using h1

private lemma exists_affine_pullback (e : ℝ² ≃ᵃ[ℝ] ℝ²) :
    ∃ φ : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 2) ℝ,
      (∀ Q : MvPolynomial (Fin 2) ℝ, (φ Q).totalDegree = Q.totalDegree) ∧
      (∀ (Q : MvPolynomial (Fin 2) ℝ) (p : ℝ²),
        eval (fun i => p i) (φ Q) = eval (fun i => e.symm p i) Q) := by
  let linOf (f : ℝ² →ᵃ[ℝ] ℝ²) (i : Fin 2) : MvPolynomial (Fin 2) ℝ :=
    C ((f 0) i) + C ((f.linear !₂[1, 0]) i) * X 0 + C ((f.linear !₂[0, 1]) i) * X 1
  have hlin_eval (f : ℝ² →ᵃ[ℝ] ℝ²) (p : ℝ²) (i : Fin 2) :
      eval (fun j => p j) (linOf f i) = (f p) i := by
    have hp : p = p 0 • !₂[(1 : ℝ), 0] + p 1 • !₂[(0 : ℝ), 1] := by
      ext j; fin_cases j <;> simp
    have hfp : f p = f.linear p + f 0 := by
      have h := f.map_vadd (0 : ℝ²) p
      rw [vadd_eq_add, vadd_eq_add, add_zero] at h
      exact h
    have hfp2 : f p = p 0 • f.linear !₂[(1 : ℝ), 0] + p 1 • f.linear !₂[(0 : ℝ), 1] + f 0 := by
      conv_lhs => rw [hfp, hp, map_add, map_smul, map_smul]
    rw [hfp2]
    simp only [linOf, map_add, map_mul, eval_C, eval_X, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hlin_deg (f : ℝ² →ᵃ[ℝ] ℝ²) (i : Fin 2) : (linOf f i).totalDegree ≤ 1 :=
    totalDegree_linear_form _ _ _
  have heval_aeval (f : ℝ² →ᵃ[ℝ] ℝ²) (Q : MvPolynomial (Fin 2) ℝ) (p : ℝ²) :
      eval (fun j => p j) (aeval (linOf f) Q) = eval (fun j => (f p) j) Q := by
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p₁ p₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
    | mul_X p₁ i ih =>
      simp only [map_mul, eval_X, aeval_X, ih, hlin_eval]
  have hlin_comp (f g : ℝ² →ᵃ[ℝ] ℝ²) (hfg : ∀ p : ℝ², f (g p) = p) :
      (aeval (linOf g)).comp (aeval (linOf f)) = AlgHom.id ℝ (MvPolynomial (Fin 2) ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, aeval_X]
    have hdeg1 : (aeval (linOf g) (linOf f i)).totalDegree ≤ 1 :=
      (totalDegree_aeval_linear (linOf g) (hlin_deg g) (linOf f i)).trans (hlin_deg f i)
    obtain ⟨a, b, c, habc⟩ := OMA.R_Erdos101_erdos_101_R1_H2_R1.affine_polynomial_form hdeg1
    have hev (p : ℝ²) : c + a * p 0 + b * p 1 = p i := by
      have h1 := heval_aeval g (linOf f i) p
      rw [hlin_eval f (g p) i, hfg p] at h1
      rw [habc] at h1
      simpa using h1
    have hc : c = 0 := by
      have h := hev !₂[0, 0]
      fin_cases i <;> simp at h ⊢ <;> linarith
    have ha : a = (if i = 0 then 1 else 0) := by
      have h := hev !₂[1, 0]
      fin_cases i <;> simp [hc] at h ⊢ <;> linarith
    have hb : b = (if i = 1 then 1 else 0) := by
      have h := hev !₂[0, 1]
      fin_cases i <;> simp [hc] at h ⊢ <;> linarith
    rw [habc, hc, ha, hb]
    fin_cases i <;> simp
  let φ : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
    AlgEquiv.ofAlgHom (aeval (linOf e.symm.toAffineMap)) (aeval (linOf e.toAffineMap))
      (hlin_comp e.toAffineMap e.symm.toAffineMap fun p => e.apply_symm_apply p)
      (hlin_comp e.symm.toAffineMap e.toAffineMap fun p => e.symm_apply_apply p)
  refine ⟨φ, ?_, ?_⟩
  · intro Q
    have h1 : (φ Q).totalDegree ≤ Q.totalDegree :=
      totalDegree_aeval_linear _ (hlin_deg e.symm.toAffineMap) Q
    have h2 : Q.totalDegree ≤ (φ Q).totalDegree := by
      have h := totalDegree_aeval_linear _ (hlin_deg e.toAffineMap) (φ Q)
      have hinv : aeval (linOf e.toAffineMap) (φ Q) = Q := φ.symm_apply_apply Q
      rwa [hinv] at h
    exact le_antisymm h1 h2
  · intro Q p
    exact heval_aeval e.symm.toAffineMap Q p

/- ### Divisibility from vanishing on an infinite graph arc -/

private lemma irreducible_isPrimitive_of_natDegree_pos {R : Type*} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] {f : Polynomial R} (hf : Irreducible f) (hdeg : 0 < f.natDegree) :
    f.IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one]
  have hdvd : Polynomial.C f.content ∣ f := Polynomial.C_content_dvd f
  obtain ⟨q, hq⟩ := hdvd
  rcases hf.isUnit_or_isUnit hq with hu | hqu
  · have huc : IsUnit f.content := Polynomial.isUnit_C.mp hu
    have hnorm : normalize f.content = 1 := normalize_eq_one.mpr huc
    simpa [Polynomial.normalize_content] using hnorm
  · exfalso
    have hq0 : q ≠ 0 := hqu.ne_zero
    have hc0 : Polynomial.C f.content ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hq; exact hf.ne_zero hq
    have hqdeg : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hqu
    have hfdeg : f.natDegree = 0 := by
      rw [hq, Polynomial.natDegree_mul hc0 hq0, Polynomial.natDegree_C, hqdeg]
    omega

private lemma dvd_of_vanish_on_infinite_graph {F P : MvPolynomial (Fin 2) ℝ}
    (hF : Irreducible F) (hP : P ≠ 0) {I : Set ℝ} (hI : I.Infinite) {α : ℝ → ℝ}
    (hF0 : ∀ x ∈ I, eval (fun i => (!₂[x, α x] : ℝ²) i) F = 0)
    (hP0 : ∀ x ∈ I, eval (fun i => (!₂[x, α x] : ℝ²) i) P = 0) :
    F ∣ P := by
  let swapE : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1)
  let oneE : MvPolynomial (Fin 1) ℝ ≃ₐ[ℝ] Polynomial ℝ :=
    (MvPolynomial.finSuccEquiv ℝ 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)))
  let Φ : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] Polynomial (Polynomial ℝ) :=
    swapE.trans ((MvPolynomial.finSuccEquiv ℝ 1).trans (Polynomial.mapAlgEquiv oneE))
  have hΦ_C (r : ℝ) : Φ (C r) = Polynomial.C (Polynomial.C r) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    simp [Polynomial.algebraMap_apply]
  have hΦ_X0 : Φ (X (0 : Fin 2)) = Polynomial.C Polynomial.X := by
    have h1 : swapE (X (0 : Fin 2)) = X (1 : Fin 2) := by
      simp [swapE]
    have h2 : MvPolynomial.finSuccEquiv ℝ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
      MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 1))
    have h3 : oneE (X (0 : Fin 1)) = Polynomial.X := by
      change (MvPolynomial.finSuccEquiv ℝ 0 (X (0 : Fin 1))).map
        (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingHom = Polynomial.X
      rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
    change (MvPolynomial.finSuccEquiv ℝ 1 (swapE (X (0 : Fin 2)))).map oneE.toRingHom = _
    rw [h1, h2, Polynomial.map_C]
    exact congrArg Polynomial.C h3
  have hΦ_X1 : Φ (X (1 : Fin 2)) = Polynomial.X := by
    have h1 : swapE (X (1 : Fin 2)) = X (0 : Fin 2) := by
      simp [swapE]
    have h2 : MvPolynomial.finSuccEquiv ℝ 1 (X (0 : Fin 2)) = Polynomial.X :=
      MvPolynomial.finSuccEquiv_X_zero
    change (MvPolynomial.finSuccEquiv ℝ 1 (swapE (X (1 : Fin 2)))).map oneE.toRingHom = _
    rw [h1, h2, Polynomial.map_X]
  have hΦ_eval (Q : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
      ((Φ Q).map (Polynomial.evalRingHom x)).eval y = eval (fun i => (!₂[x, y] : ℝ²) i) Q := by
    induction Q using MvPolynomial.induction_on with
    | C r =>
      rw [hΦ_C, Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, eval_C]
    | add p q ihp ihq =>
      simp [map_add, Polynomial.map_add, Polynomial.eval_add, ihp, ihq]
    | mul_X p i ih =>
      fin_cases i
      · change ((Φ (p * X (0 : Fin 2))).map (Polynomial.evalRingHom x)).eval y =
          eval (fun i => (!₂[x, y] : ℝ²) i) (p * X (0 : Fin 2))
        rw [map_mul, hΦ_X0, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
          Polynomial.eval_C, ih, map_mul, eval_X]
        simp
      · change ((Φ (p * X (1 : Fin 2))).map (Polynomial.evalRingHom x)).eval y =
          eval (fun i => (!₂[x, y] : ℝ²) i) (p * X (1 : Fin 2))
        rw [map_mul, hΦ_X1, Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_mul,
          Polynomial.eval_X, ih, map_mul, eval_X]
        simp
  let f : Polynomial (Polynomial ℝ) := Φ F
  let p : Polynomial (Polynomial ℝ) := Φ P
  have hf_irr : Irreducible f := algEquiv_irreducible Φ hF
  have hp_ne : p ≠ 0 := by intro h; exact hP (Φ.injective (by simpa [p] using h))
  have hno_const (q : Polynomial (Polynomial ℝ)) (hq0 : q ≠ 0) (hqdeg : q.natDegree = 0)
      (hvan : ∀ x ∈ I, (q.map (Polynomial.evalRingHom x)).eval (α x) = 0) : False := by
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
    have hc0 : q.coeff 0 ≠ 0 := by
      intro h; rw [h, map_zero] at hqC; exact hq0 hqC
    have hroots : I ⊆ ((q.coeff 0).roots.toFinset : Set ℝ) := by
      intro x hx
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hc0]
      have hx0 := hvan x hx
      rw [hqC, Polynomial.map_C, Polynomial.eval_C] at hx0
      exact hx0
    exact hI ((q.coeff 0).roots.toFinset.finite_toSet.subset hroots)
  have hf_deg : 0 < f.natDegree := by
    by_contra h0
    exact hno_const f hf_irr.ne_zero (Nat.eq_zero_of_not_pos h0) fun x hx => by
      rw [hΦ_eval]; exact hF0 x hx
  have hf_prim : f.IsPrimitive := irreducible_isPrimitive_of_natDegree_pos hf_irr hf_deg
  let K := FractionRing (Polynomial ℝ)
  let ι := algebraMap (Polynomial ℝ) K
  have hfK_irr : Irreducible (f.map ι) :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map (K := K) hf_prim).mp hf_irr
  by_cases hdvdK : f.map ι ∣ p.map ι
  · have hdvd : f ∣ p :=
      (Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map K hf_prim).mpr hdvdK
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨Φ.symm q, ?_⟩
    apply Φ.injective
    simpa [f, p] using hq
  · exfalso
    have hcop : IsCoprime (f.map ι) (p.map ι) :=
      (hfK_irr.coprime_iff_not_dvd).mpr hdvdK
    obtain ⟨uK, vK, huvK⟩ := hcop
    obtain ⟨c, hc0, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℝ)) uK
    obtain ⟨d, hd0, hd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℝ)) vK
    rw [mem_nonZeroDivisors_iff_ne_zero] at hc0 hd0
    let u := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial ℝ)) uK
    let v := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial ℝ)) vK
    have hbez : Polynomial.C d * u * f + Polynomial.C c * v * p = Polynomial.C (c * d) := by
      apply Polynomial.map_injective ι (IsFractionRing.injective (Polynomial ℝ) K)
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, map_mul]
      change Polynomial.C (ι d) * (u.map ι) * (f.map ι) +
        Polynomial.C (ι c) * (v.map ι) * (p.map ι) = Polynomial.C (ι c * ι d)
      have hc' : u.map ι = Polynomial.C (ι c) * uK := by
        rw [show u.map ι = c • uK from hc]
        ext m
        simp [Polynomial.coeff_C_mul, Algebra.smul_def, ι]
      have hd' : v.map ι = Polynomial.C (ι d) * vK := by
        rw [show v.map ι = d • vK from hd]
        ext m
        simp [Polynomial.coeff_C_mul, Algebra.smul_def, ι]
      rw [hc', hd']
      have hfac : Polynomial.C (ι d) * (Polynomial.C (ι c) * uK) * f.map ι +
          Polynomial.C (ι c) * (Polynomial.C (ι d) * vK) * p.map ι =
          Polynomial.C (ι c * ι d) * (uK * f.map ι + vK * p.map ι) := by
        rw [map_mul]; ring
      rw [hfac, huvK, mul_one]
    have hcd0 : c * d ≠ 0 := mul_ne_zero hc0 hd0
    have hroots : I ⊆ ((c * d).roots.toFinset : Set ℝ) := by
      intro x hx
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hcd0]
      have h1 := congrArg (fun q : Polynomial (Polynomial ℝ) =>
        (q.map (Polynomial.evalRingHom x)).eval (α x)) hbez
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.coe_evalRingHom] at h1
      have hfx : (f.map (Polynomial.evalRingHom x)).eval (α x) = 0 := by
        rw [hΦ_eval]; exact hF0 x hx
      have hpx : (p.map (Polynomial.evalRingHom x)).eval (α x) = 0 := by
        rw [hΦ_eval]; exact hP0 x hx
      rw [hfx, hpx, mul_zero, mul_zero, add_zero] at h1
      rw [Polynomial.IsRoot, Polynomial.eval_mul]
      exact h1.symm
    exact hI ((c * d).roots.toFinset.finite_toSet.subset hroots)

end Helpers

/- ### Main reduction theorem -/

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1_H2_R1.H2 := by
  intro hsurf hcubic d ε hε
  obtain ⟨N₁, hN₁⟩ := hsurf d (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
  refine ⟨max N₁ (max 1 N₂), ?_⟩
  intro n hn S hSn _ F G H hF hG hH hFG h₂F h₂G h₂H hdF hdG hdH A hA
  by_contra hgt
  have hdense : ε * (n : ℝ) ^ 2 < (A.card : ℝ) := lt_of_not_ge hgt
  choose! x hxS y hyS z hzS hxy hzx hzy hFx hGy hHz hLxy hzL using hA
  let Avert := A.filter fun L => (x L) 0 = (y L) 0 ∨ (x L) 0 = (z L) 0 ∨ (y L) 0 = (z L) 0
  have hAvert : Avert.card ≤ S.card := by
    apply card_vertical_lines_le
    intro L hL
    obtain ⟨hLA, hor⟩ := Finset.mem_filter.mp hL
    have hLeq : line[ℝ, x L, y L] = L := hLxy L hLA
    have hxL : x L ∈ line[ℝ, x L, y L] := left_mem_affineSpan_pair ℝ (x L) (y L)
    have hyL : y L ∈ line[ℝ, x L, y L] := right_mem_affineSpan_pair ℝ (x L) (y L)
    have hzL' : z L ∈ line[ℝ, x L, y L] := hLeq.symm ▸ hzL L hLA
    rcases hor with h0 | h0 | h0
    · exact ⟨x L, hxS L hLA, y L, hyS L hLA, hxy L hLA, hLeq, h0⟩
    · refine ⟨x L, hxS L hLA, z L, hzS L hLA, (hzx L hLA).symm, ?_, h0⟩
      exact (line_eq_of_mem_pair (hxy L hLA) (hzx L hLA).symm hxL hzL').symm.trans hLeq
    · refine ⟨y L, hyS L hLA, z L, hzS L hLA, (hzy L hLA).symm, ?_, h0⟩
      exact (line_eq_of_mem_pair (hxy L hLA) (hzy L hLA).symm hyL hzL').symm.trans hLeq
  let A' := A \ Avert
  have hA'_card : (ε / 2) * (n : ℝ) ^ 2 ≤ (A'.card : ℝ) := by
    have hsplit : A.card ≤ A'.card + Avert.card := by
      have hsub : A ⊆ A' ∪ Avert := fun L hL => by
        by_cases hv : L ∈ Avert
        · exact Finset.mem_union_right _ hv
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hL, hv⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hsplitR : (A.card : ℝ) ≤ (A'.card : ℝ) + (Avert.card : ℝ) := by exact_mod_cast hsplit
    have hAvR : (Avert.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAvert.trans hSn
    have hnN₂ : (N₂ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_max_right 1 N₂).trans ((le_max_right N₁ _).trans hn)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_max_left 1 N₂).trans ((le_max_right N₁ _).trans hn)
    have h2 : (2 : ℝ) < ε * (n : ℝ) := by
      have hlt : 2 / ε < (n : ℝ) := hN₂.trans_le hnN₂
      exact (div_lt_iff₀ hε).mp hlt |>.trans_eq (mul_comm _ _)
    have hn_le : (n : ℝ) ≤ (ε / 2) * (n : ℝ) ^ 2 := by
      have hpos : (0 : ℝ) < (n : ℝ) := by linarith
      nlinarith
    linarith
  let T : Finset (S × S × S) := A'.attach.image fun (L : {L // L ∈ A'}) =>
    let hLA : L.1 ∈ A := (Finset.mem_sdiff.mp L.2).1
    (⟨x L.1, hxS L.1 hLA⟩, ⟨y L.1, hyS L.1 hLA⟩, ⟨z L.1, hzS L.1 hLA⟩)
  have hTcard : T.card = A'.card := by
    rw [Finset.card_image_of_injective, Finset.card_attach]
    intro L₁ L₂ heq
    have h1 := (Finset.mem_sdiff.mp L₁.2).1
    have h2 := (Finset.mem_sdiff.mp L₂.2).1
    have hxEq : x L₁.1 = x L₂.1 := congrArg (fun p : S × S × S => (p.1 : ℝ²)) heq
    have hyEq : y L₁.1 = y L₂.1 := congrArg (fun p : S × S × S => (p.2.1 : ℝ²)) heq
    apply Subtype.ext
    rw [← hLxy L₁.1 h1, ← hLxy L₂.1 h2, hxEq, hyEq]
  have hTinj : (T : Set (S × S × S)).InjOn (fun t => line[ℝ, (t.1 : ℝ²), (t.2.1 : ℝ²)]) := by
    intro t₁ ht₁ t₂ ht₂ hline
    obtain ⟨L₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht₁)
    obtain ⟨L₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht₂)
    have h1 := (Finset.mem_sdiff.mp L₁.2).1
    have h2 := (Finset.mem_sdiff.mp L₂.2).1
    dsimp only at hline
    rw [hLxy L₁.1 h1, hLxy L₂.1 h2] at hline
    have hL : L₁ = L₂ := Subtype.ext hline
    subst hL
    rfl
  have hTprop : ∀ t ∈ T, eval (fun i => (t.1 : ℝ²) i) F = 0 ∧
      eval (fun i => (t.2.1 : ℝ²) i) G = 0 ∧
      eval (fun i => (t.2.2 : ℝ²) i) H = 0 ∧
      (t.1 : ℝ²) 0 ≠ (t.2.1 : ℝ²) 0 ∧ (t.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
      (t.2.1 : ℝ²) 0 ≠ (t.2.2 : ℝ²) 0 ∧
      Collinear ℝ ({(t.1 : ℝ²), (t.2.1 : ℝ²), (t.2.2 : ℝ²)} : Set ℝ²) := by
    intro t ht
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hLA, hLnv⟩ := Finset.mem_sdiff.mp L.2
    have hnv : ¬ ((x L.1) 0 = (y L.1) 0 ∨ (x L.1) 0 = (z L.1) 0 ∨ (y L.1) 0 = (z L.1) 0) :=
      fun h => hLnv (Finset.mem_filter.mpr ⟨hLA, h⟩)
    refine ⟨hFx L.1 hLA, hGy L.1 hLA, hHz L.1 hLA,
      fun h => hnv (Or.inl h), fun h => hnv (Or.inr (Or.inl h)),
      fun h => hnv (Or.inr (Or.inr h)), ?_⟩
    rw [collinear_iff_of_mem (Set.mem_insert (x L.1) _)]
    have hline : z L.1 ∈ line[ℝ, x L.1, y L.1] := (hLxy L.1 hLA).symm ▸ hzL L.1 hLA
    obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
    refine ⟨y L.1 -ᵥ x L.1, ?_⟩
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · dsimp only
      exact ⟨s, by rw [← hs, AffineMap.lineMap_apply]⟩
  obtain ⟨e, r, α, β, γ, f₁, f₂, f₃, hr, hcα, hcβ, hcγ, hcf₁, hcf₂, hcf₃,
    hi₁, hi₂, hi₃, hord, harcs, hstd, hadd⟩ :=
    hN₁ n ((le_max_left N₁ _).trans hn) S hSn F G H hF hG hH h₂F h₂G h₂H hdF hdG hdH T
      (by rwa [hTcard]) hTinj hTprop
  obtain ⟨r', P, hr', hr'le, hPne, hPdeg, hPvan⟩ :=
    hcubic r α β γ f₁ f₂ f₃ hr hcα hcβ hcγ hcf₁ hcf₂ hcf₃ hi₁ hi₂ hi₃ hord hstd hadd
  obtain ⟨φ, hφdeg, hφeval⟩ := exists_affine_pullback e
  have hIinf : (Set.Ioo (-r') r').Infinite := Set.Ioo_infinite (by linarith)
  have hIsub : Set.Ioo (-r') r' ⊆ Set.Ioo (-r) r := Set.Ioo_subset_Ioo (by linarith) hr'le
  have hF_irr : Irreducible (φ F) := algEquiv_irreducible φ hF
  have hG_irr : Irreducible (φ G) := algEquiv_irreducible φ hG
  have hFG_not : ¬ Associated (φ F) (φ G) := fun h => hFG (algEquiv_associated φ h)
  have hF_dvd : φ F ∣ P := dvd_of_vanish_on_infinite_graph hF_irr hPne hIinf
    (fun t ht => by rw [hφeval]; exact (harcs t (hIsub ht)).1)
    (fun t ht => (hPvan t ht).1)
  have hG_dvd : φ G ∣ P := dvd_of_vanish_on_infinite_graph hG_irr hPne hIinf
    (fun t ht => by rw [hφeval]; exact (harcs t (hIsub ht)).2.1)
    (fun t ht => (hPvan t ht).2.1)
  obtain ⟨Q, hQ⟩ := hF_dvd
  have hG_dvd_Q : φ G ∣ Q := by
    rw [hQ] at hG_dvd
    have hnot : ¬ φ G ∣ φ F := fun h => hFG_not (hG_irr.associated_of_dvd hF_irr h).symm
    exact ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hG_irr).dvd_mul.mp hG_dvd).resolve_left hnot
  obtain ⟨R, hR⟩ := hG_dvd_Q
  have hprod : φ F * φ G ∣ P := ⟨R, by rw [hQ, hR, mul_assoc]⟩
  have hdeg_le := totalDegree_le_of_dvd_of_isDomain hprod hPne
  rw [totalDegree_mul_of_isDomain hF_irr.ne_zero hG_irr.ne_zero, hφdeg F, hφdeg G] at hdeg_le
  omega

end OMA.R_Erdos101_erdos_101_R1_H2_R1_H2_R1
