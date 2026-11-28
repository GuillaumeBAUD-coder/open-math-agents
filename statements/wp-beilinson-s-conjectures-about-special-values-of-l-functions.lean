import Mathlib

/-!
# Beilinson's conjectures about special values of L-functions

Source: https://en.wikipedia.org/wiki/Special_values_of_L-functions
Credit: @yuka30240

The source describes the regulator up to a rational factor and refers to J. Nekovář,
*Beilinson's conjectures*, §§2, 5, 6. We use the rational-coefficient formulation for
Chow projectors, including the near-central cycle class summand and the central height
pairing. The two determinant structures in §2.2 give the values on the two sides of
the functional equation. Meromorphic continuation and the usual local and functional
equation hypotheses have their customary conditional meaning.

The cubical complex realizes rational motivic cohomology. Integral elements come from
regular alterations as in A. J. Scholl, *Integral elements in K-theory and products
of modular curves*. The real regulator is the cubical current of J. I. Burgos Gil,
E. Feliu and Y. Takeda, *On Goncharov's regulator and higher arithmetic Chow groups*,
§§5–6. At the center we use the arithmetic intersection construction of the height
under its admissible-lifting hypotheses, as in K. Künnemann, *Height pairings for
algebraic cycles on abelian varieties*, §1.
-/

namespace OMA.S_wp_beilinson_s_conjectures_about_special_values_of_l_functions

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter MeasureTheory
open scoped BigOperators Topology ContDiff

/-! ## Euler factors and rational period lines -/

abbrev ArithmeticScheme := Over (Spec (CommRingCat.of ℤ))

/-- The Euler factor uses geometric Frobenius in cohomological degree i. -/
def eulerFactor (roots : Multiset ℂ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ((roots.map (fun α => 1 - α * (p.val : ℂ) ^ (-s))).prod)⁻¹

/-- Rational equivalence between two nonzero periods. -/
def SameRationalLine (a b : ℂ) : Prop :=
  b ≠ 0 ∧ ∃ q : ℚˣ, a = (q.val : ℂ) * b

/-! ## Bloch’s cubical cycles -/

abbrev CubeRing (m : ℕ) := MvPolynomial (Fin m) ℤ

def cube (X : Scheme.{0}) (m : ℕ) : Scheme.{0} :=
  X ⨯ Spec (CommRingCat.of (CubeRing m))

/-- A coordinate substitution induces a morphism of cubes over X. -/
def cubeMap (X : Scheme.{0}) {m k : ℕ} (c : Fin m → CubeRing k) :
    cube X k ⟶ cube X m :=
  prod.map (𝟙 X) (Spec.map (CommRingCat.ofHom (MvPolynomial.bind₁ c).toRingHom))

/-- Each free coordinate occurs once in a face. The others take endpoint values. -/
structure Face (k m : ℕ) where
  coordinates : Fin m → Fin k ⊕ Bool
  free : ∀ j : Fin k, ∃! i, coordinates i = .inl j

def Face.map {k m : ℕ} (f : Face k m) (X : Scheme.{0}) : cube X k ⟶ cube X m :=
  cubeMap X (fun i => (f.coordinates i).elim MvPolynomial.X (fun b => if b then 1 else 0))

def primeCycleIdeal (X : Scheme) (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (.closure ({x} : Set X))

/-- The generic point x has codimension r and meets every face properly. -/
def Admissible (X : Scheme.{0}) (r m : ℕ) (x : cube X m) : Prop :=
  Order.coheight x = r ∧
  ∀ k (face : Face k m), ∀ y : cube X k,
    face.map X y ∈ closure ({x} : Set (cube X m)) → r ≤ Order.coheight y

/-- Multiplicity at y of the scheme-theoretic inverse image of the reduced closure of x.
Used for a flat projection and for a single properly intersecting face. -/
def inverseImageCoeff {X Y : Scheme.{0}} (f : Y ⟶ X) (x : X) (y : Y) : ℚ := by
  classical
  let i := (primeCycleIdeal X x).subschemeι
  let W := pullback f i
  let j : W ⟶ Y := pullback.fst f i
  exact ∑ᶠ z : W, if j z = y ∧ Order.coheight z = 0 then
    ((Module.length (W.presheaf.stalk z) (W.presheaf.stalk z)).toNat : ℚ) else 0

abbrev CycleCoeffs (X : Scheme.{0}) := X → ℚ

def pullCycle {X Y : Scheme.{0}} (f : Y ⟶ X) (c : CycleCoeffs X) : CycleCoeffs Y :=
  fun y => ∑ᶠ x : X, c x * inverseImageCoeff f x y

def chains (X : Scheme.{0}) (r m : ℕ) : Submodule ℚ (CycleCoeffs (cube X m)) := by
  classical
  exact Submodule.span ℚ {c | ∃ x, Admissible X r m x ∧ c = Pi.single x 1}

def dropCoordinate (X : Scheme.{0}) {m : ℕ} (j : Fin (m + 1)) :
    cube X (m + 1) ⟶ cube X m :=
  cubeMap X (fun a => MvPolynomial.X (j.succAbove a))

def endpoint (X : Scheme.{0}) {m : ℕ} (j : Fin (m + 1)) (b : Bool) :
    cube X m ⟶ cube X (m + 1) :=
  cubeMap X (j.insertNth (if b then 1 else 0) MvPolynomial.X)

def degenerate (X : Scheme.{0}) (r : ℕ) : (m : ℕ) → Submodule ℚ (CycleCoeffs (cube X m))
  | 0 => ⊥
  | m + 1 => Submodule.span ℚ {c | ∃ (j : Fin (m + 1)), ∃ a ∈ chains X r m,
      c = pullCycle (dropCoordinate X j) a}

def boundary (X : Scheme.{0}) (m : ℕ) (c : CycleCoeffs (cube X (m+1))) :
    CycleCoeffs (cube X m) :=
  ∑ j : Fin (m+1), (-1 : ℚ)^j.val •
    (pullCycle (endpoint X j true) c - pullCycle (endpoint X j false) c)

def cycles (X : Scheme.{0}) (r : ℕ) : (m : ℕ) → Submodule ℚ (CycleCoeffs (cube X m))
  | 0 => chains X r 0
  | m+1 => Submodule.span ℚ {c | c ∈ chains X r (m+1) ∧ boundary X m c ∈ degenerate X r m}

def relations (X : Scheme.{0}) (r m : ℕ) : Submodule ℚ (CycleCoeffs (cube X m)) :=
  degenerate X r m ⊔ Submodule.span ℚ {c | ∃ a ∈ chains X r (m+1), c = boundary X m a}

/-! ## Betti and de Rham realizations in complex cohomology -/

abbrev CPoint (X : Scheme.{0}) := Spec (CommRingCat.of ℂ) ⟶ X
abbrev Coord (n : ℕ) := Fin n → ℂ
abbrev RealCoord (n : ℕ) := Fin n → ℝ

def supportPoint {X : Scheme.{0}} (p : CPoint X) : X :=
  (Scheme.SpecToEquivOfField ℂ X p).1

/-- Evaluate a regular function through the residue field at a complex point. -/
def evalRegular {X : Scheme.{0}} (U : X.Opens) (g : Γ(X, U)) (p : CPoint X) : ℂ := by
  classical
  let v := Scheme.SpecToEquivOfField ℂ X p
  exact if h : v.1 ∈ U then
    v.2 ((X.residue v.1) ((X.presheaf.germ U v.1 h) g)) else 0

/-- Testing regular coordinate functions on affine opens characterizes smooth (k = ℝ)
and holomorphic (k = ℂ) maps into the complex points of a variety. -/
def plotLocus (K : Type) [NontriviallyNormedField K] [NormedAlgebra K ℂ]
    {X : Scheme.{0}} {n : ℕ} (p : Coord n → CPoint X) : Set (Coord n) :=
  interior {z | ∀ (U : X.Opens), supportPoint (p z) ∈ U →
    (∀ᶠ y in 𝓝 z, supportPoint (p y) ∈ U) ∧
    ∀ g : Γ(X, U), ContDiffAt K ∞ (fun y => evalRegular U g (p y)) z}

abbrev Alt (n k : ℕ) := ContinuousAlternatingMap ℝ (Coord n) ℂ (Fin k)
abbrev FormData (X : Scheme.{0}) (k : ℕ) :=
  (n : ℕ) → (Coord n → CPoint X) → Coord n → Alt n k

/-- Diffeological differential forms, specified by their pullbacks to smooth plots. -/
def IsSmoothForm {X : Scheme.{0}} {k : ℕ} (form : FormData X k) : Prop :=
  (∀ n p z, z ∉ plotLocus ℝ p → form n p z = 0) ∧
  (∀ n p, ContDiffOn ℝ ∞ (form n p) (plotLocus ℝ p)) ∧
  ∀ n m (p : Coord n → CPoint X) (f : Coord m → Coord n) (z : Coord m),
    f z ∈ plotLocus ℝ p → z ∈ interior {w | ContDiffAt ℝ ∞ f w} →
      form m (p ∘ f) z = (form n p (f z)).compContinuousLinearMap (fderiv ℝ f z)

def IsClosedForm {X : Scheme.{0}} {k : ℕ} (form : FormData X k) : Prop :=
  IsSmoothForm form ∧ ∀ n p, ∀ z ∈ plotLocus ℝ p, extDeriv (𝕜 := ℝ) (form n p) z = 0

/-- Evaluate the complexified form on holomorphic tangent vectors in slots J and
antiholomorphic tangent vectors elsewhere. Common powers of two cancel in the zero test. -/
def typeComponent {k n : ℕ} (form : Alt n k) (J : Finset (Fin k)) (v : Fin k → Coord n) : ℂ :=
  ∑ S : Finset (Fin k),
    (∏ j ∈ S, if j ∈ J then -Complex.I else Complex.I) *
      form (fun j => if j ∈ S then Complex.I • v j else v j)

def InHodgeFiltration {X : Scheme.{0}} {k : ℕ} (p : ℕ) (form : FormData X k) : Prop :=
  ∀ n (u : Coord n → CPoint X), ∀ z ∈ plotLocus ℂ u, ∀ J : Finset (Fin k),
    J.card < p → ∀ v, typeComponent (form n u z) J v = 0

def realSlice {n : ℕ} (z : Coord n) : RealCoord n := fun j => (z j).re
def complexSlice {n : ℕ} (t : RealCoord n) : Coord n := fun j => t j

abbrev Cell (k : ℕ) := Fin k → unitInterval
abbrev SingularCube (X : Scheme.{0}) (k : ℕ) := Cell k → CPoint X
abbrev Cochains (X : Scheme.{0}) (k : ℕ) := SingularCube X k → ℂ

/-- The parametrization of a smooth cube extends across the boundary of the cell. -/
def IsSmoothCube {X : Scheme.{0}} {k : ℕ} (σ : SingularCube X k) : Prop :=
  ∃ u : RealCoord k → CPoint X,
    (∀ t, u (fun j => (t j).val) = σ t) ∧
    ∀ t ∈ Set.Icc (0 : RealCoord k) 1, complexSlice t ∈ plotLocus ℝ (u ∘ realSlice)

def integrateCube {X : Scheme.{0}} {k : ℕ} (form : FormData X k) :
    Cochains X k := fun σ => by
  classical
  exact if h : IsSmoothCube σ then
    ∫ t in Set.Icc (0 : RealCoord k) 1, form k (h.choose ∘ realSlice) (complexSlice t)
      (fun j => Pi.single j (1 : ℂ))
  else 0

def cubeFace {X : Scheme.{0}} {k : ℕ} (σ : SingularCube X (k+1)) (j : Fin (k+1))
    (b : unitInterval) : SingularCube X k := fun t => σ (j.insertNth b t)

def coboundary {X : Scheme.{0}} {k : ℕ} (a : Cochains X k) : Cochains X (k+1) :=
  fun σ => ∑ j : Fin (k+1), (-1 : ℂ) ^ j.val * (a (cubeFace σ j 1) - a (cubeFace σ j 0))

def DegenerateCube (X : Scheme.{0}) : (k : ℕ) → SingularCube X k → Prop
  | 0, _ => False
  | k+1, σ => ∃ (j : Fin (k+1)) (τ : SingularCube X k),
      σ = fun t => τ (fun l => t (j.succAbove l))

def IsNormalized {X : Scheme.{0}} {k : ℕ} (a : Cochains X k) : Prop :=
  ∀ σ, IsSmoothCube σ → DegenerateCube X k σ → a σ = 0

def IsCocycle {X : Scheme.{0}} {k : ℕ} (a : Cochains X k) : Prop :=
  IsNormalized a ∧ ∀ σ, IsSmoothCube σ → coboundary a σ = 0

/-- Values on nonsmooth cubes play no role in smooth singular cohomology. -/
def exactCochains (X : Scheme.{0}) : (k : ℕ) → Submodule ℂ (Cochains X k)
  | 0 => Submodule.span ℂ {a | ∀ σ, IsSmoothCube σ → a σ = 0}
  | k+1 => Submodule.span ℂ {a | ∃ b : Cochains X k, IsNormalized b ∧
      ∀ σ, IsSmoothCube σ → a σ = coboundary b σ}

abbrev CochainClasses (X : Scheme.{0}) (k : ℕ) := Cochains X k ⧸ exactCochains X k

def Betti (X : Scheme.{0}) (k : ℕ) : Submodule ℚ (CochainClasses X k) :=
  Submodule.span ℚ {x | ∃ a : Cochains X k, IsCocycle a ∧
    (∀ σ, IsSmoothCube σ → ∃ q : ℚ, a σ = q) ∧ x = (exactCochains X k).mkQ a}

def hodge (X : Scheme.{0}) (k p : ℕ) : Submodule ℂ (CochainClasses X k) :=
  Submodule.span ℂ {x | ∃ form : FormData X k, IsClosedForm form ∧
    InHodgeFiltration p form ∧ x = (exactCochains X k).mkQ (integrateCube form)}

def pullCochain {Y X : Scheme.{0}} (f : Y ⟶ X) {k : ℕ} (a : Cochains X k) : Cochains Y k :=
  fun σ => a (fun t => σ t ≫ f)

def InjectiveOnCohomology {X Y : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) : Prop :=
  ∀ a : Cochains X k, IsCocycle a → pullCochain f a ∈ exactCochains Y k → a ∈ exactCochains X k

/-- A global algebraic k-form on an affine variety is a finite sum of products
g₀ dg₁ ∧ ... ∧ dgₖ of regular functions. -/
def IsAlgebraicForm {Y : Scheme.{0}} {k : ℕ} (form : FormData Y k) : Prop :=
  ∃ (m : ℕ) (g : Fin m → Fin (k+1) → Γ(Y, ⊤)), ∀ n (p : Coord n → CPoint Y),
    ∀ z ∈ plotLocus ℝ p, ∀ v : Fin k → Coord n,
      form n p z v = ∑ j, evalRegular ⊤ (g j 0) (p z) *
        (Matrix.of fun a b : Fin k =>
          fderiv ℝ (evalRegular ⊤ (g j a.succ) ∘ p) z (v b)).det

/-- The rational de Rham structure in complex Betti cohomology. On a smooth affine
variety global algebraic forms compute algebraic de Rham cohomology. Each smooth
quasi-projective X has a smooth affine Jouanolou torsor Y → X inducing an isomorphism
on cohomology. Any cohomologically injective pullback detects rationality. -/
def deRham (X : Over (Spec (CommRingCat.of ℚ))) (k : ℕ) :
    Submodule ℚ (CochainClasses X.left k) :=
  Submodule.span ℚ {x | ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (f : Y ⟶ X),
    IsAffine Y.left ∧ Smooth Y.hom ∧ LocallyOfFiniteType Y.hom ∧
    InjectiveOnCohomology f.left k ∧ ∃ (a : Cochains X.left k) (form : FormData Y.left k),
    IsCocycle a ∧ IsClosedForm form ∧ IsAlgebraicForm form ∧
    pullCochain f.left a - integrateCube form ∈ exactCochains Y.left k ∧
    x = (exactCochains X.left k).mkQ a}

/-! ## Integration currents and the real regulator -/

def analyticallyOpen {X : Scheme.{0}} (s : Set (CPoint X)) : Prop :=
  ∀ n (p : Coord n → CPoint X), ∀ z ∈ plotLocus ℝ p,
    p z ∈ s → ∀ᶠ w in 𝓝 z, p w ∈ s

/-- Holomorphic coordinate charts on the complex regular locus. -/
structure HolChart (X : Scheme.{0}) (d : ℕ) where
  source : TopologicalSpace.Opens (Coord d)
  point : Coord d → CPoint X
  inverse : CPoint X → Coord d
  leftInverse : ∀ z ∈ source, inverse (point z) = z
  openImage : analyticallyOpen (point '' source)
  holomorphic : ∀ z ∈ source, z ∈ plotLocus ℂ point
  inverseHolomorphic : ∀ n (p : Coord n → CPoint X), ∀ z ∈ plotLocus ℂ p,
    p z ∈ point '' source → DifferentiableAt ℂ (inverse ∘ p) z

def IsAtlas {X : Scheme.{0}} {d : ℕ} (A : ℕ → HolChart X d) : Prop :=
  ∀ (c : HolChart X d), ∀ z ∈ c.source,
    ∃ j, c.point z ∈ (A j).point '' (A j).source

/-- In complex coordinates we use the real orientation (x₁,y₁,...,x_d,y_d). -/
def frameVector (d j : ℕ) : Coord d :=
  fun l => if l.val = j / 2 then (if Even j then 1 else Complex.I) else 0

/-- Integrate on the regular locus in complex orientation. Removing lower-dimensional
complex subvarieties leaves the integral of a locally integrable top form unchanged. -/
def chartIntegral (X : Scheme.{0}) (d : ℕ) (density : HolChart X d → Coord d → ℂ) : ℂ := by
  classical
  exact if h : ∃ A : ℕ → HolChart X d, IsAtlas A then
    let A := h.choose
    ∑' j : ℕ, ∫ z in ((A j).source : Set (Coord d)) \
      {z | ∃ l < j, (A j).point z ∈ (A l).point '' (A l).source}, density (A j) z
  else 0

/-- Evaluate a wedge product on the coordinate frame by alternation. -/
def wedgeOnFrame (d a b : ℕ)
    (α : (Fin a → Coord d) → ℂ) (β : (Fin b → Coord d) → ℂ) : ℂ :=
  (∑ σ : Equiv.Perm (Fin (a+b)), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    α (fun i => frameVector d (σ (Fin.castAdd b i)).val) *
    β (fun i => frameVector d (σ (Fin.natAdd a i)).val)) /
    ((a.factorial : ℂ) * b.factorial)

def tatePeriod : ℂ := 2 * Real.pi * Complex.I

def cubeCoordinate {X : Scheme.{0}} {m : ℕ} (i : Fin m) (p : CPoint (cube X m)) : ℂ :=
  let A := CommRingCat.of (CubeRing m)
  let t := evalRegular ⊤ ((Scheme.ΓSpecIso A).inv (MvPolynomial.X i)) (p ≫ prod.snd)
  t / (t - 1)

/-- The alternating Wang form T_m of Burgos Gil, Feliu and Takeda, equations
(5.9)--(5.10), written using logarithmic derivatives and their conjugates. -/
def goncharovForm {d l : ℕ} (f : Fin (l+1) → Coord d → ℂ) (z : Coord d)
    (v : Fin l → Coord d) : ℂ :=
  (∑ j : Fin (l+1), (-1 : ℂ)^j.val.succ *
    ∑ σ : Equiv.Perm (Fin (l+1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      Real.log ‖f (σ 0) z‖ * (Matrix.of fun a b : Fin l =>
        let h := fderiv ℝ (f (σ a.succ)) z (v b) / f (σ a.succ) z
        if a.val < j.val then h else star h).det) / ((l+1).factorial : ℂ)

/-- Pair the unnormalized integration current of a prime cycle with a test form. -/
def cycleIntegral {X Y : Scheme.{0}} (f : Y ⟶ X) (d : ℕ) {k : ℕ}
    (test : FormData X k) : ℂ :=
  chartIntegral Y d (fun c z => test d (fun u => c.point u ≫ f) z
    (fun i => frameVector d i.val))

/-- The current of a codimension-r higher cycle in cubical degree l+1.
The power of 2πi converts the twisted-current convention to ordinary integration. -/
def primeRegulator {X : Scheme.{0}} (d r l : ℕ) (x : cube X (l+1)) {k : ℕ}
    (test : FormData X k) : ℂ :=
  let inc := (primeCycleIdeal _ x).subschemeι
  let e := d + (l+1) - r
  tatePeriod ^ ((r : ℤ) - (l+1 : ℕ)) * chartIntegral _ e (fun c z =>
    wedgeOnFrame e k l
      (fun v => test e (fun w => c.point w ≫ inc ≫ prod.fst) z v)
      (goncharovForm (fun i w => cubeCoordinate i (c.point w ≫ inc)) z))

def realForm {X : Scheme.{0}} {k : ℕ} (test : FormData X k) : Prop :=
  ∀ n p, ∀ z ∈ plotLocus ℝ p, ∀ v, (test n p z v).im = 0

/-- Compare two degree-i currents in the real Deligne quotient by testing against closed
complementary forms annihilating F^r and the real Tate twist. Here i+1 < 2r. -/
def sameDeligneClass (X : Scheme.{0}) (d i r : ℕ)
    (u v : FormData X (2*d-i) → ℂ) : Prop :=
  ∀ test, IsClosedForm test → realForm test → InHodgeFiltration (d+1-r) test →
    (Complex.I ^ (-(r : ℤ)) * (u test - v test)).im = 0

def formCurrent (X : Scheme.{0}) (d i : ℕ)
    (form : FormData X i) (test : FormData X (2*d-i)) : ℂ :=
  chartIntegral X d (fun c z => wedgeOnFrame d (2*d-i) i
    (test d c.point z) (form d c.point z))

/-! ## Arithmetic models and intersection multiplicities -/

abbrev RationalScheme := Over (Spec (CommRingCat.of ℚ))

def ProjectiveOver (R : Type) [CommRing R] (X : Scheme.{0}) : Prop :=
  ∃ n : ℕ,
    letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R) := MvPolynomial.gradedAlgebra
    ∃ f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R), IsClosedImmersion f

def ratPoint : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))

def genericFiber (Y : ArithmeticScheme) : RationalScheme :=
  Over.mk (pullback.snd Y.hom ratPoint)

def genericInclusion (Y : ArithmeticScheme) : (genericFiber Y).left ⟶ Y.left :=
  pullback.fst Y.hom ratPoint

def cubeOverMap {Y X : Scheme.{0}} (f : Y ⟶ X) (m : ℕ) : cube Y m ⟶ cube X m :=
  prod.map f (𝟙 _)

/-- The pushforward of an integral subvariety has coefficient its generic residue degree.
A positive-dimensional generic fiber gives residue degree zero. -/
def pushCycle {Y X : Scheme.{0}} (f : Y ⟶ X) (c : CycleCoeffs Y) : CycleCoeffs X := by
  classical
  exact fun x => ∑ᶠ y : Y, if f y = x then (f.residueDegree y : ℚ) * c y else 0

def RegularModel (Y : ArithmeticScheme) : Prop :=
  ProjectiveOver ℤ Y.left ∧ Flat Y.hom ∧ ∀ y : Y.left, IsRegularLocalRing (Y.left.presheaf.stalk y)

def IsAlteration {X Y : RationalScheme} (f : Y ⟶ X) : Prop :=
  Smooth Y.hom ∧ IsProper f.left ∧ Surjective f.left ∧
    ∃ (U : X.left.Opens), Dense (U : Set X.left) ∧ Dense (f.left ⁻¹' (U : Set X.left)) ∧
      IsFinite (pullback.snd f.left U.ι) ∧ Flat (pullback.snd f.left U.ι)

/-- Generic restrictions from a regular alteration, pushed to X as in Scholl's
definition of the integral part of rational motivic cohomology. -/
def integralChow (X : RationalScheme) (r m : ℕ) :
    Submodule ℚ (CycleCoeffs (cube X.left m) ⧸ relations X.left r m) :=
  Submodule.span ℚ {v | ∃ (Y : ArithmeticScheme) (f : genericFiber Y ⟶ X),
    RegularModel Y ∧ IsAlteration f ∧ ∃ c ∈ cycles Y.left r m,
      v = (relations X.left r m).mkQ (pushCycle (cubeOverMap f.left m)
        (pullCycle (cubeOverMap (genericInclusion Y) m) c))}

/-- Ideal of the closure of the generic point x in the local ring at y. -/
def primeStalkIdeal (X : Scheme.{0}) (x y : X) : Ideal (X.presheaf.stalk y) :=
  Ideal.span {a | ∃ (U : X.Opens) (hy : y ∈ U) (g : Γ(X,U)),
    (X.presheaf.germ U y hy) g = a ∧
    ∀ hx : x ∈ U, (X.residue x) ((X.presheaf.germ U x hx) g) = 0}

/-- Serre intersection multiplicity for two properly intersecting cycles at z. -/
def intersectionMultiplicity (X : Scheme.{0}) (x y z : X) : ℤ :=
  let R := X.presheaf.stalk z
  let A := ModuleCat.of R (R ⧸ primeStalkIdeal X x z)
  let B := ModuleCat.of R (R ⧸ primeStalkIdeal X y z)
  ∑ᶠ k : ℕ, (-1 : ℤ)^k * ((Module.length R (((Tor (ModuleCat R) k).obj A).obj B)).toNat : ℤ)

def properIntersection (X : Scheme.{0}) (codim : ℕ) (a b : CycleCoeffs X) : Prop :=
  ∀ x, a x ≠ 0 → ∀ y, b y ≠ 0 → ∀ z ∈ closure ({x} : Set X) ∩ closure ({y} : Set X),
    codim ≤ Order.coheight z

def cycleProduct (X : Scheme.{0}) (codim : ℕ) (a b : CycleCoeffs X) : CycleCoeffs X := by
  classical
  exact fun z => if Order.coheight z = codim then
    ∑ᶠ x : X, ∑ᶠ y : X, a x * b y * (intersectionMultiplicity X x y z : ℚ)
    else 0

/-- The structure sheaf of an integral closed subscheme as a module on the ambient scheme. -/
def structureModule (X : Scheme.{0}) (x : X) : X.Modules :=
  let I := primeCycleIdeal X x
  (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)

def IsBundle (X : Scheme.{0}) (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃ n : ℕ, Nonempty
    ((Scheme.Modules.pullback U.ι).obj M ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules))

structure BundleResolution (X : Scheme.{0}) (M : X.Modules) where
  complex : ChainComplex X.Modules ℕ
  bundles : ∀ j, IsBundle X (complex.X j)
  bounded : ∃ s, ∀ j > s, IsZero (complex.X j)
  resolved : Nonempty (complex.homology 0 ≅ M)
  acyclic : ∀ j, IsZero (complex.homology (j+1))

def abelianSheaf {X : Scheme.{0}} (M : X.Modules) :
    TopCat.Sheaf AddCommGrpCat X :=
  ⟨M.presheaf, M.isSheaf⟩

/-- On a regular projective model, this is the finite intersection contribution for
prime cycles disjoint on the generic fiber. The Tor sheaves have proper vertical
support, so their cohomology groups are finite. -/
def finiteIntersection (X : Scheme.{0}) (x y : X) : ℝ := by
  classical
  let D := primeCycleIdeal X y
  let res := BundleResolution X (structureModule X x)
  exact if h : Nonempty res then
    let C := ((Scheme.Modules.pullback D.subschemeι).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj h.some.complex
    ∑ᶠ i : ℕ, ∑ᶠ j : ℕ, (-1 : ℝ)^(i+j) *
      Real.log (Nat.card ((abelianSheaf (C.homology i)).H j))
  else 0

/-! ## Chow projectors and their local Euler factors -/

def fundamentalCycle (X : Scheme.{0}) : CycleCoeffs X := by
  classical
  exact fun x => if Order.coheight x = 0 then
    ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℚ) else 0

def graphCycle {X Y : Scheme.{0}} (f : X ⟶ Y) : CycleCoeffs (X ⨯ Y) :=
  pushCycle (prod.lift (𝟙 X) f) (fundamentalCycle X)

def ordinaryCycles (X : Scheme.{0}) (r : ℕ) : Submodule ℚ (CycleCoeffs X) := by
  classical
  exact Submodule.span ℚ {c | ∃ x : X, Order.coheight x = r ∧ c = Pi.single x 1}

def rationallyEquivalent {X : Scheme.{0}} (r : ℕ) (a b : CycleCoeffs X) : Prop :=
  pullCycle (prod.fst : cube X 0 ⟶ X) (a-b) ∈ relations X r 0

abbrev ChowAmbient (X : Scheme.{0}) (r m : ℕ) := CycleCoeffs (cube X m) ⧸ relations X r m

/-- Apply a correspondence from X to Y to a higher Chow class. Representatives must
intersect properly on every face of the cube for the pull-intersect-push formula. -/
def ActsOnChow {X Y : Scheme.{0}} (dX r m : ℕ) (P : CycleCoeffs (X ⨯ Y))
    (a : ChowAmbient X r m) (b : ChowAmbient Y r m) : Prop :=
  ∃ P' ∈ ordinaryCycles (X ⨯ Y) dX, rationallyEquivalent dX P P' ∧
  ∃ c ∈ cycles X r m, a = (relations X r m).mkQ c ∧
    let u := pullCycle (prod.fst : cube (X ⨯ Y) m ⟶ X ⨯ Y) P'
    let v := pullCycle (cubeOverMap (prod.fst : X ⨯ Y ⟶ X) m) c
    (∀ k (F : Face k m) x, u x ≠ 0 → ∀ y, v y ≠ 0 →
      ∀ z : cube (X ⨯ Y) k, F.map _ z ∈ closure ({x} : Set _) ∩ closure ({y} : Set _) →
        dX+r ≤ Order.coheight z) ∧
    b = (relations Y r m).mkQ (pushCycle (cubeOverMap (prod.snd : X ⨯ Y ⟶ Y) m)
      (cycleProduct _ (dX+r) u v))

def ordinaryClass {X : Scheme.{0}} (r : ℕ) (a : CycleCoeffs X) : ChowAmbient X r 0 :=
  (relations X r 0).mkQ (pullCycle (prod.fst : cube X 0 ⟶ X) a)

/-- Idempotence in the ring of rational Chow correspondences. -/
def ChowProjector (X : Scheme.{0}) (d : ℕ) (P : CycleCoeffs (X ⨯ X)) : Prop :=
  P ∈ ordinaryCycles _ d ∧
  ∃ A ∈ ordinaryCycles _ d, ∃ B ∈ ordinaryCycles _ d,
    rationallyEquivalent d P A ∧ rationallyEquivalent d P B ∧
    let V := (X ⨯ X) ⨯ X
    let p₁₂ : V ⟶ X ⨯ X := prod.fst
    let p₂₃ : V ⟶ X ⨯ X := prod.lift (prod.fst ≫ prod.snd) prod.snd
    let p₁₃ : V ⟶ X ⨯ X := prod.lift (prod.fst ≫ prod.fst) prod.snd
    let a := pullCycle p₁₂ A
    let b := pullCycle p₂₃ B
    properIntersection V (2*d) a b ∧
      rationallyEquivalent d (pushCycle p₁₃ (cycleProduct V (2*d) a b)) P

def transposeCycle {X Y : Scheme.{0}} (P : CycleCoeffs (X ⨯ Y)) : CycleCoeffs (Y ⨯ X) :=
  pushCycle (prod.braiding X Y).hom P

/-- Poincaré duality tests whether a class is fixed by a degree-zero correspondence. -/
def fixedCohomology (X : Scheme.{0}) (d i : ℕ) (P : CycleCoeffs (X ⨯ X))
    (v : CochainClasses X i) : Prop :=
  ∃ form : FormData X i, IsClosedForm form ∧ v = (exactCochains X i).mkQ (integrateCube form) ∧
    ∀ test : FormData X (2*d-i), IsClosedForm test →
      formCurrent X d i form test = ∑ᶠ x : ↥(X ⨯ X), (P x : ℂ) *
        let j := (primeCycleIdeal _ x).subschemeι
        chartIntegral _ d (fun c z => wedgeOnFrame d (2*d-i) i
          (test d (fun t => c.point t ≫ j ≫ prod.snd) z)
          (form d (fun t => c.point t ≫ j ≫ prod.fst) z))

def pPoint (p : Nat.Primes) : Spec (CommRingCat.of (ZMod p.val)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p.val)))

def modFiber (A : ArithmeticScheme) (p : Nat.Primes) := pullback A.hom (pPoint p)

def IsFrobenius {Y : Scheme.{0}} (q : ℕ) (F : Y ⟶ Y) : Prop :=
  (∀ y : Y, F y = y) ∧ ∀ (U : Y.Opens) (h : U ≤ F ⁻¹ᵁ U) (s : Γ(Y,U)),
    F.appLE U U h s = s^q

def specializeProjector (A : ArithmeticScheme) (p : Nat.Primes)
    (P : CycleCoeffs ((genericFiber A).left ⨯ (genericFiber A).left)) :
    CycleCoeffs (modFiber A p ⨯ modFiber A p) :=
  let j := genericInclusion A
  let k := pullback.fst A.hom (pPoint p)
  pullCycle (prod.map k k) (pushCycle (prod.map j j) P)

/-- The Lefschetz trace is the intersection degree with the graph of Frobenius.
For the diagonal projector this recovers the point count. -/
def frobeniusTrace (Y : Scheme.{0}) (p : Nat.Primes) (P : CycleCoeffs (Y ⨯ Y))
    (F : Y ⟶ Y) : ℝ :=
  ∑ᶠ x : ↥(Y ⨯ Y), ∑ᶠ y : ↥(Y ⨯ Y), (P x : ℝ) * (graphCycle F y : ℝ) *
    finiteIntersection (Y ⨯ Y) x y / Real.log p.val

/-- Omit finitely many primes, including all bad ones. At a right-hand integer
2n > i the removed Euler factors have nonzero rational values under the usual
local-factor hypotheses. The order and the leading coefficient modulo ℚˣ are unchanged. -/
def IsMotivicL (A : ArithmeticScheme) (d : ℕ) (i : Fin (2*d+1))
    (P : CycleCoeffs ((genericFiber A).left ⨯ (genericFiber A).left))
    (bad : Finset Nat.Primes) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧
  ∃ roots : {p : Nat.Primes // p ∉ bad} → Fin (2*d+1) → Multiset ℂ,
    (∀ p, SmoothOfRelativeDimension d (pullback.snd A.hom (pPoint p.val)) ∧
      (∀ j, ∀ α ∈ roots p j, ‖α‖ ^ 2 = (p.val.val : ℝ)^j.val) ∧
      ∀ k : ℕ+, ∃ F : modFiber A p.val ⟶ modFiber A p.val, IsFrobenius (p.val.val^k.val) F ∧
        (frobeniusTrace _ p.val (specializeProjector A p.val P) F : ℂ) =
          ∑ j, (-1 : ℂ)^j.val * ((roots p j).map (fun α => α^k.val)).sum) ∧
    ∀ s : ℂ, (i.val : ℝ) / 2 + 1 < s.re →
      HasProd (fun p => eulerFactor (roots p i) p.val s) (L s)

/-! ## Arithmetic heights -/

def cycleCurrent {X : Scheme.{0}} (d r : ℕ) (a : CycleCoeffs X) {k : ℕ}
    (test : FormData X k) : ℂ :=
  ∑ᶠ x : X, (a x : ℂ) * cycleIntegral (primeCycleIdeal X x).subschemeι (d-r) test

def cycleSupport {X : Scheme.{0}} (a : CycleCoeffs X) : Set X :=
  {y | ∃ x, a x ≠ 0 ∧ y ∈ closure ({x} : Set X)}

def homologicallyTrivial {X : Scheme.{0}} (d r : ℕ) (a : CycleCoeffs X) : Prop :=
  ∀ test : FormData X (2*(d-r)), IsClosedForm test → cycleCurrent d r a test = 0

def finitePair {X : Scheme.{0}} (a b : CycleCoeffs X) : ℝ :=
  ∑ᶠ x : X, ∑ᶠ y : X, (a x : ℝ) * (b y : ℝ) * finiteIntersection X x y

def verticalOrthogonal (Y : ArithmeticScheme) (k : ℕ) (a : CycleCoeffs Y.left) : Prop :=
  ∀ y : Y.left, ringChar (Y.left.residueField y) ≠ 0 → Order.coheight y = k →
    ∑ᶠ x : Y.left, (a x : ℝ) * finiteIntersection Y.left x y = 0

/-- The smooth locus of a plot in the complement of the support of an algebraic cycle. -/
def offSupport {X : Scheme.{0}} (a : CycleCoeffs X) {n : ℕ}
    (p : Coord n → CPoint X) : Set (Coord n) :=
  plotLocus ℝ p ∩ {z | supportPoint (p z) ∉ cycleSupport a}

/-- A locally integrable real form of bidegree (r-1,r-1), smooth off the cycle.
Its values on the support are set to zero for integrating the associated current. -/
def greenRepresentative {X : Scheme.{0}} (d r : ℕ) (a : CycleCoeffs X)
    (g : FormData X (2*(r-1))) : Prop :=
  realForm g ∧ InHodgeFiltration (r-1) g ∧
  (∀ n p z, z ∉ offSupport a p → g n p z = 0) ∧
  (∀ n p, ContDiffOn ℝ ∞ (g n p) (offSupport a p)) ∧
  (∀ n m (p : Coord n → CPoint X) (f : Coord m → Coord n) z,
    f z ∈ offSupport a p → z ∈ interior {w | ContDiffAt ℝ ∞ f w} →
      g m (p ∘ f) z = (g n p (f z)).compContinuousLinearMap (fderiv ℝ f z)) ∧
  ∀ (c : HolChart X d) (v : Fin (2*(r-1)) → Coord d),
    LocallyIntegrableOn (fun z => g d c.point z v) c.source

/-- On a pure (s,s) test form, dᶜ is minus pullback of dη on tangent vectors by
the complex structure, divided by 4π. This gives ddᶜ = (i/2π)∂∂̄. -/
def ddComplex {d k : ℕ} (η : Coord d → Alt d k) (z : Coord d) : Alt d (k+1+1) :=
  let J := (Complex.I • ContinuousLinearMap.id ℂ (Coord d)).restrictScalars ℝ
  extDeriv (𝕜 := ℝ) (fun w => (-(4 * Real.pi)⁻¹ : ℝ) •
    (extDeriv (𝕜 := ℝ) η w).compContinuousLinearMap J) z

/-- The Green current of a null-homologous cycle has zero curvature:
ddᶜ[g] = -δ(a), as currents on the compact complex fiber. -/
def isGreenForm {X : Scheme.{0}} (d r : ℕ) (a : CycleCoeffs X)
    (g : FormData X (2*(r-1))) : Prop :=
  greenRepresentative d r a g ∧
  ∀ η : FormData X (2*(d-r)), IsSmoothForm η → realForm η → InHodgeFiltration (d-r) η →
    chartIntegral X d (fun c z => wedgeOnFrame d (2*(d-r)+1+1) (2*(r-1))
      (ddComplex (η d c.point) z) (g d c.point z)) + cycleCurrent d r a η = 0

/-- Regular arithmetic alterations with disjoint generic representatives and extensions
orthogonal to vertical cycles. These are the geometric lifting hypotheses in the
arithmetic intersection construction of the height. -/
structure HeightLifts (X : RationalScheme) (d r : ℕ)
    (a : ChowAmbient X.left r 0) (b : ChowAmbient X.left (d+1-r) 0) where
  model : ArithmeticScheme
  map : genericFiber model ⟶ X
  degree : ℕ+
  regular : RegularModel model
  alteration : IsAlteration map
  genericDegree : pushCycle map.left (fundamentalCycle _) = (degree.val : ℚ) • fundamentalCycle X.left
  first : CycleCoeffs model.left
  second : CycleCoeffs model.left
  firstCycle : first ∈ ordinaryCycles model.left r
  secondCycle : second ∈ ordinaryCycles model.left (d+1-r)
  representsFirst : ActsOnChow d r 0 (transposeCycle (graphCycle map.left)) a
    (ordinaryClass r (pullCycle (genericInclusion model) first))
  representsSecond : ActsOnChow d (d+1-r) 0 (transposeCycle (graphCycle map.left)) b
    (ordinaryClass (d+1-r) (pullCycle (genericInclusion model) second))
  disjointGeneric : Disjoint (cycleSupport (pullCycle (genericInclusion model) first))
    (cycleSupport (pullCycle (genericInclusion model) second))
  firstOrthogonal : verticalOrthogonal model (d+1-r) first
  secondOrthogonal : verticalOrthogonal model r second

/-- Arithmetic degrees are over ℤ. The sum over all complex embeddings has a
factor of one half. The projection formula divides by the degree of the alteration. -/
def HasHeight (X : RationalScheme) (d r : ℕ)
    (a : ChowAmbient X.left r 0) (b : ChowAmbient X.left (d+1-r) 0) (h : ℝ) : Prop :=
  ∃ c : HeightLifts X d r a b,
    let u := pullCycle (genericInclusion c.model) c.first
    let v := pullCycle (genericInclusion c.model) c.second
    ∃ g, isGreenForm d r u g ∧ (c.degree.val : ℝ) * h =
      finitePair c.first c.second + (cycleCurrent d (d+1-r) v g).re / 2

/-! ## Regulator and height determinants -/

abbrev Tangent (X : Scheme.{0}) (i n : ℕ) :=
  CochainClasses X i ⧸ hodge X i n

def rationalTangent (X : RationalScheme) (d i n : ℕ) (P : CycleCoeffs (X.left ⨯ X.left)) :
    Submodule ℚ (Tangent X.left i n) :=
  Submodule.span ℚ {v | ∃ x ∈ deRham X i, fixedCohomology X.left d i P x ∧
    v = (hodge X.left i n).mkQ x}

def geometricConjugation {X : Scheme.{0}} (p : CPoint X) : CPoint X :=
  Spec.map (CommRingCat.ofHom Complex.conjAe.toRingHom) ≫ p

/-- The plus part of Betti cohomology after the Tate twist and the period comparison.
Conjugation on points acts on the untwisted rational class by (-1)^n. -/
def bettiPlus (X : Scheme.{0}) (d i n : ℕ) (P : CycleCoeffs (X ⨯ X)) :
    Submodule ℚ (Tangent X i n) :=
  Submodule.span ℚ {v | ∃ a : Cochains X i,
    let u := (exactCochains X i).mkQ a
    u ∈ Betti X i ∧ fixedCohomology X d i P u ∧
    (fun σ => a (geometricConjugation ∘ σ) - (-1 : ℂ)^n * a σ) ∈ exactCochains X i ∧
    v = (hodge X i n).mkQ (tatePeriod^n • u)}

def projectedIntegralChow (X : RationalScheme) (d r m : ℕ)
    (P : CycleCoeffs (X.left ⨯ X.left)) : Submodule ℚ (ChowAmbient X.left r m) :=
  Submodule.span ℚ {b | ∃ a ∈ integralChow X r m, ActsOnChow d r m P a b}

abbrev ClosedTest (X : Scheme.{0}) (k : ℕ) := {η : FormData X k // IsClosedForm η}

/-- In weight -2 the source has the additional summand of algebraic cycle classes
modulo homological equivalence, embedded by its periods on closed test forms. -/
def nearCycles (X : Scheme.{0}) (d i n : ℕ) (P : CycleCoeffs (X ⨯ X)) :
    Submodule ℚ (ClosedTest X (2*d-i) → ℂ) :=
  if 2*n = i+2 then Submodule.span ℚ {v | ∃ a ∈ ordinaryCycles X (n-1),
    ActsOnChow d (n-1) 0 P (ordinaryClass (n-1) a) (ordinaryClass (n-1) a) ∧
    v = fun η => cycleCurrent d (n-1) a η.val}
  else ⊥

def nullChow (X : Scheme.{0}) (d r : ℕ) (P : CycleCoeffs (X ⨯ X)) :
    Submodule ℚ (ChowAmbient X r 0) :=
  Submodule.span ℚ {b | ∃ a ∈ ordinaryCycles X r, homologicallyTrivial d r a ∧
    b = ordinaryClass r a ∧ ActsOnChow d r 0 P b b}

def rationalBasis {V : Type*} [AddCommGroup V] [Module ℚ V] {J : Type*}
    (b : J → V) (S : Submodule ℚ V) : Prop :=
  LinearIndependent ℚ b ∧ Submodule.span ℚ (Set.range b) = S

def matrixColumn {V J : Type*} [AddCommGroup V] [Module ℂ V] [Fintype J]
    (t : J → V) (R : Matrix J J ℝ) (j : J) : V :=
  ∑ h, (R h j : ℂ) • t h

def liftsRegulator (X : Scheme.{0}) (d i n l : ℕ) (a : ChowAmbient X n (l+1))
    (v : Tangent X i n) : Prop :=
  ∃ c ∈ cycles X n (l+1), a = (relations X n (l+1)).mkQ c ∧
  ∃ form : FormData X i, IsClosedForm form ∧
    v = (hodge X i n).mkQ ((exactCochains X i).mkQ (integrateCube form)) ∧
    sameDeligneClass X d i n (formCurrent X d i form)
      (fun η => ∑ᶠ x : cube X (l+1), (c x : ℂ) * primeRegulator d n l x η)

def liftsCycleClass (X : Scheme.{0}) (d i n : ℕ)
    (a : ClosedTest X (2*d-i) → ℂ) (v : Tangent X i n) : Prop :=
  ∃ form : FormData X i, IsClosedForm form ∧
    v = (hodge X i n).mkQ ((exactCochains X i).mkQ (integrateCube form)) ∧
    ∀ η : ClosedTest X (2*d-i), realForm η.val → InHodgeFiltration (d+1-n) η.val →
      (Complex.I ^ (-(n : ℤ)) * (formCurrent X d i form η.val - tatePeriod^(n-1) * a η)).im = 0

/-- Write the determinant-line identity in rational bases. The first block of columns
is Betti comparison. The other two lift the higher regulator and the cycle class map.
The determinant of all columns is the regulator measured in the de Rham determinant
line divided by the Betti-plus determinant line. -/
def regulatorPrediction (X : RationalScheme) (d i n : ℕ) (P : CycleCoeffs (X.left ⨯ X.left))
    (L : ℂ → ℂ) : Prop :=
  let l := 2*n-i-2
  ∃ k a b : ℕ,
    let J := Fin k ⊕ (Fin a ⊕ Fin b)
    ∃ (B : Fin k → Tangent X.left i n)
      (A : Fin a → ChowAmbient X.left n (l+1))
      (N : Fin b → (ClosedTest X.left (2*d-i) → ℂ))
      (T : J → Tangent X.left i n) (R : Matrix J J ℝ),
      rationalBasis B (bettiPlus X.left d i n P) ∧
      rationalBasis A (projectedIntegralChow X d n (l+1) P) ∧
      rationalBasis N (nearCycles X.left d i n P) ∧
      rationalBasis T (rationalTangent X d i n P) ∧
      (∀ j, matrixColumn T R (.inl j) = B j) ∧
      (∀ j, liftsRegulator X.left d i n l (A j) (matrixColumn T R (.inr (.inl j)))) ∧
      (∀ j, liftsCycleClass X.left d i n (N j) (matrixColumn T R (.inr (.inr j)))) ∧
      SameRationalLine (meromorphicTrailingCoeffAt L (n : ℂ)) (R.det : ℂ)

/-- The central point uses the Beilinson--Bloch height of homologically trivial cycles.
The rank assertion is unconditional on the construction of the height. The determinant
assertion uses the arithmetic height whenever the admissible liftings defining it exist. -/
def centralPrediction (X : RationalScheme) (d i n : ℕ) (P : CycleCoeffs (X.left ⨯ X.left))
    (L : ℂ → ℂ) : Prop :=
  ∃ r : ℕ,
    meromorphicOrderAt L (n : ℂ) = ((r : ℤ) : WithTop ℤ) ∧
    (∃ A : Fin r → ChowAmbient X.left n 0, rationalBasis A (nullChow X.left d n P)) ∧
    (∃ D : Fin r → ChowAmbient X.left (d+1-n) 0,
      rationalBasis D (nullChow X.left d (d+1-n) (transposeCycle P))) ∧
    ∃ k : ℕ, ∃ (B T : Fin k → Tangent X.left i n) (R : Matrix (Fin k) (Fin k) ℝ),
      rationalBasis B (bettiPlus X.left d i n P) ∧
      rationalBasis T (rationalTangent X d i n P) ∧
      (∀ j, matrixColumn T R j = B j) ∧ R.det ≠ 0 ∧
      ∀ (A : Fin r → ChowAmbient X.left n 0) (D : Fin r → ChowAmbient X.left (d+1-n) 0),
        rationalBasis A (nullChow X.left d n P) →
        rationalBasis D (nullChow X.left d (d+1-n) (transposeCycle P)) →
        ((∀ u v, Nonempty (HeightLifts X d n (A u) (D v))) →
          ∃ H : Matrix (Fin r) (Fin r) ℝ, H.det ≠ 0 ∧
            ∀ u v, HasHeight X d n (A u) (D v) (H u v)) ∧
        ∀ H : Matrix (Fin r) (Fin r) ℝ, (∀ u v, HasHeight X d n (A u) (D v) (H u v)) →
          SameRationalLine (meromorphicTrailingCoeffAt L (n : ℂ)) ((R.det * H.det : ℝ) : ℂ)

/-! ## The reflected special value -/

/-- Multiplicity of H^(p,i-p), with an optional eigensign for geometric conjugation
on a diagonal Hodge summand. -/
def hodgeMultiplicity (X : Scheme.{0}) (d i p : ℕ) (P : CycleCoeffs (X ⨯ X))
    (sign : Option ℤ) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ {v : CochainClasses X i | fixedCohomology X d i P v ∧
    ∃ form : FormData X i, IsClosedForm form ∧
      (∀ k (u : Coord k → CPoint X), ∀ z ∈ plotLocus ℂ u, ∀ J : Finset (Fin i),
        J.card ≠ p → ∀ t, typeComponent (form k u z) J t = 0) ∧
      let c := integrateCube form
      v = (exactCochains X i).mkQ c ∧
      ∀ e ∈ sign, (fun σ => c (geometricConjugation ∘ σ) - (e : ℂ)*c σ) ∈ exactCochains X i})

def infiniteFactor (X : Scheme.{0}) (d i : ℕ) (P : CycleCoeffs (X ⨯ X)) (s : ℂ) : ℂ :=
  ∏ p ∈ Finset.range (i+1),
    if 2*p < i then Complex.Gammaℂ (s-p)^hodgeMultiplicity X d i p P none
    else if 2*p = i then
      Complex.Gammaℝ (s-p)^hodgeMultiplicity X d i p P (some ((-1)^p)) *
      Complex.Gammaℝ (s-p+1)^hodgeMultiplicity X d i p P (some (-((-1)^p)))
    else 1

/-- A possible set of omitted Euler factors, under the usual local rationality
and weight hypotheses. Their roots have absolute value at most p^(i/2). -/
def completesEulerProduct (bad : Finset Nat.Primes) (i : ℕ) (incomplete full : ℂ → ℂ) : Prop :=
  Meromorphic full ∧ ∃ roots : Nat.Primes → Multiset ℂ,
    (∀ p ∈ bad, (∀ α ∈ roots p, ‖α‖^2 ≤ (p.val : ℝ)^i) ∧
      ∀ k, ∃ q : ℚ, (roots p).esymm k = (q : ℂ)) ∧
    ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s, full z = incomplete z * ∏ p ∈ bad, eulerFactor (roots p) p z

/-- The standard functional equation of the motive and its Poincaré dual singles out
the primitive pair amongst completions at finitely many bad primes. Indeed, a ratio of
two candidates has its finite local zeroes and poles in Re(s) ≤ i/2, while the ratio
on the reflected side has them in Re(s) ≥ 1+i/2. The Euler polynomials have constant
term one. The formulation is conditional on the usual analytic hypotheses. -/
def functionalEquation (X : Scheme.{0}) (d i : ℕ) (P : CycleCoeffs (X ⨯ X))
    (L dual : ℂ → ℂ) : Prop :=
  ∃ (N : ℕ+) (ε : ℂ), ‖ε‖ = 1 ∧ ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s,
    let t := (d : ℂ)+1-z
    infiniteFactor X d i P z * L z =
      ε * (N.val : ℂ)^(((i : ℂ)+1)/2-z) *
        infiniteFactor X d (2*d-i) (transposeCycle P) t * dual t

/-- The full period determinant δ(M) uses all twisted Betti and de Rham classes.
Together with the dimension of the minus part it gives Nekovář's change of
determinant structure from D(M) to B(M), including the power of 2πi. -/
def reflectedValue (X : RationalScheme) (d i n : ℕ) (P : CycleCoeffs (X.left ⨯ X.left))
    (L dual : ℂ → ℂ) : Prop :=
  let B := Submodule.span ℚ {v | ∃ u ∈ Betti X.left i, fixedCohomology X.left d i P u ∧
    v = tatePeriod^n • u}
  let D := Submodule.span ℚ {v : CochainClasses X.left i | v ∈ deRham X i ∧
    fixedCohomology X.left d i P v}
  let b := Module.finrank ℚ (bettiPlus X.left d i n P)
  let t := Module.finrank ℚ (rationalTangent X d i n P)
  let s := (d : ℂ)+1-n
  meromorphicOrderAt dual s = meromorphicOrderAt L (n : ℂ) + ((t-b : ℕ) : ℤ) ∧
  ∃ m : ℕ, ∃ (U V : Fin m → CochainClasses X.left i) (R : Matrix (Fin m) (Fin m) ℂ),
    rationalBasis U B ∧ rationalBasis V D ∧ (∀ j, U j = ∑ k, R k j • V k) ∧
    SameRationalLine (meromorphicTrailingCoeffAt L (n : ℂ))
      (meromorphicTrailingCoeffAt dual s * tatePeriod^(-((m-b : ℕ) : ℤ)) * R.det)

/-- Beilinson's special-value conjectures with rational coefficients. A Tate twist shifts
the evaluation argument, so n runs over every integer with i-2n < 0. The reflected
argument on the dual runs through the complementary integers. A variety over a number
field is viewed over ℚ by composition, with its correspondence on the corresponding
open-and-closed component of the product. -/
theorem main :
    ∀ (A : ArithmeticScheme) (d : ℕ) (i : Fin (2*d+1)) (n : ℕ),
      let X := genericFiber A
      ProjectiveOver ℤ A.left → Flat A.hom → SmoothOfRelativeDimension d X.hom →
      i.val < 2*n → ∀ P : CycleCoeffs (X.left ⨯ X.left), ChowProjector X.left d P →
      ∀ (bad : Finset Nat.Primes) (L : ℂ → ℂ), IsMotivicL A d i P bad L →
        (if 2*n = i.val+1 then centralPrediction X d i.val n P L
         else regulatorPrediction X d i.val n P L) ∧
        (i.val+1 < 2*n →
          ∀ (j : Fin (2*d+1)), j.val = 2*d-i.val →
          ∀ (omitted : Finset Nat.Primes) (dual : ℂ → ℂ),
            IsMotivicL A d j (transposeCycle P) omitted dual →
            ∀ F G : ℂ → ℂ, completesEulerProduct bad i.val L F →
              completesEulerProduct omitted j.val dual G → functionalEquation X.left d i.val P F G →
              reflectedValue X d i.val n P F G) := by
  sorry

end

end OMA.S_wp_beilinson_s_conjectures_about_special_values_of_l_functions
