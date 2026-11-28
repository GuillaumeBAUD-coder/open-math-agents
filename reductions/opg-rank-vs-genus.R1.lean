import OMAStatements.S_opg_rank_vs_genus
import Mathlib

/-!
# Rank vs genus: reduction to Heegaard existence (H1) and Tao Li's genus bound (H2)

Every witness of the target is `H³/Γ` for a discrete, torsion-free, cocompact `Γ ≤ O⁺(3,1)`.
This file proves all of the topology and group theory between such a `Γ` and the target:
`H³ ≃ₜ ℝ³` (so `H³` is simply connected), a Lorentz isometry moving `x` to `y` has entries
`≤ 10 x₀ y₀` (so a discrete `Γ` acts properly discontinuously and `H³/Γ` is Hausdorff), a compact
set meeting every orbit makes `H³/Γ` compact, the quotient map is a covering map, and by
monodromy `π₁(H³/Γ) ≅ Γ`, so a finite generating set of `Γ` generates `π₁` with at most as
many elements.

What is left is exactly two classical theorems, stated for groups rather than manifolds:
* `H1`: a closed orientable hyperbolic 3-manifold `H³/Γ` (Γ discrete, free, cocompact,
  orientation preserving) has a Heegaard splitting (Moise: triangulate, thicken the 1-skeleton).
* `H2`: Tao Li, *Rank and genus of 3-manifolds*, J. Amer. Math. Soc. 26 (2013) 777–829:
  for every `gap` there is such a `Γ` with a finite generating set `T` such that every Heegaard
  splitting of `H³/Γ` has genus `> |T| + gap`.

An explicit closed hyperbolic 3-manifold satisfying every clause of the target except the
Heegaard clauses (a mod-3 congruence subgroup of the (2,3,3,3,4,2) tetrahedral reflection group)
has also been formalized; it is not needed for this reduction.
-/

namespace OMA.R_opg_rank_vs_genus_R1

open OMA.S_opg_rank_vs_genus

def H1 : Prop :=
  ∀ Γ : Subgroup LinearSymmetry,
    (∀ g : Γ, (∀ x y : LorentzSpace, lorentzForm (act g.val x) (act g.val y) = lorentzForm x y) ∧
      (∀ x : HyperbolicSpace, act g.val x.val ∈ hyperboloid)) →
    (∀ g : Γ, 0 < (g.val.val).det) →
    (∀ g : Γ, g ≠ 1 → ∀ x : HyperbolicSpace, act g.val x.val ≠ x.val) →
    (∀ C : ℝ, {g : Γ | ∀ i j, |g.val.val i j| ≤ C}.Finite) →
    ∀ (M : Type) [TopologicalSpace M], T2Space M → CompactSpace M →
    ∀ q : HyperbolicSpace → M, Continuous q → IsOpenMap q → Function.Surjective q →
      (∀ x y : HyperbolicSpace, q x = q y ↔ ∃ g : Γ, act g.val x.val = y.val) →
      ∃ g : ℕ, HasHeegaardSplitting M g

def H2 : Prop :=
  ∀ gap : ℕ, ∃ Γ : Subgroup LinearSymmetry,
    (∀ g : Γ, (∀ x y : LorentzSpace, lorentzForm (act g.val x) (act g.val y) = lorentzForm x y) ∧
      (∀ x : HyperbolicSpace, act g.val x.val ∈ hyperboloid)) ∧
    (∀ g : Γ, 0 < (g.val.val).det) ∧
    (∀ g : Γ, g ≠ 1 → ∀ x : HyperbolicSpace, act g.val x.val ≠ x.val) ∧
    (∀ C : ℝ, {g : Γ | ∀ i j, |g.val.val i j| ≤ C}.Finite) ∧
    (∃ K : Set HyperbolicSpace, IsCompact K ∧
      ∀ x : HyperbolicSpace, ∃ g : Γ, ∃ y ∈ K, act g.val x.val = y.val) ∧
    ∃ T : Finset Γ, Subgroup.closure (T : Set Γ) = ⊤ ∧
      ∀ (M : Type) [TopologicalSpace M],
      ∀ q : HyperbolicSpace → M, Continuous q → IsOpenMap q → Function.Surjective q →
        (∀ x y : HyperbolicSpace, q x = q y ↔ ∃ g : Γ, act g.val x.val = y.val) →
        ∀ g : ℕ, HasHeegaardSplitting M g → T.card + gap < g

/-! ## §1. `H³` is homeomorphic to `ℝ³` -/

lemma time_eq (x : HyperbolicSpace) :
    x.val 0 = Real.sqrt (1 + x.val 1 ^ 2 + x.val 2 ^ 2 + x.val 3 ^ 2) := by
  obtain ⟨h1, h2⟩ := x.2
  simp only [lorentzForm] at h1
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos h2]
  nlinarith

lemma lift_mem (v : Fin 3 → ℝ) :
    ![Real.sqrt (1 + v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2), v 0, v 1, v 2] ∈ hyperboloid := by
  have h : 0 ≤ 1 + v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [lorentzForm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have := Real.mul_self_sqrt h
    nlinarith
  · simp only [Matrix.cons_val_zero]
    exact Real.sqrt_pos.2 (by positivity)

theorem homeo_nonempty : Nonempty (HyperbolicSpace ≃ₜ (Fin 3 → ℝ)) :=
  ⟨{ toFun := fun x => ![x.val 1, x.val 2, x.val 3]
     invFun := fun v => ⟨_, lift_mem v⟩
     left_inv := fun x => by
       apply Subtype.ext
       funext i
       fin_cases i
       · simp [← time_eq]
       all_goals simp
     right_inv := fun v => by
       funext i
       fin_cases i <;> simp
     continuous_toFun := by
       refine continuous_pi fun i => ?_
       fin_cases i <;> simp <;> exact (continuous_apply _).comp continuous_subtype_val
     continuous_invFun := by
       refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
       fin_cases i <;> simp <;> fun_prop }⟩

theorem hyp_contractible : ContractibleSpace HyperbolicSpace :=
  homeo_nonempty.some.contractibleSpace

theorem hyp_simplyConnected : SimplyConnectedSpace HyperbolicSpace := by
  haveI := hyp_contractible; infer_instance

theorem hyp_pathConnected : PathConnectedSpace HyperbolicSpace := by
  haveI := hyp_contractible; infer_instance

theorem hyp_locallyCompact : LocallyCompactSpace HyperbolicSpace :=
  homeo_nonempty.some.isClosedEmbedding.locallyCompactSpace

lemma act_mul' (g h : LinearSymmetry) (x : LorentzSpace) :
    act (g * h) x = act g (act h x) := by
  simp only [act, Units.val_mul, Matrix.mulVec_mulVec]

/-! ## §2. `π₁` of the base of a quotient covering with simply connected total space -/

section Pi1

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)

lemma exists_deck (x : X) (e₀ : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    ∃ g : G, (hp.isCoveringMap.monodromy γ e₀ : E) = g • (e₀ : E) := by
  obtain ⟨g, hg⟩ := hp.exists_toPermFiber_eq e₀ (hp.isCoveringMap.monodromy γ e₀)
  exact ⟨g, by rw [← hg]; rfl⟩

include hp in
lemma deck_unique (x : X) (e₀ : p ⁻¹' {x}) {g g' : G}
    (h : g • (e₀ : E) = g' • (e₀ : E)) : g = g' :=
  hp.toPermFiber_ext x e₀ (Subtype.ext h)

lemma monodromy_smul (x : X) (g : G) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (hp.isCoveringMap.monodromy γ (hp.toPermFiber x g e) : E) =
      g • (hp.isCoveringMap.monodromy γ e : E) := by
  rw [hp.monodromy_toPermFiber]; rfl

lemma deck_mul_of (x : X) (e₀ : p ⁻¹' {x}) (d : FundamentalGroup X x → G)
    (hd : ∀ γ : FundamentalGroup X x, (hp.isCoveringMap.monodromy γ e₀ : E) = d γ • (e₀ : E))
    (a b : FundamentalGroup X x) : d (a * b) = d b * d a := by
  apply deck_unique hp x e₀
  rw [← hd (a * b), mul_smul (d b) (d a) (e₀ : E)]
  letI := hp.isCoveringMap.fundamentalGroupMulAction x
  have h1 : hp.isCoveringMap.monodromy (a * b) e₀ =
      hp.isCoveringMap.monodromy a (hp.isCoveringMap.monodromy b e₀) := mul_smul a b e₀
  have h2 : hp.isCoveringMap.monodromy b e₀ = hp.toPermFiber x (d b) e₀ :=
    Subtype.ext (hd b)
  rw [h1, h2, monodromy_smul, hd a]

lemma deck_one_of (x : X) (e₀ : p ⁻¹' {x}) (d : FundamentalGroup X x → G)
    (hd : ∀ γ : FundamentalGroup X x, (hp.isCoveringMap.monodromy γ e₀ : E) = d γ • (e₀ : E)) : d 1 = 1 := by
  apply deck_unique hp x e₀
  rw [← hd (1 : FundamentalGroup X x), one_smul]
  have : hp.isCoveringMap.monodromy (1 : FundamentalGroup X x) = id :=
    hp.isCoveringMap.monodromy_refl
  rw [this]; rfl

lemma deck_injective_of [SimplyConnectedSpace E] (x : X) (e₀ : p ⁻¹' {x})
    (d : FundamentalGroup X x → G)
    (hd : ∀ γ : FundamentalGroup X x, (hp.isCoveringMap.monodromy γ e₀ : E) = d γ • (e₀ : E)) :
    Function.Injective d := by
  intro a b hab
  have hm : hp.isCoveringMap.monodromy a e₀ = hp.isCoveringMap.monodromy b e₀ :=
    Subtype.ext (by rw [hd a, hd b, hab])
  have hm' := hp.monodromy_ext e₀ hm
  have hker : (hp.isCoveringMap.monodromyPerm x) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    ext e
    simp [hm']
  rw [← MonoidHom.mem_ker, hp.ker_monodromyPerm e₀] at hker
  obtain ⟨c, hc⟩ := hker
  have : c = 1 := Subsingleton.elim _ _
  rw [this, map_one] at hc
  exact mul_inv_eq_one.mp hc.symm

lemma deck_surjective_of [PathConnectedSpace E] (x : X) (e₀ : p ⁻¹' {x})
    (d : FundamentalGroup X x → G)
    (hd : ∀ γ : FundamentalGroup X x, (hp.isCoveringMap.monodromy γ e₀ : E) = d γ • (e₀ : E)) :
    Function.Surjective d := by
  intro g
  let ey : p ⁻¹' {x} := hp.toPermFiber x g e₀
  let P : Path (e₀ : E) (ey : E) := PathConnectedSpace.somePath _ _
  let Γ : Path.Homotopic.Quotient (e₀ : E) (ey : E) := ⟦P⟧
  let pc : C(E, X) := ⟨p, hp.continuous⟩
  have hx : x = p (e₀ : E) := (Set.mem_singleton_iff.mp e₀.2).symm
  have hy : x = p (ey : E) := (Set.mem_singleton_iff.mp ey.2).symm
  let γ : FundamentalGroup X x := (Γ.map pc).cast hx hy
  refine ⟨γ, ?_⟩
  have hmono : hp.isCoveringMap.monodromy γ e₀ = ey :=
    hp.isCoveringMap.monodromy_eq_of_map_eq Γ (by
      exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq _ _).trans
        (Path.Homotopic.Quotient.cast_heq _ _)).symm)
  apply deck_unique hp x e₀
  rw [← hd γ, hmono]; rfl

include hp in
/-- **Generators transfer**: `π₁(X, x) ≅ G`, so a finite generating set of `G` gives a
generating set of `π₁(X, x)` of at most the same size. -/
theorem exists_pi1_generators [SimplyConnectedSpace E] [PathConnectedSpace E] (x : X)
    (T : Finset G) (hT : Subgroup.closure (T : Set G) = ⊤) :
    ∃ S : Finset (FundamentalGroup X x), S.card ≤ T.card ∧
      Subgroup.closure (S : Set (FundamentalGroup X x)) = ⊤ := by
  classical
  obtain ⟨e, he⟩ := hp.toIsQuotientMap.surjective x
  let e₀ : p ⁻¹' {x} := ⟨e, he⟩
  choose d hd using exists_deck hp x e₀
  let φ : FundamentalGroup X x →* G :=
    { toFun := fun γ => (d γ)⁻¹
      map_one' := by
        show (d 1)⁻¹ = 1
        rw [deck_one_of hp x e₀ d hd, inv_one]
      map_mul' := fun a b => by
        show (d (a * b))⁻¹ = (d a)⁻¹ * (d b)⁻¹
        rw [deck_mul_of hp x e₀ d hd, mul_inv_rev] }
  have hinj : Function.Injective φ := fun a b hab =>
    deck_injective_of hp x e₀ d hd (inv_injective hab)
  have hsurj : Function.Surjective φ := fun g => by
    obtain ⟨γ, hγ⟩ := deck_surjective_of hp x e₀ d hd g⁻¹
    exact ⟨γ, by simp [φ, hγ]⟩
  let ψ : FundamentalGroup X x ≃* G := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨T.image ψ.symm, Finset.card_image_le, ?_⟩
  rw [Finset.coe_image]
  have h := MonoidHom.map_closure (ψ.symm : G →* FundamentalGroup X x) (T : Set G)
  rw [hT, Subgroup.map_top_of_surjective _ ψ.symm.surjective] at h
  exact h.symm

end Pi1

/-! ## §3. Hyperbolic inequalities and the entry bound -/

lemma hyp_spatial (y : LorentzSpace) (hy : y ∈ hyperboloid) :
    y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 = y 0 ^ 2 - 1 := by
  obtain ⟨h1, -⟩ := hy
  simp only [lorentzForm] at h1
  nlinarith

lemma one_le_time (y : LorentzSpace) (hy : y ∈ hyperboloid) : 1 ≤ y 0 := by
  have h := hyp_spatial y hy
  have h0 := hy.2
  nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)]

lemma cs3 (y z : LorentzSpace) :
    (y 1 * z 1 + y 2 * z 2 + y 3 * z 3) ^ 2 ≤
      (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := by
  nlinarith [sq_nonneg (y 1 * z 2 - y 2 * z 1), sq_nonneg (y 1 * z 3 - y 3 * z 1),
    sq_nonneg (y 2 * z 3 - y 3 * z 2)]

/-- Reverse Cauchy–Schwarz, quantitative: `z₀ ≤ 2 y₀ cosh d(y,z)`. -/
lemma time_le_form (y z : LorentzSpace) (hy : y ∈ hyperboloid) (hz : z ∈ hyperboloid) :
    z 0 ≤ 2 * y 0 * (-lorentzForm y z) := by
  have hcs := cs3 y z
  rw [hyp_spatial y hy, hyp_spatial z hz] at hcs
  have hy1 := one_le_time y hy
  have hz1 := one_le_time z hz
  set s := y 1 * z 1 + y 2 * z 2 + y 3 * z 3 with hs
  have hB : -lorentzForm y z = y 0 * z 0 - s := by simp only [lorentzForm, hs]; ring
  rw [hB]
  -- want `2 y₀ s ≤ z₀ (2y₀² - 1)`
  have key : 2 * y 0 * s ≤ z 0 * (2 * y 0 ^ 2 - 1) := by
    rcases le_or_gt s 0 with h | h
    · have e1 : 0 ≤ z 0 * (2 * y 0 ^ 2 - 1) := by nlinarith
      have e2 : 2 * y 0 * s ≤ 0 := by nlinarith
      linarith
    · have hsq : (2 * y 0 * s) ^ 2 ≤ (z 0 * (2 * y 0 ^ 2 - 1)) ^ 2 := by
        have h4 : 4 * y 0 ^ 2 * (y 0 ^ 2 - 1) ≤ (2 * y 0 ^ 2 - 1) ^ 2 := by nlinarith
        have h5 : (y 0 ^ 2 - 1) * (z 0 ^ 2 - 1) ≤ (y 0 ^ 2 - 1) * z 0 ^ 2 := by nlinarith
        calc (2 * y 0 * s) ^ 2 = 4 * y 0 ^ 2 * s ^ 2 := by ring
          _ ≤ 4 * y 0 ^ 2 * ((y 0 ^ 2 - 1) * (z 0 ^ 2 - 1)) := by gcongr
          _ ≤ 4 * y 0 ^ 2 * ((y 0 ^ 2 - 1) * z 0 ^ 2) := by gcongr
          _ = (4 * y 0 ^ 2 * (y 0 ^ 2 - 1)) * z 0 ^ 2 := by ring
          _ ≤ (2 * y 0 ^ 2 - 1) ^ 2 * z 0 ^ 2 := by gcongr
          _ = (z 0 * (2 * y 0 ^ 2 - 1)) ^ 2 := by ring
      have hR : 0 ≤ z 0 * (2 * y 0 ^ 2 - 1) := by nlinarith
      nlinarith
  nlinarith

/-- `cosh d(w,x) ≤ 2 w₀ x₀`. -/
lemma neg_form_le (w x : LorentzSpace) (hw : w ∈ hyperboloid) (hx : x ∈ hyperboloid) :
    -lorentzForm w x ≤ 2 * w 0 * x 0 := by
  have hcs := cs3 w x
  rw [hyp_spatial w hw, hyp_spatial x hx] at hcs
  have hw1 := one_le_time w hw
  have hx1 := one_le_time x hx
  set s := w 1 * x 1 + w 2 * x 2 + w 3 * x 3 with hs
  have hB : -lorentzForm w x = w 0 * x 0 - s := by simp only [lorentzForm, hs]; ring
  rw [hB]
  have hsq : s ^ 2 ≤ (w 0 * x 0) ^ 2 := by nlinarith
  have hpos : 0 ≤ w 0 * x 0 := by nlinarith
  nlinarith [sq_nonneg (s + w 0 * x 0)]

lemma abs_le_of_sq (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b := by
  have := sq_le_sq.mp h
  rwa [abs_of_nonneg hb] at this

lemma abs_coord_le (z : LorentzSpace) (hz : z ∈ hyperboloid) (k : Fin 4) : |z k| ≤ z 0 := by
  have h := hyp_spatial z hz
  have h0 := hz.2
  apply abs_le_of_sq _ _ h0.le
  fin_cases k <;> simp <;> nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]

/-- **Entry bound.** A Lorentz isometry preserving the future sheet that moves `x` to `y` has
all matrix entries bounded by `10 x₀ y₀`. -/
theorem entry_bound (g : LinearSymmetry)
    (hform : ∀ u v : LorentzSpace, lorentzForm (act g u) (act g v) = lorentzForm u v)
    (hsheet : ∀ x : HyperbolicSpace, act g x.val ∈ hyperboloid)
    (x y : LorentzSpace) (hx : x ∈ hyperboloid) (hy : y ∈ hyperboloid) (hxy : act g x = y)
    (i j : Fin 4) : |g.val i j| ≤ 10 * x 0 * y 0 := by
  obtain ⟨tp, htp⟩ : ∃ tp : Fin 3 → Bool → LorentzSpace, tp = fun j sgn k =>
      if k = 0 then 5/4 else if k = j.succ then (if sgn then 3/4 else -3/4) else 0 := ⟨_, rfl⟩
  have tp_mem : ∀ j sgn, tp j sgn ∈ hyperboloid := by
    intro j sgn
    subst htp
    refine ⟨?_, by simp⟩
    fin_cases j <;> cases sgn <;> simp [lorentzForm, Fin.succ] <;> norm_num
  have tp_time : ∀ j sgn, tp j sgn 0 = 5/4 := by intro j sgn; subst htp; simp
  have mulVec_tp : ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 3) (i : Fin 4),
      A.mulVec (tp j true) i - A.mulVec (tp j false) i = (3/2) * A i j.succ := by
    intro A j i
    subst htp
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.succ] <;> ring
  have mulVec_tp0 : ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4),
      A.mulVec (tp 0 true) i + A.mulVec (tp 0 false) i = (5/2) * A i 0 := by
    intro A i
    subst htp
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring
  have hx1 := one_le_time x hx
  have hy1 := one_le_time y hy
  have himg : ∀ (j : Fin 3) (sgn : Bool) (k : Fin 4),
      |act g (tp j sgn) k| ≤ 5 * x 0 * y 0 := by
    intro j sgn k
    have hw := tp_mem j sgn
    have hgw : act g (tp j sgn) ∈ hyperboloid := hsheet ⟨_, hw⟩
    have h1 := time_le_form y (act g (tp j sgn)) hy hgw
    have hF : -lorentzForm y (act g (tp j sgn)) = -lorentzForm (tp j sgn) x := by
      rw [← hxy, hform]; simp only [lorentzForm]; ring
    rw [hF] at h1
    have h2 := neg_form_le (tp j sgn) x hw hx
    rw [tp_time] at h2
    have h3 := abs_coord_le _ hgw k
    have hy0 : 0 ≤ y 0 := by linarith
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * y 0)
    nlinarith
  have hxy0 : 0 ≤ x 0 * y 0 := by nlinarith
  by_cases hj : j = 0
  · subst hj
    have h := mulVec_tp0 g.val i
    have ha := himg 0 true i
    have hb := himg 0 false i
    simp only [act] at ha hb
    rw [abs_le] at ha hb ⊢
    constructor <;> nlinarith
  · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    have h := mulVec_tp g.val j' i
    have ha := himg j' true i
    have hb := himg j' false i
    simp only [act] at ha hb
    rw [abs_le] at ha hb ⊢
    constructor <;> nlinarith

/-! ## §4. The package: from `Γ` to the target's clauses -/

lemma exists_time_bound (K : Set HyperbolicSpace) (hK : IsCompact K) :
    ∃ R, ∀ x ∈ K, x.val 0 ≤ R := by
  obtain ⟨R, hR⟩ := hK.bddAbove_image
    (f := fun x : HyperbolicSpace => x.val 0)
    ((continuous_apply 0).comp continuous_subtype_val).continuousOn
  exact ⟨R, fun x hx => hR ⟨x, hx, rfl⟩⟩

/-- The action of `Γ` on `H³`, as an existence statement. -/
theorem exists_act (Γ : Subgroup LinearSymmetry)
    (hiso : ∀ g : Γ, (∀ x y : LorentzSpace,
        lorentzForm (act g.val x) (act g.val y) = lorentzForm x y) ∧
      (∀ x : HyperbolicSpace, act g.val x.val ∈ hyperboloid)) :
    ∃ inst : MulAction Γ HyperbolicSpace,
      ∀ (g : Γ) (x : HyperbolicSpace), (inst.smul g x).val = act g.val x.val :=
  ⟨{ smul := fun g x => ⟨act g.val x.val, (hiso g).2 x⟩
     one_smul := fun x => Subtype.ext (by
       show act ((1 : Γ) : LinearSymmetry) x.val = x.val
       simp [act])
     mul_smul := fun g h x => Subtype.ext (act_mul' g.val h.val x.val) }, fun _ _ => rfl⟩

/-- **The package.** -/
theorem package (Γ : Subgroup LinearSymmetry)
    (hiso : ∀ g : Γ, (∀ x y : LorentzSpace,
        lorentzForm (act g.val x) (act g.val y) = lorentzForm x y) ∧
      (∀ x : HyperbolicSpace, act g.val x.val ∈ hyperboloid))
    (hfree : ∀ g : Γ, g ≠ 1 → ∀ x : HyperbolicSpace, act g.val x.val ≠ x.val)
    (hfin : ∀ C : ℝ, {g : Γ | ∀ i j, |g.val.val i j| ≤ C}.Finite)
    (K : Set HyperbolicSpace) (hK : IsCompact K)
    (hcov : ∀ x : HyperbolicSpace, ∃ g : Γ, ∃ y ∈ K, act g.val x.val = y.val)
    (T : Finset Γ) (hT : Subgroup.closure (T : Set Γ) = ⊤) :
    ∃ (M : Type) (t : TopologicalSpace M),
      letI : TopologicalSpace M := t
      T2Space M ∧ CompactSpace M ∧ IsHyperbolicQuotient M ∧
      (∃ q : HyperbolicSpace → M, Continuous q ∧ IsOpenMap q ∧ Function.Surjective q ∧
        ∀ x y : HyperbolicSpace, q x = q y ↔ ∃ g : Γ, act g.val x.val = y.val) ∧
      ∃ base : M, ∃ S : Finset (FundamentalGroup M base), S.card ≤ T.card ∧
        Subgroup.closure (S : Set (FundamentalGroup M base)) = ⊤ := by
  obtain ⟨inst, hinst⟩ := exists_act Γ hiso
  letI := inst
  have hval : ∀ (g : Γ) (x : HyperbolicSpace), (g • x).val = act g.val x.val := hinst
  haveI := hyp_locallyCompact
  haveI := hyp_simplyConnected
  haveI := hyp_pathConnected
  haveI : ContinuousConstSMul Γ HyperbolicSpace := ⟨fun g => by
    refine continuous_induced_rng.2 ?_
    have : (Subtype.val ∘ fun x : HyperbolicSpace => g • x) =
        fun x : HyperbolicSpace => (g.val : LinearSymmetry).val.mulVec x.val := by
      funext x; exact hval g x
    rw [this]
    exact Continuous.matrix_mulVec continuous_const continuous_subtype_val⟩
  haveI : ProperlyDiscontinuousSMul Γ HyperbolicSpace := by
    refine ⟨fun {K L} hK hL => ?_⟩
    obtain ⟨R, hR⟩ := exists_time_bound K hK
    obtain ⟨R', hR'⟩ := exists_time_bound L hL
    refine (hfin (10 * R * R')).subset ?_
    rintro g ⟨_, ⟨x, hxK, rfl⟩, hyL⟩
    intro i j
    have hb := entry_bound g.val (hiso g).1 (hiso g).2 x.val (g • x).val x.2 (g • x).2
      (hval g x).symm i j
    have hx0 := x.2.2
    have hy0 := (g • x).2.2
    have hxR := hR x hxK
    have hyR := hR' _ hyL
    have := mul_le_mul hxR hyR hy0.le (by linarith)
    calc |(g : LinearSymmetry).val i j| ≤ 10 * x.val 0 * (g • x).val 0 := hb
      _ = 10 * (x.val 0 * (g • x).val 0) := by ring
      _ ≤ 10 * (R * R') := by gcongr
      _ = 10 * R * R' := by ring
  haveI : IsCancelSMul Γ HyperbolicSpace := by
    refine isCancelSMul_iff_eq_one_of_smul_eq.mpr fun g x hgx => ?_
    by_contra hne
    exact hfree g hne x (by rw [← hval]; exact congrArg Subtype.val hgx)
  have hq : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel Γ HyperbolicSpace)) Γ :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  have hfib : ∀ x y : HyperbolicSpace,
      Quotient.mk (MulAction.orbitRel Γ HyperbolicSpace) x =
        Quotient.mk (MulAction.orbitRel Γ HyperbolicSpace) y ↔
      ∃ g : Γ, act g.val x.val = y.val := by
    intro x y
    rw [hq.apply_eq_iff_mem_orbit, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩
      have : g⁻¹ • x = y := by rw [← hg, inv_smul_smul]
      rw [← hval]; exact congrArg Subtype.val this
    · rintro ⟨g, hg⟩
      refine ⟨g⁻¹, ?_⟩
      have : g • x = y := Subtype.ext (by rw [hval]; exact hg)
      rw [← this, inv_smul_smul]
  obtain ⟨x₀⟩ := (inferInstance : Nonempty HyperbolicSpace)
  obtain ⟨S, hS, hSc⟩ := exists_pi1_generators hq
    (Quotient.mk (MulAction.orbitRel Γ HyperbolicSpace) x₀) T hT
  refine ⟨Quotient (MulAction.orbitRel Γ HyperbolicSpace), inferInstance, inferInstance, ?_, ?_,
    ⟨_, continuous_quotient_mk', isOpenMap_quotient_mk'_mul, Quotient.mk_surjective, hfib⟩,
    _, S, hS, hSc⟩
  · refine ⟨?_⟩
    have himg : (Quotient.mk (MulAction.orbitRel Γ HyperbolicSpace)) '' K = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      induction z using Quotient.inductionOn with
      | h x =>
        obtain ⟨g, y, hyK, hy⟩ := hcov x
        exact ⟨y, hyK, ((hfib x y).mpr ⟨g, hy⟩).symm⟩
    rw [← himg]
    exact hK.image continuous_quotient_mk'
  · refine ⟨Γ, hiso, ?_, Quotient.mk _, continuous_quotient_mk', isOpenMap_quotient_mk'_mul,
      Quotient.mk_surjective, hfib⟩
    intro x
    obtain ⟨U, hU, hUd⟩ := hq.disjoint x
    refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, ?_⟩
    intro g hg u hu v hv huv
    apply hg
    apply hUd g
    exact ⟨v, ⟨u, interior_subset hu, Subtype.ext (by rw [hval]; exact huv)⟩, interior_subset hv⟩

/-! ## §5. The reduction -/

theorem main : H1 → H2 → type_of% @OMA.S_opg_rank_vs_genus.main := by
  intro h1 h2 gap
  obtain ⟨Γ, hiso, hdet, hfree, hfin, ⟨K, hK, hcov⟩, T, hT, hbound⟩ := h2 gap
  obtain ⟨M, t, hT2, hcpt, hhyp, ⟨q, hqc, hqo, hqs, hqf⟩, base, S, hS, hSc⟩ :=
    package Γ hiso hfree hfin K hK hcov T hT
  letI := t
  obtain ⟨g₀, hg₀⟩ := h1 Γ hiso hdet hfree hfin M hT2 hcpt q hqc hqo hqs hqf
  refine ⟨M, t, hT2, hcpt, hhyp, ⟨g₀, hg₀⟩, base, S, hSc, fun g hg => ?_⟩
  have := hbound M q hqc hqo hqs hqf g hg
  omega

end OMA.R_opg_rank_vs_genus_R1
