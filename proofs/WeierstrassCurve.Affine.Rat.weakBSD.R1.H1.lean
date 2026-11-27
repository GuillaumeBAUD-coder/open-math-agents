import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1

/-!
The Mordell-Weil theorem over the rationals: for every elliptic curve `E` over `ℚ` the group
`E(ℚ)` is a finitely generated abelian group, i.e. `Module.Finite ℤ E.Point`.

This file is an ADAPTATION, not new mathematics. Everything between the two marker comments
below is taken from

  EllipticCurves, by Michael Stoll and the other contributors to that repository,
  https://github.com/MichaelStollBayreuth/EllipticCurves
  commit c4c72f486112ab61eca3b1a69135ec06789897f8

which is licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The source contains a complete, kernel-checked
proof of the Mordell-Weil theorem over number fields (`WeierstrassCurve.Affine.
fg_point_of_numberField`), building on the height machinery that the same author upstreamed to
Mathlib. Parts of the source are in turn marked there as adapted from the FLT project and from
the author's Heights and Chabauty-Coleman projects.

Source modules, concatenated in dependency order (one `section` per module):
  EllipticCurves/Mathlib/Basic.lean
  EllipticCurves/Mathlib/FractionalIdeal.lean
  EllipticCurves/Mathlib/SIntegers.lean
  EllipticCurves/Mathlib/SelmerGroup.lean
  EllipticCurves/VariableChange.lean
  EllipticCurves/WeakMordellWeil.lean
  EllipticCurves/MordellWeil.lean

Changes made to the source (mechanical, by a porting script; no proof was altered in content):
  * the seven modules are merged into one file; `module` / `public import` headers and
    `@[expose] public section` are replaced by a plain `section`;
  * linter `set_option` lines are removed;
  * `to_additive` attributes are removed (`(attr := simp)` is kept as `simp`), and
    `@[reducible] def` is written as `abbrev`;
  * the three `local notation`s of `WeakMordellWeil.lean` are expanded in place;
  * only the declarations that the final theorem depends on are kept (the source also
    develops explicit 2-descent, which is not needed here); nothing was added in their place;
  * the final theorem `OMA.solution` specialises the result to `ℚ`.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
except in compliance with the License. Unless required by applicable law or agreed to in
writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
specific language governing permissions and limitations under the License.
-/

/- ===== begin EllipticCurves/Mathlib/Basic.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-!
# Material for Mathlib

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero`, `.valuationOfNeZeroMod_mk` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section Group

variable {G H : Type*} [Group G] [Group H]

/-- A map `f` between groups with `f 1 = 1` that sends triples with product `1` to triples
with product `1` is a homomorphism. Useful when a map is naturally defined via a symmetric
ternary relation, like collinearity on a cubic curve. -/
def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group

/-- The preimage of a finite subgroup under an injective group homomorphism is finite. -/
lemma Subgroup.finite_comap_of_injective {f : G →* H} (hf : Function.Injective f)
    (S : Subgroup H) [Finite S] : Finite (S.comap f) :=
  .of_injective (fun x ↦ (⟨f x, x.2⟩ : S)) fun _ _ h ↦
    Subtype.ext <| hf <| congrArg Subtype.val h

/-- A product of finitely many finite subgroups is finite. -/
instance Subgroup.instFinitePi {ι : Type*} [Finite ι] {G : ι → Type*} [(i : ι) → Group (G i)]
    {S : (i : ι) → Subgroup (G i)} [(i : ι) → Finite (S i)] :
    Finite (Subgroup.pi Set.univ S) :=
  .of_injective (fun x i ↦ (⟨x.1 i, x.2 i (Set.mem_univ i)⟩ : S i)) fun _ _ h ↦
    Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun h i)

end Group

section Units

variable {α : Type*} [Monoid α]

lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · simpa using congrArg Units.val hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩

end Units

section modPow

/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def QuotientGroup.congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e <| by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u ^ n, ⟨_, rfl⟩, by simp⟩

namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  simp [IsUnit.exists_pow_eq_unit_iff]

lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  simp only [← mk_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp

@[simp]
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩

/-- A multiplicative equivalence `α ≃* β` induces one on `n`-th power classes of units. -/
def congr (e : α ≃* β) (n : ℕ) : Units.modPow α n ≃* Units.modPow β n :=
  congrRangePowMonoidHom (Units.mapEquiv e) n

/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def piEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ) :
    Units.modPow ((i : ι) → α i) n ≃* ((i : ι) → Units.modPow (α i) n) :=
  (congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

end Units.modPow

end modPow

section Ideal

end Ideal

section LinearAlgebra

end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma Valuation.eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma Valuation.map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial of positive degree with coefficients that are integral for the
valuation `ν` is itself integral. (This is a concrete form of the fact that valuation rings are
integrally closed.) -/
lemma Valuation.le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  by_contra! hlt
  have h := ν.map_eval_eq_of_one_lt hp hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_ofPred_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

lemma Set.unit_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) : S.unit K ≤ T.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

/-- Ideal-level divisibility characterization of `Associates.count`: the multiplicity of `v` in
`J` is at least `k` iff `v ^ k` divides `J`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff_le {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/-- Divisibility characterization of `Associates.count` for a height one prime: the `v`-adic
valuation of `x` is at least `k` iff `x ∈ v ^ k`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- If the valuation of a unit `u` is the `n`-th power of the valuation of a unit `z`, then the
`v`-adic order of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero (v : HeightOneSpectrum R)
    {n : ℕ} {u z : Kˣ} (h : v.valuation K (u : K) = v.valuation K (z : K) ^ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  have hu : v.valuationOfNeZero u = v.valuationOfNeZero z ^ n := by
    rw [valuationOfNeZero_eq_iff]
    push_cast
    rw [valuationOfNeZero_eq, h]
  exact ⟨Multiplicative.toAdd (v.valuationOfNeZero z), by rw [hu]; simp [toAdd_pow]⟩

/-- The image of the class of a unit `u` under the `v`-adic valuation mod `n` is the class in
`ZMod n` of the `v`-adic order of `u`. This is the computation rule that
`Mathlib.RingTheory.DedekindDomain.SelmerGroup` lacks; it holds by definition, but the
`Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod` blocks unfolding it by hand. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk (v : HeightOneSpectrum R)
    (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) =
      Multiplicative.ofAdd ((Multiplicative.toAdd (v.valuationOfNeZero u) : ℤ) : ZMod n) :=
  rfl

/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [valuationOfNeZeroMod_mk, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]

variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]

/-- The primes of `B` lying above a set `S` of primes of `R`. -/
def IsDedekindDomain.HeightOneSpectrum.primesAbove (S : Set (HeightOneSpectrum R)) :
    Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.

-- as for `primesAbove_mono`, the `IsDedekindDomain` instances are needed for the statement

/-- The prime of `R` lying below a prime `w` of an integral extension `B`. -/
def IsDedekindDomain.HeightOneSpectrum.below [Algebra.IsIntegral R B] (w : HeightOneSpectrum B) :
    HeightOneSpectrum R where
  asIdeal := w.asIdeal.under R
  isPrime := Ideal.IsPrime.under R w.asIdeal
  ne_bot := Ideal.IsIntegral.comap_ne_bot R w.ne_bot

instance IsDedekindDomain.HeightOneSpectrum.instLiesOverBelow [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.below R).asIdeal :=
  Ideal.over_under ..

lemma IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff [Algebra.IsIntegral R B]
    (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.below R ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨w.below R, hw, rfl⟩⟩
  rwa [show w.below R = v from HeightOneSpectrum.ext hva.symm]

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`: each fiber
injects into `Ideal.primesOver`, which is finite for a Dedekind extension. -/
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_finite [Algebra.IsIntegral R B]
    [Module.IsTorsionFree R B] {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w ⟨v, hv, hva⟩ ↦ Set.mem_biUnion hv ⟨w.isPrime, ⟨hva⟩⟩
  refine (hS.biUnion fun v _ ↦ ?_).subset hsub
  have := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)

/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def IsDedekindDomain.selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Units.modPow L n) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only

namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable {A}

end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them

variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

/-- For monic `g`, the resultant does not depend on the size parameter used for the second
argument, as long as it is at least its degree. -/
lemma Monic.resultant_congr_right (hg : g.Monic) {p : R[X]} {n₁ n₂ : ℕ}
    (h₁ : p.natDegree ≤ n₁) (h₂ : n₁ ≤ n₂) :
    g.resultant p g.natDegree n₂ = g.resultant p g.natDegree n₁ := by
  rw [← Nat.add_sub_cancel' h₂, resultant_add_right_deg _ _ _ _ _ h₁, hg.coeff_natDegree,
    one_pow, one_mul]

private lemma succ_mul_div_two {n : ℕ} (hn : 0 < n) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
  rw [mul_comm m] at hk
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring, hk]
  lia

private lemma resultant_X_sub_C_add_mul_derivative (hdeg : 0 < g.natDegree) (x : R) :
    (X - C x).resultant (g + (X - C x) * derivative g) 1 g.natDegree = g.eval x := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [resultant_add_mul_right _ _ _ _ _ hd' (natDegree_X_sub_C_le x),
    resultant_X_sub_C_left _ _ _ le_rfl]

private lemma resultant_add_mul_derivative [Nontrivial R] (hg : g.Monic)
    (hdeg : 0 < g.natDegree) (x : R) :
    g.resultant (g + (X - C x) * derivative g) g.natDegree g.natDegree =
      (-1) ^ g.natDegree * g.eval x *
        g.resultant (derivative g) g.natDegree (g.natDegree - 1) := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [show g + (X - C x) * derivative g = (X - C x) * derivative g + g * 1 by ring,
    resultant_add_mul_right _ _ _ _ _ (by simp) le_rfl,
    hg.resultant_congr_right natDegree_mul_le (by rw [natDegree_X_sub_C]; lia),
    resultant_mul_right g (X - C x) (derivative g) g.natDegree le_rfl, natDegree_X_sub_C,
    resultant_X_sub_C_right _ _ _ le_rfl,
    ← hg.resultant_congr_right (n₂ := g.natDegree - 1) le_rfl (natDegree_derivative_le g)]

/-- The discriminant of `(X - C x) * g` for monic `g` of positive degree is
`g.discr * g.eval x ^ 2`. -/
theorem discr_X_sub_C_mul (hg : g.Monic) (hdeg : 0 < g.natDegree) (x : R) :
    ((X - C x) * g).discr = g.discr * g.eval x ^ 2 := by
  nontriviality R
  have hmon : ((X - C x) * g).Monic := (monic_X_sub_C x).mul hg
  have hN : ((X - C x) * g).natDegree = g.natDegree + 1 := by
    rw [(monic_X_sub_C x).natDegree_mul hg, natDegree_X_sub_C, add_comm]
  have hder : derivative ((X - C x) * g) = g + (X - C x) * derivative g := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hDle : (g + (X - C x) * derivative g).natDegree ≤ g.natDegree :=
    (natDegree_add_le _ _).trans (max_le le_rfl (natDegree_mul_le.trans
      (by rw [natDegree_X_sub_C]; have := natDegree_derivative_le g; lia)))
  -- compare the splitting of `Res((X - C x) * g, ((X - C x) * g)')` along the product with
  -- its expression through the discriminant
  have hsplit := resultant_mul_left (X - C x) g (g + (X - C x) * derivative g) g.natDegree hDle
  rw [natDegree_X_sub_C, add_comm 1 g.natDegree] at hsplit
  have hres := resultant_deriv (f := (X - C x) * g)
    (by rw [← natDegree_pos_iff_degree_pos, hN]; lia)
  rw [hN, hder, hmon.leadingCoeff, mul_one, Nat.add_sub_cancel, succ_mul_div_two hdeg,
    pow_add] at hres
  have hres2 := resultant_deriv (f := g) (natDegree_pos_iff_degree_pos.mp hdeg)
  rw [hg.leadingCoeff, mul_one] at hres2
  have hmain := hres.symm.trans hsplit
  rw [resultant_X_sub_C_add_mul_derivative hdeg x, resultant_add_mul_derivative hg hdeg x,
    hres2] at hmain
  -- now peel off the signs, which cancel
  have hpow (k : ℕ) : ((-1 : R) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  set s : R := (-1) ^ (g.natDegree * (g.natDegree - 1) / 2)
  set t : R := (-1) ^ g.natDegree
  have hs : s * s = 1 := hpow _
  have ht : t * t = 1 := hpow _
  calc ((X - C x) * g).discr
      = s * t * (s * t * ((X - C x) * g).discr) := by
        rw [← mul_assoc, mul_mul_mul_comm, hs, ht, one_mul, one_mul]
    _ = s * t * (g.eval x * (t * g.eval x * (s * g.discr))) := by rw [hmain]
    _ = s * s * (t * t) * (g.discr * g.eval x ^ 2) := by ring
    _ = g.discr * g.eval x ^ 2 := by rw [hs, ht, one_mul, one_mul]

section

variable [Nontrivial R] {q : R[X]} {n : ℕ}

lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]

lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd

end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/

end Sylvester

end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)

lemma exists_degree_lt_mk_eq [Nontrivial R] (hg : g.Monic) (a : AdjoinRoot g) :
    ∃ p, p.degree < g.degree ∧ a = mk g p := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  exact ⟨q %ₘ g, degree_modByMonic_lt q hg, (mk_modByMonic hg q).symm⟩

lemma mk_eq_mk_iff_of_degree_lt [Nontrivial R] (hg : g.Monic) {p q : R[X]}
    (hp : p.degree < g.degree) (hq : q.degree < g.degree) :
    mk g p = mk g q ↔ p = q :=
  ⟨fun h ↦ sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg (mk_eq_mk.mp h) <|
    (degree_sub_le p q).trans_lt (max_lt hp hq), fun h ↦ h ▸ rfl⟩

section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)

end Map

end AdjoinRoot

/-! ### The norm on a product algebra -/

section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

Note that this is *not* defined via `normalizedFactors` (which would require `DecidableEq K`);
membership in `normalizedFactors f` is characterized by `Factors.mem_normalizedFactors_iff`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd

/-- Membership in `normalizedFactors` (with its normalization from `DecidableEq K`) is
equivalent to being a monic irreducible factor. -/
lemma mem_normalizedFactors_iff [DecidableEq K] (hf : f ≠ 0) {p : K[X]} :
    p ∈ normalizedFactors f ↔ p.Monic ∧ Irreducible p ∧ p ∣ f := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hf]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂ ▸ monic_normalize h₁.ne_zero, h₁, h₃⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁.normalize_eq_self, h₃⟩⟩

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (mem_normalizedFactors_iff hf).mpr hp).injective

lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
        Ideal.span_singleton_eq_span_singleton.mp h

lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

lemma associated_prod [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  -- identify `f.Factors` with the subtype of the `Finset` of normalized factors
  have hprod : ∏ p : f.Factors, (p : K[X]) =
      ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ by
        rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hf]) _ _
      fun x ↦ by rw [Equiv.subtypeEquivRight_apply]
  have hcoe : ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) =
      ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hprod, hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']
  exact prod_normalizedFactors hf

lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hf hsq)).symm

end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite

lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]

open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X]/(f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h

/-- **Chinese Remainder Theorem** for `AdjoinRoot`: for `f` nonzero and squarefree,
`K[X]/(f)` is the product of the fields `K[X]/(p)` over the monic irreducible factors `p`
of `f`. -/
noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hf
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

/-- The projection of `K[X]/(f)` onto the field factor `K[X]/(p)`. -/
noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hf hsq).toRingEquiv.toRingHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  rfl

/-- The `n`-th power classes of units of `K[X]/(f)` are the product of those of its
field factors. -/
noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    Units.modPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) n) :=
  (Units.modPow.congr (equivPiFactors hf hsq).toMulEquiv n).trans <|
    Units.modPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors. -/
@[simp]
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (ha.unit : Units.modPow (AdjoinRoot f) n) p =
      ((ha.map (projFactor hf hsq p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) n) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, Units.modPow.congr,
    QuotientGroup.congrRangePowMonoidHom, QuotientGroup.congr_mk, Units.modPow.piEquiv,
    QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]
  exact congrArg _ (Units.ext rfl)

end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The integral closure of `𝓞 K` in an extension `L` of `K` is the integral closure of `ℤ`
in `L`. -/
theorem isIntegralClosure_int_integralClosure :
    IsIntegralClosure (integralClosure (𝓞 K) L) ℤ L := by
  refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩⟩
  · exact ⟨⟨x, IsIntegral.tower_top (A := 𝓞 K) hx⟩, rfl⟩
  · have hyint : IsIntegral (𝓞 K) (y : L) := y.2
    have := isIntegral_trans (R := ℤ) (y : L) hyint
    rwa [show (y : L) = x from hy] at this

variable [NumberField K] [FiniteDimensional K L]

/-- The **class number theorem** for the integral closure of `𝓞 K` in a finite extension `L`
of the number field `K`: its class group is finite. -/
theorem NumberField.finite_classGroup_integralClosure :
    Finite (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have := isIntegralClosure_int_integralClosure K L
  have := ClassGroup.fintypeOfAdmissibleOfFinite ℚ L
    (S := integralClosure (𝓞 K) L) AbsoluteValue.absIsAdmissible
  exact Finite.of_fintype _

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `𝓞 K` in a
finite extension `L` of the number field `K`: its unit group is finitely generated. -/
theorem NumberField.fg_units_integralClosure :
    Group.FG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Group.fg_of_surjective
    (f := (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).toMonoidHom)
    (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).surjective

end NumberField

/-!
### Discriminants, class numbers, and unit ranks of cubic fields

The discriminant of a number field is the discriminant of any power basis with integral
generator divided by a square; consequently a cubic field whose power-basis discriminant is
at most `49` in absolute value has trivial class group (by the Minkowski bound), and the sign
of the power-basis discriminant determines the signature and hence, by Dirichlet's unit
theorem, the unit rank (`1` if negative, `2` if positive).
-/

section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]

end Discriminant

end
/- ===== end EllipticCurves/Mathlib/Basic.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/FractionalIdeal.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-!
# The group of fractional ideals is free abelian on the primes

Let `R` be a Dedekind domain with fraction field `K`. The nonzero fractional ideals of `R` form a
group `(FractionalIdeal R⁰ K)ˣ` (every nonzero fractional ideal is invertible), and unique
factorization says this group is free abelian on the height one primes. Mathlib has all the
valuation bookkeeping (`IsDedekindDomain.HeightOneSpectrum.count` and the factorization lemmas in
`Mathlib.RingTheory.DedekindDomain.Factorization`) but does not package the isomorphism itself;
this file does.

## Main definitions and results

* `FractionalIdeal.factorization`: the isomorphism
  `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`, sending a fractional
  ideal to its tuple of valuations.
* `FractionalIdeal.exists_pow_eq`: **`n`-th roots** — a fractional ideal all of whose valuations
  are divisible by `n` is an `n`-th power. This is the key input to the fundamental exact sequence
  of the Selmer group.
* `FractionalIdeal.prod_count`, `count_injective`: a nonzero fractional ideal is the product of
  `v ^ (count v)` over the primes, and is determined by its valuations.

This is general material, candidate for upstreaming to Mathlib.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors Classical

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

/-!
### The kernel of the principal-ideal map

The principal fractional ideal `(x)` is trivial exactly when `x` comes from a unit of `R`. This
identifies `ker toPrincipalIdeal` with the units of `R`, the left end of the ideal class exact
sequence. This part needs `R` to be a domain only.
-/

section PrincipalIdeal

variable [IsDomain R]

lemma spanSingleton_eq_one_iff {x : K} (hx : x ≠ 0) :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
  constructor
  · intro h
    have hinv : spanSingleton R⁰ x⁻¹ = 1 := by rw [← spanSingleton_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (mem_one_iff R⁰).mp (h ▸ mem_spanSingleton_self R⁰ x)
    obtain ⟨b, hb⟩ := (mem_one_iff R⁰).mp (hinv ▸ mem_spanSingleton_self R⁰ x⁻¹)
    have hab : a * b = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ha, hb, mul_inv_cancel₀ hx, map_one])
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr a.isUnit, coeIdeal_top]

/-- `toPrincipalIdeal x = 1` exactly when `x` is a unit of `R`: the kernel of the principal-ideal
map is the image of `Rˣ`. -/
lemma toPrincipalIdeal_eq_one_iff (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff u.ne_zero]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- `ClassGroup.mk I = 1` exactly when the unit fractional ideal `I` is principal, with the
generator provided as a unit of `K`. Variant of `ClassGroup.mk_eq_one_iff` avoiding
`Submodule.IsPrincipal`. -/
lemma _root_.ClassGroup.mk_eq_one_iff_exists {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := hI.principal
    have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
      apply Subtype.coe_injective
      simp only [val_eq_coe, hx, coe_spanSingleton]
    have hx0 : x ≠ 0 := fun h ↦ Units.ne_zero I (by rw [hx', h, spanSingleton_zero])
    exact ⟨Units.mk0 x hx0, by rw [← Units.val_inj, coe_toPrincipalIdeal, hx']; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

end PrincipalIdeal

variable [IsDedekindDomain R]

/-- A nonzero fractional ideal is the product `∏ v ^ (count v)` over the height one primes. -/
theorem prod_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v I = I := by
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  simp_rw [fun v ↦ count_well_defined K v hI haJ]
  exact finprod_heightOneSpectrum_factorization hI haJ

/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := rfl

/-- The finitely-supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) := rfl

/-- The unit fractional ideal `∏ v ^ (g v)`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod (fun v e ↦ unitOfPrime v ^ e)

lemma coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = g.prod (fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

lemma count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- A unit fractional ideal is determined by its valuations. -/
lemma count_injective {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  apply Units.ext
  rw [← prod_count (Units.ne_zero I), ← prod_count (Units.ne_zero J)]
  exact finprod_congr fun v ↦ by rw [h v]

/-- The `v`-adic valuation of `x : K` is `exp (- count v (x))`: the `count` of the principal
fractional ideal generated by `x` recovers the adic valuation. -/
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (- count K v (spanSingleton R⁰ x)) := by
  have key (r : R) (hr : r ≠ 0) : v.valuation K (algebraMap R K r) =
      WithZero.exp (- count K v (spanSingleton R⁰ (algebraMap R K r))) := by
    rw [valuation_of_algebraMap, intValuation_apply, v.intValuationDef_if_neg hr,
      ← coeIdeal_span_singleton, count_coe K v (by simpa using hr)]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hsa : spanSingleton R⁰ (algebraMap R K a) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hsb : spanSingleton R⁰ (algebraMap R K (b:R)) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hcount : count K v (spanSingleton R⁰ (algebraMap R K a / algebraMap R K (b:R))) =
      count K v (spanSingleton R⁰ (algebraMap R K a)) -
        count K v (spanSingleton R⁰ (algebraMap R K (b:R))) := by
    rw [← spanSingleton_div_spanSingleton, div_eq_mul_inv, count_mul K v hsa (inv_ne_zero hsb),
      count_inv, sub_eq_add_neg]
  rw [map_div₀, key a ha0, key (b:R) hb0, hcount, div_eq_mul_inv, ← WithZero.exp_neg,
    ← WithZero.exp_add]
  congr 1
  ring

/-- The `v`-adic order of a unit `x : Kˣ` is `- count v (x)`: the additive form of
`valuation_eq_exp_neg_count`. -/
theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      - count K v (spanSingleton R⁰ (x : K)) := by
  have h : (v.valuationOfNeZero x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (- count K v (spanSingleton R⁰ (x : K))) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, valuation_eq_exp_neg_count v x.ne_zero]
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at h
  rw [h, toAdd_ofAdd]

/-!
### The `n`-th root as a homomorphism

On the subgroup of fractional ideals all of whose valuations are divisible by `n`, the `n`-th
root is a genuine group homomorphism (not merely an existence statement): dividing every
valuation by `n` is additive there.
-/

section NthRoot

variable (R K)

/-- The subgroup of fractional ideals whose valuations are all divisible by `n`. -/
def nDivisible (n : ℕ) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)}
  one_mem' v := by rw [Units.val_one, count_one]; exact dvd_zero _
  mul_mem' {I J} hI hJ v := by
    rw [Units.val_mul, count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    exact dvd_add (hI v) (hJ v)
  inv_mem' {I} hI v := by
    rw [Units.val_inv_eq_inv_val, count_inv]; exact (hI v).neg_right

/-- The `n`-th root ideal of `I`: its valuations divided by `n`. -/
noncomputable def nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) : (FractionalIdeal R⁰ K)ˣ :=
  ofFinsupp (Finsupp.mapRange (· / (n:ℤ)) (by simp) (toFinsupp I))

lemma count_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    count K v (nthRootFun R K n I : FractionalIdeal R⁰ K) =
      count K v (I : FractionalIdeal R⁰ K) / n := by
  rw [nthRootFun, count_ofFinsupp, Finsupp.mapRange_apply, toFinsupp_apply]

/-- The `n`-th root as a group homomorphism on the `n`-divisible subgroup. -/
noncomputable def nthRootHom (n : ℕ) : nDivisible R K n →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ)
  map_one' := count_injective fun v ↦ by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := count_injective fun v ↦ by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _), Int.add_ediv_of_dvd_left (I.2 v)]

variable {R K} in
@[simp] lemma nthRootHom_apply (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I = nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ) := rfl

/-- The `n`-th root homomorphism is a genuine `n`-th root. -/
lemma nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    (nthRootHom R K n I) ^ n = (I : (FractionalIdeal R⁰ K)ˣ) := by
  apply count_injective
  intro v
  rw [Units.val_pow_eq_pow_val, count_pow, nthRootHom_apply,
    count_nthRootFun, Int.mul_ediv_cancel' (I.2 v)]

end NthRoot

/-!
### The `n`-th-root class map and its kernel

For a unit `u : Kˣ` whose principal ideal has all valuations divisible by `n`, the `n`-th root
`𝔞` of `(u)` has a well-defined class in `ClassGroup R`. The class vanishes exactly when `u` is
a unit of `R` times an `n`-th power in `Kˣ` — the exactness of the fundamental sequence
`1 → Rˣ/(Rˣ)ⁿ → K(∅,n) → Cl(R)[n]` at the middle spot, stated here before any quotients are
taken.
-/

section NthRootClass

variable (R K)

/-- The units of `K` whose principal fractional ideal has all valuations divisible by `n`. -/
def unitsNDivisible (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal R K) (nDivisible R K n)

/-- The restriction of `toPrincipalIdeal` to `unitsNDivisible`, into the `n`-divisible
subgroup. -/
noncomputable def unitsNDivisibleToNDivisible (n : ℕ) :
    unitsNDivisible R K n →* nDivisible R K n :=
  ((toPrincipalIdeal R K).comp (unitsNDivisible R K n).subtype).codRestrict _ (fun x ↦ x.2)

@[simp] lemma coe_unitsNDivisibleToNDivisible (n : ℕ) (u : unitsNDivisible R K n) :
    (unitsNDivisibleToNDivisible R K n u : (FractionalIdeal R⁰ K)ˣ) =
      toPrincipalIdeal R K (u : Kˣ) := rfl

/-- The `n`-th-root class map: the class of the `n`-th root of the principal ideal `(u)`. -/
noncomputable def nthRootClass (n : ℕ) : unitsNDivisible R K n →* ClassGroup R :=
  (ClassGroup.mk K).comp ((nthRootHom R K n).comp (unitsNDivisibleToNDivisible R K n))

@[simp]
lemma nthRootClass_apply (n : ℕ) (u : unitsNDivisible R K n) :
    nthRootClass R K n u =
      ClassGroup.mk K (nthRootHom R K n (unitsNDivisibleToNDivisible R K n u)) :=
  rfl

/-- **Exactness of the fundamental sequence at the middle spot**: the `n`-th-root class of `u`
vanishes exactly when `u` is a unit of `R` times an `n`-th power. -/
lemma nthRootClass_eq_one_iff {n : ℕ} (hn : n ≠ 0) (u : unitsNDivisible R K n) :
    nthRootClass R K n u = 1 ↔
      ∃ (a : Rˣ) (w : Kˣ), Units.map (algebraMap R K : R →* K) a * w ^ n = (u : Kˣ) := by
  rw [nthRootClass_apply, ClassGroup.mk_eq_one_iff_exists]
  constructor
  · intro ⟨w, hw⟩
    -- the `n`-th power of the found generator `w` generates `(u)`, so `u / wⁿ` is a unit of `R`
    have hpow : toPrincipalIdeal R K (w ^ n) = toPrincipalIdeal R K (u : Kˣ) := by
      rw [map_pow, hw, nthRootHom_pow, coe_unitsNDivisibleToNDivisible]
    have h1 : toPrincipalIdeal R K ((u : Kˣ) * (w ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpow, mul_inv_cancel]
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp h1
    exact ⟨a, w, by rw [ha]; group⟩
  · intro ⟨a, w, hw⟩
    -- `w` generates the `n`-th root: its valuations are `count (u) / n`
    refine ⟨w, count_injective fun v ↦ ?_⟩
    have hcu : count K v ((toPrincipalIdeal R K (u : Kˣ) : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) = n * count K v
          ((toPrincipalIdeal R K w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) := by
      rw [← hw, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        count_mul K v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)), count_pow,
        (toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, Units.val_one, count_one, zero_add]
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcu,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hn)]

end NthRootClass

end FractionalIdeal

end
/- ===== end EllipticCurves/Mathlib/FractionalIdeal.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/SIntegers.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-!
# The ring of `S`-integers is a Dedekind domain

Let `R` be a Dedekind domain with fraction field `K` and let `S` be a set of primes of `R`.
`Mathlib.RingTheory.DedekindDomain.SInteger` defines the subalgebra `Set.integer S K` of
`S`-integers, `𝒪_S = {x : K | ∀ v ∉ S, v x ≤ 1} = ⋂_{v ∉ S} R_v`, but proves nothing about its
ring structure. This file develops it. The goal is:

* `𝒪_S` is a Dedekind domain with fraction field `K`;
* its height one primes are exactly the `v ∉ S`, via `v ↦ 𝒪_S ∩ v`;
* its class group is `Cl(R)` modulo the subgroup generated by the classes of the `v ∈ S`.

These are the facts needed in `EllipticCurves.Mathlib.SelmerGroup` to construct the right-hand
map of the fundamental exact sequence, and they reduce the whole exact sequence to the case
`S = ∅`, where the map to the class group is simply `x ↦ [𝔞]` for the ideal with `𝔞 ^ n = (x)`.
They are of independent interest, and Mathlib has none of them.

## A warning

`𝒪_S` is **not** in general a localization of `R`. Localizing at
`M = {r : R | r ≠ 0 ∧ ∀ v ∉ S, v r = 1}` gives a subring of `𝒪_S`, but it can be strictly
smaller: if `Cl(R) ≅ ℤ` is generated by the class of a single prime `v` and `S = {v}`, then
`M = Rˣ`, because no power `v ^ k` with `k ≠ 0` is principal; yet `𝒪_S ⊋ R`, since for any
integral ideal `𝔞` in the class of `v` the fractional ideal `𝔞 * v⁻¹` is principal, generated by
some `x` with `v x < 1` and `w x ≤ 1` for `w ≠ v`. So `𝒪_S` has to be handled as a general
overring of `R`, not as a ring of fractions.

The classical statement in the appropriate generality is that *every* overring of a Dedekind
domain (i.e. every ring between `R` and `K`) is a Dedekind domain. The proofs below use the
`S`-integer description directly (via the denominator-ideal argument in `map_comap_eq`), which
keeps them short; upstreaming to Mathlib might instead aim for the general overring statement.

## Implementation notes

`Set.integer S K` is a `Subalgebra R K`. Since it sits between `R` and `K`, the instance
`Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra` already makes `K` its fraction
field, so `HeightOneSpectrum`-style valuation theory applies as soon as we know it is a Dedekind
domain.

## Main statements

* `IsDedekindDomain.SInteger.isIntegrallyClosed`: `𝒪_S` is integrally closed.
* `IsDedekindDomain.SInteger.isDedekindDomain`: `𝒪_S` is a Dedekind domain.
* `IsDedekindDomain.SInteger.heightOneSpectrumEquiv`: the primes of `𝒪_S` are the `v ∉ S`, and
  `valuation_heightOneSpectrumEquiv`: the valuations restrict those of `R`.
* `IsDedekindDomain.SInteger.extendedHom_surjective` and `finite_classGroup`: extension of ideals
  `Cl(R) → Cl(𝒪_S)` is surjective, so `Cl(𝒪_S)` is finite whenever `Cl(R)` is.
* `IsDedekindDomain.SInteger.classGroupEquiv`: `Cl(𝒪_S) ≃* Cl(R) ⧸ ⟨[v] : v ∈ S⟩`.

-/

open IsDedekindDomain FractionalIdeal

open scoped nonZeroDivisors Classical

section DenomIdeal

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]

/-- The denominator ideal of `x : K`: the colon ideal `(R : x) = {r : R | r • x ∈ R}`. -/
abbrev IsDedekindDomain.SInteger.denomIdeal (x : K) : Ideal R := (1 : Submodule R K).colon {x}

lemma IsDedekindDomain.SInteger.mem_denomIdeal_iff {x : K} {r : R} :
    r ∈ denomIdeal K x ↔ ∃ s : R, algebraMap R K r * x = algebraMap R K s := by
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
  exact exists_congr fun s ↦ eq_comm

end DenomIdeal

namespace IsDedekindDomain.SInteger

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

lemma toSubring_le_valuationSubring {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (S.integer K).toSubring ≤ (v.valuation K).valuationSubring.toSubring :=
  fun _ hx ↦ hx v hv

/-- The fraction field of the ring of `S`-integers is `K`. This is already an instance, as
`Set.integer S K` is a subalgebra of `K` over `R`. -/
example : IsFractionRing (S.integer K) K := inferInstance

/-- The ring of `S`-integers is integrally closed: it is an intersection of valuation subrings
of `K`, each of which is integrally closed in `K`. -/
instance isIntegrallyClosed : IsIntegrallyClosed (S.integer K) := by
  rw [isIntegrallyClosed_iff K]
  intro x hx
  refine ⟨⟨x, fun v hv ↦ ?_⟩, rfl⟩
  -- work inside the valuation subring `V` of `v`, which contains `𝒪_S`
  set V := (v.valuation K).valuationSubring with hV
  let _ : Algebra (S.integer K) V :=
    (Subring.inclusion (toSubring_le_valuationSubring K S hv)).toAlgebra
  have _ : IsScalarTower (S.integer K) V K := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp inferInstance (hx.tower_top (A := V))
  rw [← hy]
  exact y.property

/-!
### Primes in `S` become the unit ideal

For `v ∈ S` the inverse `v⁻¹` of `v` as a fractional ideal consists of `S`-integers, because an
element `y` with `y * v ⊆ R` can have a pole only at `v`. As `v * v⁻¹ = 1`, the extension of `v`
to `𝒪_S` is therefore the unit ideal. This is the one place where the Dedekind property of `R`
enters, and it is what makes `𝒪_S` bigger than `R`.
-/

/-- A height one prime is not contained in any other one. -/
lemma exists_mem_notMem {v w : HeightOneSpectrum R} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)

/-- For `v ∈ S`, the fractional ideal `v⁻¹` consists of `S`-integers. -/
lemma mem_integer_of_mem_inv {v : HeightOneSpectrum R} (hv : v ∈ S) {y : K}
    (hy : y ∈ (v.asIdeal : FractionalIdeal R⁰ K)⁻¹) : y ∈ S.integer K := by
  intro w hw
  obtain ⟨a, ha, haw⟩ := exists_mem_notMem (show w ≠ v by rintro rfl; exact hw hv)
  have h1 : y * algebraMap R K a ∈ (1 : FractionalIdeal R⁰ K) :=
    (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)).mp hy _
      (FractionalIdeal.mem_coeIdeal_of_mem R⁰ ha)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h1
  have h2 : w.valuation K (y * algebraMap R K a) ≤ 1 := hr ▸ w.valuation_le_one r
  rwa [map_mul, w.valuation_eq_one_iff_notMem.mpr haw, mul_one] at h2

/-- For `v ∈ S`, the extension of `v` to the ring of `S`-integers is the unit ideal. -/
lemma map_asIdeal_eq_top {v : HeightOneSpectrum R} (hv : v ∈ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal = ⊤ := by
  set A := S.integer K with hA
  set M := Ideal.map (algebraMap R A) v.asIdeal with hM
  -- `1 ∈ v * v⁻¹`, as a submodule of `K`
  have h1 : (1 : K) ∈
      (v.asIdeal : FractionalIdeal R⁰ K) * (v.asIdeal : FractionalIdeal R⁰ K)⁻¹ := by
    rw [FractionalIdeal.coe_ideal_mul_inv _ v.ne_bot]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at h1
  -- every element of the product that is an `S`-integer lies in `M`
  refine Ideal.eq_top_iff_one M |>.mpr ?_
  suffices H : ∀ x ∈ (v.asIdeal : FractionalIdeal R⁰ K) * (v.asIdeal : FractionalIdeal R⁰ K)⁻¹,
      ∃ hx : x ∈ A, (⟨x, hx⟩ : A) ∈ M by
    obtain ⟨hx, hx'⟩ := H 1 (by rwa [← FractionalIdeal.coe_mul, FractionalIdeal.mem_coe] at h1)
    exact (show (⟨1, hx⟩ : A) = 1 from rfl) ▸ hx'
  intro x hx
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hx
  refine Submodule.mul_induction_on hx (fun a ha y hy ↦ ?_) (fun x y hx hy ↦ ?_)
  · obtain ⟨a, ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp
      ((FractionalIdeal.mem_coe (I := (v.asIdeal : FractionalIdeal R⁰ K))).mpr ha)
    have hyA : y ∈ A := mem_integer_of_mem_inv K S hv
      ((FractionalIdeal.mem_coe (I := (v.asIdeal : FractionalIdeal R⁰ K)⁻¹)).mpr hy)
    have haA : algebraMap R K a ∈ A := A.algebraMap_mem a
    refine ⟨mul_mem haA hyA, ?_⟩
    have he : (⟨algebraMap R K a * y, mul_mem haA hyA⟩ : A) = algebraMap R A a * ⟨y, hyA⟩ := rfl
    rw [he]
    exact Ideal.mul_mem_right _ M (Ideal.mem_map_of_mem _ ha')
  · obtain ⟨hx, hx'⟩ := hx
    obtain ⟨hy, hy'⟩ := hy
    exact ⟨add_mem hx hy, add_mem hx' hy'⟩

/-!
### Ideals of `𝒪_S` are extended from `R`

Let `I` be an ideal of `𝒪_S` and `J = I ∩ R` its contraction. For `x ∈ I` the denominator ideal
`𝔡 x = {r : R | r * x ∈ R}` is divisible only by primes in `S`, because `x` is `w`-integral for
`w ∉ S`. Hence `𝔡 x * 𝒪_S = ⊤` by `map_asIdeal_eq_top`, so `1 = ∑ dᵢ cᵢ` with `dᵢ ∈ 𝔡 x` and
`cᵢ ∈ 𝒪_S`, and `x = ∑ (dᵢ * x) * cᵢ` exhibits `x` as an element of `J * 𝒪_S`, since
`dᵢ * x ∈ R ∩ I = J`.

Noetherianity is immediate from this: `J` is finitely generated as `R` is Noetherian, hence so
is its extension `I`.
-/

/-- The denominator ideal of an `S`-integer is not contained in any prime off `S`: at such a
prime `x` is integral, so it has a denominator away from the prime. -/
lemma denomIdeal_not_le {x : K} (hx : x ∈ S.integer K) {w : HeightOneSpectrum R} (hw : w ∉ S) :
    ¬ denomIdeal K x ≤ w.asIdeal := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w x (hx w hw)
  refine fun hle ↦ d.property (hle ?_)
  rw [mem_denomIdeal_iff]
  exact ⟨n, by rw [mul_comm]; exact hnd⟩

/-- The denominator ideal of any `x : K` is nonzero: a common denominator lies in it. -/
lemma denomIdeal_ne_bot (x : K) : denomIdeal K x ≠ (⊥ : Ideal R) := by
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj R⁰ x
  refine fun h0 ↦ nonZeroDivisors.ne_zero hb ?_
  have : b ∈ denomIdeal K x := by rw [mem_denomIdeal_iff]; exact ⟨a, by rw [mul_comm]; exact hab⟩
  simpa [h0] using this

/-- The denominator ideal of an `S`-integer extends to the unit ideal of `𝒪_S`: all its prime
factors lie in `S`, and each of those extends to the unit ideal by `map_asIdeal_eq_top`. -/
lemma map_denomIdeal_eq_top {x : K} (hx : x ∈ S.integer K) :
    Ideal.map (algebraMap R (S.integer K)) (denomIdeal K x) = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have h𝔭le : denomIdeal K x ≤ M.comap (algebraMap R (S.integer K)) :=
    (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
  have h𝔭ne : M.comap (algebraMap R (S.integer K)) ≠ ⊥ :=
    fun h0 ↦ denomIdeal_ne_bot K x (le_bot_iff.mp (h0 ▸ h𝔭le))
  have hprime : (M.comap (algebraMap R (S.integer K))).IsPrime := hM.isPrime.comap _
  have hwS : (⟨_, hprime, h𝔭ne⟩ : HeightOneSpectrum R) ∈ S :=
    by_contra fun hwn ↦ denomIdeal_not_le K S hx hwn h𝔭le
  have htop := map_asIdeal_eq_top K S hwS
  exact hM.ne_top (top_le_iff.mp (htop.ge.trans Ideal.map_comap_le))

/-- **Every ideal of `𝒪_S` is extended from `R`.** -/
theorem map_comap_eq (I : Ideal (S.integer K)) :
    Ideal.map (algebraMap R (S.integer K)) (I.comap (algebraMap R (S.integer K))) = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx ↦ ?_
  set f := algebraMap R (S.integer K) with hf
  set J' := Ideal.map f (I.comap f) with hJ'
  have coeval (r : R) : ((f r : S.integer K) : K) = algebraMap R K r := by
    rw [IsScalarTower.algebraMap_apply R (S.integer K) K]; rfl
  -- for a denominator `d` of `x`, the product `f d * x` is extended from `R` and lies in `I`
  have key (d : R) (hd : d ∈ denomIdeal K (x : K)) : f d * x ∈ J' := by
    rw [mem_denomIdeal_iff] at hd
    obtain ⟨s, hs⟩ := hd
    have hfx : f d * x = f s := by
      apply Subtype.val_injective
      rw [Subalgebra.coe_mul, coeval d, coeval s, hs]
    rw [hfx]
    exact Ideal.mem_map_of_mem f (show f s ∈ I from hfx ▸ I.mul_mem_left _ hx)
  -- the elements `r` with `r * x ∈ J'` form an ideal containing the extension of `denomIdeal`
  let K' : Ideal (S.integer K) :=
    { carrier := {r | r * x ∈ J'}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by simpa [add_mul] using J'.add_mem ha hb
      smul_mem' := fun c {a} ha ↦ by
        simpa only [smul_eq_mul, Set.mem_ofPred_eq, mul_assoc] using J'.mul_mem_left c ha }
  have hsub : Ideal.map f (denomIdeal K (x : K)) ≤ K' := Ideal.map_le_iff_le_comap.mpr key
  have hmtop : Ideal.map f (denomIdeal K (x : K)) = ⊤ := map_denomIdeal_eq_top K S x.property
  have h1 : (1 : S.integer K) * x ∈ J' := hsub (hmtop.ge Submodule.mem_top)
  simpa using h1

/-!
### The Dedekind property
-/

/-- The ring of `S`-integers is Noetherian: every ideal is extended from the Noetherian
ring `R` by `map_comap_eq`. -/
instance isNoetherianRing : IsNoetherianRing (S.integer K) := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
  rw [← map_comap_eq K S I]
  exact Ideal.FG.map (IsNoetherian.noetherian (R := R) (I.comap (algebraMap R (S.integer K))))
    (algebraMap R (S.integer K))

/-- The contraction to `R` of a nonzero prime of `𝒪_S` is a nonzero prime: if it were zero, the
prime would be `map ⊥ = ⊥` by `map_comap_eq`. -/
lemma comap_ne_bot {P : Ideal (S.integer K)} (hP : P ≠ ⊥) :
    P.comap (algebraMap R (S.integer K)) ≠ ⊥ := by
  intro h0
  exact hP (by rw [← map_comap_eq K S P, h0, Ideal.map_bot])

/-- The ring of `S`-integers has Krull dimension at most `1`: the contraction to `R` of a
nonzero prime is maximal, and equalities of ideals lift back through `map_comap_eq`. -/
instance dimensionLEOne : Ring.DimensionLEOne (S.integer K) := by
  refine ⟨fun {P} hP hPp ↦ ?_⟩
  set f := algebraMap R (S.integer K) with hf
  -- pass to a maximal ideal `M` above `P` and compare contractions in `R`
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hPp.ne_top
  have hcP : P.comap f ≠ ⊥ := comap_ne_bot K S hP
  have hMne : M ≠ ⊥ := fun h ↦ hP (le_bot_iff.mp (h ▸ hPM))
  have hcM : M.comap f ≠ ⊥ := comap_ne_bot K S hMne
  -- both contractions are maximal in `R`, and one contains the other, so they are equal
  have hcPmax : (P.comap f).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hcP (hPp.comap f)
  have hcMprime : (M.comap f).IsPrime := hM.isPrime.comap f
  have heq : P.comap f = M.comap f :=
    hcPmax.eq_of_le hcMprime.ne_top (Ideal.comap_mono hPM)
  -- lift the equality back through `map_comap_eq`
  rwa [← map_comap_eq K S P, heq, map_comap_eq K S M]

/-- **The ring of `S`-integers of a Dedekind domain is a Dedekind domain.** -/
instance isDedekindDomain : IsDedekindDomain (S.integer K) where

/-!
### The height one spectrum

The primes of `𝒪_S` are the primes `v ∉ S`, via `v ↦ 𝒪_S ∩ v`. Under this correspondence the
`v`-adic valuation of `𝒪_S` is the restriction of the `v`-adic valuation of `R`, so the Selmer
group of `𝒪_S` relative to `∅` is the Selmer group of `R` relative to `S`.
-/

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is a proper ideal: it is contained in the proper
ideal of `S`-integers with `v`-valuation `< 1` (which does not contain `1`). -/
lemma map_asIdeal_ne_top {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊤ := by
  set f := algebraMap R (S.integer K) with hf
  have coeval (r : R) : ((f r : S.integer K) : K) = algebraMap R K r := by
    rw [IsScalarTower.algebraMap_apply R (S.integer K) K]; rfl
  let 𝔪 : Ideal (S.integer K) :=
    { carrier := {x | v.valuation K (x : K) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        rw [Set.mem_ofPred_eq, Subalgebra.coe_add]
        exact lt_of_le_of_lt ((v.valuation K).map_add _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha ↦ by
        have hc : v.valuation K (c : K) ≤ 1 := c.property v hv
        rw [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul]
        calc v.valuation K (c : K) * v.valuation K (a : K)
            ≤ 1 * v.valuation K (a : K) := by gcongr
          _ = v.valuation K (a : K) := one_mul _
          _ < 1 := ha }
  have hle : Ideal.map f v.asIdeal ≤ 𝔪 :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      show v.valuation K ((f a : S.integer K) : K) < 1
      rw [coeval]; exact (v.valuation_lt_one_iff_mem a).mpr ha
  intro htop
  have h1 : v.valuation K ((1 : S.integer K) : K) < 1 := le_trans htop.ge hle Submodule.mem_top
  simp at h1

lemma comap_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).comap (algebraMap R (S.integer K)) =
      v.asIdeal := by
  set f := algebraMap R (S.integer K) with hf
  refine (v.isMaximal.eq_of_le ?_ Ideal.le_comap_map).symm
  rw [Ne, Ideal.comap_eq_top_iff]
  exact map_asIdeal_ne_top K S hv

lemma isMaximal_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsMaximal := by
  set f := algebraMap R (S.integer K) with hf
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (map_asIdeal_ne_top K S hv)
  have hcle : v.asIdeal ≤ M.comap f := (comap_map_asIdeal K S hv).ge.trans (Ideal.comap_mono hle)
  have hceq : M.comap f = v.asIdeal :=
    (v.isMaximal.eq_of_le (hM.isPrime.comap f).ne_top hcle).symm
  rwa [← map_comap_eq K S M, hceq] at hM

/-- The extension of `v` to `𝒪_S` is a nonzero ideal: `v` is nonzero and the map is injective. -/
lemma map_asIdeal_ne_bot {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊥ := by
  intro h
  refine v.ne_bot ?_
  rw [← comap_map_asIdeal K S hv, h,
    Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R (S.integer K))]

/-- The prime of `𝒪_S` above a prime `v ∉ S` of `R`: the extension of `v`. -/
noncomputable def primeOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    HeightOneSpectrum (S.integer K) where
  asIdeal := Ideal.map (algebraMap R (S.integer K)) v.asIdeal
  isPrime := (isMaximal_map_asIdeal K S hv).isPrime
  ne_bot := map_asIdeal_ne_bot K S hv

@[simp] lemma primeOfNotMem_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (primeOfNotMem K S hv).asIdeal = Ideal.map (algebraMap R (S.integer K)) v.asIdeal :=
  rfl

/-- The prime of `R` below a prime `P` of `𝒪_S`. -/
noncomputable def primeBelow (P : HeightOneSpectrum (S.integer K)) : HeightOneSpectrum R where
  asIdeal := P.asIdeal.comap (algebraMap R (S.integer K))
  isPrime := P.isPrime.comap _
  ne_bot := comap_ne_bot K S P.ne_bot

@[simp] lemma primeBelow_asIdeal (P : HeightOneSpectrum (S.integer K)) :
    (primeBelow K S P).asIdeal = P.asIdeal.comap (algebraMap R (S.integer K)) :=
  rfl

lemma primeBelow_notMem (P : HeightOneSpectrum (S.integer K)) : primeBelow K S P ∉ S := by
  intro hv
  have h1 := map_asIdeal_eq_top K S hv
  rw [primeBelow_asIdeal, map_comap_eq] at h1
  exact P.isPrime.ne_top h1

/-- The primes of `𝒪_S` are exactly the primes of `R` not in `S`. -/
noncomputable def heightOneSpectrumEquiv :
    {v : HeightOneSpectrum R // v ∉ S} ≃ HeightOneSpectrum (S.integer K) where
  toFun v := primeOfNotMem K S v.property
  invFun P := ⟨primeBelow K S P, primeBelow_notMem K S P⟩
  left_inv v := Subtype.ext <| HeightOneSpectrum.ext <| comap_map_asIdeal K S v.property
  right_inv P := HeightOneSpectrum.ext <| map_comap_eq K S P.asIdeal

/-- For `v ∉ S`, the contraction of the extension of `v ^ n` is `v ^ n`: the contraction divides
`v ^ n`, so it is `v ^ j`; extending back gives `Pⱼ = Pₙ`, whence `j = n`. -/
lemma comap_map_pow {v : HeightOneSpectrum R} (hv : v ∉ S) (n : ℕ) :
    (Ideal.map (algebraMap R (S.integer K)) (v.asIdeal ^ n)).comap
        (algebraMap R (S.integer K)) = v.asIdeal ^ n := by
  set f := algebraMap R (S.integer K) with hf
  have hP0 : Ideal.map f v.asIdeal ≠ 0 := map_asIdeal_ne_bot K S hv
  have hPnu : ¬ IsUnit (Ideal.map f v.asIdeal) :=
    fun h ↦ map_asIdeal_ne_top K S hv (Ideal.isUnit_iff.mp h)
  refine le_antisymm ?_ Ideal.le_comap_map
  have hdvd : (Ideal.map f (v.asIdeal ^ n)).comap f ∣ v.asIdeal ^ n :=
    Ideal.dvd_iff_le.mpr Ideal.le_comap_map
  obtain ⟨j, -, hassoc⟩ := (dvd_prime_pow v.prime n).mp hdvd
  rw [associated_iff_eq] at hassoc
  have hmapQ : Ideal.map f ((Ideal.map f (v.asIdeal ^ n)).comap f) =
      Ideal.map f (v.asIdeal ^ n) := map_comap_eq K S _
  rw [hassoc, Ideal.map_pow, Ideal.map_pow] at hmapQ
  rw [hassoc, (pow_inj_of_not_isUnit hPnu hP0).mp hmapQ]

/-- For `v ∉ S`, the `Pᵥ`-adic valuation on `R` (computed in `𝒪_S`) is the `v`-adic valuation:
the two chains of prime powers `v ^ k` and `Pᵥ ^ k` have matching membership. -/
lemma intValuationDef_map {v : HeightOneSpectrum R} (hv : v ∉ S) (a : R) :
    (primeOfNotMem K S hv).intValuationDef (algebraMap R (S.integer K) a) =
      v.intValuationDef a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hfa : algebraMap R (S.integer K) a ≠ 0 := fun h ↦ ha
    (FaithfulSMul.algebraMap_injective R (S.integer K)
      (h.trans (map_zero (algebraMap R (S.integer K))).symm))
  have hmem (k : ℕ) : a ∈ v.asIdeal ^ k ↔
      algebraMap R (S.integer K) a ∈ (primeOfNotMem K S hv).asIdeal ^ k := by
    rw [primeOfNotMem_asIdeal, ← Ideal.map_pow, ← Ideal.mem_comap, comap_map_pow K S hv]
  suffices h : Associates.count (Associates.mk (primeOfNotMem K S hv).asIdeal)
        (Associates.mk (Ideal.span {algebraMap R (S.integer K) a})).factors =
      Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {a})).factors by
    rw [v.intValuationDef_if_neg ha, (primeOfNotMem K S hv).intValuationDef_if_neg hfa, h]
  refine Nat.le_antisymm ?_ ?_
  · exact (v.le_count_iff ha _).mpr
      ((hmem _).mpr (((primeOfNotMem K S hv).le_count_iff hfa _).mp le_rfl))
  · exact ((primeOfNotMem K S hv).le_count_iff hfa _).mpr
      ((hmem _).mp ((v.le_count_iff ha _).mp le_rfl))

/-- The valuation of `𝒪_S` at the prime above `v` is the valuation of `R` at `v`. -/
lemma valuation_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S}) (x : K) :
    (heightOneSpectrumEquiv K S v).valuation K x = (v : HeightOneSpectrum R).valuation K x := by
  have hR (a : R) : (heightOneSpectrumEquiv K S v).valuation K (algebraMap R K a) =
      (v : HeightOneSpectrum R).valuation K (algebraMap R K a) := by
    have e1 : (heightOneSpectrumEquiv K S v).valuation K (algebraMap R K a) =
        (primeOfNotMem K S v.property).intValuationDef (algebraMap R (S.integer K) a) := by
      rw [IsScalarTower.algebraMap_apply R (S.integer K) K a,
        HeightOneSpectrum.valuation_of_algebraMap]; rfl
    rw [e1, intValuationDef_map K S v.property a, HeightOneSpectrum.valuation_of_algebraMap]; rfl
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, hR a, hR b]

/-!
### The class group
-/

/-- `𝒪_S` is torsion-free over `R`, as `R` embeds into it. -/
instance : Module.IsTorsionFree R (S.integer K) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact FaithfulSMul.algebraMap_injective R (S.integer K)

/-- Extension of ideals `Cl(R) → Cl(𝒪_S)` is surjective: every ideal of `𝒪_S` is extended from
`R` (`map_comap_eq`). -/
lemma extendedHom_surjective :
    Function.Surjective (ClassGroup.extendedHom R (S.integer K)) := by
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI : (I : Ideal (S.integer K)) ≠ ⊥ := by
    have := I.2; rwa [mem_nonZeroDivisors_iff_ne_zero] at this
  refine ⟨ClassGroup.mk0 ⟨(I : Ideal (S.integer K)).comap (algebraMap R (S.integer K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (comap_ne_bot K S hI)⟩, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  exact congrArg _ (Subtype.ext (map_comap_eq K S _))

/-- The class group of `𝒪_S` is finite as soon as that of `R` is, being a quotient of it. -/
instance finite_classGroup [Finite (ClassGroup R)] : Finite (ClassGroup (S.integer K)) :=
  .of_surjective _ (extendedHom_surjective K S)

end IsDedekindDomain.SInteger

end
/- ===== end EllipticCurves/Mathlib/SIntegers.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/SelmerGroup.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-!
# Finiteness of Selmer groups

Let `R` be a Dedekind domain with fraction field `K`, let `S` be a set of primes of `R` and let
`n` be a positive integer. `Mathlib.RingTheory.DedekindDomain.SelmerGroup` defines the Selmer
group `K(S,n) ≤ Kˣ/(Kˣ)ⁿ` as the classes whose `v`-adic valuation is divisible by `n` for all
`v ∉ S`, and records as a `TODO` both the maps in the fundamental exact sequence and the
finiteness of `K(S,n)`. This file supplies them, and deduces the finiteness of the Selmer group
of a finite étale `K`-algebra, which is what the proof of the Weak Mordell-Weil theorem
(`EllipticCurves.WeakMordellWeil`, Step 7) needs.

## The hypotheses

The finiteness of `K(S,n)` is *not* automatic for a general Dedekind domain: it fails already for
`R = K` a field with `Kˣ` not `n`-divisible-of-finite-index. The fundamental exact sequence
```
1 → 𝒪_S(K)ˣ / (𝒪_S(K)ˣ)ⁿ → K(S,n) → Cl_S(R)[n] → 1
```
shows that the two things one needs are

* the `S`-unit group `Set.unit S K` is finitely generated, and
* the `S`-class group `Cl_S(R)` is finite.

Each of these follows from the corresponding statement for `S = ∅` together with `S` being finite:
`Cl_S(R)` is by construction a quotient of `Cl(R)`, and `𝒪_S(K)ˣ` is an extension of a subgroup
of the free abelian group `ℤ^S` by `Rˣ`. So the weakest reasonable hypotheses, and the ones used
below, are

* `[Finite (ClassGroup R)]`,
* `[Group.FG Rˣ]`,
* `S.Finite`, and
* `[NeZero n]`.

For `R` the ring of integers of a number field, the first is the class number theorem
(`Fintype (ClassGroup (𝓞 K))`) and the second is Dirichlet's unit theorem
(`Monoid.FG (𝓞 K)ˣ`), both in Mathlib; see the section `NumberField` at the end. Nothing here
needs `R` to be of *arithmetic* type beyond these two properties, and in particular the results
apply verbatim to the ring of integers of a function field.

Note that `[NeZero n]` cannot be dropped: `K(S,0) = Kˣ`.

## Implementation

The `S`-class group is realized as `ClassGroup (S.integer K)`, the class group of the ring
`𝒪_S = Set.integer S K` of `S`-integers, which `EllipticCurves.Mathlib.SIntegers` shows to be a
Dedekind domain
with fraction field `K`, height one spectrum `{v | v ∉ S}` (valuation-compatibly) and finite
class group whenever `Cl(R)` is finite. Via this dictionary the Selmer condition on a class
`u(Kˣ)ⁿ ∈ K(S,n)` says exactly that the principal fractional ideal `(u)` of `𝒪_S` has all its
valuations divisible by `n` (`mem_selmerGroup_iff_unitsNDivisible`), so the `n`-th-root class
map of `EllipticCurves.Mathlib.FractionalIdeal` (`FractionalIdeal.nthRootClass`, built from the
isomorphism of
the group of fractional ideals with the free abelian group on the primes) descends to the
right-hand map `toSClassGroup : K(S,n) →* Cl(𝒪_S)` of the fundamental exact sequence.

Note that `toSClassGroup` is *not* surjective onto `Cl(𝒪_S)` in general: its image is the
`n`-torsion subgroup (`range_toSClassGroup`), as the sequence above says.

## Main definitions

* `IsDedekindDomain.sUnitValuation`: the tuple of `v`-adic valuations of an `S`-unit,
  for `v ∈ S`.
* `IsDedekindDomain.sUnitToSelmer` and `IsDedekindDomain.sUnitModPowToSelmer`: the left-hand map
  of the fundamental exact sequence.
* `IsDedekindDomain.toSClassGroup`: the right-hand map of the fundamental exact sequence.
* `IsDedekindDomain.selmerGroupPi` and `IsDedekindDomain.selmerGroupOfEquiv`: the Selmer group of
  a finite étale algebra, presented through a decomposition into fields.

## Main statements

* `IsDedekindDomain.fg_sUnit`: finite generation of the `S`-unit group, and `finrank_sUnit`:
  its rank is `rank Rˣ + |S|` when moreover the class group of `R` is finite.
* `IsDedekindDomain.ker_toSClassGroup`: exactness of the fundamental sequence in the middle.
* `IsDedekindDomain.range_toSClassGroup`: exactness on the right; the image is the `n`-torsion
  of the class group.
* `IsDedekindDomain.finite_selmerGroup`: **the main result**, `K(S,n)` is finite.
* `IsDedekindDomain.finite_selmerGroupOfEquiv`: the Selmer group of a finite étale algebra is
  finite.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

/-!
### Quotients of finitely generated commutative groups
-/

/-- A commutative group is finitely generated iff it is finitely generated as a `ℤ`-module. -/
theorem Module.finite_int_additive (G : Type*) [CommGroup G] [Group.FG G] :
    Module.Finite ℤ (Additive G) :=
  Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr ‹_›)

/-- A commutative group that is finitely generated as a `ℤ`-module is finitely generated as a
group; converse direction of `Module.finite_int_additive`. -/
theorem Group.fg_of_module_finite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : Group.FG G :=
  AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp h)

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring. (The proof passes through `Additive G`, so `to_additive` cannot translate it;
an additive version would have to be stated by hand.) -/
theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    Group.FG H :=
  have : Module.Finite ℤ (Additive G) := Module.finite_int_additive G
  Group.fg_of_module_finite_int <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)

/-- An extension of finitely generated groups is finitely generated: if the kernel and the range
of `φ : G →* H` are finitely generated, then so is `G`. Generators: preimages of generators of
the range together with generators of the kernel. -/
theorem Group.fg_of_fg_ker_of_fg_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hker : Group.FG φ.ker) (hrange : Group.FG φ.range) : Group.FG G := by
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.mp hrange
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hker
  set σ : φ.range → G := Function.surjInv φ.rangeRestrict_surjective with hσ
  set U : Set G := σ '' T ∪ (φ.ker.subtype '' S) with hU
  refine Group.fg_iff.mpr ⟨U, ?_, (hTfin.image σ).union (hSfin.image _)⟩
  -- the kernel is contained in the closure of `U`
  have hkerle : φ.ker ≤ Subgroup.closure U := by
    calc φ.ker = (⊤ : Subgroup φ.ker).map φ.ker.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.closure S).map φ.ker.subtype := by rw [hS]
      _ = Subgroup.closure (φ.ker.subtype '' S) := MonoidHom.map_closure ..
      _ ≤ Subgroup.closure U := Subgroup.closure_mono Set.subset_union_right
  -- the closure of `U` surjects onto the range
  have hmap : (Subgroup.closure U).map φ.rangeRestrict = ⊤ := by
    rw [eq_top_iff, ← hT]
    refine (Subgroup.closure_mono ?_).trans_eq (MonoidHom.map_closure ..).symm
    intro t ht
    exact ⟨σ t, Set.mem_union_left _ ⟨t, ht, rfl⟩, Function.surjInv_eq _ t⟩
  -- conclude via `comap_map_eq`
  have h := Subgroup.comap_map_eq φ.rangeRestrict (Subgroup.closure U)
  rw [hmap, Subgroup.comap_top, MonoidHom.ker_rangeRestrict,
    sup_eq_left.mpr hkerle] at h
  exact h.symm

/-- A finitely generated commutative group of finite exponent is finite. -/
theorem CommGroup.finite_of_fg_of_pow_eq_one {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ)
    [NeZero n] (hn : ∀ x : G, x ^ n = 1) : Finite G := by
  let _ : Module (ZMod n) (Additive G) := AddCommGroup.zmodModule (n := n) hn
  have h₁ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (by rwa [AddGroup.fg_iff_mul_fg])
  have h₂ : Module.Finite (ZMod n) (Additive G) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod n) (Additive G)
  have := Module.finite_of_finite (ZMod n) (M := Additive G)
  exact Finite.of_equiv _ (Additive.toMul (α := G))

/-- The group of `n`-th power classes of a finitely generated commutative group is finite. -/
theorem CommGroup.finite_modPow {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ) [NeZero n] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  have : Group.FG (G ⧸ (powMonoidHom n : G →* G).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  refine finite_of_fg_of_pow_eq_one n fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-!
### `S`-units

`Set.unit S K` is the subgroup of `x : Kˣ` with `v x = 1` for all `v ∉ S`. Sending `x` to its
tuple of valuations at the primes *in* `S` gives a homomorphism to `ℤ^S` whose kernel is the
group of `∅`-units, i.e. `Rˣ`. When `S` is finite this exhibits `Set.unit S K` as an extension
of a subgroup of a free abelian group of finite rank by `Rˣ`.
-/

variable (S : Set (HeightOneSpectrum R))

/-- The tuple of `v`-adic valuations of an `S`-unit at the primes `v ∈ S`. -/
noncomputable def sUnitValuation : S.unit K →* (S → Multiplicative ℤ) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ)
  map_one' := funext fun _ ↦ map_one _
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul]; rfl

@[simp]
lemma sUnitValuation_apply (x : S.unit K) (v : S) :
    sUnitValuation K S x v = (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ) :=
  rfl

/-- The kernel of `sUnitValuation` consists of the `∅`-units, i.e. of the units of `R`. -/
theorem ker_sUnitValuation :
    (sUnitValuation K S).ker =
      ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext x
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, sUnitValuation_apply,
    Subgroup.mem_subgroupOf]
  refine ⟨fun hx v _ ↦ ?_, fun hx v ↦ ?_⟩
  · by_cases hv : v ∈ S
    · simpa using (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mp (hx ⟨v, hv⟩)
    · exact x.property v hv
  · exact (v.1.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by
      simpa using hx v.1 (Set.notMem_empty _))

variable (R) in
/-- The `∅`-units of `K` are the units of `R`. -/
noncomputable def unitsEquivEmptyUnit : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).unit K :=
  let e₁ : R ≃ₐ[R] (⊥ : Subalgebra R K) :=
    (Algebra.botEquivOfInjective (IsFractionRing.injective R K)).symm
  let e₂ : (⊥ : Subalgebra R K) ≃ₐ[R] (∅ : Set (HeightOneSpectrum R)).integer K :=
    Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K).symm
  (Units.mapEquiv (e₁.trans e₂).toRingEquiv.toMulEquiv).trans (Set.unitEquivUnitsInteger _ K).symm

/-- **Dirichlet's `S`-unit theorem**, weak form: if `Rˣ` is finitely generated and `S` is finite,
then the group of `S`-units is finitely generated.

The map `sUnitValuation` has finitely generated image (a subgroup of the free abelian group
`ℤ^S` of finite rank) and kernel isomorphic to `Rˣ` (`ker_sUnitValuation`,
`unitsEquivEmptyUnit`), and an extension of a finitely generated group by a finitely generated
group is finitely generated. -/
theorem fg_sUnit [Group.FG Rˣ] (hS : S.Finite) : Group.FG (S.unit K) := by
  have : Finite S := hS.to_subtype
  refine Group.fg_of_fg_ker_of_fg_range (sUnitValuation K S) ?_ (Subgroup.fg_of_commGroup_fg _)
  rw [ker_sUnitValuation]
  have : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K) :=
    Group.fg_of_surjective (f := (unitsEquivEmptyUnit R K).toMonoidHom)
      (unitsEquivEmptyUnit R K).surjective
  have hle : (∅ : Set (HeightOneSpectrum R)).unit K ≤ S.unit K := Set.unit_mono S.empty_subset
  exact Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.surjective

/-!
### The rank of the `S`-unit group

Strengthening `fg_sUnit`: if moreover the class group of `R` is finite, then the rank of the
`S`-unit group is exactly `rank Rˣ + |S|` (**Dirichlet's `S`-unit theorem**, rank version).
The point is that the valuation map `sUnitValuation` then has full-rank image: for each
`v ∈ S`, some power `v ^ n` is principal (`HeightOneSpectrum.exists_pow_eq_span`), and its
generator is an `S`-unit whose valuation vector is a nonzero multiple of the `v`-th standard
basis vector.
-/

section Rank

open Module

/-- The logarithmic valuation map on `S`-units, with values in `ℤ ^ S`: the additive form of
`sUnitValuation`. This is the `S`-unit analogue of `NumberField.Units.logEmbedding`. -/
noncomputable def sUnitLog : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x w ↦ Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w)
      map_zero' := by ext w; simp
      map_add' := fun x y ↦ by ext w; simp }

variable [Finite (ClassGroup R)]

end Rank

/-!
### The fundamental exact sequence
-/

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-- The class of an `S`-unit lies in the Selmer group `K(S,n)`. -/
noncomputable def sUnitToSelmer : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
    have : v.valuationOfNeZero (x : Kˣ) = 1 :=
      (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by rw [x.property v hv, WithZero.coe_one])
    simp [this]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The left-hand map of the fundamental exact sequence: an `S`-unit modulo `n`-th powers of
`S`-units maps to the Selmer group `K(S,n)`. -/
noncomputable def sUnitModPowToSelmer :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (sUnitToSelmer K S n) <| by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

@[simp]
lemma range_sUnitModPowToSelmer :
    (sUnitModPowToSelmer K S n).range = (sUnitToSelmer K S n).range := by
  ext
  exact ⟨by rintro ⟨y, rfl⟩; induction y using QuotientGroup.induction_on with
    | H y => exact ⟨y, rfl⟩, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, hy⟩⟩

/-- Transport of the integer-valued valuation along the spectrum correspondence between the
primes of `R` off `S` and the primes of `𝒪_S`. -/
lemma SInteger.valuationOfNeZero_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S})
    (u : Kˣ) : (SInteger.heightOneSpectrumEquiv K S v).valuationOfNeZero u
      = (v : HeightOneSpectrum R).valuationOfNeZero u := by
  rw [← WithZero.coe_inj,
    show ((_ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ from
      HeightOneSpectrum.valuationOfNeZero_eq _ u, HeightOneSpectrum.valuationOfNeZero_eq,
    SInteger.valuation_heightOneSpectrumEquiv K S v (u : K)]

/-- The class of `u` lies in the Selmer group `K(S,n)` exactly when
the principal fractional ideal `(u)` of the `S`-integers is `n`-divisible. -/
lemma mem_selmerGroup_iff_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Units.modPow K n) ∈ selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  have lhs : (QuotientGroup.mk u : Units.modPow K n) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd
        ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
    forall₂_congr fun v _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v n u
  have rhs : u ∈ unitsNDivisible (S.integer K) K n ↔
      ∀ w : HeightOneSpectrum (S.integer K),
        (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    refine forall_congr' fun w ↦ ?_
    rw [toAdd_valuationOfNeZero, Int.dvd_neg]
    show (n : ℤ) ∣ count K w ((toPrincipalIdeal (S.integer K) K u :
      (FractionalIdeal (S.integer K)⁰ K)ˣ) : FractionalIdeal (S.integer K)⁰ K) ↔ _
    rw [coe_toPrincipalIdeal]
  rw [lhs, rhs]
  constructor
  · intro h w
    rw [show w = SInteger.heightOneSpectrumEquiv K S
        ((SInteger.heightOneSpectrumEquiv K S).symm w) from
        ((SInteger.heightOneSpectrumEquiv K S).apply_symm_apply w).symm,
      SInteger.valuationOfNeZero_heightOneSpectrumEquiv]
    exact h _ ((SInteger.heightOneSpectrumEquiv K S).symm w).property
  · intro h v hv
    have := h (SInteger.heightOneSpectrumEquiv K S ⟨v, hv⟩)
    rwa [SInteger.valuationOfNeZero_heightOneSpectrumEquiv] at this

/-- The surjection from the `n`-divisible units onto the Selmer group. -/
noncomputable def selmerGroupFromUnits :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).comp
    (unitsNDivisible (S.integer K) K n).subtype).codRestrict _
      (fun u ↦ (mem_selmerGroup_iff_unitsNDivisible K S n (u : Kˣ)).mpr u.2)

lemma selmerGroupFromUnits_surjective :
    Function.Surjective (selmerGroupFromUnits K S n) := by
  intro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u =>
    exact ⟨⟨u, (mem_selmerGroup_iff_unitsNDivisible K S n u).mp hc⟩, rfl⟩

/-- The kernel of `selmerGroupFromUnits` is contained in that of the `n`-th-root class map:
an `n`-th power has principal `n`-th root. -/
lemma ker_selmerGroupFromUnits_le [NeZero n] :
    (selmerGroupFromUnits K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have : (QuotientGroup.mk (u : Kˣ) : Units.modPow K n) = 1 := congrArg Subtype.val hu
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp this
  exact (nthRootClass_eq_one_iff _ _ (NeZero.ne n) u).mpr ⟨1, w, by
    rw [map_one, one_mul]; exact hw⟩

/-- The right-hand map of the fundamental exact sequence: a Selmer class is sent to the ideal
class of the `n`-th root of the principal ideal `(u)` of any representative `u`, in the class
group of the ring of `S`-integers. Obtained by descending `FractionalIdeal.nthRootClass` along
`selmerGroupFromUnits`. -/
noncomputable def toSClassGroup [NeZero n] :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (QuotientGroup.lift _ (nthRootClass (S.integer K) K n)
      (ker_selmerGroupFromUnits_le K S n)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm.toMonoidHom

lemma toSClassGroup_selmerGroupFromUnits [NeZero n] (u : unitsNDivisible (S.integer K) K n) :
    toSClassGroup K S n (selmerGroupFromUnits K S n u) =
      nthRootClass (S.integer K) K n u := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm (selmerGroupFromUnits K S n u) =
        QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [toSClassGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk']

lemma coe_unitEquivUnitsInteger_symm (a : (S.integer K)ˣ) :
    ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
      Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := by
  apply Units.ext
  rw [Set.unitEquivUnitsInteger_symm_apply_coe]
  rfl

/-- Exactness of the fundamental exact sequence in the middle: a Selmer class has trivial
`n`-th-root ideal class exactly when it is represented by an `S`-unit. -/
theorem ker_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).ker = (sUnitToSelmer K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
  rw [MonoidHom.mem_ker, toSClassGroup_selmerGroupFromUnits,
    nthRootClass_eq_one_iff _ _ (NeZero.ne n)]
  constructor
  · intro ⟨a, w, hw⟩
    refine ⟨(S.unitEquivUnitsInteger K).symm a, Subtype.ext ?_⟩
    show (QuotientGroup.mk _ : Units.modPow K n) = QuotientGroup.mk (u : Kˣ)
    have hwn : (QuotientGroup.mk (w ^ n) : Units.modPow K n) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
    rw [coe_unitEquivUnitsInteger_symm, ← hw, QuotientGroup.mk_mul, hwn]
    exact (mul_one _).symm
  · intro ⟨s, hs⟩
    have hcoe : (QuotientGroup.mk (s : Kˣ) : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) :=
      congrArg Subtype.val hs
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hcoe
    refine ⟨S.unitEquivUnitsInteger K s, w, ?_⟩
    have hmap : Units.map (algebraMap (S.integer K) K : S.integer K →* K)
        (S.unitEquivUnitsInteger K s) = (s : Kˣ) := by
      rw [← coe_unitEquivUnitsInteger_symm, MulEquiv.symm_apply_apply]
    rw [powMonoidHom_apply] at hw
    rw [hmap, hw]
    group

/-!
### Finiteness
-/

variable (R) in
/-- **The Selmer group `K(S,n)` is finite**, provided that the class group of `R` is finite, that
`Rˣ` is finitely generated, that `S` is finite and that `n ≠ 0`.

The image of `sUnitModPowToSelmer` is finite, since its source is the quotient of a finitely
generated commutative group (`fg_sUnit`) by its `n`-th powers (`CommGroup.finite_modPow`).
By `ker_toSClassGroup` that image is the kernel of `toSClassGroup`, whose target
`ClassGroup (S.integer K)` is finite by `SInteger.finite_classGroup`. -/
theorem finite_selmerGroup [Finite (ClassGroup R)] [Group.FG Rˣ] (hS : S.Finite) [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have := fg_sUnit K S hS
  have hker : Finite (toSClassGroup K S n).ker := by
    rw [ker_toSClassGroup, ← range_sUnitModPowToSelmer]
    have := CommGroup.finite_modPow (G := S.unit K) n
    exact Finite.Set.finite_range _
  have hquot : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (toSClassGroup K S n).ker) :=
    .of_injective _ (QuotientGroup.kerLift_injective (toSClassGroup K S n))
  exact Finite.of_subgroup_quotient (toSClassGroup K S n).ker

/-!
### Trivial class group: the Selmer group is a quotient of the unit square classes
-/

/-!
### Selmer groups of finite étale algebras

A finite étale algebra `A` over `K` is a finite product of finite separable field extensions of
`K`. Choosing a Dedekind order `B i` in each factor `L i` and a finite set `S i` of primes of
`B i`, the Selmer group of `A` is the preimage in `Aˣ/(Aˣ)ⁿ` of the product of the Selmer groups
`L i (S i, n)` under the induced isomorphism. It is finite as soon as each factor's Selmer group
is.

The decomposition `e` is an input rather than something derived from an `Algebra.IsEtale`
hypothesis: Mathlib does not currently provide the splitting of an étale algebra into fields, and
in the application (`EllipticCurves.WeakMordellWeil`) the decomposition is explicitly
available as
`AdjoinRoot.modPowEquivPiFactors`.
-/

section Etale

variable {ι : Type*} (L : ι → Type*) [(i : ι) → Field (L i)]
  (B : (i : ι) → Type*) [(i : ι) → CommRing (B i)] [(i : ι) → IsDedekindDomain (B i)]
  [(i : ι) → Algebra (B i) (L i)] [(i : ι) → IsFractionRing (B i) (L i)]
  (S : (i : ι) → Set (HeightOneSpectrum (B i))) (n : ℕ)

variable {A : Type*} [CommRing A]

end Etale

/-!
### Number fields

For the ring of integers of a number field both hypotheses are theorems of Mathlib, so the
finiteness of `K(S,n)` holds for every finite `S` and every `n ≠ 0`.
-/

section NumberField

open NumberField

variable (F : Type*) [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ)

end NumberField

end IsDedekindDomain

end
/- ===== end EllipticCurves/Mathlib/SelmerGroup.lean ===== -/

/- ===== begin EllipticCurves/VariableChange.lean (EllipticCurves @ c4c72f486112) ===== -/
/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/

section

/-!
# Isomorphism of point groups induced by a change of variables

Material for `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`.

Mathlib's affine `Point` API provides the group homomorphism `WeierstrassCurve.Affine.Point.map`
induced by a change of the base field (for a *fixed* Weierstrass curve), but not the isomorphism of
Mordell–Weil groups induced by an admissible change of variables between two *different* curves.
This file supplies that: for `C : VariableChange F` and an elliptic curve `W` over a field `F`, the
admissible change of variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)` gives a group isomorphism
`WeierstrassCurve.Affine.Point.equivVariableChange : (C • W).Point ≃+ W.Point`. All definitions
are computable (given decidable equality on `F`): the inverse of the isomorphism is given
explicitly by the change of variables `C⁻¹`, not obtained from bijectivity via choice.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapVariableChange` : the group homomorphism `(C • W).Point →+
  W.Point`, `(x, y) ↦ (u²x + r, u³y + u²sx + t)`.
* `WeierstrassCurve.Affine.Point.equivVariableChange` : the group isomorphism `(C • W).Point ≃+
  W.Point`, with inverse coming from `C⁻¹`.
* `WeierstrassCurve.Affine.Point.equivOfEq` : transport of the point group along an equality of
  Weierstrass curves.

-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables

Throughout, the change of variables carries a point `(x, y)` of `C • W` to the point
`(u²x + r, u³y + u²sx + t)` of `W`. -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition (`negY`) only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-! ### The induced isomorphism of point groups -/

namespace Point

variable [W.IsElliptic]

/-- The underlying map `(C • W).Point → W.Point` of the change of variables, sending `0` to `0` and
`(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      (equation_iff_nonsingular.mp
        ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h)))

@[simp] lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          (equation_iff_nonsingular.mp
            ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h))) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy; rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h; exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h; rfl

/-- The group homomorphism `(C • W).Point →+ W.Point` induced by the admissible change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := equation_iff_nonsingular.mpr h₁
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := equation_iff_nonsingular.mpr h₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, with inverse coming from `C⁻¹`. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      refine some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

end Point

end WeierstrassCurve.Affine

end
/- ===== end EllipticCurves/VariableChange.lean ===== -/

/- ===== begin EllipticCurves/WeakMordellWeil.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite, where `E` is an elliptic curve
given by a Weierstrass equation `y² = x³ + a₂x² + a₄x + a₆ =: f(x)` (so with `a₁ = a₃ = 0`,
which is always achievable when the characteristic is not `2`)
over the fraction field `K` of a Dedekind domain `R`, under finiteness hypotheses — finite
class group and finitely generated unit group for the rings of integers of the field factors
of `K[X]/⟨f⟩` — that are theorems when `K` is a number field.

We use the `x-T` map approach.

The general-purpose material developed along the way, which has nothing to do with elliptic
curves, lives in `EllipticCurves.Mathlib.Basic`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   => done.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
   => done (the bare map is defined as `μ₀`).
3. Show that `μ` is a group homomorphism.
   => done.
4. Show that `ker μ = 2E(K)`.
   => done.
5. Show that `im μ` is contained in the kernel of the norm map on square classes.
   => done, via `AdjoinRoot.norm_mk_eq_resultant`, which says that the norm of
   `AdjoinRoot.mk g p` for monic `g` is the resultant of `g` and `p`
   (in `EllipticCurves.Mathlib.Basic`).
   Note that this step is *not* needed for the finiteness result (Steps 6 and 7 do not use
   it); it is included because the norm condition cuts down the Selmer group in explicit
   computations.
6. Show that `im μ ⊆ A(S,2)` for a suitable finite set `S` of "bad" primes.
   => done, as `range_μ_le_selmerGroupA` at the end of the file, for `E` over the fraction field
   of a Dedekind domain and for *any* `S` outside which the coefficients of the cubic are
   integral and `disc f` is a unit. Such sets are provided by `badPrimes` (primes dividing `2`
   or `Δ`, or occurring in a coefficient denominator); the refined sets `discBadPrimes` and
   `badPrimes₂` defined alongside it feed the sharpened Selmer-group bound of
   `EllipticCurves.SelmerGroup`.
7. Show that `A(S,2)` is finite, and conclude that `E(K)/2E(K)` is finite.
   => done, as `finite_index_range_nsmulAddMonoidHom_two` at the end of the file. The
   finiteness of the `2`-Selmer group of each field factor is
   `IsDedekindDomain.finite_selmerGroup` (in `EllipticCurves.Mathlib.SelmerGroup`); it requires
   the class group of the factor's ring of integers to be finite and its unit group to be finitely
   generated, which are taken as hypotheses (for number fields they are the class number
   theorem and Dirichlet's unit theorem, both in Mathlib).
-/

/-!
### Two commutative-ring identities

These are used in Step 3 (`μ` is a homomorphism); they encode the multiplicativity of the
`x - T` map on the level of coordinates.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product
of the `b * c - a` and its two analogues. -/
lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root
of `(d - a) * b * c`. -/
lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

lemma ringChar_ne_two [W.IsElliptic] [W.IsCharNeTwoNF] : ringChar K ≠ 2 := by
  have h := W.isUnit_Δ.ne_zero
  contrapose! h
  have h2 : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  rw [Δ_of_isCharNeTwoNF W]
  linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

/-!
### Step 1: define `A`
-/

open Polynomial

/-- The polynomial on the right hand side of a Weierstrass equation with `a₁ = a₃ = 0`. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero

lemma degree_lt_degree_f {p : K[X]} (hp : p.natDegree ≤ 2) : p.degree < W.f.degree :=
  degree_lt_degree <| by rw [natDegree_f]; lia

lemma degree_f : W.f.degree = 3 := by
  rw [degree_eq_natDegree W.f_ne_zero, natDegree_f]; rfl

/-- The discriminant of the cubic `f`, in terms of the coefficients of `W`. -/
lemma discr_f : W.f.discr = W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆
    - 27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three W.degree_f]
  simp only [f, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- In char ≠ 2 normal form, `Δ = 16 · disc f`; in particular the two agree up to a unit away
from `2`, but *not* at even places, where `disc f` is the finer invariant. -/
lemma Δ_eq_discr_f [W.IsCharNeTwoNF] : W.Δ = 16 * W.f.discr := by
  rw [Δ_of_isCharNeTwoNF W, W.discr_f]; ring

lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring

lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [separable_def', derivative_f, f]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a₄ - 96 * W.a₂ ^ 2) * X
      + C (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)),
    C (W.Δ)⁻¹ * (C (32 * W.a₂ ^ 2 - 96 * W.a₄) * X ^ 2
      + C (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * X
      + C (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)), ?_⟩
  rw [mul_assoc, mul_assoc (C (W.Δ)⁻¹), ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isCharNeTwoNF]
  simp only [C_eq_algebraMap]
  algebra

lemma squarefree_f [W.IsElliptic] [W.IsCharNeTwoNF] : Squarefree W.f :=
  (separable_f W).squarefree

lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]

lemma map_eval_f {L : Type*} [CommRing L] [Algebra K L] (x : K) :
    algebraMap K L (W.f.eval x) = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
  simp [f]

lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]

@[simp]
lemma negY_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x y : K) : W.negY x y = -y := by
  rw [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring

/-- On a point of `W`, the value `f x` is a square, so it vanishes exactly when `y` does. -/
lemma ne_zero_of_eval_f_ne_zero [W.IsCharNeTwoNF] {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) : y ≠ 0 :=
  fun h0 ↦ hx <| by simp [(equation_iff_eval_f_eq_sq W x y).mp h, h0]

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

lemma degree_lt_degree_fCofactor (x : K) {p : K[X]} (hp : p.natDegree ≤ 1) :
    p.degree < (W.fCofactor x).degree :=
  degree_lt_degree <| by rw [natDegree_fCofactor]; lia

lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp [fCofactor, f]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma discr_fCofactor (x : K) :
    (W.fCofactor x).discr = (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) := by
  have hdeg : (W.fCofactor x).degree = 2 := by
    rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, W.natDegree_fCofactor x]; rfl
  rw [discr_of_degree_eq_two hdeg]
  simp only [fCofactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- If `x` is a root of `f`, splitting off the factor `X - x` writes `disc f` as
`(fCofactor x).discr * f'(x) ^ 2`. -/
lemma discr_f_eq_discr_fCofactor_mul_sq {x : K} (hx : W.f.eval x = 0) :
    W.f.discr = (W.fCofactor x).discr * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx, mul_comm]
  rw [discr_X_sub_C_mul (W.monic_fCofactor x) (by rw [W.natDegree_fCofactor]; norm_num) x,
    W.eval_fCofactor_self x]

/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point with `2`-torsion `x`-coordinate `x` is divisible by `2`
(used in Step 4). -/
private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  apply_fun (· * (X - C x)) at hq
  rw [mul_right_comm, ← f_eq_mul_of_eval_eq_zero _ hx] at hq
  replace hq : q * W.f = ((C r * X + C s) ^ 2 - (C x - X)) * (X - C x) := by
    rw [mul_comm]; exact hq.symm
  refine ⟨C (1 / r ^ 2) * q, ?_⟩
  rw [eq_comm, mul_comm W.f]
  apply_fun (C (r ^ 2) * ·) using mul_right_injective₀ <| by simp [hr]
  dsimp only
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  rw [mul_one_div_cancel <| pow_ne_zero 2 hr, map_one, one_mul, hq]
  conv_rhs =>
    rw [sub_neg_eq_add, mul_add, ← mul_assoc, map_pow, ← mul_pow, mul_sub (C r), ← map_mul,
      mul_div_cancel₀ _ hr]
    enter [2]
    rw [← mul_pow, mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hr, map_one, one_mul,
      ← map_mul, mul_div_cancel₀ _ hr]
  simp only [C_eq_algebraMap]
  algebra

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  rw [eval_f] at hx
  have := W.Δ_of_isCharNeTwoNF ▸ W.isUnit_Δ |>.ne_zero
  contrapose! this
  linear_combination ((288 * W.a₄ - 96 * W.a₂ ^ 2) * x
      + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) * hx
    + ((32 * W.a₂ ^ 2 - 96 * W.a₄) * x ^ 2 + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * x
      + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) * this

/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma exists_mk_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  conv => enter [1, ξ, 1, l, 1, m]; rw [← map_mul, ← sub_eq_zero, ← map_sub]
  have H (ξ l m : K) : (X - C ξ) * (C r * X ^ 2 + C s * X + C t) - (C l * X + C m) =
      C r * W.f + (C (-ξ * r + s - W.a₂ * r) * X ^ 2 + C (-ξ * s - l - W.a₄ * r + t) * X
        + C (-ξ * t - m - W.a₆ * r)) := by
    simp only [f, C_eq_algebraMap]
    algebra
  conv =>
    enter [1, ξ, 1, l, 1, m]
    rw [H, map_add, map_mul]
    enter [1, 1, 2]
    rw [AdjoinRoot.mk_self]
  simp only [mul_zero, zero_add]
  suffices ∃ ξ l m, -ξ * r + s - W.a₂ * r = 0 ∧ -ξ * s - l - W.a₄ * r + t = 0 ∧
      -ξ * t - m - W.a₆ * r = 0 by
    obtain ⟨ξ, l, m, h₂, h₁, h₀⟩ := this
    refine ⟨ξ, l, m, ?_⟩
    rw [h₂, h₁, h₀]
    simp
  refine ⟨s / r - W.a₂, t - W.a₄ * r - s ^ 2 / r + W.a₂ * s,
    -W.a₆ * r - t * s / r + W.a₂ * t, ?_, ?_, ?_⟩ <;> field

/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

lemma exists_mk_eq' {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le <| Order.lt_succ_iff.mp hp⟩

/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl

lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  have h1 : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  rw [h1, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  rw [isUnit_mk_iff W h]
  have H₀ : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, W.eval_fCofactor_self]; simp
  have H₂ : (AdjoinRoot.mk (W.fCofactor x)) (C x - X + W.fCofactor x) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := AdjoinRoot.mk (W.fCofactor x) <|
    C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))) =
      C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * ·) using
      mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp

end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := Units.modPow W.A 2

/- `inferInstance` succeeds here, but instance search does not find this instance at the use
sites (e.g., for `mul_right_comm` below) unless it is declared. -/
noncomputable instance : CommGroup W.M := inferInstance

lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := Units.modPow.pow_eq_one m

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]

variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of
`x - T` if `f x ≠ 0`, and to the square class of `f' T` otherwise. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dif_pos hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dif_neg hx]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/
private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP -- cannot occur
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl

@[simp]
lemma μ₀_two_nsmul (P : W.Point) : W.μ₀ (2 • P) = 1 := by
  rw [← μ_apply, ofAdd_nsmul, map_pow, M.sq_eq_one]

/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/
private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  have hy₀ : l * ξ + m ≠ 0 := by
    have hΔ := W.isUnit_Δ.ne_zero
    rw [Δ_of_isCharNeTwoNF W] at hΔ
    contrapose! hΔ
    -- the Bézout certificate for `Δ`, evaluated at `ξ`, where `f ξ = (lξ+m)²` and
    -- `f' ξ = 2l(lξ+m)` vanish by `hΔ` and the coefficient identities
    linear_combination
      (((288 * W.a₄ - 96 * W.a₂ ^ 2) * ξ + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) *
          ((l * ξ + m) * hΔ + ξ ^ 2 * H₂ - ξ * H₁ + H₀))
        + (((32 * W.a₂ ^ 2 - 96 * W.a₄) * ξ ^ 2
            + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * ξ
            + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) *
          (2 * l * hΔ + 2 * ξ * H₂ - H₁))
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
    rw [negY_of_isCharNeTwoNF]
    grind
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    simp only [slope_of_Y_ne rfl hy, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
      negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
    rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
    field_simp
    grobner
  have heq : W.Equation ξ (l * ξ + m) := by
    rw [equation_iff_eval_f_eq_sq, eval_f]
    linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity of polynomials. -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ exists_pol_of_eq_two_smul h hP, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
      X ^ 3 - C (l ^ 2 - W.a₂) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
    simp only [f] at H
    convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
  replace H' n := congrArg (fun p ↦ p.coeff n) H'
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
  exact exists_eq_two_smul_of_identities h (by simpa using congrArg (-·) (H' 2))
    (by simpa using H' 1) (by simpa using congrArg (-·) (H' 0))

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity in `W.A`. -/
lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hf := eq_of_dvd_of_natDegree_le_of_leadingCoeff H
      (by rw [natDegree_f]; compute_degree!) (by rw [W.monic_f.leadingCoeff, hmon.leadingCoeff])
    linear_combination -hf

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, hrst⟩ := W.exists_mk_eq z
  rw [hrst] at hz
  have hr : r ≠ 0 := by
    intro rfl
    simp only [map_zero, zero_mul, zero_add, ← map_pow] at hz
    rw [AdjoinRoot.mk_eq_mk_iff_of_degree_lt W.monic_f
      (W.degree_lt_degree_f (by compute_degree!))
      (W.degree_lt_degree_f (by compute_degree!))] at hz
    apply_fun natDegree at hz
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz
    lia
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_eq' (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← hp, ← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hdvd : W.fCofactor x ∣ W.f := ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| hdvd.trans hz
  rw [map_pow, hrs, map_add _ _ (fCofactor ..), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    intro rfl
    rw [map_zero, zero_mul, zero_add, ← map_pow,
      AdjoinRoot.mk_eq_mk_iff_of_degree_lt (W.monic_fCofactor x)
        (W.degree_lt_degree_fCofactor x (by compute_degree!))
        (W.degree_lt_degree_fCofactor x (by compute_degree!))] at hz'
    apply_fun natDegree at hz'
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz'
    lia
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · exact eq_two_smul_of_μ_eq_one_of_eq h hμ hx
  · exact eq_two_smul_of_μ_eq_one_of_ne h hμ hx

end kernel

/-- The kernel of `μ` is exactly `2 • W(K)`. -/
lemma ker_μ_eq : (μ (W := W)).ker = (nsmulAddMonoidHom 2).range.toSubgroup := by
  ext P'
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [MonoidHom.mem_ker, μ_apply, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · match P with
    | 0 => exact fun _ ↦ ⟨0, by simp⟩
    | .some x y h => exact fun hμ ↦ (eq_two_smul_of_μ_eq_one h hμ).imp fun Q hQ ↦ hQ.symm
  · rintro ⟨Q, rfl⟩
    exact μ₀_two_nsmul Q

/-- A criterion for the validity of the weak Mordell-Weil Theorem. -/
lemma finite_index_range_nsmulAddMonoidHom_two_iff :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex ↔ Finite (μ (W := W)).range := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff, ← ker_μ_eq,
    Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (μ (W := W))).symm.toEquiv]
  exact Subgroup.finiteIndex_iff_finite_quotient

/-!
### The `2`-torsion of the group of points

In our situation (`a₁ = a₃ = 0`, so `-(x, y) = (x, -y)`), the `2`-torsion consists of the
origin together with the points `(x, 0)` at the roots of `f`; in particular its order is
the number of roots of `f` in `K` plus one.
-/

/-!
### Step 5: show that `im μ` is contained in the kernel of the norm map.

The norm `Algebra.norm K : W.A →* K` sends units to units, hence induces a homomorphism
`normM : W.M →* Units.modPow K 2` on square classes. We must show `normM ∘ μ = 1`.

Writing `f = (X - θ₁) * (X - θ₂) * (X - θ₃)` over a splitting field, the two cases are:

* if `f x ≠ 0`, then `N (x - θ) = ∏ᵢ (x - θᵢ) = f x = y²`, a square;
* if `f x = 0`, then `N (f' θ) = (f' x)²`, again a square.

Both are instances of `AdjoinRoot.norm_mk_eq_resultant`: the norm of `AdjoinRoot.mk g p` for
monic `g` is the resultant of `g` and `p`. See `norm_mk_C_sub_X` and
`norm_mk_C_sub_X_add_fCofactor` in Step 1 above, which deduce them from it by resultant algebra;
in the second case the factorization `f = fCofactor x * (X - C x)` splits the resultant into two
factors, each equal to `(W.fCofactor x).eval x = f' x`.

`AdjoinRoot.norm_mk_eq_resultant` is proved in `EllipticCurves.Mathlib.Basic`; it is a general fact
about
`AdjoinRoot g` for monic `g` and looks worth upstreaming.
-/

section Step5

end Step5

end WeierstrassCurve.Affine

/-!
## Step 6: `im μ ⊆ A(S,2)`

The right level of generality is: `R` a Dedekind domain, `K = Frac R`, and `E/K` given by a
Weierstrass equation with `a₁ = a₃ = 0`. Everything Step 6 needs — a height-one spectrum,
the `v`-adic
valuations, and unique factorization of fractional ideals — is exactly the Dedekind package.
Number fields are *not* needed until Step 7.

`Mathlib.RingTheory.DedekindDomain.SelmerGroup` already defines, for a Dedekind domain `R` with
fraction field `K`, the group `IsDedekindDomain.selmerGroup : Subgroup (Units.modPow K n)`,
namely the classes whose valuation is `≡ 0 mod n` at every `v ∉ S`. Note that its ambient group
is literally our `Units.modPow K n` (that file has it only as a local notation). So the target
`A(S,2)` should be assembled out of `selmerGroup`s, not defined from scratch.

The obstruction is that `A = AdjoinRoot f` is an étale algebra, not a field, so it has no
`HeightOneSpectrum`. The way around this is the decomposition of `A` into a product of fields,
provided by `EllipticCurves.Mathlib.Basic`: as `f` is separable, `AdjoinRoot.equivPiFactors` gives
`A ≃ₐ[K] ((p : W.f.Factors) → AdjoinRoot p)`, a finite product of finite separable field
extensions of `K` indexed by the monic irreducible factors `p` of `f`, and correspondingly
`AdjoinRoot.modPowEquivPiFactors` gives
`W.M = Units.modPow A 2 ≃* ((p : W.f.Factors) → Units.modPow (AdjoinRoot p) 2)`.
Each factor carries `Field`, `Algebra K` and `FiniteDimensional K` instances, and
`Polynomial.Factors.separable` supplies separability.

With that in hand:

* for each factor, `ringOfIntegersFactor R p := integralClosure R (AdjoinRoot p)` is again a
  Dedekind domain (`IsIntegralClosure.isDedekindDomain`, applicable thanks to
  `AdjoinRoot.isSeparable_of_separable`) with fraction field `AdjoinRoot p`, so
  `IsDedekindDomain.selmerGroup` applies to it;
* `A(S,2)` (`selmerGroupA`) is the preimage under the above isomorphism of the product of the
  `selmerGroupFactor R p`, the `2`-Selmer groups relative to the primes above `S`;
* the containment `im μ ⊆ A(S,2)` is checked factor by factor: for `P = (x, y)` and `w` a prime
  of `ringOfIntegersFactor R p` not above `S`, the valuation `w (x - θ)` is even, where `θ` is
  the root of `p`. If `x` has a pole at `w`, the leading term of the cubic dominates and
  `w (x - θ) = w x = w (y / x) ^ 2`. If `x` is `w`-integral, one uses the factorization
  `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over the factor `K[X]/(p)`
  itself: the cofactor
  is congruent to `f' θ` modulo `x - θ`, and `f' θ` is a `w`-unit because `w ∤ Δ`. So either
  `x - θ` is a `w`-unit, or the cofactor is, and then `w (x - θ) = w y ^ 2`.

Step 7 (finiteness of `A(S,2)`) then reduces to finiteness of the `2`-Selmer group of each
factor, which needs the primes above `S` to be finite in number, the class group of
`ringOfIntegersFactor R p` to be finite, and its unit group to be finitely generated — i.e.
number fields. Mathlib lists finiteness of `selmerGroup` as a TODO.

Note that the valuation computation stays inside the single field factor `K[X]/(p)`; no
splitting field is needed. That `f' θ` is a unit at every good prime
(`valuation_deriv_root_eq_one`) needs exactly that the coefficients of the cubic are integral
and `disc f` is a unit there — which is what `Δ ∈ badPrimes` buys, via the Bézout identity
behind `separable_f`.

All of this is carried out below: `badPrimes` (`S`) and its finiteness,
`AdjoinRoot.isSeparable_of_separable` (so that `IsIntegralClosure.isDedekindDomain` applies to
each factor), `IsDedekindDomain.HeightOneSpectrum.primesAbove` (the `S i`),
`IsDedekindDomain.selmerGroupAbove`, `selmerGroupA` (`A(S,2)`, as a subgroup of `W.M`), and
finally `range_μ_le_selmerGroupA`.
-/

section Cubic

/- Specializations of `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`
from `EllipticCurves.Mathlib.Basic` to the monic cubic `t ^ 3 + a * t ^ 2 + b * t + c`. They are
specific to Weierstrass equations, so they live here rather than in the general-support file. -/

open Polynomial

variable {L Γ : Type*} [CommRing L] [Nontrivial L] [LinearOrderedCommGroupWithZero Γ]
  (ν : Valuation L Γ) {t a b c : L}

private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      ν ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

private lemma Valuation.map_cubic_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb hc) ht
  rw [hdeg] at h
  simpa using h

private lemma Valuation.le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb hc) (by rw [hdeg]; norm_num) ?_
  simpa using heq

end Cubic

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

-- Step 6 needs neither `DecidableEq K` (except where the `x - T` map `μX` enters at the very
-- end) nor the group structure on points, so we re-declare the variables rather than
-- inheriting the ones used for Steps 2-5.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to Step 6: for a monic irreducible factor `p` of `f`, `𝕃 p` is the field
factor `K[X]/(p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding, and `θ p` is the
image of the root `T` of `f` in `𝕃 p`. -/

/-- The set of "bad" primes of `R`: those dividing `2` or the discriminant of `W`, and those
occurring in a denominator of `a₂`, `a₄` or `a₆` (the latter three are the supports of the
coefficients in the sense of `IsDedekindDomain.HeightOneSpectrum.Support`). Away from these,
the `x - T` map lands in the `2`-Selmer group. -/
def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- There are only finitely many bad primes: `2` and `W.Δ` are nonzero, and the support of any
element of `K` is finite. -/
lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes R).Finite :=
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two W)
  ((((HeightOneSpectrum.finite_setOf_valuation_ne_one h2).union
    (HeightOneSpectrum.finite_setOf_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₂)).union
        (HeightOneSpectrum.Support.finite R W.a₄)).union
          (HeightOneSpectrum.Support.finite R W.a₆)

section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}

lemma valuation_a₂_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inl (.inr hlt)))

lemma valuation_a₄_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inr hlt))

lemma valuation_a₆_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inr hlt)

lemma valuation_Δ_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.Δ = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inr hne))))

lemma valuation_two_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K 2 = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inl hne))))

/-- Away from the bad primes, `disc f` is a `v`-adic unit: `Δ = 16 · disc f`, and both `Δ`
and `2` are `v`-adic units. -/
lemma valuation_discr_eq_one_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    v.valuation K W.f.discr = 1 := by
  have h16 : v.valuation K 16 = 1 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num, map_pow,
      W.valuation_two_eq_one_of_notMem_badPrimes R hv, one_pow]
  have hΔ := W.valuation_Δ_eq_one_of_notMem_badPrimes R hv
  rwa [W.Δ_eq_discr_f, map_mul, h16, one_mul] at hΔ

end BadPrimes

section DerivativeUnit

/- `f'(x)` is a unit at a rational root `x` of `f` whenever the coefficients are integral and
the valuation of `disc f` is `1` or `exp (-1)`: this is the arithmetic input for the
`2`-torsion `x - T` representative, both at good primes and at primes with
`v(disc f) = exp (-1)`. -/

open WithZero in
private lemma eq_one_of_le_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1)
    (h2 : exp (-1) ≤ t ^ 2) : t = 1 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h2
  rw [← exp_log ht0] at h1 h2 ⊢
  rw [← exp_nsmul, two_nsmul] at h2
  rw [← exp_zero] at h1
  rw [exp_eq_one]
  have h1' := exp_le_exp.mp h1
  have h2' := exp_le_exp.mp h2
  lia

open WithZero in
/-- If `x` is a rational root of `f` and the coefficients of the cubic are `ν`-integral with
`exp (-1) ≤ ν (disc f)`, then `f'(x)` is a `ν`-unit: `disc f = (fCofactor x).discr * f'(x)²`
with both factors integral, and the square `ν (f'(x))²` cannot equal `exp (-1)`. -/
lemma valuation_deriv_eval_eq_one (ν : Valuation K ℤᵐ⁰) {x : K} (hx : W.f.eval x = 0)
    (ha₂ : ν W.a₂ ≤ 1) (ha₄ : ν W.a₄ ≤ 1) (ha₆ : ν W.a₆ ≤ 1)
    (hd : exp (-1) ≤ ν W.f.discr) :
    ν (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 := by
  have hx1 : ν x ≤ 1 := by
    rw [eval_f] at hx
    exact ν.le_one_of_root_cubic ha₂ ha₄ ha₆ hx
  have hfx : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∈ ν.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) ha₂) hx1)) ha₄
  have hcd' : (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) ∈ ν.integer :=
    sub_mem (pow_mem (add_mem hx1 ha₂) 2) (mul_mem (ofNat_mem _ 4)
      (add_mem (add_mem (pow_mem hx1 2) (mul_mem ha₂ hx1)) ha₄))
  have hcd : ν (W.fCofactor x).discr ≤ 1 := by rw [W.discr_fCofactor x]; exact hcd'
  rw [W.discr_f_eq_discr_fCofactor_mul_sq hx, map_mul, map_pow] at hd
  exact eq_one_of_le_one_of_exp_neg_one_le_sq hfx (hd.trans (mul_le_of_le_one_left' hcd))

end DerivativeUnit

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The ring of integers of the field factor `K[X]/(p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R ((AdjoinRoot (p : K[X])))

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure
of `R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K ((AdjoinRoot (p : K[X]))) _

/-- A field factor is the fraction field of its ring of integers. -/
instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) ((AdjoinRoot (p : K[X]))) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K ((AdjoinRoot (p : K[X]))) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R ((AdjoinRoot (p : K[X])))) := by
    rw [IsScalarTower.algebraMap_eq R K ((AdjoinRoot (p : K[X])))]
    exact ((algebraMap K (AdjoinRoot (p : K[X])))).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)

/-- The `w`-adic valuation of an element of `K` is the `v`-adic valuation of the prime `v`
below `w`, raised to the ramification index. -/
lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (w.below R).valuation K z ^ ((w.below R).asIdeal.ramificationIdx' w.asIdeal) =
      w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) z) :=
  HeightOneSpectrum.valuation_liesOver _ _ _ z

/-- If `z` is integral at the prime below `w`, then it is integral at `w`. -/
lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (w.below R).valuation K z ≤ 1) :
    w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _

/-- A prime `w` of the ring of integers of a field factor that does not lie above `S` lies
over a prime of `R` outside `S`. -/
lemma below_notMem_of_notMem_primesAbove [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    {S : Set (HeightOneSpectrum R)} {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) : w.below R ∉ S :=
  fun hv ↦ hw ((HeightOneSpectrum.mem_primesAbove_iff R _ _ w).mpr hv)

/-- `θ` satisfies the Weierstrass cubic in the field factor `K[X]/(p)`. -/
lemma root_cubic_eq_zero (p : W.f.Factors) :
    (AdjoinRoot.root (p : K[X])) ^ 3 + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) ^ 2 + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 :=
    AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz

/-- The Bézout identity behind `separable_f` at the level of `disc f`, evaluated at `θ`:
`f′(θ)` times an explicit quadratic in `θ` with integral coefficients equals `disc f`.
(The classical identity with `Δ` on the right is `16` times this one; this version stays
useful at even places.) -/
lemma deriv_root_mul_eq_discr_f (p : W.f.Factors) :
    (3 * (AdjoinRoot.root (p : K[X])) ^ 2 + 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄)
        * ((2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 2 - 6 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) * (AdjoinRoot.root (p : K[X])) ^ 2
          + (2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 3 - 7 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ + 9 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆) * (AdjoinRoot.root (p : K[X]))
          + ((algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ - 4 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ ^ 2 + 3 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆)) =
      (algebraMap K (AdjoinRoot (p : K[X]))) W.f.discr := by
  have hd : (algebraMap K (AdjoinRoot (p : K[X]))) W.f.discr = (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ ^ 2 - 4 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ ^ 3
      - 4 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 3 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆ - 27 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆ ^ 2
      + 18 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆ := by
    rw [W.discr_f]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  rw [hd]
  linear_combination (-(18 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ - 6 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 2) * (AdjoinRoot.root (p : K[X]))
    - (15 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ - 4 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ ^ 3 - 27 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₆)) * W.root_cubic_eq_zero p

/-- The cofactor `f / (X - x)`, computed in the field factor `K[X]/(p)`. -/
lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      (AdjoinRoot.root (p : K[X])) ^ 2 + ((algebraMap K (AdjoinRoot (p : K[X]))) x + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂) * (AdjoinRoot.root (p : K[X])) + ((algebraMap K (AdjoinRoot (p : K[X]))) x ^ 2 + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X]))) x + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1) (hd : (w.below R).valuation K W.f.discr = 1)
  -- (this is `w.valuation ((AdjoinRoot (p : K[X]))) (3 * (AdjoinRoot.root (p : K[X])) ^ 2 + 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include ha₂ ha₄ ha₆ in
/-- If the coefficients of the cubic are integral at the prime below `w`, then the root `θ` is
`w`-integral: it satisfies the monic cubic `f`, whose coefficients are integral at `w`. -/
lemma valuation_root_le_one : w.valuation ((AdjoinRoot (p : K[X]))) ((AdjoinRoot.root (p : K[X]))) ≤ 1 :=
  Valuation.le_one_of_root_cubic _
    (W.valuation_algebraMap_le_one R p w ha₂)
    (W.valuation_algebraMap_le_one R p w ha₄)
    (W.valuation_algebraMap_le_one R p w ha₆)
    (W.root_cubic_eq_zero p)

/-- An element of `K` with trivial valuation at the prime below `w` has trivial valuation
at `w`. -/
lemma valuation_algebraMap_eq_one {z : K} (hz : (w.below R).valuation K z = 1) :
    w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

include ha₂ ha₄ ha₆ in
/-- If the coefficients of the cubic are integral at the prime below `w`, then `f' θ` is
`w`-integral. -/
lemma valuation_deriv_root_le_one :
    w.valuation ((AdjoinRoot (p : K[X]))) (3 * (AdjoinRoot.root (p : K[X])) ^ 2 + 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) ≤ 1 := by
  have ht := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h : 3 * (AdjoinRoot.root (p : K[X])) ^ 2 + 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄ ∈ (w.valuation ((AdjoinRoot (p : K[X])))).integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem ht 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) (W.valuation_algebraMap_le_one R p w ha₂)) ht))
      (W.valuation_algebraMap_le_one R p w ha₄)
  exact h

include ha₂ ha₄ ha₆ hd in
/-- If the coefficients of the cubic are integral and `disc f` is a unit at the prime below
`w`, then `f' θ = 3 θ ^ 2 + 2 a₂ θ + a₄` is a `w`-unit.

Evaluating the Bézout identity behind `separable_f` at `θ` gives `f'(θ) * c(θ) = disc f`
(`deriv_root_mul_eq_discr_f`) for an explicit quadratic `c` with `w`-integral coefficients.
Both factors are integral at `w` and the product is a unit, so both are units. -/
lemma valuation_deriv_root_eq_one :
    w.valuation ((AdjoinRoot (p : K[X]))) (3 * (AdjoinRoot.root (p : K[X])) ^ 2 + 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) = 1 := by
  set L := (AdjoinRoot (p : K[X]))
  set ν := w.valuation L
  set t := (AdjoinRoot.root (p : K[X]))
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  set B := algebraMap K L W.a₆
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- both factors in `deriv_root_mul_eq_discr_f` are integral, and their product is a unit
  have hD : ν (3 * t ^ 2 + 2 * A₂ * t + A) ≤ 1 :=
    W.valuation_deriv_root_le_one R p ha₂ ha₄ ha₆
  have hC : (2 * A₂ ^ 2 - 6 * A) * t ^ 2 + (2 * A₂ ^ 3 - 7 * A₂ * A + 9 * B) * t
      + (A₂ ^ 2 * A - 4 * A ^ 2 + 3 * A₂ * B) ∈ ν.integer := by
    refine add_mem (add_mem (mul_mem ?_ (pow_mem ht 2)) (mul_mem ?_ ht)) ?_
    · exact sub_mem (mul_mem (ofNat_mem _ 2) (pow_mem hA₂ 2)) (mul_mem (ofNat_mem _ 6) hA)
    · exact add_mem (sub_mem (mul_mem (ofNat_mem _ 2) (pow_mem hA₂ 3))
        (mul_mem (mul_mem (ofNat_mem _ 7) hA₂) hA)) (mul_mem (ofNat_mem _ 9) hB)
    · exact add_mem (sub_mem (mul_mem (pow_mem hA₂ 2) hA)
        (mul_mem (ofNat_mem _ 4) (pow_mem hA 2))) (mul_mem (mul_mem (ofNat_mem _ 3) hA₂) hB)
  refine ν.eq_one_of_mul_eq_one hD hC ?_
  rw [deriv_root_mul_eq_discr_f]
  exact W.valuation_algebraMap_eq_one R p hd

include ha₂ ha₄ ha₆ hderiv in
/-- If the coefficients of the cubic are integral at the prime below `w` and `f' θ` is a
`w`-unit, and if `x` is `w`-integral and `x - θ` is not a `w`-unit, then the cofactor
`x ^ 2 + (AdjoinRoot.root (x : K[X])) + θ ^ 2 + a₂ (x + θ) + a₄` is a `w`-unit: modulo `x - θ` it equals `f' θ`. -/
lemma valuation_cofactor_eq_one {x : K}
    (hx : w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x) ≤ 1)
    (hlt : w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x - (AdjoinRoot.root (p : K[X]))) < 1) :
    w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x ^ 2 + (AdjoinRoot.root (p : K[X])) * (algebraMap K (AdjoinRoot (p : K[X]))) x + (AdjoinRoot.root (p : K[X])) ^ 2
      + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * ((algebraMap K (AdjoinRoot (p : K[X]))) x + (AdjoinRoot.root (p : K[X]))) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) = 1 := by
  set L := (AdjoinRoot (p : K[X]))
  set ν := w.valuation L
  set t := (AdjoinRoot.root (p : K[X]))
  set s := algebraMap K L x
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  have h2t : s + 2 * t + A₂ ∈ ν.integer :=
    add_mem (add_mem hx (mul_mem (ofNat_mem _ 2) ht)) hA₂
  have hlt' : ν ((s - t) * (s + 2 * t + A₂)) < ν (3 * t ^ 2 + 2 * A₂ * t + A) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [show s ^ 2 + t * s + t ^ 2 + A₂ * (s + t) + A
      = (s - t) * (s + 2 * t + A₂) + (3 * t ^ 2 + 2 * A₂ * t + A) by ring,
    ν.map_add_eq_of_lt_right hlt', hderiv]

include ha₂ ha₄ ha₆ in
/-- If `x` is a root of `f`, then at a prime `w` at which (i.e. at the prime of `R` below
which) the coefficients of the cubic are integral and `f'(x)` is a unit, the `p`-component of
the `x - T` representative is a unit.

Both `x` and `θ` are roots of `f`, so `x - θ` times the cofactor is `0` and, `L` being a field,
one of the two factors vanishes. If `x = θ` the component is `f'(x)`; if the cofactor vanishes
the component is `x - θ` and `f'(x) = (x - θ)(2x + θ + a₂)`. Either way `hdx` makes it a unit.

At a good prime, `hdx` is supplied by `valuation_deriv_eval_eq_one`; at an odd prime with
`v(disc f) = exp (-1)` the same lemma applies, so the `2`-torsion representative is unramified
there as well. -/
lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hdx : (w.below R).valuation K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1) :
    w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x - (AdjoinRoot.root (p : K[X])) + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  set L := (AdjoinRoot (p : K[X]))
  set ν := w.valuation L
  set t := (AdjoinRoot.root (p : K[X]))
  set s := algebraMap K L x with hsdef
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  set B := algebraMap K L W.a₆ with hBdef
  have hA₂ : ν A₂ ≤ 1 := W.valuation_algebraMap_le_one R p w ha₂
  have hA : ν A ≤ 1 := W.valuation_algebraMap_le_one R p w ha₄
  have hB : ν B ≤ 1 := W.valuation_algebraMap_le_one R p w ha₆
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- the `w`-unit `f'(x)`, transported to `L`
  have hderiv : ν (3 * s ^ 2 + 2 * A₂ * s + A) = 1 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat]
      using W.valuation_algebraMap_eq_one R p (w := w) hdx
  -- `x` is a root of the cubic too, hence integral at `w`
  have hs : s ^ 3 + A₂ * s ^ 2 + A * s + B = 0 := by
    rw [hsdef, hA₂def, hAdef, hBdef, ← W.map_eval_f, hx, map_zero]
  have hs1 : ν s ≤ 1 := ν.le_one_of_root_cubic hA₂ hA hB hs
  have hprod : (s - t) * (t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)) = 0 := by
    linear_combination hs - W.root_cubic_eq_zero p
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `x = θ`: the component is `f'(x)`
    rw [h0, zero_add, show t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)
        = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -(t + 2 * s + A₂) * h0, hderiv]
  · -- the cofactor vanishes: the component is `x - θ`, and `f'(x) = (x - θ)(2x + θ + a₂)`
    rw [h0, add_zero]
    have hst : s - t ∈ ν.integer := sub_mem hs1 ht
    have h2t : 2 * s + t + A₂ ∈ ν.integer :=
      add_mem (add_mem (mul_mem (ofNat_mem _ 2) hs1) ht) hA₂
    refine ν.eq_one_of_mul_eq_one hst h2t ?_
    rw [show (s - t) * (2 * s + t + A₂) = 3 * s ^ 2 + 2 * A₂ * s + A by linear_combination -h0,
      hderiv]

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1)
  -- (this is `w.valuation ((AdjoinRoot (p : K[X]))) (3 * (AdjoinRoot.root (p : K[X])) ^ 2 + 2 * (algebraMap K (AdjoinRoot (p : K[X]))) W.a₂ * (AdjoinRoot.root (p : K[X])) + (algebraMap K (AdjoinRoot (p : K[X]))) W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu ha₂ ha₄ ha₆

/-- Non-integral case: `x` has a pole at the prime of `R` below `w`.

The coefficients `a₂`, `a₄`, `a₆` and the root `θ` are `w`-integral, so `1 < ν x` makes the
leading term of the cubic dominate: `ν (f x) = ν x ^ 3`, hence `ν y ^ 2 = ν x ^ 3`. Also
`ν θ ≤ 1 < ν x`
gives `ν (x - θ) = ν x`. Therefore `ν (x - θ) = ν (y / x) ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := (AdjoinRoot (p : K[X]))
  set ν := w.valuation L
  have hx0 : algebraMap K L x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx'
    exact absurd hx' (by simp)
  have hx0' : ν (algebraMap K L x) ≠ 0 := ν.ne_zero_iff.mpr hx0
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  -- the Weierstrass equation, transported to `L`
  have heq : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hval : ν (algebraMap K L y) ^ 2 = ν (algebraMap K L x) ^ 3 := by
    rw [← map_pow, heq, ν.map_cubic_of_one_lt (W.valuation_algebraMap_le_one R p w ha₂)
      (W.valuation_algebraMap_le_one R p w ha₄) (W.valuation_algebraMap_le_one R p w ha₆) hx']
  -- `ν (x - θ) = ν x`, since `θ` is integral and `x` is not
  have hu' : ν (u : L) = ν (algebraMap K L x) := by
    rw [hu]
    exact Valuation.map_sub_eq_of_lt_left _ ((W.valuation_root_le_one R p ha₂ ha₄ ha₆).trans_lt hx')
  have hkey : ν (u : L) = ν ((Units.mk0 _ (div_ne_zero hy0 hx0) : Lˣ) : L) ^ 2 := by
    rw [hu', Units.val_mk0, map_div₀, div_pow, hval, eq_div_iff (pow_ne_zero 2 hx0'), mul_comm]
    exact (pow_succ _ 2).symm
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- Integral case: `x` is integral at the prime of `R` below `w`.

Over `L` the Weierstrass equation factors as `y ^ 2 = (x - θ) * c` with cofactor
`c = x ^ 2 + (AdjoinRoot.root (x : K[X])) + θ ^ 2 + a₂ (x + θ) + a₄`. If `x - θ` is a `w`-unit there is nothing to do.
Otherwise `ν (x - θ) < 1`, and since `c = (x - θ) * (x + 2 θ + a₂) + f' θ` with `f' θ` a
`w`-unit, the cofactor is a `w`-unit. Hence `ν (x - θ) = ν y ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := (AdjoinRoot (p : K[X]))
  set ν := w.valuation L
  set t := (AdjoinRoot.root (p : K[X]))
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p ha₂ ha₄ ha₆
  -- `y ^ 2 = (x - θ) * (x ^ 2 + (AdjoinRoot.root (x : K[X])) + θ ^ 2 + a₂ (x + θ) + a₄)` over `L`
  have heqL : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 + A₂ * algebraMap K L x ^ 2 +
      A * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [hA₂def, hAdef, ← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (u : L) * (algebraMap K L x ^ 2 + t * algebraMap K L x + t ^ 2
        + A₂ * (algebraMap K L x + t) + A) =
      (algebraMap K L y) ^ 2 := by
    rw [hu]
    linear_combination -W.root_cubic_eq_zero p - heqL
  have hu1 : ν (u : L) ≤ 1 := by rw [hu]; exact ν.map_sub_le hx' ht
  by_cases hlt : ν (u : L) = 1
  · -- `x - θ` is a unit, so its valuation is trivially even
    have hkey : ν (u : L) = ν ((1 : Lˣ) : L) ^ 2 := by rw [Units.val_one, map_one, one_pow, hlt]
    simpa using w.dvd_toAdd_valuationOfNeZero hkey
  -- otherwise `w` divides `x - θ`, and then it cannot divide the cofactor
  replace hlt : ν (u : L) < 1 := lt_of_le_of_ne hu1 hlt
  rw [hu] at hlt
  have hcof : ν (algebraMap K L x ^ 2 + t * algebraMap K L x + t ^ 2
      + A₂ * (algebraMap K L x + t) + A) = 1 :=
    W.valuation_cofactor_eq_one R p ha₂ ha₄ ha₆ hderiv hx' hlt
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have hkey : ν (u : L) = ν ((Units.mk0 _ hy0 : Lˣ) : L) ^ 2 := by
    rw [Units.val_mk0, ← map_pow, ← hfac, map_mul, hcof, mul_one]
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- The arithmetic core of Step 6, generic case, with all the group theory stripped away:
for `(x, y)` on `W` with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor
`K[X]/(p)` such that the coefficients of the cubic are integral at the prime of `R` below `w`
and `f' θ` is a `w`-unit, the `w`-adic valuation of `x - θ` is even.

The proof splits on whether `x` has a pole at the prime of `R` below `w`. -/
lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation ((AdjoinRoot (p : K[X]))) ((algebraMap K (AdjoinRoot (p : K[X]))) x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w ha₂ ha₄ ha₆ hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w ha₂ ha₄ ha₆ hderiv
      (not_lt.mp hx')

end Core

section Selmer

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- The image of the generic `x - T` representative in the field factor `K[X]/(p)` is `x - θ`. -/
lemma projFactor_mk_C_sub_X (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p (AdjoinRoot.mk W.f (C x - X)) =
      (algebraMap K (AdjoinRoot (p : K[X]))) x - (AdjoinRoot.root (p : K[X])) := by
  rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

/-- The image of the `2`-torsion `x - T` representative in the field factor `K[X]/(p)`. -/
lemma projFactor_mk_C_sub_X_add_fCofactor (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p
        (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) =
      (algebraMap K (AdjoinRoot (p : K[X]))) x - (AdjoinRoot.root (p : K[X])) + AdjoinRoot.mk (p : K[X]) (W.fCofactor x) := by
  rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))

/-- The `2`-Selmer group of the field factor `AdjoinRoot p` of `W.A`, relative to the primes of
its ring of integers lying above the primes in `S`. -/
noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup (Units.modPow ((AdjoinRoot (p : K[X]))) 2) :=
  IsDedekindDomain.selmerGroupAbove R (W.ringOfIntegersFactor R p) ((AdjoinRoot (p : K[X]))) S 2

/-- `A(S,2)` in the product decomposition: the product of the `2`-Selmer groups of the field
factors of `W.A`. -/
noncomputable def selmerGroupPi :
    Subgroup ((p : W.f.Factors) → Units.modPow ((AdjoinRoot (p : K[X]))) 2) :=
  Subgroup.pi Set.univ (W.selmerGroupFactor R S)

/-- `A(S,2)`, as a subgroup of `W.M`: the classes whose image in each field factor lies in the
`2`-Selmer group of that factor. Step 6 asserts that `im μ ≤ A(S,2)` for `S` the bad primes. -/
noncomputable def selmerGroupA : Subgroup W.M :=
  (W.selmerGroupPi R S).comap
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).toMonoidHom

lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R S ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R S p := by
  simp [selmerGroupA, selmerGroupPi, Subgroup.mem_pi]

/-!
#### The arithmetic input

Write `θ` for `AdjoinRoot.root p`, the image of the root `T` in the field factor `K[X]/(p)`,
and `𝓞` for the integral closure of `R` in `K[X]/(p)`, a Dedekind domain by
`isDedekindDomain_ringOfIntegersFactor` (an instance, in the `RingOfIntegers` section above).

The `p`-component of `μX x` is the square class of the reduction mod `p` of the `x - T`
representative, computed by `projFactor_mk_C_sub_X` and
`projFactor_mk_C_sub_X_add_fCofactor` below: it is `x - θ` in the generic case and
`x - θ + fCofactor x` when `x` is a root of `f`.

What has to be shown is that this class lies in the `2`-Selmer group of `K[X]/(p)`, i.e. that
`w (x - θ)` is even for every prime `w` of `𝓞` not lying above a prime of `S`; away from `S`,
the coefficients of the cubic are integral and `disc f` is a unit, by hypothesis.
The two cases are split off as `mem_selmerGroupFactor_of_eval_f_ne_zero` and
`mem_selmerGroupFactor_of_eval_f_eq_zero`.
-/

/-- Membership of the class of a unit in the `2`-Selmer group of a field factor: its valuation
is even at every prime of the ring of integers not lying above `S`. -/
lemma mem_selmerGroupFactor_unit_iff (p : W.f.Factors) (u : ((AdjoinRoot (p : K[X])))ˣ) :
    (QuotientGroup.mk u : Units.modPow ((AdjoinRoot (p : K[X]))) 2) ∈ W.selmerGroupFactor R S p ↔
      ∀ w : HeightOneSpectrum (W.ringOfIntegersFactor R p),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) :=
  forall₂_congr fun w _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff w 2 u

variable (hSa₂ : ∀ v ∉ S, v.valuation K W.a₂ ≤ 1) (hSa₄ : ∀ v ∉ S, v.valuation K W.a₄ ≤ 1)
  (hSa₆ : ∀ v ∉ S, v.valuation K W.a₆ ≤ 1) (hSd : ∀ v ∉ S, v.valuation K W.f.discr = 1)

include hSa₂ hSa₄ hSa₆ hSd in
/-- Generic case of the arithmetic input: `f x ≠ 0`, so the `p`-component of `μX x` is the class
of `x - θ`. -/
lemma mem_selmerGroupFactor_of_eval_f_ne_zero {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow ((AdjoinRoot (p : K[X]))) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  refine W.even_valuationOfNeZero_sub_root R p h hx _ ?_ w (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv)
    (W.valuation_deriv_root_eq_one R p (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) (hSd _ hv))
  exact W.projFactor_mk_C_sub_X x p

include hSa₂ hSa₄ hSa₆ hSd in
/-- `2`-torsion case of the arithmetic input: `f x = 0`.

By `projFactor_mk_C_sub_X_add_fCofactor` the `p`-component of `μX x` is `x - θ + fCofactor x`,
which by `valuation_projFactor_torsion_eq_one` is a unit at every prime `w` not lying above
`S`. Its valuation is therefore `0`, in particular even. -/
lemma mem_selmerGroupFactor_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0)
    (p : W.f.Factors) :
    (((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow ((AdjoinRoot (p : K[X]))) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  set u := ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit with hudef
  have hd1 : WithZero.exp (-1 : ℤ) ≤ (w.below R).valuation K W.f.discr := by
    rw [hSd _ hv]
    exact (WithZero.exp_le_exp.mpr (by lia)).trans_eq WithZero.exp_zero
  have hval : w.valuation ((AdjoinRoot (p : K[X]))) (u : (AdjoinRoot (p : K[X]))) = 1 := by
    rw [hudef, IsUnit.unit_spec, W.projFactor_mk_C_sub_X_add_fCofactor x p]
    exact W.valuation_projFactor_torsion_eq_one R p (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) hx
      (W.valuation_deriv_eval_eq_one _ hx (hSa₂ _ hv) (hSa₄ _ hv) (hSa₆ _ hv) hd1)
  simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1) (by simp [hval])

section

variable [DecidableEq K]

include hSa₂ hSa₄ hSa₆ hSd in
/-- The heart of Step 6: for a point `(x, y)` of `W` and a field factor `K[X]/(p)` of `W.A`,
the square class of the image of the `x - T` map lies in the `2`-Selmer group of that factor. -/
lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R S p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R S hSa₂ hSa₄ hSa₆ hSd hx p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_ne_zero R S hSa₂ hSa₄ hSa₆ hSd h hx p

include hSa₂ hSa₄ hSa₆ hSd in
/-- **Step 6**: the image of `μ` is contained in `A(S,2)`, whenever the coefficients of the
cubic are integral and `disc f` is a unit away from `S`. -/
theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R S := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R S hSa₂ hSa₄ hSa₆ hSd h.1 p

end

/-!
### Step 7: `A(S,2)` is finite, hence `E(K)/2E(K)` is finite

The finiteness of the `2`-Selmer group of each field factor is
`IsDedekindDomain.finite_selmerGroup` from `EllipticCurves.Mathlib.SelmerGroup`. It requires the
class group
of the factor's ring of integers to be finite and its unit group to be finitely generated;
these are taken as hypotheses here (for `K` a number field they are the class number theorem
and Dirichlet's unit theorem). The relevant set of primes, those above `S`, is finite by
`HeightOneSpectrum.primesAbove_finite` whenever `S` is. -/

section Step7

variable [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
  [(p : W.f.Factors) → Group.FG (W.ringOfIntegersFactor R p)ˣ]

/-- The `2`-Selmer group of each field factor of `W.A` is finite, for a finite set `S`. -/
theorem finite_selmerGroupFactor (hS : S.Finite) (p : W.f.Factors) :
    Finite (W.selmerGroupFactor R S p) :=
  finite_selmerGroup (W.ringOfIntegersFactor R p) ((AdjoinRoot (p : K[X])))
    (HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) 2
    (HeightOneSpectrum.primesAbove_finite R (W.ringOfIntegersFactor R p) hS)

/-- **Step 7**: `A(S,2)` is finite, for a finite set `S`. -/
theorem finite_selmerGroupA (hS : S.Finite) : Finite (W.selmerGroupA R S) := by
  have := Polynomial.Factors.finite W.f_ne_zero
  have (p : W.f.Factors) : Finite (W.selmerGroupFactor R S p) :=
    W.finite_selmerGroupFactor R S hS p
  have : Finite (W.selmerGroupPi R S) := Subgroup.instFinitePi
  exact Subgroup.finite_comap_of_injective
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).injective (W.selmerGroupPi R S)

variable [DecidableEq K]

include R in
/-- **The Weak Mordell-Weil Theorem**: `E(K)/2E(K)` is finite, for an elliptic curve `E` in
the normal form `y² = x³ + a₂x² + a₄x + a₆` over the fraction field `K` of a Dedekind domain
`R` such that for each irreducible factor `p` of the cubic, the ring of integers of
`K[X]/(p)` has finite class group and finitely generated unit group.

This is the input to the descent argument (`AddCommGroup.fg_of_descent'`) in the proof of the
Mordell-Weil theorem, `fg_point` in `EllipticCurves.MordellWeil`. -/
theorem finite_index_range_nsmulAddMonoidHom_two :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex := by
  rw [finite_index_range_nsmulAddMonoidHom_two_iff]
  have := W.finite_selmerGroupA R (W.badPrimes R) (W.finite_badPrimes R)
  exact ((W.selmerGroupA R (W.badPrimes R) : Set W.M).toFinite.subset
    (W.range_μ_le_selmerGroupA R (W.badPrimes R)
      (fun _ hv ↦ W.valuation_a₂_le_one_of_notMem_badPrimes R hv)
      (fun _ hv ↦ W.valuation_a₄_le_one_of_notMem_badPrimes R hv)
      (fun _ hv ↦ W.valuation_a₆_le_one_of_notMem_badPrimes R hv)
      (fun _ hv ↦ W.valuation_discr_eq_one_of_notMem_badPrimes R hv))).to_subtype

end Step7

end Selmer

end WeierstrassCurve.Affine

end
/- ===== end EllipticCurves/WeakMordellWeil.lean ===== -/

/- ===== begin EllipticCurves/MordellWeil.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-!
# The Mordell-Weil Theorem

The goal of this file is the **Mordell-Weil Theorem**: the group `E(K)` of `K`-rational
points of an elliptic curve `E` over a number field `K` is finitely generated. It comes in
three versions:

* `fg_point`: for `E` given by an equation `y² = x³ + a₂x² + a₄x + a₆` (that is, with
  `a₁ = a₃ = 0`) over the fraction field `K` of a Dedekind domain, where `K` has admissible
  absolute values satisfying the Northcott property and the needed class-group and unit-group
  finiteness statements are taken as hypotheses;
* `fg_point_of_variableChange`: for an arbitrary `E` over such a `K` with `2` invertible,
  by completing the square and transferring along the isomorphism of point groups from
  `EllipticCurves.VariableChange`;
* `fg_point_of_numberField`: for an arbitrary `E` over a number field, where all hypotheses
  are theorems.

The proof is by descent (`AddCommGroup.fg_of_descent'`, in Mathlib): the Weak Mordell-Weil
Theorem of `EllipticCurves.WeakMordellWeil` provides the finiteness of `E(K)/2E(K)`,
and the naïve height `h(P) = logHeight (x(P))` provides the required height function. The
main technical step on the way, and the bulk of this file, is the *approximate parallelogram
law* `∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`
(`approx_parallelogram_law`), proved via the addition-and-multiplication map on
`x`-coordinates and the bounds on heights of images under tuples of homogeneous polynomials.
Together with the Northcott property it also yields the
finiteness of sets of points of bounded naïve height (`finite_naiveLogHeight_le`) and of the
torsion subgroup of `E(K)` (`finite_torsion`).
-/

/-
We work with affine points; this seems to be quite a bit less painful
than using projective points.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

/-!
### `sym2x` and the addition-and-multiplication map

We show that the following diagram commutes.

```
  Sym² W ∋ {P, Q} ↦ {P+Q, P-Q} ∈ Sym² W
     ↓ sym2x                        ↓ sym2x
     ℙ²       - addSubMap -→        ℙ²
```

Here `W` is an arbitrary Weierstrass curve; the formulas are expressed in terms of the
`b`-invariants `b₂, b₄, b₆, b₈`.
-/

--#40303

open MvPolynomial Nat

lemma den_duplication_eq {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have Heq := (W'.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq

lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔ y = W'.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only

variable {F : Type*} [Field F] {W : Affine F}

lemma den_duplication_ne_zero_or_num_duplication_ne_zero {x y : F} (h : W.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
  rw [equation_iff x y] at h₁
  by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! H
    rw [b₂, b₄, b₆] at H
    grobner

section Decidable

variable [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.Equation x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  rw [negY, show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h

lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
     W.addX xP xQ (W.slope xP xQ yP yQ) =
       ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2 := by
  have hxPQ' : xP - xQ ≠ 0 := by grind only
  simp [addX, slope, hn, div_pow]
  field

/-- We give an explicit expression for `xRep` of `P + P` when `2*P ≠ 0`. -/
lemma Point.xRep_add_self_of_Y_ne {x y : F} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]

/-- We give an explicit expression for `xRep` of `P + Q` when `P ≠ ±Q`. -/
lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some, addX_of_X_ne hn]

/-- We give an explicit expression for `xRep` of `P - Q` when `P ≠ ±Q`. -/
lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 + W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ)
           - (W.a₂ + xP + xQ) * (xP - xQ) ^2) / (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn, xRep_some,
    addX_of_X_ne hn]
  grind only [negY]

end Decidable

lemma finite_preimage_xRep (x : F) : {P : W.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : W.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_ofPred_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by ext : 1; simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) : {P : W.Point | P.xRep 0 = x}.Finite := by
  have : {P : W.Point | P.xRep 0 = x} ⊆ {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset this

-- end #40303

/-- `sym2x` in terms of the projective `xRep` coordinates. Mathlib provides only the
per-constructor `@[simp]` lemmas and does not `@[expose]` `sym2x`, so this general unfolding is
stated here (a Mathlib-upstreaming candidate). -/
lemma Point.sym2x_eq (P Q : W.Point) :
    P.sym2x Q = ![P.xRep 0 * Q.xRep 0, P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
      P.xRep 1 * Q.xRep 1] := by
  match P, Q with
  | 0, 0 => simp [Point.xRep_zero]
  | 0, .some x y h => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, 0 => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, .some x' y' h' => simp [Point.xRep_some]

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.Point) :
    sym2x P P = fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some .. =>
    simp only [sym2x_some_some, succ_eq_add_one, reduceAdd, sym2x_some_zero, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, sym2x_zero_zero, one_smul, addSubMap]
    ext i : 1
    fin_cases i <;> simp
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [Hrs]
    by_cases! H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      refine ⟨_, H', ?_⟩
      simp [Point.sym2x_eq, Point.xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma Point.sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (addSubMap W i).eval <| sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, Point.sym2x_comm 0] using P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_comm _ Q] using Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some xP yP hP).sym2x (some xQ yQ hQ)) =
        ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
          2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
          (xP - xQ) ^ 2] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap]
      ring
    have : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 this, ?_⟩
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    rw [Hrs, Point.sym2x_eq, Point.xRep_add_of_X_ne hP hQ hxPQ, Point.xRep_sub_of_X_ne hP hQ hxPQ,
      b₂, b₄, b₆, b₈]
    ext i : 1
    fin_cases i <;> simp [field] <;> grobner

end Decidable

/-!
### The naïve height
-/

section AAV

open Height

variable [AdmissibleAbsValues F]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveLogHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveLogHeight_eq_logHeight (P : W.Point) : P.naiveLogHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveLogHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveLogHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveLogHeight, xRep]
  | some .. => simpa [naiveLogHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveLogHeight + Q.naiveLogHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveLogHeight_eq_logHeight, Q.naiveLogHeight_eq_logHeight, Point.sym2x_eq]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

/-- The "approximate parallelogram law" for the naïve height on an elliptic curve. -/
theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveLogHeight + (P - Q).naiveLogHeight - 2 * (P.naiveLogHeight + Q.naiveLogHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- speed up `grind` below by reducing to the essentials
  generalize (P + Q).naiveLogHeight + (P - Q).naiveLogHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveLogHeight + Q.naiveLogHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end AAV

section Northcott

open Height

variable [AdmissibleAbsValues F]

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.naiveLogHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveLogHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable [DecidableEq F] [W.toAffine.IsElliptic]

/-- **The Mordell-Weil Theorem**, general version: `E(K)` is finitely generated, for an
elliptic curve `E` given by an equation `y² = f(x)` with a monic cubic `f` (`a₁ = a₃ = 0`)
over a field `K` such that
* `K` has admissible absolute values satisfying the Northcott property (so heights work);
* `K` is the fraction field of a Dedekind domain `R`; and
* for each irreducible factor `p` of `f`, the integral closure of `R` in `K[X]/(p)` has
  finite class group and finitely generated unit group.

For `K` a number field all of these hold; see `fg_point_of_numberField`.

Note that the per-factor hypotheses cannot be replaced by the corresponding hypotheses on `R`
itself: by a theorem of Claborn, refined by Leedham-Green and by Clark
(*Elliptic Dedekind domains revisited*, Enseign. Math. 55 (2009)), **every** abelian group is
the class group of the integral closure of a PID in a separable *quadratic* field extension,
so `Finite (ClassGroup R)` gives no control over the class groups of the factors. (Whether
adding `Group.FG Rˣ` rescues the implication appears to be unknown; all known proofs of the
per-factor statements require `K` to be a global field.) -/
theorem fg_point (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [W.IsCharNeTwoNF]
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
    [(p : W.f.Factors) → Group.FG (W.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have H₂ (P : W.Point) : 0 ≤ P.naiveLogHeight := by
    rw [Point.naiveLogHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' (W.finite_index_range_nsmulAddMonoidHom_two R) H₂ hC

/-- **The Mordell-Weil Theorem** for an arbitrary Weierstrass curve: `E(K)` is finitely
generated, given an admissible change of variables `C` bringing `E` into the normal form
`y² = cubic` (i.e., `a₁ = a₃ = 0`), together with the finiteness hypotheses of `fg_point`
for the model `C • E`. The result is transferred along the isomorphism of point groups
`Point.equivVariableChange`.

Such a `C` exists whenever `2` is invertible in `K`
(`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`, completing the square). -/
theorem fg_point_of_variableChange (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] (C : VariableChange F) [(C • W).IsCharNeTwoNF]
    [(p : (C • W).toAffine.f.Factors) →
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor R p))]
    [(p : (C • W).toAffine.f.Factors) →
      Group.FG ((C • W).toAffine.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have := fg_point (W := (C • W).toAffine) R
  exact AddGroup.fg_of_surjective (f := (Point.equivVariableChange W C).toAddMonoidHom)
    (Point.equivVariableChange W C).surjective

end Northcott

section NumberField

open _root_.NumberField

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]

/-- **The Mordell-Weil Theorem**: the group `E(K)` of `K`-rational points of an elliptic
curve `E` over a number field `K` is finitely generated.

The square on the left-hand side is completed by an admissible change of variables (possible
since `K` has characteristic `0`), and the finiteness hypotheses of `fg_point` for the
resulting model are the class number theorem and Dirichlet's unit theorem. -/
theorem fg_point_of_numberField : AddGroup.FG W.Point := by
  have := invertibleOfNonzero (two_ne_zero (α := F))
  obtain ⟨C, hC⟩ := exists_variableChange_isCharNeTwoNF (W := W)
  have (p : (C • W).toAffine.f.Factors) :
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)) :=
    NumberField.finite_classGroup_integralClosure F (AdjoinRoot (p : Polynomial F))
  have (p : (C • W).toAffine.f.Factors) :
      Group.FG ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)ˣ :=
    NumberField.fg_units_integralClosure F (AdjoinRoot (p : Polynomial F))
  exact fg_point_of_variableChange (𝓞 F) C

end NumberField

end WeierstrassCurve.Affine

end
/- ===== end EllipticCurves/MordellWeil.lean ===== -/

/-- The Mordell-Weil theorem over `ℚ`, from `WeierstrassCurve.Affine.fg_point_of_numberField`
(Michael Stoll et al., EllipticCurves). -/
theorem OMA.solution : OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1.H1 := by
  intro E _
  exact Module.Finite.iff_addGroup_fg.mpr WeierstrassCurve.Affine.fg_point_of_numberField

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
