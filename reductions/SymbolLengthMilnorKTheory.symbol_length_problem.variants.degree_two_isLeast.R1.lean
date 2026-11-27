import FormalConjectures.Other.SymbolLengthMilnorKTheory

-- Reduction of Becher and Hoffmann's question (declaration
-- SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast)
-- to its open part.
--
-- The target says that the symbol length of K_2(C(x_1, ..., x_m))/p is exactly m - 1.
-- Proved here, with no hypothesis:
--   * the lower bound m - 1 for every m >= 1 (Becher and Hoffmann, Proposition 4.5), by maps
--     K_2/p -> Z/p built from pairs of components of a valuation of rank m, and a rank argument;
--   * the case m = 1, that is K_2(C(x))/p = 0, from the Steinberg relation applied to
--     (x - a)/(b - a) + (x - b)/(a - b) = 1 and the fact that constants are p-th powers.
-- Left as hypotheses: the upper bound m - 1 for m >= 2, split as
--   H1  m = 2 and p <= 3 (known: a theorem of Artin, see the upstream docstring),
--   H2  m = 2 and p >= 5 (open: is every class of K_2(C(x, y))/p a single symbol),
--   H3  m >= 3 (open).

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1

open MilnorK MvPolynomial

def H1 : Prop := ∀ p : ℕ, p.Prime → p ≤ 3 →
  1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) p 2

def H2 : Prop := ∀ p : ℕ, p.Prime → 5 ≤ p →
  1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) p 2

def H3 : Prop := ∀ m p : ℕ, 3 ≤ m → p.Prime →
  m - 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2

theorem kneg_mul {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * B = 0) :
    -A * B = 0 := by
  have h2 : -A + A = 0 := neg_add_cancel A
  have h3 : (-A + A) * B = 0 := by rw [h2, zero_mul]
  rw [add_mul, h, add_zero] at h3
  exact h3

theorem kmul_neg {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * B = 0) :
    A * -B = 0 := by
  have h2 : -B + B = 0 := neg_add_cancel B
  have h3 : A * (-B + B) = 0 := by rw [h2, mul_zero]
  rw [mul_add, h, add_zero] at h3
  exact h3

theorem kof_neg_mul {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : -A * B = 0) :
    A * B = 0 := by
  have h2 : -A + A = 0 := neg_add_cancel A
  have h3 : (-A + A) * B = 0 := by rw [h2, zero_mul]
  rw [add_mul, h, zero_add] at h3
  exact h3

theorem kof_mul_neg {F : Type*} [Field F] {p : ℕ} (A B : MilnorK F p) (h : A * -B = 0) :
    A * B = 0 := by
  have h2 : -B + B = 0 := neg_add_cancel B
  have h3 : A * (-B + B) = 0 := by rw [h2, mul_zero]
  rw [mul_add, h, zero_add] at h3
  exact h3

theorem units_gen (H : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ)
    (hc : ∀ (c : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ),
      (u : MvRatFunc (Fin 1) ℂ) = algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C c) →
        u ∈ H)
    (hx : ∀ (a : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ),
      (u : MvRatFunc (Fin 1) ℂ) =
        algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a) → u ∈ H)
    (u : (MvRatFunc (Fin 1) ℂ)ˣ) : u ∈ H := by
  let M : Submonoid (MvRatFunc (Fin 1) ℂ) :=
    { carrier := {x | ∀ v : (MvRatFunc (Fin 1) ℂ)ˣ, (v : MvRatFunc (Fin 1) ℂ) = x → v ∈ H}
      one_mem' := by
        intro v hv
        have : v = 1 := Units.ext hv
        rw [this]; exact H.one_mem
      mul_mem' := by
        intro x y hx' hy' v hv
        have hxy : x * y ≠ 0 := hv ▸ v.ne_zero
        have hx0 : x ≠ 0 := left_ne_zero_of_mul hxy
        have hy0 : y ≠ 0 := right_ne_zero_of_mul hxy
        have : v = Units.mk0 x hx0 * Units.mk0 y hy0 := Units.ext (by simp [hv])
        rw [this]
        exact H.mul_mem (hx' _ rfl) (hy' _ rfl) }
  have hpoly : ∀ q : MvPolynomial (Fin 1) ℂ,
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) q ∈ M := by
    intro q
    have hsurj : ∀ q : MvPolynomial (Fin 1) ℂ,
        ∃ r : Polynomial ℂ, Polynomial.eval₂RingHom MvPolynomial.C (X 0) r = q := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => exact ⟨Polynomial.C a, by simp⟩
      | add f g hf hg =>
        obtain ⟨rf, rfl⟩ := hf
        obtain ⟨rg, rfl⟩ := hg
        exact ⟨rf + rg, map_add _ _ _⟩
      | mul_X f i hf =>
        obtain ⟨rf, rfl⟩ := hf
        refine ⟨rf * Polynomial.X, ?_⟩
        have : i = 0 := Subsingleton.elim _ _
        simp [this]
    obtain ⟨r, rfl⟩ := hsurj q
    rw [(IsAlgClosed.splits r).eq_prod_roots]
    rw [map_mul, map_mul, map_multiset_prod, map_multiset_prod]
    refine M.mul_mem ?_ (M.multiset_prod_mem _ ?_)
    · intro v hv
      refine hc r.leadingCoeff v ?_
      simpa using hv
    · intro x hx'
      simp only [Multiset.map_map, Multiset.mem_map] at hx'
      obtain ⟨a, -, rfl⟩ := hx'
      intro v hv
      refine hx a v ?_
      simpa using hv
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 1) ℂ)
    (u : MvRatFunc (Fin 1) ℂ)
  have hd0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) d ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hnd, h, div_zero]
  have hn0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) n ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [← hnd, h, zero_div]
  have : u = Units.mk0 _ hn0 * (Units.mk0 _ hd0)⁻¹ :=
    Units.ext (by simp [← hnd, div_eq_mul_inv])
  rw [this]
  exact H.mul_mem (hpoly n _ rfl) (H.inv_mem (hpoly d _ rfl))

theorem algMap_ne_zero {q : MvPolynomial (Fin 1) ℂ} (hq : q ≠ 0) :
    algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq

theorem of_const_eq_zero (p : ℕ) (hp : 0 < p) (c : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C c)) :
    MilnorK.of p u = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hp
  have hz0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C z) ≠ 0 := by
    intro h
    apply u.ne_zero
    rw [hu, ← hz, map_pow, map_pow, h, zero_pow hp.ne']
  have : u = (Units.mk0 _ hz0) ^ p := Units.ext (by simp [hu, ← hz])
  rw [this, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_lin_mul_of_lin (p : ℕ) (hp : 0 < p) (a b : ℂ) (hab : a ≠ b)
    (u v : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a))
    (hv : (v : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C b)) :
    MilnorK.of p u * MilnorK.of p v = 0 := by
  have hα : (b - a) ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk1 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C (b - a)⁻¹) ≠ 0 :=
    algMap_ne_zero (by simpa using hα)
  have hk2 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (C (-(b - a)⁻¹)) ≠ 0 :=
    algMap_ne_zero (by simpa using hα)
  have hpoly : (X 0 - C a) * C (b - a)⁻¹ + (X 0 - C b) * C (-(b - a)⁻¹) =
      (1 : MvPolynomial (Fin 1) ℂ) := by
    have h1 : (C ((b - a)⁻¹ * (b - a)) : MvPolynomial (Fin 1) ℂ) = 1 := by
      rw [inv_mul_cancel₀ hα, C_1]
    rw [← h1]
    simp only [map_mul, map_sub, map_neg]
    ring
  have hst : ((u * Units.mk0 _ hk1 : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) +
      ((v * Units.mk0 _ hk2 : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, hu, hv]
    rw [← map_mul, ← map_mul, ← map_add, hpoly, map_one]
  have h := of_mul_of_eq_zero p _ _ hst
  rw [of_mul, of_mul, of_const_eq_zero p hp _ (Units.mk0 _ hk1) rfl,
    of_const_eq_zero p hp _ (Units.mk0 _ hk2) rfl, add_zero, add_zero] at h
  exact h

theorem of_lin_mul_self (p : ℕ) (hp : 0 < p) (a : ℂ) (u : (MvRatFunc (Fin 1) ℂ)ˣ)
    (hu : (u : MvRatFunc (Fin 1) ℂ) =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C a)) :
    MilnorK.of p u * MilnorK.of p u = 0 := by
  have hw0 : algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C (a + 1)) ≠ 0 := by
    refine algMap_ne_zero ?_
    intro h
    have := congrArg (MvPolynomial.eval (fun _ => a)) h
    simp at this
  have hw : (u : MvRatFunc (Fin 1) ℂ) - 1 =
      algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ) (X 0 - C (a + 1)) := by
    rw [hu, ← map_one (algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ)), ← map_sub]
    congr 1
    simp only [map_add, C_1]
    ring
  have hst : ((u⁻¹ : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) +
      ((Units.mk0 _ hw0 * u⁻¹ : (MvRatFunc (Fin 1) ℂ)ˣ) : MvRatFunc (Fin 1) ℂ) = 1 := by
    simp only [Units.val_mul, Units.val_mk0, ← hw, Units.val_inv_eq_inv_val]
    have hu0 : (u : MvRatFunc (Fin 1) ℂ) ≠ 0 := u.ne_zero
    field_simp
    ring
  have h := of_mul_of_eq_zero p _ _ hst
  rw [of_mul, of_inv] at h
  have h2 := of_lin_mul_of_lin p hp a (a + 1) (by simp) u (Units.mk0 _ hw0) hu rfl
  have h4 := kof_neg_mul _ _ h
  rw [mul_add, h2, zero_add] at h4
  exact kof_mul_neg _ _ h4

theorem of_mul_of_one_var (p : ℕ) (hp : 0 < p) (u v : (MvRatFunc (Fin 1) ℂ)ˣ) :
    MilnorK.of p u * MilnorK.of p v = 0 := by
  let K1 : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ :=
    { carrier := {u | ∀ v : (MvRatFunc (Fin 1) ℂ)ˣ, MilnorK.of p u * MilnorK.of p v = 0}
      mul_mem' := by
        intro a b ha hb v
        rw [of_mul, add_mul, ha v, hb v, add_zero]
      one_mem' := by
        intro v
        rw [of_one, zero_mul]
      inv_mem' := by
        intro a ha v
        rw [of_inv]
        exact kneg_mul _ _ (ha v) }
  have hmem : u ∈ K1 := by
    refine units_gen K1 ?_ ?_ u
    · intro c u hu v
      rw [of_const_eq_zero p hp c u hu, zero_mul]
    · intro a u hu v
      let K2 : Subgroup (MvRatFunc (Fin 1) ℂ)ˣ :=
        { carrier := {v | MilnorK.of p u * MilnorK.of p v = 0}
          mul_mem' := by
            intro x y hx hy
            show MilnorK.of p u * MilnorK.of p (x * y) = 0
            rw [of_mul, mul_add, hx, hy, add_zero]
          one_mem' := by
            show MilnorK.of p u * MilnorK.of p 1 = 0
            rw [of_one, mul_zero]
          inv_mem' := by
            intro x hx
            show MilnorK.of p u * MilnorK.of p x⁻¹ = 0
            rw [of_inv]
            exact kmul_neg _ _ hx }
      have hv : v ∈ K2 := by
        refine units_gen K2 ?_ ?_ v
        · intro c v hv
          show MilnorK.of p u * MilnorK.of p v = 0
          rw [of_const_eq_zero p hp c v hv, mul_zero]
        · intro b v hv
          show MilnorK.of p u * MilnorK.of p v = 0
          by_cases hab : a = b
          · subst hab
            have : u = v := Units.ext (hu.trans hv.symm)
            subst this
            exact of_lin_mul_self p hp a u hu
          · exact of_lin_mul_of_lin p hp a b hab u v hu hv
      exact hv
  exact hmem v

theorem grade_two_one_var (p : ℕ) (hp : 0 < p) : MilnorK.grade (MvRatFunc (Fin 1) ℂ) p 2 = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, symbol_succ]
  simp [of_mul_of_one_var p hp]

theorem exists_hom {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (l : R → ℤ)
    (hl : ∀ f g : R, f ≠ 0 → g ≠ 0 → l (f * g) = l f + l g) :
    ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L (Additive.ofMul u) = l n - l d := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hex : ∀ u : Fˣ, ∃ nd : R × R, nd.2 ≠ 0 ∧
      (u : F) * algebraMap R F nd.2 = algebraMap R F nd.1 := by
    intro u
    obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := R) (u : F)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨(n, d), hd0, ?_⟩
    have : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    rw [← hnd]
    field_simp
  choose nd hnd0 hndeq using hex
  have hnum : ∀ (u : Fˣ) (n d : R), d ≠ 0 → (u : F) * algebraMap R F d = algebraMap R F n →
      n ≠ 0 := by
    rintro u n d hd h rfl
    rw [map_zero] at h
    exact (mul_ne_zero u.ne_zero ((map_ne_zero_iff _ hinj).mpr hd)) h
  have key : ∀ (u : Fˣ) (n d : R), d ≠ 0 → (u : F) * algebraMap R F d = algebraMap R F n →
      l (nd u).1 - l (nd u).2 = l n - l d := by
    intro u n d hd h
    have hn : n ≠ 0 := hnum u n d hd h
    have hn' : (nd u).1 ≠ 0 := hnum u _ _ (hnd0 u) (hndeq u)
    have heq : n * (nd u).2 = (nd u).1 * d := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hndeq u]
      ring
    have := congrArg l heq
    rw [hl _ _ hn (hnd0 u), hl _ _ hn' hd] at this
    linarith
  refine ⟨AddMonoidHom.mk' (fun a => l (nd a.toMul).1 - l (nd a.toMul).2) ?_, ?_⟩
  · intro a b
    have h1 := hndeq a.toMul
    have h2 := hndeq b.toMul
    have hprod : (((a + b).toMul : Fˣ) : F) *
        algebraMap R F ((nd a.toMul).2 * (nd b.toMul).2) =
        algebraMap R F ((nd a.toMul).1 * (nd b.toMul).1) := by
      rw [map_mul, map_mul, ← h1, ← h2, toMul_add, Units.val_mul]
      ring
    have := key (a + b).toMul _ _ (mul_ne_zero (hnd0 _) (hnd0 _)) hprod
    show l (nd (a + b).toMul).1 - l (nd (a + b).toMul).2 =
      (l (nd a.toMul).1 - l (nd a.toMul).2) + (l (nd b.toMul).1 - l (nd b.toMul).2)
    rw [this, hl _ _ (hnum _ _ _ (hnd0 _) h1) (hnum _ _ _ (hnd0 _) h2),
      hl _ _ (hnd0 _) (hnd0 _)]
    ring
  · intro u n d hd h
    exact key u n d hd h

theorem steinberg_of_trichotomy {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (l1 l2 : R → ℤ) (L1 L2 : Additive Fˣ →+ ℤ)
    (h1 : ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L1 (Additive.ofMul u) = l1 n - l1 d)
    (h2 : ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L2 (Additive.ofMul u) = l2 n - l2 d)
    (htri : ∀ f g : R, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      (l1 f = l1 g ∧ l2 f = l2 g) ∨ (l1 (f + g) = l1 f ∧ l2 (f + g) = l2 f) ∨
        (l1 (f + g) = l1 g ∧ l2 (f + g) = l2 g))
    (a b : Fˣ) (hab : (a : F) + (b : F) = 1) :
    L1 (Additive.ofMul a) * L2 (Additive.ofMul b) =
      L2 (Additive.ofMul a) * L1 (Additive.ofMul b) := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := R) (a : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  have ha : (a : F) * algebraMap R F d = algebraMap R F n := by
    rw [← hnd]
    field_simp
  have hb : (b : F) * algebraMap R F d = algebraMap R F (d - n) := by
    have : (b : F) = 1 - (a : F) := by rw [← hab]; ring
    rw [this, map_sub, ← ha]
    ring
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (mul_ne_zero a.ne_zero hd') ha
  have hm0 : d - n ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    exact (mul_ne_zero b.ne_zero hd') hb
  have hsum : n + (d - n) = d := by ring
  have hs0 : n + (d - n) ≠ 0 := by rw [hsum]; exact hd0
  rw [h1 a n d hd0 ha, h2 a n d hd0 ha, h1 b (d - n) d hd0 hb, h2 b (d - n) d hd0 hb]
  rcases htri n (d - n) hn0 hm0 hs0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
    ring
  · rw [hsum] at e1 e2
    rw [e1, e2]
    ring
  · rw [hsum] at e1 e2
    rw [e1, e2]
    ring

theorem mat_add {S : Type*} [CommRing S] (l m l' m' : S) :
    (!![0, l + l', -(m + m'), 0; 0, 0, 0, m + m'; 0, 0, 0, l + l'; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) S) =
    !![0, l, -m, 0; 0, 0, 0, m; 0, 0, 0, l; 0, 0, 0, 0] +
      !![0, l', -m', 0; 0, 0, 0, m'; 0, 0, 0, l'; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem mat_mul {S : Type*} [CommRing S] (l m l' m' : S) :
    (!![0, l, -m, 0; 0, 0, 0, m; 0, 0, 0, l; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) S) *
      !![0, l', -m', 0; 0, 0, 0, m'; 0, 0, 0, l'; 0, 0, 0, 0] =
    !![0, 0, 0, l * m' - m * l'; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem mat_zero {S : Type*} [CommRing S] :
    (!![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) S) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_symbol_map {F : Type*} [Field F] (p : ℕ) (L M : Additive Fˣ →+ ℤ)
    (hst : ∀ a b : Fˣ, (a : F) + (b : F) = 1 →
      L (Additive.ofMul a) * M (Additive.ofMul b) =
        M (Additive.ofMul a) * L (Additive.ofMul b)) :
    ∃ Φ : MilnorK F p →+ ZMod p, ∀ a b : Fˣ, Φ (MilnorK.of p a * MilnorK.of p b) =
      ((L (Additive.ofMul a) * M (Additive.ofMul b) -
        M (Additive.ofMul a) * L (Additive.ofMul b) : ℤ) : ZMod p) := by
  obtain ⟨G, hGdef⟩ : ∃ G : Additive Fˣ →+ Matrix (Fin 4) (Fin 4) (ZMod p), ∀ a, G a =
      !![0, (L a : ZMod p), -(M a : ZMod p), 0;
        0, 0, 0, (M a : ZMod p); 0, 0, 0, (L a : ZMod p); 0, 0, 0, 0] := by
    refine ⟨AddMonoidHom.mk' (fun a => !![0, (L a : ZMod p), -(M a : ZMod p), 0;
      0, 0, 0, (M a : ZMod p); 0, 0, 0, (L a : ZMod p); 0, 0, 0, 0]) ?_, fun a => rfl⟩
    intro a b
    rw [← mat_add, map_add, map_add, Int.cast_add, Int.cast_add]
  have hG : ∀ a b : Additive Fˣ, G a * G b =
      !![0, 0, 0, ((L a * M b - M a * L b : ℤ) : ZMod p);
        0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
    intro a b
    rw [hGdef, hGdef, mat_mul]
    push_cast
    rfl
  have hrel : ∀ ⦃x y : TensorAlgebra ℤ (Additive Fˣ)⦄, MilnorK.Rel F p x y →
      (TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom x =
        (TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom y := by
    intro x y h
    cases h with
    | steinberg a b h =>
      have h0 := hst a b h
      have h3 := hG (Additive.ofMul a) (Additive.ofMul b)
      rw [h0, sub_self, Int.cast_zero, mat_zero] at h3
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, TensorAlgebra.lift_ι_apply,
        AddMonoidHom.coe_toIntLinearMap, map_zero]
      exact h3
    | natCast =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_natCast, map_zero]
      ext i j
      simp [Matrix.natCast_apply]
  have hρ : ∀ a : Fˣ, RingQuot.lift ⟨(TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom, hrel⟩
      (MilnorK.of p a) = G (Additive.ofMul a) := by
    intro a
    simp [MilnorK.of, RingQuot.lift_mkRingHom_apply]
  refine ⟨AddMonoidHom.mk' (fun x =>
    RingQuot.lift ⟨(TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom, hrel⟩ x 0 3)
    (by intro x y; simp [map_add]), ?_⟩
  intro a b
  show RingQuot.lift ⟨(TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom, hrel⟩
    (MilnorK.of p a * MilnorK.of p b) 0 3 = _
  rw [map_mul, hρ, hρ, hG]
  simp

theorem rm_neg (a : ℂ) (Q : Polynomial ℂ) :
    (-Q).rootMultiplicity a = Q.rootMultiplicity a := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · have h : Polynomial.C (-1 : ℂ) * Q ≠ 0 := mul_ne_zero (by simp) hQ
    have h2 := Polynomial.rootMultiplicity_mul (x := a) h
    rw [Polynomial.rootMultiplicity_C, zero_add] at h2
    rw [← h2]
    congr 1
    simp

theorem rm_add_of_lt (a : ℂ) (P Q : Polynomial ℂ) (hP : P ≠ 0) (hPQ : P + Q ≠ 0)
    (h : P.rootMultiplicity a < Q.rootMultiplicity a) :
    (P + Q).rootMultiplicity a = P.rootMultiplicity a := by
  have h1 := Polynomial.rootMultiplicity_add a hPQ
  have e : (P + Q) + (-Q) = P := by ring
  have hP' : (P + Q) + (-Q) ≠ 0 := by rw [e]; exact hP
  have h2 := Polynomial.rootMultiplicity_add a hP'
  rw [rm_neg, e] at h2
  rcases min_le_iff.mp h1 with h3 | h3 <;> rcases min_le_iff.mp h2 with h4 | h4 <;> omega

theorem tri {σ : Type*} (m : MonomialOrder σ) (a : ℂ) (f g : MvPolynomial σ (Polynomial ℂ))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (m.degree f = m.degree g ∧
      (m.leadingCoeff f).rootMultiplicity a = (m.leadingCoeff g).rootMultiplicity a) ∨
    (m.degree (f + g) = m.degree f ∧
      (m.leadingCoeff (f + g)).rootMultiplicity a = (m.leadingCoeff f).rootMultiplicity a) ∨
    (m.degree (f + g) = m.degree g ∧
      (m.leadingCoeff (f + g)).rootMultiplicity a = (m.leadingCoeff g).rootMultiplicity a) := by
  have hlf : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
  have hlg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  rcases lt_trichotomy (m.toSyn (m.degree f)) (m.toSyn (m.degree g)) with h | h | h
  · right; right
    refine ⟨m.degree_add_eq_right_of_lt h, ?_⟩
    rw [add_comm, m.leadingCoeff_add_of_lt h]
  · have hd : m.degree f = m.degree g := m.toSyn.injective h
    by_cases hc : m.leadingCoeff f + m.leadingCoeff g = 0
    · left
      refine ⟨hd, ?_⟩
      have h2 : m.leadingCoeff f = -m.leadingCoeff g := eq_neg_of_add_eq_zero_left hc
      rw [h2, rm_neg]
    · have hcoeff : (f + g).coeff (m.degree f) = m.leadingCoeff f + m.leadingCoeff g := by
        have e1 : m.leadingCoeff f = f.coeff (m.degree f) := rfl
        have e2 : m.leadingCoeff g = g.coeff (m.degree f) := by rw [hd]; rfl
        rw [coeff_add, e1, e2]
      have hdeg : m.degree (f + g) = m.degree f := by
        apply m.toSyn.injective
        apply le_antisymm
        · have h3 := m.degree_add_le (f := f) (g := g)
          rw [← h, sup_idem] at h3
          exact h3
        · apply m.le_degree
          rw [mem_support_iff, hcoeff]
          exact hc
      have hlc : m.leadingCoeff (f + g) = m.leadingCoeff f + m.leadingCoeff g := by
        rw [← hcoeff, ← hdeg]
        rfl
      rcases lt_trichotomy ((m.leadingCoeff f).rootMultiplicity a)
        ((m.leadingCoeff g).rootMultiplicity a) with h' | h' | h'
      · right; left
        refine ⟨hdeg, ?_⟩
        rw [hlc]
        exact rm_add_of_lt a _ _ hlf hc h'
      · left
        exact ⟨hd, h'⟩
      · right; right
        refine ⟨hdeg.trans hd, ?_⟩
        rw [hlc, add_comm]
        exact rm_add_of_lt a _ _ hlg (by rwa [add_comm]) h'
  · right; left
    exact ⟨m.degree_add_of_lt h, by rw [m.leadingCoeff_add_of_lt h]⟩

theorem lower_bound_abstract {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (n : ℕ) (e : R →+* MvPolynomial (Fin n) (Polynomial ℂ))
    (he : Function.Injective e) (g y : Fin n → R)
    (hg : ∀ j : Fin n, e (g j) = C (Polynomial.X - Polynomial.C ((j : ℕ) : ℂ)))
    (hy : ∀ j : Fin n, e (y j) = X j) (p : ℕ) (hp : p.Prime) (k : ℕ)
    (hk : k ∈ symbolLengthBounds F p 2) : n ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  obtain ⟨m⟩ : Nonempty (MonomialOrder (Fin n)) := ⟨MonomialOrder.lex⟩
  have he0 : ∀ f : R, f ≠ 0 → e f ≠ 0 := fun f hf => (map_ne_zero_iff e he).mpr hf
  have hLw : ∀ j : Fin n, ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (nn d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F nn →
      L (Additive.ofMul u) = ((m.degree (e nn) j : ℕ) : ℤ) - ((m.degree (e d) j : ℕ) : ℤ) := by
    intro j
    exact exists_hom (fun f => ((m.degree (e f) j : ℕ) : ℤ)) (by
      intro f g hf hg
      rw [map_mul, m.degree_mul (he0 f hf) (he0 g hg)]
      simp)
  have hLv : ∀ i : Fin n, ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (nn d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F nn →
      L (Additive.ofMul u) =
        (((m.leadingCoeff (e nn)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ) -
          (((m.leadingCoeff (e d)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ) := by
    intro i
    exact exists_hom
      (fun f => (((m.leadingCoeff (e f)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ)) (by
      intro f g hf hg
      have h1 : m.leadingCoeff (e f) * m.leadingCoeff (e g) ≠ 0 :=
        mul_ne_zero (m.leadingCoeff_ne_zero_iff.mpr (he0 f hf))
          (m.leadingCoeff_ne_zero_iff.mpr (he0 g hg))
      rw [map_mul, m.leadingCoeff_mul, Polynomial.rootMultiplicity_mul h1]
      simp)
  choose Lw hLw using hLw
  choose Lv hLv using hLv
  have hΦww : ∀ j j2 : Fin n, ∃ Φ : MilnorK F p →+ ZMod p, ∀ a b : Fˣ,
      Φ (MilnorK.of p a * MilnorK.of p b) =
        ((Lw j (Additive.ofMul a) * Lw j2 (Additive.ofMul b) -
          Lw j2 (Additive.ofMul a) * Lw j (Additive.ofMul b) : ℤ) : ZMod p) := by
    intro j j2
    refine exists_symbol_map p (Lw j) (Lw j2) ?_
    refine steinberg_of_trichotomy (fun f => ((m.degree (e f) j : ℕ) : ℤ))
      (fun f => ((m.degree (e f) j2 : ℕ) : ℤ)) (Lw j) (Lw j2) (hLw j) (hLw j2) ?_
    intro f g hf hg _
    rcases tri m 0 (e f) (e g) (he0 f hf) (he0 g hg) with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · left
      simp only [h1, and_self]
    · right; left
      simp only [map_add, h1, and_self]
    · right; right
      simp only [map_add, h1, and_self]
  have hΦwv : ∀ j i : Fin n, ∃ Φ : MilnorK F p →+ ZMod p, ∀ a b : Fˣ,
      Φ (MilnorK.of p a * MilnorK.of p b) =
        ((Lw j (Additive.ofMul a) * Lv i (Additive.ofMul b) -
          Lv i (Additive.ofMul a) * Lw j (Additive.ofMul b) : ℤ) : ZMod p) := by
    intro j i
    refine exists_symbol_map p (Lw j) (Lv i) ?_
    refine steinberg_of_trichotomy (fun f => ((m.degree (e f) j : ℕ) : ℤ))
      (fun f => (((m.leadingCoeff (e f)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ))
      (Lw j) (Lv i) (hLw j) (hLv i) ?_
    intro f g hf hg _
    rcases tri m ((i : ℕ) : ℂ) (e f) (e g) (he0 f hf) (he0 g hg) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      simp only [h1, h2, and_self]
    · right; left
      simp only [map_add, h1, h2, and_self]
    · right; right
      simp only [map_add, h1, h2, and_self]
  choose Φww hΦww using hΦww
  choose Φwv hΦwv using hΦwv
  have hg0 : ∀ l : Fin n, g l ≠ 0 := by
    intro l h
    have h1 := hg l
    rw [h, map_zero] at h1
    have h2 : (Polynomial.X - Polynomial.C ((l : ℕ) : ℂ)) = 0 :=
      C_injective (Fin n) (Polynomial ℂ) (h1.symm.trans (map_zero C).symm)
    exact Polynomial.X_sub_C_ne_zero _ h2
  have hy0 : ∀ l : Fin n, y l ≠ 0 := by
    intro l h
    have h1 := hy l
    rw [h, map_zero] at h1
    exact X_ne_zero l h1.symm
  obtain ⟨gu, hgu⟩ : ∃ gu : Fin n → Fˣ, ∀ l, (gu l : F) = algebraMap R F (g l) :=
    ⟨fun l => Units.mk0 _ ((map_ne_zero_iff _ hinj).mpr (hg0 l)), fun l => rfl⟩
  obtain ⟨yu, hyu⟩ : ∃ yu : Fin n → Fˣ, ∀ l, (yu l : F) = algebraMap R F (y l) :=
    ⟨fun l => Units.mk0 _ ((map_ne_zero_iff _ hinj).mpr (hy0 l)), fun l => rfl⟩
  have vw_g : ∀ j l : Fin n, Lw j (Additive.ofMul (gu l)) = 0 := by
    intro j l
    rw [hLw j (gu l) (g l) 1 one_ne_zero (by rw [hgu, map_one, mul_one]), hg, map_one,
      MonomialOrder.degree_C, MonomialOrder.degree_one]
    simp
  have vw_y : ∀ j l : Fin n, Lw j (Additive.ofMul (yu l)) = if l = j then 1 else 0 := by
    intro j l
    rw [hLw j (yu l) (y l) 1 one_ne_zero (by rw [hyu, map_one, mul_one]), hy, map_one,
      MonomialOrder.degree_X, MonomialOrder.degree_one, Finsupp.single_apply]
    split_ifs <;> simp
  have vv_g : ∀ i l : Fin n, Lv i (Additive.ofMul (gu l)) = if i = l then 1 else 0 := by
    intro i l
    rw [hLv i (gu l) (g l) 1 one_ne_zero (by rw [hgu, map_one, mul_one]), hg, map_one,
      MonomialOrder.leadingCoeff_C, MonomialOrder.leadingCoeff_one,
      Polynomial.rootMultiplicity_X_sub_C, ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    have hiff : (((i : ℕ) : ℂ) = ((l : ℕ) : ℂ)) ↔ i = l := by
      rw [Nat.cast_inj, Fin.val_inj]
    simp only [hiff]
    split_ifs <;> simp
  have vv_y : ∀ i l : Fin n, Lv i (Additive.ofMul (yu l)) = 0 := by
    intro i l
    rw [hLv i (yu l) (y l) 1 one_ne_zero (by rw [hyu, map_one, mul_one]), hy, map_one,
      MonomialOrder.leadingCoeff_X, MonomialOrder.leadingCoeff_one,
      ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    simp
  have hξ : (∑ l, MilnorK.of p (gu l) * MilnorK.of p (yu l)) ∈ MilnorK.grade F p 2 := by
    refine sum_mem fun l _ => ?_
    rw [← symbol_pair]
    exact symbol_mem_grade F p _
  obtain ⟨k2, hk2, s, hs⟩ := hk _ hξ
  have hsym : ∀ t, symbol p (s t) = MilnorK.of p (s t 0) * MilnorK.of p (s t 1) := by
    intro t
    simp [symbol_succ]
  simp only [hsym] at hs
  obtain ⟨H, hH1, hH2⟩ : ∃ H : Fin n ⊕ Fin n → Additive Fˣ →+ ℤ,
      (∀ j, H (Sum.inl j) = Lw j) ∧ (∀ i, H (Sum.inr i) = Lv i) :=
    ⟨Sum.elim Lw Lv, fun j => rfl, fun i => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod p), ∀ r r2, M r r2 =
      ∑ t, ((H r (Additive.ofMul (s t 0)) * H r2 (Additive.ofMul (s t 1)) -
        H r2 (Additive.ofMul (s t 0)) * H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p) :=
    ⟨Matrix.of fun r r2 => ∑ t, ((H r (Additive.ofMul (s t 0)) * H r2 (Additive.ofMul (s t 1)) -
        H r2 (Additive.ofMul (s t 0)) * H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p),
      fun r r2 => rfl⟩
  have hrank : M.rank ≤ Fintype.card (Fin k2 ⊕ Fin k2) := by
    have hfact : M = Matrix.fromCols
        (Matrix.of fun r t => ((H r (Additive.ofMul (s t 0)) : ℤ) : ZMod p))
        (Matrix.of fun r t => ((H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p)) *
        Matrix.fromRows
        (Matrix.of fun t r => ((H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p))
        (Matrix.of fun t r => -((H r (Additive.ofMul (s t 0)) : ℤ) : ZMod p)) := by
      ext r r2
      rw [hM, Matrix.fromCols_mul_fromRows, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Matrix.of_apply]
      push_cast
      ring
    rw [hfact]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  have c1 : ∀ j j2 : Fin n, M (Sum.inl j) (Sum.inl j2) = 0 := by
    intro j j2
    have h1 := congrArg (Φww j j2) hs
    rw [map_sum, map_sum] at h1
    simp only [hΦww, vw_g] at h1
    rw [hM]
    simp only [hH1]
    rw [← h1]
    simp
  have c2 : ∀ j i : Fin n, M (Sum.inl j) (Sum.inr i) = if j = i then -1 else 0 := by
    intro j i
    have h1 := congrArg (Φwv j i) hs
    rw [map_sum, map_sum] at h1
    simp only [hΦwv, vw_g, vw_y, vv_g, vv_y] at h1
    rw [hM]
    simp only [hH1, hH2]
    rw [← h1]
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : ¬ i = j := fun h => hji h.symm
      simp [hji, hij]
  have c3 : ∀ r r2, M r2 r = -M r r2 := by
    intro r r2
    rw [hM, hM, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    ring
  have hblocks : M = Matrix.fromBlocks 0 (-1) 1 M.toBlocks₂₂ := by
    ext r r2
    rcases r with j | i <;> rcases r2 with j2 | i2
    · simp [c1]
    · rw [c2]
      by_cases h : j = i2 <;> simp [h, Matrix.one_apply]
    · rw [c3, c2]
      by_cases h : j2 = i
      · subst h
        simp
      · have h2 : ¬ i = j2 := fun hh => h hh.symm
        simp [h, h2, Matrix.one_apply]
    · rfl
  have hone : M * Matrix.fromBlocks M.toBlocks₂₂ 1 (-1) 0 = 1 := by
    conv_lhs => rw [hblocks]
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  have h2n : 2 * n ≤ 2 * k2 := by
    calc 2 * n = Fintype.card (Fin n ⊕ Fin n) := by simp; ring
      _ = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod p)).rank := Matrix.rank_one.symm
      _ = (M * Matrix.fromBlocks M.toBlocks₂₂ 1 (-1) 0).rank := by rw [hone]
      _ ≤ M.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin k2 ⊕ Fin k2) := hrank
      _ = 2 * k2 := by simp; ring
  omega

theorem lower_bound (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) :
    ∀ k ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2, m - 1 ≤ k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  intro k hk
  rw [Nat.add_sub_cancel]
  refine lower_bound_abstract (R := MvPolynomial (Fin (n + 1)) ℂ) (F := MvRatFunc (Fin (n + 1)) ℂ) n
    (((renameEquiv ℂ (_root_.finSuccEquiv n)).trans (optionEquivRight ℂ (Fin n))).toAlgHom.toRingHom)
    (AlgEquiv.injective _) (fun j => X 0 - C ((j : ℕ) : ℂ)) (fun j => X j.succ) ?_ ?_ p hp k hk
  · intro j
    simp [optionEquivRight_X_none, optionEquivRight_C]
  · intro j
    simp [optionEquivRight_X_some]

theorem main : H1 → H2 → H3 → type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast := by
  intro h1 h2 h3 m p hm hp
  refine ⟨?_, fun k hk => lower_bound m hm p hp k hk⟩
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with rfl | rfl
    · rw [Nat.sub_self, zero_mem_symbolLengthBounds_iff]
      exact grade_two_one_var p hp.pos
    · show 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) p 2
      rcases Nat.lt_or_ge p 4 with hp3 | hp4
      · exact h1 p hp (by omega)
      · have hp4ne : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        exact h2 p hp (by omega)
  · exact h3 m p hge hp

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1
