import OMAReductions.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1
import Mathlib.Algebra.QuaternionBasis
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Denumerable
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

open scoped TensorProduct Polynomial

namespace OMA.KaplanskyH1

instance instIsOrderedAddMonoidLex {α β : Type} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] :
    IsOrderedAddMonoid (α ×ₗ β) where
  add_le_add_left a b hab c := by
    rw [Prod.Lex.le_iff] at hab ⊢
    rcases hab with hlt | ⟨heq, hle⟩
    · exact Or.inl (by simpa [add_comm] using add_lt_add_right hlt (ofLex c).1)
    · exact Or.inr ⟨by simp [heq], by simpa [add_comm] using add_le_add_right hle (ofLex c).2⟩

/-- A multiplicative ultrametric valuation into a linearly ordered abelian group. -/
structure Val (K : Type) [Field K] (Γ : Type) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] where
  toFun : K → Γ
  map_mul : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → toFun (x * y) = toFun x + toFun y
  map_add_le : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
    toFun (x + y) ≤ max (toFun x) (toFun y)

lemma Val.map_one {K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) : v.toFun 1 = 0 := by
  have h := v.map_mul (one_ne_zero (α := K)) one_ne_zero
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

lemma Val.map_neg {K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) {x : K} (hx : x ≠ 0) :
    v.toFun (-x) = v.toFun x := by
  have h1 : v.toFun (-1) = 0 := by
    have h := v.map_mul (neg_ne_zero.mpr (one_ne_zero (α := K))) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, one_mul, v.map_one] at h
    rcases lt_trichotomy (v.toFun (-1)) 0 with hlt | heq | hgt
    · exact absurd (add_lt_add hlt hlt) (by rw [← h, add_zero]; exact lt_irrefl _)
    · exact heq
    · exact absurd (add_lt_add hgt hgt) (by rw [← h, add_zero]; exact lt_irrefl _)
  rw [← neg_one_mul, v.map_mul (neg_ne_zero.mpr one_ne_zero) hx, h1, zero_add]

lemma Val.add_ne_zero_of_lt {K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) {x y : K} (hx : x ≠ 0)
    (h : v.toFun x < v.toFun y) : x + y ≠ 0 := by
  intro h0
  have hyx : y = -x := eq_neg_of_add_eq_zero_right h0
  rw [hyx, v.map_neg hx] at h
  exact lt_irrefl _ h

lemma Val.sum_ne_zero_of_unique_max {ι K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) (s : Finset ι) (f : ι → K) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (hf₀ : f i₀ ≠ 0) (hmax : ∀ i ∈ s, i ≠ i₀ → f i ≠ 0 → v.toFun (f i) < v.toFun (f i₀)) :
    ∑ i ∈ s, f i ≠ 0 := by
  classical
  have hrest : ∀ t : Finset ι, (∀ i ∈ t, f i ≠ 0 → v.toFun (f i) < v.toFun (f i₀)) →
      ∑ i ∈ t, f i = 0 ∨ (∑ i ∈ t, f i ≠ 0 ∧ v.toFun (∑ i ∈ t, f i) < v.toFun (f i₀)) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => exact Or.inl rfl
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      rcases ih (fun i hi => ht i (Finset.mem_insert_of_mem hi)) with h0 | ⟨hne, hlt⟩
      · rw [h0, add_zero]
        by_cases hfa : f a = 0
        · exact Or.inl hfa
        · exact Or.inr ⟨hfa, ht a (Finset.mem_insert_self _ _) hfa⟩
      · by_cases hfa : f a = 0
        · rw [hfa, zero_add]; exact Or.inr ⟨hne, hlt⟩
        · by_cases hsum : f a + ∑ i ∈ t, f i = 0
          · exact Or.inl hsum
          · refine Or.inr ⟨hsum, lt_of_le_of_lt (v.map_add_le hfa hne hsum) ?_⟩
            exact max_lt (ht a (Finset.mem_insert_self _ _) hfa) hlt
  rw [← Finset.add_sum_erase s f hi₀]
  rcases hrest (s.erase i₀) (fun i hi => hmax i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
    with h0 | ⟨hne, hlt⟩
  · rw [h0, add_zero]; exact hf₀
  · rw [add_comm]; exact v.add_ne_zero_of_lt hne hlt

/-- Degree valuation on `RatFunc K` into `ℤ`. -/
noncomputable def Val.ratFuncBase (K : Type) [Field K] : Val (RatFunc K) ℤ :=
  let vp (p : K[X]) : ℤ := p.natDegree
  have hvp_mul : ∀ {p q : K[X]}, p ≠ 0 → q ≠ 0 → vp (p * q) = vp p + vp q := fun hp hq => by
    simp [vp, Polynomial.natDegree_mul hp hq]
  have hvp_add : ∀ {p q : K[X]}, vp (p + q) ≤ max (vp p) (vp q) := fun {p q} => by
    dsimp only [vp]; exact_mod_cast Polynomial.natDegree_add_le p q
  let vf (f : RatFunc K) : ℤ := vp f.num - vp f.denom
  have hvf_eq : ∀ {f : RatFunc K} {p q : K[X]}, p ≠ 0 → q ≠ 0 →
      f = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q →
      vf f = vp p - vp q := by
    intro f p q hp hq hfq
    have hf0 : f ≠ 0 := by
      rw [hfq]; exact div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
    have hnum := RatFunc.num_ne_zero hf0
    have hden := RatFunc.denom_ne_zero f
    have hcross : f.num * q = p * f.denom := by
      apply RatFunc.algebraMap_injective K
      rw [_root_.map_mul, _root_.map_mul]
      have h1 : algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom =
          algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q := by
        rw [RatFunc.num_div_denom, hfq]
      exact (div_eq_div_iff (RatFunc.algebraMap_ne_zero hden) (RatFunc.algebraMap_ne_zero hq)).mp h1
    have h := congr_arg vp hcross
    rw [hvp_mul hnum hq, hvp_mul hp hden] at h
    dsimp only [vf]; omega
  { toFun := vf
    map_mul := fun {x y} hx hy => by
      have hxn := RatFunc.num_ne_zero hx; have hxd := RatFunc.denom_ne_zero x
      have hyn := RatFunc.num_ne_zero hy; have hyd := RatFunc.denom_ne_zero y
      have hmul : x * y = algebraMap K[X] (RatFunc K) (x.num * y.num) /
          algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
        rw [_root_.map_mul, _root_.map_mul, mul_div_mul_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
      rw [hvf_eq (mul_ne_zero hxn hyn) (mul_ne_zero hxd hyd) hmul, hvp_mul hxn hyn, hvp_mul hxd hyd]
      dsimp only [vf]; omega
    map_add_le := fun {x y} hx hy hxy => by
      have hxn := RatFunc.num_ne_zero hx; have hxd := RatFunc.denom_ne_zero x
      have hyn := RatFunc.num_ne_zero hy; have hyd := RatFunc.denom_ne_zero y
      have hadd_eq : x + y = algebraMap K[X] (RatFunc K) (x.num * y.denom + x.denom * y.num) /
          algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
        rw [_root_.map_add, _root_.map_mul, _root_.map_mul, _root_.map_mul,
          ← div_add_div _ _ (RatFunc.algebraMap_ne_zero hxd) (RatFunc.algebraMap_ne_zero hyd),
          RatFunc.num_div_denom, RatFunc.num_div_denom]
      have hnum0 : x.num * y.denom + x.denom * y.num ≠ 0 := by
        intro h0; apply hxy; rw [hadd_eq, h0, _root_.map_zero, zero_div]
      rw [hvf_eq hnum0 (mul_ne_zero hxd hyd) hadd_eq, hvp_mul hxd hyd]
      have hle := hvp_add (p := x.num * y.denom) (q := x.denom * y.num)
      rw [hvp_mul hxn hyd, hvp_mul hxd hyn] at hle
      dsimp only [vf]; omega }

/-- Extend a valuation from `K` to `RatFunc K` into `ℤ ×ₗ Γ`. -/
noncomputable def Val.ratFunc {K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) : Val (RatFunc K) (ℤ ×ₗ Γ) :=
  let vp (p : K[X]) : ℤ ×ₗ Γ := toLex ((p.natDegree : ℤ), v.toFun p.leadingCoeff)
  have hvp_mul : ∀ {p q : K[X]}, p ≠ 0 → q ≠ 0 → vp (p * q) = vp p + vp q := by
    intro p q hp hq
    apply ofLex.injective
    ext
    · simp [vp, Polynomial.natDegree_mul hp hq]
    · simp [vp, Polynomial.leadingCoeff_mul,
        v.map_mul (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hq)]
  have hvp_add : ∀ {p q : K[X]}, p ≠ 0 → q ≠ 0 → p + q ≠ 0 →
      vp (p + q) ≤ max (vp p) (vp q) := by
    intro p q hp hq hpq
    by_cases hlt : p.natDegree < q.natDegree
    · apply le_max_of_le_right
      have hdeg := Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
      have hlc := Polynomial.leadingCoeff_add_of_degree_lt (Polynomial.degree_lt_degree hlt)
      simp [vp, hdeg, hlc]
    · by_cases hgt : q.natDegree < p.natDegree
      · apply le_max_of_le_left
        have hdeg := Polynomial.natDegree_add_eq_left_of_natDegree_lt hgt
        have hlc := Polynomial.leadingCoeff_add_of_degree_lt' (Polynomial.degree_lt_degree hgt)
        simp [vp, hdeg, hlc]
      · have heq : p.natDegree = q.natDegree := by omega
        have hle : (p + q).natDegree ≤ p.natDegree := by
          simpa [heq] using Polynomial.natDegree_add_le p q
        rcases lt_or_eq_of_le hle with hlt' | heq'
        · exact le_max_of_le_left (Prod.Lex.le_iff.mpr (Or.inl (by simp only [vp, ofLex_toLex]; exact_mod_cast hlt')))
        · have hlc : (p + q).leadingCoeff = p.leadingCoeff + q.leadingCoeff := by
            rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, Polynomial.leadingCoeff,
              heq', ← heq, Polynomial.coeff_add]
          have hadd := v.map_add_le (Polynomial.leadingCoeff_ne_zero.mpr hp)
            (Polynomial.leadingCoeff_ne_zero.mpr hq)
            (by rw [← hlc]; exact Polynomial.leadingCoeff_ne_zero.mpr hpq)
          rw [← hlc] at hadd
          rcases le_max_iff.mp hadd with h1 | h2
          · exact le_max_of_le_left (Prod.Lex.le_iff.mpr (Or.inr ⟨by simp [vp, heq'], h1⟩))
          · exact le_max_of_le_right (Prod.Lex.le_iff.mpr (Or.inr ⟨by simp [vp, heq', heq], h2⟩))
  let vf (f : RatFunc K) : ℤ ×ₗ Γ := vp f.num - vp f.denom
  have hvf_eq : ∀ {f : RatFunc K} {p q : K[X]}, p ≠ 0 → q ≠ 0 →
      f = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q →
      vf f = vp p - vp q := by
    intro f p q hp hq hfq
    have hf0 : f ≠ 0 := by
      rw [hfq]; exact div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
    have hnum := RatFunc.num_ne_zero hf0
    have hden := RatFunc.denom_ne_zero f
    have hcross : f.num * q = p * f.denom := by
      apply RatFunc.algebraMap_injective K
      rw [_root_.map_mul, _root_.map_mul]
      have h1 : algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom =
          algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q := by
        rw [RatFunc.num_div_denom, hfq]
      exact (div_eq_div_iff (RatFunc.algebraMap_ne_zero hden) (RatFunc.algebraMap_ne_zero hq)).mp h1
    have h := congr_arg vp hcross
    rw [hvp_mul hnum hq, hvp_mul hp hden] at h
    dsimp only [vf]
    exact sub_eq_sub_iff_add_eq_add.mpr (by rw [h, add_comm])
  { toFun := vf
    map_mul := fun {x y} hx hy => by
      have hxn := RatFunc.num_ne_zero hx; have hxd := RatFunc.denom_ne_zero x
      have hyn := RatFunc.num_ne_zero hy; have hyd := RatFunc.denom_ne_zero y
      have hmul : x * y = algebraMap K[X] (RatFunc K) (x.num * y.num) /
          algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
        rw [_root_.map_mul, _root_.map_mul, mul_div_mul_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
      rw [hvf_eq (mul_ne_zero hxn hyn) (mul_ne_zero hxd hyd) hmul,
        hvp_mul hxn hyn, hvp_mul hxd hyd]
      dsimp only [vf]; abel
    map_add_le := fun {x y} hx hy hxy => by
      have hxn := RatFunc.num_ne_zero hx; have hxd := RatFunc.denom_ne_zero x
      have hyn := RatFunc.num_ne_zero hy; have hyd := RatFunc.denom_ne_zero y
      have hadd_eq : x + y = algebraMap K[X] (RatFunc K) (x.num * y.denom + x.denom * y.num) /
          algebraMap K[X] (RatFunc K) (x.denom * y.denom) := by
        rw [_root_.map_add, _root_.map_mul, _root_.map_mul, _root_.map_mul,
          ← div_add_div _ _ (RatFunc.algebraMap_ne_zero hxd) (RatFunc.algebraMap_ne_zero hyd),
          RatFunc.num_div_denom, RatFunc.num_div_denom]
      have hnum0 : x.num * y.denom + x.denom * y.num ≠ 0 := by
        intro h0; apply hxy; rw [hadd_eq, h0, _root_.map_zero, zero_div]
      rw [hvf_eq hnum0 (mul_ne_zero hxd hyd) hadd_eq, hvp_mul hxd hyd]
      have hle := hvp_add (mul_ne_zero hxn hyd) (mul_ne_zero hxd hyn) hnum0
      rw [hvp_mul hxn hyd, hvp_mul hxd hyn] at hle
      rcases le_max_iff.mp hle with h1 | h2
      · apply le_max_of_le_left
        calc vp (x.num * y.denom + x.denom * y.num) - (vp x.denom + vp y.denom)
            ≤ (vp x.num + vp y.denom) - (vp x.denom + vp y.denom) := sub_le_sub_right h1 _
          _ = vf x := by dsimp only [vf]; abel
      · apply le_max_of_le_right
        calc vp (x.num * y.denom + x.denom * y.num) - (vp x.denom + vp y.denom)
            ≤ (vp x.denom + vp y.num) - (vp x.denom + vp y.denom) := sub_le_sub_right h2 _
          _ = vf y := by dsimp only [vf]; abel }

lemma Val.ratFuncBase_algMap {K : Type} [Field K] {p : K[X]} (hp : p ≠ 0) :
    (Val.ratFuncBase K).toFun (algebraMap K[X] (RatFunc K) p) = (p.natDegree : ℤ) := by
  have h1 : (algebraMap K[X] (RatFunc K) p).num = p * (algebraMap K[X] (RatFunc K) p).denom := by
    apply RatFunc.algebraMap_injective K
    rw [_root_.map_mul]
    have h := RatFunc.num_div_denom (algebraMap K[X] (RatFunc K) p)
    exact (div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))).mp h
  have hden := RatFunc.denom_ne_zero (algebraMap K[X] (RatFunc K) p)
  have hdeg := congr_arg Polynomial.natDegree h1
  rw [Polynomial.natDegree_mul hp hden] at hdeg
  change ((algebraMap K[X] (RatFunc K) p).num.natDegree : ℤ) -
    ((algebraMap K[X] (RatFunc K) p).denom.natDegree : ℤ) = (p.natDegree : ℤ)
  omega

lemma Val.ratFunc_algMap {K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) {p : K[X]} (hp : p ≠ 0) :
    v.ratFunc.toFun (algebraMap K[X] (RatFunc K) p) =
      toLex ((p.natDegree : ℤ), v.toFun p.leadingCoeff) := by
  have h1 : (algebraMap K[X] (RatFunc K) p).num = p * (algebraMap K[X] (RatFunc K) p).denom := by
    apply RatFunc.algebraMap_injective K
    rw [_root_.map_mul]
    have h := RatFunc.num_div_denom (algebraMap K[X] (RatFunc K) p)
    exact (div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))).mp h
  have hden := RatFunc.denom_ne_zero (algebraMap K[X] (RatFunc K) p)
  have hdeg := congr_arg Polynomial.natDegree h1
  rw [Polynomial.natDegree_mul hp hden] at hdeg
  have hlc := congr_arg Polynomial.leadingCoeff h1
  rw [Polynomial.leadingCoeff_mul] at hlc
  have hvl := congr_arg v.toFun hlc
  rw [v.map_mul (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hden)] at hvl
  apply ofLex.injective
  ext
  · change ((algebraMap K[X] (RatFunc K) p).num.natDegree : ℤ) -
      ((algebraMap K[X] (RatFunc K) p).denom.natDegree : ℤ) = (p.natDegree : ℤ)
    omega
  · change v.toFun (algebraMap K[X] (RatFunc K) p).num.leadingCoeff -
      v.toFun (algebraMap K[X] (RatFunc K) p).denom.leadingCoeff = v.toFun p.leadingCoeff
    rw [hvl, add_sub_cancel_right]

lemma countable_poly (K : Type) [Field K] [Countable K] : Countable K[X] := by
  have hinj : Function.Injective (fun p : K[X] => List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) := by
    intro p q h
    have hlen : p.natDegree + 1 = q.natDegree + 1 := by
      simpa using congr_arg List.length h
    have hdeg : p.natDegree = q.natDegree := by omega
    ext n
    by_cases hn : n < p.natDegree + 1
    · have hget := congr_arg (fun l : List K => l[n]?) h
      rw [List.getElem?_ofFn, List.getElem?_ofFn] at hget
      have hn' : n < q.natDegree + 1 := by omega
      simp only [dif_pos hn, dif_pos hn', Option.some.injEq] at hget
      exact hget
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  exact Function.Injective.countable hinj

lemma countable_ratFunc (K : Type) [Field K] [Countable K] : Countable (RatFunc K) := by
  have : Countable K[X] := countable_poly K
  have hinj : Function.Injective (fun f : RatFunc K => (f.num, f.denom)) := fun f g h => by
    have h1 : f.num = g.num := congr_arg Prod.fst h
    have h2 : f.denom = g.denom := congr_arg Prod.snd h
    rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g, h1, h2]
  exact Function.Injective.countable hinj

abbrev K₁ : Type := RatFunc ℚ
noncomputable instance : Field K₁ := RatFunc.instField ℚ
instance : Countable K₁ := countable_ratFunc ℚ

abbrev K₂ : Type := RatFunc K₁
noncomputable instance : Field K₂ := RatFunc.instField K₁
instance : Countable K₂ := countable_ratFunc K₁

abbrev K₃ : Type := RatFunc K₂
noncomputable instance : Field K₃ := RatFunc.instField K₂
instance : Countable K₃ := countable_ratFunc K₂

abbrev K₄ : Type := RatFunc K₃
noncomputable instance : Field K₄ := RatFunc.instField K₃
instance : Countable K₄ := countable_ratFunc K₃

abbrev Γ₄ := ℤ ×ₗ (ℤ ×ₗ (ℤ ×ₗ ℤ))

noncomputable def v₄ : Val K₄ Γ₄ :=
  (((Val.ratFuncBase ℚ).ratFunc).ratFunc).ratFunc

noncomputable def liftC {K : Type} [Field K] (a : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (Polynomial.C a)

lemma liftC_ne_zero {K : Type} [Field K] {a : K} (ha : a ≠ 0) : liftC a ≠ 0 :=
  RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr ha)

lemma Val.ratFunc_liftC {K Γ : Type} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : Val K Γ) {a : K} (ha : a ≠ 0) :
    v.ratFunc.toFun (liftC a) = toLex (0, v.toFun a) := by
  rw [liftC, Val.ratFunc_algMap _ (Polynomial.C_ne_zero.mpr ha)]
  simp

noncomputable def t₁ : K₄ := liftC (liftC (liftC (algebraMap ℚ[X] K₁ Polynomial.X)))
noncomputable def t₂ : K₄ := liftC (liftC (algebraMap K₁[X] K₂ Polynomial.X))
noncomputable def t₃ : K₄ := liftC (algebraMap K₂[X] K₃ Polynomial.X)
noncomputable def t₄ : K₄ := algebraMap K₃[X] K₄ Polynomial.X

lemma t₁_ne : t₁ ≠ 0 :=
  liftC_ne_zero (liftC_ne_zero (liftC_ne_zero (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)))

lemma t₂_ne : t₂ ≠ 0 :=
  liftC_ne_zero (liftC_ne_zero (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero))

lemma t₃_ne : t₃ ≠ 0 :=
  liftC_ne_zero (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)

lemma t₄_ne : t₄ ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

lemma lex4_ext {a b : Γ₄}
    (h1 : (ofLex a).1 = (ofLex b).1)
    (h2 : (ofLex (ofLex a).2).1 = (ofLex (ofLex b).2).1)
    (h3 : (ofLex (ofLex (ofLex a).2).2).1 = (ofLex (ofLex (ofLex b).2).2).1)
    (h4 : (ofLex (ofLex (ofLex a).2).2).2 = (ofLex (ofLex (ofLex b).2).2).2) :
    a = b := by
  apply ofLex.injective; ext
  · exact h1
  · apply ofLex.injective; ext
    · exact h2
    · apply ofLex.injective; ext
      · exact h3
      · exact h4

lemma v₄_t₁ : v₄.toFun t₁ = toLex (0, toLex (0, toLex (0, 1))) := by
  have h0 : algebraMap ℚ[X] K₁ Polynomial.X ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have h1 : liftC (algebraMap ℚ[X] K₁ Polynomial.X) ≠ 0 := liftC_ne_zero h0
  have h2 : liftC (liftC (algebraMap ℚ[X] K₁ Polynomial.X)) ≠ 0 := liftC_ne_zero h1
  dsimp only [v₄, t₁]
  rw [Val.ratFunc_liftC _ h2, Val.ratFunc_liftC _ h1, Val.ratFunc_liftC _ h0,
    Val.ratFuncBase_algMap Polynomial.X_ne_zero]
  simp

lemma v₄_t₂ : v₄.toFun t₂ = toLex (0, toLex (0, toLex (1, 0))) := by
  have h1 : algebraMap K₁[X] K₂ Polynomial.X ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have h2 : liftC (algebraMap K₁[X] K₂ Polynomial.X) ≠ 0 := liftC_ne_zero h1
  dsimp only [v₄, t₂]
  rw [Val.ratFunc_liftC _ h2, Val.ratFunc_liftC _ h1, Val.ratFunc_algMap _ Polynomial.X_ne_zero]
  simp [Val.map_one]

lemma v₄_t₃ : v₄.toFun t₃ = toLex (0, toLex (1, toLex (0, 0))) := by
  have h1 : algebraMap K₂[X] K₃ Polynomial.X ≠ 0 := RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  dsimp only [v₄, t₃]
  rw [Val.ratFunc_liftC _ h1, Val.ratFunc_algMap _ Polynomial.X_ne_zero]
  simp [Val.map_one]
  rfl

lemma v₄_t₄ : v₄.toFun t₄ = toLex (1, toLex (0, toLex (0, 0))) := by
  dsimp only [v₄, t₄]
  rw [Val.ratFunc_algMap _ Polynomial.X_ne_zero]
  simp [Val.map_one]
  rfl

def fxor (i j : Fin 4) : Fin 4 :=
  ⟨i.1 ^^^ j.1, by fin_cases i <;> fin_cases j <;> decide⟩

lemma fxor_invol (i j : Fin 4) : fxor i (fxor i j) = j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma fxor_eq_iff (i j k : Fin 4) : fxor i j = k ↔ j = fxor i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

def qcoeff {F : Type} [Field F] (a b : F) (i j : Fin 4) : F :=
  match i.1, j.1 with
  | 0, _ => 1
  | _, 0 => 1
  | 1, 1 => a
  | 1, 2 => 1
  | 1, 3 => a
  | 2, 1 => -1
  | 2, 2 => b
  | 2, 3 => -b
  | 3, 1 => -a
  | 3, 2 => b
  | 3, 3 => -(a * b)
  | _, _ => 1

lemma basisOneIJK_mul {F : Type} [Field F] (a b : F) (i j : Fin 4) :
    QuaternionAlgebra.basisOneIJK a 0 b i * QuaternionAlgebra.basisOneIJK a 0 b j =
      qcoeff a b i j • QuaternionAlgebra.basisOneIJK a 0 b (fxor i j) := by
  fin_cases i <;> fin_cases j <;> ext <;> simp [QuaternionAlgebra.basisOneIJK, qcoeff, fxor]

lemma qcoeff_ne_zero {F : Type} [Field F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (i j : Fin 4) :
    qcoeff a b i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [qcoeff, ha, hb]

def δ (p : Fin 4 × Fin 4) : Γ₄ :=
  toLex ((p.2.1 / 2 : ℤ), toLex ((p.2.1 % 2 : ℤ), toLex ((p.1.1 / 2 : ℤ), (p.1.1 % 2 : ℤ))))

lemma δ_parity_inj {u w : Γ₄} {p q : Fin 4 × Fin 4}
    (h : u + u + δ p = w + w + δ q) : p = q := by
  have h1 := congr_arg (fun g : Γ₄ => (ofLex g).1) h
  have h2 := congr_arg (fun g : Γ₄ => (ofLex (ofLex g).2).1) h
  have h3 := congr_arg (fun g : Γ₄ => (ofLex (ofLex (ofLex g).2).2).1) h
  have h4 := congr_arg (fun g : Γ₄ => (ofLex (ofLex (ofLex g).2).2).2) h
  simp only [δ, ofLex_add, ofLex_toLex, Prod.fst_add, Prod.snd_add] at h1 h2 h3 h4
  ext <;> omega

lemma qcoeff_val_left (i j : Fin 4) :
    v₄.toFun (qcoeff t₁ t₂ i j) + v₄.toFun (qcoeff t₁ t₂ i j) + δ (fxor i j, 0) =
      δ (i, 0) + δ (j, 0) := by
  fin_cases i <;> fin_cases j <;>
    apply lex4_ext <;>
    simp [qcoeff, fxor, δ, v₄.map_one, v₄.map_neg, v₄.map_mul, t₁_ne, t₂_ne, v₄_t₁, v₄_t₂,
      ofLex_add, ofLex_toLex]

lemma qcoeff_val_right (i j : Fin 4) :
    v₄.toFun (qcoeff t₃ t₄ i j) + v₄.toFun (qcoeff t₃ t₄ i j) + δ (0, fxor i j) =
      δ (0, i) + δ (0, j) := by
  fin_cases i <;> fin_cases j <;>
    apply lex4_ext <;>
    simp [qcoeff, fxor, δ, v₄.map_one, v₄.map_neg, v₄.map_mul, t₃_ne, t₄_ne, v₄_t₃, v₄_t₄,
      ofLex_add, ofLex_toLex]

lemma δ_split (p : Fin 4 × Fin 4) : δ p = δ (p.1, 0) + δ (0, p.2) := by
  apply lex4_ext <;> simp [δ, ofLex_add, ofLex_toLex]

def pxor (p q : Fin 4 × Fin 4) : Fin 4 × Fin 4 := (fxor p.1 q.1, fxor p.2 q.2)

noncomputable def pcoeff (p q : Fin 4 × Fin 4) : K₄ :=
  qcoeff t₁ t₂ p.1 q.1 * qcoeff t₃ t₄ p.2 q.2

lemma pcoeff_ne_zero (p q : Fin 4 × Fin 4) : pcoeff p q ≠ 0 :=
  mul_ne_zero (qcoeff_ne_zero t₁_ne t₂_ne p.1 q.1) (qcoeff_ne_zero t₃_ne t₄_ne p.2 q.2)

lemma pcoeff_val (p q : Fin 4 × Fin 4) :
    v₄.toFun (pcoeff p q) + v₄.toFun (pcoeff p q) + δ (pxor p q) = δ p + δ q := by
  have h1 := qcoeff_val_left p.1 q.1
  have h2 := qcoeff_val_right p.2 q.2
  rw [pcoeff, v₄.map_mul (qcoeff_ne_zero t₁_ne t₂_ne p.1 q.1) (qcoeff_ne_zero t₃_ne t₄_ne p.2 q.2),
    δ_split (pxor p q), δ_split p, δ_split q]
  dsimp only [pxor]
  calc v₄.toFun (qcoeff t₁ t₂ p.1 q.1) + v₄.toFun (qcoeff t₃ t₄ p.2 q.2) +
      (v₄.toFun (qcoeff t₁ t₂ p.1 q.1) + v₄.toFun (qcoeff t₃ t₄ p.2 q.2)) +
      (δ (fxor p.1 q.1, 0) + δ (0, fxor p.2 q.2))
      = (v₄.toFun (qcoeff t₁ t₂ p.1 q.1) + v₄.toFun (qcoeff t₁ t₂ p.1 q.1) + δ (fxor p.1 q.1, 0)) +
        (v₄.toFun (qcoeff t₃ t₄ p.2 q.2) + v₄.toFun (qcoeff t₃ t₄ p.2 q.2) + δ (0, fxor p.2 q.2)) := by abel
    _ = (δ (p.1, 0) + δ (q.1, 0)) + (δ (0, p.2) + δ (0, q.2)) := by rw [h1, h2]
    _ = δ (p.1, 0) + δ (0, p.2) + (δ (q.1, 0) + δ (0, q.2)) := by abel

theorem noZeroDivisors_biquat :
    NoZeroDivisors (QuaternionAlgebra K₄ t₁ 0 t₂ ⊗[K₄] QuaternionAlgebra K₄ t₃ 0 t₄) := by
  classical
  let B := (QuaternionAlgebra.basisOneIJK t₁ 0 t₂).tensorProduct
    (QuaternionAlgebra.basisOneIJK t₃ 0 t₄)
  have hBmul : ∀ p q : Fin 4 × Fin 4, B p * B q = pcoeff p q • B (pxor p q) := fun ⟨p1, p2⟩ ⟨q1, q2⟩ => by
    simp only [B, pxor, Module.Basis.tensorProduct_apply]
    rw [Algebra.TensorProduct.tmul_mul_tmul, basisOneIJK_mul, basisOneIJK_mul,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul, mul_comm]
    rfl
  have hrepr_mul : ∀ x y r, B.repr (x * y) r =
      ∑ p : Fin 4 × Fin 4, B.repr x p * B.repr y (pxor p r) * pcoeff p (pxor p r) := by
    intro x y r
    conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm, hBmul, smul_smul, map_sum, map_smul,
      Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single (pxor p r)]
    · have hinv : pxor p (pxor p r) = r := Prod.ext (fxor_invol _ _) (fxor_invol _ _)
      simp [hinv, mul_assoc]
    · intro q _ hq
      have hne : pxor p q ≠ r := fun h => hq (Prod.ext ((fxor_eq_iff _ _ _).mp (congr_arg Prod.fst h))
        ((fxor_eq_iff _ _ _).mp (congr_arg Prod.snd h)))
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨fun {x y} hxy => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  have hSx : (Finset.univ.filter fun p : Fin 4 × Fin 4 => B.repr x p ≠ 0).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hx; apply B.repr.injective; ext p
    have hp : p ∉ Finset.univ.filter (fun p => B.repr x p ≠ 0) := by rw [hempty]; simp
    simpa using hp
  have hSy : (Finset.univ.filter fun q : Fin 4 × Fin 4 => B.repr y q ≠ 0).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hy; apply B.repr.injective; ext q
    have hq : q ∉ Finset.univ.filter (fun q => B.repr y q ≠ 0) := by rw [hempty]; simp
    simpa using hq
  let wx (p : Fin 4 × Fin 4) : Γ₄ := v₄.toFun (B.repr x p) + v₄.toFun (B.repr x p) + δ p
  let wy (q : Fin 4 × Fin 4) : Γ₄ := v₄.toFun (B.repr y q) + v₄.toFun (B.repr y q) + δ q
  obtain ⟨p₀, hp₀, hmax_x⟩ := Finset.exists_max_image _ wx hSx
  obtain ⟨q₀, hq₀, hmax_y⟩ := Finset.exists_max_image _ wy hSy
  have hxp₀ : B.repr x p₀ ≠ 0 := (Finset.mem_filter.mp hp₀).2
  have hyq₀ : B.repr y q₀ ≠ 0 := (Finset.mem_filter.mp hq₀).2
  have hlt_x : ∀ p, p ≠ p₀ → B.repr x p ≠ 0 → wx p < wx p₀ := fun p hne hp =>
    lt_of_le_of_ne (hmax_x p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
      (fun heq => hne (δ_parity_inj heq))
  let r₀ := pxor p₀ q₀
  have hr₀ : B.repr (x * y) r₀ ≠ 0 := by
    rw [hrepr_mul x y r₀]
    have hq₀_eq : pxor p₀ r₀ = q₀ := Prod.ext (fxor_invol _ _) (fxor_invol _ _)
    apply v₄.sum_ne_zero_of_unique_max Finset.univ _ p₀ (Finset.mem_univ _)
    · rw [hq₀_eq]; exact mul_ne_zero (mul_ne_zero hxp₀ hyq₀) (pcoeff_ne_zero p₀ q₀)
    · intro p _ hne hterm
      have hxp : B.repr x p ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hterm)
      have hyq : B.repr y (pxor p r₀) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hterm)
      have hle_y : wy (pxor p r₀) ≤ wy q₀ :=
        hmax_y _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyq⟩)
      have hlt_sum : wx p + wy (pxor p r₀) < wx p₀ + wy q₀ :=
        add_lt_add_of_lt_of_le (hlt_x p hne hxp) hle_y
      have hval : ∀ p' : Fin 4 × Fin 4, B.repr x p' ≠ 0 → B.repr y (pxor p' r₀) ≠ 0 →
          v₄.toFun (B.repr x p' * B.repr y (pxor p' r₀) * pcoeff p' (pxor p' r₀)) +
          v₄.toFun (B.repr x p' * B.repr y (pxor p' r₀) * pcoeff p' (pxor p' r₀)) + δ r₀ =
          wx p' + wy (pxor p' r₀) := by
        intro p' h1 h2
        rw [v₄.map_mul (mul_ne_zero h1 h2) (pcoeff_ne_zero _ _), v₄.map_mul h1 h2]
        have hpv := pcoeff_val p' (pxor p' r₀)
        have hinv : pxor p' (pxor p' r₀) = r₀ := Prod.ext (fxor_invol _ _) (fxor_invol _ _)
        rw [hinv] at hpv
        dsimp only [wx, wy]
        calc v₄.toFun ((B.repr x) p') + v₄.toFun ((B.repr y) (pxor p' r₀)) + v₄.toFun (pcoeff p' (pxor p' r₀)) +
            (v₄.toFun ((B.repr x) p') + v₄.toFun ((B.repr y) (pxor p' r₀)) + v₄.toFun (pcoeff p' (pxor p' r₀))) + δ r₀
            = (v₄.toFun ((B.repr x) p') + v₄.toFun ((B.repr x) p')) +
              (v₄.toFun ((B.repr y) (pxor p' r₀)) + v₄.toFun ((B.repr y) (pxor p' r₀))) +
              (v₄.toFun (pcoeff p' (pxor p' r₀)) + v₄.toFun (pcoeff p' (pxor p' r₀)) + δ r₀) := by abel
          _ = (v₄.toFun ((B.repr x) p') + v₄.toFun ((B.repr x) p')) +
              (v₄.toFun ((B.repr y) (pxor p' r₀)) + v₄.toFun ((B.repr y) (pxor p' r₀))) +
              (δ p' + δ (pxor p' r₀)) := by rw [hpv]
          _ = v₄.toFun ((B.repr x) p') + v₄.toFun ((B.repr x) p') + δ p' +
              (v₄.toFun ((B.repr y) (pxor p' r₀)) + v₄.toFun ((B.repr y) (pxor p' r₀)) + δ (pxor p' r₀)) := by abel
      have h1 := hval p hxp hyq
      have h2 := hval p₀ hxp₀ (by rw [hq₀_eq]; exact hyq₀)
      have hlt_sum' : wx p + wy (pxor p r₀) < wx p₀ + wy (pxor p₀ r₀) := by rw [hq₀_eq]; exact hlt_sum
      have hdouble : v₄.toFun (B.repr x p * B.repr y (pxor p r₀) * pcoeff p (pxor p r₀)) +
          v₄.toFun (B.repr x p * B.repr y (pxor p r₀) * pcoeff p (pxor p r₀)) <
          v₄.toFun (B.repr x p₀ * B.repr y (pxor p₀ r₀) * pcoeff p₀ (pxor p₀ r₀)) +
          v₄.toFun (B.repr x p₀ * B.repr y (pxor p₀ r₀) * pcoeff p₀ (pxor p₀ r₀)) := by
        have := lt_of_eq_of_lt h1 (lt_of_lt_of_eq hlt_sum' h2.symm)
        exact lt_of_add_lt_add_right this
      by_contra hge
      push Not at hge
      exact not_lt_of_ge (add_le_add hge hge) hdouble
  exact hr₀ (by rw [hxy, map_zero]; rfl)

theorem test_H1 :
    ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)) (_ : Countable F) (a b c d : F),
      NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d) :=
  ⟨K₄, inferInstance, inferInstance, inferInstance, t₁, t₂, t₃, t₄, noZeroDivisors_biquat⟩

end OMA.KaplanskyH1

theorem OMA.solution : OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.H1 :=
  OMA.KaplanskyH1.test_H1
