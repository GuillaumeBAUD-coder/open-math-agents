import OMAReductions.R_mse_2615963_R3
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Proof of `mse-2615963.R3.H1`

Evaluates `∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ m).eval k` modulo an odd prime `p`.

Working over `F = ZMod p`, pick a non-square `d : F` and form the quadratic extension field
`K = QuadraticAlgebra F d 0`. Let `A ≤ Kˣ` be the image of `Fˣ` (order `p - 1`) and
`B ≤ Kˣ` be the norm-1 subgroup `{u ∈ Kˣ | u.re^2 - d * u.im^2 = 1}` (order `p + 1`,
proved via rational stereographic parametrization `t ↦ ((1 + d t^2)/(1 - d t^2), 2 t/(1 - d t^2))`).

Every `x ∈ F` has total preimage size `2` under the pair of maps `u ↦ (u + u⁻¹).re` from `A`
and `B` (with `x = ±2` contributing `1` from `A` and `1` from `B`). Using the Chebyshev identity
`C_m(u + u⁻¹) = u^m + u^{-m}` and `u ↦ u⁻¹` symmetry, we obtain
`2 * ∑ x : F, C_m(x) = 2 * (∑ u ∈ A, u^m + ∑ u ∈ B, u^m)` in `K`.
Since `A` and `B` are finite cyclic subgroups of `Kˣ` of orders `p - 1` and `p + 1`, the power
sums evaluate to `(if (p - 1) ∣ m then -1 else 0)` and `(if (p + 1) ∣ m then 1 else 0)` in `F`.
-/

namespace Mse2615963R3H1Proof

open Polynomial

private lemma exists_nonsquare (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ d : ZMod p, ∀ x : ZMod p, x ^ 2 ≠ d := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hp : p.Prime := Fact.out
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  have hnotinj : ¬ Function.Injective (fun x : ZMod p => x ^ 2) := by
    intro hinj
    have h1 : (1 : ZMod p) ^ 2 = (-1 : ZMod p) ^ 2 := by ring
    have heq : (1 : ZMod p) = -1 := hinj h1
    apply h2ne
    linear_combination heq
  have hnotsurj : ¬ Function.Surjective (fun x : ZMod p => x ^ 2) := fun hsurj =>
    hnotinj (Finite.injective_iff_surjective.mpr hsurj)
  rw [Function.Surjective] at hnotsurj
  push Not at hnotsurj
  exact hnotsurj

private lemma sq_sub_mul_sq_ne_zero {p : ℕ} [Fact p.Prime] {d : ZMod p}
    (hd : ∀ x : ZMod p, x ^ 2 ≠ d) {a b : ZMod p} (hab : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 - d * b ^ 2 ≠ 0 := by
  intro h0
  by_cases hb : b = 0
  · subst hb
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      sq_eq_zero_iff] at h0
    rcases hab with ha | hb'
    · exact ha h0
    · exact hb' rfl
  · apply hd (a / b)
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hb)]
    linear_combination h0

private noncomputable def qInv {p : ℕ} [Fact p.Prime] (d : ZMod p)
    (x : QuadraticAlgebra (ZMod p) d 0) : QuadraticAlgebra (ZMod p) d 0 :=
  ⟨x.re * (x.re ^ 2 - d * x.im ^ 2)⁻¹, -x.im * (x.re ^ 2 - d * x.im ^ 2)⁻¹⟩

private lemma qMul_qInv {p : ℕ} [Fact p.Prime] {d : ZMod p} (hd : ∀ x : ZMod p, x ^ 2 ≠ d)
    (x : QuadraticAlgebra (ZMod p) d 0) (hx : x ≠ 0) :
    x * qInv d x = 1 := by
  have hab : x.re ≠ 0 ∨ x.im ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext <;> simp [h.1, h.2]
  have hn : x.re ^ 2 - d * x.im ^ 2 ≠ 0 := sq_sub_mul_sq_ne_zero hd hab
  ext
  · change x.re * (x.re * (x.re ^ 2 - d * x.im ^ 2)⁻¹) +
      d * x.im * (-x.im * (x.re ^ 2 - d * x.im ^ 2)⁻¹) = 1
    field_simp [hn]
    ring
  · change x.re * (-x.im * (x.re ^ 2 - d * x.im ^ 2)⁻¹) +
      x.im * (x.re * (x.re ^ 2 - d * x.im ^ 2)⁻¹) +
      0 * x.im * (-x.im * (x.re ^ 2 - d * x.im ^ 2)⁻¹) = 0
    ring

private lemma qIsDomain {p : ℕ} [Fact p.Prime] {d : ZMod p}
    (hd : ∀ x : ZMod p, x ^ 2 ≠ d) : IsDomain (QuadraticAlgebra (ZMod p) d 0) := by
  have : Nontrivial (QuadraticAlgebra (ZMod p) d 0) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg QuadraticAlgebra.re h)⟩⟩
  have : NoZeroDivisors (QuadraticAlgebra (ZMod p) d 0) :=
    ⟨fun {x y} hxy => by
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        have h := congrArg (qInv d x * ·) hxy
        rw [← mul_assoc, mul_comm (qInv d x) x, qMul_qInv hd x hx, one_mul, mul_zero] at h
        exact h⟩
  exact NoZeroDivisors.to_isDomain _

private noncomputable def qUnit {p : ℕ} [Fact p.Prime] {d : ZMod p}
    (hd : ∀ x : ZMod p, x ^ 2 ≠ d) (x : QuadraticAlgebra (ZMod p) d 0) (hx : x ≠ 0) :
    (QuadraticAlgebra (ZMod p) d 0)ˣ :=
  ⟨x, qInv d x, qMul_qInv hd x hx, by rw [mul_comm]; exact qMul_qInv hd x hx⟩

private lemma chebyshev_C_eval_add_inv {R : Type*} [CommRing R] (u : Rˣ) (m : ℕ) :
    (Chebyshev.C R (m : ℤ)).eval ((u : R) + ((u⁻¹ : Rˣ) : R)) =
      (u : R) ^ m + ((u⁻¹ : Rˣ) : R) ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      simp [Chebyshev.C_zero]
      ring
    | 1 =>
      simp [Chebyshev.C_one]
    | n + 2 =>
      have hrec : Chebyshev.C R ((n + 2 : ℕ) : ℤ) =
          X * Chebyshev.C R ((n + 1 : ℕ) : ℤ) - Chebyshev.C R (n : ℤ) := by
        push_cast
        exact Chebyshev.C_add_two R (n : ℤ)
      rw [hrec, eval_sub, eval_mul, eval_X, ih (n + 1) (by omega), ih n (by omega)]
      have huv : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by exact_mod_cast u.mul_inv
      have hvu : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by exact_mod_cast u.inv_mul
      calc ((u : R) + ((u⁻¹ : Rˣ) : R)) * ((u : R) ^ (n + 1) + ((u⁻¹ : Rˣ) : R) ^ (n + 1)) -
            ((u : R) ^ n + ((u⁻¹ : Rˣ) : R) ^ n)
          = (u : R) ^ (n + 2) + ((u⁻¹ : Rˣ) : R) ^ (n + 2) +
            ((u : R) * ((u⁻¹ : Rˣ) : R) - 1) * ((u : R) ^ n + ((u⁻¹ : Rˣ) : R) ^ n) := by
            ring
        _ = (u : R) ^ (n + 2) + ((u⁻¹ : Rˣ) : R) ^ (n + 2) := by
            rw [huv, sub_self, zero_mul, add_zero]

private lemma sum_subgroup_pow {K : Type*} [CommRing K] [IsDomain K] [Fintype K] [DecidableEq K]
    (G : Subgroup Kˣ) [Fintype G] (m : ℕ) :
    (∑ g : G, ((g : Kˣ) : K) ^ m) =
      if Fintype.card G ∣ m then (Fintype.card G : K) else 0 := by
  have : IsCyclic G := isCyclic_of_injective_ringHom
    (MonoidHom.comp (Units.coeHom K) G.subtype) (Units.val_injective.comp Subtype.val_injective)
  split_ifs with hdvd
  · have h1 : ∀ g : G, ((g : Kˣ) : K) ^ m = 1 := by
      intro g
      obtain ⟨k, rfl⟩ := hdvd
      have hg : g ^ Fintype.card G = 1 := pow_card_eq_one
      have hgk : (g ^ (Fintype.card G * k) : G) = 1 := by rw [pow_mul, hg, one_pow]
      have hcoe := congrArg (fun x : G => ((x : Kˣ) : K)) hgk
      simpa using hcoe
    simp [h1]
  · obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := G)
    have hord : orderOf g₀ = Fintype.card G := by
      rw [← Nat.card_eq_fintype_card]
      exact orderOf_eq_card_of_forall_mem_zpowers hg₀
    have hne1 : g₀ ^ m ≠ 1 := by
      intro h1
      exact hdvd (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    have hne1K : ((g₀ : Kˣ) : K) ^ m ≠ 1 := by
      intro h1
      apply hne1
      apply Subtype.ext
      apply Units.ext
      simpa using h1
    set S : K := ∑ g : G, ((g : Kˣ) : K) ^ m
    have hmul : ((g₀ : Kˣ) : K) ^ m * S = S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
      simp [mul_pow]
    have hzero : (((g₀ : Kˣ) : K) ^ m - 1) * S = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne1K)

private lemma mul_nonsquare_isSquare {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d y : ZMod p} (hd : ∀ x : ZMod p, x ^ 2 ≠ d) (hy0 : y ≠ 0) (hy : ∀ x : ZMod p, x ^ 2 ≠ y) :
    ∃ c : ZMod p, c ^ 2 = y / d := by
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  let sqHom : (ZMod p)ˣ →* (ZMod p)ˣ :=
    { toFun := fun u => u ^ 2
      map_one' := one_pow 2
      map_mul' := fun a b => mul_pow a b 2 }
  have hker_card : Nat.card sqHom.ker = 2 := by
    have hker_set : (sqHom.ker : Set (ZMod p)ˣ) = {1, -1} := by
      ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, sqHom]
      constructor
      · intro h
        have h' : (u : ZMod p) ^ 2 = 1 := by
          simpa [sqHom] using congrArg Units.val (MonoidHom.mem_ker.mp h)
        rcases sq_eq_one_iff.mp h' with h1 | h2
        · left; exact Units.ext h1
        · right; exact Units.ext h2
      · rintro (rfl | rfl) <;> simp
    have h1ne : (1 : (ZMod p)ˣ) ≠ -1 := by
      intro h
      have h' : (1 : ZMod p) = -1 := congrArg Units.val h
      have h2 : (2 : ZMod p) = 0 := by linear_combination h'
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
      have hp : p.Prime := Fact.out
      have := Nat.le_of_dvd (by decide) hdvd
      have := hp.two_le
      omega
    change Nat.card (sqHom.ker : Set (ZMod p)ˣ) = 2
    rw [Nat.card_coe_set_eq, hker_set, Set.ncard_pair h1ne]
  have hind : sqHom.range.index = 2 := by
    have hcard := Subgroup.card_mul_index sqHom.range
    have hrange := Subgroup.card_eq_card_quotient_mul_card_subgroup sqHom.ker
    have hiso := QuotientGroup.quotientKerEquivRange sqHom
    have h1 : Nat.card sqHom.range = Nat.card ((ZMod p)ˣ ⧸ sqHom.ker) :=
      Nat.card_congr hiso.symm.toEquiv
    have hpos : 0 < Nat.card sqHom.range := Nat.card_pos
    have hEq : Nat.card sqHom.range * sqHom.range.index = Nat.card sqHom.range * 2 := by
      rw [hcard, hrange, h1, hker_card]
    exact Nat.eq_of_mul_eq_mul_left hpos hEq
  let u_d : (ZMod p)ˣ := Units.mk0 d hd0
  let u_y : (ZMod p)ˣ := Units.mk0 y hy0
  have hd_not : u_d ∉ sqHom.range := by
    rintro ⟨v, hv⟩
    exact hd (v : ZMod p) (congrArg Units.val hv)
  have hy_not : u_y ∉ sqHom.range := by
    rintro ⟨v, hv⟩
    exact hy (v : ZMod p) (congrArg Units.val hv)
  -- Quotient by sqHom.range has cardinality 2, so two non-trivial cosets are equal
  have : Fintype ((ZMod p)ˣ ⧸ sqHom.range) := Fintype.ofFinite _
  have hqcard : Fintype.card ((ZMod p)ˣ ⧸ sqHom.range) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hind]
  have hne_one_d : (u_d : (ZMod p)ˣ ⧸ sqHom.range) ≠ 1 := by
    intro h
    exact hd_not ((QuotientGroup.eq_one_iff u_d).mp h)
  have hne_one_y : (u_y : (ZMod p)ˣ ⧸ sqHom.range) ≠ 1 := by
    intro h
    exact hy_not ((QuotientGroup.eq_one_iff u_y).mp h)
  have hcoset : (u_y : (ZMod p)ˣ ⧸ sqHom.range) = (u_d : (ZMod p)ˣ ⧸ sqHom.range) := by
    by_contra hne
    have h3 : ({1, (u_d : (ZMod p)ˣ ⧸ sqHom.range), (u_y : (ZMod p)ˣ ⧸ sqHom.range)} :
        Finset ((ZMod p)ˣ ⧸ sqHom.range)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne)]
      simp [hne_one_d.symm, hne_one_y.symm]
    have hle : ({1, (u_d : (ZMod p)ˣ ⧸ sqHom.range), (u_y : (ZMod p)ˣ ⧸ sqHom.range)} :
        Finset ((ZMod p)ˣ ⧸ sqHom.range)).card ≤ Fintype.card ((ZMod p)ˣ ⧸ sqHom.range) :=
      Finset.card_le_univ _
    omega
  have hmem : u_d⁻¹ * u_y ∈ sqHom.range := (QuotientGroup.eq.mp hcoset.symm)
  obtain ⟨v, hv⟩ := hmem
  refine ⟨(v : ZMod p), ?_⟩
  have hval := congrArg Units.val hv
  change (v : ZMod p) ^ 2 = d⁻¹ * y at hval
  rw [hval, div_eq_inv_mul]

private lemma sum_chebyshev_C_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    ∑ x : ZMod p, (Chebyshev.C (ZMod p) (m : ℤ)).eval x =
      (if (p - 1) ∣ m then (-1 : ZMod p) else 0) + (if (p + 1) ∣ m then (1 : ZMod p) else 0) := by
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  obtain ⟨d, hd⟩ := exists_nonsquare p hp2
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  have : IsDomain (QuadraticAlgebra (ZMod p) d 0) := qIsDomain hd
  let K := QuadraticAlgebra (ZMod p) d 0
  have : Fintype K := Fintype.ofEquiv (ZMod p × ZMod p)
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun x => (x.re, x.im)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let emb : ZMod p →+* K :=
    { toFun := fun x => ⟨x, 0⟩
      map_one' := rfl
      map_mul' := fun x y =>
        QuadraticAlgebra.ext (by change x * y = x * y + d * 0 * 0; ring)
          (by change 0 = x * 0 + 0 * y + 0 * 0 * 0; ring)
      map_zero' := rfl
      map_add' := fun x y => QuadraticAlgebra.ext rfl (add_zero (0 : ZMod p)).symm }
  have hemb_re : ∀ x : ZMod p, (emb x).re = x := fun x => rfl
  have hemb_im : ∀ x : ZMod p, (emb x).im = 0 := fun x => rfl
  -- Subgroup A = {u ∈ Kˣ | u.im = 0}
  let A : Subgroup Kˣ :=
    { carrier := {u : Kˣ | (u : K).im = 0}
      mul_mem' := fun {a b} ha hb => by
        change (a : K).re * (b : K).im + (a : K).im * (b : K).re + 0 * (a : K).im * (b : K).im = 0
        rw [ha, hb]; ring
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        have hmul : ((a : K) * ((a⁻¹ : Kˣ) : K)).im = 0 := by
          have : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by exact_mod_cast a.mul_inv
          rw [this]; rfl
        change (a : K).re * ((a⁻¹ : Kˣ) : K).im + (a : K).im * ((a⁻¹ : Kˣ) : K).re +
          0 * (a : K).im * ((a⁻¹ : Kˣ) : K).im = 0 at hmul
        rw [ha] at hmul
        have hare : (a : K).re ≠ 0 := by
          intro h0
          have ha0 : (a : K) = 0 := QuadraticAlgebra.ext h0 ha
          exact a.ne_zero ha0
        have : (a : K).re * ((a⁻¹ : Kˣ) : K).im = 0 := by linear_combination hmul
        exact (mul_eq_zero.mp this).resolve_left hare }
  -- Subgroup B = {u ∈ Kˣ | u.re^2 - d * u.im^2 = 1}
  let normK : K → ZMod p := fun x => x.re ^ 2 - d * x.im ^ 2
  have hnorm_mul : ∀ x y : K, normK (x * y) = normK x * normK y := fun x y => by
    change (x.re * y.re + d * x.im * y.im) ^ 2 -
      d * (x.re * y.im + x.im * y.re + 0 * x.im * y.im) ^ 2 =
      (x.re ^ 2 - d * x.im ^ 2) * (y.re ^ 2 - d * y.im ^ 2)
    ring
  let B : Subgroup Kˣ :=
    { carrier := {u : Kˣ | normK (u : K) = 1}
      mul_mem' := fun {a b} ha hb => by
        change normK ((a : K) * (b : K)) = 1
        rw [hnorm_mul, ha, hb, mul_one]
      one_mem' := by change (1 : ZMod p) ^ 2 - d * 0 ^ 2 = 1; ring
      inv_mem' := fun {a} ha => by
        have h1 : normK ((a : K) * ((a⁻¹ : Kˣ) : K)) = 1 := by
          have : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by exact_mod_cast a.mul_inv
          rw [this]; change (1 : ZMod p) ^ 2 - d * 0 ^ 2 = 1; ring
        rw [hnorm_mul, ha, one_mul] at h1
        exact h1 }
  have : Fintype A := Fintype.ofFinite A
  have : Fintype B := Fintype.ofFinite B
  -- Cardinality of A is p - 1
  have hcardA : Fintype.card A = p - 1 := by
    have heq : Fintype.card A = Fintype.card (ZMod p)ˣ := by
      refine Fintype.card_congr
        { toFun := fun u => Units.mk0 (u.1 : K).re (by
            intro h0
            have hu0 : (u.1 : K) = 0 := QuadraticAlgebra.ext h0 u.2
            exact u.1.ne_zero hu0)
          invFun := fun v => ⟨Units.map emb.toMonoidHom v, rfl⟩
          left_inv := fun u => by
            apply Subtype.ext; apply Units.ext; ext
            · rfl
            · exact u.2.symm
          right_inv := fun v => by apply Units.ext; rfl }
    rw [heq, ZMod.card_units]
  -- Cardinality of B is p + 1 via stereographic parametrization
  have hcardB : Fintype.card B = p + 1 := by
    have hden_ne : ∀ t : ZMod p, 1 - d * t ^ 2 ≠ 0 := by
      intro t ht
      by_cases ht0 : t = 0
      · subst ht0; simp at ht
      · apply hd t⁻¹
        rw [inv_pow]
        have : d * t ^ 2 = 1 := by linear_combination -ht
        field_simp [ht0]
        linear_combination -this
    let toB : Option (ZMod p) → B
      | none => ⟨-1, by
          show normK ((-1 : Kˣ) : K) = 1
          dsimp only [normK]
          rw [Units.val_neg, Units.val_one, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one,
            QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one]
          ring⟩
      | some t =>
        let den := 1 - d * t ^ 2
        let x : K := ⟨(1 + d * t ^ 2) / den, (2 * t) / den⟩
        have hxnorm : normK x = 1 := by
          have hdn : 1 - d * t ^ 2 ≠ 0 := hden_ne t
          change ((1 + d * t ^ 2) / (1 - d * t ^ 2)) ^ 2 -
            d * ((2 * t) / (1 - d * t ^ 2)) ^ 2 = 1
          field_simp [hdn]
          ring
        have hxne : x ≠ 0 := by
          intro h0
          rw [h0] at hxnorm
          change (0 : ZMod p) ^ 2 - d * 0 ^ 2 = 1 at hxnorm
          norm_num at hxnorm
        ⟨qUnit hd x hxne, hxnorm⟩
    let fromB : B → Option (ZMod p) := fun u =>
      if (u.1 : K).re = -1 then none else some ((u.1 : K).im / ((u.1 : K).re + 1))
    have heq : Fintype.card B = Fintype.card (Option (ZMod p)) := by
      refine Fintype.card_congr
        { toFun := fromB
          invFun := toB
          left_inv := fun u => by
            dsimp only [fromB]
            by_cases hre : (u.1 : K).re = -1
            · rw [if_pos hre]
              have him : (u.1 : K).im = 0 := by
                have hn : (u.1 : K).re ^ 2 - d * (u.1 : K).im ^ 2 = 1 := u.2
                rw [hre] at hn
                have h2 : d * (u.1 : K).im ^ 2 = 0 := by linear_combination -hn
                exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h2).resolve_left hd0)
              apply Subtype.ext; apply Units.ext; ext
              · dsimp only [toB]; rw [Units.val_neg, Units.val_one, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one, hre]
              · dsimp only [toB]; rw [Units.val_neg, Units.val_one, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero, him]
            · rw [if_neg hre]
              set a := (u.1 : K).re
              set b := (u.1 : K).im
              have ha1 : a + 1 ≠ 0 := fun h => hre (by linear_combination h)
              have hn : a ^ 2 - d * b ^ 2 = 1 := u.2
              have hden : 1 - d * (b / (a + 1)) ^ 2 = 2 / (a + 1) := by
                field_simp [ha1]
                linear_combination hn
              have hnum1 : 1 + d * (b / (a + 1)) ^ 2 = 2 * a / (a + 1) := by
                field_simp [ha1]
                linear_combination -hn
              apply Subtype.ext; apply Units.ext; ext
              · change (1 + d * (b / (a + 1)) ^ 2) / (1 - d * (b / (a + 1)) ^ 2) = a
                rw [hnum1, hden]
                field_simp [ha1, h2ne]
              · change (2 * (b / (a + 1))) / (1 - d * (b / (a + 1)) ^ 2) = b
                rw [hden]
                field_simp [ha1, h2ne]
          right_inv := fun o => by
            cases o with
            | none =>
              dsimp only [toB, fromB]
              rw [if_pos (by rw [Units.val_neg, Units.val_one, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one])]
            | some t =>
              dsimp only [toB, fromB, qUnit]
              have hdn : 1 - d * t ^ 2 ≠ 0 := hden_ne t
              have hne1 : (1 + d * t ^ 2) / (1 - d * t ^ 2) ≠ -1 := by
                intro h
                have h' : 1 + d * t ^ 2 = -1 * (1 - d * t ^ 2) := (div_eq_iff hdn).mp h
                exact h2ne (by linear_combination h')
              rw [if_neg hne1]
              congr 1
              have hadd : (1 + d * t ^ 2) / (1 - d * t ^ 2) + 1 = 2 / (1 - d * t ^ 2) := by
                field_simp [hdn]; ring
              rw [hadd, div_div_div_cancel_right₀ hdn, mul_div_cancel_left₀ t h2ne] }
    rw [heq, Fintype.card_option, ZMod.card]
  -- Define φ : A ⊕ B → ZMod p sending u to (u + u⁻¹).re
  let phiA : A → ZMod p := fun u => ((u.1 : K) + ((u.1⁻¹ : Kˣ) : K)).re
  let phiB : B → ZMod p := fun u => ((u.1 : K) + ((u.1⁻¹ : Kˣ) : K)).re
  have hphiA_emb : ∀ u : A, emb (phiA u) = (u.1 : K) + ((u.1⁻¹ : Kˣ) : K) := fun u => by
    ext
    · rfl
    · change 0 = (u.1 : K).im + ((u.1⁻¹ : Kˣ) : K).im
      rw [u.2, A.inv_mem u.2, add_zero]
  have hB_inv_im : ∀ u : B, ((u.1⁻¹ : Kˣ) : K) = ⟨(u.1 : K).re, -(u.1 : K).im⟩ := fun u => by
    have hmul : (u.1 : K) * (⟨(u.1 : K).re, -(u.1 : K).im⟩ : K) = 1 := by
      ext
      · change (u.1 : K).re * (u.1 : K).re + d * (u.1 : K).im * -(u.1 : K).im = 1
        have hn : (u.1 : K).re ^ 2 - d * (u.1 : K).im ^ 2 = 1 := u.2
        linear_combination hn
      · change (u.1 : K).re * -(u.1 : K).im + (u.1 : K).im * (u.1 : K).re +
          0 * (u.1 : K).im * -(u.1 : K).im = 0
        ring
    have hinv := u.1.mul_inv
    have : (u.1 : K) * ((u.1⁻¹ : Kˣ) : K) = (u.1 : K) * ⟨(u.1 : K).re, -(u.1 : K).im⟩ := by
      rw [hmul]; exact_mod_cast hinv
    exact mul_left_cancel₀ u.1.ne_zero this
  have hphiB_emb : ∀ u : B, emb (phiB u) = (u.1 : K) + ((u.1⁻¹ : Kˣ) : K) := fun u => by
    ext
    · rfl
    · change 0 = (u.1 : K).im + ((u.1⁻¹ : Kˣ) : K).im
      rw [hB_inv_im u]
      simp
  -- Every x : ZMod p has exact fiber size 2 in A ⊕ B
  have hfiber : ∀ x : ZMod p,
      (Finset.univ.filter (fun u : A => phiA u = x)).card +
      (Finset.univ.filter (fun u : B => phiB u = x)).card = 2 := by
    intro x
    set Δ := x ^ 2 - 4
    have hphiA_iff : ∀ u : A, phiA u = x ↔ (2 * (u.1 : K).re - x) ^ 2 = Δ := fun u => by
      have ha0 : (u.1 : K).re ≠ 0 := fun h0 => u.1.ne_zero (QuadraticAlgebra.ext h0 u.2)
      have hinv_re : ((u.1⁻¹ : Kˣ) : K).re = (u.1 : K).re⁻¹ := by
        have h1 : ((u.1 : K) * ((u.1⁻¹ : Kˣ) : K)).re = 1 := by
          have : (u.1 : K) * ((u.1⁻¹ : Kˣ) : K) = 1 := by exact_mod_cast u.1.mul_inv
          rw [this]; rfl
        change (u.1 : K).re * ((u.1⁻¹ : Kˣ) : K).re + d * (u.1 : K).im * ((u.1⁻¹ : Kˣ) : K).im = 1 at h1
        rw [u.2, mul_zero, zero_mul, add_zero] at h1
        exact eq_inv_of_mul_eq_one_right h1
      change (u.1 : K).re + ((u.1⁻¹ : Kˣ) : K).re = x ↔ _
      rw [hinv_re]
      constructor
      · intro h
        have h' : (u.1 : K).re ^ 2 + 1 = x * (u.1 : K).re := by
          have := congrArg (· * (u.1 : K).re) h
          field_simp [ha0] at this
          linear_combination this
        dsimp [Δ]
        linear_combination 4 * h'
      · intro h
        dsimp [Δ] at h
        have h' : 4 * ((u.1 : K).re ^ 2 - x * (u.1 : K).re + 1) = 0 := by linear_combination h
        have h4 : (4 : ZMod p) ≠ 0 := by
          have : (4 : ZMod p) = 2 * 2 := by norm_num
          rw [this]; exact mul_ne_zero h2ne h2ne
        have hq : (u.1 : K).re ^ 2 - x * (u.1 : K).re + 1 = 0 :=
          (mul_eq_zero.mp h').resolve_left h4
        field_simp [ha0]
        linear_combination hq
    have hphiB_iff : ∀ u : B, phiB u = x ↔ (u.1 : K).re = x / 2 := fun u => by
      change (u.1 : K).re + ((u.1⁻¹ : Kˣ) : K).re = x ↔ _
      rw [hB_inv_im u]
      dsimp only
      constructor
      · intro h; field_simp [h2ne]; linear_combination h
      · intro h; rw [h]; field_simp [h2ne]; ring
    by_cases hΔ0 : Δ = 0
    · -- Case Δ = 0: 1 in A, 1 in B
      have hx0 : x / 2 ≠ 0 := by
        intro h0
        have hx : x = 0 := (div_eq_zero_iff.mp h0).resolve_right h2ne
        dsimp [Δ] at hΔ0
        rw [hx] at hΔ0
        have : (2 : ZMod p) * 2 = 0 := by linear_combination -hΔ0
        exact mul_ne_zero h2ne h2ne this
      have hsq : (x / 2) ^ 2 = 1 := by
        dsimp [Δ] at hΔ0
        field_simp [h2ne]
        linear_combination hΔ0
      let uA : A := ⟨Units.map emb.toMonoidHom (Units.mk0 (x / 2) hx0), rfl⟩
      have hA1 : Finset.univ.filter (fun u : A => phiA u = x) = {uA} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hphiA_iff,
          hΔ0, sq_eq_zero_iff]
        constructor
        · intro h
          apply Subtype.ext; apply Units.ext; ext
          · change (u.1 : K).re = x / 2
            field_simp [h2ne]; linear_combination h
          · exact u.2
        · rintro rfl
          change 2 * (x / 2) - x = 0
          field_simp [h2ne]; ring
      let uB : B := ⟨Units.map emb.toMonoidHom (Units.mk0 (x / 2) hx0), by
        change (x / 2) ^ 2 - d * 0 ^ 2 = 1; rw [hsq]; ring⟩
      have hB1 : Finset.univ.filter (fun u : B => phiB u = x) = {uB} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hphiB_iff]
        constructor
        · intro h
          have him : (u.1 : K).im = 0 := by
            have hn : (u.1 : K).re ^ 2 - d * (u.1 : K).im ^ 2 = 1 := u.2
            rw [h, hsq] at hn
            have : d * (u.1 : K).im ^ 2 = 0 := by linear_combination -hn
            exact sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hd0)
          apply Subtype.ext; apply Units.ext; ext
          · exact h
          · exact him
        · rintro rfl; rfl
      rw [hA1, hB1, Finset.card_singleton, Finset.card_singleton]
    · by_cases hsq : ∃ c : ZMod p, c ^ 2 = Δ
      · -- Case Δ = c^2 ≠ 0: 2 in A, 0 in B
        obtain ⟨c, hc⟩ := hsq
        have hc0 : c ≠ 0 := fun h => hΔ0 (by rw [← hc, h]; ring)
        have hpos1 : (x + c) / 2 ≠ 0 := by
          intro h
          have hxc : x + c = 0 := (div_eq_zero_iff.mp h).resolve_right h2ne
          have : (4 : ZMod p) = 0 := by
            have h1 : x ^ 2 = c ^ 2 := by
              have : x = -c := by linear_combination hxc
              rw [this]; ring
            dsimp [Δ] at hc; linear_combination h1 + hc
          have : (2 : ZMod p) * 2 = 0 := by linear_combination this
          exact mul_ne_zero h2ne h2ne this
        have hpos2 : (x - c) / 2 ≠ 0 := by
          intro h
          have hxc : x - c = 0 := (div_eq_zero_iff.mp h).resolve_right h2ne
          have : (4 : ZMod p) = 0 := by
            have h1 : x ^ 2 = c ^ 2 := by
              have : x = c := by linear_combination hxc
              rw [this]
            dsimp [Δ] at hc; linear_combination h1 + hc
          have : (2 : ZMod p) * 2 = 0 := by linear_combination this
          exact mul_ne_zero h2ne h2ne this
        let u1 : A := ⟨Units.map emb.toMonoidHom (Units.mk0 ((x + c) / 2) hpos1), rfl⟩
        let u2 : A := ⟨Units.map emb.toMonoidHom (Units.mk0 ((x - c) / 2) hpos2), rfl⟩
        have hu12 : u1 ≠ u2 := by
          intro h
          have hre : (x + c) / 2 = (x - c) / 2 := congrArg (fun u : A => (u.1 : K).re) h
          have : c = 0 := by
            have h1 := congrArg (· * 2) hre
            field_simp [h2ne] at h1
            have : 2 * c = 0 := by linear_combination h1
            exact (mul_eq_zero.mp this).resolve_left h2ne
          exact hc0 this
        have hA2 : Finset.univ.filter (fun u : A => phiA u = x) = {u1, u2} := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, hphiA_iff, ← hc, sq_eq_sq_iff_eq_or_eq_neg]
          constructor
          · rintro (h | h)
            · left; apply Subtype.ext; apply Units.ext; ext
              · change (u.1 : K).re = (x + c) / 2; field_simp [h2ne]; linear_combination h
              · exact u.2
            · right; apply Subtype.ext; apply Units.ext; ext
              · change (u.1 : K).re = (x - c) / 2; field_simp [h2ne]; linear_combination h
              · exact u.2
          · rintro (rfl | rfl)
            · left; change 2 * ((x + c) / 2) - x = c; field_simp [h2ne]; ring
            · right; change 2 * ((x - c) / 2) - x = -c; field_simp [h2ne]; ring
        have hB0 : Finset.univ.filter (fun u : B => phiB u = x) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, hphiB_iff]
          intro hre
          have hn : (u.1 : K).re ^ 2 - d * (u.1 : K).im ^ 2 = 1 := u.2
          rw [hre] at hn
          have h4 : d * (2 * (u.1 : K).im) ^ 2 = c ^ 2 := by
            have h4ne : (4 : ZMod p) ≠ 0 := by
              have : (4 : ZMod p) = 2 * 2 := by norm_num
              rw [this]; exact mul_ne_zero h2ne h2ne
            have h1 : (x / 2) ^ 2 - 1 = Δ / 4 := by
              dsimp [Δ]; field_simp [h2ne, h4ne]; ring
            have h2 : d * (u.1 : K).im ^ 2 = Δ / 4 := by linear_combination -hn + h1
            rw [← hc] at h2
            have h3 := congrArg (· * 4) h2
            field_simp [h4ne] at h3
            linear_combination h3
          have him0 : (u.1 : K).im ≠ 0 := by
            intro h0
            rw [h0] at h4
            have : c ^ 2 = 0 := by linear_combination -h4
            exact hc0 (sq_eq_zero_iff.mp this)
          apply hd (c / (2 * (u.1 : K).im))
          rw [div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero h2ne him0))]
          linear_combination -h4
        rw [hA2, hB0, Finset.card_pair hu12, Finset.card_empty]
      · -- Case Δ non-square: 0 in A, 2 in B
        push Not at hsq
        have hA0 : Finset.univ.filter (fun u : A => phiA u = x) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, hphiA_iff]
          exact hsq (2 * (u.1 : K).re - x)
        obtain ⟨c, hc⟩ := mul_nonsquare_isSquare hp2 hd hΔ0 hsq
        have hc0 : c ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by decide)] at hc
          exact hΔ0 ((div_eq_zero_iff.mp hc.symm).resolve_right hd0)
        have hnorm1 : normK ⟨x / 2, c / 2⟩ = 1 := by
          change (x / 2) ^ 2 - d * (c / 2) ^ 2 = 1
          have hcd : d * c ^ 2 = Δ := by rw [hc, mul_div_cancel₀ _ hd0]
          dsimp [Δ] at hcd
          field_simp [h2ne]
          linear_combination -hcd
        have hnorm2 : normK ⟨x / 2, -(c / 2)⟩ = 1 := by
          change (x / 2) ^ 2 - d * (-(c / 2)) ^ 2 = 1
          simpa using hnorm1
        have hne1 : (⟨x / 2, c / 2⟩ : K) ≠ 0 := by
          intro h0
          have : c / 2 = 0 := congrArg QuadraticAlgebra.im h0
          exact hc0 ((div_eq_zero_iff.mp this).resolve_right h2ne)
        have hne2 : (⟨x / 2, -(c / 2)⟩ : K) ≠ 0 := by
          intro h0
          have : -(c / 2) = 0 := congrArg QuadraticAlgebra.im h0
          exact hc0 ((div_eq_zero_iff.mp (neg_eq_zero.mp this)).resolve_right h2ne)
        let v1 : B := ⟨qUnit hd ⟨x / 2, c / 2⟩ hne1, hnorm1⟩
        let v2 : B := ⟨qUnit hd ⟨x / 2, -(c / 2)⟩ hne2, hnorm2⟩
        have hv12 : v1 ≠ v2 := by
          intro h
          have him : c / 2 = -(c / 2) := congrArg (fun u : B => (u.1 : K).im) h
          have h2c : 2 * (c / 2) = 0 := by linear_combination him
          rw [mul_div_cancel₀ _ h2ne] at h2c
          exact hc0 h2c
        have hB2 : Finset.univ.filter (fun u : B => phiB u = x) = {v1, v2} := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, hphiB_iff]
          constructor
          · intro hre
            have hn : (u.1 : K).re ^ 2 - d * (u.1 : K).im ^ 2 = 1 := u.2
            rw [hre] at hn
            have himsq : (u.1 : K).im ^ 2 = (c / 2) ^ 2 := by
              have hcd : d * c ^ 2 = Δ := by rw [hc, mul_div_cancel₀ _ hd0]
              have h4 : 4 * d * (u.1 : K).im ^ 2 = d * c ^ 2 := by
                dsimp [Δ] at hcd
                have h1 : x ^ 2 - 4 * d * (u.1 : K).im ^ 2 = 4 := by
                  have h' := hn
                  field_simp [h2ne] at h'
                  linear_combination h'
                linear_combination -h1 - hcd
              have h5 : d * ((u.1 : K).im ^ 2 - (c / 2) ^ 2) = 0 := by
                field_simp [h2ne]
                linear_combination h4
              have h6 := (mul_eq_zero.mp h5).resolve_left hd0
              linear_combination h6
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with h1 | h2
            · left; apply Subtype.ext; apply Units.ext; ext <;> [exact hre; exact h1]
            · right; apply Subtype.ext; apply Units.ext; ext <;> [exact hre; exact h2]
          · rintro (rfl | rfl) <;> rfl
        rw [hA0, hB2, Finset.card_empty, Finset.card_pair hv12]
  -- Now compare 2 * ∑ x, C_m(x) with ∑_{u ∈ A} C_m(φ_A u) + ∑_{u ∈ B} C_m(φ_B u)
  let f : ZMod p → ZMod p := fun x => (Chebyshev.C (ZMod p) (m : ℤ)).eval x
  have hsum_double : (2 : ZMod p) * ∑ x : ZMod p, f x =
      (∑ u : A, f (phiA u)) + (∑ u : B, f (phiB u)) := by
    have hA_fib : ∑ u : A, f (phiA u) =
        ∑ x : ZMod p, ((Finset.univ.filter (fun u : A => phiA u = x)).card : ZMod p) * f x := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := phiA) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2])]
      simp
    have hB_fib : ∑ u : B, f (phiB u) =
        ∑ x : ZMod p, ((Finset.univ.filter (fun u : B => phiB u = x)).card : ZMod p) * f x := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := phiB) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2])]
      simp
    rw [hA_fib, hB_fib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hf2 := congrArg (Nat.cast : ℕ → ZMod p) (hfiber x)
    push_cast at hf2
    rw [← add_mul, hf2]
  -- Embed into K and evaluate via Chebyshev identity
  have hK_eq : emb ((2 : ZMod p) * ∑ x : ZMod p, f x) =
      emb ((2 : ZMod p) * ((if (p - 1) ∣ m then (-1 : ZMod p) else 0) +
        (if (p + 1) ∣ m then (1 : ZMod p) else 0))) := by
    rw [hsum_double, map_add, map_sum, map_sum]
    have hmapC : ∀ x : ZMod p, emb (f x) = (Chebyshev.C K (m : ℤ)).eval (emb x) := fun x => by
      dsimp only [f]
      rw [← Polynomial.eval_map_apply, Chebyshev.map_C]
    have hsumA : ∑ u : A, emb (f (phiA u)) = 2 * ∑ u : A, ((u.1 : K) ^ m) := by
      have h1 : ∑ u : A, emb (f (phiA u)) =
          (∑ u : A, (u.1 : K) ^ m) + (∑ u : A, ((u.1⁻¹ : Kˣ) : K) ^ m) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hmapC, hphiA_emb, chebyshev_C_eval_add_inv]
      have hinv : ∑ u : A, ((u.1⁻¹ : Kˣ) : K) ^ m = ∑ u : A, (u.1 : K) ^ m :=
        Fintype.sum_equiv (Equiv.inv A) _ _ (fun _ => rfl)
      rw [h1, hinv, ← two_mul]
    have hsumB : ∑ u : B, emb (f (phiB u)) = 2 * ∑ u : B, ((u.1 : K) ^ m) := by
      have h1 : ∑ u : B, emb (f (phiB u)) =
          (∑ u : B, (u.1 : K) ^ m) + (∑ u : B, ((u.1⁻¹ : Kˣ) : K) ^ m) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hmapC, hphiB_emb, chebyshev_C_eval_add_inv]
      have hinv : ∑ u : B, ((u.1⁻¹ : Kˣ) : K) ^ m = ∑ u : B, (u.1 : K) ^ m :=
        Fintype.sum_equiv (Equiv.inv B) _ _ (fun _ => rfl)
      rw [h1, hinv, ← two_mul]
    have hA_pow : ∑ u : A, (u.1 : K) ^ m =
        if Fintype.card A ∣ m then (Fintype.card A : K) else 0 := sum_subgroup_pow A m
    have hB_pow : ∑ u : B, (u.1 : K) ^ m =
        if Fintype.card B ∣ m then (Fintype.card B : K) else 0 := sum_subgroup_pow B m
    rw [hsumA, hsumB, hA_pow, hB_pow, hcardA, hcardB]
    have hp1 : ((p - 1 : ℕ) : K) = -1 := by
      have hle : 1 ≤ p := hp.one_le
      have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, Nat.cast_one]
      have h2 := congrArg emb h1
      rw [map_natCast, map_neg, map_one] at h2
      exact h2
    have hp2' : ((p + 1 : ℕ) : K) = 1 := by
      have h1 : ((p + 1 : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
      have h2 := congrArg emb h1
      rw [map_natCast, map_one] at h2
      exact h2
    rw [hp1, hp2']
    simp only [map_mul, map_add, map_ofNat, apply_ite emb, map_neg, map_one, map_zero]
    ring
  have h2mul : (2 : ZMod p) * ∑ x : ZMod p, f x =
      (2 : ZMod p) * ((if (p - 1) ∣ m then (-1 : ZMod p) else 0) +
        (if (p + 1) ∣ m then (1 : ZMod p) else 0)) :=
    congrArg QuadraticAlgebra.re hK_eq
  exact mul_left_cancel₀ h2ne h2mul

end Mse2615963R3H1Proof

theorem OMA.solution : OMA.R_mse_2615963_R3.H1 := by
  intro p hp hp2 m
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hrange : ∑ k ∈ Finset.range p,
      (((Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ) : ℤ) : ZMod p) =
      ∑ x : ZMod p, (Polynomial.Chebyshev.C (ZMod p) (m : ℤ)).eval x := by
    have hev : ∀ k : ℕ, (((Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ) : ℤ) : ZMod p) =
        (Polynomial.Chebyshev.C (ZMod p) (m : ℤ)).eval (k : ZMod p) := fun k => by
      change (Int.castRingHom (ZMod p)) ((Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ)) = _
      rw [← Polynomial.eval_map_apply, Polynomial.Chebyshev.map_C]
      simp
    simp_rw [hev]
    refine Finset.sum_nbij (fun k : ℕ => (k : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_
      (fun _ _ => rfl)
    · intro a ha b hb hab
      have ha' : a < p := Finset.mem_range.mp ha
      have hb' : b < p := Finset.mem_range.mp hb
      have hval := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at hval
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  rw [hrange]
  have hmain := Mse2615963R3H1Proof.sum_chebyshev_C_zmod p hp2 m
  simpa [apply_ite (Int.cast : ℤ → ZMod p)] using hmain
