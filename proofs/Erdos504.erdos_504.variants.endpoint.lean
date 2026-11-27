import FormalConjectures.ErdosProblems.«504»
import Mathlib

-- Problem: Erdos Problem 504, endpoint variant: alpha(2^n - 1) = (1 - 1/n) * pi for n >= 3.
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/504.lean
--   (declaration Erdos504.erdos_504.variants.endpoint)
-- Credit: @graydeveloper01
--
-- Mathematical credit.  The sector colouring and the cluster construction are due to
-- G. Szekeres (On an extremum problem in the plane, Amer. J. Math. 63, 1941).  The
-- lower bound for 2^n - 1 points is Theorem 3 (note added in proof) of P. Erdos and
-- G. Szekeres (On some extremum problems in elementary geometry, Ann. Univ. Sci.
-- Budapest 3-4, 1960-61).  An independent Lean formalization of the 2^n case and of the
-- Szekeres construction exists at github.com/ToshiDad/erdos-504; the proof below was
-- written independently of it.
--
-- Outline (theta = pi / n).
-- A. Lower bound: 2^n - 1 points cannot have all angles < pi - theta.
--   1. For a frame angle a, sides u is the set of sectors [a + k theta, a + (k+1) theta)
--      in which u has a forward neighbour.  The angle bound makes u -> sides u injective,
--      so with 2^n - 1 points exactly one subset of Fin n is not a side set
--      (two_missing).
--   2. A point q misses a class at frame b when no line through q and another point
--      has direction in [b, b + theta).  If q misses class k then sides q with k flipped
--      is not a side set (miss_flip); hence two points missing classes at frames that
--      differ by a multiple of theta coincide (miss_unique).  This replaces Lemma 4 of
--      the paper.
--   3. Every point misses a class at some frame, by looking at a largest angle at that
--      point (miss_exists; this uses strictness).
--   4. Hull walk: an extreme point Q carries a wedge [a, c] of directions with
--      c < a + pi - theta, both ends attained; a point on the last ray carries a wedge
--      starting at c - pi (step).  This gives Q_i, a_i with a_(i+1) < a_i - theta, and
--      Q_i misses a class at every frame in (a_(i+1), a_i - theta] (wedge_miss).
--   5. Q_i is the unique minimiser of a linear functional for normals in
--      (a_(i+1), a_i), which forces a_M = a_0 - 2 pi for some M <= 2n - 1.  The frames
--      of step 4, reduced mod theta, then cover a full period, so by 2 and 3 every
--      point is one of Q_0 .. Q_(M-1): 2^n - 1 <= 2n - 1, false for n >= 3.
-- B. Upper bound: for z = rho * exp(i theta) with rho tiny, the 2^n subset sums of
--    1, z, .., z^(n-1) have all angles < pi - theta + eps: the difference of two sums
--    is +- z^k (1 + u) with u tiny, k the least index where the subsets differ, and the
--    sign is decided by the subset of the base point.  Deleting one point gives
--    2^n - 1 points.

namespace OMA.ES504E

open Real

def Pol (w : ℂ) (φ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)

lemma Pol.ne_zero {w : ℂ} {φ : ℝ} (h : Pol w φ) : w ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := h
  exact mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)

lemma Pol.neg {w : ℂ} {φ : ℝ} (h : Pol w φ) : Pol (-w) (φ + π) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma Pol.neg' {w : ℂ} {φ : ℝ} (h : Pol w φ) : Pol (-w) (φ - π) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  push_cast
  rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
  field_simp

lemma Pol.norm_eq {w : ℂ} {φ : ℝ} {r : ℝ} (hr : 0 < r)
    (h : w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) : ‖w‖ = r := by
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr.le]

lemma Pol.unique {w : ℂ} {φ ψ : ℝ} (h1 : Pol w φ) (h2 : Pol w ψ)
    (h : |φ - ψ| < 2 * π) : φ = ψ := by
  obtain ⟨r, hr, e1⟩ := h1
  obtain ⟨s, hs, e2⟩ := h2
  have n1 := Pol.norm_eq hr e1
  have n2 := Pol.norm_eq hs e2
  have hrs : r = s := by rw [← n1, ← n2]
  subst hrs
  rw [e1] at e2
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e3 := mul_left_cancel₀ hr0 e2
  rw [Complex.exp_eq_exp_iff_exists_int] at e3
  obtain ⟨m, hm⟩ := e3
  have hm' : φ = ψ + m * (2 * π) := by
    have := congrArg Complex.im hm
    simpa using this
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  have hm1 : (-1 : ℝ) < m := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hm2 : (m : ℝ) < 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hm0 : m = 0 := by
    have a1 : (-1 : ℤ) < m := by exact_mod_cast hm1
    have a2 : m < (1 : ℤ) := by exact_mod_cast hm2
    omega
  rw [hm'] ; simp [hm0]

lemma pol_exists {w : ℂ} (hw : w ≠ 0) (c : ℝ) :
    ∃ φ : ℝ, c ≤ φ ∧ φ < c + 2 * π ∧ Pol w φ := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  refine ⟨toIcoMod h2 c (Complex.arg w), (toIcoMod_mem_Ico h2 c _).1,
    (toIcoMod_mem_Ico h2 c _).2, ‖w‖, norm_pos_iff.mpr hw, ?_⟩
  have e : Complex.exp ((toIcoMod h2 c (Complex.arg w) : ℝ) * Complex.I)
      = Complex.exp ((Complex.arg w : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(toIcoDiv h2 c (Complex.arg w)), ?_⟩
    rw [toIcoMod]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e, Complex.norm_mul_exp_arg_mul_I]

lemma pol_arg {w : ℂ} (hw : w ≠ 0) : Pol w (Complex.arg w) :=
  ⟨‖w‖, norm_pos_iff.mpr hw, (Complex.norm_mul_exp_arg_mul_I w).symm⟩

noncomputable def hgt (a : ℝ) (w : ℂ) : ℝ := w.im * Real.cos a - w.re * Real.sin a

lemma hgt_sub (a : ℝ) (z w : ℂ) : hgt a (z - w) = hgt a z - hgt a w := by
  simp only [hgt, Complex.sub_re, Complex.sub_im]; ring

lemma hgt_exp (a : ℝ) {w : ℂ} {r φ : ℝ}
    (h : w = (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) :
    hgt a w = r * Real.sin (φ - a) := by
  subst h
  simp only [hgt, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_sub]
  ring

lemma hgt_add_sub (a θ : ℝ) (w : ℂ) :
    hgt (a + θ) w + hgt (a - θ) w = 2 * Real.cos θ * hgt a w := by
  simp only [hgt, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]; ring

lemma Pol.data {w : ℂ} {φ : ℝ} (h : Pol w φ) :
    ∃ r : ℝ, 0 < r ∧ ‖w‖ = r ∧ ∀ a : ℝ, hgt a w = r * Real.sin (φ - a) := by
  obtain ⟨r, hr, e⟩ := h
  exact ⟨r, hr, Pol.norm_eq hr e, fun a => hgt_exp a e⟩

lemma angle_pol {p q r : ℂ} {φ ψ : ℝ} (h1 : Pol (p - q) φ) (h2 : Pol (r - q) ψ)
    (h : |φ - ψ| ≤ π) : EuclideanGeometry.angle p q r = |φ - ψ| := by
  obtain ⟨s, hs, e1⟩ := h1
  obtain ⟨t, ht, e2⟩ := h2
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [e1, e2]
  have c1 : ((s : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
      = s • Complex.exp ((φ : ℂ) * Complex.I) := by simp
  have c2 : ((t : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
      = t • Complex.exp ((ψ : ℂ) * Complex.I) := by simp
  rw [c1, c2, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]
  unfold InnerProductGeometry.angle
  have hin : inner ℝ (Complex.exp ((φ : ℂ) * Complex.I)) (Complex.exp ((ψ : ℂ) * Complex.I))
      = Real.cos (|φ - ψ|) := by
    rw [Real.cos_abs, Real.cos_sub, Complex.inner]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hin, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
  simp only [mul_one, div_one]
  exact Real.arccos_cos (abs_nonneg _) h

lemma pol_add_two_pi {w : ℂ} {φ : ℝ} (h : Pol w φ) : Pol w (φ + 2 * π) := by
  have := h.neg.neg
  rw [neg_neg] at this
  have e : φ + π + π = φ + 2 * π := by ring
  rwa [e] at this

lemma pol_sub_two_pi {w : ℂ} {φ : ℝ} (h : Pol w φ) : Pol w (φ - 2 * π) := by
  have := h.neg'.neg'
  rw [neg_neg] at this
  have e : φ - π - π = φ - 2 * π := by ring
  rwa [e] at this

lemma pol_mul {w w' : ℂ} {φ φ' : ℝ} (h : Pol w φ) (h' : Pol w' φ') : Pol (w * w') (φ + φ') := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := h'
  refine ⟨r * s, mul_pos hr hs, ?_⟩
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

lemma hgt_two_pi (β : ℝ) (w : ℂ) : hgt (β + 2 * π) w = hgt β w := by
  simp [hgt, Real.cos_add_two_pi, Real.sin_add_two_pi]

structure Cfg (θ : ℝ) (n : ℕ) (S : Finset ℂ) : Prop where
  hθ : 0 < θ
  hn : (n : ℝ) * θ = π
  hn3 : 3 ≤ n
  hG : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q → EuclideanGeometry.angle p q r < π - θ
  hcard : S.card = 2 ^ n - 1

def Sec (θ a : ℝ) (k : ℕ) (w : ℂ) : Prop :=
  ∃ φ : ℝ, a + k * θ ≤ φ ∧ φ < a + k * θ + θ ∧ Pol w φ

def sides (θ : ℝ) (n : ℕ) (S : Finset ℂ) (a : ℝ) (u : ℂ) : Set (Fin n) :=
  {k | ∃ v ∈ S, Sec θ a k (v - u)}

def Miss (S : Finset ℂ) (θ : ℝ) (q : ℂ) (α : ℝ) : Prop :=
  ∀ v ∈ S, ∀ φ : ℝ, α ≤ φ → φ < α + θ → ¬ Pol (v - q) φ ∧ ¬ Pol (q - v) φ

structure Wedge (θ : ℝ) (S : Finset ℂ) (Q : ℂ) (a c : ℝ) : Prop where
  le : a ≤ c
  lt : c < a + π - θ
  fst : ∃ X ∈ S, Pol (X - Q) a
  lst : ∃ X ∈ S, Pol (X - Q) c
  all : ∀ X ∈ S, X ≠ Q → ∃ φ : ℝ, a ≤ φ ∧ φ ≤ c ∧ Pol (X - Q) φ

variable {θ : ℝ} {n : ℕ} {S : Finset ℂ}

lemma Cfg.three (G : Cfg θ n S) : 3 * θ ≤ π := by
  have h : (3 : ℝ) ≤ n := by exact_mod_cast G.hn3
  have := G.hn
  have := G.hθ
  nlinarith

lemma Cfg.idx (G : Cfg θ n S) {k : ℕ} (hk : k < n) :
    0 ≤ (k : ℝ) * θ ∧ (k : ℝ) * θ + θ ≤ π := by
  have h : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have := G.hn
  have := G.hθ
  constructor
  · positivity
  · nlinarith

lemma sec_total (G : Cfg θ n S) {w : ℂ} (hw : w ≠ 0) (a : ℝ) :
    ∃ k, k < n ∧ (Sec θ a k w ∨ Sec θ a k (-w)) := by
  have hθ := G.hθ
  have hn := G.hn
  obtain ⟨φ, h1, h2, hp⟩ := pol_exists hw a
  have key : ∀ ψ : ℝ, a ≤ ψ → ψ < a + π →
      ∃ k, k < n ∧ a + (k : ℝ) * θ ≤ ψ ∧ ψ < a + (k : ℝ) * θ + θ := by
    intro ψ h1 h2
    have hnn : 0 ≤ (ψ - a) / θ := div_nonneg (by linarith) hθ.le
    refine ⟨⌊(ψ - a) / θ⌋₊, ?_, ?_, ?_⟩
    · have h3 : ((⌊(ψ - a) / θ⌋₊ : ℕ) : ℝ) ≤ (ψ - a) / θ := Nat.floor_le hnn
      have h4 : (ψ - a) / θ < n := by rw [div_lt_iff₀ hθ]; linarith
      exact_mod_cast lt_of_le_of_lt h3 h4
    · have h3 : ((⌊(ψ - a) / θ⌋₊ : ℕ) : ℝ) ≤ (ψ - a) / θ := Nat.floor_le hnn
      rw [le_div_iff₀ hθ] at h3
      linarith
    · have h3 := Nat.lt_floor_add_one ((ψ - a) / θ)
      rw [div_lt_iff₀ hθ] at h3
      linarith
  by_cases hc : φ < a + π
  · obtain ⟨k, hk, b1, b2⟩ := key φ h1 hc
    exact ⟨k, hk, Or.inl ⟨φ, b1, b2, hp⟩⟩
  · rw [not_lt] at hc
    obtain ⟨k, hk, b1, b2⟩ := key (φ - π) (by linarith) (by linarith)
    exact ⟨k, hk, Or.inr ⟨φ - π, b1, b2, hp.neg'⟩⟩

lemma sec_clash (G : Cfg θ n S) {a : ℝ} {k : ℕ} {u v w : ℂ}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (h1 : Sec θ a k (v - u)) (h2 : Sec θ a k (u - w)) : False := by
  obtain ⟨φ, a1, a2, p1⟩ := h1
  obtain ⟨ψ, b1, b2, p2⟩ := h2
  have hθ := G.hθ
  have h3 := G.three
  have hvu : v ≠ u := fun h => p1.ne_zero (by rw [h, sub_self])
  have hwu : w ≠ u := fun h => p2.ne_zero (by rw [h, sub_self])
  have hg := G.hG v hv u hu w hw hvu hwu
  by_cases hc : ψ ≤ φ
  · have p3 : Pol (w - u) (ψ + π) := by
      have := p2.neg
      rwa [neg_sub] at this
    have hab : |φ - (ψ + π)| = π - (φ - ψ) := by
      rw [abs_of_nonpos (by linarith)]; ring
    have := angle_pol p1 p3 (by rw [hab]; linarith)
    rw [this, hab] at hg
    linarith
  · rw [not_le] at hc
    have p3 : Pol (w - u) (ψ - π) := by
      have := p2.neg'
      rwa [neg_sub] at this
    have hab : |φ - (ψ - π)| = π - (ψ - φ) := by
      rw [abs_of_nonneg (by linarith)]; ring
    have := angle_pol p1 p3 (by rw [hab]; linarith)
    rw [this, hab] at hg
    linarith

lemma edge_alt (G : Cfg θ n S) (a : ℝ) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    ∃ k, ∃ hk : k < n,
      (Sec θ a k (v - u) ∧ (⟨k, hk⟩ : Fin n) ∈ sides θ n S a u ∧
        (⟨k, hk⟩ : Fin n) ∉ sides θ n S a v) ∨
      (Sec θ a k (u - v) ∧ (⟨k, hk⟩ : Fin n) ∈ sides θ n S a v ∧
        (⟨k, hk⟩ : Fin n) ∉ sides θ n S a u) := by
  obtain ⟨k, hk, h | h⟩ := sec_total G (sub_ne_zero.mpr (Ne.symm huv)) a
  · refine ⟨k, hk, Or.inl ⟨h, ⟨v, hv, h⟩, ?_⟩⟩
    rintro ⟨w, hw, hsec⟩
    exact sec_clash G hv hw hu hsec h
  · rw [neg_sub] at h
    refine ⟨k, hk, Or.inr ⟨h, ⟨u, hu, h⟩, ?_⟩⟩
    rintro ⟨w, hw, hsec⟩
    exact sec_clash G hu hw hv hsec h

lemma sides_inj (G : Cfg θ n S) (a : ℝ) : Set.InjOn (sides θ n S a) (S : Set ℂ) := by
  intro u hu v hv he
  by_contra huv
  obtain ⟨k, hk, h | h⟩ := edge_alt G a hu hv huv
  · exact h.2.2 (he ▸ h.2.1)
  · exact h.2.2 (he.symm ▸ h.2.1)

lemma two_missing (G : Cfg θ n S) (a : ℝ) {T1 T2 : Set (Fin n)}
    (h1 : ∀ u ∈ S, sides θ n S a u ≠ T1) (h2 : ∀ u ∈ S, sides θ n S a u ≠ T2) : T1 = T2 := by
  classical
  by_contra hne
  have hinj := sides_inj G a
  have hsub : S.image (sides θ n S a) ⊆ (Finset.univ.erase T1).erase T2 := by
    intro T hT
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hT
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨h2 u hu, h1 u hu⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, G.hcard,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_set, Fintype.card_fin] at hc
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) G.hn3
  omega

lemma card_ge (G : Cfg θ n S) : 7 ≤ S.card := by
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) G.hn3
  rw [G.hcard]; omega

lemma exists_other (G : Cfg θ n S) (Q : ℂ) : ∃ X ∈ S, X ≠ Q := by
  classical
  have h7 := card_ge G
  have : 0 < (S.erase Q).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := Q)
    omega
  obtain ⟨X, hX⟩ := Finset.card_pos.mp this
  exact ⟨X, (Finset.mem_erase.mp hX).2, (Finset.mem_erase.mp hX).1⟩

lemma miss_flip (G : Cfg θ n S) (a : ℝ) {p : ℂ} (hp : p ∈ S) {k : ℕ} (hk : k < n)
    (hm : Miss S θ p (a + k * θ)) :
    ∀ u ∈ S, sides θ n S a u ≠ {j | ¬ (j ∈ sides θ n S a p ↔ j = (⟨k, hk⟩ : Fin n))} := by
  intro u hu hs
  have hmem : ∀ j : Fin n, j ∈ sides θ n S a u ↔
      ¬ (j ∈ sides θ n S a p ↔ j = (⟨k, hk⟩ : Fin n)) := by
    intro j; rw [hs]; rfl
  have hne : p ≠ u := by
    intro h
    rw [← h] at hmem
    have := hmem ⟨k, hk⟩
    tauto
  obtain ⟨j, hj, h | h⟩ := edge_alt G a hp hu hne
  · have hjk : (⟨j, hj⟩ : Fin n) = ⟨k, hk⟩ := by
      have := hmem ⟨j, hj⟩
      have h1 := h.2.1
      have h2 := h.2.2
      tauto
    have e : j = k := by simpa using hjk
    subst e
    obtain ⟨φ, b1, b2, hpol⟩ := h.1
    exact (hm u hu φ b1 b2).1 hpol
  · have hjk : (⟨j, hj⟩ : Fin n) = ⟨k, hk⟩ := by
      have := hmem ⟨j, hj⟩
      have h1 := h.2.1
      have h2 := h.2.2
      tauto
    have e : j = k := by simpa using hjk
    subst e
    obtain ⟨φ, b1, b2, hpol⟩ := h.1
    exact (hm u hu φ b1 b2).2 hpol

lemma miss_unique_nat (G : Cfg θ n S) (a : ℝ) {p p' : ℂ} (hp : p ∈ S) (hp' : p' ∈ S)
    {k k' : ℕ} (hk : k < n) (hk' : k' < n)
    (hm : Miss S θ p (a + k * θ)) (hm' : Miss S θ p' (a + k' * θ)) : p = p' := by
  by_contra hne
  have e := two_missing G a (miss_flip G a hp hk hm) (miss_flip G a hp' hk' hm')
  have hmem : ∀ j : Fin n, ¬ (j ∈ sides θ n S a p ↔ j = (⟨k, hk⟩ : Fin n)) ↔
      ¬ (j ∈ sides θ n S a p' ↔ j = (⟨k', hk'⟩ : Fin n)) := fun j => Set.ext_iff.mp e j
  obtain ⟨j, hj, h | h⟩ := edge_alt G a hp hp' hne
  · have hjk : (⟨j, hj⟩ : Fin n) = ⟨k, hk⟩ ∨ (⟨j, hj⟩ : Fin n) = ⟨k', hk'⟩ := by
      have := hmem ⟨j, hj⟩
      have h1 := h.2.1
      have h2 := h.2.2
      tauto
    obtain ⟨φ, b1, b2, hpol⟩ := h.1
    rcases hjk with hjk | hjk
    · have e : j = k := by simpa using hjk
      subst e
      exact (hm p' hp' φ b1 b2).1 hpol
    · have e : j = k' := by simpa using hjk
      subst e
      exact (hm' p hp φ b1 b2).2 hpol
  · have hjk : (⟨j, hj⟩ : Fin n) = ⟨k, hk⟩ ∨ (⟨j, hj⟩ : Fin n) = ⟨k', hk'⟩ := by
      have := hmem ⟨j, hj⟩
      have h1 := h.2.1
      have h2 := h.2.2
      tauto
    obtain ⟨φ, b1, b2, hpol⟩ := h.1
    rcases hjk with hjk | hjk
    · have e : j = k := by simpa using hjk
      subst e
      exact (hm p' hp' φ b1 b2).2 hpol
    · have e : j = k' := by simpa using hjk
      subst e
      exact (hm' p hp φ b1 b2).1 hpol

lemma miss_add_pi {q : ℂ} {α : ℝ} (h : Miss S θ q α) : Miss S θ q (α + π) := by
  intro v hv φ b1 b2
  constructor
  · intro hp
    have := hp.neg'
    rw [neg_sub] at this
    exact (h v hv (φ - π) (by linarith) (by linarith)).2 this
  · intro hp
    have := hp.neg'
    rw [neg_sub] at this
    exact (h v hv (φ - π) (by linarith) (by linarith)).1 this

lemma miss_sub_pi {q : ℂ} {α : ℝ} (h : Miss S θ q α) : Miss S θ q (α - π) := by
  intro v hv φ b1 b2
  constructor
  · intro hp
    have := hp.neg
    rw [neg_sub] at this
    exact (h v hv (φ + π) (by linarith) (by linarith)).2 this
  · intro hp
    have := hp.neg
    rw [neg_sub] at this
    exact (h v hv (φ + π) (by linarith) (by linarith)).1 this

lemma miss_int {q : ℂ} {α : ℝ} (h : Miss S θ q α) (m : ℤ) : Miss S θ q (α + m * π) := by
  induction m using Int.induction_on with
  | zero => simpa using h
  | succ i ih =>
    have e : α + ((i : ℤ) + 1 : ℤ) * π = α + (i : ℤ) * π + π := by push_cast; ring
    rw [e]; exact miss_add_pi ih
  | pred i ih =>
    have e : α + ((-(i : ℤ) - 1 : ℤ) : ℝ) * π = α + ((-(i : ℤ) : ℤ) : ℝ) * π - π := by
      push_cast; ring
    rw [e]; exact miss_sub_pi ih

lemma miss_unique (G : Cfg θ n S) {p p' : ℂ} (hp : p ∈ S) (hp' : p' ∈ S) {α : ℝ} (j : ℤ)
    (hm : Miss S θ p α) (hm' : Miss S θ p' (α + j * θ)) : p = p' := by
  have hn0 : (0 : ℤ) < n := by have := G.hn3; omega
  have h1 := Int.emod_nonneg j hn0.ne'
  have h2 := Int.emod_lt_of_pos j hn0
  have h3 : ((j % n).toNat : ℤ) = j % n := Int.toNat_of_nonneg h1
  have hk : (j % n).toNat < n := by omega
  have hdec : (j : ℝ) = (n : ℝ) * ((j / n : ℤ) : ℝ) + (((j % n).toNat : ℕ) : ℝ) := by
    have h4 : j = (n : ℤ) * (j / n) + ((j % n).toNat : ℤ) := by
      rw [h3]; exact (Int.mul_ediv_add_emod j n).symm
    exact_mod_cast h4
  have hm2 := miss_int hm' (-(j / n))
  have e : α + j * θ + ((-(j / n) : ℤ) : ℝ) * π = α + (((j % n).toNat : ℕ) : ℝ) * θ := by
    have := G.hn
    push_cast
    rw [hdec, ← this]
    ring
  rw [e] at hm2
  exact miss_unique_nat G α hp hp' (by have := G.hn3; omega : 0 < n) hk (by simpa using hm) hm2

lemma miss_exists (G : Cfg θ n S) {q : ℂ} (hq : q ∈ S) : ∃ α : ℝ, Miss S θ q α := by
  classical
  have hθ := G.hθ
  have hπ := Real.pi_pos
  obtain ⟨X0, hX0, hX0q⟩ := exists_other G q
  have hne : ((S.erase q) ×ˢ (S.erase q)).Nonempty :=
    ⟨(X0, X0), Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨hX0q, hX0⟩, Finset.mem_erase.mpr ⟨hX0q, hX0⟩⟩⟩
  obtain ⟨⟨p1, p2⟩, hmem, hmax⟩ := Finset.exists_max_image _
    (fun pr : ℂ × ℂ => EuclideanGeometry.angle pr.1 q pr.2) hne
  obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hmem
  obtain ⟨hp1q, hp1⟩ := Finset.mem_erase.mp hm1
  obtain ⟨hp2q, hp2⟩ := Finset.mem_erase.mp hm2
  simp only at hp1q hp1 hp2q hp2 hmax
  have hmax' : ∀ X ∈ S, ∀ Y ∈ S, X ≠ q → Y ≠ q →
      EuclideanGeometry.angle X q Y ≤ EuclideanGeometry.angle p1 q p2 := by
    intro X hX Y hY hXq hYq
    exact hmax (X, Y) (Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨hXq, hX⟩, Finset.mem_erase.mpr ⟨hYq, hY⟩⟩)
  have hω := G.hG p1 hp1 q hq p2 hp2 hp1q hp2q
  have hω0 : 0 ≤ EuclideanGeometry.angle p1 q p2 := EuclideanGeometry.angle_nonneg _ _ _
  have hwlog : ∃ q1 ∈ S, ∃ q2 ∈ S, ∃ ψ : ℝ, q1 ≠ q ∧ q2 ≠ q ∧ Pol (q1 - q) ψ ∧
      Pol (q2 - q) (ψ + EuclideanGeometry.angle p1 q p2) := by
    have hpol1 := pol_arg (sub_ne_zero.mpr hp1q)
    obtain ⟨φ2, c1, c2, hpol2⟩ := pol_exists (sub_ne_zero.mpr hp2q) (Complex.arg (p1 - q) - π)
    have ha := angle_pol hpol1 hpol2 (by rw [abs_le]; constructor <;> linarith)
    by_cases hc : Complex.arg (p1 - q) ≤ φ2
    · refine ⟨p1, hp1, p2, hp2, Complex.arg (p1 - q), hp1q, hp2q, hpol1, ?_⟩
      rw [ha, abs_of_nonpos (by linarith)]
      have e : Complex.arg (p1 - q) + -(Complex.arg (p1 - q) - φ2) = φ2 := by ring
      rw [e]; exact hpol2
    · rw [not_le] at hc
      refine ⟨p2, hp2, p1, hp1, φ2, hp2q, hp1q, hpol2, ?_⟩
      rw [ha, abs_of_nonneg (by linarith)]
      have e : φ2 + (Complex.arg (p1 - q) - φ2) = Complex.arg (p1 - q) := by ring
      rw [e]; exact hpol1
  obtain ⟨q1, hq1, q2, hq2, ψ, hq1q, hq2q, pol1, pol2⟩ := hwlog
  set ω := EuclideanGeometry.angle p1 q p2 with hωdef
  refine ⟨ψ - θ - (π - θ - ω) / 2, ?_⟩
  intro v hv φ b1 b2
  constructor
  · intro hp
    have hvq : v ≠ q := fun h => hp.ne_zero (by rw [h, sub_self])
    have hab : |φ - (ψ + ω)| = ψ + ω - φ := by
      rw [abs_of_nonpos (by linarith)]; ring
    have ha := angle_pol hp pol2 (by rw [hab]; linarith)
    have := hmax' v hv q2 hq2 hvq hq2q
    rw [ha, hab] at this
    linarith
  · intro hp
    have hvq : v ≠ q := fun h => hp.ne_zero (by rw [h, sub_self])
    have hp' : Pol (v - q) (φ + π) := by
      have := hp.neg
      rwa [neg_sub] at this
    have hab : |φ + π - ψ| = φ + π - ψ := abs_of_nonneg (by linarith)
    have ha := angle_pol hp' pol1 (by rw [hab]; linarith)
    have := hmax' v hv q1 hq1 hvq hq1q
    rw [ha, hab] at this
    linarith

lemma wedge_of_half (G : Cfg θ n S) {Q : ℂ} (hQ : Q ∈ S) (a0 : ℝ) {X0 : ℂ} (hX0 : X0 ∈ S)
    (hX0Q : X0 ≠ Q)
    (H : ∀ X ∈ S, X ≠ Q → ∃ φ : ℝ, a0 ≤ φ ∧ φ ≤ a0 + π ∧ Pol (X - Q) φ) :
    ∃ a c : ℝ, Wedge θ S Q a c ∧ (∀ X ∈ S, Pol (X - Q) a0 → a = a0) := by
  classical
  have hπ := Real.pi_pos
  choose! d hd using H
  have hne : (S.erase Q).Nonempty := ⟨X0, Finset.mem_erase.mpr ⟨hX0Q, hX0⟩⟩
  obtain ⟨Xm, hXm, hmin⟩ := Finset.exists_min_image (S.erase Q) d hne
  obtain ⟨XM, hXM, hmax⟩ := Finset.exists_max_image (S.erase Q) d hne
  obtain ⟨hXmQ, hXmS⟩ := Finset.mem_erase.mp hXm
  obtain ⟨hXMQ, hXMS⟩ := Finset.mem_erase.mp hXM
  obtain ⟨m1, m2, m3⟩ := hd Xm hXmS hXmQ
  obtain ⟨M1, M2, M3⟩ := hd XM hXMS hXMQ
  have hle : d Xm ≤ d XM := hmin XM hXM
  have ha := angle_pol m3 M3 (by rw [abs_le]; constructor <;> linarith)
  have hg := G.hG Xm hXmS Q hQ XM hXMS hXmQ hXMQ
  rw [ha, abs_of_nonpos (by linarith)] at hg
  refine ⟨d Xm, d XM, ⟨hle, by linarith, ⟨Xm, hXmS, m3⟩, ⟨XM, hXMS, M3⟩, ?_⟩, ?_⟩
  · intro X hX hXQ
    have hXe : X ∈ S.erase Q := Finset.mem_erase.mpr ⟨hXQ, hX⟩
    exact ⟨d X, hmin X hXe, hmax X hXe, (hd X hX hXQ).2.2⟩
  · intro X hX hp
    have hXQ : X ≠ Q := fun h => hp.ne_zero (by rw [h, sub_self])
    obtain ⟨x1, x2, x3⟩ := hd X hX hXQ
    have e := Pol.unique x3 hp (by rw [abs_lt]; constructor <;> linarith)
    have := hmin X (Finset.mem_erase.mpr ⟨hXQ, hX⟩)
    linarith

lemma exists_wedge (G : Cfg θ n S) : ∃ Q ∈ S, ∃ a c : ℝ, Wedge θ S Q a c := by
  have hθ := G.hθ
  have hπ := Real.pi_pos
  have hn0 : 0 < n := by have := G.hn3; omega
  by_cases hU : ∃ u ∈ S, sides θ n S 0 u = Set.univ
  · obtain ⟨Q, hQ, hs⟩ := hU
    obtain ⟨X0, hX0, hX0Q⟩ := exists_other G Q
    obtain ⟨a, c, W, -⟩ := wedge_of_half G hQ 0 hX0 hX0Q (by
      intro X hX hXQ
      obtain ⟨k, hk, h | h⟩ := edge_alt G 0 hQ hX (Ne.symm hXQ)
      · obtain ⟨φ, b1, b2, hp⟩ := h.1
        obtain ⟨i0, i1⟩ := G.idx hk
        exact ⟨φ, by linarith, by linarith, hp⟩
      · exact absurd (hs ▸ Set.mem_univ _) h.2.2)
    exact ⟨Q, hQ, a, c, W⟩
  · by_cases hE : ∃ u ∈ S, sides θ n S 0 u = ∅
    · obtain ⟨Q, hQ, hs⟩ := hE
      obtain ⟨X0, hX0, hX0Q⟩ := exists_other G Q
      obtain ⟨a, c, W, -⟩ := wedge_of_half G hQ π hX0 hX0Q (by
        intro X hX hXQ
        obtain ⟨k, hk, h | h⟩ := edge_alt G 0 hQ hX (Ne.symm hXQ)
        · have := h.2.1
          rw [hs] at this
          exact absurd this (Set.notMem_empty _)
        · obtain ⟨φ, b1, b2, hp⟩ := h.1
          obtain ⟨i0, i1⟩ := G.idx hk
          have hp' : Pol (X - Q) (φ + π) := by
            have := hp.neg
            rwa [neg_sub] at this
          exact ⟨φ + π, by linarith, by linarith, hp'⟩)
      exact ⟨Q, hQ, a, c, W⟩
    · exfalso
      have e := two_missing G 0 (fun u hu h => hU ⟨u, hu, h⟩) (fun u hu h => hE ⟨u, hu, h⟩)
      have : (⟨0, hn0⟩ : Fin n) ∈ (∅ : Set (Fin n)) := e ▸ Set.mem_univ _
      exact this

lemma step (G : Cfg θ n S) {Q : ℂ} (hQ : Q ∈ S) {a c : ℝ} (W : Wedge θ S Q a c) :
    ∃ R ∈ S, ∃ c' : ℝ, Wedge θ S R (c - π) c' := by
  have hθ := G.hθ
  have hπ := Real.pi_pos
  obtain ⟨R, hR, pR⟩ := W.lst
  have hRQ : R ≠ Q := fun h => pR.ne_zero (by rw [h, sub_self])
  have hlt := W.lt
  have pQR : Pol (Q - R) (c - π) := by
    have := pR.neg'
    rwa [neg_sub] at this
  obtain ⟨a', c', W', hfix⟩ := wedge_of_half G hR (c - π) hQ (Ne.symm hRQ) (by
    intro X hX hXR
    by_cases hXQ : X = Q
    · rw [hXQ]
      exact ⟨c - π, le_refl _, by linarith, pQR⟩
    · obtain ⟨φ, d1, d2, hpX⟩ := W.all X hX hXQ
      obtain ⟨χ, e1, e2, hpχ⟩ := pol_exists (sub_ne_zero.mpr hXR) (c - π)
      obtain ⟨r1, hr1, -, H1⟩ := hpX.data
      obtain ⟨r2, hr2, -, H2⟩ := pQR.data
      obtain ⟨r3, hr3, -, H3⟩ := hpχ.data
      have hh : hgt (c - π) (X - R) = hgt (c - π) (X - Q) + hgt (c - π) (Q - R) := by
        rw [hgt_sub, hgt_sub, hgt_sub]; ring
      rw [H1, H2, H3, sub_self, Real.sin_zero, mul_zero, add_zero] at hh
      have s1 : 0 ≤ Real.sin (φ - (c - π)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have s3 : 0 ≤ Real.sin (χ - (c - π)) := by
        have h0 : 0 ≤ r3 * Real.sin (χ - (c - π)) := by rw [hh]; positivity
        exact (mul_nonneg_iff_of_pos_left hr3).mp h0
      have hχ : χ - (c - π) ≤ π := by
        by_contra hc
        rw [not_le] at hc
        have hneg : Real.sin (χ - (c - π) - 2 * π) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
        rw [Real.sin_sub_two_pi] at hneg
        linarith
      exact ⟨χ, e1, by linarith, hpχ⟩)
  have e := hfix Q hQ pQR
  subst e
  exact ⟨R, hR, c', W'⟩

lemma wedge_miss (hθ : 0 < θ) {Q : ℂ} {a c : ℝ} (W : Wedge θ S Q a c) {α : ℝ}
    (h1 : c - π < α) (h2 : α ≤ a - θ) : Miss S θ Q α := by
  have hπ := Real.pi_pos
  have hlt := W.lt
  have hle := W.le
  intro v hv φ b1 b2
  constructor
  · intro hp
    have hvQ : v ≠ Q := fun h => hp.ne_zero (by rw [h, sub_self])
    obtain ⟨ψ, d1, d2, hq⟩ := W.all v hv hvQ
    have := Pol.unique hp hq (by rw [abs_lt]; constructor <;> linarith)
    linarith
  · intro hp
    have hvQ : v ≠ Q := fun h => hp.ne_zero (by rw [h, sub_self])
    have hp' : Pol (v - Q) (φ + π) := by
      have := hp.neg
      rwa [neg_sub] at this
    obtain ⟨ψ, d1, d2, hq⟩ := W.all v hv hvQ
    have := Pol.unique hp' hq (by rw [abs_lt]; constructor <;> linarith)
    linarith

lemma wedge_hgt {Q : ℂ} {a c : ℝ} (W : Wedge θ S Q a c) {β : ℝ}
    (h1 : c - π < β) (h2 : β < a) : ∀ X ∈ S, X ≠ Q → 0 < hgt β (X - Q) := by
  intro X hX hXQ
  obtain ⟨φ, d1, d2, hp⟩ := W.all X hX hXQ
  obtain ⟨r, hr, -, H⟩ := hp.data
  rw [H]
  exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

lemma wedge_unique (hθ : 0 < θ) {Q : ℂ} {a c a' c' : ℝ} (W : Wedge θ S Q a c)
    (W' : Wedge θ S Q a' c') (h1 : a' < a) (h2 : a < a' + 2 * π) : False := by
  have hπ := Real.pi_pos
  have l1 := W.lt
  have l2 := W'.lt
  have k1 := W.le
  have k2 := W'.le
  obtain ⟨X, hX, pX⟩ := W.fst
  obtain ⟨X', hX', pX'⟩ := W'.fst
  have hXQ : X ≠ Q := fun h => pX.ne_zero (by rw [h, sub_self])
  have hXQ' : X' ≠ Q := fun h => pX'.ne_zero (by rw [h, sub_self])
  obtain ⟨φ, d1, d2, hp⟩ := W'.all X hX hXQ
  obtain ⟨φ', d1', d2', hp'⟩ := W.all X' hX' hXQ'
  have e1 := Pol.unique pX hp (by rw [abs_lt]; constructor <;> linarith)
  have e2 := Pol.unique (pol_add_two_pi pX') hp' (by rw [abs_lt]; constructor <;> linarith)
  linarith

lemma exists_walk (G : Cfg θ n S) : ∃ (Q : ℕ → ℂ) (a c : ℕ → ℝ),
    (∀ i, Q i ∈ S) ∧ (∀ i, Wedge θ S (Q i) (a i) (c i)) ∧ ∀ i, a (i + 1) = c i - π := by
  obtain ⟨Q0, hQ0, a0, c0, W0⟩ := exists_wedge G
  have hstep : ∀ s : {x : ℂ × ℝ × ℝ // x.1 ∈ S ∧ Wedge θ S x.1 x.2.1 x.2.2},
      ∃ t : {x : ℂ × ℝ × ℝ // x.1 ∈ S ∧ Wedge θ S x.1 x.2.1 x.2.2},
        t.1.2.1 = s.1.2.2 - π := by
    intro s
    obtain ⟨R, hR, c', W'⟩ := step G s.2.1 s.2.2
    exact ⟨⟨(R, s.1.2.2 - π, c'), hR, W'⟩, rfl⟩
  choose nxt hnxt using hstep
  refine ⟨fun i => (nxt^[i] ⟨(Q0, a0, c0), hQ0, W0⟩).1.1,
    fun i => (nxt^[i] ⟨(Q0, a0, c0), hQ0, W0⟩).1.2.1,
    fun i => (nxt^[i] ⟨(Q0, a0, c0), hQ0, W0⟩).1.2.2, ?_, ?_, ?_⟩
  · intro i; exact (nxt^[i] ⟨(Q0, a0, c0), hQ0, W0⟩).2.1
  · intro i; exact (nxt^[i] ⟨(Q0, a0, c0), hQ0, W0⟩).2.2
  · intro i
    simp only [Function.iterate_succ_apply']
    exact hnxt _

lemma two_mul_lt_pow {n : ℕ} (hn : 3 ≤ n) : 2 * n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem no_cfg (G : Cfg θ n S) : False := by
  classical
  have hθ := G.hθ
  have hπ := Real.pi_pos
  have hnθ := G.hn
  obtain ⟨Q, a, c, hS, hW, hrec⟩ := exists_walk G
  have hdec : ∀ i, a (i + 1) < a i - θ := by
    intro i; have := (hW i).lt; rw [hrec]; linarith
  have hlow : ∀ i, a i - π ≤ a (i + 1) := by
    intro i; have := (hW i).le; rw [hrec]; linarith
  have hdecS : ∀ i : ℕ, a (i + 1) < a 0 - ((i : ℝ) + 1) * θ := by
    intro i
    induction i with
    | zero => have := hdec 0; simpa using this
    | succ m ih => have := hdec (m + 1); push_cast; linarith
  have hex : ∃ M, a M ≤ a 0 - 2 * π := by
    refine ⟨2 * n - 1 + 1, ?_⟩
    have h := hdecS (2 * n - 1)
    have e : ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * n := by
      have : 1 ≤ 2 * n := by have := G.hn3; omega
      rw [Nat.cast_sub this]; push_cast; ring
    rw [e] at h
    nlinarith
  have hM := Nat.find_spec hex
  have hMmin : ∀ m, m < Nat.find hex → a 0 - 2 * π < a m := by
    intro m hm
    have := Nat.find_min hex hm
    linarith
  set M := Nat.find hex with hMdef
  have hM0 : M ≠ 0 := by
    intro h
    rw [h] at hM
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have heq : a M = a 0 - 2 * π := by
    by_contra hne
    have hlt : a M < a 0 - 2 * π := lt_of_le_of_ne hM hne
    rw [hm] at hlt
    have hmm : a 0 - 2 * π < a m := hMmin m (by omega)
    have h10 := hdec 0
    have hsm := hdec m
    simp only [zero_add] at h10
    set β := (max (a (m + 1)) (a 1 - 2 * π) + (a 0 - 2 * π)) / 2 with hβ
    have hmx : max (a (m + 1)) (a 1 - 2 * π) < a 0 - 2 * π := max_lt hlt (by linarith)
    have b1 : a (m + 1) < β := by
      have := le_max_left (a (m + 1)) (a 1 - 2 * π); rw [hβ]; linarith
    have b2 : a 1 - 2 * π < β := by
      have := le_max_right (a (m + 1)) (a 1 - 2 * π); rw [hβ]; linarith
    have b3 : β < a 0 - 2 * π := by rw [hβ]; linarith
    have r1 := hrec m
    have r0 := hrec 0
    simp only [zero_add] at r0
    have hmin1 := wedge_hgt (hW m) (β := β) (by linarith) (by linarith)
    have hmin0 := wedge_hgt (hW 0) (β := β + 2 * π) (by linarith) (by linarith)
    have hQe : Q m = Q 0 := by
      by_contra hQne
      have t1 := hmin1 (Q 0) (hS 0) (Ne.symm hQne)
      have t2 := hmin0 (Q m) (hS m) hQne
      rw [hgt_two_pi, hgt_sub] at t2
      rw [hgt_sub] at t1
      linarith
    by_cases hm0 : m = 0
    · rw [hm0] at hlt
      have := hlow 0
      simp only [zero_add] at this hlt
      linarith
    · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hd := hdecS m'
      rw [← Nat.succ_eq_add_one, ← hm'] at hd
      have hpos : 0 < ((m' : ℝ) + 1) * θ := by positivity
      have Wm := hW m
      rw [hQe] at Wm
      exact wedge_unique hθ (hW 0) Wm (by linarith) (by linarith)
  have hMlt : M < 2 * n := by
    have hd := hdecS m
    rw [← Nat.succ_eq_add_one, ← hm, heq] at hd
    have h1 : ((m : ℝ) + 1) * θ < (2 * n : ℝ) * θ := by nlinarith
    have h2 : (m : ℝ) + 1 < 2 * n := lt_of_mul_lt_mul_right h1 hθ.le
    have h3 : ((m + 1 : ℕ) : ℝ) < ((2 * n : ℕ) : ℝ) := by push_cast; exact h2
    rw [hm]
    exact_mod_cast h3
  have hbM : a M + (M : ℝ) * θ ≤ a 0 - θ := by
    have h1 : (M : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hMlt
    rw [heq]
    nlinarith
  have hcover : ∀ q ∈ S, ∃ i, i < M ∧ q = Q i := by
    intro q hq
    obtain ⟨α, hα⟩ := miss_exists G hq
    set j : ℤ := ⌊(a 0 - α) / θ⌋ with hj
    have j1 : (j : ℝ) * θ ≤ a 0 - α := by
      have := Int.floor_le ((a 0 - α) / θ)
      rwa [le_div_iff₀ hθ] at this
    have j2 : a 0 - α < ((j : ℝ) + 1) * θ := by
      have := Int.lt_floor_add_one ((a 0 - α) / θ)
      rwa [div_lt_iff₀ hθ] at this
    have hP : ∃ i, a (i + 1) + ((i : ℝ) + 1) * θ < α + j * θ := by
      refine ⟨m, ?_⟩
      have : a M + (M : ℝ) * θ ≤ a 0 - θ := hbM
      rw [hm] at this
      push_cast at this
      linarith
    have hi := Nat.find_spec hP
    have himin := fun k hk => Nat.find_min hP (m := k) hk
    have hile : Nat.find hP ≤ m := Nat.find_min' hP (by
      have : a M + (M : ℝ) * θ ≤ a 0 - θ := hbM
      rw [hm] at this
      push_cast at this
      linarith)
    set i := Nat.find hP with hidef
    have hup : α + j * θ ≤ a i + (i : ℝ) * θ := by
      by_cases hi0 : i = 0
      · rw [hi0]; simp; linarith
      · obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have := himin i' (by omega)
        rw [not_lt] at this
        rw [hi']
        push_cast
        linarith
    refine ⟨i, by omega, ?_⟩
    have hmiss : Miss S θ (Q i) (α + j * θ - ((i : ℝ) + 1) * θ) :=
      wedge_miss hθ (hW i) (by rw [← hrec]; linarith) (by linarith)
    have e : α + j * θ - ((i : ℝ) + 1) * θ = α + ((j - (i + 1) : ℤ) : ℝ) * θ := by
      push_cast; ring
    rw [e] at hmiss
    exact miss_unique G hq (hS i) _ hα hmiss
  have hsub : S ⊆ (Finset.range M).image Q := by
    intro q hq
    obtain ⟨i, hi, e⟩ := hcover q hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, e.symm⟩
  have hc := Finset.card_le_card hsub
  have hc2 := Finset.card_image_le (s := Finset.range M) (f := Q)
  rw [Finset.card_range] at hc2
  rw [G.hcard] at hc
  have := two_mul_lt_pow G.hn3
  omega

-- Upper bound: subset sums of powers of z.

lemma angle_le {p q r : ℂ} {φ φ' B : ℝ} (h1 : Pol (p - q) φ) (h2 : Pol (r - q) φ')
    (hB : B ≤ π)
    (h : |φ - φ'| ≤ B ∨ |φ - φ' + 2 * π| ≤ B ∨ |φ - φ' - 2 * π| ≤ B) :
    EuclideanGeometry.angle p q r ≤ B := by
  rcases h with h | h | h
  · rw [angle_pol h1 h2 (by linarith)]; exact h
  · have e : φ + 2 * π - φ' = φ - φ' + 2 * π := by ring
    rw [angle_pol (pol_add_two_pi h1) h2 (by rw [e]; linarith), e]; exact h
  · have e : φ - 2 * π - φ' = φ - φ' - 2 * π := by ring
    rw [angle_pol (pol_sub_two_pi h1) h2 (by rw [e]; linarith), e]; exact h

lemma angle_dirs {θ η : ℝ} {n : ℕ} (hθ : 0 < θ) (hn : (n : ℝ) * θ = π)
    (hη2 : 2 * η ≤ θ) {p q r : ℂ} {k k' : ℕ} (hk : k < n) (hk' : k' < n) {ψ ψ' σ σ' : ℝ}
    (hψ : |ψ| ≤ η) (hψ' : |ψ'| ≤ η) (hσ : σ = 0 ∨ σ = π) (hσ' : σ' = 0 ∨ σ' = π)
    (hs : k = k' → σ = σ')
    (h1 : Pol (p - q) (k * θ + ψ + σ)) (h2 : Pol (r - q) (k' * θ + ψ' + σ')) :
    EuclideanGeometry.angle p q r ≤ π - θ + 2 * η := by
  have hπ := Real.pi_pos
  obtain ⟨x1, x2⟩ := abs_le.mp hψ
  obtain ⟨y1, y2⟩ := abs_le.mp hψ'
  refine angle_le h1 h2 (by linarith) ?_
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · have c1 : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hlt
    have c2 : (k' : ℝ) + 1 ≤ n := by exact_mod_cast hk'
    have c0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have d1 : (k : ℝ) * θ + θ ≤ k' * θ := by nlinarith
    have d2 : (k' : ℝ) * θ + θ ≤ π := by nlinarith
    have d3 : 0 ≤ (k : ℝ) * θ := by positivity
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · left; rw [abs_le]; constructor <;> linarith
    · right; left; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith
  · have e := hs heq
    subst heq
    subst e
    have c2 : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have c0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have d2 : θ ≤ π := by nlinarith
    left; rw [abs_le]; constructor <;> linarith
  · have c1 : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hgt
    have c2 : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have c0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
    have d1 : (k' : ℝ) * θ + θ ≤ k * θ := by nlinarith
    have d2 : (k : ℝ) * θ + θ ≤ π := by nlinarith
    have d3 : 0 ≤ (k' : ℝ) * θ := by positivity
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · left; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith
    · right; right; rw [abs_le]; constructor <;> linarith
    · left; rw [abs_le]; constructor <;> linarith

lemma pol_one_add {η : ℝ} (hη : 0 < η) (hη2 : η ≤ π / 2) {u : ℂ}
    (hu : 2 * ‖u‖ ≤ Real.sin η) : ∃ ψ : ℝ, |ψ| ≤ η ∧ Pol (1 + u) ψ := by
  have hs1 : Real.sin η ≤ 1 := Real.sin_le_one η
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hre : (1 : ℝ) / 2 ≤ (1 + u).re := by
    have := Complex.abs_re_le_norm u
    have := (abs_le.mp this).1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hne : (1 + u) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hnorm : (1 : ℝ) / 2 ≤ ‖1 + u‖ := le_trans hre (Complex.re_le_norm _)
  have hnpos : 0 < ‖1 + u‖ := by linarith
  have him : |(1 + u).im| ≤ ‖u‖ := by
    simpa using Complex.abs_im_le_norm u
  have ht : |(1 + u).im / ‖1 + u‖| ≤ Real.sin η := by
    rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    nlinarith
  refine ⟨Complex.arg (1 + u), ?_, pol_arg hne⟩
  rw [Complex.arg_of_re_nonneg (by linarith)]
  obtain ⟨t1, t2⟩ := abs_le.mp ht
  rw [abs_le]
  constructor
  · have := Real.arcsin_le_arcsin (x := Real.sin (-η)) (y := (1 + u).im / ‖1 + u‖)
      (by rw [Real.sin_neg]; exact t1)
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at this
  · have := Real.arcsin_le_arcsin t2
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at this

lemma pol_pow {z : ℂ} {ρ θ : ℝ} (hρ : 0 < ρ)
    (hz : z = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (k : ℕ) :
    Pol (z ^ k) (k * θ) := by
  refine ⟨ρ ^ k, pow_pos hρ k, ?_⟩
  rw [hz, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

noncomputable def pt (z : ℂ) (n : ℕ) (T : Finset ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, if k ∈ T then z ^ k else 0

lemma pt_diff {z : ℂ} {n : ℕ} (hz : ‖z‖ ≤ 1) {T T' : Finset ℕ}
    (hT : T ⊆ Finset.range n) (hT' : T' ⊆ Finset.range n) (hne : T ≠ T') :
    ∃ k, k < n ∧ (k ∈ T ↔ k ∉ T') ∧ ∃ u : ℂ, ‖u‖ ≤ n * ‖z‖ ∧
      (k ∈ T → pt z n T - pt z n T' = z ^ k * (1 + u)) ∧
      (k ∉ T → pt z n T - pt z n T' = -(z ^ k * (1 + u))) := by
  classical
  have hD : ((Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T'))).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hne
    ext k
    by_cases hk : k ∈ Finset.range n
    · have : k ∉ (Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T')) := by
        rw [hemp]; exact Finset.notMem_empty _
      rw [Finset.mem_filter] at this
      tauto
    · exact ⟨fun h => absurd (hT h) hk, fun h => absurd (hT' h) hk⟩
  set k0 := ((Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T'))).min' hD with hk0
  have hk0mem := Finset.min'_mem _ hD
  rw [← hk0, Finset.mem_filter, Finset.mem_range] at hk0mem
  obtain ⟨hk0n, hk0d⟩ := hk0mem
  have hbelow : ∀ k, k < k0 → (k ∈ T ↔ k ∈ T') := by
    intro k hk
    by_contra hc
    have hmem : k ∈ (Finset.range n).filter (fun k => ¬ (k ∈ T ↔ k ∈ T')) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩
    have := Finset.min'_le _ k hmem
    omega
  set e : ℕ → ℂ := fun k => (if k ∈ T then (1 : ℂ) else 0) - (if k ∈ T' then 1 else 0) with he
  set w : ℂ := ∑ k ∈ Finset.range n, if k0 < k then e k * z ^ (k - k0) else 0 with hw
  have hsum : pt z n T - pt z n T' = z ^ k0 * (e k0 + w) := by
    unfold pt
    rw [← Finset.sum_sub_distrib, mul_add, hw, Finset.mul_sum]
    have h1 : z ^ k0 * e k0 = ∑ k ∈ Finset.range n, if k = k0 then z ^ k0 * e k0 else 0 := by
      rw [Finset.sum_ite_eq' (Finset.range n) k0]
      simp [hk0n]
    rw [h1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rcases lt_trichotomy k k0 with hlt | heq | hgt
    · have := hbelow k hlt
      have hk1 : ¬ k = k0 := by omega
      have hk2 : ¬ k0 < k := by omega
      rw [if_neg hk1, if_neg hk2]
      by_cases hkT : k ∈ T
      · have hkT' : k ∈ T' := this.mp hkT
        simp [hkT, hkT']
      · have hkT' : k ∉ T' := fun h => hkT (this.mpr h)
        simp [hkT, hkT']
    · have hk2 : ¬ k0 < k := by omega
      rw [if_pos heq, if_neg hk2, heq]
      simp only [he]
      split_ifs <;> ring
    · have hk1 : ¬ k = k0 := by omega
      rw [if_neg hk1, if_pos hgt]
      have hpow : z ^ k = z ^ k0 * z ^ (k - k0) := by
        rw [← pow_add]; congr 1; omega
      simp only [he, hpow]
      split_ifs <;> ring
  have hebound : ∀ k, ‖e k‖ ≤ 1 := by
    intro k
    simp only [he]
    split_ifs <;> simp
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hwb : ‖w‖ ≤ n * ‖z‖ := by
    have := norm_sum_le_of_le (Finset.range n)
      (f := fun k => if k0 < k then e k * z ^ (k - k0) else 0) (n := fun _ => ‖z‖) (by
        intro k _
        by_cases hk : k0 < k
        · rw [if_pos hk, norm_mul, norm_pow]
          have h1 : ‖z‖ ^ (k - k0) ≤ ‖z‖ := pow_le_of_le_one hz0 hz (by omega)
          have h2 := hebound k
          have h3 : 0 ≤ ‖z‖ ^ (k - k0) := pow_nonneg hz0 _
          nlinarith [norm_nonneg (e k)]
        · rw [if_neg hk, norm_zero]; exact hz0)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  refine ⟨k0, hk0n, by tauto, ?_⟩
  by_cases hkT : k0 ∈ T
  · have hkT' : k0 ∉ T' := by tauto
    refine ⟨w, hwb, fun _ => ?_, fun h => absurd hkT h⟩
    rw [hsum]
    simp [he, hkT, hkT']
  · have hkT' : k0 ∈ T' := by tauto
    refine ⟨-w, by rw [norm_neg]; exact hwb, fun h => absurd h hkT, fun _ => ?_⟩
    rw [hsum]
    simp [he, hkT, hkT']
    ring

set_option maxHeartbeats 1000000 in
lemma upper {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, S.card = 2 ^ n ∧ ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
      EuclideanGeometry.angle p q r < π - π / n + ε := by
  classical
  have hπ := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set θ : ℝ := π / n with hθdef
  have hθ : 0 < θ := by positivity
  have hnθ : (n : ℝ) * θ = π := by rw [hθdef]; field_simp
  have hθπ : θ ≤ π := by nlinarith
  set η : ℝ := min ε θ / 4 with hηdef
  have hm : 0 < min ε θ := lt_min hε hθ
  have hη : 0 < η := by positivity
  have hηε : 4 * η ≤ ε := by rw [hηdef]; linarith [min_le_left ε θ]
  have hηθ : 4 * η ≤ θ := by rw [hηdef]; linarith [min_le_right ε θ]
  have hsin : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη (by linarith)
  set ρ : ℝ := Real.sin η / (2 * n) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ2 : 2 * (n * ρ) = Real.sin η := by rw [hρdef]; field_simp
  have hρ1 : ρ ≤ 1 := by
    have := Real.sin_le_one η
    nlinarith
  set z : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hzn : ‖z‖ = ρ := Pol.norm_eq hρ hz
  have hdir : ∀ T ∈ (Finset.range n).powerset, ∀ T' ∈ (Finset.range n).powerset, T ≠ T' →
      ∃ k, k < n ∧ (k ∈ T ↔ k ∉ T') ∧ ∃ ψ σ : ℝ, |ψ| ≤ η ∧ (σ = 0 ∨ σ = π) ∧
        (σ = 0 ↔ k ∈ T) ∧ Pol (pt z n T - pt z n T') (k * θ + ψ + σ) := by
    intro T hT T' hT' hne
    obtain ⟨k, hk, hiff, u, hu, h1, h2⟩ := pt_diff (z := z) (n := n) (by rw [hzn]; exact hρ1)
      (Finset.mem_powerset.mp hT) (Finset.mem_powerset.mp hT') hne
    rw [hzn] at hu
    obtain ⟨ψ, hψ, hpol⟩ := pol_one_add hη (by linarith) (u := u) (by linarith)
    have hmul := pol_mul (pol_pow hρ hz k) hpol
    refine ⟨k, hk, hiff, ψ, ?_⟩
    by_cases hkT : k ∈ T
    · refine ⟨0, hψ, Or.inl rfl, by simp [hkT], ?_⟩
      rw [h1 hkT, add_zero]
      exact hmul
    · refine ⟨π, hψ, Or.inr rfl, by simp [hkT, hπ.ne'], ?_⟩
      rw [h2 hkT]
      exact hmul.neg
  have hinj : Set.InjOn (pt z n) ((Finset.range n).powerset : Set (Finset ℕ)) := by
    intro T hT T' hT' he
    by_contra hne
    obtain ⟨k, -, -, ψ, σ, -, -, -, hpol⟩ := hdir T hT T' hT' hne
    exact hpol.ne_zero (by rw [he, sub_self])
  refine ⟨(Finset.range n).powerset.image (pt z n), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_range]
  · intro p hp q hq r hr hpq hrq
    obtain ⟨Tp, hTp, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨Tq, hTq, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨Tr, hTr, rfl⟩ := Finset.mem_image.mp hr
    have hpq' : Tp ≠ Tq := fun h => hpq (by rw [h])
    have hrq' : Tr ≠ Tq := fun h => hrq (by rw [h])
    obtain ⟨k, hk, hiff, ψ, σ, hψ, hσ, hσT, hpol⟩ := hdir Tp hTp Tq hTq hpq'
    obtain ⟨k', hk', hiff', ψ', σ', hψ', hσ', hσT', hpol'⟩ := hdir Tr hTr Tq hTq hrq'
    have hs : k = k' → σ = σ' := by
      intro e
      subst e
      have hTT : k ∈ Tp ↔ k ∈ Tr :=
        ⟨fun h => hiff'.mpr (hiff.mp h), fun h => hiff.mpr (hiff'.mp h)⟩
      rcases hσ with h | h <;> rcases hσ' with h' | h'
      · rw [h, h']
      · exfalso
        have a1 := hσT.mp h
        have a2 : ¬ σ' = 0 := by rw [h']; exact hπ.ne'
        exact a2 (hσT'.mpr (hTT.mp a1))
      · exfalso
        have a1 := hσT'.mp h'
        have a2 : ¬ σ = 0 := by rw [h]; exact hπ.ne'
        exact a2 (hσT.mpr (hTT.mpr a1))
      · rw [h, h']
    have := angle_dirs hθ hnθ (by linarith) hk hk' hψ hψ' hσ hσ' hs hpol hpol'
    linarith

end OMA.ES504E

theorem OMA.solution : type_of% @Erdos504.erdos_504.variants.endpoint := by
  intro n hn
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have e : (1 - 1 / (n : ℝ)) * Real.pi = Real.pi - Real.pi / n := by field_simp
  have hdiv : 0 < Real.pi / n := by positivity
  have hdiv1 : Real.pi / n ≤ Real.pi := div_le_self hπ.le hn1
  unfold Erdos504.minimaxAngle
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨⟨by rw [e]; linarith, by rw [e]; linarith⟩, ?_⟩
    intro S hcard
    by_contra hcon
    push Not at hcon
    apply OMA.ES504E.no_cfg (θ := Real.pi / n) (n := n) (S := S)
    refine ⟨hdiv, by field_simp, hn, ?_, hcard⟩
    intro p hp q hq r hr hpq hrq
    by_cases hpr : p = r
    · subst hpr
      have h0 : EuclideanGeometry.angle p q p = 0 :=
        EuclideanGeometry.angle_self_of_ne hpq
      rw [h0]
      have : Real.pi / n ≤ Real.pi / 3 := by
        apply div_le_div_of_nonneg_left hπ.le (by norm_num)
        exact_mod_cast hn
      linarith
    · have h := hcon p hp q hq r hr hpq hrq hpr
      linarith
  · rintro α ⟨⟨h0, h1⟩, hα⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨S, hc, hS⟩ := OMA.ES504E.upper (n := n) (by omega)
      (ε := α - (1 - 1 / (n : ℝ)) * Real.pi) (by linarith)
    have hpos : 0 < S.card := by rw [hc]; positivity
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hpos
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, -, hle⟩ := hα (S.erase x0)
      (by rw [Finset.card_erase_of_mem hx0, hc])
    have := hS x (Finset.mem_of_mem_erase hx) z (Finset.mem_of_mem_erase hz) y
      (Finset.mem_of_mem_erase hy) hxz hyz
    rw [e] at hlt
    linarith
