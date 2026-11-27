-- Adapted from github.com/plby/lean-proofs (commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e), (c) 2026 Boris Alexeev, Apache 2.0 licence, Lean by OpenAI Codex, informal proof by Balister Bollobas Morris Sahasrabudhe Tiba
import FormalConjectures.GreensOpenProblems.«84»
import Mathlib
section
namespace Xq.Bernstein
open scoped BigOperators
def frequency (k : ℕ) : ℂ := (k : ℂ) * Complex.I
noncomputable def ZiS (r : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, a k * frequency k ^ r *
    Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I)
@[simp]
theorem ZlP (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    ZiS 0 s a x =
      ∑ k ∈ s, a k * Complex.exp (((k : ℂ) * (x : ℂ)) * Complex.I) := by
  simp [ZiS]
theorem Zho {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n)
    {w : ℂ} (hw : w ≠ 0) :
    (p.reflect n).eval w⁻¹ * w ^ n = p.eval w := by
  let iw : Invertible w := invertibleOfNonzero hw
  simpa [invOf_eq_inv] using
    (@Polynomial.eval₂_reflect_mul_pow ℂ _ ℂ _ (RingHom.id ℂ) w iw n p hdeg)
theorem Zcv {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖(p.reflect n).eval u‖ ≤ M := by
  let q := p.reflect n
  have hboundary : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzzero
      simp [hzzero] at hz
    have hzinv : ‖z⁻¹‖ = 1 := by simp [hz]
    have hrel := Zho hdeg (w := z⁻¹) (inv_ne_zero hz0)
    have hnorm : ‖q.eval z‖ = ‖p.eval z⁻¹‖ := by
      have hpownorm : ‖(z⁻¹) ^ n‖ = 1 := by
        rw [norm_pow, hzinv, one_pow]
      calc
        ‖q.eval z‖ = ‖q.eval z‖ * 1 := by simp
        _ = ‖q.eval z‖ * ‖(z⁻¹) ^ n‖ := by rw [hpownorm]
        _ = ‖q.eval z * (z⁻¹) ^ n‖ := by rw [norm_mul]
        _ = ‖p.eval z⁻¹‖ := by
          rw [show q.eval z * (z⁻¹) ^ n = p.eval z⁻¹ by simpa [q] using hrel]
    rw [hnorm]
    exact hM z⁻¹ hzinv
  by_cases hueq : ‖u‖ = 1
  · exact hboundary u hueq
  have hult : ‖u‖ < 1 := lt_of_le_of_ne hu hueq
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball
      ((p.reflect n).differentiableOn.diffContOnCl_ball Set.Subset.rfl)
      (C := M)
  · intro z hz
    apply hboundary z
    have hzsphere : z ∈ Metric.sphere (0 : ℂ) 1 :=
      Metric.frontier_ball_subset_sphere hz
    simpa [Metric.mem_sphere, dist_zero_right] using hzsphere
  · exact subset_closure (by simpa [Metric.mem_ball, dist_zero_right] using hult)
theorem ZfT {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖p.eval w‖ ≤ M * ‖w‖ ^ n := by
  have hw0 : w ≠ 0 := by
    apply norm_ne_zero_iff.mp
    linarith
  have hu : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hw)).2 hw
  have hq := Zcv hdeg hM hu
  have hrel := Zho hdeg hw0
  calc
    ‖p.eval w‖ = ‖(p.reflect n).eval w⁻¹‖ * ‖w‖ ^ n := by
      rw [← hrel, norm_mul, norm_pow]
    _ ≤ M * ‖w‖ ^ n :=
      mul_le_mul_of_nonneg_right hq (by positivity)
theorem Zha {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) :
    ‖p.coeff n‖ ≤ M := by
  have hq := Zcv hdeg hM (u := (0 : ℂ)) (by norm_num)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
    Polynomial.revAt_zero] at hq
  exact hq
theorem Zds {p : Polynomial ℂ} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.derivative.eval z‖ ≤ (n : ℝ) * M := by
  by_cases hn : n = 0
  · subst n
    have hpdeg : p.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
    rw [Polynomial.derivative_eq_zero.mpr hpdeg]
    simp
  have hnNat : 0 < n := Nat.pos_of_ne_zero hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  by_contra hbound
  rw [not_le] at hbound
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz
  let β : ℂ := p.derivative.eval z / ((n : ℂ) * z ^ (n - 1))
  have hdenom : (n : ℂ) * z ^ (n - 1) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hn) (pow_ne_zero _ hz0)
  have hβcancel : β * (n : ℂ) * z ^ (n - 1) = p.derivative.eval z := by
    dsimp [β]
    field_simp
  have hβnorm : ‖β‖ = ‖p.derivative.eval z‖ / (n : ℝ) := by
    dsimp [β]
    rw [norm_div, norm_mul, norm_pow, hz, one_pow, mul_one]
    simp
  have hβM : M < ‖β‖ := by
    rw [hβnorm, lt_div_iff₀ hnReal]
    simpa [mul_comm] using hbound
  let P : Polynomial ℂ := p - Polynomial.C β * Polynomial.X ^ n
  have hpcoeff : ‖p.coeff n‖ ≤ M := Zha hdeg hM
  have hcoeffne : p.coeff n ≠ β := by
    intro heq
    rw [heq] at hpcoeff
    exact (not_le_of_gt hβM) hpcoeff
  have hPcoeff : P.coeff n ≠ 0 := by
    simpa [P, Polynomial.coeff_C_mul_X_pow] using sub_ne_zero.mpr hcoeffne
  have hPnatDegreePos : 0 < P.natDegree :=
    hnNat.trans_le (Polynomial.le_natDegree_of_ne_zero hPcoeff)
  have hPdegreePos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hPnatDegreePos
  have hPderiv : P.derivative.eval z = 0 := by
    rw [show P.derivative.eval z = p.derivative.eval z -
        β * (n : ℂ) * z ^ (n - 1) by
      simp only [P, Polynomial.derivative_sub, Polynomial.derivative_C_mul_X_pow,
        Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_X_pow]]
    exact sub_eq_zero.mpr hβcancel.symm
  have hPderiv_ne : P.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    exact hPnatDegreePos.ne'
  have hzDerivRoot : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hPderiv_ne, hPderiv⟩
  have hroots : P.rootSet ℂ ⊆ Metric.ball 0 1 := by
    intro w hwroot
    rw [Polynomial.mem_rootSet] at hwroot
    have hPeval0 : P.eval w = 0 := by
      simpa [Polynomial.coe_aeval_eq_eval] using hwroot.2
    have hPeval : p.eval w = β * w ^ n := by
      apply sub_eq_zero.mp
      simpa [P] using hPeval0
    have hwlt : ‖w‖ < 1 := by
      by_contra hwlt
      have hwge : 1 ≤ ‖w‖ := le_of_not_gt hwlt
      have hout := ZfT hdeg hM hwge
      have hmul : ‖β‖ * ‖w‖ ^ n ≤ M * ‖w‖ ^ n := by
        rw [hPeval, norm_mul, norm_pow] at hout
        exact hout
      have hpow : 0 < ‖w‖ ^ n := pow_pos (lt_of_lt_of_le zero_lt_one hwge) n
      have : ‖β‖ ≤ M := le_of_mul_le_mul_right hmul hpow
      exact (not_le_of_gt hβM) this
    simpa [Metric.mem_ball, dist_zero_right] using hwlt
  have hconvex : convexHull ℝ (P.rootSet ℂ) ⊆ Metric.ball 0 1 :=
    convexHull_min hroots (convex_ball 0 1)
  have hzHull : z ∈ convexHull ℝ (P.rootSet ℂ) :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet hPdegreePos hzDerivRoot
  have hzlt : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hconvex hzHull
  linarith
noncomputable def Zar (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * p.derivative
@[simp]
theorem Ze0 (p : Polynomial ℂ) (z : ℂ) :
    (Zar p).eval z = z * p.derivative.eval z := by
  simp [Zar]
theorem Zhw (p : Polynomial ℂ) :
    (Zar p).natDegree ≤ p.natDegree := by
  by_cases hp : p.natDegree = 0
  · simp [Zar, Polynomial.derivative_of_natDegree_zero hp, hp]
  have hd := Polynomial.natDegree_derivative_le p
  calc
    (Zar p).natDegree ≤
        Polynomial.X.natDegree + p.derivative.natDegree := by
      exact Polynomial.natDegree_mul_le
    _ ≤ 1 + (p.natDegree - 1) := by
      simp only [Polynomial.natDegree_X]
      exact Nat.add_le_add_left hd 1
    _ = p.natDegree := by omega
theorem Ze8 (r : ℕ) (p : Polynomial ℂ) :
    (Zar^[r] p).natDegree ≤ p.natDegree := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact (Zhw _).trans ih
theorem Zci
    {p : Polynomial ℂ} {n : ℕ} (hdeg : p.natDegree ≤ n) {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ M)
    (r : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(Zar^[r] p).eval z‖ ≤ (n : ℝ) ^ r * M := by
  induction r generalizing z with
  | zero => simpa using hM z hz
  | succ r ih =>
      let q := Zar^[r] p
      have hqdeg : q.natDegree ≤ n :=
        (Ze8 r p).trans hdeg
      have hqM : ∀ w : ℂ, ‖w‖ = 1 → ‖q.eval w‖ ≤ (n : ℝ) ^ r * M := by
        intro w hw
        exact ih hw
      have hderiv :=
        Zds hqdeg hqM hz
      rw [Function.iterate_succ_apply']
      calc
        ‖(Zar q).eval z‖ = ‖q.derivative.eval z‖ := by
          rw [Ze0, norm_mul, hz, one_mul]
        _ ≤ (n : ℝ) * ((n : ℝ) ^ r * M) := hderiv
        _ = (n : ℝ) ^ (r + 1) * M := by rw [pow_succ]; ring
end Xq.Bernstein
end
section
namespace Xq.CosineAlgebra
def ZaC (k : ℕ) (A B : ℂ) : ℂ :=
  Complex.I ^ k * A + ((2 : ℂ) * Complex.I) ^ k * B
def ZaZ (k : ℕ) (A B : ℂ) : ℝ :=
  (ZaC k A B).re
@[simp] theorem Zjy (A B : ℂ) :
    ZaZ 0 A B = A.re + B.re := by
  simp [ZaZ, ZaC]
@[simp] theorem ZjT (A B : ℂ) :
    ZaZ 1 A B = -A.im - 2 * B.im := by
  simp [ZaZ, ZaC]
  ring
@[simp] theorem ZjU (A B : ℂ) :
    ZaZ 2 A B = -A.re - 4 * B.re := by
  norm_num [ZaZ, ZaC, pow_succ]
  ring
@[simp] theorem ZiT (A B : ℂ) :
    ZaZ 3 A B = A.im + 8 * B.im := by
  norm_num [ZaZ, ZaC, pow_succ]
theorem ZhP {A B : ℂ} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (h0 : |ZaZ 0 A B| ≤ epsilon)
    (h1 : |ZaZ 1 A B| ≤ epsilon)
    (h2 : |ZaZ 2 A B| ≤ epsilon)
    (h3 : |ZaZ 3 A B| ≤ epsilon) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 9 : ℝ) * epsilon ^ 2 := by
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have hAre : |A.re| ≤ (5 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [Zjy, ZjU] at h0' h2'
    constructor <;> nlinarith
  have hAim : |A.im| ≤ (5 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [ZjT, ZiT] at h1' h3'
    constructor <;> nlinarith
  have hBre : |B.re| ≤ (2 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [Zjy, ZjU] at h0' h2'
    constructor <;> nlinarith
  have hBim : |B.im| ≤ (1 / 3 : ℝ) * epsilon := by
    rw [abs_le]
    simp only [ZjT, ZiT] at h1' h3'
    constructor <;> nlinarith
  have hAreSq : A.re ^ 2 ≤ ((5 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.re) (mul_nonneg (by norm_num) hepsilon)).2 hAre
  have hAimSq : A.im ^ 2 ≤ ((5 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg A.im) (mul_nonneg (by norm_num) hepsilon)).2 hAim
  have hBreSq : B.re ^ 2 ≤ ((2 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.re) (mul_nonneg (by norm_num) hepsilon)).2 hBre
  have hBimSq : B.im ^ 2 ≤ ((1 / 3 : ℝ) * epsilon) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg B.im) (mul_nonneg (by norm_num) hepsilon)).2 hBim
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith
theorem ZfU {A B : ℂ}
    (h : ∀ k : Fin 4, |ZaZ k A B| ≤ 3 / 8) :
    ‖A‖ ^ 2 + ‖B‖ ^ 2 ≤ (55 / 64 : ℝ) := by
  have hbound := ZhP (A := A) (B := B)
    (epsilon := (3 / 8 : ℝ)) (by norm_num)
    (by simpa using h ⟨0, by omega⟩)
    (by simpa using h ⟨1, by omega⟩)
    (by simpa using h ⟨2, by omega⟩)
    (by simpa using h ⟨3, by omega⟩)
  norm_num at hbound ⊢
  exact hbound
theorem Zh9 {A B : ℂ} (D : Fin 4 → ℝ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, |D k - ZaZ k A B| ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |D k| := by
  by_contra hlarge
  push Not at hlarge
  have hleading : ∀ k : Fin 4, |ZaZ k A B| ≤ 3 / 8 := by
    intro k
    calc
      |ZaZ k A B| = |D k - (D k - ZaZ k A B)| := by ring_nf
      _ ≤ |D k| + |D k - ZaZ k A B| := abs_sub _ _
      _ ≤ 3 / 8 := by
        have hk := herror k
        have hk' := hlarge k
        linarith
  have hsmall := ZfU hleading
  rw [henergy] at hsmall
  norm_num at hsmall
theorem Zgi {A B : ℂ} (D : Fin 4 → ℂ)
    (henergy : ‖A‖ ^ 2 + ‖B‖ ^ 2 = 1)
    (herror : ∀ k : Fin 4, ‖D k - ZaC k A B‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| := by
  apply Zh9 (fun k ↦ (D k).re) henergy
  intro k
  have hre :
      |(D k - ZaC k A B).re| ≤
        ‖D k - ZaC k A B‖ :=
    Complex.abs_re_le_norm _
  have hid :
      (D k - ZaC k A B).re =
        (D k).re - ZaZ k A B := by
    rfl
  rw [hid] at hre
  exact hre.trans (herror k)
theorem ZlR {u v alpha beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1) :
    ‖u * alpha‖ ^ 2 + ‖v * beta‖ ^ 2 = 1 := by
  rw [norm_mul, norm_mul, hu, hv, one_mul, one_mul]
  exact henergy
theorem Zfv {u v alpha beta : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (henergy : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1)
    (D : Fin 4 → ℂ)
    (herror : ∀ k : Fin 4,
      ‖D k - ZaC k (u * alpha) (v * beta)‖ ≤ 1 / 8) :
    ∃ k : Fin 4, 1 / 4 ≤ |(D k).re| :=
  Zgi D (ZlR hu hv henergy) herror
end Xq.CosineAlgebra
end
section
namespace Xq
open scoped BigOperators ComplexConjugate
noncomputable section
def Zd (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)
@[simp]
theorem Zbv (theta : ℝ) : ‖Zd theta‖ = 1 := by
  simp [Zd, Complex.norm_exp]
@[simp]
theorem Zk2 (theta : ℝ) : Zd theta ≠ 0 := by
  simp [Zd]
@[simp]
theorem ZlK (theta : ℝ) : Zd (-theta) = (Zd theta)⁻¹ := by
  simp [Zd, Complex.exp_neg]
theorem ZdG (theta : ℝ) (k : ℕ) :
    Zd theta ^ k =
      (Real.cos (k * theta) : ℂ) + (Real.sin (k * theta) : ℂ) * Complex.I := by
  rw [Zd, ← Complex.exp_nat_mul]
  have harg : (k : ℂ) * ((theta : ℂ) * Complex.I) =
      (((k : ℝ) * theta : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, ← Complex.cos_add_sin_I]
  simp
theorem ZiU (theta : ℝ) (k : ℕ) :
    (Zd theta)⁻¹ ^ k =
      (Real.cos (k * theta) : ℂ) - (Real.sin (k * theta) : ℂ) * Complex.I := by
  rw [← ZlK, ZdG]
  simp [Real.cos_neg, Real.sin_neg]
  ring_nf
theorem Ziu (theta : ℝ) (k : ℕ) :
    Zd theta ^ k + (Zd theta)⁻¹ ^ k =
      (2 * Real.cos (k * theta) : ℝ) := by
  rw [ZdG, ZiU]
  push_cast
  ring
theorem Ze9 (theta : ℝ) (k : ℕ) :
    Zd theta ^ k - (Zd theta)⁻¹ ^ k =
      (2 * Real.sin (k * theta) : ℝ) * Complex.I := by
  rw [ZdG, ZiU]
  push_cast
  ring
def Zfa (s : Finset ℕ) (eps : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * Real.cos (k * theta)
def Zd8 (s : Finset ℕ) (eps : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ k ∈ s, eps k * Real.sin (k * theta)
def Zef (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (theta : ℝ) : ℂ :=
  1 +
    ∑ k ∈ C, (epsC k : ℂ) *
      (Zd theta ^ k + (Zd theta)⁻¹ ^ k) +
    ∑ k ∈ Se, (epsE k : ℂ) *
      (Zd theta ^ k - (Zd theta)⁻¹ ^ k) +
    ∑ k ∈ So, (epsO k : ℂ) *
      (Zd theta ^ k - (Zd theta)⁻¹ ^ k)
def Zam (c se so : ℝ) : ℂ :=
  ((1 + 2 * c : ℝ) : ℂ) + ((2 * (se + so) : ℝ) : ℂ) * Complex.I
@[simp]
theorem Zmb (c se so : ℝ) :
    (Zam c se so).re = 1 + 2 * c := by
  simp [Zam]
@[simp]
theorem Zmc (c se so : ℝ) :
    (Zam c se so).im = 2 * (se + so) := by
  simp [Zam]
theorem Zfb (C Se So : Finset ℕ)
    (epsC epsE epsO : ℕ → ℝ) (theta : ℝ) :
    Zef C Se So epsC epsE epsO theta =
      Zam (Zfa C epsC theta)
        (Zd8 Se epsE theta) (Zd8 So epsO theta) := by
  classical
  have hC :
      (∑ k ∈ C, (epsC k : ℂ) *
        (Zd theta ^ k + (Zd theta)⁻¹ ^ k)) =
        ((2 * Zfa C epsC theta : ℝ) : ℂ) := by
    rw [Zfa]
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Ziu]
    push_cast
    ring
  have hE :
      (∑ k ∈ Se, (epsE k : ℂ) *
        (Zd theta ^ k - (Zd theta)⁻¹ ^ k)) =
        ((2 * Zd8 Se epsE theta : ℝ) : ℂ) * Complex.I := by
    rw [Zd8]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Ze9]
    push_cast
    ring
  have hO :
      (∑ k ∈ So, (epsO k : ℂ) *
        (Zd theta ^ k - (Zd theta)⁻¹ ^ k)) =
        ((2 * Zd8 So epsO theta : ℝ) : ℂ) * Complex.I := by
    rw [Zd8]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Ze9]
    push_cast
    ring
  rw [Zef, hC, hE, hO]
  simp only [Zam]
  push_cast
  ring
theorem ZdW (c se so : ℝ) :
    2 * |c| - 1 ≤ ‖Zam c se so‖ := by
  have htriangle : |2 * c| ≤ |1 + 2 * c| + 1 := by
    calc
      |2 * c| = |(1 + 2 * c) - 1| := by ring_nf
      _ ≤ |1 + 2 * c| + |(1 : ℝ)| := abs_sub _ _
      _ = |1 + 2 * c| + 1 := by norm_num
  have hre : |1 + 2 * c| ≤ ‖Zam c se so‖ := by
    simpa using Complex.abs_re_le_norm (Zam c se so)
  rw [abs_mul] at htriangle
  norm_num at htriangle
  linarith
theorem ZdX (c se so : ℝ) :
    2 * (|so| - |se|) ≤ ‖Zam c se so‖ := by
  have htriangle : |so| ≤ |se + so| + |se| := by
    calc
      |so| = |(se + so) - se| := by ring_nf
      _ ≤ |se + so| + |se| := abs_sub _ _
  have him : |2 * (se + so)| ≤ ‖Zam c se so‖ := by
    simpa using Complex.abs_im_le_norm (Zam c se so)
  rw [abs_mul] at him
  norm_num at him
  linarith
theorem ZfI {a c se so : ℝ}
    (hgap : a / 2 + |se| ≤ |so|) :
    a ≤ ‖Zam c se so‖ := by
  have h := ZdX c se so
  linarith
theorem ZjB (c se so A B D : ℝ)
    (hA : |c| ≤ A) (hB : |se| ≤ B) (hD : |so| ≤ D) :
    ‖Zam c se so‖ ≤ 1 + 2 * (A + B + D) := by
  calc
    ‖Zam c se so‖ ≤ |1 + 2 * c| + |2 * (se + so)| := by
      simpa [Zam] using
        Complex.norm_le_abs_re_add_abs_im (Zam c se so)
    _ ≤ (1 + 2 * |c|) + 2 * (|se| + |so|) := by
      calc
        |1 + 2 * c| + |2 * (se + so)| ≤
            (|1| + |2 * c|) + |2| * (|se| + |so|) := by
              gcongr
              · exact abs_add_le _ _
              · rw [abs_mul]
                gcongr
                exact abs_add_le _ _
        _ = (1 + 2 * |c|) + 2 * (|se| + |so|) := by norm_num
    _ ≤ 1 + 2 * (A + B + D) := by linarith
theorem ZdY {n : ℕ} {c se so : ℝ}
    (hn : 1 ≤ n)
    (hc : |c| ≤ Real.sqrt n)
    (hse : |se| ≤ 6 * Real.sqrt n)
    (hso : |so| ≤ 2 ^ 10 * Real.sqrt n) :
    ‖Zam c se so‖ ≤ 2 ^ 12 * Real.sqrt n := by
  have hsqrt : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have h := ZjB c se so
    (Real.sqrt n) (6 * Real.sqrt n) (2 ^ 10 * Real.sqrt n) hc hse hso
  norm_num at h ⊢
  nlinarith
theorem Zdk {n : ℕ} {c se so : ℝ}
    (hse : |se| ≤ 6 * Real.sqrt n)
    (hso : 10 * Real.sqrt n ≤ |so|) :
    8 * Real.sqrt n ≤ ‖Zam c se so‖ := by
  apply ZfI
  linarith
end
end Xq
end
section
namespace Xq
open scoped ComplexConjugate
noncomputable section
mutual
  def rudinShapiroP : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t
  def rudinShapiroQ : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t
end
@[simp] theorem Zl9 : rudinShapiroP 0 = 1 := rfl
@[simp] theorem rudinShapiroQ_zero : rudinShapiroQ 0 = 1 := rfl
@[simp] theorem rudinShapiroP_succ (t : ℕ) :
    rudinShapiroP (t + 1) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl
@[simp] theorem ZcX (t : ℕ) :
    rudinShapiroQ (t + 1) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl
@[simp] theorem ZbF (t : ℕ) (z : ℂ) :
    (rudinShapiroP (t + 1)).eval z =
      (rudinShapiroP t).eval z + z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rudinShapiroP_succ]
@[simp] theorem ZbG (t : ℕ) (z : ℂ) :
    (rudinShapiroQ (t + 1)).eval z =
      (rudinShapiroP t).eval z - z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [ZcX]
lemma ZfV (a b u : ℂ) :
    Complex.normSq (a + u * b) + Complex.normSq (a - u * b) =
      2 * (Complex.normSq a + Complex.normSq u * Complex.normSq b) := by
  rw [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul]
  ring
theorem Zfw (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ^ 2 + ‖(rudinShapiroQ t).eval z‖ ^ 2 =
      (2 ^ (t + 1) : ℝ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [ZbF, ZbG,
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        ZfV]
      have hzu : Complex.normSq (z ^ (2 ^ t)) = 1 := by
        simp [Complex.normSq_eq_norm_sq, norm_pow, hz]
      rw [hzu, one_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ih]
      rw [show (2 ^ (t + 1 + 1) : ℝ) = 2 ^ (t + 1) * 2 by
        rw [pow_succ]]
      ring
theorem ZbR (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have h := Zfw t hz
  have hsq : ‖(rudinShapiroP t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroQ t).eval z‖]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)]
theorem ZeU (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroQ t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have h := Zfw t hz
  have hsq : ‖(rudinShapiroQ t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroP t).eval z‖]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)]
structure ZjC (t : ℕ) : Prop where
  p_sign : ∀ k < 2 ^ t, (rudinShapiroP t).coeff k = 1 ∨
    (rudinShapiroP t).coeff k = -1
  q_sign : ∀ k < 2 ^ t, (rudinShapiroQ t).coeff k = 1 ∨
    (rudinShapiroQ t).coeff k = -1
  p_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroP t).coeff k = 0
  q_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroQ t).coeff k = 0
theorem Zco (t : ℕ) : ZjC t := by
  induction t with
  | zero =>
      constructor
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k ≠ 0 := by omega
        simp [Polynomial.coeff_one, this]
      · intro k hk
        have : k ≠ 0 := by omega
        simp [Polynomial.coeff_one, this]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
        simp [pow_succ, mul_two]
      constructor
      · intro k hk
        rw [rudinShapiroP_succ, Polynomial.coeff_add,
          Polynomial.coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), add_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_add]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          exact ih.q_sign (k - 2 ^ t) hrest
      · intro k hk
        rw [ZcX, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), sub_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_sub]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          rcases ih.q_sign (k - 2 ^ t) hrest with h | h
          · right
            rw [h]
          · left
            rw [h]
            simp
      · intro k hk
        rw [rudinShapiroP_succ, Polynomial.coeff_add,
          Polynomial.coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_add]
        apply ih.q_zero
        omega
      · intro k hk
        rw [ZcX, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_sub]
        rw [ih.q_zero]
        · simp
        · omega
theorem Zac {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP t).coeff k = 1 ∨ (rudinShapiroP t).coeff k = -1 :=
  (Zco t).p_sign k hk
theorem Zad {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ t).coeff k = 1 ∨ (rudinShapiroQ t).coeff k = -1 :=
  (Zco t).q_sign k hk
theorem ZQ {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroP t).coeff k = 0 :=
  (Zco t).p_zero k hk
theorem Zel {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroQ t).coeff k = 0 :=
  (Zco t).q_zero k hk
theorem Zjj (t : ℕ) :
    (rudinShapiroP t).natDegree = 2 ^ t - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply ZQ
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases Zac hlt with h | h <;> simp [h]
theorem Zjk (t : ℕ) :
    (rudinShapiroQ t).natDegree = 2 ^ t - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply Zel
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases Zad hlt with h | h <;> simp [h]
def ZD (p : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range m, Polynomial.C (p.coeff k) * Polynomial.X ^ k
@[simp] theorem ZlS (p : Polynomial ℂ) : ZD p 0 = 0 := by
  simp [ZD]
theorem Zak (p : Polynomial ℂ) (m k : ℕ) :
    (ZD p m).coeff k = if k < m then p.coeff k else 0 := by
  simp [ZD, Polynomial.coeff_C_mul]
theorem Zb3 {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rudinShapiroP_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), add_zero]
theorem Zbr {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [ZcX, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), sub_zero]
@[simp] theorem Zcp (t k : ℕ) :
    (rudinShapiroP (t + 1)).coeff (2 ^ t + k) = (rudinShapiroQ t).coeff k := by
  rw [rudinShapiroP_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), ZQ]
  · simp
  · exact Nat.le_add_right _ _
@[simp] theorem Zhx (t k : ℕ) :
    (rudinShapiroQ (t + 1)).coeff (2 ^ t + k) = -(rudinShapiroQ t).coeff k := by
  rw [ZcX, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), ZQ]
  · simp
  · exact Nat.le_add_right _ _
theorem Zd9 {t m : ℕ} (hm : m ≤ 2 ^ t) :
    ZD (rudinShapiroP (t + 1)) m =
      ZD (rudinShapiroP t) m := by
  ext k
  rw [Zak, Zak]
  split_ifs with hk
  · exact Zb3 (lt_of_lt_of_le hk hm)
  · rfl
theorem Zea {t m : ℕ} (hm : m ≤ 2 ^ t) :
    ZD (rudinShapiroQ (t + 1)) m =
      ZD (rudinShapiroP t) m := by
  ext k
  rw [Zak, Zak]
  split_ifs with hk
  · exact Zbr (lt_of_lt_of_le hk hm)
  · rfl
theorem Zem (t r : ℕ) :
    ZD (rudinShapiroP (t + 1)) (2 ^ t + r) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * ZD (rudinShapiroQ t) r := by
  ext k
  rw [Zak, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    Zak]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), add_zero]
    exact Zb3 hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, ZQ hle, zero_add]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, Zcp]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest]
theorem Zen (t r : ℕ) :
    ZD (rudinShapiroQ (t + 1)) (2 ^ t + r) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * ZD (rudinShapiroQ t) r := by
  ext k
  rw [Zak, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    Zak]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), sub_zero]
    exact Zbr hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, ZQ hle, zero_sub]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, Zhx]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest, neg_zero]
private lemma ZdH
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    Real.sqrt (2 * x) + 5 * Real.sqrt y ≤ 5 * Real.sqrt (x + y) := by
  have h2x : 0 ≤ 2 * x := by positivity
  have hxy : 0 ≤ x + y := by positivity
  have hs2x := Real.sq_sqrt h2x
  have hsy := Real.sq_sqrt hy
  have hsxy := Real.sq_sqrt hxy
  have hn2x := Real.sqrt_nonneg (2 * x)
  have hny := Real.sqrt_nonneg y
  have hnxy := Real.sqrt_nonneg (x + y)
  nlinarith [sq_nonneg (Real.sqrt (2 * x) - Real.sqrt y),
    sq_nonneg (Real.sqrt (2 * x) + 5 * Real.sqrt y - 5 * Real.sqrt (x + y))]
theorem Zeo (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(ZD (rudinShapiroP t) m).eval z‖ ≤ 5 * Real.sqrt m ∧
      ‖(ZD (rudinShapiroQ t) m).eval z‖ ≤ 5 * Real.sqrt m := by
  induction t generalizing m with
  | zero =>
      have hm' : m ≤ 1 := by simpa using hm
      interval_cases m <;> norm_num [ZD, rudinShapiroP, rudinShapiroQ]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by simp [pow_succ, mul_two]
      by_cases hlow : m ≤ 2 ^ t
      · rw [Zd9 hlow,
          Zea hlow]
        exact ⟨(ih m hlow).1, (ih m hlow).1⟩
      · have hAm : 2 ^ t ≤ m := by omega
        let r := m - 2 ^ t
        have hm_eq : 2 ^ t + r = m := by
          dsimp [r]
          omega
        have hr : r ≤ 2 ^ t := by omega
        have hir := ih r hr
        have hfull := ZbR t hz
        have hcastpow : (2 ^ (t + 1) : ℝ) = 2 * (2 ^ t : ℝ) := by
          rw [pow_succ]
          ring
        have hsqrt : Real.sqrt (2 ^ (t + 1) : ℝ) =
            Real.sqrt (2 * (2 ^ t : ℝ)) := congrArg Real.sqrt hcastpow
        have hsqrt_bound : Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) ≤
            5 * Real.sqrt ((2 ^ t : ℝ) + r) := by
          apply ZdH
          · positivity
          · positivity
          · exact_mod_cast hr
        constructor
        · rw [← hm_eq, Zem,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
          calc
            ‖(rudinShapiroP t).eval z + z ^ 2 ^ t *
                (ZD (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (ZD (rudinShapiroQ t) r).eval z‖ :=
              norm_add_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(ZD (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * Real.sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * Real.sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num
        · rw [← hm_eq, Zen,
            Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
          calc
            ‖(rudinShapiroP t).eval z - z ^ 2 ^ t *
                (ZD (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (ZD (rudinShapiroQ t) r).eval z‖ :=
              norm_sub_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(ZD (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * Real.sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * Real.sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num
theorem ZdI (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(ZD (rudinShapiroP t) m).eval z‖ ≤ 5 * Real.sqrt m :=
  (Zeo t m hm hz).1
end
end Xq
end
section
namespace Xq
open scoped BigOperators ComplexConjugate
noncomputable section
def Zt (t : ℕ) : ℕ := 2 ^ (t + 10)
def ZbH (t : ℕ) : ℕ :=
  2 ^ (t + 11) + 2 ^ t - 1
structure ZaM (n t : ℕ) (gamma : ℝ) : Prop where
  t_odd : Odd t
  gamma_pos : 0 < gamma
  gamma_le : gamma ≤ 1 / 2 ^ 40
  equation : gamma * n = ZbH t
def Zby (t : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ t)).image (fun j => Zt t + j) ∪
    (Finset.range (2 ^ t)).image (fun j => 2 * Zt t + j)
def ZlA (t : ℕ) : Finset ℕ :=
  (Zby t).image (fun j => 2 * j)
def ZhO (n t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n) \ Zby t
def ZlB (n t : ℕ) : Finset ℕ :=
  (ZhO n t).image (fun j => 2 * j)
def Zn (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ Zt t * rudinShapiroP t +
    Polynomial.X ^ (2 * Zt t) * rudinShapiroQ t
def Zaq (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ Zt t * rudinShapiroP t +
    Polynomial.X ^ (2 * Zt t) * rudinShapiroP t
def ZF (n t u : ℕ) : Polynomial ℂ :=
  ZD (rudinShapiroP u) (n + 1) - Zaq t
def Zo (t : ℕ) (theta : ℝ) : ℝ :=
  (Zn t).eval (Zd (2 * theta)) |>.re
def ZeB (n t u : ℕ) (theta : ℝ) : ℝ :=
  (ZF n t u).eval (Zd (2 * theta)) |>.im
lemma Zhb (t : ℕ) : Zt t = 2 ^ t * 2 ^ 10 := by
  simp [Zt, pow_add]
lemma ZcY (t : ℕ) : 2 * Zt t = 2 ^ (t + 11) := by
  simp [Zt, pow_succ']
lemma Zbs (t : ℕ) :
    Zt t + 2 ^ t ≤ 2 * Zt t := by
  rw [Zhb]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]
lemma ZjV (t : ℕ) : 2 ^ t ≤ Zt t := by
  rw [Zhb]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]
lemma Zia (t : ℕ) :
    ZbH t + 1 = 2 * Zt t + 2 ^ t := by
  have hp : 0 < 2 ^ (t + 11) := by positivity
  have hone : 1 ≤ 2 ^ (t + 11) := hp
  have hsum : 1 ≤ 2 ^ (t + 11) + 2 ^ t :=
    hone.trans (Nat.le_add_right _ _)
  rw [ZbH, Nat.sub_add_cancel hsum, ZcY]
lemma ZaM.ZlT {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) : gamma ≤ 1 := by
  calc
    gamma ≤ 1 / (2 : ℝ) ^ 40 := h.gamma_le
    _ ≤ 1 := by norm_num
lemma ZaM.Zkv {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) : ZbH t ≤ n := by
  have hnonneg : 0 ≤ (n : ℝ) := by positivity
  have hreal : (ZbH t : ℝ) ≤ n := by
    rw [← h.equation]
    nlinarith [h.ZlT]
  exact_mod_cast hreal
lemma ZaM.Zep {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) : 2 ^ (t + 11) ≤ n := by
  apply le_trans _ h.Zkv
  rw [ZbH]
  have hpos : 0 < 2 ^ t := by positivity
  omega
lemma ZaM.five_le_n {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) : 5 ≤ n := by
  have hp := h.Zep
  have hbase : 2 ^ 11 ≤ 2 ^ (t + 11) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hbase
  omega
lemma ZaM.ZhQ {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) : 2 ^ (t + 5) ≤ n := by
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h.Zep
lemma ZaM.ZlH {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) :
    2 * Zt t + 2 ^ t ≤ n + 1 := by
  rw [← Zia]
  exact Nat.add_le_add_right h.Zkv 1
@[simp] lemma ZaA (t k : ℕ) :
    k ∈ Zby t ↔
      (∃ j < 2 ^ t, k = Zt t + j) ∨
      ∃ j < 2 ^ t, k = 2 * Zt t + j := by
  simp [Zby, eq_comm]
@[simp] lemma ZkM (t k : ℕ) :
    k ∈ ZlA t ↔ ∃ j ∈ Zby t, k = 2 * j := by
  simp [ZlA, eq_comm]
@[simp] lemma Zd7 (n t k : ℕ) :
    k ∈ ZhO n t ↔ 1 ≤ k ∧ k ≤ n ∧ k ∉ Zby t := by
  simp [ZhO, and_assoc]
@[simp] lemma ZkN (n t k : ℕ) :
    k ∈ ZlB n t ↔ ∃ j ∈ ZhO n t, k = 2 * j := by
  simp [ZlB, eq_comm]
lemma ZdJ {n t : ℕ}
    (hblock : 2 * Zt t + 2 ^ t ≤ n + 1) :
    Zby t ⊆ Finset.range (n + 1) := by
  intro k hk
  rw [ZaA] at hk
  simp only [Finset.mem_range]
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have hsep := Zbs t
    omega
  · omega
lemma Zkf (n t : ℕ) : Disjoint (ZlA t) (ZlB n t) := by
  rw [Finset.disjoint_left]
  intro k hkC hkS
  rw [ZkM] at hkC
  rw [ZkN] at hkS
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkS
  have : a = b := by omega
  subst b
  exact (Zd7 n t a).mp hb |>.2.2 ha
lemma ZaK (t j : ℕ) (hj : j < 2 ^ t) :
    (Zn t).coeff (Zt t + j) =
      (rudinShapiroP t).coeff j := by
  rw [Zn, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hnot : ¬2 * Zt t ≤ Zt t + j := by
    have hsep := Zbs t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp
lemma Zav (t j : ℕ) (_ : j < 2 ^ t) :
    (Zn t).coeff (2 * Zt t + j) =
      (rudinShapiroQ t).coeff j := by
  rw [Zn, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hfirst : Zt t ≤ 2 * Zt t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * Zt t + j - Zt t = Zt t + j := by omega
  rw [hsub, ZQ]
  · simp
  · exact (ZjV t).trans (Nat.le_add_right _ _)
lemma Zdi (t k : ℕ)
    (hk : k ∉ Zby t) :
    (Zn t).coeff k = 0 := by
  rw [Zn, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hT : Zt t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * Zt t ≤ k
    · rw [if_pos h2T]
      have hq : 2 ^ t ≤ k - 2 * Zt t := by
        by_contra hq
        have hq' : k - 2 * Zt t < 2 ^ t := Nat.lt_of_not_ge hq
        apply hk
        rw [ZaA]
        right
        exact ⟨k - 2 * Zt t, hq', (Nat.add_sub_of_le h2T).symm⟩
      have hp : 2 ^ t ≤ k - Zt t := by omega
      rw [ZQ hp, Zel hq,
        zero_add]
    · rw [if_neg h2T, add_zero]
      apply ZQ
      by_contra hp
      have hp' : k - Zt t < 2 ^ t := Nat.lt_of_not_ge hp
      apply hk
      rw [ZaA]
      left
      exact ⟨k - Zt t, hp', (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * Zt t ≤ k := by omega
    rw [if_neg h2T, zero_add]
theorem Zax (t : ℕ) :
    (Zn t).support = Zby t := by
  ext k
  simp only [Polynomial.mem_support_iff, ne_eq, ZaA]
  constructor
  · intro hk
    by_contra hout
    apply hk
    apply Zdi t k
    rwa [ZaA]
  · intro hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [ZaK t j hj]
      rcases Zac hj with h | h <;>
        rw [h] <;> norm_num
    · rw [Zav t j hj]
      rcases Zad hj with h | h <;>
        rw [h] <;> norm_num
lemma ZeC (t j : ℕ) (hj : j < 2 ^ t) :
    (Zaq t).coeff (Zt t + j) =
      (rudinShapiroP t).coeff j := by
  rw [Zaq, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hnot : ¬2 * Zt t ≤ Zt t + j := by
    have hsep := Zbs t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp
lemma Zeq (t j : ℕ) (_ : j < 2 ^ t) :
    (Zaq t).coeff (2 * Zt t + j) =
      (rudinShapiroP t).coeff j := by
  rw [Zaq, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hfirst : Zt t ≤ 2 * Zt t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * Zt t + j - Zt t = Zt t + j := by omega
  rw [hsub, ZQ]
  · simp
  · exact (ZjV t).trans (Nat.le_add_right _ _)
lemma ZaG (t k : ℕ)
    (hk : k ∉ Zby t) :
    (Zaq t).coeff k = 0 := by
  rw [Zaq, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hT : Zt t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * Zt t ≤ k
    · rw [if_pos h2T]
      have hsecond : 2 ^ t ≤ k - 2 * Zt t := by
        by_contra hsecond
        apply hk
        rw [ZaA]
        right
        exact ⟨k - 2 * Zt t, Nat.lt_of_not_ge hsecond,
          (Nat.add_sub_of_le h2T).symm⟩
      have hfirst : 2 ^ t ≤ k - Zt t := by omega
      rw [ZQ hfirst,
        ZQ hsecond, zero_add]
    · rw [if_neg h2T, add_zero]
      apply ZQ
      by_contra hfirst
      apply hk
      rw [ZaA]
      left
      exact ⟨k - Zt t, Nat.lt_of_not_ge hfirst,
        (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * Zt t ≤ k := by omega
    rw [if_neg h2T, zero_add]
lemma Zbp {a b k : ℕ} (hab : a ≤ b) (hk : k < 2 ^ a) :
    (rudinShapiroP b).coeff k = (rudinShapiroP a).coeff k := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hpow : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
      rw [Zb3 (hk.trans_le hpow), ih]
lemma ZhR (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 10)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 9) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 10 = (t + 9) + 1 by omega,
    Zbr (hj.trans_le hpow)]
  exact Zbp (by omega) hj
lemma ZgO (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 11)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 10) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 11 = (t + 10) + 1 by omega,
    Zbr (hj.trans_le hpow)]
  exact Zbp (by omega) hj
lemma Zfc {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (Zt t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : Zt t + j < 2 ^ (t + 11) := by
    rw [← ZcY]
    have hsep := Zbs t
    omega
  calc
    (rudinShapiroP u).coeff (Zt t + j) =
        (rudinShapiroP (t + 11)).coeff (Zt t + j) :=
      Zbp (by omega) hindex
    _ = (rudinShapiroQ (t + 10)).coeff j := by
      simpa [Zt] using Zcp (t + 10) j
    _ = (rudinShapiroP t).coeff j := ZhR t j hj
lemma Ze1 {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (2 * Zt t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : 2 * Zt t + j < 2 ^ (t + 12) := by
    have hsmall := ZjV t
    rw [show 2 ^ (t + 12) = 2 * Zt t + 2 * Zt t by
      simp [Zt, pow_add]
      ring]
    omega
  calc
    (rudinShapiroP u).coeff (2 * Zt t + j) =
        (rudinShapiroP (t + 12)).coeff (2 * Zt t + j) :=
      Zbp hu hindex
    _ = (rudinShapiroQ (t + 11)).coeff j := by
      simpa [ZcY] using Zcp (t + 11) j
    _ = (rudinShapiroP t).coeff j := ZgO t j hj
lemma Zfx {t u k : ℕ}
    (hu : t + 12 ≤ u) (hk : k ∈ Zby t) :
    (rudinShapiroP u).coeff k = (Zaq t).coeff k := by
  rw [ZaA] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [Zfc hu hj,
      ZeC t j hj]
  · rw [Ze1 hu hj,
      Zeq t j hj]
lemma ZdK {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * Zt t + 2 ^ t ≤ n + 1)
    (hk : k ∈ Zby t) :
    (ZF n t u).coeff k = 0 := by
  have hkrange := ZdJ hblock hk
  simp only [Finset.mem_range] at hkrange
  rw [ZF, Polynomial.coeff_sub,
    Zak, if_pos hkrange,
    Zfx hu hk, sub_self]
lemma Zdl {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k < n + 1)
    (hkC : k ∉ Zby t) :
    (ZF n t u).coeff k = 1 ∨
      (ZF n t u).coeff k = -1 := by
  rw [ZF, Polynomial.coeff_sub,
    Zak, if_pos hk,
    ZaG t k hkC, sub_zero]
  exact Zac (hk.trans_le hprefix)
theorem ZaD {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ ZhO n t) :
    (ZF n t u).coeff k = 1 ∨
      (ZF n t u).coeff k = -1 := by
  rw [Zd7] at hk
  exact Zdl hprefix (by omega) hk.2.2
theorem Zda {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * Zt t + 2 ^ t ≤ n + 1)
    (hk : k ∈ Zby t) :
    (ZF n t u).coeff k = 0 :=
  ZdK hu hblock hk
theorem ZkO (t : ℕ) (theta : ℝ) :
    Zo t theta =
      ((Zd (2 * theta)) ^ Zt t *
          (rudinShapiroP t).eval (Zd (2 * theta)) +
        (Zd (2 * theta)) ^ (2 * Zt t) *
          (rudinShapiroQ t).eval (Zd (2 * theta))).re := by
  simp [Zo, Zn]
theorem Zl2 (n t u : ℕ) (theta : ℝ) :
    ZeB n t u theta =
      ((ZD (rudinShapiroP u) (n + 1)).eval
          (Zd (2 * theta)) -
        (Zd (2 * theta)) ^ Zt t *
          (rudinShapiroP t).eval (Zd (2 * theta)) -
        (Zd (2 * theta)) ^ (2 * Zt t) *
          (rudinShapiroP t).eval (Zd (2 * theta))).im := by
  simp [ZeB, ZF, Zaq]
  ring
private lemma Zhy {n t : ℕ}
    (hscale : 2 ^ (t + 3) ≤ n) :
    2 * Real.sqrt (2 ^ (t + 1) : ℝ) ≤ Real.sqrt n := by
  have hcast : (2 ^ (t + 3) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 3) : ℝ) = 4 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 3 = (t + 1) + 2 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := Real.sq_sqrt hA
  have hsn := Real.sq_sqrt hn
  have hsAn := Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := Real.sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith
theorem ZjD (n t : ℕ)
    (hscale : 2 ^ (t + 3) ≤ n) (theta : ℝ) :
    |Zo t theta| ≤ Real.sqrt n := by
  let z := Zd (2 * theta)
  have hz : ‖z‖ = 1 := Zbv _
  have hP := ZbR t hz
  have hQ := ZeU t hz
  rw [ZkO]
  change |(z ^ Zt t * (rudinShapiroP t).eval z +
      z ^ (2 * Zt t) * (rudinShapiroQ t).eval z).re| ≤ _
  calc
    |(z ^ Zt t * (rudinShapiroP t).eval z +
        z ^ (2 * Zt t) * (rudinShapiroQ t).eval z).re| ≤
        ‖z ^ Zt t * (rudinShapiroP t).eval z +
          z ^ (2 * Zt t) * (rudinShapiroQ t).eval z‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖z ^ Zt t * (rudinShapiroP t).eval z‖ +
        ‖z ^ (2 * Zt t) * (rudinShapiroQ t).eval z‖ := norm_add_le _ _
    _ = ‖(rudinShapiroP t).eval z‖ + ‖(rudinShapiroQ t).eval z‖ := by
      simp [norm_pow, hz]
    _ ≤ 2 * Real.sqrt (2 ^ (t + 1) : ℝ) := by linarith
    _ ≤ Real.sqrt n := Zhy hscale
private lemma Zgu {n : ℕ} (hn : 5 ≤ n) :
    Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (11 / 10 : ℝ) * Real.sqrt n := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hs0 := Real.sq_sqrt hn0
  have hs1 := Real.sq_sqrt hn1
  have hs0n := Real.sqrt_nonneg (n : ℝ)
  have hs1n := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
  have hncast : (5 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num only [Nat.cast_add, Nat.cast_one] at hs1
  by_contra hnot
  have hlt : ((11 / 10 : ℝ) * Real.sqrt n) ^ 2 <
      Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hs1n).2 (lt_of_not_ge hnot)
  norm_num only [Nat.cast_add, Nat.cast_one] at hlt
  have hlt' : (121 / 100 : ℝ) * n < n + 1 := by
    nlinarith [hlt, hs0, hs1]
  nlinarith
private lemma ZfW {n t : ℕ}
    (hscale : 2 ^ (t + 5) ≤ n) :
    2 * Real.sqrt (2 ^ (t + 1) : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt n := by
  have hcast : (2 ^ (t + 5) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 5) : ℝ) = 16 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 5 = (t + 1) + 4 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := Real.sq_sqrt hA
  have hsn := Real.sq_sqrt hn
  have hsAn := Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := Real.sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith
theorem ZiV (n t u : ℕ)
    (hprefix : n + 1 ≤ 2 ^ u) (hn : 5 ≤ n)
    (hscale : 2 ^ (t + 5) ≤ n) (theta : ℝ) :
    |ZeB n t u theta| ≤ 6 * Real.sqrt n := by
  let z := Zd (2 * theta)
  have hz : ‖z‖ = 1 := Zbv _
  have hpref := ZdI u (n + 1) hprefix hz
  have hP := ZbR t hz
  rw [Zl2]
  change |((ZD (rudinShapiroP u) (n + 1)).eval z -
      z ^ Zt t * (rudinShapiroP t).eval z -
      z ^ (2 * Zt t) * (rudinShapiroP t).eval z).im| ≤ _
  calc
    |((ZD (rudinShapiroP u) (n + 1)).eval z -
        z ^ Zt t * (rudinShapiroP t).eval z -
        z ^ (2 * Zt t) * (rudinShapiroP t).eval z).im| ≤
        ‖(ZD (rudinShapiroP u) (n + 1)).eval z -
          z ^ Zt t * (rudinShapiroP t).eval z -
          z ^ (2 * Zt t) * (rudinShapiroP t).eval z‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖(ZD (rudinShapiroP u) (n + 1)).eval z‖ +
          ‖z ^ Zt t * (rudinShapiroP t).eval z‖ +
          ‖z ^ (2 * Zt t) * (rudinShapiroP t).eval z‖ := by
      calc
        _ ≤ ‖(ZD (rudinShapiroP u) (n + 1)).eval z -
              z ^ Zt t * (rudinShapiroP t).eval z‖ +
              ‖z ^ (2 * Zt t) * (rudinShapiroP t).eval z‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖(ZD (rudinShapiroP u) (n + 1)).eval z‖ +
          2 * ‖(rudinShapiroP t).eval z‖ := by
      simp [norm_pow, hz]
      ring
    _ ≤ 5 * Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
      exact add_le_add hpref (mul_le_mul_of_nonneg_left hP (by norm_num))
    _ ≤ 5 * ((11 / 10 : ℝ) * Real.sqrt n) +
          (1 / 2 : ℝ) * Real.sqrt n := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Zgu hn) (by norm_num))
        (ZfW hscale)
    _ = 6 * Real.sqrt n := by ring
theorem Zfd {n t : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) (theta : ℝ) :
    |Zo t theta| ≤ Real.sqrt n := by
  apply ZjD n t
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    h.ZhQ
theorem ZeD {n t u : ℕ} {gamma : ℝ}
    (h : ZaM n t gamma) (hprefix : n + 1 ≤ 2 ^ u)
    (theta : ℝ) :
    |ZeB n t u theta| ≤ 6 * Real.sqrt n :=
  ZiV n t u hprefix h.five_le_n
    h.ZhQ theta
end
end Xq
end
section
namespace Xq.Interpolation
open scoped BigOperators
theorem ZdZ :
    ∀ (k : ℕ) (g : ℝ → ℝ) (x : Fin (k + 1) → ℝ),
      ContDiff ℝ k g → StrictMono x → (∀ i, g (x i) = 0) →
      ∃ z ∈ Set.Icc (x 0) (x (Fin.last k)), iteratedDeriv k g z = 0 := by
  intro k
  induction k with
  | zero =>
      intro g x _hg _hx hzero
      refine ⟨x 0, ⟨le_rfl, ?_⟩, ?_⟩
      · simp
      · simpa using hzero 0
  | succ k ih =>
      intro g x hg hx hzero
      have hrolle (i : Fin (k + 1)) :
          ∃ c ∈ Set.Ioo (x i.castSucc) (x i.succ), deriv g c = 0 := by
        apply exists_deriv_eq_zero
        · exact hx Fin.castSucc_lt_succ
        · exact hg.continuous.continuousOn
        · rw [hzero i.castSucc, hzero i.succ]
      let c : Fin (k + 1) → ℝ := fun i ↦ Classical.choose (hrolle i)
      have hc_mem (i : Fin (k + 1)) :
          c i ∈ Set.Ioo (x i.castSucc) (x i.succ) :=
        (Classical.choose_spec (hrolle i)).1
      have hc_zero (i : Fin (k + 1)) : deriv g (c i) = 0 :=
        (Classical.choose_spec (hrolle i)).2
      have hc_mono : StrictMono c := by
        intro i j hij
        have hij' : i.succ ≤ j.castSucc := by
          apply Fin.mk_le_mk.mpr
          omega
        exact (hc_mem i).2.trans ((hx.monotone hij').trans_lt (hc_mem j).1)
      have hderiv : ContDiff ℝ k (deriv g) := hg.deriv'
      obtain ⟨z, hz, hz0⟩ := ih (deriv g) c hderiv hc_mono hc_zero
      refine ⟨z, ⟨?_, ?_⟩, ?_⟩
      · exact (hc_mem 0).1.le.trans hz.1
      · exact hz.2.trans (hc_mem (Fin.last k)).2.le
      · simpa only [iteratedDeriv_succ'] using hz0
noncomputable def ZI (k : ℕ) (y : Fin (k + 1) → ℝ)
    (j : Fin (k + 1)) : ℝ :=
  (k.factorial : ℝ) /
    ∏ i ∈ (Finset.univ.erase j), (y j - y i)
theorem Zer (k : ℕ)
    (y : Fin (k + 1) → ℝ) (v : Fin (k + 1) → ℝ) (hy : Function.Injective y)
    (x : ℝ) :
    ((Polynomial.derivative^[k])
      (Lagrange.interpolate Finset.univ y v)).eval x =
      ∑ i, ZI k y i * v i := by
  rw [Lagrange.iterate_derivative_interpolate v hy.injOn (by simp)]
  simp [ZI, Finset.mul_sum, div_eq_mul_inv, mul_comm]
  simp [Polynomial.eval_finsetSum, mul_left_comm]
theorem Zhc (k : ℕ) (P : Polynomial ℝ) (x : ℝ) :
    iteratedDeriv k (fun t ↦ P.eval t) x =
      ((Polynomial.derivative^[k]) P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hfun : deriv (fun t ↦ P.eval t) = fun t ↦ P.derivative.eval t := by
        funext t
        exact P.deriv
      rw [hfun, ih]
      rw [Function.iterate_succ_apply']
      exact congrArg (Polynomial.eval x)
        ((Function.Commute.self_iterate
          (Polynomial.derivative : Polynomial ℝ → Polynomial ℝ) k) P).symm
theorem Zgv (k : ℕ) (f : ℝ → ℝ)
    (y : Fin (k + 1) → ℝ) (x Delta M : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (_hDelta : 0 ≤ Delta) (hM : 0 ≤ M)
    (hyx : ∀ i, |y i - x| ≤ Delta)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ M) :
    |iteratedDeriv k f x -
      ∑ i, ZI k y i * f (y i)| ≤ Delta * M := by
  let P : Polynomial ℝ := Lagrange.interpolate Finset.univ y (fun i ↦ f (y i))
  let g : ℝ → ℝ := fun t ↦ f t - P.eval t
  have hP : ContDiff ℝ (k + 1) (fun t ↦ P.eval t) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial n a =>
        simp only [Polynomial.eval_monomial]
        fun_prop
  have hg : ContDiff ℝ k g := by
    apply ContDiff.sub (hf.of_le (by norm_num)) (hP.of_le (by norm_num))
  have hzero : ∀ i, g (y i) = 0 := by
    intro i
    have hPi : P.eval (y i) = f (y i) := by
      dsimp only [P]
      exact Lagrange.eval_interpolate_at_node _ hy.injective.injOn (Finset.mem_univ i)
    dsimp only [g]
    rw [hPi, sub_self]
  obtain ⟨z, hz, hz0⟩ :=
    ZdZ k g y hg hy hzero
  have hPAt : ContDiffAt ℝ k (fun t ↦ P.eval t) z := (hP.of_le (by norm_num)).contDiffAt
  have hfAt : ContDiffAt ℝ k f z := (hf.of_le (by norm_num)).contDiffAt
  have hzEq : iteratedDeriv k f z =
      ∑ i, ZI k y i * f (y i) := by
    change iteratedDeriv k (f - fun t ↦ P.eval t) z = 0 at hz0
    rw [iteratedDeriv_sub hfAt hPAt, Zhc,
      Zer k y (fun i ↦ f (y i)) hy.injective z] at hz0
    linarith
  have hzDist : |z - x| ≤ Delta := by
    have hleft := (abs_le.mp (hyx (0 : Fin (k + 1)))).1
    have hright := (abs_le.mp (hyx (Fin.last k))).2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  have hmean :
      |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := iteratedDeriv k f) (x := z) (y := x)
      (fun t _ ↦ hdiff.differentiableAt)
      (fun t _ ↦ by
        rw [← iteratedDeriv_succ]
        simpa only [Real.norm_eq_abs] using hderiv t)
      convex_univ (Set.mem_univ z) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using h
  rw [← hzEq]
  calc
    |iteratedDeriv k f x - iteratedDeriv k f z| ≤ M * |x - z| := hmean
    _ = M * |z - x| := by rw [abs_sub_comm]
    _ ≤ M * Delta := mul_le_mul_of_nonneg_left hzDist hM
    _ = Delta * M := mul_comm _ _
theorem Zhz (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    eta ^ k ≤ |∏ i ∈ (Finset.univ.erase j), (y j - y i)| := by
  classical
  rw [Finset.abs_prod]
  have hcard : (Finset.univ.erase j).card = k := by simp
  calc
    eta ^ k = eta ^ (Finset.univ.erase j).card := congrArg (eta ^ ·) hcard.symm
    _ = ∏ _i ∈ (Finset.univ.erase j), eta := by simp
    _ ≤ ∏ i ∈ (Finset.univ.erase j), |y j - y i| := by
      apply Finset.prod_le_prod (fun _i _hi ↦ heta)
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simpa only [abs_sub_comm] using hsep i j hij
theorem Zgw (k : ℕ) (y : Fin (k + 1) → ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (j : Fin (k + 1)) :
    |ZI k y j| ≤ (k.factorial : ℝ) / eta ^ k := by
  rw [ZI, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  have hprod := Zhz k y eta heta.le hsep j
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
theorem Zkz {n : ℕ} (u : Fin n → ℝ) (A : ℝ)
    (hA : ∀ i, |u i| ≤ A) :
    |∑ i, u i| ≤ n * A := by
  calc
    |∑ i, u i| ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, A := Finset.sum_le_sum fun i _ ↦ hA i
    _ = n * A := by simp [nsmul_eq_mul]
theorem ZkA (k : ℕ) (y : Fin (k + 1) → ℝ) (eta epsilon : ℝ)
    (heta : 0 < eta) (_hepsilon : 0 ≤ epsilon)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ epsilon) :
    |∑ i, ZI k y i * v i| ≤
      (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) := by
  have h := Zkz
    (fun i ↦ ZI k y i * v i)
    ((k.factorial : ℝ) / eta ^ k * epsilon) (fun i ↦ by
      rw [abs_mul]
      exact mul_le_mul
        (Zgw k y eta heta hsep i) (hv i)
        (abs_nonneg _) (by positivity))
  simpa [Nat.cast_add, Nat.cast_one] using h
theorem Zhd (k : ℕ) (y : Fin (k + 1) → ℝ)
    (eta epsilon remainder d : ℝ)
    (heta : 0 < eta) (hepsilon : 0 ≤ epsilon) (_hremainder : 0 ≤ remainder)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ epsilon)
    (happrox : |d - ∑ i, ZI k y i * v i| ≤ remainder) :
    |d| ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) := by
  have hsum := ZkA k y eta epsilon heta hepsilon hsep v hv
  calc
    |d| = |(d - ∑ i, ZI k y i * v i) +
        ∑ i, ZI k y i * v i| := by ring_nf
    _ ≤ |d - ∑ i, ZI k y i * v i| +
        |∑ i, ZI k y i * v i| := abs_add_le _ _
    _ ≤ remainder + (k + 1) * ((k.factorial : ℝ) / eta ^ k * epsilon) :=
      add_le_add happrox hsum
theorem Zk3 (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (y : Fin (k + 1) → ℝ) (eta d : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (v : Fin (k + 1) → ℝ) (hv : ∀ i, |v i| ≤ eta ^ 3 / 128)
    (happrox : |d - ∑ i, ZI k y i * v i| ≤ 126 * eta) :
    |d| < 1 / 4 := by
  have hetaPow : 0 ≤ eta ^ 3 / 128 := by positivity
  have hbound := Zhd k y eta (eta ^ 3 / 128)
    (126 * eta) d heta hetaPow (by positivity) hsep v hv happrox
  have hetaOne : eta < 1 := by
    calc
      eta < (1 : ℝ) / 2048 := hetaSmall
      _ < 1 := by norm_num
  have hetaLeOne : eta ≤ 1 := hetaOne.le
  have hetaSqLeOne : eta ^ 2 ≤ 1 := by nlinarith [sq_nonneg eta]
  have hinterp :
      (k + 1 : ℝ) * ((k.factorial : ℝ) / eta ^ k * (eta ^ 3 / 128)) ≤ 3 / 16 := by
    interval_cases k <;> norm_num at hk₁ hk₃ ⊢
    · field_simp [ne_of_gt heta]
      nlinarith [sq_nonneg eta]
    · field_simp [ne_of_gt heta]
      nlinarith
    · field_simp [ne_of_gt heta]
      norm_num
  have hrem : 126 * eta < 1 / 16 := by
    norm_num at hetaSmall ⊢
    nlinarith
  nlinarith
theorem Zib (k : ℕ) (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (f : ℝ → ℝ) (y : Fin (k + 1) → ℝ) (x eta : ℝ)
    (hf : ContDiff ℝ (k + 1) f) (hy : StrictMono y)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hsep : ∀ i j, i ≠ j → eta ≤ |y i - y j|)
    (hyx : ∀ i, |y i - x| ≤ 7 * eta)
    (hvalue : ∀ i, |f (y i)| ≤ eta ^ 3 / 128)
    (hderiv : ∀ t, |iteratedDeriv (k + 1) f t| ≤ 18) :
    |iteratedDeriv k f x| < 1 / 4 := by
  have happrox' := Zgv k f y x (7 * eta) 18 hf hy
    (by positivity) (by norm_num) hyx hderiv
  have happrox :
      |iteratedDeriv k f x -
        ∑ i, ZI k y i * f (y i)| ≤ 126 * eta := by
    convert happrox' using 1
    ring
  exact Zk3 k hk₁ hk₃ y eta (iteratedDeriv k f x) heta hetaSmall
    hsep (fun i ↦ f (y i)) hvalue happrox
end Xq.Interpolation
end
section
namespace Xq.Intervals
open Set
noncomputable def Zz (n k : ℕ) : ℝ := (k : ℝ) * Real.pi / n
noncomputable def Zln (n k : ℕ) : Set ℝ :=
  Icc (Zz n k) (Zz n (k + 1))
def ZiW (start length : ℕ) : Finset ℕ :=
  (Finset.range length).image (start + ·)
@[simp] theorem Zmj {start length i : ℕ} :
    i ∈ ZiW start length ↔ start ≤ i ∧ i < start + length := by
  constructor
  · simp only [ZiW, Finset.mem_image, Finset.mem_range]
    rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hsi, hi⟩
    simp only [ZiW, Finset.mem_image, Finset.mem_range]
    exact ⟨i - start, by omega, by omega⟩
@[simp] theorem Zmf (start length : ℕ) :
    (ZiW start length).card = length := by
  rw [ZiW, Finset.card_image_of_injective]
  · simp
  · exact fun _ _ h ↦ Nat.add_left_cancel h
theorem Ziw (n : ℕ) : Zz n 0 = 0 := by
  simp [Zz]
theorem ZlL (n k l : ℕ) :
    Zz n (k + l) = Zz n k + Zz n l := by
  simp only [Zz, Nat.cast_add]
  ring
theorem Zkw (n k : ℕ) :
    Zz n (k + 1) = Zz n k + Real.pi / n := by
  rw [ZlL]
  simp [Zz]
theorem Zcj {n : ℕ} (hn : 0 < n) :
    StrictMono (Zz n) := by
  intro i j hij
  simp only [Zz]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hn'
  simpa [mul_div_assoc] using (mul_lt_mul_of_pos_right (by exact_mod_cast hij) hpi)
theorem ZbE {n : ℕ} (hn : 0 < n) :
    Monotone (Zz n) := (Zcj hn).monotone
def Zlr (I : ℝ × ℝ) : ℝ × ℝ := (-I.2, -I.1)
noncomputable def ZjW (I : ℝ × ℝ) : ℝ × ℝ :=
  (Real.pi - I.2, Real.pi - I.1)
noncomputable def Zix (I : ℝ × ℝ) : ℝ × ℝ :=
  (Real.pi + I.1, Real.pi + I.2)
@[simp] theorem Zl3 {a b x : ℝ} :
    x ∈ Icc a b ↔ -x ∈ Icc (Zlr (a, b)).1 (Zlr (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔ (-b ≤ -x ∧ -x ≤ -a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
@[simp] theorem ZlM {a b x : ℝ} :
    x ∈ Icc a b ↔
      Real.pi - x ∈ Icc (ZjW (a, b)).1 (ZjW (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔
    (Real.pi - b ≤ Real.pi - x ∧ Real.pi - x ≤ Real.pi - a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
@[simp] theorem ZlQ {a b x : ℝ} :
    x ∈ Icc a b ↔
      Real.pi + x ∈ Icc (Zix (a, b)).1 (Zix (a, b)).2 := by
  simp [Zix]
def ZkP (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1))
def Zls (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ bad i ∧ (i = 0 ∨ ¬ bad (i - 1))
@[simp] theorem Zmd {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ ZkP N bad ↔ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1)) := by
  simp [ZkP]
  omega
@[simp] theorem Zjl {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ Zls N bad ↔
      i < N ∧ bad i ∧ (i = 0 ∨ ¬ bad (i - 1)) := by
  simp [Zls]
def Zay (N : ℕ) (bad : ℕ → Prop) (a b : ℕ) : Prop :=
  a ≤ b ∧ b < N ∧
    (∀ i ∈ Finset.range N, a ≤ i → i ≤ b → bad i) ∧
    (a = 0 ∨ ¬ bad (a - 1)) ∧
    (b + 1 = N ∨ ¬ bad (b + 1))
instance Zlo (N : ℕ) (bad : ℕ → Prop)
    [DecidablePred bad] (a b : ℕ) : Decidable (Zay N bad a b) := by
  unfold Zay
  infer_instance
def Ziy (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun I ↦
    Zay N bad I.1 I.2
theorem Zay.Zkx {N a b c d : ℕ} {bad : ℕ → Prop}
    (h₁ : Zay N bad a b) (h₂ : Zay N bad c d)
    (hac : a = c) : (a, b) = (c, d) := by
  subst c
  congr 1
  apply le_antisymm
  · by_contra hnot
    have hdb : d < b := Nat.lt_of_not_ge hnot
    have hbad : bad (d + 1) :=
      h₁.2.2.1 (d + 1) (Finset.mem_range.2 (lt_of_le_of_lt hdb h₁.2.1))
        (Nat.le_succ_of_le h₂.1) hdb
    rcases h₂.2.2.2.2 with heq | hnbad
    · have hNb : N ≤ b := by omega
      exact (Nat.not_le_of_gt h₁.2.1) hNb
    · exact hnbad hbad
  · by_contra hnot
    have hbd : b < d := Nat.lt_of_not_ge hnot
    have hbad : bad (b + 1) :=
      h₂.2.2.1 (b + 1) (Finset.mem_range.2 (lt_of_le_of_lt hbd h₂.2.1))
        (Nat.le_succ_of_le h₁.1) hbd
    rcases h₁.2.2.2.2 with heq | hnbad
    · have hNd : N ≤ d := by omega
      exact (Nat.not_le_of_gt h₂.2.1) hNd
    · exact hnbad hbad
@[simp] theorem Zin {N a b : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    (a, b) ∈ Ziy N bad ↔ Zay N bad a b := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (h.1.trans_lt h.2.1), Finset.mem_range.mpr h.2.1⟩, h⟩
theorem ZkQ {N i : ℕ} {bad : ℕ → Prop} [DecidablePred bad]
    (hiN : i < N) (hi : bad i) :
    ∃ a, a ≤ i ∧ a ∈ Zls N bad ∧
      ∀ j, a ≤ j → j ≤ i → bad j := by
  induction i with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · rw [Zjl]
        exact ⟨hiN, hi, Or.inl rfl⟩
      · intro j hj₀ hj₁
        have : j = 0 := by omega
        simpa [this] using hi
  | succ i ih =>
      by_cases hprev : bad i
      · obtain ⟨a, hai, hastart, harun⟩ := ih (by omega) hprev
        refine ⟨a, by omega, hastart, ?_⟩
        intro j haj hji
        by_cases hj : j = i + 1
        · simpa [hj] using hi
        · exact harun j haj (by omega)
      · refine ⟨i + 1, le_rfl, ?_, ?_⟩
        · rw [Zjl]
          refine ⟨hiN, hi, Or.inr ?_⟩
          change ¬ bad i
          exact hprev
        · intro j hj₀ hj₁
          have : j = i + 1 := by omega
          simpa [this] using hi
theorem Zgx {N i : ℕ} {bad : ℕ → Prop}
    (hiN : i < N) (hi : bad i) :
    ∃ a b, Zay N bad a b ∧ a ≤ i ∧ i ≤ b := by
  classical
  obtain ⟨a, hai, hastart, harun⟩ := ZkQ hiN hi
  let P : ℕ → Prop := fun b ↦
    b < N ∧ ∀ j ∈ Finset.range N, a ≤ j → j ≤ b → bad j
  let _ : DecidablePred P := fun _ ↦ inferInstance
  have hi_bound : i ≤ N - 1 := by omega
  have hPi : P i := by
    refine ⟨hiN, ?_⟩
    intro j hjN haj hji
    exact harun j haj hji
  let b := Nat.findGreatest P (N - 1)
  have hib : i ≤ b := by
    exact Nat.le_findGreatest hi_bound hPi
  have hPb : P b := by
    exact Nat.findGreatest_spec hi_bound hPi
  have hright : b + 1 = N ∨ ¬ bad (b + 1) := by
    by_cases heq : b + 1 = N
    · exact Or.inl heq
    · right
      intro hbad
      have hsuccN : b + 1 < N := by omega
      have hsuccBound : b + 1 ≤ N - 1 := by omega
      have hPsucc : P (b + 1) := by
        refine ⟨hsuccN, ?_⟩
        intro j hjN haj hjb
        by_cases hj : j = b + 1
        · simpa [hj] using hbad
        · exact hPb.2 j hjN haj (by omega)
      exact (Nat.findGreatest_is_greatest (P := P) (n := N - 1)
        (k := b + 1) (Nat.lt_succ_self b) hsuccBound) hPsucc
  refine ⟨a, b, ?_, hai, hib⟩
  refine ⟨hai.trans hib, hPb.1, hPb.2, ?_, hright⟩
  exact (Zjl.mp hastart).2.2
theorem Zfe {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ I ∈ Ziy N bad, I.1 ≤ i ∧ i ≤ I.2 := by
  obtain ⟨a, b, hab, hai, hib⟩ := Zgx hiN hi
  exact ⟨(a, b), Zin.mpr hab, hai, hib⟩
theorem Zkg {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (f x < level ∧ level ≤ f y) ∨
      (f y < level ∧ level ≤ f x)) :
    ∃ u ∈ Icc x y, f u = level := by
  rcases hcross with h | h
  · rcases intermediate_value_Icc hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rcases intermediate_value_Icc' hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
theorem ZfG {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (|f x| < level ∧ level ≤ |f y|) ∨
      (|f y| < level ∧ level ≤ |f x|)) :
    ∃ u ∈ Icc x y, |f u| = level :=
  Zkg hf.abs hxy hcross
end Xq.Intervals
end
section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal
namespace Xq.GaussianWalk
noncomputable def ZR : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by norm_num⟩
noncomputable instance ZkL :
    IsProbabilityMeasure ZR := by
  unfold ZR
  infer_instance
theorem Zce :
    ∫ x, x ∂ZR = 0 := by
  rw [ZR, integral_bernoulliMeasure]
  norm_num
theorem Zeg :
    ∀ᵐ x ∂ZR, x ∈ Icc (-1 : ℝ) 1 := by
  rw [ZR, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)
theorem ZeE :
    HasSubgaussianMGF id 1 ZR := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := ZR) (X := id) measurable_id.aemeasurable
    Zeg Zce
  have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) = (1 : ℝ≥0) := by
    norm_num
  rw [hc] at h
  exact h
theorem Zdm :
    ∀ᵐ x ∂ZR, |x| = 1 := by
  have hmeas : MeasurableSet {x : ℝ | |x| = 1} :=
    measurable_abs (measurableSet_singleton 1)
  rw [ZR, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)
noncomputable def Zi (iota : Type*) [Fintype iota] :
    Measure (iota → ℝ) :=
  Measure.pi fun _ : iota ↦ ZR
noncomputable instance ZjE
    (iota : Type*) [Fintype iota] :
    IsProbabilityMeasure (Zi iota) := by
  unfold Zi
  infer_instance
theorem ZhS
    (iota : Type*) [Fintype iota] :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ omega i)
      (Zi iota) := by
  unfold Zi
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable
theorem ZeF
    (iota : Type*) [Fintype iota] :
    ∀ᵐ omega ∂Zi iota, ∀ i, |omega i| = 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : iota ↦ ZR) i)
    |>.quasiMeasurePreserving.tendsto_ae Zdm
theorem ZfX
    (iota : Type*) [Fintype iota] (i : iota) :
    HasSubgaussianMGF (fun omega : iota → ℝ ↦ omega i) 1
      (Zi iota) := by
  refine HasSubgaussianMGF.of_map (μ := Zi iota) (X := id)
    (Y := fun omega : iota → ℝ ↦ omega i)
    (measurable_pi_apply i).aemeasurable ?_
  have hmap : (Zi iota).map (fun omega : iota → ℝ ↦ omega i) =
      ZR := by
    unfold Zi
    exact (measurePreserving_eval (μ := fun _ : iota ↦ ZR) i).map_eq
  rw [hmap]
  exact ZeE
theorem ZhA
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ a i * omega i)
      (Zi iota) := by
  have h := (ZhS iota).comp
    (fun i x ↦ a i * x) (fun i ↦ measurable_const.mul measurable_id)
  simpa [Function.comp_def] using h
theorem Zb4
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    HasSubgaussianMGF
      (fun omega : iota → ℝ ↦ ∑ i, a i * omega i)
      (∑ i, ⟨a i ^ 2, sq_nonneg (a i)⟩)
      (Zi iota) := by
  apply HasSubgaussianMGF.sum_of_iIndepFun
    (ZhA iota a) (s := Finset.univ)
  intro i hi
  have h := (ZfX iota i).const_mul (a i)
  have hc : (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) * 1 =
      ⟨a i ^ 2, sq_nonneg (a i)⟩ := mul_one _
  exact hc ▸ h
def partialSum {Omega : Type*} (Y : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  ∑ i ∈ Finset.range n, Y i omega
@[simp]
theorem Zlt {Omega : Type*} (Y : ℕ → Omega → ℝ) :
    partialSum Y 0 = 0 := by
  funext omega
  simp [partialSum]
end Xq.GaussianWalk
end
section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal
namespace Xq.Martingale
structure HasConditionalGaussianMGF
    {Omega : Type*} (m : MeasurableSpace Omega)
    {mOmega : MeasurableSpace Omega} (hm : m ≤ mOmega)
    [StandardBorelSpace Omega]
    (X : Omega → ℝ) (variance : Omega → ℝ≥0)
    (mu : Measure Omega := by volume_tac) [IsFiniteMeasure mu] : Prop where
  integrable_exp_mul :
    ∀ t : ℝ, Integrable (fun omega ↦ exp (t * X omega)) mu
  mgf_eq :
    ∀ᵐ omega ∂(mu.trim hm), ∀ t : ℝ,
      mgf X (condExpKernel mu m omega) t =
        exp (variance omega * t ^ 2 / 2)
namespace HasConditionalGaussianMGF
end HasConditionalGaussianMGF
def partialSum {Omega : Type*} (increment : ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) : ℝ :=
  ∑ i ∈ Finset.range n, increment i omega
@[simp]
theorem Zlt {Omega : Type*} (increment : ℕ → Omega → ℝ) :
    partialSum increment 0 = 0 := by
  funext omega
  simp [partialSum]
end Xq.Martingale
end
section
namespace Xq.ProjectionWalk
open scoped BigOperators
noncomputable section
variable {I K : Type*} [Fintype I]
abbrev Zm (I : Type*) [Fintype I] := EuclideanSpace ℝ I
def Zdb (w : K → Zm I) : Submodule ℝ (Zm I) :=
  Submodule.span ℝ (Set.range w)
def ZcA (w : K → Zm I) : Submodule ℝ (Zm I) :=
  (Zdb w)ᗮ
theorem Ziz (w : K → Zm I) (k : K) :
    w k ∈ Zdb w := by
  exact Submodule.subset_span (Set.mem_range_self k)
theorem ZiA (w : K → Zm I) (x : Zm I) :
    x ∈ ZcA w ↔ ∀ k, inner ℝ (w k) x = 0 := by
  constructor
  · intro hx k
    exact (Submodule.mem_orthogonal (Zdb w) x).1 hx
      (w k) (Ziz w k)
  · intro hx
    rw [ZcA, Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact hx k
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]
variable [Fintype K]
theorem ZgP (w : K → Zm I) :
    Module.finrank ℝ (Zdb w) ≤ Fintype.card K := by
  exact finrank_range_le_card w
omit [Fintype K] in
theorem Zdt (w : K → Zm I) :
    Module.finrank ℝ (Zdb w) +
      Module.finrank ℝ (ZcA w) = Fintype.card I := by
  calc
    Module.finrank ℝ (Zdb w) +
        Module.finrank ℝ (ZcA w) =
        Module.finrank ℝ (Zm I) := by
      exact Submodule.finrank_add_finrank_orthogonal (Zdb w)
    _ = Fintype.card I := finrank_euclideanSpace
theorem Zd0 (w : K → Zm I) :
    Fintype.card I - Fintype.card K ≤
      Module.finrank ℝ (ZcA w) := by
  have hrank := ZgP w
  have hsum := Zdt w
  omega
variable {J : Type*} [DecidableEq I]
def Zhe (i : I) : Zm I :=
  EuclideanSpace.single i 1
@[simp]
theorem Zgo (i : I) (x : Zm I) :
    inner ℝ (Zhe i) x = x i := by
  rw [Zhe, EuclideanSpace.inner_single_left]
  norm_num
def ZcB (v : J → Zm I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Sum coordinates discrepancies → Zm I
  | Sum.inl i => Zhe i.1
  | Sum.inr j => v j.1
def ZcQ (v : J → Zm I) (coordinates : Finset I)
    (discrepancies : Finset J) : Submodule ℝ (Zm I) :=
  ZcA (ZcB v coordinates discrepancies)
theorem ZdA
    (v : J → Zm I) (coordinates : Finset I)
    (discrepancies : Finset J) (x : Zm I) :
    x ∈ ZcQ v coordinates discrepancies ↔
      (∀ i ∈ coordinates, x i = 0) ∧
      (∀ j ∈ discrepancies, inner ℝ (v j) x = 0) := by
  rw [ZcQ, ZiA]
  constructor
  · intro h
    constructor
    · intro i hi
      simpa [ZcB, Zgo] using
        h (Sum.inl ⟨i, hi⟩)
    · intro j hj
      simpa [ZcB] using h (Sum.inr ⟨j, hj⟩)
  · rintro ⟨hcoord, hdisc⟩ k
    cases k with
    | inl i =>
        simpa [ZcB, Zgo] using hcoord i.1 i.2
    | inr j =>
        simpa [ZcB] using hdisc j.1 j.2
theorem ZgQ
    (v : J → Zm I) (coordinates : Finset I)
    (discrepancies : Finset J) :
    Fintype.card I - (coordinates.card + discrepancies.card) ≤
      Module.finrank ℝ (ZcQ v coordinates discrepancies) := by
  have h := Zd0
    (ZcB v coordinates discrepancies)
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at h
  exact h
end
end Xq.ProjectionWalk
end
section
open scoped BigOperators
noncomputable section
namespace Xq.Discrepancy
variable {I J : Type*} [Fintype I] [Fintype J]
def dot (x v : I → ℝ) : ℝ := ∑ i, x i * v i
theorem ZgR (x y v : I → ℝ) :
    dot (x - y) v = dot x v - dot y v := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
def ZdB (x : I → ℝ) : Prop := ∀ i, |x i| ≤ 1
def Zcw (x : I → ℝ) : Prop := ∀ i, x i = 1 ∨ x i = -1
def ZdC (v : I → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)
def ZkB (x : I → ℝ) : ProjectionWalk.Zm I :=
  WithLp.toLp 2 x
@[simp] theorem Zk4 (x : I → ℝ) (i : I) :
    ZkB x i = x i := rfl
theorem Zle (v : I → ℝ) : ‖ZkB v‖ = ZdC v := by
  rw [EuclideanSpace.norm_eq]
  simp only [Zk4, Real.norm_eq_abs, sq_abs, ZdC]
theorem ZkR (v : I → ℝ) : ZdC v = 0 ↔ v = 0 := by
  rw [← Zle, norm_eq_zero]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun x : ProjectionWalk.Zm I ↦ x i) h
    simpa [ZkB] using hi
  · rintro rfl
    rfl
theorem Zhf (x v : I → ℝ)
    (hv : ZdC v = 0) : dot x v = 0 := by
  rw [(ZkR v).mp hv]
  simp [dot]
def Za5 [DecidableEq I] (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ |x i| = 1
def Zmg (F : Finset I) (x v : I → ℝ) : ℝ :=
  ∑ i ∈ F, x i * v i
def restrict (F : Finset I) (x : I → ℝ) : F → ℝ := fun i ↦ x i
def Za6 [DecidableEq I] (F : Finset I) (x : I → ℝ) :
    ↥(Fᶜ : Finset I) → ℝ := fun i ↦ x i
def glue [DecidableEq I] (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) : I → ℝ :=
  fun i ↦ if hi : i ∈ F then xF ⟨i, hi⟩ else xOutside ⟨i, by simp [hi]⟩
section Glue
variable [DecidableEq I] (F : Finset I)
@[simp] theorem Zmk (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∈ F) :
    glue F xF xOutside i = xF ⟨i, hi⟩ := by
  simp [glue, hi]
@[simp] theorem ZkS (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) {i : I} (hi : i ∉ F) :
    glue F xF xOutside i = xOutside ⟨i, by simp [hi]⟩ := by
  simp [glue, hi]
@[simp] theorem Zmm (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    restrict F (glue F xF xOutside) = xF := by
  funext i
  simp [restrict]
@[simp] theorem ZlZ (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) :
    Za6 F (glue F xF xOutside) = xOutside := by
  funext i
  have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
  change glue F xF xOutside i = xOutside i
  rw [ZkS F xF xOutside hi]
@[simp] theorem Zmn (x : I → ℝ) :
    glue F (restrict F x) (Za6 F x) = x := by
  funext i
  by_cases hi : i ∈ F <;> simp [glue, restrict, Za6, hi]
theorem Zl4 {xF : F → ℝ} {xOutside : ↥(Fᶜ : Finset I) → ℝ}
    (hF : Zcw xF) (hOutside : Zcw xOutside) :
    Zcw (glue F xF xOutside) := by
  intro i
  by_cases hi : i ∈ F
  · simpa [glue, hi] using hF ⟨i, hi⟩
  · simpa [glue, hi] using hOutside ⟨i, Finset.mem_compl.mpr hi⟩
end Glue
section RestrictedDot
variable [DecidableEq I]
theorem ZhB (F : Finset I) (x v : I → ℝ) :
    dot x v = Zmg F x v + Zmg Fᶜ x v := by
  simpa only [dot, Zmg] using
    (F.sum_add_sum_compl (fun i ↦ x i * v i)).symm
theorem Zma (F : Finset I) (xF : F → ℝ)
    (xOutside : ↥(Fᶜ : Finset I) → ℝ) (v : I → ℝ) :
    dot (glue F xF xOutside) v =
      dot xF (restrict F v) + dot xOutside (Za6 F v) := by
  rw [ZhB F]
  congr 1
  · rw [Zmg, dot, ← Finset.sum_attach]
    simp [glue, restrict]
  · rw [Zmg, dot, ← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (i : I) ∉ F := Finset.mem_compl.mp i.property
    simp [glue, Za6, hi]
theorem ZiX (F : Finset I) (x v : I → ℝ) :
    dot x v = dot (restrict F x) (restrict F v) +
      dot (Za6 F x) (Za6 F v) := by
  simpa using Zma F (restrict F x) (Za6 F x) v
end RestrictedDot
def ZfY [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ,
    ZdB x ∧
      Fintype.card I ≤ 2 * (Za5 x).card ∧
      ∀ j, |dot (x - x₀) (v j)| ≤ c j * ZdC (v j)
def Zbz (I J : Type*)
    [Fintype I] [Fintype J] [DecidableEq I] : Prop :=
  ∀ (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ),
    ZdB x₀ →
      (∀ j, 0 ≤ c j) →
      (∑ j, Real.exp (-(c j) ^ 2 / 16)) ≤ (Fintype.card I : ℝ) / 16 →
      ZfY v x₀ c
def ZhT
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) : Prop :=
  ∃ x : I → ℝ, Zcw x ∧
    ∀ j,
      |dot (x - x₀) (v j)| ≤
        (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖
def Zbh (c : J → ℝ) : J → ℝ := fun j ↦ 2 * c j / 7
omit [Fintype J] in
theorem ZfZ {c : J → ℝ} (hc : ∀ j, 0 ≤ c j) :
    ∀ j, 0 ≤ Zbh c j := by
  intro j
  simp only [Zbh]
  exact div_nonneg (mul_nonneg (by norm_num) (hc j)) (by norm_num)
omit [Fintype J] in
theorem ZiB (c : J → ℝ) (j : J) :
    -((Zbh c j) ^ 2) / 16 = -(c j) ^ 2 / 196 := by
  simp only [Zbh]
  ring
theorem Zjm {c : J → ℝ}
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    (∑ j, Real.exp (-((Zbh c j) ^ 2) / 16)) ≤
      (Fintype.card I : ℝ) / 16 := by
  simpa only [ZiB] using hbudget
theorem Zkh [DecidableEq I]
    (hLM : Zbz I J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : ZdB x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    ZfY v x₀ (Zbh c) := by
  exact hLM v x₀ (Zbh c) hx₀
    (ZfZ hc) (Zjm hbudget)
theorem Zhg (d : ℕ) (c : ℝ)
    (hd : 900 < d) (hc : 0 ≤ c) :
    2 * c / 7 * Real.sqrt d +
        (Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
          Real.sqrt (d / 2 : ℕ) ≤
      (c + 30) * Real.sqrt d := by
  have he_pos_nat : 0 < d / 2 := by omega
  have he_ge_nat : 450 ≤ d / 2 := by omega
  have hd_le_nat : d ≤ 2 * (d / 2) + 1 := by omega
  have he_pos : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast he_pos_nat
  have he_ge : (450 : ℝ) ≤ (d / 2 : ℕ) := by exact_mod_cast he_ge_nat
  have hd_le : (d : ℝ) ≤ 2 * (d / 2 : ℕ) + 1 := by exact_mod_cast hd_le_nat
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hratio_pos : 0 < (d : ℝ) / (d / 2 : ℕ) := div_pos hd_pos he_pos
  have hratio_le : (d : ℝ) / (d / 2 : ℕ) ≤ (901 : ℝ) / 450 := by
    rw [div_le_iff₀ he_pos]
    nlinarith
  have hlog_aux : Real.log ((901 : ℝ) / 450) ≤ Real.log 2 + 1 / 900 := by
    rw [show (901 : ℝ) / 450 = 2 * (901 / 900) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    gcongr
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 901 / 900 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog : Real.log ((d : ℝ) / (d / 2 : ℕ)) ≤ (36 : ℝ) / 49 := by
    calc
      Real.log ((d : ℝ) / (d / 2 : ℕ))
          ≤ Real.log ((901 : ℝ) / 450) := Real.log_le_log hratio_pos hratio_le
      _ ≤ Real.log 2 + 1 / 900 := hlog_aux
      _ ≤ (36 : ℝ) / 49 := by
        have h := Real.log_two_lt_d9.le
        norm_num at h ⊢
        linarith
  have ha :
      Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) ≤ c + 12 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have he_le_nat : 2 * (d / 2) ≤ d := by omega
  have he_le : 2 * ((d / 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast he_le_nat
  have hsqrt : Real.sqrt (d / 2 : ℕ) ≤ (71 : ℝ) / 100 * Real.sqrt d := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsqd := Real.sq_sqrt hd_pos.le
      nlinarith
  calc
    2 * c / 7 * Real.sqrt d +
          (Real.sqrt (c ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) + 30) *
            Real.sqrt (d / 2 : ℕ)
        ≤ 2 * c / 7 * Real.sqrt d + (c + 42) * Real.sqrt (d / 2 : ℕ) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (by linarith [ha]) (Real.sqrt_nonneg _)) _
    _ ≤ 2 * c / 7 * Real.sqrt d +
          (c + 42) * ((71 : ℝ) / 100 * Real.sqrt d) := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left hsqrt (by linarith)) _
    _ = (2 * c / 7 + (c + 42) * ((71 : ℝ) / 100)) * Real.sqrt d := by ring
    _ ≤ (c + 30) * Real.sqrt d := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          nlinarith
@[simp] theorem Zmo (v : I → ℝ) : dot 0 v = 0 := by
  simp [dot]
@[simp] theorem Zml (x : I → ℝ) : dot x 0 = 0 := by
  simp [dot]
theorem ZjF (x v : I → ℝ) :
    |dot x v| ≤ ∑ i, |x i| * |v i| := by
  rw [dot]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun i _ ↦ by rw [abs_mul]
theorem ZfJ
    {x v : I → ℝ} {a : ℝ} (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) :
    |dot x v| ≤ Fintype.card I * a * ‖v‖ := by
  calc
    |dot x v| ≤ ∑ i, |x i| * |v i| := ZjF x v
    _ ≤ ∑ _i : I, a * ‖v‖ := by
      refine Finset.sum_le_sum fun i _ ↦ mul_le_mul (hx i) (norm_le_pi_norm v i)
        (abs_nonneg _) ha
    _ = Fintype.card I * a * ‖v‖ := by simp [mul_assoc]
theorem Zic (v : I → ℝ) :
    (∑ i, (v i) ^ 2) ≤ Fintype.card I * ‖v‖ ^ 2 := by
  calc
    (∑ i, (v i) ^ 2) ≤ ∑ _i : I, ‖v‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hvi : |v i| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      rw [← sq_abs]
      nlinarith [abs_nonneg (v i), norm_nonneg v,
        mul_nonneg (sub_nonneg.mpr hvi) (add_nonneg (norm_nonneg v) (abs_nonneg (v i)))]
    _ = Fintype.card I * ‖v‖ ^ 2 := by simp
theorem ZhC (v : I → ℝ) :
    ZdC v ≤ Real.sqrt (Fintype.card I) * ‖v‖ := by
  have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hcard_nonneg : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
  rw [ZdC, ← Real.sqrt_sq hnorm_nonneg, ← Real.sqrt_mul hcard_nonneg]
  exact Real.sqrt_le_sqrt (Zic v)
def Zes (x : I → ℝ) : I → ℝ :=
  fun i ↦ if 0 ≤ x i then 1 else -1
omit [Fintype I] in
theorem ZkT (x : I → ℝ) : Zcw (Zes x) := by
  intro i
  simp only [Zes]
  split_ifs <;> simp
omit [Fintype I] in
theorem Zid {x : I → ℝ} (hx : ZdB x) (i : I) :
    |Zes x i - x i| ≤ 1 := by
  have hxi := hx i
  simp only [abs_le] at hxi
  simp only [Zes]
  split_ifs with h
  · rw [abs_of_nonneg]
    · linarith
    · linarith
  · rw [abs_of_nonpos]
    · linarith
    · linarith
theorem Zff
    {x : I → ℝ} (hx : ZdB x) (v : I → ℝ) :
    |dot (Zes x - x) v| ≤ Fintype.card I * ‖v‖ := by
  change |dot (fun i ↦ Zes x i - x i) v| ≤ Fintype.card I * ‖v‖
  simpa using ZfJ (v := v) (a := 1)
    (by norm_num) (Zid hx)
theorem Zfy
    (hcard : Fintype.card I ≤ 900) :
    (Fintype.card I : ℝ) ≤ 30 * Real.sqrt (Fintype.card I) := by
  have h0 : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (Fintype.card I) ≤ 30 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
      exact_mod_cast hcard
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (Fintype.card I)]
omit [Fintype J] in
theorem ZgS
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : ZdB x₀) (hc : ∀ j, 0 ≤ c j)
    (hcard : Fintype.card I ≤ 900) :
    ZhT v x₀ c := by
  refine ⟨Zes x₀, ZkT x₀, ?_⟩
  intro j
  have hround := Zff hx₀ (v j)
  have hdim := Zfy (I := I) hcard
  calc
    |dot (Zes x₀ - x₀) (v j)|
        ≤ Fintype.card I * ‖v j‖ := hround
    _ ≤ 30 * Real.sqrt (Fintype.card I) * ‖v j‖ := by
      exact mul_le_mul_of_nonneg_right hdim (norm_nonneg _)
    _ ≤ (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖ := by
      gcongr
      linarith [hc j]
end Xq.Discrepancy
end
section
open scoped BigOperators
noncomputable section
namespace Xq.Discrepancy
universe uI uJ
variable {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
def ZaQ (d : ℕ) (c : J → ℝ) : J → ℝ :=
  fun j ↦ Real.sqrt (c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ)))
omit [Fintype J] in
theorem Zhp (d : ℕ) (c : J → ℝ) :
    ∀ j, 0 ≤ ZaQ d c j := fun _ ↦ Real.sqrt_nonneg _
theorem half_pos {d : ℕ} (hd : 900 < d) : 0 < d / 2 := by omega
theorem Zmu {d : ℕ} (hd : 900 < d) : d / 2 < d := by omega
theorem Zk5 {d : ℕ} (hd : 900 < d) :
    (1 : ℝ) ≤ (d : ℝ) / (d / 2 : ℕ) := by
  have hq : 0 < ((d / 2 : ℕ) : ℝ) := by exact_mod_cast half_pos hd
  rw [le_div_iff₀ hq]
  norm_num
  exact_mod_cast (show d / 2 ≤ d by omega)
omit [Fintype J] in
theorem Zlf {d : ℕ} (hd : 900 < d) (c : J → ℝ) (j : J) :
    ZaQ d c j ^ 2 =
      c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ)) := by
  rw [ZaQ, Real.sq_sqrt]
  have hlog : 0 ≤ Real.log ((d : ℝ) / (d / 2 : ℕ)) :=
    Real.log_nonneg (Zk5 hd)
  positivity
omit [Fintype J] in
theorem Zie {d : ℕ} (hd : 900 < d)
    (c : J → ℝ) (j : J) :
    Real.exp (-(ZaQ d c j) ^ 2 / 196) =
      Real.exp (-(c j) ^ 2 / 196) * ((d / 2 : ℕ) : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqR : (0 : ℝ) < (d / 2 : ℕ) := by exact_mod_cast half_pos hd
  rw [Zlf hd]
  rw [show -(c j ^ 2 + 196 * Real.log ((d : ℝ) / (d / 2 : ℕ))) / 196 =
      -(c j) ^ 2 / 196 - Real.log ((d : ℝ) / (d / 2 : ℕ)) by ring]
  rw [Real.exp_sub, Real.exp_log (div_pos hdR hqR)]
  field_simp
theorem Zki {d : ℕ} (hd : 900 < d) (c : J → ℝ)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤ (d : ℝ) / 16) :
    (∑ j, Real.exp (-(ZaQ d c j) ^ 2 / 196)) ≤
      ((d / 2 : ℕ) : ℝ) / 16 := by
  simp_rw [Zie hd]
  simp_rw [mul_div_assoc]
  rw [← Finset.sum_mul]
  have hfactor : 0 ≤ (((d / 2 : ℕ) : ℝ) / d) := by positivity
  calc
    (∑ j, Real.exp (-(c j) ^ 2 / 196)) * (((d / 2 : ℕ) : ℝ) / d)
        ≤ ((d : ℝ) / 16) * (((d / 2 : ℕ) : ℝ) / d) := by
          exact mul_le_mul_of_nonneg_right hbudget hfactor
    _ = ((d / 2 : ℕ) : ℝ) / 16 := by
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      field_simp
def ZiY [DecidableEq I] (F : Finset I) (q : ℕ) (v : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => v i
  | Sum.inr _ => 0
def Zkd [DecidableEq I] (F : Finset I) (q : ℕ) (x : I → ℝ) :
    Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ
  | Sum.inl i => x i
  | Sum.inr _ => 0
theorem Zlu [DecidableEq I] (F : Finset I) (q : ℕ)
    {x : I → ℝ} (hx : ZdB x) : ZdB (Zkd F q x) := by
  intro i
  cases i with
  | inl i => simpa [Zkd] using hx i
  | inr i => simp [Zkd]
theorem Zk6 [DecidableEq I] (F : Finset I) (q : ℕ)
    (v : I → ℝ) : ‖ZiY F q v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  cases i with
  | inl i => simpa [ZiY] using norm_le_pi_norm v i
  | inr i => simp [ZiY]
theorem Zmp [DecidableEq I] (F : Finset I) (q : ℕ)
    (hcard : Fᶜ.card ≤ q) :
    Fintype.card (Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))) = q := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin,
    Nat.add_sub_of_le hcard]
theorem Zl5 [DecidableEq I] (F : Finset I) (q : ℕ)
    (y : Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card)) → ℝ)
    (x v : I → ℝ) :
    dot (y - Zkd F q x) (ZiY F q v) =
      dot (fun i : ↥(Fᶜ : Finset I) ↦ y (Sum.inl i) - x i)
        (Za6 F v) := by
  simp [dot, Zkd, ZiY, Za6]
theorem ZjX [DecidableEq I] (x : I → ℝ) :
    Zcw (restrict (Za5 x) x) := by
  intro i
  have hi : |x i| = 1 := by
    simpa [Za5] using i.property
  simpa [restrict] using (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hi
theorem ZiZ [DecidableEq I] {x : I → ℝ}
    (hfixed : Fintype.card I ≤ 2 * (Za5 x).card) :
    (Za5 x)ᶜ.card ≤ Fintype.card I / 2 := by
  rw [Finset.card_compl]
  omega
theorem ZbI
    (hLM : ∀ (K : Type uI) [Fintype K] [DecidableEq K],
      Zbz K J)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : ZdB x₀) (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card I : ℝ) / 16) :
    ZhT v x₀ c := by
  classical
  generalize hdcard : Fintype.card I = d at hbudget ⊢
  induction d using Nat.strong_induction_on generalizing I c with
  | h d ih =>
      by_cases hdsmall : d ≤ 900
      · exact ZgS v x₀ c hx₀ hc
          (hdcard.trans_le hdsmall)
      · have hdlarge : 900 < d := by omega
        have hbudgetI :
            (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
              (Fintype.card I : ℝ) / 16 := by simpa [hdcard] using hbudget
        obtain ⟨x, hxCube, hxFixed, hxError⟩ :=
          Zkh (hLM I) v x₀ c hx₀ hc hbudgetI
        let F : Finset I := Za5 x
        let q : ℕ := d / 2
        have hFcard : Fᶜ.card ≤ q := by
          dsimp only [F, q]
          have hhalf := ZiZ hxFixed
          simpa [hdcard] using hhalf
        let K := Sum ↥(Fᶜ : Finset I) (Fin (q - Fᶜ.card))
        let vK : J → K → ℝ := fun j ↦ ZiY F q (v j)
        let xK : K → ℝ := Zkd F q x
        have hcardK : Fintype.card K = q := by
          exact Zmp F q hFcard
        have hq_lt : q < d := by
          dsimp only [q]
          exact Zmu hdlarge
        have hxK : ZdB xK := Zlu F q hxCube
        have hbudgetK :
            (∑ j, Real.exp (-(ZaQ d c j) ^ 2 / 196)) ≤
              (Fintype.card K : ℝ) / 16 := by
          rw [hcardK]
          exact Zki hdlarge c hbudget
        have hrecursive : ZhT vK xK (ZaQ d c) := by
          apply ih q hq_lt (I := K) vK xK (ZaQ d c) hxK
            (Zhp d c) hcardK
          simpa [hcardK] using hbudgetK
        obtain ⟨yK, hyKSign, hyKError⟩ := hrecursive
        let yOutside : ↥(Fᶜ : Finset I) → ℝ := fun i ↦ yK (Sum.inl i)
        let y : I → ℝ := glue F (restrict F x) yOutside
        have hyOutsideSign : Zcw yOutside := fun i ↦ hyKSign (Sum.inl i)
        have hySign : Zcw y := by
          exact Zl4 F (ZjX x) hyOutsideSign
        refine ⟨y, hySign, ?_⟩
        intro j
        have hpartial :
            |dot (x - x₀) (v j)| ≤
              (2 * c j / 7 * Real.sqrt d) * ‖v j‖ := by
          calc
            |dot (x - x₀) (v j)|
                ≤ Zbh c j * ZdC (v j) := hxError j
            _ ≤ Zbh c j *
                (Real.sqrt (Fintype.card I) * ‖v j‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (ZhC (v j))
                    (ZfZ hc j)
            _ = (2 * c j / 7 * Real.sqrt d) * ‖v j‖ := by
                  simp [Zbh, hdcard]
                  ring
        have hvKnorm : ‖vK j‖ ≤ ‖v j‖ := Zk6 F q (v j)
        have hrecursiveError :
            |dot (yK - xK) (vK j)| ≤
              ((ZaQ d c j + 30) * Real.sqrt q) * ‖v j‖ := by
          calc
            |dot (yK - xK) (vK j)|
                ≤ (ZaQ d c j + 30) *
                    Real.sqrt (Fintype.card K) * ‖vK j‖ := hyKError j
            _ = ((ZaQ d c j + 30) * Real.sqrt q) * ‖vK j‖ := by
                  rw [hcardK]
            _ ≤ ((ZaQ d c j + 30) * Real.sqrt q) * ‖v j‖ := by
                  exact mul_le_mul_of_nonneg_left hvKnorm
                    (mul_nonneg (by linarith [Zhp d c j])
                      (Real.sqrt_nonneg _))
        have hyxDot :
            dot (y - x) (v j) = dot (yK - xK) (vK j) := by
          calc
            dot (y - x) (v j) =
                dot (yOutside - Za6 F x) (Za6 F (v j)) := by
              change dot (glue F (restrict F x) yOutside - x) (v j) = _
              rw [ZgR, Zma, ZiX F x,
                ZgR]
              ring
            _ = dot (yK - xK) (vK j) := by
              symm
              exact Zl5 F q yK x (v j)
        have hyx :
            |dot (y - x) (v j)| ≤
              ((ZaQ d c j + 30) * Real.sqrt q) * ‖v j‖ := by
          rw [hyxDot]
          exact hrecursiveError
        have hsplit :
            dot (y - x₀) (v j) = dot (x - x₀) (v j) + dot (y - x) (v j) := by
          rw [ZgR, ZgR, ZgR]
          ring
        rw [hsplit]
        calc
          |dot (x - x₀) (v j) + dot (y - x) (v j)|
              ≤ |dot (x - x₀) (v j)| + |dot (y - x) (v j)| := abs_add_le _ _
          _ ≤ (2 * c j / 7 * Real.sqrt d) * ‖v j‖ +
                ((ZaQ d c j + 30) * Real.sqrt q) * ‖v j‖ :=
              add_le_add hpartial hyx
          _ = (2 * c j / 7 * Real.sqrt d +
                (ZaQ d c j + 30) * Real.sqrt q) * ‖v j‖ := by ring
          _ ≤ ((c j + 30) * Real.sqrt d) * ‖v j‖ := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [ZaQ, q] using
                  Zhg d (c j) hdlarge (hc j))
                (norm_nonneg _)
          _ = (c j + 30) * Real.sqrt (Fintype.card I) * ‖v j‖ := by
              rw [hdcard]
end Xq.Discrepancy
end
section
namespace Xq.KernelClaims
open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral
private lemma ZjG (omega : ℝ) (homega : omega ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -Real.cos (omega * y) / omega)
      (Real.sin (omega * x)) x := by
  simpa [homega] using ((hasDerivAt_const_mul omega).cos.neg.div_const omega)
theorem Zbf
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ h' x)
    (hcos : Real.cos ((2 * (n : ℝ)) * b) = Real.cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  let omega : ℝ := 2 * (n : ℝ)
  have homega : omega ≠ 0 := by
    dsimp [omega]
    positivity
  let v : ℝ → ℝ := fun x ↦ -Real.cos (omega * x) / omega
  have hvderiv : ∀ x ∈ Icc a b, HasDerivAt v (Real.sin (omega * x)) x := by
    intro x hx
    exact ZjG omega homega x
  have hh'int : IntervalIntegrable h' volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hv'int : IntervalIntegrable (fun x ↦ Real.sin (omega * x)) volume a b :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hderivU : ∀ x ∈ uIcc a b, HasDerivAt h (h' x) x := by
    simpa [uIcc_of_le hab] using hderiv
  have hvderivU : ∀ x ∈ uIcc a b, HasDerivAt v (Real.sin (omega * x)) x := by
    simpa [uIcc_of_le hab] using hvderiv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) hderivU hvderivU hh'int hv'int
  have hhprime : (∫ x in a..b, h' x) = h b - h a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderivU hh'int
  have hdiff_nonneg : 0 ≤ h b - h a := by
    rw [← hhprime]
    exact intervalIntegral.integral_nonneg hab hnonneg
  have hv_bound (x : ℝ) : |v x| ≤ 1 / omega := by
    dsimp [v]
    rw [abs_div, abs_neg, abs_of_pos (show 0 < omega by positivity)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  have hj_bound : |∫ x in a..b, h' x * v x| ≤ (h b - h a) / omega := by
    calc
      |∫ x in a..b, h' x * v x| ≤ ∫ x in a..b, |h' x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, h' x * (1 / omega) := by
        refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
        · exact (hh'int.mul_continuousOn
            (show ContinuousOn v (uIcc a b) from by
              simpa [uIcc_of_le hab] using
                ((Real.continuous_cos.comp
                  (continuous_const.mul continuous_id)).neg.div_const _).continuousOn)).abs
        · exact hh'int.mul_const _
        · intro x hx
          rw [abs_mul, abs_of_nonneg (hnonneg x hx)]
          exact mul_le_mul_of_nonneg_left (hv_bound x) (hnonneg x hx)
      _ = (h b - h a) / omega := by
        rw [intervalIntegral.integral_mul_const, hhprime]
        ring
  have hboundary :
      h b * v b - h a * v a =
        (Real.cos (omega * a) * (h a - h b)) / omega := by
    dsimp [v, omega] at hcos ⊢
    rw [hcos]
    ring
  change |∫ x in a..b, h x * Real.sin (omega * x)| ≤ |h b - h a| / n
  rw [hparts, hboundary]
  have hboundary_abs :
      |Real.cos (omega * a) * (h a - h b) / omega| ≤
        (h b - h a) / omega := by
    rw [abs_div, abs_mul, abs_sub_comm, abs_of_nonneg hdiff_nonneg,
      abs_of_pos (show 0 < omega by positivity)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left hdiff_nonneg (Real.abs_cos_le_one _)) (by positivity)
  calc
    |Real.cos (omega * a) * (h a - h b) / omega -
        ∫ x in a..b, h' x * v x| ≤
        |Real.cos (omega * a) * (h a - h b) / omega| +
          |∫ x in a..b, h' x * v x| := abs_sub _ _
    _ ≤ (h b - h a) / omega + (h b - h a) / omega :=
      add_le_add hboundary_abs hj_bound
    _ = |h b - h a| / n := by
      rw [abs_of_nonneg hdiff_nonneg]
      dsimp [omega]
      field_simp
      ring
theorem Zb5
    {h h' : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h' (Icc a b))
    (hnonpos : ∀ x ∈ Icc a b, h' x ≤ 0)
    (hcos : Real.cos ((2 * (n : ℝ)) * b) = Real.cos ((2 * (n : ℝ)) * a)) :
    |∫ x in a..b, h x * Real.sin ((2 * (n : ℝ)) * x)| ≤
      |h b - h a| / n := by
  have h := Zbf
    (h := fun x ↦ -h x) (h' := fun x ↦ -h' x) hn hab
    (fun x hx ↦ (hderiv x hx).neg) hcont.neg
    (fun x hx ↦ neg_nonneg.mpr (hnonpos x hx)) hcos
  simpa only [neg_mul, intervalIntegral.integral_neg, abs_neg, neg_sub_neg,
    abs_sub_comm] using h
theorem Za0
    {m : ℕ} {A B E : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hlocal : ∀ k < m, E k ≤ (B k - A k) / n)
    (hchain : ∀ k < m, B k ≤ A (k + 1)) :
    ∑ k ∈ Finset.range m, E k ≤ (A m - A 0) / n := by
  calc
    ∑ k ∈ Finset.range m, E k ≤
        ∑ k ∈ Finset.range m, (B k - A k) / n := by
      exact Finset.sum_le_sum fun k hk ↦ hlocal k (Finset.mem_range.mp hk)
    _ ≤ ∑ k ∈ Finset.range m, (A (k + 1) - A k) / n := by
      refine Finset.sum_le_sum fun k hk ↦ div_le_div_of_nonneg_right ?_ (by positivity)
      exact sub_le_sub_right (hchain k (Finset.mem_range.mp hk)) _
    _ = (A m - A 0) / n := by
      rw [← Finset.sum_div]
      congr 1
      simpa using Finset.sum_range_sub A m
theorem Zi0 {value main error : ℝ}
    (hvalue : value = main + error)
    (hmain_lower : 4 / 3 ≤ |main|)
    (hmain_upper : |main| ≤ 4)
    (herror : |error| ≤ 2 / 3) :
    2 / 3 ≤ |value| ∧ |value| ≤ 5 := by
  subst value
  constructor
  · have hreverse : |main| ≤ |main + error| + |error| := by
      calc
        |main| = |(main + error) - error| := by ring_nf
        _ ≤ |main + error| + |error| := abs_sub _ _
    linarith
  · have hforward : |main + error| ≤ |main| + |error| :=
      abs_add_le main error
    linarith
end Xq.KernelClaims
end
section
namespace Xq.Rounding
open scoped BigOperators
noncomputable section
def Zl (j : ℕ) : ℕ := 2 * j + 1
def ZL (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, a j * Real.sin ((Zl j : ℝ) * theta)
def Zap (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, (a j : ℂ) *
    (((Zl j : ℝ) : ℂ) * Complex.I) ^ l *
      Complex.exp ((((Zl j : ℝ) * theta : ℝ) : ℂ) * Complex.I)
def ZaE (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℝ :=
  (Zap l n a theta).im
@[simp]
theorem ZjH (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    ZaE 0 n a theta = ZL n a theta := by
  classical
  simp only [ZaE, Zap, ZL, pow_zero,
    mul_one]
  change Complex.imLm
    (∑ j ∈ Finset.range n, (a j : ℂ) *
      Complex.exp ((((Zl j : ℝ) * theta : ℝ) : ℂ) * Complex.I)) = _
  rw [map_sum Complex.imLm]
  apply Finset.sum_congr rfl
  intro j hj
  change ((a j : ℂ) *
    Complex.exp ((((Zl j : ℝ) * theta : ℝ) : ℂ) * Complex.I)).im = _
  rw [Complex.mul_im]
  simp [Complex.exp_im]
theorem Zi1 (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    |ZaE l n a theta| ≤
      ∑ j ∈ Finset.range n, |a j| * (Zl j : ℝ) ^ l := by
  classical
  calc
    |ZaE l n a theta| ≤ ‖Zap l n a theta‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ∑ j ∈ Finset.range n,
        ‖(a j : ℂ) *
          ((((Zl j : ℝ) : ℂ) * Complex.I) ^ l) *
          Complex.exp ((((Zl j : ℝ) * theta : ℝ) : ℂ) * Complex.I)‖ := by
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, |a j| * (Zl j : ℝ) ^ l := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_mul, norm_pow]
      have hexp :
          ‖Complex.exp ((((Zl j : ℝ) * theta : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I _
      have hfreq : 0 ≤ (Zl j : ℝ) := by positivity
      have hnormFreq : ‖((Zl j : ℝ) : ℂ)‖ = (Zl j : ℝ) :=
        Complex.norm_of_nonneg hfreq
      rw [hexp, mul_one, Complex.norm_mul, hnormFreq, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
theorem Zf0 {n j : ℕ} (hj : j ∈ Finset.range n) :
    Zl j ≤ 2 * n := by
  simp only [Finset.mem_range] at hj
  simp only [Zl]
  omega
theorem Zf1 (l n : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hA : ∀ j < n, |a j| ≤ A) (hA0 : 0 ≤ A) (theta : ℝ) :
    |ZaE l n a theta| ≤
      n * A * (2 * n : ℝ) ^ l := by
  refine (Zi1 l n a theta).trans ?_
  calc
    (∑ j ∈ Finset.range n, |a j| * (Zl j : ℝ) ^ l) ≤
        ∑ _j ∈ Finset.range n, A * (2 * n : ℝ) ^ l := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hfreq : (Zl j : ℝ) ≤ (2 * n : ℝ) := by
        exact_mod_cast Zf0 hj
      exact mul_le_mul (hA j hj')
        (pow_le_pow_left₀ (by positivity) hfreq l) (by positivity) hA0
    _ = n * A * (2 * n : ℝ) ^ l := by
      simp [mul_assoc]
theorem ZeG (n : ℕ) (a : ℕ → ℝ)
    (x h : ℝ) :
    HasSum (fun l : ℕ => Zap l n a x * (h : ℂ) ^ l / l.factorial)
      (Zap 0 n a (x + h)) := by
  classical
  have hj (j : ℕ) :
      HasSum
        (fun l : ℕ =>
          ((a j : ℂ) *
            Complex.exp ((((Zl j : ℝ) * x : ℝ) : ℂ) * Complex.I)) *
            (((((Zl j : ℝ) : ℂ) * Complex.I) * (h : ℂ)) ^ l /
              l.factorial))
        ((a j : ℂ) *
          Complex.exp ((((Zl j : ℝ) * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((Zl j : ℝ) : ℂ) * Complex.I * (h : ℂ))) := by
    let z : ℂ := (((Zl j : ℝ) : ℂ) * Complex.I) * (h : ℂ)
    let c : ℂ := (a j : ℂ) *
      Complex.exp ((((Zl j : ℝ) * x : ℝ) : ℂ) * Complex.I)
    have hz : HasSum (fun l : ℕ => z ^ l / l.factorial) (Complex.exp z) :=
      Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp z
    simpa only [z, c] using hz.mul_left c
  have hsum := hasSum_sum (s := Finset.range n) (fun j _ => hj j)
  convert hsum using 1
  · funext l
    simp only [Zap, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hjmem
    rw [mul_pow]
    ring
  · simp only [Zap, pow_zero, mul_one]
    apply Finset.sum_congr rfl
    intro j hjmem
    rw [show ((((Zl j : ℝ) * (x + h) : ℝ) : ℂ) * Complex.I) =
        ((((Zl j : ℝ) * x : ℝ) : ℂ) * Complex.I) +
          (((Zl j : ℝ) : ℂ) * Complex.I * (h : ℂ)) by
            push_cast; ring]
    rw [Complex.exp_add]
    ring
theorem Zgy (n : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    HasSum (fun l : ℕ => ZaE l n a x * h ^ l / l.factorial)
      (ZaE 0 n a (x + h)) := by
  have him := Complex.hasSum_im (ZeG n a x h)
  convert him using 1
  · funext l
    change (Zap l n a x).im * h ^ l / l.factorial =
      (Zap l n a x * (h : ℂ) ^ l / l.factorial).im
    have hcomponents : ((h : ℂ) ^ l).re = h ^ l ∧ ((h : ℂ) ^ l).im = 0 := by
      induction l with
      | zero => simp
      | succ l ih =>
          rw [pow_succ, pow_succ, Complex.mul_re, Complex.mul_im]
          simp [ih.1, ih.2]
    have hpow : (h : ℂ) ^ l = ((h ^ l : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hcomponents.1, hcomponents.2]
    rw [hpow]
    rw [Complex.div_im, Complex.normSq_natCast]
    have hfac : (l.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac, Nat.factorial_ne_zero]
    rw [Complex.mul_im, Complex.mul_re]
    norm_num
    apply Or.inl
    rw [hcomponents.2, hcomponents.1]
    ring
  · rfl
theorem ZcL {l : ℕ} (hl : 2 ≤ l) :
    65 + 2 * l ≤ 35 * l.factorial := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      by_cases hl2 : l = 2
      · subst l
        norm_num
      · have hl3 : 3 ≤ l := by omega
        have hlprev : 2 ≤ l - 1 := by omega
        have hih := ih (l - 1) (by omega) hlprev
        have hfac : 1 ≤ (l - 1).factorial := Nat.factorial_pos _
        have hthree : 3 * (l - 1).factorial ≤ l * (l - 1).factorial :=
          Nat.mul_le_mul_right _ hl3
        rw [show l = (l - 1) + 1 by omega, Nat.factorial_succ]
        calc
          65 + 2 * ((l - 1) + 1) = (65 + 2 * (l - 1)) + 2 := by omega
          _ ≤ 35 * (l - 1).factorial + 2 := Nat.add_le_add_right hih 2
          _ ≤ 35 * (3 * (l - 1).factorial) := by omega
          _ ≤ 35 * (l * (l - 1).factorial) := Nat.mul_le_mul_left 35 hthree
          _ = 35 * ((l - 1 + 1) * (l - 1).factorial) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ l)]
theorem Zfz (l : ℕ) :
    65 + 2 * l ≤ 67 * l.factorial := by
  by_cases hl : l < 2
  · interval_cases l <;> norm_num
  · exact (ZcL (l := l) (by omega)).trans
      (Nat.mul_le_mul_right l.factorial (by norm_num))
theorem Zfg {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)
  have hgeom : Summable (fun l : ℕ => (67 : ℝ) * q ^ l) := hgeo0.mul_left 67
  apply Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hgeom
  have hcoef : (65 + 2 * l : ℝ) ≤ 67 * l.factorial := by
    exact_mod_cast Zfz l
  have hfact : (0 : ℝ) < l.factorial := by positivity
  calc
    (65 + 2 * l : ℝ) * q ^ l / l.factorial ≤
        (67 * l.factorial) * q ^ l / l.factorial := by gcongr
    _ = 67 * q ^ l := by field_simp
theorem Zfh {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 11 / 112) :
    (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) ≤ 72 := by
  have hq1 : q < 1 := by linarith
  have hs := Zfg hq0 hq1
  rw [← hs.sum_add_tsum_nat_add 2]
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)
  have htailGeom : Summable (fun k : ℕ => (35 : ℝ) * q ^ (k + 2)) :=
    (hgeo0.mul_left (35 * q ^ 2)).congr
      (fun k => by rw [pow_add]; ring)
  have htail : (∑' k : ℕ,
      (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) ≤
      ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
    have hsTail : Summable (fun k : ℕ =>
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) := by
      simpa only using (summable_nat_add_iff 2).2 hs
    apply Summable.tsum_le_tsum
    · intro k
      have hcoef : (65 + 2 * ((k + 2 : ℕ) : ℝ)) ≤ 35 * (k + 2).factorial := by
        exact_mod_cast ZcL (l := k + 2) (by omega)
      have hfact : (0 : ℝ) < (k + 2).factorial := by positivity
      calc
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial ≤
            (35 * (k + 2).factorial) * q ^ (k + 2) / (k + 2).factorial := by
          gcongr
        _ = 35 * q ^ (k + 2) := by field_simp
    · exact hsTail
    · exact htailGeom
  calc
    (∑ l ∈ Finset.range 2, (65 + 2 * l : ℝ) * q ^ l / l.factorial) +
        ∑' k : ℕ, (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) /
          (k + 2).factorial ≤
        65 + 67 * q + ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
      convert add_le_add_left htail (65 + 67 * q) using 1 <;>
        norm_num [Finset.sum_range_succ] <;> ring
    _ = 65 + 67 * q + 35 * q ^ 2 / (1 - q) := by
      rw [show (∑' k : ℕ, (35 : ℝ) * q ^ (k + 2)) =
          35 * q ^ 2 * ∑' k : ℕ, q ^ k by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            rw [pow_add]
            ring,
        tsum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)]
      field_simp
    _ ≤ 72 := by
      have hmono : 0 ≤ ((11 / 112 : ℝ) - q) *
          (74 - 32 * ((11 / 112 : ℝ) + q)) := by
        apply mul_nonneg
        · linarith
        · nlinarith
      have hdiv : 35 * q ^ 2 / (1 - q) ≤ 72 - (65 + 67 * q) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
theorem ZfK
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ) (x theta : ℝ)
    (hnear : |theta - x| ≤ Real.pi / (64 * n))
    (hdisc : ∀ l : ℕ,
      |ZaE l n a x| ≤
        (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) :
    |ZL n a theta| ≤ 72 * Real.sqrt n := by
  let h : ℝ := theta - x
  have htheta : x + h = theta := by dsimp [h]; ring
  have hq0 : 0 ≤ |h| * (2 * n : ℝ) := mul_nonneg (abs_nonneg _) (by positivity)
  have hpi : Real.pi < 22 / 7 := by
    exact lt_of_lt_of_le Real.pi_lt_d20 (by norm_num)
  have hq : |h| * (2 * n : ℝ) ≤ 11 / 112 := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnear' : |h| ≤ Real.pi / (64 * n) := hnear
    calc
      |h| * (2 * n : ℝ) ≤ (Real.pi / (64 * n)) * (2 * n) := by
        gcongr
      _ = Real.pi / 32 := by field_simp; ring
      _ ≤ 11 / 112 := by linarith
  have htaylor := Zgy n a x h
  let q : ℝ := |h| * (2 * n : ℝ)
  have hqdef : q = |h| * (2 * n : ℝ) := rfl
  have haff : Summable
      (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) :=
    Zfg (q := q) (hqdef ▸ hq0)
      (lt_of_le_of_lt (hqdef ▸ hq) (by norm_num : (11 / 112 : ℝ) < 1))
  have hbSummable : Summable (fun l : ℕ =>
      ((65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) *
        |h| ^ l / l.factorial) := by
    refine (haff.mul_left (Real.sqrt n)).congr (fun l => ?_)
    rw [hqdef, mul_pow]
    ring
  have hTaylorBound := htaylor.norm_le_of_bounded hbSummable.hasSum (fun l => by
    have hfacabs : |(l.factorial : ℝ)| = (l.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, hfacabs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hdisc l) (by positivity)) (by positivity))
  rw [Real.norm_eq_abs, ZjH, htheta] at hTaylorBound
  calc
    |ZL n a theta| ≤ ∑' l : ℕ,
        ((65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) *
          |h| ^ l / l.factorial := hTaylorBound
    _ = Real.sqrt n *
        (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      rw [hqdef]
      rw [mul_pow]
      ring
    _ ≤ Real.sqrt n * 72 := by
      exact mul_le_mul_of_nonneg_left
        (Zfh (q := q) (hqdef ▸ hq0) (hqdef ▸ hq))
        (Real.sqrt_nonneg n)
    _ = 72 * Real.sqrt n := by ring
end
end Xq.Rounding
end
section
namespace Xq.OddSine
open scoped BigOperators Interval
open Set
noncomputable section
def K : ℝ := 2 ^ 7
@[simp] theorem Zmw : K = 128 := by norm_num [K]
abbrev RealInterval := ℝ × ℝ
def Zal (I : RealInterval) (theta : ℝ) : Prop :=
  theta ∈ Icc I.1 I.2
structure Za (n : ℕ) where
  base : Finset RealInterval
  ordered : ∀ I ∈ base, I.1 ≤ I.2
  nondegenerate : ∀ I ∈ base, I.1 < I.2
  in_first_quadrant : ∀ I ∈ base, 0 ≤ I.1 ∧ I.2 ≤ Real.pi / 2
  grid_endpoints : ∀ I ∈ base, ∃ a b : ℤ,
    I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n
  short : ∀ I ∈ base, I.2 - I.1 ≤ 6 * Real.pi / n
  separated : Set.Pairwise ((↑base : Set RealInterval))
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      Real.pi / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ base,
    100 * Real.pi / n ≤ I.1 ∧ I.2 ≤ Real.pi / 2 - 100 * Real.pi / n
def ZaH {n : ℕ} (F : Za n) (theta : ℝ) : Prop :=
  ∃ I ∈ F.base,
    Zal I theta ∨ Zal I (-theta) ∨
      Zal I (Real.pi - theta) ∨ Zal I (theta - Real.pi)
def Zgz {n : ℕ} (F : Za n) (j : Fin n) :
    (↑F.base : Type) → ℝ :=
  fun I ↦ 4 * K * Real.sqrt n *
    ∫ theta in I.1.1..I.1.2,
      Real.sin ((Xq.Rounding.Zl j : ℝ) * theta)
theorem ZkC {n : ℕ} (hn : 0 < n)
    (F : Za n) (j : Fin n) :
    ‖Zgz F j‖ ≤
      24 * K * Real.pi * Real.sqrt n / n := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro I
    rw [Real.norm_eq_abs]
    simp only [Zgz, abs_mul]
    have hintegral :
        ‖∫ theta in I.1.1..I.1.2,
            Real.sin ((Xq.Rounding.Zl j : ℝ) * theta)‖ ≤
          I.1.2 - I.1.1 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := I.1.1) (b := I.1.2) (C := (1 : ℝ))
        (f := fun theta : ℝ ↦
          Real.sin ((Xq.Rounding.Zl j : ℝ) * theta))
        (fun theta htheta ↦ by
          simpa [Real.norm_eq_abs] using
            Real.abs_sin_le_one
              ((Xq.Rounding.Zl j : ℝ) * theta))
      simpa [abs_of_nonneg (sub_nonneg.2 (F.ordered I I.2))] using h
    have hwidth := F.short I I.2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hK : (0 : ℝ) ≤ K := by norm_num [K]
    have hcoefficient : 0 ≤ 4 * K * Real.sqrt n := by positivity
    calc
      |4| * |K| * |Real.sqrt ↑n| *
          |∫ theta in I.1.1..I.1.2,
            Real.sin ((Xq.Rounding.Zl ↑j : ℝ) * theta)| ≤
          (4 * K * Real.sqrt n) * (I.1.2 - I.1.1) := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
              abs_of_nonneg (by norm_num [K] : (0 : ℝ) ≤ K),
              abs_of_nonneg (Real.sqrt_nonneg _)]
            exact mul_le_mul_of_nonneg_left hintegral hcoefficient
      _ ≤ (4 * K * Real.sqrt n) * (6 * Real.pi / n) := by
            exact mul_le_mul_of_nonneg_left hwidth hcoefficient
      _ = 24 * K * Real.pi * Real.sqrt n / n := by ring
  · have hK : (0 : ℝ) ≤ K := by norm_num [K]
    positivity
def ZbJ {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (j : ℕ) : ℝ :=
  if _hj : j < n then
    ∑ I : (↑F.base : Type),
      alpha I * (4 * K * Real.sqrt n *
        ∫ theta in I.1.1..I.1.2,
          Real.sin ((Xq.Rounding.Zl j : ℝ) * theta))
  else 0
theorem Zkj {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (j : Fin n) :
    ZbJ F alpha j = Xq.Discrepancy.dot alpha (Zgz F j) := by
  simp [ZbJ, Zgz, Xq.Discrepancy.dot, j.isLt]
def ZaU {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  Xq.Rounding.ZL n (ZbJ F alpha) theta
structure ZdL {n : ℕ}
    (F : Za n) (c : Fin n → ℝ) : Prop where
  parameter_nonneg : ∀ j, 0 ≤ c j
  budget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
    (Fintype.card (↑F.base : Type) : ℝ) / 16
  unit_error : ∀ j,
    (c j + 30) * Real.sqrt (Fintype.card (↑F.base : Type)) *
      ‖Zgz F j‖ ≤ 1
theorem ZfL {n : ℕ} (hn : 0 < n)
    (F : Za n) (c : Fin n → ℝ)
    (hc : ∀ j, 0 ≤ c j)
    (hbudget : (∑ j, Real.exp (-(c j) ^ 2 / 196)) ≤
      (Fintype.card (↑F.base : Type) : ℝ) / 16)
    (hscalar : ∀ j,
      (c j + 30) * Real.sqrt (Fintype.card (↑F.base : Type)) *
        (24 * K * Real.pi * Real.sqrt n / n) ≤ 1) :
    ZdL F c := by
  refine ⟨hc, hbudget, ?_⟩
  intro j
  have hleft : 0 ≤
      (c j + 30) * Real.sqrt (Fintype.card (↑F.base : Type)) :=
    mul_nonneg (by linarith [hc j]) (Real.sqrt_nonneg _)
  exact (mul_le_mul_of_nonneg_left (ZkC hn F j) hleft).trans
    (hscalar j)
theorem Zjn {n : ℕ} (F : Za n)
    (c : Fin n → ℝ) (hc : ZdL F c)
    (hLM : ∀ (I : Type) [Fintype I] [DecidableEq I],
      Xq.Discrepancy.Zbz I (Fin n)) :
    ∃ alpha : (↑F.base : Type) → ℝ,
      Xq.Discrepancy.Zcw alpha ∧ ∀ j < n, |ZbJ F alpha j| ≤ 1 := by
  classical
  have hzero : Xq.Discrepancy.ZdB (0 : (↑F.base : Type) → ℝ) := by
    intro I
    simp
  obtain ⟨alpha, halpha, herror⟩ :=
    Xq.Discrepancy.ZbI hLM
      (Zgz F) (0 : (↑F.base : Type) → ℝ) c hzero
      hc.parameter_nonneg hc.budget
  refine ⟨alpha, halpha, ?_⟩
  intro j hj
  let jf : Fin n := ⟨j, hj⟩
  rw [Zkj F alpha jf]
  simpa [jf] using (herror jf).trans (hc.unit_error jf)
structure ZcC {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) where
  main : ℝ → ℝ
  error : ℝ → ℝ
  decomposition : ∀ theta,
    ZaU F alpha theta =
      (K * Real.sqrt n) * (main theta + error theta)
  main_lower : ∀ theta, ZaH F theta → 4 / 3 ≤ |main theta|
  main_upper : ∀ theta, |main theta| ≤ 4
  error_bound : ∀ theta, |error theta| ≤ 2 / 3
theorem Zi2 {n : ℕ} (_hn : 0 < n)
    (F : Za n) (alpha : (↑F.base : Type) → ℝ)
    (hkernel : ZcC F alpha) :
    (∀ theta, ZaH F theta →
      (2 * K / 3) * Real.sqrt n ≤ |ZaU F alpha theta|) ∧
    (∀ theta, |ZaU F alpha theta| ≤ 5 * K * Real.sqrt n) := by
  constructor
  · intro theta htheta
    have hnormalized := Xq.KernelClaims.Zi0
      (value := hkernel.main theta + hkernel.error theta)
      (main := hkernel.main theta) (error := hkernel.error theta)
      (hvalue := (rfl : hkernel.main theta + hkernel.error theta =
        hkernel.main theta + hkernel.error theta))
      (hmain_lower := hkernel.main_lower theta htheta)
      (hmain_upper := hkernel.main_upper theta)
      (herror := hkernel.error_bound theta)
    rw [hkernel.decomposition theta, abs_mul]
    have hK : 0 ≤ K := by norm_num [K]
    have hfactor : 0 ≤ K * Real.sqrt n := mul_nonneg hK
      (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hfactor]
    calc
      (2 * K / 3) * Real.sqrt n = (K * Real.sqrt n) * (2 / 3) := by ring
      _ ≤ (K * Real.sqrt n) * |hkernel.main theta + hkernel.error theta| :=
        mul_le_mul_of_nonneg_left hnormalized.1 hfactor
  · intro theta
    have hnormalized : |hkernel.main theta + hkernel.error theta| ≤ 5 := by
      calc
        |hkernel.main theta + hkernel.error theta| ≤
            |hkernel.main theta| + |hkernel.error theta| := abs_add_le _ _
        _ ≤ 4 + 2 / 3 :=
          add_le_add (hkernel.main_upper theta) (hkernel.error_bound theta)
        _ ≤ 5 := by norm_num
    rw [hkernel.decomposition theta, abs_mul]
    have hK : 0 ≤ K := by norm_num [K]
    have hfactor : 0 ≤ K * Real.sqrt n := mul_nonneg hK
      (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hfactor]
    calc
      (K * Real.sqrt n) * |hkernel.main theta + hkernel.error theta|
          ≤ (K * Real.sqrt n) * 5 :=
        mul_le_mul_of_nonneg_left hnormalized hfactor
      _ = 5 * K * Real.sqrt n := by ring
def Zd1 (n l : ℕ) (theta : ℝ) : Fin n → ℝ :=
  fun j ↦
    ((((((Xq.Rounding.Zl j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((Xq.Rounding.Zl j : ℝ) * theta : ℝ) : ℂ) *
        Complex.I))).im
structure ZhD (n : ℕ) (G : Type) [Fintype G] where
  point : G → ℝ
  parameter : G × Fin n → ℝ
  parameter_nonneg : ∀ q, 0 ≤ parameter q
  budget : (∑ q, Real.exp (-(parameter q) ^ 2 / 196)) ≤ (n : ℝ) / 16
  parameter_bound : ∀ g l, parameter (g, l) + 30 ≤ 65 + 2 * (l : ℕ)
  cover : ∀ (a : ℕ → ℝ) (theta : ℝ), ∃ g theta',
    |theta' - point g| ≤ Real.pi / (64 * n) ∧
      |Xq.Rounding.ZL n a theta| =
        |Xq.Rounding.ZL n a theta'|
theorem Zi3 (n l : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Xq.Rounding.ZaE l n a theta =
      Xq.Discrepancy.dot (fun j : Fin n ↦ a j)
        (Zd1 n l theta) := by
  classical
  simp only [Xq.Rounding.ZaE,
    Xq.Rounding.Zap,
    Zd1, Xq.Discrepancy.dot]
  change Complex.imLm
      (∑ j ∈ Finset.range n, (a j : ℂ) *
        (((Xq.Rounding.Zl j : ℝ) : ℂ) * Complex.I) ^ l *
          Complex.exp ((((Xq.Rounding.Zl j : ℝ) * theta : ℝ) : ℂ) *
            Complex.I)) = _
  rw [map_sum Complex.imLm]
  change (∑ j ∈ Finset.range n,
    ((a j : ℂ) *
      (((Xq.Rounding.Zl j : ℝ) : ℂ) * Complex.I) ^ l *
        Complex.exp ((((Xq.Rounding.Zl j : ℝ) * theta : ℝ) : ℂ) *
          Complex.I)).im) = _
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    ((a j : ℂ) *
      (((Xq.Rounding.Zl j : ℝ) : ℂ) * Complex.I) ^ l *
        Complex.exp ((((Xq.Rounding.Zl j : ℝ) * theta : ℝ) : ℂ) *
          Complex.I)).im) n]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, Complex.mul_im]
  simp
theorem Zi4 {n l : ℕ} (theta : ℝ) :
    ‖Zd1 n l theta‖ ≤ (2 * n : ℝ) ^ l := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  rw [Real.norm_eq_abs]
  have him := Complex.abs_im_le_norm
    ((((((Xq.Rounding.Zl j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((Xq.Rounding.Zl j : ℝ) * theta : ℝ) : ℂ) *
        Complex.I)))
  change |((((((Xq.Rounding.Zl j : ℝ) : ℂ) * Complex.I) ^ l) *
      Complex.exp ((((Xq.Rounding.Zl j : ℝ) * theta : ℝ) : ℂ) *
        Complex.I))).im| ≤ _
  refine him.trans ?_
  simp only [norm_mul, norm_pow, Complex.norm_I, mul_one,
      Complex.norm_exp_ofReal_mul_I]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hfreq : (Xq.Rounding.Zl j : ℝ) ≤ 2 * n := by
    exact_mod_cast Xq.Rounding.Zf0
      (Finset.mem_range.2 j.isLt)
  exact pow_le_pow_left₀ (by positivity) hfreq l
theorem ZlC (n : ℕ) (a b : ℕ → ℝ) (theta : ℝ) :
    Xq.Rounding.ZL n (a - b) theta =
      Xq.Rounding.ZL n a theta -
        Xq.Rounding.ZL n b theta := by
  classical
  simp only [Xq.Rounding.ZL, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
theorem ZlD (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Xq.Rounding.ZL n a (-theta) =
      -Xq.Rounding.ZL n a theta := by
  classical
  simp [Xq.Rounding.ZL, mul_neg]
theorem Zi5 (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Xq.Rounding.ZL n a (Real.pi - theta) =
      Xq.Rounding.ZL n a theta := by
  classical
  simp only [Xq.Rounding.ZL]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [mul_sub]
  have hrewrite :
      (Xq.Rounding.Zl j : ℝ) * Real.pi -
          (Xq.Rounding.Zl j : ℝ) * theta =
        (Xq.Rounding.Zl j : ℕ) * Real.pi -
          (Xq.Rounding.Zl j : ℝ) * theta := by
    norm_num
  rw [hrewrite, Real.sin_nat_mul_pi_sub]
  simp [Xq.Rounding.Zl, pow_add]
theorem Zi6 (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    Xq.Rounding.ZL n a (theta + Real.pi) =
      -Xq.Rounding.ZL n a theta := by
  classical
  simp only [Xq.Rounding.ZL, mul_add]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (Xq.Rounding.Zl j : ℝ) * theta +
      (Xq.Rounding.Zl j : ℝ) * Real.pi =
      (Xq.Rounding.Zl j : ℝ) * theta +
        (Xq.Rounding.Zl j : ℕ) * Real.pi by norm_num,
    Real.sin_add_nat_mul_pi]
  simp [Xq.Rounding.Zl, pow_add]
theorem Zb9
    (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    ∃ theta' ∈ Icc (0 : ℝ) (Real.pi / 2),
      |Xq.Rounding.ZL n a theta| =
        |Xq.Rounding.ZL n a theta'| := by
  let x := toIcoMod Real.pi_pos 0 theta
  have hxmem : x ∈ Ico (0 : ℝ) Real.pi := by
    simpa [x] using toIcoMod_mem_Ico Real.pi_pos 0 theta
  have hperiodic : Function.Periodic
      (fun y : ℝ ↦ |Xq.Rounding.ZL n a y|) Real.pi := by
    intro y
    change |Xq.Rounding.ZL n a (y + Real.pi)| =
      |Xq.Rounding.ZL n a y|
    rw [Zi6 n a y, abs_neg]
  have hreduce : |Xq.Rounding.ZL n a theta| =
      |Xq.Rounding.ZL n a x| := by
    have heq := toIcoMod_add_toIcoDiv_zsmul Real.pi_pos 0 theta
    rw [← heq]
    exact hperiodic.zsmul (toIcoDiv Real.pi_pos 0 theta) x
  by_cases hx : x ≤ Real.pi / 2
  · exact ⟨x, ⟨show (0 : ℝ) ≤ x from hxmem.1, hx⟩, hreduce⟩
  · refine ⟨Real.pi - x, ?_, ?_⟩
    · constructor
      · linarith [hxmem.2]
      · linarith
    · rw [hreduce, Zi5]
theorem Zlv {n : ℕ} (hn : 0 < n) {G : Type} [Fintype G]
    (setup : ZhD n G) (hat : ℕ → ℝ)
    (hhat : ∀ j < n, |hat j| ≤ 1)
    (hLM : ∀ (I : Type) [Fintype I] [DecidableEq I],
      Xq.Discrepancy.Zbz I (G × Fin n)) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      ∀ theta,
        |Xq.Rounding.ZL n eps theta -
          Xq.Rounding.ZL n hat theta| ≤
          72 * Real.sqrt n := by
  classical
  let x₀ : Fin n → ℝ := fun j ↦ hat j
  let v : G × Fin n → Fin n → ℝ :=
    fun q ↦ Zd1 n q.2 (setup.point q.1)
  have hx₀ : Xq.Discrepancy.ZdB x₀ := by
    intro j
    exact hhat j j.isLt
  have hbudget : (∑ q, Real.exp (-(setup.parameter q) ^ 2 / 196)) ≤
      (Fintype.card (Fin n) : ℝ) / 16 := by
    simpa using setup.budget
  obtain ⟨epsFin, hepsSign, hepsDisc⟩ :=
    Xq.Discrepancy.ZbI
      hLM v x₀ setup.parameter
      hx₀ setup.parameter_nonneg hbudget
  let eps : ℕ → ℝ := fun j ↦ if hj : j < n then epsFin ⟨j, hj⟩ else 1
  refine ⟨eps, ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · simpa [eps, hj] using hepsSign ⟨j, hj⟩
    · simp [eps, hj]
  · intro theta
    let a : ℕ → ℝ := eps - hat
    obtain ⟨g, theta', hnear, habs⟩ := setup.cover a theta
    have hdisc : ∀ l : ℕ,
        |Xq.Rounding.ZaE l n a (setup.point g)| ≤
          (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l := by
      intro l
      by_cases hl : l < n
      · let lf : Fin n := ⟨l, hl⟩
        have hfull := hepsDisc (g, lf)
        have hdot : Xq.Discrepancy.dot (epsFin - x₀) (v (g, lf)) =
            Xq.Rounding.ZaE l n a (setup.point g) := by
          rw [Zi3]
          apply congrArg (fun z : Fin n → ℝ ↦
            Xq.Discrepancy.dot z (Zd1 n l (setup.point g)))
          funext j
          simp [a, eps, x₀, j.isLt]
        rw [← hdot]
        calc
          |Xq.Discrepancy.dot (epsFin - x₀) (v (g, lf))| ≤
              (setup.parameter (g, lf) + 30) * Real.sqrt n *
                ‖v (g, lf)‖ := by simpa [v] using hfull
          _ ≤ (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_right (setup.parameter_bound g lf)
                (Real.sqrt_nonneg _)
            · simpa [v, lf] using
                (Zi4 (n := n) (l := l) (setup.point g))
            · exact norm_nonneg _
            · exact mul_nonneg (by linarith [setup.parameter_nonneg (g, lf)])
                (Real.sqrt_nonneg _)
      · have hcoeff : ∀ j < n, |a j| ≤ 2 := by
          intro j hj
          have heps : |eps j| = 1 := by
            rcases (show eps j = 1 ∨ eps j = -1 by
              simp only [eps, dif_pos hj]
              exact hepsSign ⟨j, hj⟩) with h | h <;> simp [h]
          calc
            |a j| = |eps j - hat j| := rfl
            _ ≤ |eps j| + |hat j| := abs_sub _ _
            _ ≤ 2 := by linarith [hhat j hj]
        have htrivial :=
          Xq.Rounding.Zf1 l n a 2 hcoeff
          (by norm_num) (setup.point g)
        have hsqrt : 1 ≤ Real.sqrt n := by
          rw [Real.one_le_sqrt]
          exact_mod_cast hn
        have hln : n ≤ l := Nat.le_of_not_gt hl
        calc
          |Xq.Rounding.ZaE l n a (setup.point g)| ≤
              n * 2 * (2 * n : ℝ) ^ l := htrivial
          _ ≤ (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : (n : ℝ) ≤ l := by exact_mod_cast hln
            nlinarith
    have hround := Xq.Rounding.ZfK hn a
      (setup.point g) theta' hnear hdisc
    rw [← ZlC] at ⊢
    rw [habs]
    exact hround
end
end Xq.OddSine
end
section
namespace Xq
end Xq
end
section
namespace Xq.CosineConstruction
open Set
open scoped BigOperators
noncomputable section
def Zp (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1
def ZdM (gamma : ℝ) : ℝ :=
  (1 / 2 ^ 8 : ℝ) * gamma ^ 3 * Real.sqrt gamma
def Ze (n : ℕ) (gamma : ℝ) : ℝ :=
  ZdM gamma * Real.sqrt n
structure Parameters (n t : ℕ) (gamma : ℝ) : Prop where
  n_pos : 0 < n
  t_odd : Odd t
  equation : gamma * n = Zp t
  gamma_lower : (1 / 2 ^ 43 : ℝ) < gamma
  gamma_upper : gamma ≤ (1 / 2 ^ 40 : ℝ)
theorem Parameters.gamma_pos {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : 0 < gamma := by
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / 2 ^ 43) h.gamma_lower.le
theorem Zlw {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < ZdM gamma := by
  simp only [ZdM]
  positivity
theorem ZhU {n : ℕ} {gamma : ℝ}
    (hn : 0 < n) (hgamma : 0 < gamma) : 0 < Ze n gamma := by
  simp only [Ze]
  exact mul_pos (Zlw hgamma) (Real.sqrt_pos.2 (by exact_mod_cast hn))
theorem Parameters.Zjz {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : ZaM n t gamma where
  t_odd := h.t_odd
  gamma_pos := h.gamma_pos
  gamma_le := h.gamma_upper
  equation := by simpa [Zp, ZbH] using h.equation
theorem Parameters.Zet {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    0 < 2 * (Zt t : ℝ) * Real.pi / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTR : (0 : ℝ) < Zt t := by
    exact_mod_cast (show 0 < Zt t by simp [Zt])
  exact div_pos (mul_pos (mul_pos (by norm_num) hTR) Real.pi_pos) hnR
theorem Parameters.Zmv {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    2 * (Zt t : ℝ) * Real.pi / n < 1 / 2048 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTle : (2 * Zt t : ℝ) ≤ gamma * n := by
    rw [h.equation]
    exact_mod_cast (show 2 * Zt t ≤ Zp t by
      rw [Zp, ZcY]
      have hp : 0 < 2 ^ t := by positivity
      omega)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hgam : gamma ≤ 1 / 2 ^ 40 := h.gamma_upper
  have hgamma : 0 < gamma := h.gamma_pos
  calc
    2 * (Zt t : ℝ) * Real.pi / n ≤
        (gamma * n) * Real.pi / n := by
      gcongr
    _ = gamma * Real.pi := by field_simp
    _ < gamma * 4 := by gcongr
    _ ≤ (1 / 2 ^ 40 : ℝ) * 4 := by gcongr
    _ < 1 / 2048 := by norm_num
theorem Parameters.Zl6 {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    (15 / 16 : ℝ) * (gamma * n) < 2 * Zt t := by
  rw [h.equation]
  have hnat : 15 * Zp t < 16 * (2 * Zt t) := by
    rw [Zp, Zt]
    have hp : 0 < 2 ^ t := by positivity
    rw [show 2 ^ (t + 11) = 2 ^ t * 2 ^ 11 by rw [pow_add],
      show 2 ^ (t + 10) = 2 ^ t * 2 ^ 10 by rw [pow_add]]
    norm_num
    omega
  have hreal : (15 : ℝ) * Zp t < 16 * (2 * Zt t) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  nlinarith
private theorem ZkU (t : ℕ) :
    Real.sqrt (2 * (Zt t : ℝ)) =
      32 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have hpow : (2 * (Zt t : ℝ)) = (2 ^ (t + 1) : ℝ) * 32 ^ 2 := by
    norm_num [Zt, pow_add]
    ring
  rw [hpow, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ (t + 1)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
  ring
theorem Parameters.ZhE {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    Ze n gamma ≤
      Real.sqrt (2 ^ (t + 1) : ℝ) *
        (2 * (Zt t : ℝ) * Real.pi / n) ^ 3 / 128 := by
  let A : ℝ := gamma * n
  let B : ℝ := 2 * Zt t
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hgamma : 0 < gamma := h.gamma_pos
  have hA : 0 < A := mul_pos hgamma hnR
  have hB : 0 < B := by
    dsimp [B]
    have hT : (0 : ℝ) < Zt t := by
      exact_mod_cast (show 0 < Zt t by simp [Zt])
    positivity
  have hratio : (15 / 16 : ℝ) * A < B := by
    simpa [A, B] using h.Zl6
  have hratioSq : (15 / 16 : ℝ) ^ 2 * A < B := by
    have : (15 / 16 : ℝ) ^ 2 < 15 / 16 := by norm_num
    nlinarith
  have hsqrtRatio : (15 / 16 : ℝ) * Real.sqrt A < Real.sqrt B := by
    have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
    have hsA2 : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
    have hsB2 : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
    nlinarith
  have hcubes : (15 / 16 : ℝ) ^ 3 * A ^ 3 < B ^ 3 := by
    have hp := pow_lt_pow_left₀ hratio
      (mul_nonneg (by norm_num) hA.le) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [mul_pow] using hp
  have hprod : (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) <
      B ^ 3 * Real.sqrt B := by
    have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    have hrpos : (0 : ℝ) < 15 / 16 := by norm_num
    have hm := mul_lt_mul hcubes hsqrtRatio.le
      (mul_pos hrpos hsApos) (pow_nonneg hB.le 3)
    calc
      (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) =
          ((15 / 16 : ℝ) ^ 3 * A ^ 3) *
            ((15 / 16 : ℝ) * Real.sqrt A) := by ring
      _ < B ^ 3 * Real.sqrt B := hm
  have hnumeric : (16 : ℝ) < 3 ^ 3 * (15 / 16 : ℝ) ^ 4 := by norm_num
  have hpiCube : (3 : ℝ) ^ 3 < Real.pi ^ 3 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have hmain : 16 * (A ^ 3 * Real.sqrt A) <
      Real.pi ^ 3 * (B ^ 3 * Real.sqrt B) := by
    have hAprodpos : 0 < A ^ 3 * Real.sqrt A :=
      mul_pos (pow_pos hA 3) (Real.sqrt_pos.2 hA)
    have hrprodpos : 0 < (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) := by
      positivity
    have hpiCubePos : 0 < Real.pi ^ 3 := pow_pos Real.pi_pos 3
    calc
      16 * (A ^ 3 * Real.sqrt A) <
          (3 ^ 3 * (15 / 16 : ℝ) ^ 4) * (A ^ 3 * Real.sqrt A) := by
        exact mul_lt_mul_of_pos_right hnumeric hAprodpos
      _ = 3 ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A)) := by ring
      _ < Real.pi ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A)) :=
        mul_lt_mul_of_pos_right hpiCube hrprodpos
      _ < Real.pi ^ 3 * (B ^ 3 * Real.sqrt B) :=
        mul_lt_mul_of_pos_left hprod hpiCubePos
  have hsqrtA : Real.sqrt A = Real.sqrt gamma * Real.sqrt n := by
    dsimp [A]
    rw [Real.sqrt_mul (le_of_lt hgamma)]
  have hsqrtB : Real.sqrt B = 32 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    simpa [B] using ZkU t
  have hscaled :
      (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n <
        Real.sqrt (2 ^ (t + 1) : ℝ) *
          (B * Real.pi / n) ^ 3 / 128 := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hlhs :
        (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n =
          (16 * (A ^ 3 * Real.sqrt A)) / (4096 * n ^ 3) := by
      calc
        (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n =
            (1 / 256 : ℝ) * gamma ^ 3 *
              (Real.sqrt gamma * Real.sqrt n) := by ring
        _ = (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt A := by rw [← hsqrtA]
        _ = (16 * (A ^ 3 * Real.sqrt A)) / (4096 * n ^ 3) := by
          dsimp [A]
          field_simp [hn0]
          ring
    have hs : Real.sqrt (2 ^ (t + 1) : ℝ) = Real.sqrt B / 32 := by
      rw [hsqrtB]
      ring
    have hrhs :
        Real.sqrt (2 ^ (t + 1) : ℝ) * (B * Real.pi / n) ^ 3 / 128 =
          (Real.pi ^ 3 * (B ^ 3 * Real.sqrt B)) / (4096 * n ^ 3) := by
      rw [hs]
      field_simp [hn0]
      ring
    rw [hlhs, hrhs]
    exact div_lt_div_of_pos_right hmain (by positivity)
  norm_num [Ze, ZdM, B] at hscaled ⊢
  exact hscaled.le
def Zas (t : ℕ) : ℝ := (Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹
def Zq (r t : ℕ) (x : ℝ) : ℂ :=
  (Zas t : ℂ) *
    (Complex.I / (Zt t : ℝ)) ^ r *
      ((Xq.Bernstein.Zar^[r]) (rudinShapiroP t)).eval
        (Zd (x / Zt t))
def Zr (r t : ℕ) (x : ℝ) : ℂ :=
  (Zas t : ℂ) *
    (Complex.I / (Zt t : ℝ)) ^ r *
      ((Xq.Bernstein.Zar^[r]) (rudinShapiroQ t)).eval
        (Zd (x / Zt t))
def ZE (t : ℕ) (x : ℝ) : ℂ :=
  Zd x * Zq 0 t x +
    Zd (2 * x) * Zr 0 t x
theorem ZfA (t : ℕ) : 0 < Zas t := by
  simp only [Zas]
  positivity
theorem Zk7 (t : ℕ) (x : ℝ) :
    ‖Zq 0 t x‖ ^ 2 +
      ‖Zr 0 t x‖ ^ 2 = 1 := by
  have henergy := Zfw t (Zbv (x / Zt t))
  have hEpos : (0 : ℝ) < (2 ^ (t + 1) : ℝ) := by positivity
  have hspos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_pos.2 hEpos
  have hsquare := Real.sq_sqrt hEpos.le
  simp only [Zq, Zr, pow_zero,
    Function.iterate_zero_apply, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ZfA t)]
  rw [show
    (Zas t * 1 * ‖(rudinShapiroP t).eval (Zd (x / Zt t))‖) ^ 2 +
      (Zas t * 1 * ‖(rudinShapiroQ t).eval (Zd (x / Zt t))‖) ^ 2 =
      Zas t ^ 2 *
        (‖(rudinShapiroP t).eval (Zd (x / Zt t))‖ ^ 2 +
          ‖(rudinShapiroQ t).eval (Zd (x / Zt t))‖ ^ 2) by ring,
    henergy]
  simp only [Zas]
  field_simp
  exact hsquare.symm
private theorem ZeV
    (p : Polynomial ℂ) (t r : ℕ) (x : ℝ)
    (hdeg : p.natDegree ≤ 2 ^ t)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 →
      ‖p.eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ)) :
    ‖(Zas t : ℂ) *
        (Complex.I / (Zt t : ℝ)) ^ r *
        ((Xq.Bernstein.Zar^[r]) p).eval
          (Zd (x / Zt t))‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  have heuler :=
    Xq.Bernstein.Zci
      hdeg hcircle r (Zbv (x / Zt t))
  have hTnat : 0 < Zt t := by simp [Zt]
  have hTpos : (0 : ℝ) < Zt t := by exact_mod_cast hTnat
  have hspos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hpowcast : ((2 ^ t : ℕ) : ℝ) / Zt t = 1 / 2 ^ 10 := by
    rw [Zhb]
    push_cast
    field_simp
    norm_num
  have hnonneg : 0 ≤ (1 / (Zt t : ℝ)) ^ r := by positivity
  calc
    ‖(Zas t : ℂ) *
        (Complex.I / (Zt t : ℝ)) ^ r *
        ((Xq.Bernstein.Zar^[r]) p).eval
          (Zd (x / Zt t))‖ =
      Zas t * (1 / (Zt t : ℝ)) ^ r *
        ‖((Xq.Bernstein.Zar^[r]) p).eval
          (Zd (x / Zt t))‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_I]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (ZfA t), abs_of_pos hTpos, one_div]
    _ ≤ Zas t * (1 / (Zt t : ℝ)) ^ r *
        (((2 ^ t : ℕ) : ℝ) ^ r * Real.sqrt (2 ^ (t + 1) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left heuler
        (mul_nonneg (ZfA t).le hnonneg)
    _ = (((2 ^ t : ℕ) : ℝ) / Zt t) ^ r := by
      rw [Zas]
      field_simp
      ring
    _ = (1 / 2 ^ 10 : ℝ) ^ r := by rw [hpowcast]
theorem Zd2 (r t : ℕ) (x : ℝ) :
    ‖Zq r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply ZeV (rudinShapiroP t) t r x
  · rw [Zjj]
    exact Nat.sub_le _ _
  · intro z hz
    exact ZbR t hz
theorem Zd3 (r t : ℕ) (x : ℝ) :
    ‖Zr r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply ZeV (rudinShapiroQ t) t r x
  · rw [Zjk]
    exact Nat.sub_le _ _
  · intro z hz
    exact ZeU t hz
theorem Za9 (t : ℕ) (theta : ℝ) :
    Zo t theta =
      Real.sqrt (2 ^ (t + 1) : ℝ) * (ZE t (2 * Zt t * theta)).re := by
  have hTnat : 0 < Zt t := by simp [Zt]
  have hT : (Zt t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  have hs : Real.sqrt (2 ^ (t + 1) : ℝ) ≠ 0 := by positivity
  have hdiv : (2 * (Zt t : ℝ) * theta) / Zt t = 2 * theta := by
    field_simp [hT]
  have hphase₁ : Zd (2 * (Zt t : ℝ) * theta) =
      Zd (2 * theta) ^ Zt t := by
    simp only [Zd, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hphase₂ : Zd (2 * (2 * (Zt t : ℝ) * theta)) =
      Zd (2 * theta) ^ (2 * Zt t) := by
    simp only [Zd, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [ZkO]
  simp only [ZE, Zq, Zr, pow_zero,
    mul_one, Function.iterate_zero_apply, hdiv, hphase₁, hphase₂, Zas]
  rw [show
    Zd (2 * theta) ^ Zt t *
          ((((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroP t).eval (Zd (2 * theta))) +
      Zd (2 * theta) ^ (2 * Zt t) *
          ((((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroQ t).eval (Zd (2 * theta))) =
      (((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
        (Zd (2 * theta) ^ Zt t *
            (rudinShapiroP t).eval (Zd (2 * theta)) +
          Zd (2 * theta) ^ (2 * Zt t) *
            (rudinShapiroQ t).eval (Zd (2 * theta))) by ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp
private theorem Zcq {t k : ℕ}
    (hk : k ∈ (Zn t).support) :
    ((Zn t).coeff k).im = 0 := by
  rw [Zax] at hk
  rw [ZaA] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [ZaK t j hj]
    rcases Zac hj with h | h <;> simp [h]
  · rw [Zav t j hj]
    rcases Zad hj with h | h <;> simp [h]
theorem ZcZ (t : ℕ) (theta : ℝ) :
    Zo t theta =
      ∑ k ∈ (Zn t).support,
        ((Zn t).coeff k).re * Real.cos (k * (2 * theta)) := by
  classical
  rw [Zo, Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.reLm
      (∑ k ∈ (Zn t).support,
        (Zn t).coeff k * Zd (2 * theta) ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hre : (Zd (2 * theta) ^ k).re = Real.cos (k * (2 * theta)) := by
    have h := congrArg Complex.re (Xq.ZdG (2 * theta) k)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change ((Zn t).coeff k * Zd (2 * theta) ^ k).re = _
  rw [Complex.mul_re, Zcq hk, zero_mul, sub_zero, hre]
@[simp] theorem ZlE (t : ℕ) (theta : ℝ) :
    Zo t (-theta) = Zo t theta := by
  classical
  rw [ZcZ, ZcZ]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * -theta) = -((k : ℝ) * (2 * theta)) by ring,
    Real.cos_neg]
@[simp] theorem Zk8 (t : ℕ) (theta : ℝ) :
    Zo t (Real.pi - theta) = Zo t theta := by
  classical
  rw [ZcZ, ZcZ]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * (Real.pi - theta)) =
      (k : ℝ) * (2 * Real.pi) - (k : ℝ) * (2 * theta) by ring,
    Real.cos_nat_mul_two_pi_sub]
@[simp] theorem Zme (t : ℕ) (theta : ℝ) :
    Zo t (theta - Real.pi) = Zo t theta := by
  rw [show theta - Real.pi = -(Real.pi - theta) by ring, ZlE,
    Zk8]
def ZdN (f : ℝ → ℝ) (eta : ℝ) : Prop :=
  ∀ a : ℝ, ∃ j : ℕ, j < 7 ∧
    ∀ x ∈ Icc (a + (j : ℝ) * eta) (a + ((j : ℝ) + 1) * eta),
    eta ^ 3 / 128 ≤ |f x|
theorem Zdu
    (f : ℝ → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hf : ContDiff ℝ 4 f)
    (hlarge : ∀ x, ∃ k : Fin 4, 1 / 4 ≤ |iteratedDeriv k f x|)
    (hderiv : ∀ r ≤ 4, ∀ x, |iteratedDeriv r f x| ≤ 18) :
    ZdN f eta := by
  intro a
  by_contra hnone
  push Not at hnone
  have hsample (j : Fin 7) :
      ∃ x ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta),
        |f x| < eta ^ 3 / 128 := by
    exact hnone (j : ℕ) j.isLt
  let sample : Fin 7 → ℝ := fun j ↦ Classical.choose (hsample j)
  have sample_mem (j : Fin 7) :
      sample j ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta) :=
    (Classical.choose_spec (hsample j)).1
  have sample_small (j : Fin 7) : |f (sample j)| < eta ^ 3 / 128 :=
    (Classical.choose_spec (hsample j)).2
  obtain ⟨k, hklarge⟩ := hlarge (sample 0)
  by_cases hk0 : (k : ℕ) = 0
  · have hsmall := sample_small (0 : Fin 7)
    simp only [hk0, iteratedDeriv_zero] at hklarge
    have hetaOne : eta < 1 := lt_trans hetaSmall (by norm_num)
    have hetaCube : eta ^ 3 < 1 := pow_lt_one₀ heta.le hetaOne (by norm_num)
    norm_num at hsmall hklarge
    nlinarith
  · have hk₁ : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
    have hk₃ : (k : ℕ) ≤ 3 := by omega
    let node : Fin ((k : ℕ) + 1) → ℝ := fun i ↦
      sample ⟨2 * (i : ℕ), by omega⟩
    have hnode_mem (i : Fin ((k : ℕ) + 1)) :
        node i ∈ Icc (a + (2 * (i : ℕ)) * eta)
          (a + (2 * (i : ℕ) + 1) * eta) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (sample_mem ⟨2 * (i : ℕ), by omega⟩)
    have hnode_mono : StrictMono node := by
      intro i j hij
      have hi := hnode_mem i
      have hj := hnode_mem j
      have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
      dsimp only [node]
      have hgap : a + (2 * (i : ℕ) + 1) * eta <
          a + (2 * (j : ℕ)) * eta := by
        have : (2 * (i : ℕ) + 1 : ℝ) < 2 * (j : ℕ) := by exact_mod_cast (by omega)
        nlinarith
      exact hi.2.trans_lt (hgap.trans_le hj.1)
    have hnode_sep : ∀ i j, i ≠ j → eta ≤ |node i - node j| := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hijlt
        rw [abs_of_nonpos (sub_nonpos.mpr (hnode_mono hijlt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (i : ℕ) + 1) * eta + eta ≤
            a + (2 * (j : ℕ)) * eta := by
          have : (2 * (i : ℕ) + 2 : ℝ) ≤ 2 * (j : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hi.2, hj.1]
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hjiNat : (j : ℕ) < (i : ℕ) := by exact_mod_cast hjilt
        rw [abs_of_nonneg (sub_nonneg.mpr (hnode_mono hjilt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (j : ℕ) + 1) * eta + eta ≤
            a + (2 * (i : ℕ)) * eta := by
          have : (2 * (j : ℕ) + 2 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hj.2, hi.1]
    have hnode_dist (i : Fin ((k : ℕ) + 1)) :
        |node i - sample 0| ≤ 7 * eta := by
      have hi := hnode_mem i
      have h0 := sample_mem (0 : Fin 7)
      have hleft : sample 0 ≤ node i := by
        by_cases hi0 : (i : ℕ) = 0
        · apply le_of_eq
          have hieq : i = 0 := Fin.ext hi0
          subst i
          apply congrArg sample
          exact Fin.ext rfl
        · have hiPos : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr hi0
          have hgap : a + eta ≤ a + (2 * (i : ℕ)) * eta := by
            have : (1 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
            nlinarith
          norm_num at h0
          exact h0.2.trans (hgap.trans hi.1)
      rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
      have hik : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hupper : node i ≤ a + 7 * eta := by
        calc
          node i ≤ a + (2 * (i : ℕ) + 1) * eta := hi.2
          _ ≤ a + 7 * eta := by
            have : (2 * (i : ℕ) + 1 : ℝ) ≤ 7 := by exact_mod_cast (by omega)
            nlinarith
      norm_num at h0
      linarith [h0.1]
    have hnode_value (i : Fin ((k : ℕ) + 1)) :
        |f (node i)| ≤ eta ^ 3 / 128 := by
      have hiLe : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hkLt : (k : ℕ) < 4 := k.isLt
      have hidx : 2 * (i : ℕ) < 7 := by omega
      exact (sample_small ⟨2 * (i : ℕ), hidx⟩).le
    have hk4 : (k : ℕ) + 1 ≤ 4 := by omega
    have hquarter := Xq.Interpolation.Zib
      (k : ℕ) hk₁ hk₃ f node (sample 0) eta
      (hf.of_le (by exact_mod_cast hk4)) hnode_mono heta hetaSmall hnode_sep hnode_dist
      hnode_value
      (fun x ↦ hderiv ((k : ℕ) + 1) hk4 x)
    linarith
def Zcr (n t : ℕ) (gamma : ℝ) (i : ℕ) : Prop :=
  ∃ theta ∈ Xq.Intervals.Zln n i,
    |Zo t theta| < Ze n gamma
noncomputable instance ZlI (n t : ℕ) (gamma : ℝ) :
    DecidablePred (Zcr n t gamma) := Classical.decPred _
noncomputable def Zcs (n t : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  @Xq.Intervals.Ziy (2 * n) (Zcr n t gamma)
    (Classical.decPred _)
@[simp] theorem ZJ {n t : ℕ} {gamma : ℝ} {a b : ℕ} :
    (a, b) ∈ Zcs n t gamma ↔
      Xq.Intervals.Zay (2 * n) (Zcr n t gamma) a b := by
  classical
  exact Xq.Intervals.Zin
def Zbt (n : ℕ) (I : ℕ × ℕ) : Xq.OddSine.RealInterval :=
  (Xq.Intervals.Zz n I.1,
    Xq.Intervals.Zz n (I.2 + 1))
noncomputable def ZaF (n t : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  (Zcs n t gamma).filter fun I ↦ 2 * (I.2 + 1) ≤ n
noncomputable def ZaP (n t : ℕ) (gamma : ℝ) :
    Finset Xq.OddSine.RealInterval :=
  (ZaF n t gamma).image (Zbt n)
@[simp] theorem Zy {n t : ℕ} {gamma : ℝ} {I : ℕ × ℕ} :
    I ∈ ZaF n t gamma ↔
      I ∈ Zcs n t gamma ∧ 2 * (I.2 + 1) ≤ n := by
  classical
  simp [ZaF]
theorem ZjI {n : ℕ} (hn : 0 < n) :
    Function.Injective (Zbt n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Zbt, Prod.mk.injEq] at h
  have hstrict := Xq.Intervals.Zcj hn
  have hac : a = c := hstrict.injective h.1
  have hbd : b + 1 = d + 1 := hstrict.injective h.2
  simp only [Prod.mk.injEq]
  exact ⟨hac, Nat.succ.inj hbd⟩
theorem ZhV {n t : ℕ} {gamma : ℝ} (hn : 0 < n) :
    (ZaP n t gamma).card =
      (ZaF n t gamma).card := by
  classical
  exact Finset.card_image_of_injective _ (ZjI hn)
def ZbA (n t : ℕ) (gamma : ℝ) : Prop :=
  ∀ a, a + 7 ≤ 2 * n →
    ∃ j < 7, ¬Zcr n t gamma (a + j)
theorem Zfi
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hgood : ZdN (fun x ↦ (ZE t x).re)
      (2 * (Zt t : ℝ) * Real.pi / n)) :
    ZbA n t gamma := by
  intro a ha
  let eta : ℝ := 2 * (Zt t : ℝ) * Real.pi / n
  obtain ⟨j, hj, hcell⟩ := hgood (a * eta)
  refine ⟨j, hj, ?_⟩
  rintro ⟨theta, htheta, hsmall⟩
  let x : ℝ := 2 * Zt t * theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hT : (0 : ℝ) < Zt t := by
    exact_mod_cast (show 0 < Zt t by simp [Zt])
  have hx : x ∈ Icc (a * eta + (j : ℝ) * eta)
      (a * eta + ((j : ℝ) + 1) * eta) := by
    rcases htheta with ⟨hthetaL, hthetaR⟩
    simp only [Xq.Intervals.Zz] at hthetaL hthetaR
    dsimp [x, eta]
    constructor <;> push_cast at * <;>
      (field_simp [ne_of_gt hnR] at hthetaL hthetaR ⊢; nlinarith [Real.pi_pos])
  have hnorm : eta ^ 3 / 128 ≤ |(ZE t x).re| := by
    simpa [eta] using hcell x hx
  have hsqrt : 0 ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_nonneg _
  have hlower : Ze n gamma ≤
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(ZE t x).re| := by
    calc
      Ze n gamma ≤
          Real.sqrt (2 ^ (t + 1) : ℝ) * eta ^ 3 / 128 := by
        simpa [eta] using hparam.ZhE
      _ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) * |(ZE t x).re| := by
        have := mul_le_mul_of_nonneg_left hnorm hsqrt
        nlinarith
  have heq : |Zo t theta| =
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(ZE t x).re| := by
    rw [Za9]
    dsimp [x]
    rw [abs_mul, abs_of_nonneg hsqrt]
  rw [← heq] at hlower
  exact (not_lt_of_ge hlower) hsmall
theorem Zif {n t : ℕ} {gamma : ℝ}
    (hseven : ZbA n t gamma) {a b : ℕ}
    (hab : (a, b) ∈ Zcs n t gamma) :
    b + 1 - a ≤ 6 := by
  classical
  rw [ZJ] at hab
  by_contra hlong
  have hab7 : a + 7 ≤ b + 1 := by omega
  have hbN : b < 2 * n := hab.2.1
  have ha7N : a + 7 ≤ 2 * n := by omega
  obtain ⟨j, hj, hgood⟩ := hseven a ha7N
  apply hgood
  exact hab.2.2.1 (a + j) (Finset.mem_range.mpr (by omega)) (by omega) (by omega)
theorem ZjY {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n) (hseven : ZbA n t gamma) {I : ℕ × ℕ}
    (hI : I ∈ Zcs n t gamma) :
    Xq.Intervals.Zz n (I.2 + 1) -
        Xq.Intervals.Zz n I.1 ≤ 6 * Real.pi / n := by
  rcases I with ⟨a, b⟩
  have hlen := Zif hseven hI
  simp only [Xq.Intervals.Zz]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : a ≤ b + 1 := by
    rw [ZJ] at hI
    exact hI.1.trans (Nat.le_succ b)
  have hcast : ((b + 1 - a : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hlen
  rw [Nat.cast_sub hba] at hcast
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hnR).2
  nlinarith [Real.pi_pos]
theorem Zct {n t : ℕ} {gamma : ℝ} {a b c d : ℕ}
    (h₁ : (a, b) ∈ Zcs n t gamma)
    (h₂ : (c, d) ∈ Zcs n t gamma)
    (hbc : b < c) : b + 2 ≤ c := by
  classical
  rw [ZJ] at h₁ h₂
  by_contra h
  have hc : c = b + 1 := by omega
  have hcN : c < 2 * n := h₂.1.trans_lt h₂.2.1
  have hbadc := h₂.2.2.1 c (Finset.mem_range.mpr hcN) le_rfl h₂.1
  rcases h₁.2.2.2.2 with hright | hgood
  · rw [hc, hright] at hcN
    omega
  · exact hgood (by simpa [hc] using hbadc)
structure ZbL (n t : ℕ) (gamma : ℝ) : Prop where
  separated : Set.Pairwise
    (↑(ZaP n t gamma) :
      Set Xq.OddSine.RealInterval)
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      Real.pi / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ ZaP n t gamma,
    100 * Real.pi / n ≤ I.1 ∧
      I.2 ≤ Real.pi / 2 - 100 * Real.pi / n
def Zbq
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hseven : ZbA n t gamma)
    (hgeom : ZbL n t gamma) :
    Xq.OddSine.Za n where
  base := ZaP n t gamma
  ordered := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [Zy] at hJ
    rcases J with ⟨a, b⟩
    simp only [Zbt]
    apply Xq.Intervals.ZbE hn
    rw [ZJ] at hJ
    exact Nat.le_succ_of_le hJ.1.1
  nondegenerate := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [Zy] at hJ
    rcases J with ⟨a, b⟩
    simp only [Zbt]
    apply Xq.Intervals.Zcj hn
    rw [ZJ] at hJ
    exact Nat.lt_succ_of_le hJ.1.1
  in_first_quadrant := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [Zy] at hJ
    rcases J with ⟨a, b⟩
    simp only [Zbt]
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
        (Nat.cast_nonneg _)
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hidx : (2 * (b + 1) : ℝ) ≤ n := by exact_mod_cast hJ.2
      simp only [Xq.Intervals.Zz]
      norm_num [Nat.cast_add]
      apply (div_le_iff₀ hnR).2
      have hmul := mul_le_mul_of_nonneg_right hidx Real.pi_pos.le
      nlinarith
  grid_endpoints := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rcases J with ⟨a, b⟩
    exact ⟨a, b + 1, by simp [Zbt, Xq.Intervals.Zz],
      by simp [Zbt, Xq.Intervals.Zz]⟩
  short := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [Zy] at hJ
    simpa only [Zbt] using ZjY hn hseven hJ.1
  separated := hgeom.separated
  away_from_axes := hgeom.away_from_axes
def ZgT {n : ℕ} (F : Xq.OddSine.Za n)
    (theta : ℝ) : Prop :=
  ∃ I ∈ F.base, Xq.OddSine.Zal I theta
theorem ZeH
    {n t : ℕ} {gamma : ℝ} (F : Xq.OddSine.Za n)
    (hfirst : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ¬ZgT F theta →
        Ze n gamma ≤ |Zo t theta|) :
    ∀ theta ∈ Icc (-Real.pi / 2) (3 * Real.pi / 2),
      ¬Xq.OddSine.ZaH F theta →
        Ze n gamma ≤ |Zo t theta| := by
  intro theta htheta hout
  rcases htheta with ⟨hthetaLower, hthetaUpper⟩
  by_cases h0 : theta ≤ 0
  · have hphi : -theta ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith
    have hbase : ¬ZgT F (-theta) := by
      rintro ⟨I, hI, hmem⟩
      exact hout ⟨I, hI, Or.inr (Or.inl hmem)⟩
    simpa using hfirst (-theta) hphi hbase
  · have htheta0 : 0 ≤ theta := le_of_not_ge h0
    by_cases hhalf : theta ≤ Real.pi / 2
    · exact hfirst theta ⟨htheta0, hhalf⟩ fun hbase ↦ by
        rcases hbase with ⟨I, hI, hmem⟩
        exact hout ⟨I, hI, Or.inl hmem⟩
    · have hhalf' : Real.pi / 2 ≤ theta := le_of_not_ge hhalf
      by_cases hpi : theta ≤ Real.pi
      · have hphi : Real.pi - theta ∈ Icc (0 : ℝ) (Real.pi / 2) := by
          constructor <;> linarith
        have hbase : ¬ZgT F (Real.pi - theta) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inl hmem))⟩
        simpa using hfirst (Real.pi - theta) hphi hbase
      · have hpi' : Real.pi ≤ theta := le_of_not_ge hpi
        have hphi : theta - Real.pi ∈ Icc (0 : ℝ) (Real.pi / 2) := by
          constructor <;> linarith
        have hbase : ¬ZgT F (theta - Real.pi) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inr hmem))⟩
        simpa using hfirst (theta - Real.pi) hphi hbase
theorem Zi7
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hseven : ZbA n t gamma)
    (hgeom : ZbL n t gamma) :
    (Zbq hn hseven hgeom).base.card =
      (ZaF n t gamma).card :=
  ZhV hn
end
end Xq.CosineConstruction
end
section
namespace Xq.CosineConstruction
open scoped BigOperators
noncomputable section
private theorem Ze2 (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Zd (c * y))
      ((c : ℂ) * Complex.I * Zd (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ ((c : ℂ) * Complex.I) * (y : ℂ))
      ((c : ℂ) * Complex.I) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul
      ((c : ℂ) * Complex.I)
  simpa only [Zd, Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm] using
    hinner.cexp
private theorem Zgj (r t : ℕ) (x : ℝ) :
    HasDerivAt (Zq r t)
      (Zq (r + 1) t x) x := by
  have hTnat : 0 < Zt t := by simp [Zt]
  have hT : (Zt t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (Xq.Bernstein.Zar^[r]) (rudinShapiroP t)
  have hunit : HasDerivAt (fun y : ℝ ↦ Zd (y / Zt t))
      ((Complex.I / (Zt t : ℝ)) * Zd (x / Zt t)) x := by
    convert Ze2 (1 / Zt t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (Zd (x / Zt t))).comp x hunit
  let C : ℂ := (Zas t : ℂ) * (Complex.I / (Zt t : ℝ)) ^ r
  have hfun : Zq r t =
      fun y ↦ C * p.eval (Zd (y / Zt t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : Zq (r + 1) t x =
      C * (p.derivative.eval (Zd (x / Zt t)) *
        ((Complex.I / (Zt t : ℝ)) * Zd (x / Zt t))) := by
    unfold Zq
    rw [Function.iterate_succ_apply', Xq.Bernstein.Ze0,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C
private theorem Zgk (r t : ℕ) (x : ℝ) :
    HasDerivAt (Zr r t)
      (Zr (r + 1) t x) x := by
  have hTnat : 0 < Zt t := by simp [Zt]
  have hT : (Zt t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (Xq.Bernstein.Zar^[r]) (rudinShapiroQ t)
  have hunit : HasDerivAt (fun y : ℝ ↦ Zd (y / Zt t))
      ((Complex.I / (Zt t : ℝ)) * Zd (x / Zt t)) x := by
    convert Ze2 (1 / Zt t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (Zd (x / Zt t))).comp x hunit
  let C : ℂ := (Zas t : ℂ) * (Complex.I / (Zt t : ℝ)) ^ r
  have hfun : Zr r t =
      fun y ↦ C * p.eval (Zd (y / Zt t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : Zr (r + 1) t x =
      C * (p.derivative.eval (Zd (x / Zt t)) *
        ((Complex.I / (Zt t : ℝ)) * Zd (x / Zt t))) := by
    unfold Zr
    rw [Function.iterate_succ_apply', Xq.Bernstein.Ze0,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C
private theorem Zbu (c : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ Zd (c * x)) := by
  have hr : ContDiff ℝ ⊤ (fun x : ℝ ↦ c * x) := contDiff_const.mul contDiff_id
  have hc : ContDiff ℝ ⊤ (fun x : ℝ ↦ ((c * x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  unfold Zd
  exact (hc.mul contDiff_const).cexp
theorem ZdD (r t : ℕ) :
    ContDiff ℝ ⊤ (Zq r t) := by
  let p := (Xq.Bernstein.Zar^[r]) (rudinShapiroP t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ Zd (x / Zt t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      Zbu ((Zt t : ℝ)⁻¹)
  unfold Zq
  exact contDiff_const.mul (hp.comp hu)
theorem ZdE (r t : ℕ) :
    ContDiff ℝ ⊤ (Zr r t) := by
  let p := (Xq.Bernstein.Zar^[r]) (rudinShapiroQ t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ Zd (x / Zt t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      Zbu ((Zt t : ℝ)⁻¹)
  unfold Zr
  exact contDiff_const.mul (hp.comp hu)
theorem ZfB (q r t : ℕ) :
    iteratedDeriv q (Zq r t) =
      Zq (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (Zgj (r + q) t x).deriv
theorem ZfC (q r t : ℕ) :
    iteratedDeriv q (Zr r t) =
      Zr (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (Zgk (r + q) t x).deriv
private theorem Zeu (q : ℕ) (c : ℝ) :
    iteratedDeriv q (fun x : ℝ ↦ Zd (c * x)) =
      fun x ↦ ((c : ℂ) * Complex.I) ^ q * Zd (c * x) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa only [pow_succ, mul_assoc] using
        (Ze2 c x).const_mul (((c : ℂ) * Complex.I) ^ q) |>.deriv
def ZaB (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (Complex.I ^ i * Zd x) * Zq (r - i) t x +
    ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * Zd (2 * x)) *
          Zr (r - i) t x
theorem Zhq (t : ℕ) :
    ContDiff ℝ ⊤ (ZE t) := by
  unfold ZE
  simpa only [one_mul] using
    (((Zbu 1).mul (ZdD 0 t)).add
      ((Zbu 2).mul (ZdE 0 t)))
theorem ZiC (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (ZE t) x = ZaB r t x := by
  have hu1 : ContDiff ℝ ⊤ (fun y : ℝ ↦ Zd y) := by
    simpa only [one_mul] using Zbu 1
  have hu2 : ContDiff ℝ ⊤ (fun y : ℝ ↦ Zd (2 * y)) :=
    Zbu 2
  have hp := ZdD 0 t
  have hq := ZdE 0 t
  have hdu1 (i : ℕ) : iteratedDeriv i (fun y : ℝ ↦ Zd y) x =
      Complex.I ^ i * Zd x := by
    have h := congrFun (Zeu i 1) x
    norm_num at h
    exact h
  unfold ZE ZaB
  change iteratedDeriv r
      ((fun y ↦ Zd y * Zq 0 t y) +
        fun y ↦ Zd (2 * y) * Zr 0 t y) x = _
  rw [iteratedDeriv_add
    ((hu1.mul hp).contDiffAt.of_le (by simp))
    ((hu2.mul hq).contDiffAt.of_le (by simp))]
  congr 1
  · change iteratedDeriv r
        ((fun y ↦ Zd y) * Zq 0 t) x = _
    rw [iteratedDeriv_mul
      (hu1.contDiffAt.of_le (by simp))
      (hp.contDiffAt.of_le (by simp))]
    simp_rw [hdu1,
      congrFun (ZfB _ _ _) x]
    simp only [Nat.zero_add]
  · change iteratedDeriv r
        ((fun y ↦ Zd (2 * y)) * Zr 0 t) x = _
    rw [iteratedDeriv_mul
      (hu2.contDiffAt.of_le (by simp))
      (hq.contDiffAt.of_le (by simp))]
    simp_rw [congrFun (Zeu _ 2) x,
      congrFun (ZfC _ _ _) x]
    norm_num
theorem ZdO (t : ℕ) :
    ContDiff ℝ ⊤ (fun x ↦ (ZE t x).re) := by
  exact Complex.reCLM.contDiff.comp (Zhq t)
private theorem ZhW {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y ↦ (f y).re) f'.re x := by
  have hc : HasDerivAt (fun _ : ℝ ↦ Complex.reCLM) 0 x := hasDerivAt_const x _
  simpa using hc.clm_apply hf
theorem ZhF (r t : ℕ) :
    iteratedDeriv r (fun x ↦ (ZE t x).re) =
      fun x ↦ (iteratedDeriv r (ZE t) x).re := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      funext x
      have hd : DifferentiableAt ℝ (iteratedDeriv r (ZE t)) x :=
        ((Zhq t).differentiable_iteratedDeriv r (by simp)) x
      exact (ZhW hd.hasDerivAt).deriv
theorem Zdn (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y ↦ (ZE t y).re) x =
      (ZaB r t x).re := by
  rw [congrFun (ZhF r t) x,
    ZiC]
private theorem Zf2 (r t : ℕ) (x : ℝ) :
    ‖ZaB r t x‖ ≤
      ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold ZaB
  calc
    ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * Zd x) *
              Zq (r - i) t x +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Zd (2 * x)) *
              Zr (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * Zd x) *
              Zq (r - i) t x‖ +
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Zd (2 * x)) *
              Zr (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow,
          Zbv, mul_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (Zd2 (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, Zbv, mul_one,
          Complex.norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (Zd3 (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))
theorem ZeI {r : ℕ} (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    ‖ZaB r t x‖ ≤ 18 := by
  refine (Zf2 r t x).trans ?_
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.choose]
theorem ZaV (r : ℕ) (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    |iteratedDeriv r (fun y ↦ (ZE t y).re) x| ≤ 18 := by
  rw [Zdn]
  exact (Complex.abs_re_le_norm _).trans
    (ZeI hr t x)
private def ZbS (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (Complex.I ^ i * Zd x) * Zq (r - i) t x +
    ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * Zd (2 * x)) *
          Zr (r - i) t x
private theorem Zf3 (r t : ℕ) (x : ℝ) :
    ZaB r t x -
        Xq.CosineAlgebra.ZaC r
          (Zd x * Zq 0 t x)
          (Zd (2 * x) * Zr 0 t x) =
      ZbS r t x := by
  unfold ZaB ZbS
    Xq.CosineAlgebra.ZaC
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
  ring
private theorem ZeJ (r t : ℕ) (x : ℝ) :
    ‖ZbS r t x‖ ≤
      ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold ZbS
  calc
    ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * Zd x) *
              Zq (r - i) t x +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Zd (2 * x)) *
              Zr (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * Zd x) *
              Zq (r - i) t x‖ +
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Zd (2 * x)) *
              Zr (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow,
          Zbv, mul_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (Zd2 (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, Zbv, mul_one,
          Complex.norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (Zd3 (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))
private theorem Zc0 {r : ℕ}
    (hr : r < 4) (t : ℕ) (x : ℝ) :
    ‖ZaB r t x -
        Xq.CosineAlgebra.ZaC r
          (Zd x * Zq 0 t x)
          (Zd (2 * x) * Zr 0 t x)‖ ≤ 1 / 8 := by
  rw [Zf3]
  refine (ZeJ r t x).trans ?_
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.choose]
theorem Zeb (t : ℕ) (x : ℝ) :
    ∃ k : Fin 4,
      1 / 4 ≤ |iteratedDeriv k (fun y ↦ (ZE t y).re) x| := by
  have hlarge := Xq.CosineAlgebra.Zfv
    (u := Zd x) (v := Zd (2 * x))
    (alpha := Zq 0 t x) (beta := Zr 0 t x)
    (Zbv x) (Zbv (2 * x)) (Zk7 t x)
    (fun k : Fin 4 ↦ ZaB k t x)
    (fun k ↦ Zc0 k.isLt t x)
  simpa only [Zdn] using hlarge
theorem ZeK (t : ℕ) {eta : ℝ}
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048) :
    ZdN (fun x ↦ (ZE t x).re) eta := by
  exact Zdu
    (fun x ↦ (ZE t x).re) eta heta hetaSmall
    ((ZdO t).of_le (by simp))
    (Zeb t)
    (fun r hr x ↦ ZaV r hr t x)
end
end Xq.CosineConstruction
end
section
namespace Xq.CosineConstruction
open Set
noncomputable section
private theorem Zjo {N a b c d : ℕ} {bad : ℕ → Prop}
    (h₁ : Xq.Intervals.Zay N bad a b)
    (h₂ : Xq.Intervals.Zay N bad c d)
    (hne : (a, b) ≠ (c, d)) :
    b < c ∨ d < a := by
  classical
  rcases lt_trichotomy a c with hac | hac | hca
  · left
    by_contra hbc
    have hcb : c ≤ b := Nat.le_of_not_gt hbc
    have hcpos : 0 < c := by omega
    have hcPredN : c - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le c 1) (hcb.trans_lt h₁.2.1)
    have hbadPred : bad (c - 1) :=
      h₁.2.2.1 (c - 1) (Finset.mem_range.mpr hcPredN) (by omega) (by omega)
    rcases h₂.2.2.2.1 with hc0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred
  · exact False.elim (hne (h₁.Zkx h₂ hac))
  · right
    by_contra hda
    have had : a ≤ d := Nat.le_of_not_gt hda
    have hapos : 0 < a := by omega
    have haPredN : a - 1 < N :=
      lt_of_le_of_lt (Nat.sub_le a 1) (had.trans_lt h₂.2.1)
    have hbadPred : bad (a - 1) :=
      h₂.2.2.1 (a - 1) (Finset.mem_range.mpr haPredN) (by omega) (by omega)
    rcases h₁.2.2.2.1 with ha0 | hgoodPred
    · omega
    · exact hgoodPred hbadPred
theorem Zec
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n) :
    Set.Pairwise
      (↑(ZaP n t gamma) :
        Set Xq.OddSine.RealInterval)
      (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
        Real.pi / n ≤ |x - y|) := by
  classical
  intro I hI J hJ hne x hx y hy
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp hJ
  have hrunsNe : (a, b) ≠ (c, d) := by
    intro heq
    apply hne
    exact congrArg (Zbt n) heq
  rw [Zy] at hab hcd
  have horient := Zjo
    (show Xq.Intervals.Zay (2 * n) (Zcr n t gamma) a b by
      simpa only [ZJ] using hab.1)
    (show Xq.Intervals.Zay (2 * n) (Zcr n t gamma) c d by
      simpa only [ZJ] using hcd.1)
    hrunsNe
  simp only [Zbt, mem_Icc] at hx hy ⊢
  have hmono := Xq.Intervals.ZbE hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  rcases horient with hbc | hda
  · have hgap : b + 2 ≤ c := Zct hab.1 hcd.1 hbc
    have hgrid :
        Xq.Intervals.Zz n (b + 1) + Real.pi / n ≤
          Xq.Intervals.Zz n c := by
      rw [← Xq.Intervals.Zkw]
      exact hmono hgap
    rw [abs_of_nonpos (by linarith [hx.2, hy.1])]
    linarith [hx.2, hy.1]
  · have hgap : d + 2 ≤ a := Zct hcd.1 hab.1 hda
    have hgrid :
        Xq.Intervals.Zz n (d + 1) + Real.pi / n ≤
          Xq.Intervals.Zz n a := by
      rw [← Xq.Intervals.Zkw]
      exact hmono hgap
    rw [abs_of_nonneg (by linarith [hx.1, hy.2])]
    linarith [hx.1, hy.2]
private theorem Zeh (k : ℕ) :
    (rudinShapiroP (2 * k + 1)).eval 1 = (2 ^ (k + 1) : ℕ) ∧
    (rudinShapiroQ (2 * k + 1)).eval 1 = 0 ∧
    (rudinShapiroP (2 * k + 1)).eval (-1) = 0 ∧
    (rudinShapiroQ (2 * k + 1)).eval (-1) = (2 ^ (k + 1) : ℕ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rcases ih with ⟨hP1, hQ1, hPm1, hQm1⟩
      have hs : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [hs, show (2 * k + 1) + 2 = ((2 * k + 1) + 1) + 1 by omega]
      rw [ZbF ((2 * k + 1) + 1) 1,
        ZbG ((2 * k + 1) + 1) 1,
        ZbF ((2 * k + 1) + 1) (-1),
        ZbG ((2 * k + 1) + 1) (-1)]
      rw [ZbF (2 * k + 1) 1,
        ZbG (2 * k + 1) 1,
        ZbF (2 * k + 1) (-1),
        ZbG (2 * k + 1) (-1)]
      rw [hP1, hQ1, hPm1, hQm1]
      norm_num [pow_succ]
      ring
private theorem ZgU (k : ℕ) :
    Real.sqrt (2 ^ ((2 * k + 1) + 1) : ℝ) = (2 ^ (k + 1) : ℕ) := by
  rw [show (2 * k + 1) + 1 = (k + 1) * 2 by omega, pow_mul]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
  · norm_num
  · positivity
theorem ZeW {t : ℕ} (ht : Odd t) :
    (ZE t 0).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases Zeh k with ⟨hP1, hQ1, _hPm1, _hQm1⟩
  have hunit0 : Zd 0 = 1 := by simp [Zd]
  simp only [ZE, Zq, Zr, pow_zero,
    one_mul, Function.iterate_zero_apply, hunit0, zero_div, Zas]
  rw [hP1, hQ1, ZgU]
  norm_num
private theorem ZjJ (t : ℕ) :
    Zd ((Zt t : ℝ) * Real.pi) = 1 := by
  rw [show Zd ((Zt t : ℝ) * Real.pi) = Zd Real.pi ^ Zt t by
    simp only [Zd, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring]
  have hpi : Zd Real.pi = -1 := by simp [Zd]
  rw [hpi]
  rw [show Zt t = 2 * 2 ^ (t + 9) by simp [Zt, pow_succ']]
  rw [pow_mul]
  norm_num
theorem ZbD {t : ℕ} (ht : Odd t) :
    (ZE t ((Zt t : ℝ) * Real.pi)).re = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rcases Zeh k with ⟨_hP1, _hQ1, hPm1, hQm1⟩
  have hTpos : (0 : ℝ) < Zt (2 * k + 1) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) ((2 * k + 1) + 10))
  have hdiv :
      ((Zt (2 * k + 1) : ℝ) * Real.pi) / Zt (2 * k + 1) =
        Real.pi := by
    field_simp
  have hphase₁ := ZjJ (2 * k + 1)
  have hphase₂ :
      Zd (2 * ((Zt (2 * k + 1) : ℝ) * Real.pi)) = 1 := by
    rw [show 2 * ((Zt (2 * k + 1) : ℝ) * Real.pi) =
      (Zt (2 * k + 1) : ℝ) * Real.pi +
        (Zt (2 * k + 1) : ℝ) * Real.pi by ring]
    rw [show Zd
        ((Zt (2 * k + 1) : ℝ) * Real.pi +
          (Zt (2 * k + 1) : ℝ) * Real.pi) =
        Zd ((Zt (2 * k + 1) : ℝ) * Real.pi) *
          Zd ((Zt (2 * k + 1) : ℝ) * Real.pi) by
      simp [Zd, Complex.exp_add, add_mul]]
    rw [hphase₁]
    norm_num
  simp only [ZE, Zq, Zr, pow_zero,
    one_mul, Function.iterate_zero_apply, hphase₁, hphase₂, hdiv,
    show Zd Real.pi = -1 by simp [Zd], Zas]
  rw [hPm1, hQm1, ZgU]
  norm_num
theorem ZaR
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    Ze n gamma < Real.sqrt (2 ^ (t + 1) : ℝ) / 2 := by
  have hgamma0 : 0 ≤ gamma := (hparam.gamma_pos).le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hthreshold0 : 0 ≤ Ze n gamma := by
    exact (ZhU hparam.n_pos hparam.gamma_pos).le
  have hscale0 : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hscaleSq : (Real.sqrt (2 ^ (t + 1) : ℝ)) ^ 2 = 2 ^ (t + 1) :=
    Real.sq_sqrt (by positivity)
  have hthresholdSq :
      (Ze n gamma) ^ 2 =
        (1 / 2 ^ 16 : ℝ) * (gamma ^ 7 * n) := by
    simp only [Ze, ZdM, mul_pow]
    rw [Real.sq_sqrt hgamma0, Real.sq_sqrt hn0]
    ring
  have hgammaOne : gamma ≤ 1 :=
    hparam.gamma_upper.trans (by norm_num)
  have hgammaPow : gamma ^ 6 ≤ 1 := by
    exact pow_le_one₀ hgamma0 hgammaOne
  have hnum : Zp t < 2 ^ (t + 12) := by
    have hpowpos : 0 < 2 ^ t := by positivity
    simp only [Zp, pow_add]
    norm_num
    omega
  have hnumR : (Zp t : ℝ) < (2 : ℝ) ^ (t + 12) := by
    exact_mod_cast hnum
  have hgammaNum : gamma ^ 7 * (n : ℝ) < (2 : ℝ) ^ (t + 12) := by
    calc
      gamma ^ 7 * (n : ℝ) = gamma ^ 6 * (gamma * n) := by ring
      _ = gamma ^ 6 * Zp t := by rw [hparam.equation]
      _ ≤ 1 * Zp t := by
        exact mul_le_mul_of_nonneg_right hgammaPow (by positivity)
      _ < (2 : ℝ) ^ (t + 12) := by simpa using hnumR
  have hsqLt :
      (Ze n gamma) ^ 2 <
        (Real.sqrt (2 ^ (t + 1) : ℝ) / 2) ^ 2 := by
    rw [hthresholdSq, div_pow, hscaleSq]
    calc
      (1 / 2 ^ 16 : ℝ) * (gamma ^ 7 * n) <
          (1 / 2 ^ 16 : ℝ) * 2 ^ (t + 12) := by gcongr
      _ < (2 ^ (t + 1) : ℝ) / 2 ^ 2 := by
        norm_num [pow_add]
        have hpow : (0 : ℝ) < 2 ^ t := by positivity
        nlinarith
  nlinarith
private theorem ZbU
    {t : ℕ} {axis x : ℝ}
    (haxis : (ZE t axis).re = 1)
    (hdiff : Differentiable ℝ (fun y ↦ (ZE t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (ZE t z).re) y| ≤ 18)
    (hclose : 18 * |x - axis| < 1 / 2) :
    1 / 2 < (ZE t x).re := by
  have hmean :
      |(ZE t x).re - (ZE t axis).re| ≤
        18 * |x - axis| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := fun y ↦ (ZE t y).re)
      (x := axis) (y := x)
      (fun y _ ↦ hdiff.differentiableAt)
      (fun y _ ↦ by
        simpa only [Real.norm_eq_abs, iteratedDeriv_succ', iteratedDeriv_zero]
          using hderiv y)
      convex_univ (Set.mem_univ axis) (Set.mem_univ x)
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  rw [haxis] at hmean
  have := (abs_le.mp hmean).1
  linarith
private theorem ZhG
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    (2 * Zt t : ℝ) / n < gamma := by
  obtain ⟨k, ht⟩ := hparam.t_odd
  have htpos : 0 < t := by omega
  have hpow : 1 < 2 ^ t := by
    exact one_lt_pow₀ (by norm_num) htpos.ne'
  have hnat : 2 * Zt t < Zp t := by
    rw [Zp, ZcY]
    omega
  have hreal : (2 * Zt t : ℝ) < gamma * n := by
    rw [hparam.equation]
    exact_mod_cast hnat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  exact (div_lt_iff₀ hnR).2 hreal
private theorem Zf4
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 101) :
    18 * C * Real.pi * ((2 * Zt t : ℝ) / n) < 1 / 2 := by
  have hratio := ZhG hparam
  have hgamma0 := hparam.gamma_pos.le
  calc
    18 * C * Real.pi * ((2 * Zt t : ℝ) / n) ≤
        18 * C * Real.pi * gamma := by
      apply mul_le_mul_of_nonneg_left hratio.le
      positivity
    _ ≤ 18 * 101 * 4 * (1 / 2 ^ 40 : ℝ) := by
      gcongr
      · exact Real.pi_le_four
      · exact hparam.gamma_upper
    _ < 1 / 2 := by norm_num
theorem Zi8
    {n t i : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (ZE t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (ZE t z).re) y| ≤ 18)
    (hi : i < 100) :
    ¬Zcr n t gamma i := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hmono := Xq.Intervals.ZbE hparam.n_pos
  have htheta0 : 0 ≤ theta := by
    have hgp : 0 ≤ Xq.Intervals.Zz n i := by
      rw [← Xq.Intervals.Ziw n]
      exact hmono (Nat.zero_le i)
    exact hgp.trans htheta.1
  have htheta100 : theta ≤ 100 * Real.pi / n := by
    calc
      theta ≤ Xq.Intervals.Zz n (i + 1) := htheta.2
      _ ≤ Xq.Intervals.Zz n 100 := hmono (by omega)
      _ = 100 * Real.pi / n := by simp [Xq.Intervals.Zz]
  let x : ℝ := 2 * Zt t * theta
  have hxclose : 18 * |x - 0| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * Zt t := by positivity
    rw [sub_zero, abs_of_nonneg (mul_nonneg hT0 htheta0)]
    calc
      18 * (2 * (Zt t : ℝ) * theta) ≤
          18 * (2 * (Zt t : ℝ) * (100 * Real.pi / n)) := by gcongr
      _ = 18 * 100 * Real.pi * ((2 * Zt t : ℝ) / n) := by ring
      _ < 1 / 2 := Zf4 hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (ZE t x).re :=
    ZbU
      (ZeW hparam.t_odd) hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := ZaR hparam
  have hcos : Ze n gamma < Zo t theta := by
    rw [Za9]
    change Ze n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (ZE t x).re
    nlinarith
  have habs : Zo t theta ≤ |Zo t theta| := le_abs_self _
  linarith
theorem ZiD
    {n t i : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (ZE t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (ZE t z).re) y| ≤ 18)
    (hiFirst : 2 * (i + 1) ≤ n)
    (hiNear : ¬2 * (i + 1 + 100) ≤ n) :
    ¬Zcr n t gamma i := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hiFirstR : (2 : ℝ) * (i + 1) ≤ n := by exact_mod_cast hiFirst
  have hiNearNat : n < 2 * (i + 101) := by omega
  have hiNearR : (n : ℝ) < 2 * (i + 101) := by exact_mod_cast hiNearNat
  have hrightEndpoint :
      Xq.Intervals.Zz n (i + 1) ≤ Real.pi / 2 := by
    simp only [Xq.Intervals.Zz, Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hthetaAxis : theta ≤ Real.pi / 2 :=
    htheta.2.trans hrightEndpoint
  have hgridDist :
      Real.pi / 2 - Xq.Intervals.Zz n i <
        101 * Real.pi / n := by
    simp only [Xq.Intervals.Zz]
    apply (sub_lt_iff_lt_add).2
    rw [← add_div]
    apply (lt_div_iff₀ hnR).2
    nlinarith [Real.pi_pos]
  have hthetaDist : Real.pi / 2 - theta < 101 * Real.pi / n := by
    linarith [htheta.1, hgridDist]
  have hthetaDist0 : 0 ≤ Real.pi / 2 - theta := sub_nonneg.mpr hthetaAxis
  let x : ℝ := 2 * Zt t * theta
  let axis : ℝ := Zt t * Real.pi
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * Zt t := by positivity
    rw [show x - axis =
        -(2 * (Zt t : ℝ)) * (Real.pi / 2 - theta) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_neg, abs_of_nonneg hT0, abs_of_nonneg hthetaDist0]
    calc
      18 * (2 * (Zt t : ℝ) * (Real.pi / 2 - theta)) ≤
          18 * (2 * (Zt t : ℝ) * (101 * Real.pi / n)) := by
            gcongr
      _ = 18 * 101 * Real.pi * ((2 * Zt t : ℝ) / n) := by ring
      _ < 1 / 2 := Zf4 hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (ZE t x).re :=
    ZbU
      (show (ZE t axis).re = 1 by
        dsimp only [axis]
        exact ZbD hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := ZaR hparam
  have hcos : Ze n gamma < Zo t theta := by
    rw [Za9]
    change Ze n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (ZE t x).re
    nlinarith
  have habs : Zo t theta ≤ |Zo t theta| := le_abs_self _
  linarith
theorem Zjp
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hdiff : Differentiable ℝ (fun y ↦ (ZE t y).re))
    (hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (ZE t z).re) y| ≤ 18) :
    ¬Zcr n t gamma (n / 2) := by
  rintro ⟨theta, htheta, hsmall⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hqLower : 2 * (n / 2) ≤ n := by omega
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqLowerR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hqLower
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have hgridLower :
      Real.pi / 2 - Real.pi / n ≤
        Xq.Intervals.Zz n (n / 2) := by
    simp only [Xq.Intervals.Zz]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hgridUpper :
      Xq.Intervals.Zz n (n / 2 + 1) ≤
        Real.pi / 2 + Real.pi / n := by
    simp only [Xq.Intervals.Zz, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hthetaDist : |theta - Real.pi / 2| ≤ Real.pi / n := by
    rw [abs_le]
    constructor <;> linarith [htheta.1, htheta.2, hgridLower, hgridUpper]
  let x : ℝ := 2 * Zt t * theta
  let axis : ℝ := Zt t * Real.pi
  have hxclose : 18 * |x - axis| < 1 / 2 := by
    have hT0 : (0 : ℝ) ≤ 2 * Zt t := by positivity
    rw [show x - axis =
        (2 * (Zt t : ℝ)) * (theta - Real.pi / 2) by
      dsimp only [x, axis]
      ring]
    rw [abs_mul, abs_of_nonneg hT0]
    calc
      18 * (2 * (Zt t : ℝ) * |theta - Real.pi / 2|) ≤
          18 * (2 * (Zt t : ℝ) * (Real.pi / n)) := by gcongr
      _ = 18 * 1 * Real.pi * ((2 * Zt t : ℝ) / n) := by ring
      _ < 1 / 2 := Zf4 hparam (by norm_num) (by norm_num)
  have hxhalf : 1 / 2 < (ZE t x).re :=
    ZbU
      (show (ZE t axis).re = 1 by
        dsimp only [axis]
        exact ZbD hparam.t_odd)
      hdiff hderiv hxclose
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hthreshold := ZaR hparam
  have hcos : Ze n gamma < Zo t theta := by
    rw [Za9]
    change Ze n gamma <
      Real.sqrt (2 ^ (t + 1) : ℝ) * (ZE t x).re
    nlinarith
  have habs : Zo t theta ≤ |Zo t theta| := le_abs_self _
  linarith
theorem Zb0
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬Zcr n t gamma i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬Zcr n t gamma i) :
    ∀ I ∈ ZaP n t gamma,
      100 * Real.pi / n ≤ I.1 ∧
        I.2 ≤ Real.pi / 2 - 100 * Real.pi / n := by
  classical
  intro I hI
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hI
  rw [Zy] at hab
  have hrun :
      Xq.Intervals.Zay (2 * n) (Zcr n t gamma) a b := by
    simpa only [ZJ] using hab.1
  have hbada : Zcr n t gamma a :=
    hrun.2.2.1 a (Finset.mem_range.mpr (hrun.1.trans_lt hrun.2.1)) le_rfl hrun.1
  have hbadb : Zcr n t gamma b :=
    hrun.2.2.1 b (Finset.mem_range.mpr hrun.2.1) hrun.1 le_rfl
  have ha100 : 100 ≤ a := by
    by_contra ha
    exact hleft a (by omega) hbada
  have hb100 : 2 * (b + 1 + 100) ≤ n := by
    by_contra hb
    exact hright b hab.2 hb hbadb
  simp only [Zbt]
  constructor
  · rw [show 100 * Real.pi / (n : ℝ) =
        Xq.Intervals.Zz n 100 by
      simp [Xq.Intervals.Zz]]
    exact Xq.Intervals.ZbE hn ha100
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb100R : (2 : ℝ) * (b + 1 + 100) ≤ n := by exact_mod_cast hb100
    simp only [Xq.Intervals.Zz, Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ hnR).2
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
theorem ZeL
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hleft : ∀ i, i < 100 → ¬Zcr n t gamma i)
    (hright : ∀ i, 2 * (i + 1) ≤ n → ¬2 * (i + 1 + 100) ≤ n →
      ¬Zcr n t gamma i) :
    ZbL n t gamma where
  separated := Zec hn
  away_from_axes :=
    Zb0 hn hleft hright
theorem ZfM
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    ZbL n t gamma := by
  have hdiff : Differentiable ℝ (fun y ↦ (ZE t y).re) :=
    (ZdO t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (ZE t z).re) y| ≤ 18 := by
    intro y
    exact ZaV 1 (by omega) t y
  apply ZeL hparam.n_pos
  · intro i hi
    exact Zi8 hparam hdiff hderiv hi
  · intro i hiFirst hiNear
    exact ZiD hparam hdiff hderiv hiFirst hiNear
theorem ZdP
    {n t : ℕ} {gamma theta : ℝ} (hparam : Parameters n t gamma)
    (htheta : theta ∈ Icc 0 (Real.pi / 2))
    (hsmall : |Zo t theta| < Ze n gamma) :
    ∃ I ∈ ZaP n t gamma,
      Xq.OddSine.Zal I theta := by
  classical
  have hdiff : Differentiable ℝ (fun y ↦ (ZE t y).re) :=
    (ZdO t).differentiable (by norm_num)
  have hderiv : ∀ y,
      |iteratedDeriv 1 (fun z ↦ (ZE t z).re) y| ≤ 18 := by
    intro y
    exact ZaV 1 (by omega) t y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  let P : ℕ → Prop := fun k ↦
    theta ≤ Xq.Intervals.Zz n (k + 1)
  have hqUpper : n < 2 * (n / 2 + 1) := by omega
  have hqUpperR : (n : ℝ) < 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hqUpper
  have haxisGrid :
      Real.pi / 2 ≤ Xq.Intervals.Zz n (n / 2 + 1) := by
    simp only [Xq.Intervals.Zz, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    nlinarith [Real.pi_pos]
  have hPex : ∃ k, P k :=
    ⟨n / 2, htheta.2.trans haxisGrid⟩
  let i : ℕ := Nat.find hPex
  have hiright : theta ≤ Xq.Intervals.Zz n (i + 1) := by
    simpa only [i, P] using Nat.find_spec hPex
  have hileft : Xq.Intervals.Zz n i ≤ theta := by
    by_cases hi0 : i = 0
    · rw [hi0, Xq.Intervals.Ziw]
      exact htheta.1
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hnot := Nat.find_min hPex (show i - 1 < Nat.find hPex by
        simpa only [i] using Nat.sub_lt hipos Nat.one_pos)
      have hpred : i - 1 + 1 = i := by omega
      change ¬theta ≤ Xq.Intervals.Zz n (i - 1 + 1) at hnot
      rw [hpred] at hnot
      exact (lt_of_not_ge hnot).le
  have hiq : i ≤ n / 2 := by
    exact Nat.find_min' hPex (htheta.2.trans haxisGrid)
  have hiN : i < 2 * n := by
    have hnpos : 0 < n := hparam.n_pos
    have hn2 : n < 2 * n := by omega
    exact hiq.trans_lt ((Nat.div_le_self n 2).trans_lt hn2)
  have hbad : Zcr n t gamma i :=
    ⟨theta, ⟨hileft, hiright⟩, hsmall⟩
  obtain ⟨⟨a, b⟩, hab, hai, hib⟩ :=
    Xq.Intervals.Zfe hiN hbad
  have hrun : (a, b) ∈ Zcs n t gamma := by
    simpa only [Zcs] using hab
  have hfirst : 2 * (b + 1) ≤ n := by
    by_contra hcross
    have hqLower : 2 * (n / 2) ≤ n := by omega
    have haq : a ≤ n / 2 := hai.trans hiq
    have hqb : n / 2 ≤ b := by omega
    have hmax :
        Xq.Intervals.Zay
          (2 * n) (Zcr n t gamma) a b :=
      ZJ.mp hrun
    have hbadMiddle : Zcr n t gamma (n / 2) :=
      hmax.2.2.1 (n / 2)
        (Finset.mem_range.mpr (by omega)) haq hqb
    exact Zjp hparam hdiff hderiv hbadMiddle
  have hfirstRun : (a, b) ∈ ZaF n t gamma :=
    Zy.mpr ⟨hrun, hfirst⟩
  refine ⟨Zbt n (a, b), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(a, b), hfirstRun, rfl⟩
  · simp only [Xq.OddSine.Zal, Zbt, mem_Icc]
    have hmono := Xq.Intervals.ZbE hparam.n_pos
    exact ⟨(hmono hai).trans hileft,
      hiright.trans (hmono (by omega))⟩
end
end Xq.CosineConstruction
end
section
namespace Xq.CosineConstruction
open Filter
noncomputable section
private lemma ZbM (k : ℕ) :
    Zp (2 * k + 1) + 1 = 4098 * 4 ^ k := by
  have hpow : 0 < 2 ^ ((2 * k + 1) + 11) := by positivity
  have hone : 1 ≤ 2 ^ ((2 * k + 1) + 11) + 2 ^ (2 * k + 1) :=
    hpow.trans_le (Nat.le_add_right _ _)
  rw [Zp, Nat.sub_add_cancel hone]
  simp [pow_add, pow_mul]
  ring
theorem ZhH :
    ∀ᶠ n : ℕ in atTop, ∃ t gamma, Parameters n t gamma := by
  filter_upwards [eventually_ge_atTop (2 ^ 40 * 4098)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hx : (1 : ℝ) ≤ (n : ℝ) / (2 ^ 40 * 4098) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)]
    exact_mod_cast hn
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  let t := 2 * k + 1
  let gamma := (Zp t : ℝ) / n
  refine ⟨t, gamma, ?_⟩
  constructor
  · exact hnpos
  · exact ⟨k, by simp [t]⟩
  · dsimp only [gamma]
    field_simp
  · dsimp only [gamma, t]
    have hnum : ((Zp (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast ZbM k
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hkpow : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hnupper : (n : ℝ) < (2 ^ 40 * 4098) * 4 ^ (k + 1) := by
      simpa [mul_comm] using (div_lt_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hkhi
    rw [show (4 : ℝ) ^ (k + 1) = 4 ^ k * 4 by rw [pow_succ]] at hnupper
    norm_num at hnupper ⊢
    nlinarith
  · dsimp only [gamma, t]
    have hnum : ((Zp (2 * k + 1) : ℕ) : ℝ) + 1 =
        4098 * 4 ^ k := by
      exact_mod_cast ZbM k
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
    have hnlower : (2 ^ 40 * 4098 : ℝ) * 4 ^ k ≤ n := by
      simpa [mul_comm] using (le_div_iff₀
        (by positivity : (0 : ℝ) < 2 ^ 40 * 4098)).mp hklo
    norm_num at hnlower ⊢
    nlinarith
end
end Xq.CosineConstruction
end
section
namespace Xq.CosineConstruction
open Set
noncomputable section
def Zbg (p : Polynomial ℂ) : Polynomial ℝ :=
  ∑ k ∈ p.support,
    Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)
theorem Zfj
    (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0)
    (x : ℝ) :
    (Zbg p).eval (Real.cos x) =
      (p.eval (Xq.Zd x)).re := by
  classical
  rw [Zbg, Polynomial.eval_finsetSum,
    Polynomial.eval_eq_sum, Polynomial.sum_def]
  change (∑ k ∈ p.support,
      (Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (Real.cos x)) =
    Complex.reLm (∑ k ∈ p.support, p.coeff k * Xq.Zd x ^ k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.Chebyshev.T_real_cos]
  have hpow := congrArg Complex.re (Xq.ZdG x k)
  have hre : (Xq.Zd x ^ k).re = Real.cos (k * x) := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using hpow
  change (p.coeff k).re * Real.cos ((k : ℤ) * x) =
    (p.coeff k * Xq.Zd x ^ k).re
  rw [Complex.mul_re, hreal k hk, zero_mul, sub_zero, hre]
  norm_cast
theorem ZgV (t k : ℕ) :
    ((Zn t).coeff k).im = 0 := by
  classical
  by_cases hk : k ∈ (Zn t).support
  · rw [Zax, ZaA] at hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [ZaK t j hj]
      rcases Zac hj with h | h <;> simp [h]
    · rw [Zav t j hj]
      rcases Zad hj with h | h <;> simp [h]
  · have hcoeff : (Zn t).coeff k = 0 := by
      simpa [Polynomial.mem_support_iff] using hk
    simp [hcoeff]
def ZV (t : ℕ) : Polynomial ℝ :=
  Zbg (Zn t)
theorem ZfN (t : ℕ) (x : ℝ) :
    (ZV t).eval (Real.cos (2 * x)) =
      Zo t x := by
  simpa only [ZV, Zo] using
    Zfj (Zn t)
      (fun k _ ↦ ZgV t k) (2 * x)
theorem ZbN (t : ℕ) :
    (ZV t).natDegree ≤ Zp t := by
  classical
  rw [ZV, Zbg]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ∈ (Zn t).support := by simpa using hk
  have hkBound : k ≤ Zp t := by
    rw [Zax, ZaA] at hk'
    rcases hk' with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [Zp, ← ZcY,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      have hjle : j ≤ 2 ^ t - 1 := Nat.le_sub_one_of_lt hj
      omega
    · rw [Zp, ← ZcY,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
  calc
    (Polynomial.C ((Zn t).coeff k).re *
        Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree ≤
        (Polynomial.C ((Zn t).coeff k).re).natDegree +
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by simp
    _ = k := by omega
    _ ≤ Zp t := hkBound
private theorem ZaW (t : ℕ) :
    Zp t = 2 * Zt t + (2 ^ t - 1) := by
  rw [Zp, ← ZcY,
    Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
private theorem Zgl (t : ℕ) :
    Zp t ∈ (Zn t).support := by
  rw [ZaW, Zax,
    ZaA]
  right
  exact ⟨2 ^ t - 1, Nat.sub_lt (by positivity) (by norm_num), rfl⟩
theorem Zev (t : ℕ) :
    (ZV t).natDegree = Zp t := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (ZbN t)
  let m := Zp t
  have hm : m ∈ (Zn t).support :=
    Zgl t
  have hj : 2 ^ t - 1 < 2 ^ t := by
    have : 0 < 2 ^ t := by positivity
    omega
  have htop : ((Zn t).coeff m).re ≠ 0 := by
    rw [show m = 2 * Zt t + (2 ^ t - 1) from ZaW t]
    rw [Zav t (2 ^ t - 1) hj]
    rcases Zad hj with h | h <;> simp [h]
  have hTtop : (Polynomial.Chebyshev.T ℝ (m : ℤ)).coeff m ≠ 0 := by
    have hdeg : (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree = m := by simp
    have hc := Polynomial.coeff_natDegree
      (p := Polynomial.Chebyshev.T ℝ (m : ℤ))
    rw [hdeg] at hc
    rw [hc, Polynomial.Chebyshev.leadingCoeff_T]
    positivity
  change (ZV t).coeff m ≠ 0
  rw [ZV, Zbg,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul]
    exact mul_ne_zero htop hTtop
  · intro k hk hkm
    have hkBound : k ≤ m := by
      rw [Zax, ZaA] at hk
      rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [show m = 2 * Zt t + (2 ^ t - 1) from ZaW t]
        have hjle := Nat.le_sub_one_of_lt hj
        omega
      · rw [show m = 2 * Zt t + (2 ^ t - 1) from ZaW t]
        exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
    have hklt : k < m := lt_of_le_of_ne hkBound hkm
    have hTzero : (Polynomial.Chebyshev.T ℝ (k : ℤ)).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hklt)
    rw [Polynomial.coeff_C_mul, hTzero, mul_zero]
  · intro hnot
    exact (hnot hm).elim
theorem ZbK (t : ℕ) (c : ℝ) :
    ZV t - Polynomial.C c ≠ 0 := by
  intro hzero
  have hconst : ZV t = Polynomial.C c :=
    sub_eq_zero.mp hzero
  have hdeg := Zev t
  rw [hconst] at hdeg
  have hmpos : 0 < Zp t := by
    rw [ZaW]
    have hT : 0 < Zt t := by simp [Zt]
    omega
  simp at hdeg
  omega
theorem ZgW (t : ℕ) : Continuous (Zo t) := by
  unfold Zo Xq.Zd
  fun_prop
private abbrev Zai (n t : ℕ) (gamma : ℝ) :=
  ↑(ZaF n t gamma)
private noncomputable def Zc1 {n t : ℕ} {gamma : ℝ}
    (I : Zai n t gamma) : ℝ :=
  Classical.choose (show Zcr n t gamma I.1.1 by
    have hI := (Zy.mp I.2).1
    rw [ZJ] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)
private theorem ZcD {n t : ℕ} {gamma : ℝ}
    (I : Zai n t gamma) :
    Zc1 I ∈ Xq.Intervals.Zln n I.1.1 := by
  exact (Classical.choose_spec (show Zcr n t gamma I.1.1 by
    have hI := (Zy.mp I.2).1
    rw [ZJ] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).1
private theorem Zfu {n t : ℕ} {gamma : ℝ}
    (I : Zai n t gamma) :
    |Zo t (Zc1 I)| < Ze n gamma := by
  exact (Classical.choose_spec (show Zcr n t gamma I.1.1 by
    have hI := (Zy.mp I.2).1
    rw [ZJ] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).2
private theorem Zlg {n t : ℕ} {gamma : ℝ}
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (I : Zai n t gamma) :
    Ze n gamma ≤
      |Zo t (Xq.Intervals.Zz n I.1.1)| := by
  have hI := (Zy.mp I.2).1
  rw [ZJ] at hI
  have hn : 0 < n := by
    have hb : I.1.2 < 2 * n := hI.2.1
    exact Nat.pos_of_ne_zero (fun hn0 ↦ by simp [hn0] at hb)
  by_cases ha : I.1.1 = 0
  · simpa [ha, Xq.Intervals.Ziw] using hzero
  · have hgood : ¬Zcr n t gamma (I.1.1 - 1) :=
      hI.2.2.2.1.resolve_left ha
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨Xq.Intervals.Zz n I.1.1, ?_, hlt⟩
    simp only [Xq.Intervals.Zln, mem_Icc]
    constructor
    · exact (Xq.Intervals.ZbE (by omega)) (Nat.sub_le _ _)
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha)]
private theorem Zk9 {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (I : Zai n t gamma) :
    Ze n gamma ≤
      |Zo t (Xq.Intervals.Zz n (I.1.2 + 1))| := by
  have hmem := Zy.mp I.2
  have hI := hmem.1
  rw [ZJ] at hI
  by_cases heq : 2 * (I.1.2 + 1) = n
  · have hnEven : (n : ℝ) = 2 * (I.1.2 + 1 : ℕ) := by exact_mod_cast heq.symm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have harg : Xq.Intervals.Zz n (I.1.2 + 1) = Real.pi / 2 := by
      rw [Xq.Intervals.Zz, div_eq_iff hnR]
      rw [hnEven]
      ring
    rwa [harg]
  · have hstrict : 2 * (I.1.2 + 1) < n := lt_of_le_of_ne hmem.2 heq
    have hnotlast : I.1.2 + 1 ≠ 2 * n := by omega
    have hgood : ¬Zcr n t gamma (I.1.2 + 1) :=
      hI.2.2.2.2.resolve_left hnotlast
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨Xq.Intervals.Zz n (I.1.2 + 1), ?_, hlt⟩
    simp only [Xq.Intervals.Zln, mem_Icc]
    exact ⟨le_rfl, (Xq.Intervals.ZbE hn) (by omega)⟩
private theorem ZhX {n t : ℕ} {gamma : ℝ}
    (_ : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (I : Zai n t gamma) :
    ∃ x ∈ Icc (Xq.Intervals.Zz n I.1.1) (Zc1 I),
      |Zo t x| = Ze n gamma := by
  apply Xq.Intervals.ZfG (ZgW t)
  · exact (ZcD I).1
  · exact Or.inr ⟨Zfu I, Zlg hzero I⟩
private theorem Zhr {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (I : Zai n t gamma) :
    ∃ x ∈ Icc (Zc1 I)
        (Xq.Intervals.Zz n (I.1.2 + 1)),
      |Zo t x| = Ze n gamma := by
  apply Xq.Intervals.ZfG (ZgW t)
  · have hw := (ZcD I).2
    have hI := (Zy.mp I.2).1
    rw [ZJ] at hI
    exact hw.trans ((Xq.Intervals.ZbE hn)
      (Nat.add_le_add_right hI.1 1))
  · exact Or.inl ⟨Zfu I, Zk9 hn hhalf I⟩
private noncomputable def Zjq {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (I : Zai n t gamma) : ℝ :=
  Classical.choose (ZhX hn hzero I)
private noncomputable def Zio {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (I : Zai n t gamma) : ℝ :=
  Classical.choose (Zhr hn hhalf I)
private theorem ZcV {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (I : Zai n t gamma) :
    Zjq hn hzero I ∈
        Icc (Xq.Intervals.Zz n I.1.1) (Zc1 I) ∧
      |Zo t (Zjq hn hzero I)| = Ze n gamma :=
  Classical.choose_spec (ZhX hn hzero I)
private theorem ZcE {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (I : Zai n t gamma) :
    Zio hn hhalf I ∈
        Icc (Zc1 I) (Xq.Intervals.Zz n (I.1.2 + 1)) ∧
      |Zo t (Zio hn hhalf I)| = Ze n gamma :=
  Classical.choose_spec (Zhr hn hhalf I)
private theorem Zgp {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (I : Zai n t gamma) :
    Zjq hn hzero I < Zc1 I := by
  have hs := ZcV hn hzero I
  refine hs.1.2.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [heq] at hv
  exact (Zfu I).ne hv
private theorem Zf5 {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (I : Zai n t gamma) :
    Zc1 I < Zio hn hhalf I := by
  have hs := ZcE hn hhalf I
  refine hs.1.1.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [← heq] at hv
  exact (Zfu I).ne hv
private noncomputable def Za1 {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|) :
    Zai n t gamma × Fin 2 → ℝ
  | (I, k) => if (k : ℕ) = 0 then Zjq hn hzero I else Zio hn hhalf I
private theorem Zbc {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (K : Zai n t gamma) (k : Fin 2) :
    Xq.Intervals.Zz n K.1.1 ≤ Za1 hn hzero hhalf (K, k) ∧
    Za1 hn hzero hhalf (K, k) ≤
      Xq.Intervals.Zz n (K.1.2 + 1) := by
  by_cases hk : (k : ℕ) = 0
  · simp only [Za1, if_pos hk]
    refine ⟨(ZcV hn hzero K).1.1, ?_⟩
    have hrun := ZJ.mp (Zy.mp K.2).1
    exact (ZcV hn hzero K).1.2.trans <|
      (ZcD K).2.trans <|
        (Xq.Intervals.ZbE hn) (Nat.add_le_add_right hrun.1 1)
  · simp only [Za1, if_neg hk]
    have hleft := (ZcD K).1
    exact ⟨hleft.trans (ZcE hn hhalf K).1.1,
      (ZcE hn hhalf K).1.2⟩
private theorem ZkD {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (K : Zai n t gamma) (k : Fin 2) :
    |Zo t (Za1 hn hzero hhalf (K, k))| =
      Ze n gamma := by
  by_cases hk : (k : ℕ) = 0
  · simpa only [Za1, if_pos hk] using (ZcV hn hzero K).2
  · simpa only [Za1, if_neg hk] using (ZcE hn hhalf K).2
private theorem Zjr {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|) :
    Function.Injective (Za1 hn hzero hhalf) := by
  rintro ⟨I, i⟩ ⟨J, j⟩ hij
  have contact_bounds (K : Zai n t gamma) (k : Fin 2) :
      Xq.Intervals.Zz n K.1.1 ≤ Za1 hn hzero hhalf (K, k) ∧
      Za1 hn hzero hhalf (K, k) ≤
        Xq.Intervals.Zz n (K.1.2 + 1) := by
    by_cases hk : (k : ℕ) = 0
    · simp only [Za1, if_pos hk]
      have hspec := ZcV hn hzero K
      refine ⟨hspec.1.1, ?_⟩
      have hrun := ZJ.mp (Zy.mp K.2).1
      exact (ZcV hn hzero K).1.2.trans <|
        (ZcD K).2.trans <|
          (Xq.Intervals.ZbE hn) (Nat.add_le_add_right hrun.1 1)
    · simp only [Za1, if_neg hk]
      exact ⟨(ZcD K).1.trans (ZcE hn hhalf K).1.1,
        (ZcE hn hhalf K).1.2⟩
  have hIJ : I = J := by
    apply Subtype.ext
    rcases lt_trichotomy I.1.1 J.1.1 with hlt | heq | hgt
    · have hI := (Zy.mp I.2).1
      have hJ := (Zy.mp J.2).1
      have hbc : I.1.2 < J.1.1 := by
        by_contra hnot
        have hmaxI := (ZJ.mp hI)
        have hmaxJ := (ZJ.mp hJ)
        have hJpos : 0 < J.1.1 := by omega
        have hpred : J.1.1 - 1 ≥ I.1.1 := by omega
        have hpred_le : J.1.1 - 1 ≤ I.1.2 := by omega
        have hbad := hmaxI.2.2.1 (J.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxI.2.1)) hpred hpred_le
        exact hmaxJ.2.2.2.1.resolve_left (Nat.ne_of_gt hJpos) hbad
      have hsep := Zct hI hJ hbc
      have hidx : I.1.2 + 1 < J.1.1 := by
        calc
          I.1.2 + 1 < (I.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ J.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : Xq.Intervals.Zz n (I.1.2 + 1) <
          Xq.Intervals.Zz n J.1.1 :=
        Xq.Intervals.Zcj hn hidx
      have hi := Zbc hn hzero hhalf I i
      have hj := Zbc hn hzero hhalf J j
      rw [hij] at hi
      linarith
    · have hmaxI := ZJ.mp (Zy.mp I.2).1
      have hmaxJ := ZJ.mp (Zy.mp J.2).1
      exact Xq.Intervals.Zay.Zkx hmaxI hmaxJ heq
    · have hI := (Zy.mp I.2).1
      have hJ := (Zy.mp J.2).1
      have hdc : J.1.2 < I.1.1 := by
        by_contra hnot
        have hmaxI := (ZJ.mp hI)
        have hmaxJ := (ZJ.mp hJ)
        have hIpos : 0 < I.1.1 := by omega
        have hpred : I.1.1 - 1 ≥ J.1.1 := by omega
        have hpred_le : I.1.1 - 1 ≤ J.1.2 := by omega
        have hbad := hmaxJ.2.2.1 (I.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxJ.2.1)) hpred hpred_le
        exact hmaxI.2.2.2.1.resolve_left (Nat.ne_of_gt hIpos) hbad
      have hsep := Zct hJ hI hdc
      have hidx : J.1.2 + 1 < I.1.1 := by
        calc
          J.1.2 + 1 < (J.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ I.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : Xq.Intervals.Zz n (J.1.2 + 1) <
          Xq.Intervals.Zz n I.1.1 :=
        Xq.Intervals.Zcj hn hidx
      have hi := Zbc hn hzero hhalf I i
      have hj := Zbc hn hzero hhalf J j
      rw [hij] at hi
      linarith
  subst J
  congr 1
  by_contra hne
  have hfin : ((i : ℕ) = 0 ∧ (j : ℕ) ≠ 0) ∨
      ((i : ℕ) ≠ 0 ∧ (j : ℕ) = 0) := by
    omega
  rcases hfin with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · simp only [Za1, if_pos hi, if_neg hj] at hij
    exact (Zgp hn hzero I).trans
      (Zf5 hn hhalf I) |>.ne hij
  · simp only [Za1, if_neg hi, if_pos hj] at hij
    exact (Zgp hn hzero I).trans
      (Zf5 hn hhalf I) |>.ne hij.symm
private noncomputable def Zbd
    (q : Polynomial ℝ) (level : ℝ) : Finset ℝ :=
  (q - Polynomial.C level).roots.toFinset ∪
    (q - Polynomial.C (-level)).roots.toFinset
private theorem Zfk
    (q : Polynomial ℝ) (level : ℝ) :
    (Zbd q level).card ≤ 2 * q.natDegree := by
  have hplus : (q - Polynomial.C level).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans <|
        (Polynomial.natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  have hminus : (q - Polynomial.C (-level)).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans <|
        (Polynomial.natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  calc
    (Zbd q level).card ≤
        (q - Polynomial.C level).roots.toFinset.card +
          (q - Polynomial.C (-level)).roots.toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ q.natDegree + q.natDegree := Nat.add_le_add hplus hminus
    _ = 2 * q.natDegree := by omega
private theorem Ze3
    {q : Polynomial ℝ} {level x : ℝ}
    (hlevel : 0 ≤ level)
    (hplus : q - Polynomial.C level ≠ 0)
    (hminus : q - Polynomial.C (-level) ≠ 0)
    (hx : |q.eval x| = level) :
    x ∈ Zbd q level := by
  rw [abs_eq hlevel] at hx
  rw [Zbd, Finset.mem_union]
  rcases hx with hx | hx
  · left
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hplus, Polynomial.IsRoot.def]
    simp [hx]
  · right
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hminus, Polynomial.IsRoot.def]
    simp [hx]
theorem ZdQ
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ Ze n gamma)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (Real.cos (2 * x)) = Zo t x)
    (hplus : q - Polynomial.C (Ze n gamma) ≠ 0)
    (hminus : q - Polynomial.C (-Ze n gamma) ≠ 0) :
    (ZaF n t gamma).card ≤ q.natDegree := by
  let roots := Zbd q (Ze n gamma)
  let f : Zai n t gamma × Fin 2 → ↑roots := fun p ↦
    ⟨Real.cos (2 * Za1 hn hzero hhalf p), by
      apply Ze3 hlevel hplus hminus
      rw [hq]
      exact ZkD hn hzero hhalf p.1 p.2⟩
  have hcos_inj : Set.InjOn (fun x : ℝ ↦ Real.cos (2 * x))
      (Icc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have h2x : 2 * x ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact mul_nonneg (by norm_num) hx.1
      · calc
          2 * x ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
          _ = Real.pi := by ring
    have h2y : 2 * y ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact mul_nonneg (by norm_num) hy.1
      · calc
          2 * y ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hy.2 (by norm_num)
          _ = Real.pi := by ring
    have := Real.injOn_cos h2x h2y hxy
    linarith
  have hf : Function.Injective f := by
    intro p r hpr
    apply Zjr hn hzero hhalf
    apply hcos_inj
    · constructor
      · exact (show 0 ≤ Xq.Intervals.Zz n p.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (Zbc hn hzero hhalf p.1 p.2).1
      · have hp := (Zy.mp p.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((p.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hp
        apply (Zbc hn hzero hhalf p.1 p.2).2.trans
        simp only [Xq.Intervals.Zz]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
    · constructor
      · exact (show 0 ≤ Xq.Intervals.Zz n r.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (Zbc hn hzero hhalf r.1 r.2).1
      · have hr := (Zy.mp r.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((r.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hr
        apply (Zbc hn hzero hhalf r.1 r.2).2.trans
        simp only [Xq.Intervals.Zz]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
    · exact Subtype.ext_iff.mp hpr
  have hcard := Fintype.card_le_of_injective f hf
  have hrootcard : roots.card ≤ 2 * q.natDegree :=
    Zfk q (Ze n gamma)
  have htwice : 2 * (ZaF n t gamma).card ≤ 2 * q.natDegree := by
    calc
      2 * (ZaF n t gamma).card =
          Fintype.card (Zai n t gamma × Fin 2) := by
        simp [Fintype.card_prod, mul_comm]
      _ ≤ Fintype.card ↑roots := hcard
      _ = roots.card := Fintype.card_coe _
      _ ≤ 2 * q.natDegree := hrootcard
  omega
theorem Zb1
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ Ze n gamma)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (Real.cos (2 * x)) = Zo t x)
    (hplus : q - Polynomial.C (Ze n gamma) ≠ 0)
    (hminus : q - Polynomial.C (-Ze n gamma) ≠ 0)
    (hdegree : q.natDegree ≤ Zp t) :
    (ZaF n t gamma).card ≤ Zp t :=
  (ZdQ hn hlevel hzero hhalf q hq hplus hminus).trans
    hdegree
theorem Zdv
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ Ze n gamma)
    (hzero : Ze n gamma ≤ |Zo t 0|)
    (hhalf : Ze n gamma ≤ |Zo t (Real.pi / 2)|) :
    (ZaF n t gamma).card ≤ Zp t := by
  apply Zb1
    hn hlevel hzero hhalf (ZV t)
  · exact ZfN t
  · exact ZbK t _
  · exact ZbK t _
  · exact ZbN t
end
end Xq.CosineConstruction
end
section
namespace Xq
open Filter
def Zcw (a : ℂ) : Prop := a = 1 ∨ a = -1
theorem Zcw.norm_eq_one {a : ℂ} (ha : Zcw a) : ‖a‖ = 1 := by
  rcases ha with rfl | rfl <;> simp
def Zc2 (n : ℕ) (p : Polynomial ℂ) : Prop :=
  p.degree = n ∧ ∀ i ≤ n, Zcw (p.coeff i)
noncomputable def ZhI (n : ℕ) (a : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)
theorem Zhs (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : i ≤ n) :
    (ZhI n a).coeff i = a ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (a j)) = _
  rw [map_sum]
  rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_iff.mpr hi⟩]
  · simp
  · intro j _ hj
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    rw [if_neg]
    intro hji
    apply hj
    exact Fin.ext hji
  · simp
theorem Zkk (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : n < i) :
    (ZhI n a).coeff i = 0 := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (a j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [if_neg]
  exact ne_of_lt ((Nat.le_of_lt_succ j.isLt).trans_lt hi)
theorem ZlN (n : ℕ) (a : Fin (n + 1) → ℂ) (z : ℂ) :
    (ZhI n a).eval z = ∑ i, a i * z ^ (i : ℕ) := by
  classical
  simpa [ZhI] using Polynomial.eval_finsetSum (Finset.univ : Finset (Fin (n + 1)))
    (fun i : Fin (n + 1) ↦ Polynomial.monomial (i : ℕ) (a i)) z
theorem Zlx (n : ℕ) (a : Fin (n + 1) → ℂ) (ha : a ⟨n, Nat.lt_succ_self n⟩ ≠ 0) :
    (ZhI n a).degree = n := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    exact Zkk n m a (by exact_mod_cast hm)
  · simpa [Zhs n n a le_rfl] using ha
theorem ZjZ (n : ℕ) (a : Fin (n + 1) → ℂ)
    (ha : ∀ i, Zcw (a i)) : Zc2 n (ZhI n a) := by
  constructor
  · apply Zlx
    rcases ha ⟨n, Nat.lt_succ_self n⟩ with h | h <;> simp [h]
  · intro i hi
    rw [Zhs n i a hi]
    exact ha ⟨i, Nat.lt_succ_iff.mpr hi⟩
def ZhJ (delta Delta : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    delta * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ Delta * Real.sqrt n
def ZgX (c₁ c₂ : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    Real.sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * Real.sqrt n
theorem ZeM {delta Delta : ℝ} {n : ℕ}
    {p : Polynomial ℂ} (hdelta : 0 < delta) (hDelta : 0 < Delta) (hn : 0 < n)
    (hp : ZhJ delta Delta n p) :
    ZgX (2 / delta) (2 * Delta) n p := by
  intro z hz
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  obtain ⟨hlower, hupper⟩ := hp z hz
  constructor
  · have hmul : 2 * Real.sqrt n ≤ (2 / delta) * ‖p.eval z‖ := by
      calc
        2 * Real.sqrt n = (2 / delta) * (delta * Real.sqrt n) := by field_simp
        _ ≤ (2 / delta) * ‖p.eval z‖ :=
          mul_le_mul_of_nonneg_left hlower (by positivity)
    linarith
  · have hstrict : Delta * Real.sqrt n < (2 * Delta) * Real.sqrt n := by
      have := mul_pos hDelta hsqrt
      nlinarith
    exact hupper.trans_lt hstrict
theorem Zfl {delta Delta : ℝ}
    (hdelta : 0 < delta) (hDelta : 0 < Delta)
    (hflat : ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      Zc2 n p ∧ ZhJ delta Delta n p) :
    ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      p.degree = n ∧
      (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
      ZgX (2 / delta) (2 * Delta) n p := by
  filter_upwards [hflat, eventually_gt_atTop (0 : ℕ)] with n hnflat hn
  obtain ⟨p, hpLittlewood, hpFlat⟩ := hnflat
  exact ⟨p, hpLittlewood.1, hpLittlewood.2,
    ZeM hdelta hDelta hn hpFlat⟩
end Xq
end
section
open Filter
namespace Xq
noncomputable section
def Zlp (n : ℕ) (eps : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)
@[simp]
theorem Zl0 (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : i ≤ n) :
    (Zlp n eps).coeff i = eps ⟨i, Nat.lt_succ_iff.2 hi⟩ := by
  classical
  change (Polynomial.lcoeff ℂ i)
      (∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Fintype.sum_eq_single ⟨i, Nat.lt_succ_iff.2 hi⟩]
  · rw [if_pos rfl]
  · intro b hb
    simp only [ite_eq_right_iff]
    intro hbi
    exact (hb (Fin.ext hbi)).elim
@[simp]
theorem Zl1 (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : n < i) :
    (Zlp n eps).coeff i = 0 := by
  classical
  change (Polynomial.lcoeff ℂ i)
      (∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [ite_eq_right_iff]
  intro hji
  omega
@[simp]
theorem Zmq (n : ℕ) (eps : Fin (n + 1) → ℂ) (z : ℂ) :
    (Zlp n eps).eval z = ∑ j : Fin (n + 1), eps j * z ^ j.1 := by
  simp [Zlp, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
end
end Xq
end
section
namespace Xq
open Filter
open scoped BigOperators
noncomputable section
def Zbe (theta : ℝ) : Prop :=
  theta ∈ Set.Icc (-Real.pi / 2) (3 * Real.pi / 2)
def ZiE (base r : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range r, Polynomial.monomial (base + 1 + j) 1
theorem Zjs (base r i : ℕ) :
    (ZiE base r).coeff i =
      if base < i ∧ i ≤ base + r then 1 else 0 := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j ∈ Finset.range r, Polynomial.monomial (base + 1 + j) 1) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  by_cases hi : base < i ∧ i ≤ base + r
  · rw [if_pos hi]
    have hj : i - (base + 1) < r := by omega
    rw [Finset.sum_eq_single (i - (base + 1))]
    · have heq : base + 1 + (i - (base + 1)) = i := by omega
      simp [heq]
    · intro b hb hne
      rw [if_neg]
      intro heq
      apply hne
      omega
    · simp [hj]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro heq
    apply hi
    simp only [Finset.mem_range] at hj
    omega
def ZbV (base r : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p + ZiE base r
theorem ZjK {base r i : ℕ} {p : Polynomial ℂ}
    (hi : i ≤ base) :
    (ZbV base r p).coeff i = p.coeff i := by
  rw [ZbV, Polynomial.coeff_add, Zjs]
  simp [show ¬base < i by omega]
theorem Zfm {base r i : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) (hlo : base < i) (hhi : i ≤ base + r) :
    (ZbV base r p).coeff i = 1 := by
  rw [ZbV, Polynomial.coeff_add, Zjs, if_pos ⟨hlo, hhi⟩]
  have hpzero : p.coeff i = 0 := by
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hlo
  rw [hpzero, zero_add]
theorem Zla {base r : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) :
    (ZbV base r p).degree = base + r := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero (n := base + r)
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro i hi
    have hisum : base + r < i := by exact_mod_cast hi
    rw [ZbV, Polynomial.coeff_add, Zjs]
    have hibase : base < i := by omega
    have htail : ¬(base < i ∧ i ≤ base + r) := by omega
    rw [if_neg htail]
    simp only [add_zero]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hibase
  · by_cases hr : r = 0
    · subst r
      simpa only [Nat.add_zero, ZbV, ZiE, Finset.range_zero,
        Finset.sum_empty, add_zero] using
        (show p.coeff base ≠ 0 by
          apply Polynomial.coeff_ne_zero_of_eq_degree hp)
    · rw [Zfm hp (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hr)) le_rfl]
      norm_num
theorem Zjt {base r : ℕ} {p : Polynomial ℂ}
    (hp : Zc2 base p) :
    Zc2 (base + r) (ZbV base r p) := by
  constructor
  · exact Zla hp.1
  · intro i hi
    by_cases hibase : i ≤ base
    · rw [ZjK hibase]
      exact hp.2 i hibase
    · rw [Zfm hp.1 (Nat.lt_of_not_ge hibase) hi]
      exact Or.inl rfl
theorem ZlU (base r : ℕ) (z : ℂ) :
    (ZiE base r).eval z = ∑ j ∈ Finset.range r, z ^ (base + 1 + j) := by
  simp [ZiE, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
theorem Zht {base r : ℕ} {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(ZiE base r).eval z‖ ≤ r := by
  rw [ZlU]
  calc
    ‖∑ j ∈ Finset.range r, z ^ (base + 1 + j)‖ ≤
        ∑ j ∈ Finset.range r, ‖z ^ (base + 1 + j)‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_pow, hz]
    _ = r := by simp
theorem Zig {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(ZbV base r p).eval z‖ ≤ ‖p.eval z‖ + r := by
  rw [ZbV, Polynomial.eval_add]
  calc
    ‖p.eval z + (ZiE base r).eval z‖ ≤
        ‖p.eval z‖ + ‖(ZiE base r).eval z‖ := norm_add_le _ _
    _ ≤ ‖p.eval z‖ + r := by
      gcongr
      exact Zht hz
theorem Zih {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.eval z‖ - r ≤ ‖(ZbV base r p).eval z‖ := by
  have htri : ‖p.eval z‖ ≤
      ‖(ZbV base r p).eval z‖ + ‖(ZiE base r).eval z‖ := by
    calc
      ‖p.eval z‖ =
          ‖(ZbV base r p).eval z - (ZiE base r).eval z‖ := by
            congr 1
            simp [ZbV]
      _ ≤ _ := norm_sub_le _ _
  linarith [Zht (base := base) (r := r) hz]
structure Zaj (n : ℕ) where
  coeff : Fin (4 * n + 1) → ℂ
  Zit : ∀ j, Zcw (coeff j)
  cosine : ℝ → ℝ
  ZeB : ℝ → ℝ
  oddSine : ℝ → ℝ
  dangerous : ℝ → Prop
  eval_eq : ∀ theta,
    (ZhI (4 * n) coeff).eval (Zd theta) =
      Zd theta ^ (2 * n) *
        Zam (cosine theta) (ZeB theta) (oddSine theta)
  cosine_upper : ∀ theta, |cosine theta| ≤ Real.sqrt n
  evenSine_upper : ∀ theta, |ZeB theta| ≤ 6 * Real.sqrt n
  oddSine_upper : ∀ theta, |oddSine theta| ≤ 2 ^ 10 * Real.sqrt n
  cosine_lower_off_dangerous : ∀ theta, Zbe theta →
    ¬ dangerous theta →
    (1 / 2 ^ 160 : ℝ) * Real.sqrt n + 1 ≤ 2 * |cosine theta|
  oddSine_lower_on_dangerous : ∀ theta, Zbe theta →
    dangerous theta →
    10 * Real.sqrt n ≤ |oddSine theta|
def Zaj.polynomial {n : ℕ} (A : Zaj n) :
    Polynomial ℂ :=
  ZhI (4 * n) A.coeff
theorem Zaj.ZlV {n : ℕ}
    (A : Zaj n) : Zc2 (4 * n) A.polynomial := by
  exact ZjZ (4 * n) A.coeff A.Zit
theorem Zaj.ZlW {n : ℕ}
    (A : Zaj n) (theta : ℝ) :
    ‖A.polynomial.eval (Zd theta)‖ =
      ‖Zam (A.cosine theta) (A.ZeB theta) (A.oddSine theta)‖ := by
  rw [Zaj.polynomial, A.eval_eq, norm_mul, norm_pow,
    Zbv, one_pow, one_mul]
theorem Zaj.ZhY {n : ℕ}
    (hn : 1 ≤ n) (A : Zaj n) (theta : ℝ)
    (htheta : Zbe theta) :
    (1 / 2 ^ 160 : ℝ) * Real.sqrt n ≤
        ‖A.polynomial.eval (Zd theta)‖ ∧
      ‖A.polynomial.eval (Zd theta)‖ ≤
        2 ^ 12 * Real.sqrt n := by
  rw [A.ZlW]
  constructor
  · by_cases hdanger : A.dangerous theta
    · have hbig := Zdk
          (c := A.cosine theta)
          (A.evenSine_upper theta)
          (A.oddSine_lower_on_dangerous theta htheta hdanger)
      have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      norm_num at hbig ⊢
      nlinarith
    · have hcos := ZdW
          (A.cosine theta) (A.ZeB theta) (A.oddSine theta)
      have hlower := A.cosine_lower_off_dangerous theta htheta hdanger
      norm_num at hlower ⊢
      linarith
  · exact ZdY hn
      (A.cosine_upper theta) (A.evenSine_upper theta) (A.oddSine_upper theta)
@[simp] theorem Zkl (theta : ℝ) :
    Zd (theta + 2 * Real.pi) = Zd theta := by
  unfold Zd
  rw [show (((theta + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (theta : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by
        push_cast
        ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
theorem ZdR {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ theta : ℝ, Zbe theta ∧ Zd theta = z := by
  let a := z.arg
  have haLower : -Real.pi < a := Complex.neg_pi_lt_arg z
  have haUpper : a ≤ Real.pi := Complex.arg_le_pi z
  have haPoint : Zd a = z := by
    calc
      Zd a = Complex.exp ((a : ℂ) * Complex.I) := rfl
      _ = ‖z‖ * Complex.exp ((a : ℂ) * Complex.I) := by rw [hz]; simp
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  by_cases ha : -Real.pi / 2 ≤ a
  · refine ⟨a, ⟨ha, ?_⟩, haPoint⟩
    nlinarith [Real.pi_pos]
  · refine ⟨a + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [Real.pi_pos]
    · nlinarith [lt_of_not_ge ha]
    · rw [Zkl]
      exact haPoint
theorem Zaj.ZlF {n : ℕ}
    (hn : 1 ≤ n) (A : Zaj n) :
    ∀ z : ℂ, ‖z‖ = 1 →
      (1 / 2 ^ 160 : ℝ) * Real.sqrt n ≤ ‖A.polynomial.eval z‖ ∧
      ‖A.polynomial.eval z‖ ≤ 2 ^ 12 * Real.sqrt n := by
  intro z hz
  obtain ⟨theta, htheta, rfl⟩ :=
    ZdR hz
  exact A.ZhY hn theta htheta
private theorem Zlh (n : ℕ) :
    Real.sqrt (16 * (n : ℝ)) = 4 * Real.sqrt n := by
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16)]
  norm_num
private theorem ZkV {a b : ℕ} (h : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b := by
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)
theorem ZiF (d : ℕ)
    (hn : 1 ≤ d / 4) (A : Zaj (d / 4))
    (habsorb : 3 ≤ (1 / 2 ^ 163 : ℝ) * Real.sqrt d) :
    ∃ p : Polynomial ℂ, Zc2 d p ∧
      ZhJ (1 / 2 ^ 163) (2 ^ 13) d p := by
  let n := d / 4
  let r := d % 4
  let q := A.polynomial
  let p := ZbV (4 * n) r q
  have hr : r ≤ 3 := by
    dsimp [r]
    omega
  have hdecomp : 4 * n + r = d := by
    dsimp [n, r]
    omega
  have hqLittlewood : Zc2 (4 * n) q := by
    exact A.ZlV
  have hpLittlewood : Zc2 d p := by
    rw [← hdecomp]
    exact Zjt hqLittlewood
  refine ⟨p, hpLittlewood, ?_⟩
  intro z hz
  have hqflat := A.ZlF hn z hz
  have hnle : n ≤ d := by
    dsimp [n]
    omega
  have hdle : d ≤ 16 * n := by
    rw [← hdecomp]
    omega
  have hsqrt_nd : Real.sqrt n ≤ Real.sqrt d := ZkV hnle
  have hsqrt_dn : Real.sqrt d ≤ 4 * Real.sqrt n := by
    calc
      Real.sqrt d ≤ Real.sqrt (16 * (n : ℝ)) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZkV hdle
      _ = 4 * Real.sqrt n := Zlh n
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsqrt_three : 3 ≤ Real.sqrt d := by
    have hfactor : (1 / 2 ^ 163 : ℝ) ≤ 1 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hfactor hsqrt_nonneg]
  constructor
  · have htail := Zih
        (base := 4 * n) (r := r) (p := q) hz
    change ‖q.eval z‖ - (r : ℝ) ≤ ‖p.eval z‖ at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    have hscale : (1 / 2 ^ 162 : ℝ) * Real.sqrt d ≤
        (1 / 2 ^ 160 : ℝ) * Real.sqrt n := by
      norm_num at ⊢
      nlinarith
    norm_num at hqflat habsorb ⊢
    nlinarith
  · have htail := Zig
        (base := 4 * n) (r := r) (p := q) hz
    change ‖p.eval z‖ ≤ ‖q.eval z‖ + (r : ℝ) at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    norm_num at hqflat ⊢
    nlinarith
def ZbB : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, Nonempty (Zaj n)
private theorem Zju :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 ≤ (1 / 2 ^ 163 : ℝ) * Real.sqrt d := by
  have hsqrt : Filter.Tendsto (fun d : ℕ ↦ Real.sqrt (d : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun d : ℕ ↦ (1 / 2 ^ 163 : ℝ) * Real.sqrt d)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (eventually_ge_atTop 3)
theorem ZeN
    (hcentered : ZbB) :
    ∀ᶠ d : ℕ in Filter.atTop, ∃ p : Polynomial ℂ,
      Zc2 d p ∧
      ZhJ (1 / 2 ^ 163) (2 ^ 13) d p := by
  rw [ZbB, eventually_atTop] at hcentered
  obtain ⟨N, hN⟩ := hcentered
  filter_upwards [eventually_ge_atTop (4 * max N 1), Zju]
    with d hd habsorb
  have hnN : N ≤ d / 4 := by omega
  have hn1 : 1 ≤ d / 4 := by omega
  obtain ⟨A⟩ := hN (d / 4) hnN
  exact ZiF d hn1 A habsorb
theorem Zli (hcentered : ZbB) :
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (Real.sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * Real.sqrt n) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    have hflat := ZeN hcentered
    have hstrict := Zfl
      (delta := (1 / 2 ^ 163 : ℝ)) (Delta := (2 ^ 13 : ℝ))
      (by positivity) (by positivity) hflat
    exact ⟨2 / (1 / 2 ^ 163 : ℝ), 2 * (2 ^ 13 : ℝ), hstrict⟩
  · intro _
    trivial
end
end Xq
end
section
namespace Xq.CosineConstruction
open Filter Set
noncomputable section
structure ZkW (n : ℕ) where
  t : ℕ
  gamma : ℝ
  parameters : Parameters n t gamma
  family : Xq.OddSine.Za n
  base_card : (family.base.card : ℝ) ≤ gamma * n
  upper : ∀ theta, |Zo t theta| ≤ Real.sqrt n
  lower : ∀ theta, Xq.Zbe theta →
    ¬Xq.OddSine.ZaH family theta →
      ZdM gamma * Real.sqrt n ≤ |Zo t theta|
theorem ZgA
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    ZbA n t gamma := by
  apply Zfi hparam
  exact ZeK t hparam.Zet hparam.Zmv
theorem ZiG
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    Ze n gamma ≤ |Zo t 0| ∧
      Ze n gamma ≤ |Zo t (Real.pi / 2)| := by
  have hthreshold := ZaR hparam
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  constructor
  · rw [Za9]
    simp only [mul_zero]
    rw [ZeW hparam.t_odd]
    simp only [mul_one, abs_of_pos hscale]
    linarith
  · rw [Za9]
    have harg : 2 * (Zt t : ℝ) * (Real.pi / 2) =
        (Zt t : ℝ) * Real.pi := by ring
    rw [harg, ZbD hparam.t_odd]
    simp only [mul_one, abs_of_pos hscale]
    linarith
theorem ZhZ
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hseven : ZbA n t gamma)
    (hgeom : ZbL n t gamma) :
    ((Zbq hparam.n_pos hseven hgeom).base.card : ℝ) ≤
      gamma * n := by
  have hend := ZiG hparam
  have hcard := Zdv hparam.n_pos
    (ZhU hparam.n_pos hparam.gamma_pos).le hend.1 hend.2
  rw [Zi7 hparam.n_pos hseven hgeom]
  have hcardR : ((ZaF n t gamma).card : ℝ) ≤
      Zp t := by exact_mod_cast hcard
  rwa [hparam.equation]
def ZiH
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    ZkW n := by
  let hseven : ZbA n t gamma :=
    ZgA hparam
  let hgeom : ZbL n t gamma :=
    ZfM hparam
  let F : Xq.OddSine.Za n :=
    Zbq hparam.n_pos hseven hgeom
  refine
    { t := t
      gamma := gamma
      parameters := hparam
      family := F
      base_card := ?_
      upper := ?_
      lower := ?_ }
  · simpa only [F] using ZhZ hparam hseven hgeom
  · intro theta
    exact Zfd hparam.Zjz theta
  · intro theta htheta hout
    have hfirst : ∀ x ∈ Icc (0 : ℝ) (Real.pi / 2),
        ¬ZgT F x → Ze n gamma ≤ |Zo t x| := by
      intro x hx hbase
      apply le_of_not_gt
      intro hsmall
      apply hbase
      obtain ⟨I, hI, hxI⟩ :=
        ZdP hparam hx hsmall
      refine ⟨I, ?_, hxI⟩
      change I ∈ ZaP n t gamma
      exact hI
    have hlower := ZeH F hfirst theta
      (by simpa only [Xq.Zbe] using htheta) hout
    simpa only [Ze] using hlower
theorem ZgB :
    ∀ᶠ n : ℕ in atTop, Nonempty (ZkW n) := by
  filter_upwards [ZhH] with n hparam
  obtain ⟨t, gamma, hparam⟩ := hparam
  exact ⟨ZiH hparam⟩
end
end Xq.CosineConstruction
end
section
namespace Xq.OddSine
open scoped BigOperators
noncomputable section
def ZbT (n N : ℕ) : ℝ :=
  14 * Real.sqrt (Real.log ((16 * n : ℕ) / (N : ℝ)))
private lemma Zgq
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    (2 : ℝ) ^ 44 ≤ (16 * n : ℕ) / (N : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ gamma * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hgamma hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  apply (le_div_iff₀ hNR).2
  push_cast
  norm_num at hsmall ⊢
  nlinarith
private lemma Zb6
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    0 ≤ Real.log ((16 * n : ℕ) / (N : ℝ)) := by
  apply Real.log_nonneg
  exact (by norm_num : (1 : ℝ) ≤ 2 ^ 44).trans
    (Zgq hn hN hgamma hcard)
private lemma ZjL
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.log ((16 * n : ℕ) / (N : ℝ)) /
        ((16 * n : ℕ) / (N : ℝ)) ≤
      (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  have hq : (2 : ℝ) ^ 44 ≤ q := Zgq hn hN hgamma hcard
  have hexp : Real.exp 1 ≤ (2 : ℝ) ^ 44 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hmono : Real.log q / q ≤ Real.log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 :=
    Real.log_div_self_antitoneOn hexp (hexp.trans hq) hq
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogpow : Real.log ((2 : ℝ) ^ 44) ≤ 44 * (7 / 10 : ℝ) := by
    rw [Real.log_pow]
    nlinarith
  dsimp only [q] at hmono
  calc
    Real.log ((16 * n : ℕ) / (N : ℝ)) /
          ((16 * n : ℕ) / (N : ℝ)) ≤
        Real.log ((2 : ℝ) ^ 44) / (2 : ℝ) ^ 44 := hmono
    _ ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 := by
      apply div_le_div_of_nonneg_right (hlogpow.trans (by norm_num)) (by positivity)
private lemma ZkX
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.sqrt N * Real.sqrt n / n ≤ (1 : ℝ) / 2 ^ 20 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hsmall : (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := by
    calc
      (N : ℝ) ≤ gamma * n := hcard
      _ ≤ (1 / (2 : ℝ) ^ 40) * n :=
        mul_le_mul_of_nonneg_right hgamma hnR.le
      _ = (n : ℝ) / 2 ^ 40 := by ring
  have hsqrtn_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hsqrtN_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNR
  have hscale_nonneg : 0 ≤ Real.sqrt N * Real.sqrt n / (n : ℝ) := by positivity
  have hsquare :
      (Real.sqrt N * Real.sqrt n / (n : ℝ)) ^ 2 = (N : ℝ) / n := by
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    field_simp
  have htarget_nonneg : (0 : ℝ) ≤ 1 / 2 ^ 20 := by positivity
  have hratio : (N : ℝ) / n ≤ (1 : ℝ) / 2 ^ 40 := by
    apply (div_le_iff₀ hnR).2
    calc
      (N : ℝ) ≤ (n : ℝ) / 2 ^ 40 := hsmall
      _ = ((1 : ℝ) / 2 ^ 40) * n := by ring
  nlinarith [sq_nonneg
    (Real.sqrt N * Real.sqrt n / (n : ℝ) + (1 : ℝ) / 2 ^ 20)]
private lemma ZgC
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.sqrt (Real.log ((16 * n : ℕ) / (N : ℝ))) *
        (Real.sqrt N * Real.sqrt n / n) ≤
      (28 / 5 : ℝ) / 2 ^ 20 := by
  let q : ℝ := (16 * n : ℕ) / (N : ℝ)
  let a : ℝ := Real.sqrt N * Real.sqrt n / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hlog : 0 ≤ Real.log q := by
    dsimp only [q]
    exact Zb6 hn hN hgamma hcard
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have hsqrta : a ^ 2 = 16 / q := by
    have hsqrtn_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    have hsqrtN_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNR.le
    dsimp [a, q]
    rw [div_pow, mul_pow, hsqrtN_sq, hsqrtn_sq]
    push_cast
    field_simp
  have hquot := ZjL hn hN hgamma hcard
  change Real.log q / q ≤ (28 / 5 : ℝ) ^ 2 / 2 ^ 44 at hquot
  have hsqrtlog_sq : (Real.sqrt (Real.log q)) ^ 2 = Real.log q :=
    Real.sq_sqrt hlog
  have hleft_nonneg : 0 ≤ Real.sqrt (Real.log q) * a := by positivity
  have hright_nonneg : (0 : ℝ) ≤ (28 / 5 : ℝ) / 2 ^ 20 := by positivity
  have hsquare :
      (Real.sqrt (Real.log q) * a) ^ 2 = 16 * (Real.log q / q) := by
    rw [mul_pow, hsqrtlog_sq, hsqrta]
    field_simp
  nlinarith
theorem Zf6
    {n N : ℕ} {gamma : ℝ} (hn : 0 < n) (hN : 0 < N)
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (N : ℝ) ≤ gamma * n) :
    Real.exp (-(ZbT n N) ^ 2 / 196) =
      (N : ℝ) / (16 * n) := by
  have hlog := Zb6 hn hN hgamma hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [ZbT, mul_pow, Real.sq_sqrt hlog]
  have hqpos : (0 : ℝ) < (16 * n : ℕ) / (N : ℝ) := by positivity
  rw [show -((14 : ℝ) ^ 2 * Real.log ((16 * n : ℕ) / (N : ℝ))) / 196 =
      -Real.log ((16 * n : ℕ) / (N : ℝ)) by ring]
  rw [Real.exp_neg, Real.exp_log hqpos]
  push_cast
  field_simp
theorem ZfO
    {n : ℕ} (hn : 0 < n) (F : Za n) {gamma : ℝ}
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hbase : 0 < F.base.card)
    (hcard : (F.base.card : ℝ) ≤ gamma * n) :
    ZdL F
      (fun _ ↦ ZbT n F.base.card) := by
  classical
  apply ZfL hn
  · intro j
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · simp_rw [Zf6 hn hbase hgamma hcard]
    simp
    field_simp
    norm_num
  · intro j
    have hscale := ZkX hn hbase hgamma hcard
    have hlogscale :=
      ZgC hn hbase hgamma hcard
    have hpi : Real.pi ≤ (22 / 7 : ℝ) :=
      Real.pi_lt_d4.le.trans (by norm_num)
    rw [ZbT]
    simp only [Zmw]
    have hnonneg :
        0 ≤ (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          (Real.sqrt F.base.card * Real.sqrt n / n) := by
      have hlog := Zb6 hn hbase hgamma hcard
      positivity
    calc
      (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
          Real.sqrt (Fintype.card (↑F.base : Type)) *
          (24 * 128 * Real.pi * Real.sqrt n / n) =
        (24 * 128 * Real.pi) *
          ((14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (Real.sqrt F.base.card * Real.sqrt n / n)) := by
          simp only [Fintype.card_coe]
          ring
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          ((14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
            (Real.sqrt F.base.card * Real.sqrt n / n)) := by
          gcongr
      _ ≤ (24 * 128 * (22 / 7 : ℝ)) *
          (14 * ((28 / 5 : ℝ) / 2 ^ 20) + 30 * ((1 : ℝ) / 2 ^ 20)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (14 * Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) + 30) *
                (Real.sqrt F.base.card * Real.sqrt n / n) =
              14 * (Real.sqrt (Real.log ((16 * n : ℕ) / (F.base.card : ℝ))) *
                (Real.sqrt F.base.card * Real.sqrt n / n)) +
              30 * (Real.sqrt F.base.card * Real.sqrt n / n) := by ring
            _ ≤ 14 * ((28 / 5 : ℝ) / 2 ^ 20) +
                30 * ((1 : ℝ) / 2 ^ 20) := by gcongr
      _ ≤ 1 := by norm_num
theorem Zdw
    {n : ℕ} (F : Za n) (hbase : F.base.card = 0) :
    ∃ alpha : (↑F.base : Type) → ℝ,
      Xq.Discrepancy.Zcw alpha ∧
        ∀ j < n, |ZbJ F alpha j| ≤ 1 := by
  classical
  have hempty : F.base = ∅ := Finset.card_eq_zero.mp hbase
  have hisEmpty : IsEmpty (↑F.base : Type) := Finset.isEmpty_coe_sort.mpr hempty
  let alpha : (↑F.base : Type) → ℝ := fun _ ↦ 1
  refine ⟨alpha, fun I ↦ Or.inl rfl, ?_⟩
  intro j hj
  simp [ZbJ, hj]
end
end Xq.OddSine
end
section
namespace Xq.Kernel
open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral
lemma ZiI (n : ℕ) (t : ℝ) :
    2 * Real.sin t * (∑ j ∈ Finset.range n,
      Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      Real.sin ((2 * n : ℕ) * t) := by
  have hterm (j : ℕ) :
      2 * Real.sin t * Real.cos (((2 * j + 1 : ℕ) : ℝ) * t) =
        Real.sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          Real.sin (((2 * j : ℕ) : ℝ) * t) := by
    rw [Real.two_mul_sin_mul_cos]
    have hsub : t - ((2 * j + 1 : ℕ) : ℝ) * t =
        -(((2 * j : ℕ) : ℝ) * t) := by
      push_cast
      ring
    have hadd : t + ((2 * j + 1 : ℕ) : ℝ) * t =
        ((2 * (j + 1) : ℕ) : ℝ) * t := by
      push_cast
      ring
    rw [hsub, hadd, Real.sin_neg]
    ring
  calc
    2 * Real.sin t * (∑ j ∈ Finset.range n,
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
        ∑ j ∈ Finset.range n,
          (2 * Real.sin t * Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) := by
            rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range n,
        (Real.sin (((2 * (j + 1) : ℕ) : ℝ) * t) -
          Real.sin (((2 * j : ℕ) : ℝ) * t)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
    _ = Real.sin (((2 * n : ℕ) : ℝ) * t) - Real.sin 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_mul,
        Real.sin_zero] using
        (Finset.sum_range_sub
          (fun j : ℕ => Real.sin (((2 * j : ℕ) : ℝ) * t)) n)
    _ = Real.sin ((2 * n : ℕ) * t) := by simp
lemma Zhv (n : ℕ) {t : ℝ} (ht : Real.sin t ≠ 0) :
    2 * (∑ j ∈ Finset.range n,
      Real.cos (((2 * j + 1 : ℕ) : ℝ) * t)) =
      Real.sin ((2 * n : ℕ) * t) / Real.sin t := by
  have h := ZiI n t
  apply (eq_div_iff ht).2
  rw [← h]
  ring
lemma two_mul_sin_mul_sin (u v : ℝ) :
    2 * Real.sin u * Real.sin v = Real.cos (u - v) - Real.cos (u + v) := by
  rw [Real.cos_sub, Real.cos_add]
  ring
theorem Zkm (n : ℕ) {θ θ₀ : ℝ}
    (hsub : Real.sin (θ - θ₀) ≠ 0) (hadd : Real.sin (θ + θ₀) ≠ 0) :
    4 * (∑ j ∈ Finset.range n,
      Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
      Real.sin ((2 * n : ℕ) * (θ - θ₀)) / Real.sin (θ - θ₀) -
        Real.sin ((2 * n : ℕ) * (θ + θ₀)) / Real.sin (θ + θ₀) := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc, Finset.mul_sum]
  have hprod (j : ℕ) :
      2 * (Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
    calc
      2 * (Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
          Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ)) =
          2 * Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ₀) *
            Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ) := by ring
      _ = Real.cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) -
            (((2 * j + 1 : ℕ) : ℝ) * θ)) -
          Real.cos ((((2 * j + 1 : ℕ) : ℝ) * θ₀) +
            (((2 * j + 1 : ℕ) : ℝ) * θ)) :=
        two_mul_sin_mul_sin _ _
      _ = Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) -
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀)) := by
            have hneg : (((2 * j + 1 : ℕ) : ℝ) * θ₀) -
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                -(((2 * j + 1 : ℕ) : ℝ) * (θ - θ₀)) := by ring
            have hplus : (((2 * j + 1 : ℕ) : ℝ) * θ₀) +
                (((2 * j + 1 : ℕ) : ℝ) * θ) =
                ((2 * j + 1 : ℕ) : ℝ) * (θ + θ₀) := by ring
            rw [hneg, Real.cos_neg, hplus]
  rw [Finset.sum_congr rfl (fun j _ => hprod j), Finset.sum_sub_distrib,
    mul_sub, Zhv n hsub, Zhv n hadd]
lemma Ziq {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) :
      deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Real.sin_ge_sub_cube ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h
lemma Zir {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv (t : ℝ) :
      deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Ziq ht0]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  exact h
lemma ZkE {x : ℝ} (hx : 0 ≤ x) :
    Real.sinc x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (div_le_iff₀ hxpos).2
  nlinarith [Zir hxpos.le]
noncomputable def Zah (b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, Real.sinc x
lemma ZkY {b : ℝ} (hb : 0 ≤ b) :
    Zah b ≤ b - b ^ 3 / 18 + b ^ 5 / 600 := by
  have hs : IntervalIntegrable Real.sinc volume 0 b :=
    Real.continuous_sinc.intervalIntegrable 0 b
  have hp1 : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2 / 6) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => 1 - x ^ 2 / 6)).intervalIntegrable 0 b
  have hp2 : IntervalIntegrable (fun x : ℝ => x ^ 4 / 120) volume 0 b :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4 / 120)).intervalIntegrable 0 b
  have hp : IntervalIntegrable
      (fun x : ℝ => 1 - x ^ 2 / 6 + x ^ 4 / 120) volume 0 b := hp1.add hp2
  have hmono := intervalIntegral.integral_mono_on hb hs hp
    (fun x hx => ZkE hx.1)
  calc
    Zah b = ∫ x in (0 : ℝ)..b, Real.sinc x := rfl
    _ ≤ ∫ x in (0 : ℝ)..b, (1 - x ^ 2 / 6 + x ^ 4 / 120) := hmono
    _ = b - b ^ 3 / 18 + b ^ 5 / 600 := by
      rw [intervalIntegral.integral_add hp1 hp2]
      simp [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow]
      ring
theorem Zgr : Zah Real.pi < 2 := by
  have hSi := ZkY Real.pi_pos.le
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hcube : (3.14 : ℝ) ^ 3 < Real.pi ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d2 (by norm_num) (by norm_num)
  have hfifth : Real.pi ^ 5 < (3.15 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
  norm_num at hpi hcube hfifth ⊢
  nlinarith
end Xq.Kernel
end
section
namespace Xq.OddKernelIdentity
open scoped BigOperators Interval
open Set MeasureTheory
noncomputable section
def oddKernel (n : ℕ) (x theta : ℝ) : ℝ :=
  4 * ∑ j ∈ Finset.range n,
    Real.sin ((Xq.Rounding.Zl j : ℝ) * x) *
      Real.sin ((Xq.Rounding.Zl j : ℝ) * theta)
def ZcM (n : ℕ) (I : Xq.OddSine.RealInterval)
    (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2, oddKernel n x theta
theorem Zii (n : ℕ)
    (I : Xq.OddSine.RealInterval) (theta : ℝ) :
    ZcM n I theta =
      4 * ∑ j ∈ Finset.range n,
        (∫ x in I.1..I.2,
          Real.sin ((Xq.Rounding.Zl j : ℝ) * x)) *
            Real.sin ((Xq.Rounding.Zl j : ℝ) * theta) := by
  classical
  simp only [ZcM, oddKernel,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_mul_const]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.sin ((Xq.Rounding.Zl j : ℝ) * x) *
        Real.sin ((Xq.Rounding.Zl j : ℝ) * theta))).intervalIntegrable _ _
theorem Ze4 {n : ℕ}
    (F : Xq.OddSine.Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Xq.OddSine.ZaU F alpha theta =
      (Xq.OddSine.K * Real.sqrt n) *
        ∑ I : (↑F.base : Type), alpha I * ZcM n I.1 theta := by
  classical
  rw [show Xq.OddSine.ZaU F alpha theta =
      ∑ j ∈ Finset.range n,
        (∑ I : (↑F.base : Type),
          alpha I * (4 * Xq.OddSine.K * Real.sqrt n *
            ∫ x in I.1.1..I.1.2,
              Real.sin ((Xq.Rounding.Zl j : ℝ) * x))) *
          Real.sin ((Xq.Rounding.Zl j : ℝ) * theta) by
    simp only [Xq.OddSine.ZaU,
      Xq.Rounding.ZL]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Xq.OddSine.ZbJ,
      dif_pos (Finset.mem_range.mp hj)]
  ]
  simp_rw [Zii]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro j hj
  ring
theorem Zed {n : ℕ} (hn : 0 < n)
    (F : Xq.OddSine.Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Xq.OddSine.ZaU F alpha theta /
        (Xq.OddSine.K * Real.sqrt n) =
      ∑ I : (↑F.base : Type), alpha I * ZcM n I.1 theta := by
  rw [Ze4]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num [Xq.OddSine.K])
    (Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)))
theorem Zj0 (n : ℕ) {x theta : ℝ}
    (hsub : Real.sin (x - theta) ≠ 0)
    (hadd : Real.sin (x + theta) ≠ 0) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) := by
  simpa [oddKernel, Xq.Rounding.Zl, mul_comm] using
    (Xq.Kernel.Zkm n
      (θ := x) (θ₀ := theta) hsub hadd)
theorem ZeO (n : ℕ) {x theta : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < Real.pi / 2)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hxt : x ≠ theta) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) := by
  rcases htheta with ⟨ht₀, ht₁⟩
  apply Zj0
  · intro hzero
    have hdiff : x - theta = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp hzero
    exact hxt (sub_eq_zero.mp hdiff)
  · intro hzero
    have hsum : x + theta = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp hzero
    linarith
theorem Zdc (n : ℕ)
    {a b theta : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ x in a..b, oddKernel n x theta) =
      ∫ x in a..b,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume theta] with x hxt hx
  rw [uIoc_of_le hab] at hx
  exact ZeO n
    (ha.trans hx.1) (hx.2.trans_lt hb) htheta hxt
theorem Zb7 {n : ℕ}
    (hn : 0 < n) (F : Xq.OddSine.Za n)
    (I : Xq.OddSine.RealInterval) (hI : I ∈ F.base)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ZcM n I theta =
      ∫ x in I.1..I.2,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < 100 * Real.pi / (n : ℝ) := by positivity
  apply Zdc n
  · exact F.ordered I hI
  · linarith [F.away_from_axes I hI |>.1]
  · linarith [F.away_from_axes I hI |>.2]
  · exact htheta
theorem Zcf {n : ℕ}
    (hn : 0 < n) (F : Xq.OddSine.Za n)
    (alpha : (↑F.base : Type) → ℝ) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Xq.OddSine.ZaU F alpha theta /
        (Xq.OddSine.K * Real.sqrt n) =
      ∑ I : (↑F.base : Type), alpha I *
        ∫ x in I.1.1..I.1.2,
          (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
            Real.sin ((2 * n : ℕ) * (x + theta)) /
              Real.sin (x + theta)) := by
  rw [Zed hn]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Zb7
    hn F I.1 I.2 htheta]
end
end Xq.OddKernelIdentity
end
section
namespace Xq.KernelNearGeometry
open scoped BigOperators
open Set
noncomputable section
open Xq.OddSine
def Zdd (theta : ℝ) (I : RealInterval) : ℝ :=
  max (I.1 - theta) (max (theta - I.2) 0)
theorem ZeX {theta : ℝ} {I : RealInterval}
    (htheta : Zal I theta) :
    Zdd theta I = 0 := by
  rw [Zal, mem_Icc] at htheta
  simp only [Zdd]
  rw [max_eq_right (sub_nonpos.mpr htheta.2)]
  rw [max_eq_right (sub_nonpos.mpr htheta.1)]
theorem ZcN {theta : ℝ} {I : RealInterval}
    (hI : I.1 ≤ I.2) (htheta : theta ≤ I.1) :
    Zdd theta I = I.1 - theta := by
  have htheta' : theta ≤ I.2 := htheta.trans hI
  simp only [Zdd]
  rw [max_eq_right (sub_nonpos.mpr htheta')]
  rw [max_eq_left (sub_nonneg.mpr htheta)]
theorem Zck {theta : ℝ} {I : RealInterval}
    (hI : I.1 ≤ I.2) (htheta : I.2 ≤ theta) :
    Zdd theta I = theta - I.2 := by
  have htheta' : I.1 ≤ theta := hI.trans htheta
  simp only [Zdd]
  rw [max_eq_left (sub_nonneg.mpr htheta)]
  rw [max_eq_right]
  exact (sub_nonpos.mpr htheta').trans (sub_nonneg.mpr htheta)
def Near (n : ℕ) (theta : ℝ) (I : RealInterval) : Prop :=
  Zdd theta I < Real.pi / n
noncomputable def ZeP {n : ℕ} (F : Za n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (Near n theta) (Classical.decPred _) F.base
def Zh0 {n : ℕ} (F : Za n) (theta : ℝ) : Prop :=
  ∃ I ∈ F.base, Zal I theta
noncomputable def ZcF {n : ℕ} (F : Za n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (fun I ↦ Near n theta I ∧ I.2 < theta)
    (Classical.decPred _) F.base
noncomputable def Zca {n : ℕ} (F : Za n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (fun I ↦ Near n theta I ∧ theta < I.1)
    (Classical.decPred _) F.base
noncomputable def Zu {n : ℕ} (F : Za n)
    (theta : ℝ) : Finset (↑F.base : Type) :=
  @Finset.filter (↑F.base : Type) (fun I ↦ Near n theta I.1)
    (Classical.decPred _) Finset.univ
theorem Zei {n : ℕ}
    (F : Za n) (theta : ℝ) :
    ZeP F theta =
      (Zu F theta).image (fun I ↦ I.1) := by
  classical
  ext I
  simp [ZeP, Zu, and_comm]
theorem ZdS {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I J : RealInterval}
    (hI : I ∈ F.base) (hJ : J ∈ F.base)
    (hthetaI : Zal I theta) (hthetaJ : Zal J theta) :
    I = J := by
  by_contra hne
  have hsep := F.separated hI hJ hne theta hthetaI theta hthetaJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  exact (not_le_of_gt hpi) (by simpa using hsep)
theorem Zh1 {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I J : RealInterval}
    (hI : I ∈ F.base) (hJ : J ∈ F.base) (hne : I ≠ J)
    (htheta : Zal I theta) :
    Real.pi / n ≤ Zdd theta J := by
  have hnotJ : ¬Zal J theta := by
    intro hthetaJ
    exact hne (ZdS hn F hI hJ htheta hthetaJ)
  rw [Zal, mem_Icc] at hnotJ
  rcases not_and_or.mp hnotJ with hleft | hright
  · have hleft' : theta < J.1 := lt_of_not_ge hleft
    rw [ZcN (F.ordered J hJ) hleft'.le]
    have hsep := F.separated hI hJ hne theta htheta J.1
      ⟨le_rfl, F.ordered J hJ⟩
    rw [abs_of_neg (sub_neg.mpr hleft')] at hsep
    linarith
  · have hright' : J.2 < theta := lt_of_not_ge hright
    rw [Zck (F.ordered J hJ) hright'.le]
    have hsep := F.separated hI hJ hne theta htheta J.2
      ⟨F.ordered J hJ, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hright')] at hsep
    exact hsep
theorem Ze5 {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : Zal I theta) :
    Zu F theta = {⟨I, hI⟩} := by
  classical
  ext J
  simp only [Zu, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hnear
    apply Subtype.ext
    by_contra hne
    have hgap := Zh1 hn F hI J.property
      (fun h ↦ hne h.symm) htheta
    exact (not_lt_of_ge hgap) hnear
  · intro hJI
    subst J
    rw [Near, ZeX htheta]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos Real.pi_pos hnR
theorem Zdx {n : ℕ}
    (F : Za n) (theta : ℝ) :
    (Zu F theta).card = (ZeP F theta).card := by
  rw [Zei]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
theorem ZcG {n : ℕ}
    (F : Za n) {theta : ℝ}
    (hout : ¬Zh0 F theta) :
    ZeP F theta =
      ZcF F theta ∪ Zca F theta := by
  classical
  ext I
  simp only [ZeP, ZcF, Zca,
    Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hI, hnear⟩
    have hnot : ¬Zal I theta := fun h ↦ hout ⟨I, hI, h⟩
    rw [Zal, mem_Icc] at hnot
    rcases not_and_or.mp hnot with hright | hleft
    · exact Or.inr ⟨hI, hnear, lt_of_not_ge hright⟩
    · exact Or.inl ⟨hI, hnear, lt_of_not_ge hleft⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, hleft.2.1⟩
    · exact ⟨hright.1, hright.2.1⟩
theorem Zhh {n : ℕ} (_hn : 0 < n)
    (F : Za n) (theta : ℝ) :
    (ZcF F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  simp only [ZcF, Finset.mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.2
    ⟨F.ordered I hI.1, le_rfl⟩ J.2 ⟨F.ordered J hJ.1, le_rfl⟩
  have hgapI : theta - I.2 < Real.pi / n := by
    rw [← Zck (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : theta - J.2 < Real.pi / n := by
    rw [← Zck (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.2 - J.2| < Real.pi / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs
theorem ZgY {n : ℕ} (_hn : 0 < n)
    (F : Za n) (theta : ℝ) :
    (Zca F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  simp only [Zca, Finset.mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.1
    ⟨le_rfl, F.ordered I hI.1⟩ J.1 ⟨le_rfl, F.ordered J hJ.1⟩
  have hgapI : I.1 - theta < Real.pi / n := by
    rw [← ZcN (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : J.1 - theta < Real.pi / n := by
    rw [← ZcN (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.1 - J.1| < Real.pi / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs
theorem Zdy {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (hout : ¬Zh0 F theta) :
    (ZeP F theta).card ≤ 2 := by
  rw [ZcG F hout]
  calc
    (ZcF F theta ∪ Zca F theta).card ≤
        (ZcF F theta).card +
          (Zca F theta).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (Zhh hn F theta)
      (ZgY hn F theta)
    _ = 2 := rfl
theorem Zc3 {n : ℕ}
    (hn : 0 < n) (F : Za n) {theta : ℝ}
    (hout : ¬Zh0 F theta) :
    (Zu F theta).card ≤ 2 := by
  rw [Zdx]
  exact Zdy hn F hout
theorem ZcH {n : ℕ}
    (hn : 0 < n) (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hdangerous : ZaH F theta) :
    ∃! I : RealInterval, I ∈ F.base ∧ Zal I theta := by
  rcases hdangerous with ⟨I, hI, hmain | hneg | hreflect | htranslate⟩
  · refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact ZdS hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [Zal, mem_Icc] at hneg
    have htheta0 : theta = 0 := by linarith [htheta.1, hquadI.1, hneg.1]
    have hmain : Zal I theta := by
      rw [Zal, mem_Icc]
      simpa [htheta0] using hneg
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact ZdS hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [Zal, mem_Icc] at hreflect
    have hthetaMid : theta = Real.pi / 2 := by
      linarith [htheta.2, hquadI.2, hreflect.2]
    have harg : Real.pi - theta = theta := by
      rw [hthetaMid]
      ring
    have hmain : Zal I theta := by
      rw [Zal, mem_Icc, ← harg]
      exact hreflect
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact ZdS hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [Zal, mem_Icc] at htranslate
    exfalso
    nlinarith [htheta.2, hquadI.1, htranslate.1, Real.pi_pos]
theorem ZcO {n : ℕ}
    (hn : 0 < n) (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hdangerous : ZaH F theta) :
    ∃! I : (↑F.base : Type), Zal I.1 theta := by
  obtain ⟨I, hI, hunique⟩ :=
    ZcH hn F htheta hdangerous
  refine ⟨⟨I, hI.1⟩, hI.2, ?_⟩
  intro J hthetaJ
  apply Subtype.ext
  exact hunique J.1 ⟨J.property, hthetaJ⟩
theorem Zdo {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : Zal I theta)
    (f : (↑F.base : Type) → ℝ) :
    ∑ J ∈ Zu F theta, f J = f ⟨I, hI⟩ := by
  rw [Ze5 hn F hI htheta]
  simp
theorem Zcg {n : ℕ}
    (hn : 0 < n) (F : Za n) {theta C : ℝ}
    (hout : ¬Zh0 F theta) (hC : 0 ≤ C)
    (f : (↑F.base : Type) → ℝ)
    (hf : ∀ I ∈ Zu F theta, |f I| ≤ C) :
    |∑ I ∈ Zu F theta, f I| ≤ 2 * C := by
  classical
  have hcard := Zc3 hn F hout
  calc
    |∑ I ∈ Zu F theta, f I| ≤
        ∑ I ∈ Zu F theta, |f I| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I ∈ Zu F theta, C := by
      exact Finset.sum_le_sum fun I hI ↦ hf I hI
    _ = ((Zu F theta).card : ℝ) * C := by simp
    _ ≤ 2 * C := by
      gcongr
      exact_mod_cast hcard
end
end Xq.KernelNearGeometry
end
section
namespace Xq.SineIntegralGrid
open scoped Interval
open Real Set MeasureTheory intervalIntegral
noncomputable section
private def ZaI (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040
private def Zbi (x : ℝ) : ℝ :=
  1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3
private lemma ZkF {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  let q (t : ℝ) := Real.cos t -
    (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hqderiv (t : ℝ) :
      deriv q t = -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    simp (disch := fun_prop) [q]
    ring
  have hqmono : MonotoneOn q (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hqderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Xq.Kernel.Zir ht0]
  have hq {t : ℝ} (ht : 0 ≤ t) :
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
    have h := hqmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show t ∈ Ici 0 by exact ht) ht
    dsimp [q] at h
    norm_num at h
    linarith
  let f (t : ℝ) := Real.sin t -
    (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hfderiv (t : ℝ) :
      deriv f t = Real.cos t -
        (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
    simp (disch := fun_prop) [f]
    ring
  have hfmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hfderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [hq ht0]
  have h := hfmono (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  linarith
private lemma Zh2 {x : ℝ} (hx : 0 ≤ x) :
    ZaI x ≤ Real.sinc x := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num [ZaI]
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (le_div_iff₀ hxpos).2
  have h := ZkF hxpos.le
  dsimp [ZaI]
  nlinarith
private lemma Zee {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) : 0 ≤ Real.sinc x := by
  obtain rfl | hxpos := hx0.eq_or_lt
  · simp
  rw [Real.sinc_of_ne_zero hxpos.ne']
  exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi) hx0
private lemma Zj1 {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) : 0 ≤ Zbi x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu0 : 0 ≤ x / Real.pi := div_nonneg hx0 hpi.le
  have hu1 : x / Real.pi ≤ 1 := (div_le_one hpi).2 hxpi
  dsimp [Zbi]
  nlinarith [sq_nonneg (x / Real.pi)]
private lemma Zi9 {x : ℝ} (hx0 : 0 ≤ x)
    (_ : x ≤ Real.pi) :
    Zbi x ≤ Real.pi / (x + Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxpi_pos : 0 < x + Real.pi := add_pos_of_nonneg_of_pos hx0 hpi
  apply (le_div_iff₀ hxpi_pos).2
  dsimp [Zbi]
  field_simp
  ring_nf
  nlinarith [sq_nonneg (x ^ 2)]
private lemma Zj2 (x : ℝ) (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) :
    Real.sinc x + Real.sinc (x + Real.pi) =
      Real.sinc x * (Real.pi / (x + Real.pi)) := by
  by_cases hx : x = 0
  · subst x
    simp [Real.sinc_of_ne_zero Real.pi_ne_zero]
  have hxpi0 : x + Real.pi ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx, Real.sinc_of_ne_zero hxpi0, Real.sin_add_pi]
  field_simp
  ring
private lemma ZkZ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    ZaI x * Zbi x ≤
      Real.sinc x + Real.sinc (x + Real.pi) := by
  have hsinc0 := Zee hx.1 hx.2
  have hpoly := Zh2 hx.1
  have hgeom0 := Zj1 hx.1 hx.2
  have hweight := Zi9 hx.1 hx.2
  rw [Zj2 x hx.1 hx.2]
  exact (mul_le_mul_of_nonneg_right hpoly hgeom0).trans
    (mul_le_mul_of_nonneg_left hweight hsinc0)
private lemma Zja :
    (∫ x in (0 : ℝ)..Real.pi,
      ZaI x * Zbi x) =
      -(73 * Real.pi ^ 7) / 12700800 +
        43 * Real.pi ^ 5 / 100800 - 7 * Real.pi ^ 3 / 360 +
          7 * Real.pi / 12 := by
  let F (x : ℝ) :=
    -x ^ 7 / 35280 + x ^ 5 / 600 - x ^ 3 / 18 + x +
    x ^ 8 / (40320 * Real.pi) - x ^ 6 / (720 * Real.pi) +
    x ^ 4 / (24 * Real.pi) - x ^ 2 / (2 * Real.pi) -
    x ^ 9 / (45360 * Real.pi ^ 2) + x ^ 7 / (840 * Real.pi ^ 2) -
    x ^ 5 / (30 * Real.pi ^ 2) + x ^ 3 / (3 * Real.pi ^ 2) +
    x ^ 10 / (50400 * Real.pi ^ 3) - x ^ 8 / (960 * Real.pi ^ 3) +
    x ^ 6 / (36 * Real.pi ^ 3) - x ^ 4 / (4 * Real.pi ^ 3)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := fun x => ZaI x * Zbi x)]
  · dsimp [F]
    field_simp [Real.pi_ne_zero]
    ring
  · intro x hx
    have hdiff : DifferentiableAt ℝ F x := by
      dsimp [F]
      fun_prop
    have hderiv : deriv F x =
        ZaI x * Zbi x := by
      simp (disch := fun_prop) [F, ZaI, Zbi]
      field_simp [Real.pi_ne_zero]
      ring
    rw [← hderiv]
    exact hdiff.hasDerivAt
  · exact (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3))).intervalIntegrable _ _
private lemma Zew :
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..Real.pi,
      ZaI x * Zbi x := by
  rw [Zja]
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi' : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have h3 : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi' Real.pi_pos.le (by norm_num)
  have h5 : (3.14 : ℝ) ^ 5 < Real.pi ^ 5 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  have h7 : Real.pi ^ 7 < (3.15 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hpi' Real.pi_pos.le (by norm_num)
  norm_num at hpi hpi' h3 h5 h7 ⊢
  linarith
theorem Za7 :
    (4 : ℝ) / 3 < Xq.Kernel.Zah (2 * Real.pi) := by
  have hsinc : IntervalIntegrable Real.sinc volume (0 : ℝ) Real.pi :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hsinc' : IntervalIntegrable (fun x : ℝ => Real.sinc (x + Real.pi))
      volume (0 : ℝ) Real.pi :=
    (Real.continuous_sinc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hpoly : IntervalIntegrable
      (fun x : ℝ => ZaI x * Zbi x)
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on Real.pi_pos.le hpoly
    (hsinc.add hsinc') ZkZ
  calc
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..Real.pi,
        ZaI x * Zbi x :=
      Zew
    _ ≤ ∫ x in (0 : ℝ)..Real.pi,
        (Real.sinc x + Real.sinc (x + Real.pi)) := hmono
    _ = Xq.Kernel.Zah (2 * Real.pi) := by
      rw [intervalIntegral.integral_add hsinc hsinc']
      rw [intervalIntegral.integral_comp_add_right Real.sinc Real.pi]
      have hadd := intervalIntegral.integral_add_adjacent_intervals hsinc
        (Real.continuous_sinc.intervalIntegrable Real.pi (2 * Real.pi))
      unfold Xq.Kernel.Zah
      convert hadd using 1
      ring_nf
private def Zb (k : ℕ) : ℝ := (k : ℝ) * (2 * Real.pi)
private lemma Zhi (k : ℕ) : 0 ≤ Zb k := by
  exact mul_nonneg (Nat.cast_nonneg k) (by positivity)
private lemma Zk0 {k : ℕ} (hk : 0 < k) : 0 < Zb k := by
  dsimp [Zb]
  exact mul_pos (by exact_mod_cast hk) (by positivity)
private lemma ZcI (k : ℕ) (x : ℝ) :
    Real.sin (Zb k + x) = Real.sin x := by
  rw [add_comm]
  exact Real.sin_add_nat_mul_two_pi x k
private lemma Zj3 {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    0 ≤ Real.sinc (Zb k + x) +
      Real.sinc (Zb k + Real.pi + x) := by
  have hc : 0 < Zb k := Zk0 hk
  have hcx : 0 < Zb k + x := add_pos_of_pos_of_nonneg hc hx0
  have hcxpi : 0 < Zb k + Real.pi + x := by positivity
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [Real.sinc_of_ne_zero hcx.ne', Real.sinc_of_ne_zero hcxpi.ne']
  rw [ZcI]
  have hphase : Zb k + Real.pi + x = Zb k + (x + Real.pi) := by ring
  rw [hphase, ZcI, Real.sin_add_pi]
  have hden : Zb k + x ≤ Zb k + (x + Real.pi) := by
    linarith [Real.pi_pos]
  have hrecip := one_div_le_one_div_of_le hcx hden
  calc
    0 ≤ Real.sin x *
        (1 / (Zb k + x) - 1 / (Zb k + (x + Real.pi))) :=
      mul_nonneg hsin (sub_nonneg.2 hrecip)
    _ = Real.sin x / (Zb k + x) +
        -Real.sin x / (Zb k + (x + Real.pi)) := by ring
private lemma Zkn (k : ℕ)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    Real.sinc (Zb k + Real.pi + x) +
      Real.sinc (Zb (k + 1) + x) ≤ 0 := by
  have hfirst : 0 < Zb k + Real.pi + x := by
    have := Zhi k
    positivity
  have hsecond : 0 < Zb (k + 1) + x := by
    apply add_pos_of_pos_of_nonneg
    · exact Zk0 (Nat.succ_pos k)
    · exact hx0
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [Real.sinc_of_ne_zero hfirst.ne', Real.sinc_of_ne_zero hsecond.ne']
  have hphase1 : Zb k + Real.pi + x = Zb k + (x + Real.pi) := by ring
  rw [hphase1, ZcI, Real.sin_add_pi, ZcI]
  have heven : Zb (k + 1) = Zb k + 2 * Real.pi := by
    simp [Zb]
    ring
  have hden : Zb k + (x + Real.pi) ≤ Zb (k + 1) + x := by
    rw [heven]
    linarith [Real.pi_pos]
  have hfirst' : 0 < Zb k + (x + Real.pi) := by
    linarith
  have hrecip := one_div_le_one_div_of_le hfirst' hden
  calc
    -Real.sin x / (Zb k + (x + Real.pi)) +
        Real.sin x / (Zb (k + 1) + x) =
        Real.sin x *
          (1 / (Zb (k + 1) + x) -
            1 / (Zb k + (x + Real.pi))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsin (sub_nonpos.2 hrecip)
private lemma Zbw {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, f x ≤ 0) :
    (∫ x in a..b, f x) ≤ 0 := by
  have h := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun x hx => neg_nonneg.2 (hf x hx))
  rw [intervalIntegral.integral_neg] at h
  linarith
private lemma Zgs {k : ℕ} (hk : 0 < k) :
    0 ≤ ∫ x in Zb k..Zb (k + 1), Real.sinc x := by
  have hs : IntervalIntegrable Real.sinc volume
      (Zb k) (Zb k + Real.pi) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable Real.sinc volume
      (Zb k + Real.pi) (Zb (k + 1)) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hshift1 := intervalIntegral.integral_comp_add_right Real.sinc (Zb k)
    (a := (0 : ℝ)) (b := Real.pi)
  have hshift2 := intervalIntegral.integral_comp_add_right Real.sinc
    (Zb k + Real.pi) (a := (0 : ℝ)) (b := Real.pi)
  have hp : 0 ≤ ∫ x in (0 : ℝ)..Real.pi,
      (Real.sinc (Zb k + x) +
        Real.sinc (Zb k + Real.pi + x)) := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro x hx
    exact Zj3 hk hx.1 hx.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in Zb k..Zb k + Real.pi, Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (Zb k + x) := by
    rw [add_comm (Zb k)]
    convert hshift1.symm using 1 <;> ring_nf
  have hi2 : (∫ x in Zb k + Real.pi..Zb (k + 1), Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (Zb k + Real.pi + x) := by
    convert hshift2.symm using 1 <;> simp [Zb] <;> ring_nf
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable (fun x : ℝ => Real.sinc (Zb k + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => Real.sinc (Zb k + Real.pi + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp
private lemma ZgZ (k : ℕ) :
    (∫ x in Zb k + Real.pi..Zb (k + 1) + Real.pi,
      Real.sinc x) ≤ 0 := by
  have hs : IntervalIntegrable Real.sinc volume
      (Zb k + Real.pi) (Zb (k + 1)) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable Real.sinc volume
      (Zb (k + 1)) (Zb (k + 1) + Real.pi) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hshift1 := intervalIntegral.integral_comp_add_right Real.sinc
    (Zb k + Real.pi) (a := (0 : ℝ)) (b := Real.pi)
  have hshift2 := intervalIntegral.integral_comp_add_right Real.sinc
    (Zb (k + 1)) (a := (0 : ℝ)) (b := Real.pi)
  have hp : (∫ x in (0 : ℝ)..Real.pi,
      (Real.sinc (Zb k + Real.pi + x) +
        Real.sinc (Zb (k + 1) + x))) ≤ 0 := by
    apply Zbw Real.pi_pos.le
    intro x hx
    exact Zkn k hx.1 hx.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in Zb k + Real.pi..Zb (k + 1), Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (Zb k + Real.pi + x) := by
    convert hshift1.symm using 1 <;> simp [Zb] <;> ring_nf
  have hi2 : (∫ x in Zb (k + 1)..Zb (k + 1) + Real.pi,
      Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (Zb (k + 1) + x) := by
    rw [add_comm (Zb (k + 1))]
    convert hshift2.symm using 1 <;> ring_nf
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable
      (fun x : ℝ => Real.sinc (Zb k + Real.pi + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => Real.sinc (Zb (k + 1) + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp
private lemma Zg0 (k : ℕ) {x : ℝ}
    (hlo : Zb k ≤ x) (hhi : x ≤ Zb k + Real.pi) :
    0 ≤ Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : 0 ≤ x := (Zhi k).trans hlo
  have ht0 : 0 ≤ x - Zb k := sub_nonneg.2 hlo
  have htpi : x - Zb k ≤ Real.pi := by linarith
  have hsin_t : 0 ≤ Real.sin (x - Zb k) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : Zb k + (x - Zb k) = x := by ring
  have hsin : Real.sin x = Real.sin (x - Zb k) := by
    calc
      Real.sin x = Real.sin (Zb k + (x - Zb k)) :=
        congrArg Real.sin hphase.symm
      _ = Real.sin (x - Zb k) := ZcI _ _
  rw [Real.sinc_of_ne_zero hx, hsin]
  exact div_nonneg hsin_t hx0
private lemma Zdj (k : ℕ) {x : ℝ}
    (hlo : Zb k + Real.pi ≤ x) (hhi : x ≤ Zb (k + 1)) :
    Real.sinc x ≤ 0 := by
  have hc0 := Zhi k
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith [Real.pi_pos] :
    0 < Zb k + Real.pi) hlo
  let t := x - (Zb k + Real.pi)
  have ht0 : 0 ≤ t := sub_nonneg.2 hlo
  have heven : Zb (k + 1) = Zb k + 2 * Real.pi := by
    simp [Zb]
    ring
  have htpi : t ≤ Real.pi := by
    dsimp [t]
    rw [heven] at hhi
    linarith
  have hsint : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : x = Zb k + (t + Real.pi) := by
    dsimp [t]
    ring
  have hden : 0 ≤ Zb k + (t + Real.pi) := by
    rw [← hphase]
    exact hxpos.le
  rw [Real.sinc_of_ne_zero hxpos.ne', hphase, ZcI,
    Real.sin_add_pi]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hsint) hden
private lemma ZiJ {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hlo : Zb k ≤ x) (hhi : x ≤ Zb (k + 1)) :
    0 ≤ ∫ t in Zb k..x, Real.sinc t := by
  by_cases hmid : x ≤ Zb k + Real.pi
  · apply intervalIntegral.integral_nonneg (μ := volume) hlo
    intro t ht
    exact Zg0 k ht.1 (ht.2.trans hmid)
  · have hxmid : Zb k + Real.pi ≤ x := le_of_not_ge hmid
    have htail : (∫ t in x..Zb (k + 1), Real.sinc t) ≤ 0 := by
      apply Zbw hhi
      intro t ht
      exact Zdj k (hxmid.trans ht.1) ht.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (Zb k) x)
      (Real.continuous_sinc.intervalIntegrable x (Zb (k + 1)))
    linarith [Zgs hk]
private lemma Zjb (k : ℕ) {x : ℝ}
    (hlo : Zb k + Real.pi ≤ x)
    (hhi : x ≤ Zb (k + 1) + Real.pi) :
    (∫ t in Zb k + Real.pi..x, Real.sinc t) ≤ 0 := by
  by_cases hmid : x ≤ Zb (k + 1)
  · apply Zbw hlo
    intro t ht
    exact Zdj k ht.1 (ht.2.trans hmid)
  · have hxmid : Zb (k + 1) ≤ x := le_of_not_ge hmid
    have htail : 0 ≤ ∫ t in x..Zb (k + 1) + Real.pi,
        Real.sinc t := by
      apply intervalIntegral.integral_nonneg (μ := volume) hhi
      intro t ht
      exact Zg0 (k + 1) (hxmid.trans ht.1) ht.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (Zb k + Real.pi) x)
      (Real.continuous_sinc.intervalIntegrable x (Zb (k + 1) + Real.pi))
    linarith [ZgZ k]
private lemma Zj4 (k : ℕ) :
    0 ≤ ∫ x in Zb 1..Zb (k + 1), Real.sinc x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (Zb 1) (Zb (k + 1)))
        (Real.continuous_sinc.intervalIntegrable (Zb (k + 1))
          (Zb (k + 2)))
      have hblock := Zgs (k := k + 1) (Nat.succ_pos k)
      rw [← hadd]
      exact add_nonneg ih hblock
private lemma Zko (k : ℕ) :
    (∫ x in Real.pi..Zb k + Real.pi, Real.sinc x) ≤ 0 := by
  induction k with
  | zero => simp [Zb]
  | succ k ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable Real.pi (Zb k + Real.pi))
        (Real.continuous_sinc.intervalIntegrable (Zb k + Real.pi)
          (Zb (k + 1) + Real.pi))
      have hblock := ZgZ k
      rw [← hadd]
      exact add_nonpos ih hblock
private lemma ZcR {x : ℝ}
    (hlo : Zb 1 ≤ x) (hhi : x ≤ Zb 7) :
    0 ≤ ∫ t in Zb 1..x, Real.sinc t := by
  have join (k : ℕ) (hk : 0 < k) (hklow : Zb k ≤ x)
      (hkhi : x ≤ Zb (k + 1)) :
      0 ≤ ∫ t in Zb 1..x, Real.sinc t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (Zb 1) (Zb k))
      (Real.continuous_sinc.intervalIntegrable (Zb k) x)
    rw [← hadd]
    exact add_nonneg (by simpa [Nat.sub_add_cancel hk] using Zj4 (k - 1))
      (ZiJ hk hklow hkhi)
  by_cases h2 : x ≤ Zb 2
  · exact join 1 (by norm_num) hlo h2
  by_cases h3 : x ≤ Zb 3
  · exact join 2 (by norm_num) (le_of_not_ge h2) h3
  by_cases h4 : x ≤ Zb 4
  · exact join 3 (by norm_num) (le_of_not_ge h3) h4
  by_cases h5 : x ≤ Zb 5
  · exact join 4 (by norm_num) (le_of_not_ge h4) h5
  by_cases h6 : x ≤ Zb 6
  · exact join 5 (by norm_num) (le_of_not_ge h5) h6
  exact join 6 (by norm_num) (le_of_not_ge h6) hhi
private lemma Zf7 {x : ℝ}
    (hlo : Real.pi ≤ x) (hhi : x ≤ Zb 7) :
    (∫ t in Real.pi..x, Real.sinc t) ≤ 0 := by
  have join (k : ℕ) (hklow : Zb k + Real.pi ≤ x)
      (hkhi : x ≤ Zb (k + 1) + Real.pi) :
      (∫ t in Real.pi..x, Real.sinc t) ≤ 0 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable Real.pi (Zb k + Real.pi))
      (Real.continuous_sinc.intervalIntegrable (Zb k + Real.pi) x)
    rw [← hadd]
    exact add_nonpos (Zko k)
      (Zjb k hklow hkhi)
  by_cases h1 : x ≤ Zb 1 + Real.pi
  · exact join 0 (by simpa [Zb] using hlo) h1
  by_cases h2 : x ≤ Zb 2 + Real.pi
  · exact join 1 (le_of_not_ge h1) h2
  by_cases h3 : x ≤ Zb 3 + Real.pi
  · exact join 2 (le_of_not_ge h2) h3
  by_cases h4 : x ≤ Zb 4 + Real.pi
  · exact join 3 (le_of_not_ge h3) h4
  by_cases h5 : x ≤ Zb 5 + Real.pi
  · exact join 4 (le_of_not_ge h4) h5
  by_cases h6 : x ≤ Zb 6 + Real.pi
  · exact join 5 (le_of_not_ge h5) h6
  have hlast : x ≤ Zb 7 + Real.pi := hhi.trans (le_add_of_nonneg_right Real.pi_pos.le)
  exact join 6 (le_of_not_ge h6) hlast
theorem ZaN {x : ℝ} (hx0 : 0 ≤ x)
    (hx14 : x ≤ 14 * Real.pi) :
    Xq.Kernel.Zah x ∈ Icc (0 : ℝ) 2 := by
  have hxEven : x ≤ Zb 7 := by
    dsimp [Zb]
    convert hx14 using 1
    ring
  constructor
  · by_cases hxpi : x ≤ Real.pi
    · apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact Zee ht.1 (ht.2.trans hxpi)
    by_cases hx2 : x ≤ Zb 1
    · have htail : (∫ t in x..Zb 1, Real.sinc t) ≤ 0 := by
        apply Zbw hx2
        intro t ht
        have htpi : Real.pi ≤ t := (le_of_not_ge hxpi).trans ht.1
        exact Zdj 0 (by simpa [Zb] using htpi) ht.2
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (Real.continuous_sinc.intervalIntegrable x (Zb 1))
      have hfirst := Za7
      unfold Xq.Kernel.Zah at hfirst ⊢
      have heq : Zb 1 = 2 * Real.pi := by simp [Zb]
      rw [heq] at hadd htail
      linarith
    · have htail := ZcR (le_of_not_ge hx2) hxEven
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (Zb 1))
        (Real.continuous_sinc.intervalIntegrable (Zb 1) x)
      have hfirst := Za7
      unfold Xq.Kernel.Zah at hfirst ⊢
      have heq : Zb 1 = 2 * Real.pi := by simp [Zb]
      rw [heq] at hadd htail
      linarith
  · by_cases hxpi : x ≤ Real.pi
    · have htail : 0 ≤ ∫ t in x..Real.pi, Real.sinc t := by
        apply intervalIntegral.integral_nonneg hxpi
        intro t ht
        exact Zee (hx0.trans ht.1) ht.2
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (Real.continuous_sinc.intervalIntegrable x Real.pi)
      have hpi := Xq.Kernel.Zgr
      unfold Xq.Kernel.Zah at hpi ⊢
      linarith
    · have htail := Zf7 (le_of_not_ge hxpi) hxEven
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) Real.pi)
        (Real.continuous_sinc.intervalIntegrable Real.pi x)
      have hpi := Xq.Kernel.Zgr
      unfold Xq.Kernel.Zah at hpi ⊢
      linarith
theorem ZbY {x : ℝ}
    (hx2 : 2 * Real.pi ≤ x) (hx14 : x ≤ 14 * Real.pi) :
    (4 : ℝ) / 3 ≤ Xq.Kernel.Zah x := by
  have hlo : Zb 1 ≤ x := by simpa [Zb] using hx2
  have hhi : x ≤ Zb 7 := by
    dsimp [Zb]
    convert hx14 using 1
    ring
  have htail := ZcR hlo hhi
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (Zb 1))
    (Real.continuous_sinc.intervalIntegrable (Zb 1) x)
  have hfirst := Za7
  unfold Xq.Kernel.Zah at hfirst ⊢
  have heq : Zb 1 = 2 * Real.pi := by simp [Zb]
  rw [heq] at hadd htail
  linarith
theorem Zhj (x : ℝ) :
    Xq.Kernel.Zah (-x) = -Xq.Kernel.Zah x := by
  unfold Xq.Kernel.Zah
  have h := intervalIntegral.integral_comp_neg (f := Real.sinc)
    (a := (0 : ℝ)) (b := x)
  simp only [Real.sinc_neg] at h
  calc
    (∫ y in (0 : ℝ)..-x, Real.sinc y) =
        -(∫ y in -x..(0 : ℝ), Real.sinc y) :=
      intervalIntegral.integral_symm (-x) 0
    _ = -(∫ y in (0 : ℝ)..x, Real.sinc y) := by
      simpa using (congrArg Neg.neg h).symm
theorem ZbZ (n : ℕ) (hn : 0 < n)
    (u v theta : ℝ) :
    (∫ x in u..v,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) =
      Xq.Kernel.Zah (2 * (n : ℝ) * (v - theta)) -
        Xq.Kernel.Zah (2 * (n : ℝ) * (u - theta)) := by
  let c : ℝ := 2 * (n : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hcomp := intervalIntegral.integral_comp_mul_add Real.sinc hc (-c * theta)
    (a := u) (b := v)
  have hscale : (∫ x in u..v, c * Real.sinc (c * x + -c * theta)) =
      ∫ y in c * u + -c * theta..c * v + -c * theta, Real.sinc y := by
    rw [intervalIntegral.integral_const_mul]
    rw [hcomp]
    simp [hc]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (c * u + -c * theta))
    (Real.continuous_sinc.intervalIntegrable (c * u + -c * theta)
      (c * v + -c * theta))
  unfold Xq.Kernel.Zah
  rw [show (∫ x in u..v,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) =
      ∫ x in u..v, c * Real.sinc (c * x + -c * theta) by
        congr 1
        funext x
        dsimp [c]
        ring_nf]
  rw [hscale]
  have hu : c * u + -c * theta = c * (u - theta) := by ring
  have hv : c * v + -c * theta = c * (v - theta) := by ring
  rw [hu, hv] at hadd ⊢
  linarith
private lemma Zc4
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v = 2 * Real.pi) :
    (4 : ℝ) / 3 ≤ Xq.Kernel.Zah u +
      Xq.Kernel.Zah v := by
  have hbound (z w : ℝ) (hzpi : Real.pi ≤ z) (hz2 : z ≤ 2 * Real.pi)
      (hw0 : 0 ≤ w) (hw14 : w ≤ 14 * Real.pi) :
      (4 : ℝ) / 3 ≤ Xq.Kernel.Zah w +
        Xq.Kernel.Zah z := by
    have htail : (∫ t in z..2 * Real.pi, Real.sinc t) ≤ 0 := by
      apply Zbw hz2
      intro t ht
      exact Zdj 0 (by simpa [Zb] using hzpi.trans ht.1)
        (by simpa [Zb] using ht.2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (0 : ℝ) z)
      (Real.continuous_sinc.intervalIntegrable z (2 * Real.pi))
    have hw := ZaN hw0 hw14
    rcases hw with ⟨hw_nonneg, hw_le⟩
    have hfirst := Za7
    unfold Xq.Kernel.Zah at hfirst hw_nonneg hw_le ⊢
    linarith
  by_cases hupi : u ≤ Real.pi
  · have hvpi : Real.pi ≤ v := by linarith
    have hv2 : v ≤ 2 * Real.pi := by linarith
    have hu14 : u ≤ 14 * Real.pi := by nlinarith [Real.pi_pos]
    exact hbound v u hvpi hv2 hu hu14
  · have hvpi : v ≤ Real.pi := by linarith
    have hupi' : Real.pi ≤ u := le_of_not_ge hupi
    have hu2 : u ≤ 2 * Real.pi := by linarith
    have hv14 : v ≤ 14 * Real.pi := by nlinarith [Real.pi_pos]
    simpa [add_comm] using hbound u v hupi' hu2 hv hv14
theorem Zg1 (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n)
    {theta : ℝ}
    (htheta : theta ∈ Icc ((a : ℝ) * Real.pi / n)
      ((b : ℝ) * Real.pi / n)) :
    (∫ x in (a : ℝ) * Real.pi / n..(b : ℝ) * Real.pi / n,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) ∈
      Icc ((4 : ℝ) / 3) 4 := by
  let L : ℝ := (a : ℝ) * Real.pi / n
  let U : ℝ := (b : ℝ) * Real.pi / n
  let c : ℝ := 2 * (n : ℝ)
  let u : ℝ := c * (theta - L)
  let v : ℝ := c * (U - theta)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hu : 0 ≤ u := mul_nonneg hc.le (sub_nonneg.2 htheta.1)
  have hv : 0 ≤ v := mul_nonneg hc.le (sub_nonneg.2 htheta.2)
  have huv : u + v = c * (U - L) := by
    dsimp [u, v]
    ring
  have htotal : u + v = 2 * ((b - a : ℤ) : ℝ) * Real.pi := by
    rw [huv]
    dsimp [c, U, L]
    push_cast
    field_simp
  have hsum12 : u + v ≤ 12 * Real.pi := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    calc
      u + v = c * (U - L) := huv
      _ ≤ c * (6 * Real.pi / n) := by simpa [U, L] using hm
      _ = 12 * Real.pi := by
        dsimp [c]
        field_simp
        norm_num
  have hu14 : u ≤ 14 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hv14 : v ≤ 14 * Real.pi := by
    nlinarith [Real.pi_pos]
  have huMem := ZaN hu hu14
  have hvMem := ZaN hv hv14
  rcases huMem with ⟨huSi0, huSi2⟩
  rcases hvMem with ⟨hvSi0, hvSi2⟩
  have hlower : (4 : ℝ) / 3 ≤ Xq.Kernel.Zah u +
      Xq.Kernel.Zah v := by
    by_cases hgap : b - a = 1
    · apply Zc4 hu hv
      rw [htotal, hgap]
      norm_num
    · have hgap2 : (2 : ℤ) ≤ b - a := by omega
      have htotal4 : 4 * Real.pi ≤ u + v := by
        rw [htotal]
        have hcast : (2 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hgap2
        nlinarith [Real.pi_pos]
      by_cases hu2 : 2 * Real.pi ≤ u
      · have hmain := ZbY hu2 hu14
        linarith
      · have hv2 : 2 * Real.pi ≤ v := by linarith
        have hmain := ZbY hv2 hv14
        linarith
  have hupper : Xq.Kernel.Zah u +
      Xq.Kernel.Zah v ≤ 4 := by linarith
  have hid := ZbZ n hn L U theta
  have hL : 2 * (n : ℝ) * (L - theta) = -u := by
    dsimp [c, u]
    ring
  have hU : 2 * (n : ℝ) * (U - theta) = v := by rfl
  dsimp [L, U] at hid ⊢
  rw [hid, hL, hU, Zhj]
  constructor <;> linarith
theorem Zfn (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n)
    {theta : ℝ}
    (hnear :
      (theta ≤ (a : ℝ) * Real.pi / n ∧
        (a : ℝ) * Real.pi / n - theta ≤ Real.pi / n) ∨
      ((b : ℝ) * Real.pi / n ≤ theta ∧
        theta - (b : ℝ) * Real.pi / n ≤ Real.pi / n)) :
    |∫ x in (a : ℝ) * Real.pi / n..(b : ℝ) * Real.pi / n,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))| ≤ 2 := by
  let L : ℝ := (a : ℝ) * Real.pi / n
  let U : ℝ := (b : ℝ) * Real.pi / n
  let c : ℝ := 2 * (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hwidth : c * (U - L) ≤ 12 * Real.pi := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    dsimp [c, U, L] at hm ⊢
    field_simp at hm ⊢
    nlinarith
  have hUL0 : 0 ≤ U - L := by
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    dsimp [U, L]
    have hmul : (a : ℝ) * Real.pi ≤ (b : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right habR.le Real.pi_pos.le
    exact sub_nonneg.2 (div_le_div_of_nonneg_right hmul hnR.le)
  have hid := ZbZ n hn L U theta
  rcases hnear with hleft | hright
  · let z : ℝ := c * (L - theta)
    let w : ℝ := c * (U - theta)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hleft.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * Real.pi := by
      have hm := mul_le_mul_of_nonneg_left hleft.2 hc.le
      dsimp [c, z, L] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * Real.pi := by rw [hzw]; linarith
    have hzMem := ZaN hz0 (hz2.trans (by nlinarith [Real.pi_pos]))
    have hwMem := ZaN hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - theta) = z := by rfl
    have hU : 2 * (n : ℝ) * (U - theta) = w := by rfl
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU]
    rw [abs_le]
    constructor <;> linarith
  · let z : ℝ := c * (theta - U)
    let w : ℝ := c * (theta - L)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hright.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * Real.pi := by
      have hm := mul_le_mul_of_nonneg_left hright.2 hc.le
      dsimp [c, z, U] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * Real.pi := by rw [hzw]; linarith
    have hzMem := ZaN hz0 (hz2.trans (by nlinarith [Real.pi_pos]))
    have hwMem := ZaN hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - theta) = -w := by dsimp [c, w]; ring
    have hU : 2 * (n : ℝ) * (U - theta) = -z := by dsimp [c, z]; ring
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU, Zhj z, Zhj w]
    rw [abs_le]
    constructor <;> linarith
end
end Xq.SineIntegralGrid
end
section
namespace Xq.KernelDistantClaim
open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral
noncomputable section
open Xq.OddSine
def ZG (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))
def ZT {n : ℕ} (F : Za n)
    (theta : ℝ) : Finset (↑F.base : Type) :=
  @Finset.filter (↑F.base : Type)
    (fun I ↦ ¬Xq.KernelNearGeometry.Near n theta I.1)
    (Classical.decPred _) Finset.univ
theorem Zhk {n : ℕ}
    (F : Za n) (theta : ℝ) :
    ZT F theta =
      Finset.univ \
        Xq.KernelNearGeometry.Zu F theta := by
  classical
  ext I
  simp [ZT,
    Xq.KernelNearGeometry.Zu]
private def ZaS {n : ℕ} (F : Za n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval
    (fun I ↦ ¬Xq.KernelNearGeometry.Near n theta I)
    (Classical.decPred _) F.base
private lemma Zc5 {n : ℕ}
    (F : Za n) (theta : ℝ) (f : RealInterval → ℝ) :
    ∑ I ∈ ZT F theta, f I.1 =
      ∑ I ∈ ZaS F theta, f I := by
  classical
  apply Finset.sum_bij (fun I _ ↦ I.1)
  · intro I hI
    simp only [ZT, Finset.mem_filter, Finset.mem_univ,
      true_and] at hI
    simp [ZaS, I.property, hI]
  · intro I hI J hJ hIJ
    exact Subtype.ext hIJ
  · intro I hI
    simp only [ZaS, Finset.mem_filter] at hI
    refine ⟨⟨I, hI.1⟩, ?_, rfl⟩
    simp [ZT, hI.2]
  · intro I hI
    rfl
private lemma ZdT {n : ℕ} (hn : 0 < n)
    {I : RealInterval}
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n)
    (theta : ℝ) :
    Real.cos ((2 * (n : ℝ)) * (I.2 - theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 - theta)) := by
  obtain ⟨a, b, ha, hb⟩ := hgrid
  rw [ha, hb]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    Real.cos ((2 * (n : ℝ)) * ((b : ℝ) * Real.pi / n - theta)) =
        Real.cos ((b : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) := by
          congr 1
          field_simp [hn0]
    _ = Real.cos ((2 * (n : ℝ)) * theta) :=
      Real.cos_int_mul_two_pi_sub _ b
    _ = Real.cos ((a : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) :=
      (Real.cos_int_mul_two_pi_sub _ a).symm
    _ = Real.cos ((2 * (n : ℝ)) * ((a : ℝ) * Real.pi / n - theta)) := by
          congr 1
          field_simp [hn0]
theorem ZcJ
    {n : ℕ} (hn : 0 < n)
    {I : RealInterval} {theta : ℝ}
    (hzero : ∀ u ∈ uIcc (I.1 - theta) (I.2 - theta), u ≠ 0) :
    ZG n I theta =
      ∫ u in (I.1 - theta)..(I.2 - theta),
        u⁻¹ * Real.sin ((2 * (n : ℝ)) * u) := by
  rw [ZG]
  rw [intervalIntegral.integral_comp_sub_right
    (fun u : ℝ ↦ 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u)) theta]
  apply intervalIntegral.integral_congr
  intro u hu
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by positivity
  have hu0 := hzero u hu
  change 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u) =
    u⁻¹ * Real.sin (2 * (n : ℝ) * u)
  rw [Real.sinc_of_ne_zero (mul_ne_zero hn0 hu0)]
  field_simp [hn0, hu0]
theorem ZbO {n : ℕ} (hn : 0 < n)
    {I : RealInterval} {theta : ℝ} (hord : I.1 ≤ I.2)
    (hgrid : ∃ a b : ℤ,
      I.1 = (a : ℝ) * Real.pi / n ∧ I.2 = (b : ℝ) * Real.pi / n)
    (hside : I.2 ≤ theta - Real.pi / n ∨
      theta + Real.pi / n ≤ I.1) :
    |ZG n I theta| ≤
      ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hleftOrRight : I.2 < theta ∨ theta < I.1 := by
    rcases hside with hleft | hright
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hzero : ∀ u ∈ uIcc (I.1 - theta) (I.2 - theta), u ≠ 0 := by
    intro u hu
    rw [uIcc_of_le (sub_le_sub_right hord theta)] at hu
    rcases hleftOrRight with hleft | hright
    · have : u < 0 := lt_of_le_of_lt hu.2 (sub_neg.mpr hleft)
      exact this.ne
    · have : 0 < u := lt_of_lt_of_le (sub_pos.mpr hright) hu.1
      exact this.ne'
  rw [ZcJ hn hzero]
  have hlocal :=
    Xq.KernelClaims.Zb5
      (h := fun u : ℝ ↦ u⁻¹) (h' := fun u : ℝ ↦ -(u ^ 2)⁻¹)
      hn (sub_le_sub_right hord theta)
      (fun u hu ↦ hasDerivAt_inv (hzero u (by
        simpa [uIcc_of_le (sub_le_sub_right hord theta)] using hu)))
      (by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (by fun_prop)
        intro u hu
        exact pow_ne_zero 2 (hzero u (by
          simpa [uIcc_of_le (sub_le_sub_right hord theta)] using hu)))
      (fun u hu ↦ neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg u)))
      (ZdT hn hgrid theta)
  have hanti : (I.2 - theta)⁻¹ ≤ (I.1 - theta)⁻¹ := by
    rcases hleftOrRight with hleft | hright
    · exact inv_antitoneOn_Iio
        (show I.1 - theta ∈ Iio 0 by exact sub_neg.mpr (hord.trans_lt hleft))
        (show I.2 - theta ∈ Iio 0 by exact sub_neg.mpr hleft)
        (sub_le_sub_right hord theta)
    · exact inv_antitoneOn_Ioi
        (show I.1 - theta ∈ Ioi 0 by exact sub_pos.mpr hright)
        (show I.2 - theta ∈ Ioi 0 by exact sub_pos.mpr (hright.trans_le hord))
        (sub_le_sub_right hord theta)
  rw [abs_of_nonpos (sub_nonpos.mpr hanti)] at hlocal
  convert hlocal using 1
  ring
private lemma Zan
    (s : Finset RealInterval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex RealInterval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↑t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↑t) : Lex RealInterval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↑t) : Lex RealInterval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then
      f (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealInterval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↑t) : Lex RealInterval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↑t) : Lex RealInterval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Xq.KernelClaims.Za0
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simp [t]
      _ = ∑ J : ↑t, (f (ofLex (J.1 : Lex RealInterval)).2 -
          f (ofLex (J.1 : Lex RealInterval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex RealInterval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↑t) : Lex RealInterval)).2 -
          f (ofLex ((e i : ↑t) : Lex RealInterval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↑t ↦
              f (ofLex (J.1 : Lex RealInterval)).2 -
                f (ofLex (J.1 : Lex RealInterval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr
      (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 =
        f (ofLex ((e ⟨0, hmpos⟩ : ↑t) : Lex RealInterval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)
private lemma ZaL
    (s : Finset RealInterval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := Zan s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h
private lemma ZjM {n : ℕ} (hn : 0 < n)
    (F : Za n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  rcases le_total I.1 J.1 with hle | hle
  · left
    by_contra hnot
    have hJlt : J.1 < I.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne J.1
      ⟨hle, hJlt.le⟩ J.1 ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this
  · right
    by_contra hnot
    have hIlt : I.1 < J.2 := lt_of_not_ge hnot
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 ⟨hle, hIlt.le⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hpiN) this
private def Zae {n : ℕ} (F : Za n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval (fun I ↦ I.2 ≤ theta)
    (Classical.decPred _) (ZaS F theta)
private def ZU {n : ℕ} (F : Za n)
    (theta : ℝ) : Finset RealInterval :=
  @Finset.filter RealInterval (fun I ↦ ¬I.2 ≤ theta)
    (Classical.decPred _) (ZaS F theta)
private lemma Zjc {n : ℕ} (_hn : 0 < n)
    (F : Za n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ Zae F theta) :
    I.2 ≤ theta - Real.pi / n := by
  simp only [Zae, ZaS, Finset.mem_filter] at hI
  have hgap : Real.pi / (n : ℝ) ≤
      Xq.KernelNearGeometry.Zdd theta I := by
    exact le_of_not_gt hI.1.2
  rw [Xq.KernelNearGeometry.Zck
    (F.ordered I hI.1.1) hI.2] at hgap
  linarith
private lemma Zis {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ ZU F theta) :
    theta + Real.pi / n ≤ I.1 := by
  simp only [ZU, ZaS, Finset.mem_filter] at hI
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hright : theta ≤ I.1 := by
    by_contra hnot
    have hleft : I.1 < theta := lt_of_not_ge hnot
    have hright : theta < I.2 := lt_of_not_ge hI.2
    apply hI.1.2
    rw [Xq.KernelNearGeometry.Near,
      Xq.KernelNearGeometry.ZeX]
    · exact hpiN
    · exact ⟨hleft.le, hright.le⟩
  have hgap : Real.pi / (n : ℝ) ≤
      Xq.KernelNearGeometry.Zdd theta I := by
    exact le_of_not_gt hI.1.2
  rw [Xq.KernelNearGeometry.ZcN
    (F.ordered I hI.1.1) hright] at hgap
  linarith
private lemma Zgt {n : ℕ} (hn : 0 < n)
    (F : Za n) (s : Finset RealInterval)
    (hs : s ⊆ F.base) :
    Set.Pairwise (↑s : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  exact ZjM hn F (hs hI) (hs hJ) hne
private lemma Zhl {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ Zae F theta,
        ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
      (n : ℝ) / Real.pi := by
  classical
  let s := Zae F theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Xq.KernelNearGeometry.Near n theta J) ∧ J.2 ≤ theta := by
        simpa only [s, Zae, ZaS,
          Finset.mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        (0 : ℝ) ≤ J.1 ∧ J.2 ≤ theta - Real.pi / n := by
      intro J hJ
      exact ⟨(F.in_first_quadrant J (hbase J hJ)).1,
        Zjc hn F (by simpa [s] using hJ)⟩
    have hLU : (0 : ℝ) ≤ theta - Real.pi / n :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := ZaL s
      (fun x : ℝ ↦ (x - theta)⁻¹) 0 (theta - Real.pi / n)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (Zgt hn F s hbase)
      (sub_inv_antitoneOn_Icc_left (by linarith))
    have hzeroEndpoint : (0 - theta)⁻¹ ≤ 0 :=
      inv_nonpos.mpr (sub_nonpos.mpr htheta.1)
    have hfarEndpoint :
        (theta - Real.pi / (n : ℝ) - theta)⁻¹ =
          -(n : ℝ) / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
      ring
    rw [hfarEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ Zae F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
          (0 - theta)⁻¹ - (-(n : ℝ) / Real.pi) := htel
      _ ≤ 0 - (-(n : ℝ) / Real.pi) :=
        sub_le_sub_right hzeroEndpoint _
      _ = (n : ℝ) / Real.pi := by ring
  · have hs0 : Zae F theta = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp only [Finset.sum_sub_distrib, Finset.sum_empty, sub_self, ge_iff_le]
    positivity
private lemma Zg2 {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ ZU F theta,
        ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
      (n : ℝ) / Real.pi := by
  classical
  let s := ZU F theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpiN : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  by_cases hs : s.Nonempty
  · obtain ⟨I, hI⟩ := hs
    have hbase : ∀ J ∈ s, J ∈ F.base := by
      intro J hJ
      have hJ' : (J ∈ F.base ∧
          ¬Xq.KernelNearGeometry.Near n theta J) ∧ ¬J.2 ≤ theta := by
        simpa only [s, ZU, ZaS,
          Finset.mem_filter] using hJ
      exact hJ'.1.1
    have hinside : ∀ J ∈ s,
        theta + Real.pi / n ≤ J.1 ∧ J.2 ≤ Real.pi / 2 := by
      intro J hJ
      exact ⟨Zis hn F (by simpa [s] using hJ),
        (F.in_first_quadrant J (hbase J hJ)).2⟩
    have hLU : theta + Real.pi / n ≤ Real.pi / 2 :=
      (hinside I hI).1.trans
        ((F.ordered I (hbase I hI)).trans (hinside I hI).2)
    have htel := ZaL s
      (fun x : ℝ ↦ (x - theta)⁻¹)
      (theta + Real.pi / n) (Real.pi / 2)
      (fun J hJ ↦ F.nondegenerate J (hbase J hJ)) hLU hinside
      (Zgt hn F s hbase)
      (sub_inv_antitoneOn_Icc_right (by linarith))
    have hlastEndpoint : 0 ≤ (Real.pi / 2 - theta)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr htheta.2)
    have hnearEndpoint :
        (theta + Real.pi / (n : ℝ) - theta)⁻¹ =
          (n : ℝ) / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
      ring
    rw [hnearEndpoint] at htel
    dsimp [s] at htel
    calc
      ∑ I ∈ ZU F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) ≤
          (n : ℝ) / Real.pi - (Real.pi / 2 - theta)⁻¹ := htel
      _ ≤ (n : ℝ) / Real.pi - 0 :=
        sub_le_sub_left hlastEndpoint _
      _ = (n : ℝ) / Real.pi := by ring
  · have hs0 : ZU F theta = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [s] using hs
    rw [hs0]
    simp only [Finset.sum_sub_distrib, Finset.sum_empty, sub_self, ge_iff_le]
    positivity
private lemma Zf8 {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ Zae F theta, |ZG n I theta| ≤
      1 / Real.pi := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ Zae F theta, |ZG n I theta| ≤
        ∑ I ∈ Zae F theta,
          (((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n) := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Xq.KernelNearGeometry.Near n theta I) ∧ I.2 ≤ theta := by
        simpa only [Zae, ZaS,
          Finset.mem_filter] using hI
      exact ZbO hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inl (Zjc hn F hI))
    _ = (∑ I ∈ Zae F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹)) / n := by
      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / Real.pi) / n :=
      div_le_div_of_nonneg_right
        (Zhl hn F htheta) hnR.le
    _ = 1 / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
private lemma ZfP {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ ZU F theta, |ZG n I theta| ≤
      1 / Real.pi := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    ∑ I ∈ ZU F theta, |ZG n I theta| ≤
        ∑ I ∈ ZU F theta,
          (((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹) / n) := by
      apply Finset.sum_le_sum
      intro I hI
      have hI' : (I ∈ F.base ∧
          ¬Xq.KernelNearGeometry.Near n theta I) ∧ ¬I.2 ≤ theta := by
        simpa only [ZU, ZaS,
          Finset.mem_filter] using hI
      exact ZbO hn
        (F.ordered I hI'.1.1) (F.grid_endpoints I hI'.1.1)
        (Or.inr (Zis hn F hI))
    _ = (∑ I ∈ ZU F theta,
          ((I.1 - theta)⁻¹ - (I.2 - theta)⁻¹)) / n := by
      rw [Finset.sum_div]
    _ ≤ ((n : ℝ) / Real.pi) / n :=
      div_le_div_of_nonneg_right
        (Zg2 hn F htheta) hnR.le
    _ = 1 / Real.pi := by
      field_simp [hn0, Real.pi_ne_zero]
theorem Zde {n : ℕ}
    (hn : 0 < n) (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ ZT F theta,
        |ZG n I.1 theta| ≤ 2 / Real.pi := by
  classical
  rw [Zc5 F theta
    (fun I ↦ |ZG n I theta|)]
  have hsplit :
      (∑ I ∈ ZaS F theta, |ZG n I theta|) =
        (∑ I ∈ Zae F theta,
          |ZG n I theta|) +
        ∑ I ∈ ZU F theta,
          |ZG n I theta| := by
    rw [Zae, ZU,
      Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  calc
    (∑ I ∈ Zae F theta, |ZG n I theta|) +
        ∑ I ∈ ZU F theta,
          |ZG n I theta| ≤
        1 / Real.pi + 1 / Real.pi :=
      add_le_add (Zf8 hn F htheta)
        (ZfP hn F htheta)
    _ = 2 / Real.pi := by ring
end
end Xq.KernelDistantClaim
end
section
namespace Xq.KernelReplacementMonotone
open Real Set
noncomputable section
def Zj : ℝ → ℝ :=
  dslope (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0
@[simp] theorem ZiK : Zj 0 = 0 := by
  rw [Zj, dslope_same]
  have hsinc : AnalyticAt ℝ Real.sinc 0 := by
    rw [Real.sinc_eq_dslope]
    exact Real.analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
  have hinv : DifferentiableAt ℝ (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0 :=
    (hsinc.inv (by simp)).differentiableAt
  let d := deriv (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0
  have hd : HasDerivAt (fun u : ℝ ↦ (Real.sinc u)⁻¹) d 0 := hinv.hasDerivAt
  have hdneg : HasDerivAt (fun u : ℝ ↦ (Real.sinc (-u))⁻¹) (-d) 0 := by
    have hcomp := HasDerivAt.comp_of_eq (x := (0 : ℝ)) hd
      (hasDerivAt_neg 0) (by simp)
    simpa [d, Function.comp_def] using hcomp
  have hdneg' : HasDerivAt (fun u : ℝ ↦ (Real.sinc u)⁻¹) (-d) 0 := by
    simpa only [Real.sinc_neg] using hdneg
  have := hd.unique hdneg'
  dsimp [d] at this ⊢
  linarith
theorem Za2 {u : ℝ} (hu : u ≠ 0)
    (hsu : Real.sin u ≠ 0) :
    Zj u = 1 / Real.sin u - 1 / u := by
  have hmul : u * Zj u = (Real.sinc u)⁻¹ - 1 := by
    simpa [Zj] using
      (sub_smul_dslope (fun x : ℝ ↦ (Real.sinc x)⁻¹) 0 u)
  apply (mul_left_cancel₀ hu)
  rw [hmul, Real.sinc_of_ne_zero hu]
  field_simp [hu, hsu]
private lemma Zkp : AnalyticAt ℝ Real.sinc 0 := by
  rw [Real.sinc_eq_dslope]
  exact Real.analyticAt_sin.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
theorem Zcx :
    AnalyticAt ℝ Zj 0 := by
  have hinv : AnalyticAt ℝ (fun u : ℝ ↦ (Real.sinc u)⁻¹) 0 :=
    Zkp.inv (by simp)
  exact hinv.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt
theorem ZdU {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hu0 : u ≠ 0) : Real.sin u ≠ 0 := by
  intro hsu
  apply hu0
  exact (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hu.1, Real.pi_pos])
    (by linarith [hu.2, Real.pi_pos])).mp hsu
theorem Zbk {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    AnalyticAt ℝ Zj u := by
  by_cases hu0 : u = 0
  · simpa [hu0] using Zcx
  have hsu := ZdU hu hu0
  have hrhs : AnalyticAt ℝ (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) u := by
    fun_prop
  apply hrhs.congr
  filter_upwards [eventually_ne_nhds hu0,
      (Real.continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
  exact (Za2 hx0 hsx).symm
theorem Zcl {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    DifferentiableAt ℝ Zj u :=
  (Zbk hu).differentiableAt
theorem ZgD {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt Zj (deriv Zj u) u :=
  (Zcl hu).hasDerivAt
theorem Zfo {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ Zj u * u := by
  rcases lt_trichotomy u 0 with hu0 | rfl | hu0
  · have hsu : Real.sin u < 0 := by
      rw [← neg_pos, ← Real.sin_neg]
      exact Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hu0)
        (by linarith [hu.1, Real.pi_pos])
    rw [Za2 hu0.ne (ne_of_lt hsu)]
    have hsle : u ≤ Real.sin u := by
      have := Real.sin_le (show 0 ≤ -u by linarith)
      rw [Real.sin_neg] at this
      linarith
    rw [show (1 / Real.sin u - 1 / u) * u =
        (u - Real.sin u) / Real.sin u by
      field_simp [hu0.ne, ne_of_lt hsu]
      ]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr hsle) hsu.le
  · simp
  · have hsu : 0 < Real.sin u :=
      Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu.2, Real.pi_pos])
    rw [Za2 hu0.ne' (ne_of_gt hsu)]
    have hsle := Real.sin_le hu0.le
    rw [show (1 / Real.sin u - 1 / u) * u =
        (u - Real.sin u) / Real.sin u by
      field_simp [hu0.ne', ne_of_gt hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsle) hsu.le
theorem Zc6 {u : ℝ}
    (hu : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ deriv Zj u := by
  by_cases hu0 : u = 0
  · subst u
    have hd := Zcx.differentiableAt.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    apply ge_of_tendsto hd
    have hIcc : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈ nhds (0 : ℝ) :=
      Icc_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hIcc' : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ :=
      mem_nhdsWithin_of_mem_nhds hIcc
    filter_upwards [self_mem_nhdsWithin, hIcc'] with x hx hxmem
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [slope, ZiK, sub_zero, vsub_eq_sub,
      smul_eq_mul]
    rw [show x⁻¹ * Zj x =
        (Zj x * x) / x ^ 2 by
      field_simp [hx0]
      ]
    exact div_nonneg (Zfo hxmem) (sq_nonneg x)
  · have hsu := ZdU hu hu0
    have heq : Zj =ᶠ[nhds u]
        (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) := by
      filter_upwards [eventually_ne_nhds hu0,
        (Real.continuous_sin.tendsto u) (isOpen_ne.mem_nhds hsu)] with x hx0 hsx
      exact Za2 hx0 hsx
    have hbase := ((Real.hasDerivAt_sin u).inv hsu).sub
      ((hasDerivAt_id u).inv hu0)
    have hbase' : HasDerivAt (fun x : ℝ ↦ 1 / Real.sin x - 1 / x)
        (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
      have hfun : (fun x : ℝ ↦ 1 / Real.sin x - 1 / x) =
          Real.sin⁻¹ - id⁻¹ := by
        funext x
        simp only [one_div, Pi.sub_apply, Pi.inv_apply, id_eq]
      have hcoef : 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
          -Real.cos u / Real.sin u ^ 2 - -1 / id u ^ 2 := by
        simp only [id_eq]
        ring
      rw [hfun, hcoef]
      exact hbase
    have hderiv : HasDerivAt Zj
        (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
      exact heq.hasDerivAt_iff.mpr hbase'
    rw [hderiv.deriv]
    have habs : |u| ≤ Real.pi / 2 := (abs_le).2 hu
    have hcos0 : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc hu
    have hsin_sq : u ^ 2 * Real.cos u ≤ Real.sin u ^ 2 := by
      have ht0 : 0 ≤ |u| := abs_nonneg u
      have ht2 : |u| < 2 := by
        exact lt_of_le_of_lt habs (by linarith [Real.pi_lt_four])
      have htsq : |u| ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ ht0 (by norm_num)).2 ht2
      have hsmall : |u| ^ 2 ≤ 12 := by norm_num at htsq ⊢; linarith
      have hslo := Real.sin_ge_sub_cube (abs_nonneg u)
      have hcosup := Xq.Kernel.Ziq (abs_nonneg u)
      rw [Real.cos_abs] at hcosup
      have hbase : 0 ≤ |u| - |u| ^ 3 / 6 := by
        rw [show |u| - |u| ^ 3 / 6 = |u| * (1 - |u| ^ 2 / 6) by ring]
        exact mul_nonneg ht0 (by nlinarith [htsq])
      have habspi : |u| ≤ Real.pi := by linarith [habs, Real.pi_pos]
      have hsine0 : 0 ≤ Real.sin |u| :=
        Real.sin_nonneg_of_nonneg_of_le_pi ht0 habspi
      have hsloSq : (|u| - |u| ^ 3 / 6) ^ 2 ≤ Real.sin |u| ^ 2 :=
        (sq_le_sq₀ hbase hsine0).2 hslo
      have habssin := Real.abs_sin_eq_sin_abs_of_abs_le_pi habspi
      have hsinSqEq : Real.sin |u| ^ 2 = Real.sin u ^ 2 := by
        rw [← habssin, sq_abs]
      have hcosmult : |u| ^ 2 * Real.cos u ≤
          |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) :=
        mul_le_mul_of_nonneg_left hcosup (sq_nonneg |u|)
      have hprod : 0 ≤ |u| ^ 4 * (12 - |u| ^ 2) :=
        mul_nonneg (pow_nonneg ht0 4) (sub_nonneg.mpr hsmall)
      have hpoly : |u| ^ 2 * (1 - |u| ^ 2 / 2 + |u| ^ 4 / 24) ≤
          (|u| - |u| ^ 3 / 6) ^ 2 := by
        nlinarith
      rw [← sq_abs u, ← hsinSqEq]
      exact hcosmult.trans (hpoly.trans hsloSq)
    have hden : 0 < u ^ 2 * Real.sin u ^ 2 :=
      mul_pos (sq_pos_of_ne_zero hu0) (sq_pos_of_ne_zero hsu)
    rw [show 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
        (Real.sin u ^ 2 - u ^ 2 * Real.cos u) /
          (u ^ 2 * Real.sin u ^ 2) by
      field_simp [hu0, hsu]
      ]
    exact div_nonneg (sub_nonneg.mpr hsin_sq) hden.le
theorem Zfp :
    (∀ u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt Zj (deriv Zj u) u) ∧
    ContinuousOn (deriv Zj)
      (Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (∀ u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2),
      0 ≤ deriv Zj u) := by
  refine ⟨fun u hu ↦ ZgD hu, ?_,
    fun u hu ↦ Zc6 hu⟩
  intro u hu
  exact (Zbk hu).deriv.continuousAt.continuousWithinAt
theorem Zbm :
    MonotoneOn Zj
      (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun u hu ↦
      (Zbk hu).continuousAt.continuousWithinAt
  · exact fun u hu ↦
      (Zcl (interior_subset hu)).differentiableWithinAt
  · intro u hu
    exact Zc6 (interior_subset hu)
@[simp] theorem ZgE :
    Zj (Real.pi / 2) = 1 - 2 / Real.pi := by
  rw [Za2 (by positivity) (by simp), Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
@[simp] theorem ZfD :
    Zj (-(Real.pi / 2)) = -(1 - 2 / Real.pi) := by
  rw [Za2
      (neg_ne_zero.mpr (div_ne_zero Real.pi_ne_zero (by norm_num))) (by simp), Real.sin_neg,
    Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
  ring
theorem Zex :
    Zj (Real.pi / 2) -
      Zj (-(Real.pi / 2)) = 2 - 4 / Real.pi := by
  rw [ZgE, ZfD]
  ring
end
end Xq.KernelReplacementMonotone
end
section
namespace Xq.KernelReflectedClaim
open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral
noncomputable section
open Xq.OddSine
def Zaa (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) / Real.sin (x + theta)
private def eta (n : ℕ) : ℝ := 100 * Real.pi / n
private def Zat (theta x : ℝ) : ℝ := (Real.sin (x + theta))⁻¹
private def ZM (theta : ℝ) : ℝ := Real.pi / 2 - theta
private noncomputable def Zbx {n : ℕ}
    (F : Za n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ I.2 ≤ ZM theta
private noncomputable def Zbj {n : ℕ}
    (F : Za n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ ZM theta ≤ I.1
private noncomputable def Zba {n : ℕ}
    (F : Za n) (theta : ℝ) : Finset RealInterval :=
  F.base.filter fun I ↦ I.1 < ZM theta ∧ ZM theta < I.2
private lemma Zet {n : ℕ} (hn : 0 < n) : 0 < eta n := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hn)
private lemma ZeQ {n : ℕ} (hn : 4096 ≤ n) :
    eta n ≤ Real.pi / 2 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  dsimp [eta]
  apply (div_le_iff₀ hnpos).2
  nlinarith [Real.pi_pos]
private lemma Zd4 {n : ℕ} (F : Za n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) :
    eta n ≤ x + theta ∧ x + theta ≤ Real.pi - eta n := by
  have haway := F.away_from_axes I hI
  constructor
  · exact (show eta n ≤ I.1 from haway.1) |>.trans hx.1 |>.trans
      (le_add_of_nonneg_right htheta.1)
  · exact (add_le_add hx.2 htheta.2).trans
      (show I.2 + Real.pi / 2 ≤ Real.pi - eta n by
        dsimp [eta]
        linarith [haway.2])
private lemma Zh3 {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {x : ℝ}
    (hx : x ∈ Icc I.1 I.2) : 0 < Real.sin (x + theta) := by
  have hband := Zd4 F htheta hI hx
  have heta := Zet hn
  exact Real.sin_pos_of_pos_of_lt_pi (heta.trans_le hband.1)
    (by linarith [hband.2, heta])
private lemma Zbn {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 + theta) (I.2 + theta)) :
    0 < Real.sin u := by
  have hx : u - theta ∈ Icc I.1 I.2 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simpa only [sub_add_cancel] using
    Zh3 hn F htheta hI hx
private lemma ZeR {n : ℕ} (hn : 0 < n)
    (F : Za n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < Real.pi / (n : ℝ) := by
    exact div_pos Real.pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 := ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 := ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
private abbrev Interval := ℝ × ℝ
private lemma Zan
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Interval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Interval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Interval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Xq.KernelClaims.Za0
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) =
      ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simp [t]
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Interval)).2 -
          f (ofLex (J.1 : Lex Interval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Interval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Interval)).2 -
          f (ofLex ((e i : ↥t) : Lex Interval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Interval)).2 -
                f (ofLex (J.1 : Lex Interval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Interval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)
private lemma ZaL
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := Zan s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h
private lemma Zj5 {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) :
    Real.cos ((2 * (n : ℝ)) * (I.2 + theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 + theta)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  have hphase (k : ℤ) :
      (2 * (n : ℝ)) * ((k : ℝ) * Real.pi / n + theta) =
        (2 * (n : ℝ)) * theta + (k : ℝ) * (2 * Real.pi) := by
    field_simp [hnR]
    ring
  rw [hphase a, hphase b, Real.cos_add_int_mul_two_pi,
    Real.cos_add_int_mul_two_pi]
private lemma Zh4 {n : ℕ} (I : RealInterval) (theta : ℝ) :
    Zaa n I theta =
      ∫ u in I.1 + theta..I.2 + theta,
        (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u) := by
  have hshift := intervalIntegral.integral_comp_add_right
    (fun u : ℝ ↦ (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u))
    theta (a := I.1) (b := I.2)
  rw [← hshift]
  unfold Zaa
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [div_eq_mul_inv]
  ring
private lemma Zlj {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ Zbx F theta) :
    |Zaa n I theta| ≤
      (Zat theta I.1 - Zat theta I.2) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hside : I.2 ≤ ZM theta := (Finset.mem_filter.mp hI).2
  have hab : I.1 + theta ≤ I.2 + theta := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      HasDerivAt Real.sin⁻¹ (-Real.cos u / Real.sin u ^ 2) u := by
    intro u hu
    exact (Real.hasDerivAt_sin u).inv
      (ne_of_gt (Zbn hn0 F htheta hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
      (Icc (I.1 + theta) (I.2 + theta)) := by
    intro u hu
    have hsin : Real.sin u ≠ 0 := ne_of_gt
      (Zbn hn0 F htheta hbase hu)
    exact ((Real.continuous_cos.continuousAt.neg).div
      (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonpos : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      -Real.cos u / Real.sin u ^ 2 ≤ 0 := by
    intro u hu
    have huHalf : u ≤ Real.pi / 2 := by
      dsimp [ZM] at hside
      linarith [hu.2]
    have huNonneg : -(Real.pi / 2) ≤ u := by
      have hx : u - theta ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := Zd4 F htheta hbase hx
      linarith [hband.1, Zet hn0, Real.pi_pos]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.cos_nonneg_of_mem_Icc ⟨huNonneg, huHalf⟩))
      (sq_nonneg _)
  have hosc := Xq.KernelClaims.Zb5
    (h := Real.sin⁻¹) (h' := fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
    hn0 hab hderiv hcont hnonpos (Zj5 hn0 F hbase)
  rw [Zh4]
  have hamp : Zat theta I.2 ≤ Zat theta I.1 := by
    have hsinA : 0 < Real.sin (I.1 + theta) :=
      Zh3 hn0 F htheta hbase ⟨le_rfl, F.ordered I hbase⟩
    have hbandA := Zd4 F htheta hbase
      ⟨le_rfl, F.ordered I hbase⟩
    have hsinmono : Real.sin (I.1 + theta) ≤ Real.sin (I.2 + theta) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hbandA.1, Zet hn0, Real.pi_pos])
        (by dsimp [ZM] at hside; linarith)
        (by linarith [F.ordered I hbase])
    simpa only [Zat, one_div] using
      one_div_le_one_div_of_le hsinA hsinmono
  change |∫ u in I.1 + theta..I.2 + theta,
      (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u)| ≤
    |(Real.sin (I.2 + theta))⁻¹ - (Real.sin (I.1 + theta))⁻¹| / n at hosc
  have hamp' : (Real.sin (I.2 + theta))⁻¹ ≤
      (Real.sin (I.1 + theta))⁻¹ := by simpa only [Zat] using hamp
  rw [abs_of_nonpos (sub_nonpos.mpr hamp')] at hosc
  simpa only [Zat, neg_sub] using hosc
private lemma Zlb {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ Zbj F theta) :
    |Zaa n I theta| ≤
      (Zat theta I.2 - Zat theta I.1) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hside : ZM theta ≤ I.1 := (Finset.mem_filter.mp hI).2
  have hab : I.1 + theta ≤ I.2 + theta := by
    linarith [F.ordered I hbase]
  have hderiv : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      HasDerivAt Real.sin⁻¹ (-Real.cos u / Real.sin u ^ 2) u := by
    intro u hu
    exact (Real.hasDerivAt_sin u).inv
      (ne_of_gt (Zbn hn0 F htheta hbase hu))
  have hcont : ContinuousOn (fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
      (Icc (I.1 + theta) (I.2 + theta)) := by
    intro u hu
    have hsin : Real.sin u ≠ 0 := ne_of_gt
      (Zbn hn0 F htheta hbase hu)
    exact ((Real.continuous_cos.continuousAt.neg).div
      (Real.continuous_sin.continuousAt.pow 2) (pow_ne_zero 2 hsin)).continuousWithinAt
  have hnonneg : ∀ u ∈ Icc (I.1 + theta) (I.2 + theta),
      0 ≤ -Real.cos u / Real.sin u ^ 2 := by
    intro u hu
    have huHalf : Real.pi / 2 ≤ u := by
      dsimp [ZM] at hside
      linarith [hu.1]
    have huTop : u ≤ Real.pi + Real.pi / 2 := by
      have hx : u - theta ∈ Icc I.1 I.2 :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hband := Zd4 F htheta hbase hx
      linarith [hband.2, Zet hn0, Real.pi_pos]
    exact div_nonneg (neg_nonneg.mpr
      (Real.cos_nonpos_of_pi_div_two_le_of_le huHalf huTop)) (sq_nonneg _)
  have hosc := Xq.KernelClaims.Zbf
    (h := Real.sin⁻¹) (h' := fun u : ℝ ↦ -Real.cos u / Real.sin u ^ 2)
    hn0 hab hderiv hcont hnonneg (Zj5 hn0 F hbase)
  rw [Zh4]
  have hamp : Zat theta I.1 ≤ Zat theta I.2 := by
    have hsinB : 0 < Real.sin (I.2 + theta) :=
      Zh3 hn0 F htheta hbase ⟨F.ordered I hbase, le_rfl⟩
    have hcompOrder : Real.pi - (I.2 + theta) ≤
        Real.pi - (I.1 + theta) := by linarith [F.ordered I hbase]
    have hcompTop : Real.pi - (I.1 + theta) ≤ Real.pi / 2 := by
      dsimp [ZM] at hside
      linarith
    have hcompLow : -(Real.pi / 2) ≤ Real.pi - (I.2 + theta) := by
      have hband := Zd4 F htheta hbase
        ⟨F.ordered I hbase, le_rfl⟩
      linarith [hband.2, Zet hn0, Real.pi_pos]
    have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      hcompLow hcompTop hcompOrder
    rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsinmono
    simpa only [Zat, one_div] using
      one_div_le_one_div_of_le hsinB hsinmono
  change |∫ u in I.1 + theta..I.2 + theta,
      (Real.sin u)⁻¹ * Real.sin ((2 * (n : ℝ)) * u)| ≤
    |(Real.sin (I.2 + theta))⁻¹ - (Real.sin (I.1 + theta))⁻¹| / n at hosc
  have hamp' : (Real.sin (I.1 + theta))⁻¹ ≤
      (Real.sin (I.2 + theta))⁻¹ := by simpa only [Zat] using hamp
  rw [abs_of_nonneg (sub_nonneg.mpr hamp')] at hosc
  simpa only [Zat] using hosc
private lemma Zjv {n : ℕ} (hn : 4096 ≤ n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (_ : eta n ≤ ZM theta) :
    AntitoneOn (Zat theta) (Icc (eta n) (ZM theta)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinX : 0 < Real.sin (x + theta) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hx.1, Zet hn0, htheta.1]
    · dsimp [ZM] at hy
      linarith [hy.2, Real.pi_pos]
  have hsinmono : Real.sin (x + theta) ≤ Real.sin (y + theta) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hx.1, Zet hn0, htheta.1, Real.pi_pos])
      (by dsimp [ZM] at hy; linarith [hy.2])
      (by linarith)
  simpa only [Zat, one_div] using
    one_div_le_one_div_of_le hsinX hsinmono
private lemma Zjd {n : ℕ} (hn : 4096 ≤ n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (_ : ZM theta ≤ Real.pi / 2 - eta n) :
    MonotoneOn (Zat theta)
      (Icc (ZM theta) (Real.pi / 2 - eta n)) := by
  intro x hx y hy hxy
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsinY : 0 < Real.sin (y + theta) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · dsimp [ZM] at hx
      linarith [hx.1, Real.pi_pos]
    · linarith [hy.2, Zet hn0, htheta.2]
  have hcompOrder : Real.pi - (y + theta) ≤ Real.pi - (x + theta) := by
    linarith
  have hcompTop : Real.pi - (x + theta) ≤ Real.pi / 2 := by
    dsimp [ZM] at hx
    linarith [hx.1]
  have hcompLow : -(Real.pi / 2) ≤ Real.pi - (y + theta) := by
    linarith [hy.2, Zet hn0, htheta.2, Real.pi_pos]
  have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    hcompLow hcompTop hcompOrder
  rw [Real.sin_pi_sub, Real.sin_pi_sub] at hsinmono
  simpa only [Zat, one_div] using
    one_div_le_one_div_of_le hsinY hsinmono
private lemma Zl7 {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ Zbx F theta, |Zaa n I theta| ≤
      1 / ((n : ℝ) * Real.sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : eta n ≤ ZM theta
  · have hvar := ZaL
      (Zbx F theta) (Zat theta) (eta n) (ZM theta)
      (fun I hI ↦ F.nondegenerate I (Finset.mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(F.away_from_axes I (Finset.mem_filter.mp hI).1).1,
        (Finset.mem_filter.mp hI).2⟩)
      (fun I hI J hJ hne ↦ ZeR hn0 F
        (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne)
      (Zjv hn htheta hbranch)
    have hturn : Zat theta (ZM theta) = 1 := by
      simp [Zat, ZM]
    have hampEta : Zat theta (eta n) ≤ 1 / Real.sin (eta n) := by
      have hsineta : 0 < Real.sin (eta n) :=
        Real.sin_pos_of_pos_of_lt_pi (Zet hn0)
          ((ZeQ hn).trans_lt (by linarith [Real.pi_pos]))
      have hsinmono : Real.sin (eta n) ≤ Real.sin (eta n + theta) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Zet hn0, Real.pi_pos])
          (by dsimp [ZM] at hbranch; linarith)
          (by linarith [htheta.1])
      simpa only [Zat, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ Zbx F theta, |Zaa n I theta| ≤
          ∑ I ∈ Zbx F theta,
            (Zat theta I.1 - Zat theta I.2) / n :=
        Finset.sum_le_sum fun I hI ↦ Zlj hn F htheta hI
      _ = (∑ I ∈ Zbx F theta,
            (Zat theta I.1 - Zat theta I.2)) / n := by
        rw [Finset.sum_div]
      _ ≤ (1 / Real.sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * Real.sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : Zbx F theta = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (Finset.mem_filter.mp hmem).1
      have hside := (Finset.mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).1
      have hstrict := F.nondegenerate I hI
      dsimp [eta, ZM] at hbranch hside
      linarith
    rw [hempty]
    simp only [Finset.sum_empty, one_div, mul_inv_rev, ge_iff_le]
    have hsineta : 0 < Real.sin (eta n) :=
      Real.sin_pos_of_pos_of_lt_pi (Zet hn0)
        ((ZeQ hn).trans_lt (by linarith [Real.pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))
private lemma ZlX {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ Zbj F theta, |Zaa n I theta| ≤
      1 / ((n : ℝ) * Real.sin (eta n)) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  by_cases hbranch : ZM theta ≤ Real.pi / 2 - eta n
  · have hvar := Zan
      (Zbj F theta) (Zat theta) (ZM theta)
        (Real.pi / 2 - eta n)
      (fun I hI ↦ F.nondegenerate I (Finset.mem_filter.mp hI).1)
      hbranch
      (fun I hI ↦ ⟨(Finset.mem_filter.mp hI).2,
        (F.away_from_axes I (Finset.mem_filter.mp hI).1).2⟩)
      (fun I hI J hJ hne ↦ ZeR hn0 F
        (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne)
      (Zjd hn htheta hbranch)
    have hturn : Zat theta (ZM theta) = 1 := by
      simp [Zat, ZM]
    have hampU : Zat theta (Real.pi / 2 - eta n) ≤
        1 / Real.sin (eta n) := by
      have hsineta : 0 < Real.sin (eta n) :=
        Real.sin_pos_of_pos_of_lt_pi (Zet hn0)
          ((ZeQ hn).trans_lt (by linarith [Real.pi_pos]))
      have hcompOrder : eta n ≤
          Real.pi - ((Real.pi / 2 - eta n) + theta) := by
        linarith [htheta.2]
      have hcompTop : Real.pi - ((Real.pi / 2 - eta n) + theta) ≤
          Real.pi / 2 := by
        dsimp [ZM] at hbranch
        linarith
      have hsinmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := eta n)
        (y := Real.pi - ((Real.pi / 2 - eta n) + theta))
        (by linarith [Zet hn0, Real.pi_pos]) hcompTop hcompOrder
      rw [Real.sin_pi_sub] at hsinmono
      simpa only [Zat, one_div] using
        one_div_le_one_div_of_le hsineta hsinmono
    calc
      ∑ I ∈ Zbj F theta, |Zaa n I theta| ≤
          ∑ I ∈ Zbj F theta,
            (Zat theta I.2 - Zat theta I.1) / n :=
        Finset.sum_le_sum fun I hI ↦ Zlb hn F htheta hI
      _ = (∑ I ∈ Zbj F theta,
            (Zat theta I.2 - Zat theta I.1)) / n := by
        rw [Finset.sum_div]
      _ ≤ (1 / Real.sin (eta n)) / n := by
        apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn0)).2
        rw [hturn] at hvar
        linarith
      _ = 1 / ((n : ℝ) * Real.sin (eta n)) := by
        field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn0]
  · have hempty : Zbj F theta = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hmem
      have hI := (Finset.mem_filter.mp hmem).1
      have hside := (Finset.mem_filter.mp hmem).2
      have haway := (F.away_from_axes I hI).2
      have hstrict := F.nondegenerate I hI
      dsimp [eta, ZM] at hbranch hside
      linarith
    rw [hempty]
    simp only [Finset.sum_empty, one_div, mul_inv_rev, ge_iff_le]
    have hsineta : 0 < Real.sin (eta n) :=
      Real.sin_pos_of_pos_of_lt_pi (Zet hn0)
        ((ZeQ hn).trans_lt (by linarith [Real.pi_pos]))
    exact mul_nonneg (inv_nonneg.mpr hsineta.le)
      (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))
private lemma Zje {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (_ : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ Zba F theta) :
    |Zaa n I theta| ≤ 12 * Real.pi / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hbase : I ∈ F.base := (Finset.mem_filter.mp hI).1
  have hcross := (Finset.mem_filter.mp hI).2
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := I.1) (b := I.2) (C := (2 : ℝ))
    (f := fun x : ℝ ↦
      Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) / Real.sin (x + theta))
    (fun x hx ↦ by
      rw [Set.uIoc_of_le (F.ordered I hbase)] at hx
      have hxI : x ∈ Icc I.1 I.2 := ⟨hx.1.le, hx.2⟩
      have hdist : |(x + theta) - Real.pi / 2| ≤ 6 * Real.pi / n := by
        have hwidth := F.short I hbase
        dsimp [ZM] at hcross
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2]
      have hsmall : |(x + theta) - Real.pi / 2| ≤ 1 := by
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        have hfrac : 6 * Real.pi / (n : ℝ) < 1 := by
          apply (div_lt_iff₀ hnRpos).2
          nlinarith
        exact hdist.trans hfrac.le
      have hcos : (1 : ℝ) / 2 ≤ Real.cos ((x + theta) - Real.pi / 2) := by
        have hlow := Real.one_sub_sq_div_two_le_cos
          (x := (x + theta) - Real.pi / 2)
        have hsq : ((x + theta) - Real.pi / 2) ^ 2 ≤ 1 := by
          have habs0 : 0 ≤ |(x + theta) - Real.pi / 2| := abs_nonneg _
          nlinarith [sq_abs ((x + theta) - Real.pi / 2)]
        linarith
      have hsin : (1 : ℝ) / 2 ≤ Real.sin (x + theta) := by
        rw [← Real.cos_sub_pi_div_two]
        exact hcos
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by linarith : 0 ≤ Real.sin (x + theta))]
      apply (div_le_iff₀ (by linarith : 0 < Real.sin (x + theta))).2
      nlinarith [Real.abs_sin_le_one
        (((2 * n : ℕ) : ℝ) * (x + theta))])
  unfold Zaa
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ x in I.1..I.2,
        Real.sin (((2 * n : ℕ) : ℝ) * (x + theta)) /
          Real.sin (x + theta)| ≤ 2 * |I.2 - I.1| := hnorm
    _ = 2 * (I.2 - I.1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (F.ordered I hbase))]
    _ ≤ 2 * (6 * Real.pi / n) := by
      gcongr
      exact F.short I hbase
    _ = 12 * Real.pi / n := by ring
private lemma Zkq {n : ℕ} (hn : 0 < n)
    (F : Za n) (theta : ℝ) :
    (Zba F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  have hbaseI := (Finset.mem_filter.mp hI).1
  have hbaseJ := (Finset.mem_filter.mp hJ).1
  by_contra hne
  have hcrossI := (Finset.mem_filter.mp hI).2
  have hcrossJ := (Finset.mem_filter.mp hJ).2
  have hsep := F.separated hbaseI hbaseJ hne (ZM theta)
    ⟨hcrossI.1.le, hcrossI.2.le⟩ (ZM theta)
    ⟨hcrossJ.1.le, hcrossJ.2.le⟩
  have hpi : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos (by exact_mod_cast hn)
  have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
  exact (not_le_of_gt hpi) this
private lemma Zly {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ Zba F theta, |Zaa n I theta| ≤
      12 * Real.pi / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  calc
    ∑ I ∈ Zba F theta, |Zaa n I theta| ≤
        ∑ _I ∈ Zba F theta, 12 * Real.pi / n :=
      Finset.sum_le_sum fun I hI ↦ Zje hn F htheta hI
    _ = ((Zba F theta).card : ℝ) * (12 * Real.pi / n) := by simp
    _ ≤ 1 * (12 * Real.pi / n) := by
      gcongr
      exact_mod_cast Zkq hn0 F theta
    _ = 12 * Real.pi / n := one_mul _
private lemma ZlG {n : ℕ} (F : Za n) (theta : ℝ) :
    F.base = (Zbx F theta ∪ Zbj F theta) ∪
      Zba F theta := by
  classical
  ext I
  simp only [Zbx, Zbj, Zba, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · intro hI
    by_cases hleft : I.2 ≤ ZM theta
    · exact Or.inl (Or.inl ⟨hI, hleft⟩)
    · by_cases hright : ZM theta ≤ I.1
      · exact Or.inl (Or.inr ⟨hI, hright⟩)
      · exact Or.inr ⟨hI, lt_of_not_ge hright, lt_of_not_ge hleft⟩
  · rintro ((⟨hI, _⟩ | ⟨hI, _⟩) | ⟨hI, _⟩) <;> exact hI
private lemma ZkG {n : ℕ} (F : Za n)
    (theta : ℝ) : Disjoint (Zbx F theta) (Zbj F theta) := by
  classical
  rw [Finset.disjoint_left]
  intro I hleft hright
  have hbase := (Finset.mem_filter.mp hleft).1
  have hstrict := F.nondegenerate I hbase
  linarith [(Finset.mem_filter.mp hleft).2, (Finset.mem_filter.mp hright).2]
private lemma Zjw {n : ℕ} (F : Za n)
    (theta : ℝ) :
    Disjoint (Zbx F theta ∪ Zbj F theta)
      (Zba F theta) := by
  classical
  rw [Finset.disjoint_left]
  intro I hsides hcross
  simp only [Finset.mem_union] at hsides
  have hc := (Finset.mem_filter.mp hcross).2
  rcases hsides with hleft | hright
  · linarith [(Finset.mem_filter.mp hleft).2, hc.2]
  · linarith [(Finset.mem_filter.mp hright).2, hc.1]
theorem ZhK {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I : (↑F.base : Type), |Zaa n I.1 theta| ≤
      2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) + 12 * Real.pi / n := by
  classical
  rw [← Finset.sum_subtype F.base (by simp)
    (fun I ↦ |Zaa n I theta|)]
  rw [ZlG F theta,
    Finset.sum_union (Zjw F theta),
    Finset.sum_union (ZkG F theta)]
  have hleft := Zl7 hn F htheta
  have hright := ZlX hn F htheta
  have hcross := Zly hn F htheta
  dsimp [eta] at hleft hright
  calc
    (∑ I ∈ Zbx F theta, |Zaa n I theta|) +
          (∑ I ∈ Zbj F theta, |Zaa n I theta|) +
        ∑ I ∈ Zba F theta, |Zaa n I theta| ≤
      1 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
        1 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by linarith
    _ = 2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by ring
end
end Xq.KernelReflectedClaim
end
section
namespace Xq.ConcreteKernelClaims
open scoped BigOperators Interval
open Real Set MeasureTheory intervalIntegral
noncomputable section
open Xq.OddSine
private abbrev Interval := ℝ × ℝ
theorem Zan
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hmono : MonotoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.2 - f I.1) ≤ f U - f L := by
  classical
  let t : Finset (Lex Interval) := s.image toLex
  let m := t.card
  let e : Fin m ≃o ↥t := Finset.orderIsoOfFin t rfl
  have emem (k : Fin m) : ofLex ((e k : ↥t) : Lex Interval) ∈ s := by
    have hk := (e k).property
    change ((e k : ↥t) : Lex Interval) ∈ s.image toLex at hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨I, hI, hEq⟩
    simpa [← hEq] using hI
  let A : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 else f U
  let B : ℕ → ℝ := fun k ↦
    if hk : k < m then f (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).2 else f U
  let E : ℕ → ℝ := fun k ↦ B k - A k
  have hchain : ∀ k < m, B k ≤ A (k + 1) := by
    intro k hk
    simp only [B, A, dif_pos hk]
    by_cases hks : k + 1 < m
    · rw [dif_pos hks]
      apply hmono
      · exact ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans
            (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
      · exact ⟨(hinside _ (emem ⟨k + 1, hks⟩)).1,
          (hord _ (emem ⟨k + 1, hks⟩)).le.trans
            (hinside _ (emem ⟨k + 1, hks⟩)).2⟩
      have horder : e ⟨k, hk⟩ ≤ e ⟨k + 1, hks⟩ :=
        e.le_iff_le.mpr (by simp)
      have hleft : (ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval)).1 ≤
          (ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval)).1 := by
        exact (Prod.Lex.le_iff.mp horder).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
      have hne : ofLex ((e ⟨k, hk⟩ : ↥t) : Lex Interval) ≠
          ofLex ((e ⟨k + 1, hks⟩ : ↥t) : Lex Interval) := by
        intro heq
        have heq' : e ⟨k, hk⟩ = e ⟨k + 1, hks⟩ := by
          apply Subtype.ext
          exact ofLex.injective heq
        have : (⟨k, hk⟩ : Fin m) = ⟨k + 1, hks⟩ := e.injective heq'
        simp at this
      rcases hsep (emem ⟨k, hk⟩) (emem ⟨k + 1, hks⟩) hne with hgood | hbad
      · exact hgood
      · have hstrict := hord _ (emem ⟨k + 1, hks⟩)
        linarith
    · rw [dif_neg hks]
      exact hmono
        ⟨(hinside _ (emem ⟨k, hk⟩)).1.trans (hord _ (emem ⟨k, hk⟩)).le,
          (hinside _ (emem ⟨k, hk⟩)).2⟩
        ⟨hLU, le_rfl⟩ (hinside _ (emem ⟨k, hk⟩)).2
  have htelescope :=
    Xq.KernelClaims.Za0
      (n := 1) (m := m) (A := A) (B := B) (E := E) (by norm_num)
      (fun k hk ↦ by simp [E]) hchain
  have hsum : (∑ I ∈ s, (f I.2 - f I.1)) = ∑ k ∈ Finset.range m, E k := by
    calc
      (∑ I ∈ s, (f I.2 - f I.1)) =
          ∑ J ∈ t, (f (ofLex J).2 - f (ofLex J).1) := by
            symm
            simp [t]
      _ = ∑ J : ↥t, (f (ofLex (J.1 : Lex Interval)).2 -
          f (ofLex (J.1 : Lex Interval)).1) := by
            symm
            exact (Finset.sum_subtype (M := ℝ) (s := t) (p := fun J ↦ J ∈ t)
              (by simp) (fun J : Lex Interval ↦
                f (ofLex J).2 - f (ofLex J).1)).symm
      _ = ∑ i : Fin m, (f (ofLex ((e i : ↥t) : Lex Interval)).2 -
          f (ofLex ((e i : ↥t) : Lex Interval)).1) := by
            exact (e.toEquiv.sum_comp (fun J : ↥t ↦
              f (ofLex (J.1 : Lex Interval)).2 -
                f (ofLex (J.1 : Lex Interval)).1)).symm
      _ = ∑ i : Fin m, E i := by
            apply Finset.sum_congr rfl
            intro i _
            simp [E, A, B, i.isLt]
      _ = ∑ k ∈ Finset.range m, E k := Fin.sum_univ_eq_sum_range E m
  rw [hsum]
  by_cases hm : m = 0
  · simpa [hm] using sub_nonneg.mpr (hmono ⟨le_rfl, hLU⟩ ⟨hLU, le_rfl⟩ hLU)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hA0 : A 0 = f (ofLex ((e ⟨0, hmpos⟩ : ↥t) : Lex Interval)).1 := by
      simp [A, hmpos]
    have hAm : A m = f U := by simp [A]
    rw [hA0, hAm] at htelescope
    simp only [Nat.cast_one, div_one] at htelescope
    exact htelescope.trans (sub_le_sub_left
      (hmono ⟨le_rfl, hLU⟩
        ⟨(hinside _ (emem ⟨0, hmpos⟩)).1,
          (hord _ (emem ⟨0, hmpos⟩)).le.trans
            (hinside _ (emem ⟨0, hmpos⟩)).2⟩
        (hinside _ (emem ⟨0, hmpos⟩)).1) _)
theorem ZaL
    (s : Finset Interval) (f : ℝ → ℝ) (L U : ℝ)
    (hord : ∀ I ∈ s, I.1 < I.2)
    (hLU : L ≤ U)
    (hinside : ∀ I ∈ s, L ≤ I.1 ∧ I.2 ≤ U)
    (hsep : Set.Pairwise (↑s : Set Interval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1))
    (hanti : AntitoneOn f (Icc L U)) :
    ∑ I ∈ s, (f I.1 - f I.2) ≤ f L - f U := by
  have h := Zan s (-f) L U hord hLU hinside hsep
    (fun _ hx _ hy hxy ↦ neg_le_neg (hanti hx hy hxy))
  simpa only [Pi.neg_apply, neg_sub_neg] using h
def ZaO (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    Xq.KernelReplacementMonotone.Zj (x - theta) *
      Real.sin ((2 * (n : ℝ)) * (x - theta))
private lemma ZeR {n : ℕ} (hn : 0 < n)
    (F : Za n) :
    Set.Pairwise (↑F.base : Set RealInterval)
      (fun I J ↦ I.2 ≤ J.1 ∨ J.2 ≤ I.1) := by
  intro I hI J hJ hne
  have hgrid : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos (by exact_mod_cast hn)
  by_cases hfirst : I.1 ≤ J.1
  · left
    by_contra hnot
    have hJinI : J.1 ∈ Icc I.1 I.2 :=
      ⟨hfirst, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne J.1 hJinI J.1
      ⟨le_rfl, F.ordered J hJ⟩
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
  · right
    have hsecond : J.1 ≤ I.1 := (lt_of_not_ge hfirst).le
    by_contra hnot
    have hIinJ : I.1 ∈ Icc J.1 J.2 :=
      ⟨hsecond, (lt_of_not_ge hnot).le⟩
    have hsep := F.separated hI hJ hne I.1
      ⟨le_rfl, F.ordered I hI⟩ I.1 hIinJ
    have : Real.pi / (n : ℝ) ≤ 0 := by simpa using hsep
    exact (not_le_of_gt hgrid) this
private lemma ZbP {n : ℕ} (F : Za n)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) {u : ℝ}
    (hu : u ∈ Icc (I.1 - theta) (I.2 - theta)) :
    u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hquadrant := F.in_first_quadrant I hI
  constructor
  · linarith [hu.1, hquadrant.1, htheta.2]
  · linarith [hu.2, hquadrant.2, htheta.1]
private lemma ZdT {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) :
    Real.cos ((2 * (n : ℝ)) * (I.2 - theta)) =
      Real.cos ((2 * (n : ℝ)) * (I.1 - theta)) := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I hI
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [ha, hb]
  calc
    Real.cos ((2 * (n : ℝ)) * ((b : ℝ) * Real.pi / n - theta)) =
        Real.cos ((b : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) := by
          congr 1
          field_simp [hn0]
    _ = Real.cos ((2 * (n : ℝ)) * theta) :=
      Real.cos_int_mul_two_pi_sub _ b
    _ = Real.cos ((a : ℝ) * (2 * Real.pi) - (2 * (n : ℝ)) * theta) :=
      (Real.cos_int_mul_two_pi_sub _ a).symm
    _ = Real.cos ((2 * (n : ℝ)) * ((a : ℝ) * Real.pi / n - theta)) := by
          congr 1
          field_simp [hn0]
private lemma Zh5 (n : ℕ) (I : RealInterval)
    (theta : ℝ) :
    ZaO n I theta =
      ∫ u in I.1 - theta..I.2 - theta,
        Xq.KernelReplacementMonotone.Zj u *
          Real.sin ((2 * (n : ℝ)) * u) := by
  exact intervalIntegral.integral_comp_sub_right
    (fun u : ℝ ↦
      Xq.KernelReplacementMonotone.Zj u *
        Real.sin ((2 * (n : ℝ)) * u)) theta
private lemma Zij {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    {I : RealInterval} (hI : I ∈ F.base) :
    |ZaO n I theta| ≤
      (Xq.KernelReplacementMonotone.Zj (I.2 - theta) -
        Xq.KernelReplacementMonotone.Zj (I.1 - theta)) / n := by
  rw [Zh5]
  have hdata :=
    Xq.KernelReplacementMonotone.Zfp
  have hosc := Xq.KernelClaims.Zbf
    (h := Xq.KernelReplacementMonotone.Zj)
    (h' := deriv Xq.KernelReplacementMonotone.Zj)
    hn (sub_le_sub_right (F.ordered I hI) theta)
    (fun u hu ↦ hdata.1 u (ZbP F htheta hI hu))
    (hdata.2.1.mono (fun u hu ↦ ZbP F htheta hI hu))
    (fun u hu ↦ hdata.2.2 u (ZbP F htheta hI hu))
    (ZdT hn F hI)
  have hmono := Xq.KernelReplacementMonotone.Zbm
    (ZbP F htheta hI
      ⟨le_rfl, sub_le_sub_right (F.ordered I hI) theta⟩)
    (ZbP F htheta hI
      ⟨sub_le_sub_right (F.ordered I hI) theta, le_rfl⟩)
    (sub_le_sub_right (F.ordered I hI) theta)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at hosc
  exact hosc
theorem Zg3 {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I ∈ F.base, |ZaO n I theta| ≤
      (2 - 4 / Real.pi) / n := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let f : ℝ → ℝ := fun x ↦
    Xq.KernelReplacementMonotone.Zj (x - theta)
  have hfmono : MonotoneOn f (Icc (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    exact Xq.KernelReplacementMonotone.Zbm
      ⟨by linarith [hx.1, htheta.2], by linarith [hx.2, htheta.1]⟩
      ⟨by linarith [hy.1, htheta.2], by linarith [hy.2, htheta.1]⟩
      (sub_le_sub_right hxy theta)
  have htel := Zan F.base f 0 (Real.pi / 2)
    F.nondegenerate (by positivity) F.in_first_quadrant
    (ZeR hn0 F) hfmono
  have hglobal : f (Real.pi / 2) - f 0 ≤
      Xq.KernelReplacementMonotone.Zj (Real.pi / 2) -
        Xq.KernelReplacementMonotone.Zj (-(Real.pi / 2)) := by
    apply sub_le_sub
    · exact Xq.KernelReplacementMonotone.Zbm
        ⟨by linarith [htheta.2, Real.pi_pos], by linarith [htheta.1]⟩
        ⟨by linarith [Real.pi_pos], le_rfl⟩ (by linarith [htheta.1])
    · exact Xq.KernelReplacementMonotone.Zbm
        ⟨le_rfl, by linarith [Real.pi_pos]⟩
        ⟨by linarith [htheta.2], by linarith [htheta.1, Real.pi_pos]⟩
        (by linarith [htheta.2])
  calc
    ∑ I ∈ F.base, |ZaO n I theta| ≤
        ∑ I ∈ F.base, (f I.2 - f I.1) / n := by
          apply Finset.sum_le_sum
          intro I hI
          exact Zij hn0 F htheta hI
    _ = (∑ I ∈ F.base, (f I.2 - f I.1)) / n := by
          rw [Finset.sum_div]
    _ ≤ (f (Real.pi / 2) - f 0) / n := by
          exact div_le_div_of_nonneg_right htel (Nat.cast_nonneg n)
    _ ≤ (Xq.KernelReplacementMonotone.Zj (Real.pi / 2) -
        Xq.KernelReplacementMonotone.Zj (-(Real.pi / 2))) / n := by
          exact div_le_div_of_nonneg_right hglobal (Nat.cast_nonneg n)
    _ = (2 - 4 / Real.pi) / n := by
          rw [Xq.KernelReplacementMonotone.Zex]
theorem ZeS {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∑ I : (↑F.base : Type), |ZaO n I.1 theta| ≤
      (2 - 4 / Real.pi) / n := by
  rw [Finset.univ_eq_attach]
  calc
    ∑ I ∈ F.base.attach, |ZaO n I.1 theta| =
        ∑ I ∈ F.base, |ZaO n I theta| :=
      Finset.sum_attach F.base (fun I ↦ |ZaO n I theta|)
    _ ≤ (2 - 4 / Real.pi) / n :=
      Zg3 hn F htheta
def ZcW (n : ℕ) (I : RealInterval) (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2,
    (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
      Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta))
private lemma ZbQ {n : ℕ} (hn : 0 < n)
    {u : ℝ} (huHalf : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hu : u ≠ 0) :
    Real.sin ((2 * n : ℕ) * u) / Real.sin u =
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * u) +
        Xq.KernelReplacementMonotone.Zj u *
          Real.sin (2 * (n : ℝ) * u) := by
  have hsin := Xq.KernelReplacementMonotone.ZdU
    huHalf hu
  have hscale : (2 * (n : ℝ)) ≠ 0 := by positivity
  have harg : 2 * (n : ℝ) * u ≠ 0 := mul_ne_zero hscale hu
  rw [Real.sinc_of_ne_zero harg,
    Xq.KernelReplacementMonotone.Za2 hu hsin]
  norm_cast
  field_simp [hu, hsin, hscale]
  ring
theorem ZbW
    {n : ℕ} (hn : 0 < n) (F : Za n)
    {I : RealInterval} (hI : I ∈ F.base) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ZcW n I theta =
      Xq.KernelDistantClaim.ZG n I theta +
        ZaO n I theta -
          Xq.KernelReflectedClaim.Zaa n I theta := by
  let p : ℝ → ℝ := fun x ↦
    2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))
  let r : ℝ → ℝ := fun x ↦
    Xq.KernelReplacementMonotone.Zj (x - theta) *
      Real.sin (2 * (n : ℝ) * (x - theta))
  let q : ℝ → ℝ := fun x ↦
    Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta)
  let s : ℝ → ℝ := fun x ↦
    Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)
  have hord := F.ordered I hI
  have hpint : IntervalIntegrable p volume I.1 I.2 := by
    apply Continuous.intervalIntegrable
    dsimp [p]
    fun_prop
  have hrcont : ContinuousOn r (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hxHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ZbP F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    have hamp : ContinuousAt
        (fun y : ℝ ↦
          Xq.KernelReplacementMonotone.Zj (y - theta)) x := by
      have hsub : ContinuousAt (fun y : ℝ ↦ y - theta) x :=
        continuousAt_id.sub continuousAt_const
      simpa only [Function.comp_def] using
        (Xq.KernelReplacementMonotone.Zbk
          hxHalf).continuousAt.comp_of_eq hsub rfl
    exact (hamp.mul (by fun_prop)).continuousWithinAt
  have hrint : IntervalIntegrable r volume I.1 I.2 := hrcont.intervalIntegrable
  have hscont : ContinuousOn s (uIcc I.1 I.2) := by
    intro x hx
    have hxI : x ∈ Icc I.1 I.2 := by
      simpa [uIcc_of_le hord] using hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmesh : 0 < 100 * Real.pi / (n : ℝ) := by positivity
    have haxes := F.away_from_axes I hI
    have hsumPos : 0 < x + theta := by
      linarith [hxI.1, haxes.1, htheta.1]
    have hsumLt : x + theta < Real.pi := by
      linarith [hxI.2, haxes.2, htheta.2]
    have hsin : Real.sin (x + theta) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hsumPos hsumLt)
    have hnum : ContinuousAt
        (fun y : ℝ ↦ Real.sin ((2 * n : ℕ) * (y + theta))) x := by
      fun_prop
    have hden : ContinuousAt (fun y : ℝ ↦ Real.sin (y + theta)) x := by
      fun_prop
    exact (hnum.div hden hsin).continuousWithinAt
  have hsint : IntervalIntegrable s volume I.1 I.2 := hscont.intervalIntegrable
  have hqr : ∀ᵐ x ∂volume, x ∈ uIoc I.1 I.2 → q x = p x + r x := by
    filter_upwards [Measure.ae_ne volume theta] with x hxt hx
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - theta ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ZbP F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    exact ZbQ hn huHalf hu
  have hqrRestrict : p + r =ᵐ[volume.restrict (uIoc I.1 I.2)] q := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume theta)] with x hx hxt
    have hxIoc : x ∈ Ioc I.1 I.2 := by
      simpa [uIoc_of_le hord] using hx
    have hxI : x ∈ Icc I.1 I.2 := ⟨hxIoc.1.le, hxIoc.2⟩
    have hu : x - theta ≠ 0 := sub_ne_zero.mpr hxt
    have huHalf : x - theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ZbP F htheta hI
        ⟨sub_le_sub_right hxI.1 theta, sub_le_sub_right hxI.2 theta⟩
    exact (ZbQ hn huHalf hu).symm
  have hqint : IntervalIntegrable q volume I.1 I.2 :=
    (hpint.add hrint).congr_ae hqrRestrict
  have hfirst : (∫ x in I.1..I.2, q x) =
      (∫ x in I.1..I.2, p x) + ∫ x in I.1..I.2, r x := by
    rw [intervalIntegral.integral_congr_ae hqr,
      intervalIntegral.integral_add hpint hrint]
  rw [ZcW, show (fun x : ℝ ↦
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) =
      fun x ↦ q x - s x by rfl,
    intervalIntegral.integral_sub hqint hsint, hfirst]
  rfl
theorem Zgm {n : ℕ} (hn : 4096 ≤ n) :
    2 / Real.pi + 2 / (n * Real.sin (100 * Real.pi / n)) +
        12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤ 2 / 3 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let x : ℝ := 100 * Real.pi / n
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 10 := by
    rw [show x = 100 * Real.pi / n by rfl, div_le_iff₀ hnpos]
    nlinarith [Real.pi_lt_four]
  have hxsq : x ^ 2 ≤ 1 / 100 := by nlinarith [sq_nonneg x]
  have hsin0 := Real.sin_ge_sub_cube hxpos.le
  have hsin : (99 / 100) * x ≤ Real.sin x := by
    nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hxsq)]
  have hden : 300 ≤ (n : ℝ) * Real.sin x := by
    calc
      (300 : ℝ) ≤ 99 * Real.pi := by
        nlinarith [Real.pi_gt_d2]
      _ = (n : ℝ) * ((99 / 100) * x) := by
        dsimp [x]
        field_simp [hn0]
      _ ≤ (n : ℝ) * Real.sin x := mul_le_mul_of_nonneg_left hsin hnpos.le
  have hdenpos : 0 < (n : ℝ) * Real.sin x := lt_of_lt_of_le (by norm_num) hden
  have hreflectedPole : 2 / ((n : ℝ) * Real.sin x) ≤ 1 / 150 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  have hprincipal : 2 / Real.pi ≤ 100 / 157 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d2]
  have hcrossing : 12 * Real.pi / (n : ℝ) ≤ 189 / 20480 := by
    apply (div_le_iff₀ hnpos).2
    nlinarith [Real.pi_lt_d2]
  have hreplacement : (2 - 4 / Real.pi) / (n : ℝ) ≤ 1 / 2048 := by
    apply (div_le_iff₀ hnpos).2
    have : 0 ≤ 4 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
    nlinarith
  change 2 / Real.pi + 2 / ((n : ℝ) * Real.sin x) +
      12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤ 2 / 3
  calc
    2 / Real.pi + 2 / ((n : ℝ) * Real.sin x) +
          12 * Real.pi / n + (2 - 4 / Real.pi) / n ≤
        100 / 157 + 1 / 150 + 189 / 20480 + 1 / 2048 := by linarith
    _ ≤ 2 / 3 := by norm_num
theorem Zfq {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n) (alpha : (↑F.base : Type) → ℝ)
    (halpha : Xq.Discrepancy.Zcw alpha) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |(∑ I : (↑F.base : Type), alpha I * ZcW n I.1 theta) -
        (∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
          alpha I * Xq.KernelDistantClaim.ZG n I.1 theta)| ≤
      2 / 3 := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let principal : (↑F.base : Type) → ℝ := fun I ↦
    Xq.KernelDistantClaim.ZG n I.1 theta
  let replacement : (↑F.base : Type) → ℝ := fun I ↦
    ZaO n I.1 theta
  let reflected : (↑F.base : Type) → ℝ := fun I ↦
    Xq.KernelReflectedClaim.Zaa n I.1 theta
  have halphaAbs (I : (↑F.base : Type)) : |alpha I| = 1 := by
    rcases halpha I with hI | hI <;> simp [hI]
  have hquotient :
      (∑ I : (↑F.base : Type), alpha I * ZcW n I.1 theta) =
        (∑ I : (↑F.base : Type), alpha I * principal I) +
          (∑ I : (↑F.base : Type), alpha I * replacement I) -
            ∑ I : (↑F.base : Type), alpha I * reflected I := by
    simp_rw [ZbW
      hn0 F (hI := Subtype.property _) htheta]
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rfl
  have hpartition :
      (∑ I : (↑F.base : Type), alpha I * principal I) =
        (∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
          alpha I * principal I) +
        ∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
          alpha I * principal I := by
    rw [Xq.KernelDistantClaim.Zhk]
    calc
      (∑ I : (↑F.base : Type), alpha I * principal I) =
          (∑ I ∈ Finset.univ \
              Xq.KernelNearGeometry.Zu F theta,
            alpha I * principal I) +
          ∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
            alpha I * principal I :=
        (Finset.sum_sdiff
          (Finset.subset_univ
            (Xq.KernelNearGeometry.Zu F theta))).symm
      _ = (∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
            alpha I * principal I) +
          ∑ I ∈ Finset.univ \
              Xq.KernelNearGeometry.Zu F theta,
            alpha I * principal I := add_comm _ _
  have hresidual :
      (∑ I : (↑F.base : Type), alpha I * ZcW n I.1 theta) -
          (∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
            alpha I * Xq.KernelDistantClaim.ZG n I.1 theta) =
        (∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
          alpha I * principal I) +
        (∑ I : (↑F.base : Type), alpha I * replacement I) -
          ∑ I : (↑F.base : Type), alpha I * reflected I := by
    rw [hquotient, hpartition]
    dsimp only [principal]
    ring
  have hprincipal :
      |∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
          alpha I * principal I| ≤ 2 / Real.pi := by
    calc
      |∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
          alpha I * principal I| ≤
          ∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
            |alpha I * principal I| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
            |principal I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ 2 / Real.pi :=
        Xq.KernelDistantClaim.Zde
          hn0 F htheta
  have hreplacement :
      |∑ I : (↑F.base : Type), alpha I * replacement I| ≤
        (2 - 4 / Real.pi) / n := by
    calc
      |∑ I : (↑F.base : Type), alpha I * replacement I| ≤
          ∑ I : (↑F.base : Type), |alpha I * replacement I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : (↑F.base : Type), |replacement I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ (2 - 4 / Real.pi) / n :=
        ZeS hn F htheta
  have hreflected :
      |∑ I : (↑F.base : Type), alpha I * reflected I| ≤
        2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n := by
    calc
      |∑ I : (↑F.base : Type), alpha I * reflected I| ≤
          ∑ I : (↑F.base : Type), |alpha I * reflected I| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ I : (↑F.base : Type), |reflected I| := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [abs_mul, halphaAbs, one_mul]
      _ ≤ 2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n :=
        Xq.KernelReflectedClaim.ZhK hn F htheta
  rw [hresidual]
  calc
    |(∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
          alpha I * principal I) +
        (∑ I : (↑F.base : Type), alpha I * replacement I) -
          ∑ I : (↑F.base : Type), alpha I * reflected I| ≤
        |∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
          alpha I * principal I| +
        |∑ I : (↑F.base : Type), alpha I * replacement I| +
        |∑ I : (↑F.base : Type), alpha I * reflected I| := by
          linarith [abs_add_le
            (∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
              alpha I * principal I)
            (∑ I : (↑F.base : Type), alpha I * replacement I),
            abs_sub
              ((∑ I ∈ Xq.KernelDistantClaim.ZT F theta,
                alpha I * principal I) +
                ∑ I : (↑F.base : Type), alpha I * replacement I)
              (∑ I : (↑F.base : Type), alpha I * reflected I)]
    _ ≤ 2 / Real.pi + (2 - 4 / Real.pi) / n +
        (2 / ((n : ℝ) * Real.sin (100 * Real.pi / n)) +
          12 * Real.pi / n) := by linarith
    _ ≤ 2 / 3 := by
      linarith [Zgm hn]
end
end Xq.ConcreteKernelClaims
end
section
namespace Xq.OddKernelCertificate
open scoped BigOperators Interval
open Set
noncomputable section
open Xq.OddSine
local instance (P : Prop) : Decidable P := Classical.propDecidable P
def Zw {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  ZaU F alpha theta / (K * Real.sqrt n)
private def ZaT (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) : ℝ :=
  min 4 (max (if dangerous then 4 / 3 else 0) a)
private lemma Zf9 (dangerous : Prop) [Decidable dangerous]
    {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ZaT dangerous a := by
  unfold ZaT
  apply le_min (by norm_num)
  exact le_max_of_le_right ha
private lemma Zjf (dangerous : Prop) [Decidable dangerous]
    (a : ℝ) :
    ZaT dangerous a ≤ 4 := by
  exact min_le_left _ _
private lemma ZgF {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (hdangerous : dangerous) :
    4 / 3 ≤ ZaT dangerous a := by
  unfold ZaT
  rw [if_pos hdangerous]
  apply le_min (by norm_num)
  exact le_max_left _ _
private lemma Zh6 {dangerous : Prop}
    [Decidable dangerous] {a : ℝ} (ha : 0 ≤ a)
    (haUpper : a ≤ 14 / 3)
    (haLower : dangerous → 2 / 3 ≤ a) :
    |a - ZaT dangerous a| ≤ 2 / 3 := by
  classical
  unfold ZaT
  by_cases hdangerous : dangerous
  · rw [if_pos hdangerous]
    have halower := haLower hdangerous
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right]
      · by_cases ha43 : 4 / 3 ≤ a
        · rw [max_eq_right ha43]
          norm_num
        · rw [max_eq_left (le_of_not_ge ha43)]
          rw [abs_of_nonpos]
          · linarith
          · linarith
      · exact max_le (by norm_num) ha4
    · have h4a : 4 ≤ max (4 / 3) a := by
        exact le_max_of_le_right (le_of_not_ge ha4)
      rw [min_eq_left h4a, abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith
  · rw [if_neg hdangerous, max_eq_right ha]
    by_cases ha4 : a ≤ 4
    · rw [min_eq_right ha4]
      norm_num
    · rw [min_eq_left (le_of_not_ge ha4),
        abs_of_nonneg (sub_nonneg.2 (le_of_not_ge ha4))]
      linarith
private def ZgG {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  let m := ZaT (ZaH F theta)
    |Zw F alpha theta|
  if 0 ≤ Zw F alpha theta then m else -m
private def Zg4 {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  Zw F alpha theta - ZgG F alpha theta
private lemma Zj6 {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    |ZgG F alpha theta| =
      ZaT (ZaH F theta)
        |Zw F alpha theta| := by
  classical
  simp only [ZgG]
  by_cases hv : 0 ≤ Zw F alpha theta
  · rw [if_pos hv,
      abs_of_nonneg (Zf9 _ (abs_nonneg _))]
  · rw [if_neg hv, abs_neg,
      abs_of_nonneg (Zf9 _ (abs_nonneg _))]
private lemma Zlk {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    |Zg4 F alpha theta| =
      |(|Zw F alpha theta| -
        ZaT (ZaH F theta)
          |Zw F alpha theta|)| := by
  classical
  unfold Zg4 ZgG
  by_cases hv : 0 ≤ Zw F alpha theta
  · rw [if_pos hv, abs_of_nonneg hv]
  · rw [if_neg hv, abs_of_neg (lt_of_not_ge hv)]
    have heq : Zw F alpha theta +
        ZaT (ZaH F theta)
            (-Zw F alpha theta) =
          -(-Zw F alpha theta -
            ZaT (ZaH F theta)
              (-Zw F alpha theta)) := by ring
    rw [sub_neg_eq_add, heq, abs_neg]
noncomputable def ZeT {n : ℕ} (hn : 0 < n)
    (F : Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (hlower : ∀ theta, ZaH F theta →
      2 / 3 ≤ |Zw F alpha theta|)
    (hupper : ∀ theta, |Zw F alpha theta| ≤ 14 / 3) :
    ZcC F alpha := by
  classical
  refine
    { main := ZgG F alpha
      error := Zg4 F alpha
      decomposition := ?_
      main_lower := ?_
      main_upper := ?_
      error_bound := ?_ }
  · intro theta
    have hscale : K * Real.sqrt n ≠ 0 := by
      apply mul_ne_zero
      · norm_num [K]
      · exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
    rw [show ZgG F alpha theta + Zg4 F alpha theta =
        Zw F alpha theta by
      simp only [Zg4]
      ring]
    simp only [Zw]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ hscale).symm
  · intro theta htheta
    rw [Zj6]
    exact ZgF htheta
  · intro theta
    rw [Zj6]
    exact Zjf _ _
  · intro theta
    rw [Zlk]
    exact Zh6 (abs_nonneg _)
      (hupper theta) (hlower theta)
theorem ZfQ {n : ℕ}
    (F : Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (hlower : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ZaH F theta → 2 / 3 ≤ |Zw F alpha theta|)
    (hupper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |Zw F alpha theta| ≤ 14 / 3) :
    (∀ theta, ZaH F theta →
      2 / 3 ≤ |Zw F alpha theta|) ∧
    (∀ theta, |Zw F alpha theta| ≤ 14 / 3) := by
  constructor
  · intro theta htheta
    obtain ⟨I, hI, hmem | hmem | hmem | hmem⟩ := htheta
    · exact hlower theta
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
        ⟨I, hI, Or.inl hmem⟩
    · have hqmem : -theta ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : ZaH F (-theta) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (-theta) hqmem hqdanger
      simpa only [Zw, ZaU,
        ZlD, abs_div, abs_neg] using hq
    · have hqmem : Real.pi - theta ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : ZaH F (Real.pi - theta) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (Real.pi - theta) hqmem hqdanger
      simpa only [Zw, ZaU,
        Zi5, abs_div] using hq
    · have hqmem : theta - Real.pi ∈ Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨(F.in_first_quadrant I hI).1.trans hmem.1,
          hmem.2.trans (F.in_first_quadrant I hI).2⟩
      have hqdanger : ZaH F (theta - Real.pi) :=
        ⟨I, hI, Or.inl hmem⟩
      have hq := hlower (theta - Real.pi) hqmem hqdanger
      have heq : theta = (theta - Real.pi) + Real.pi := by ring
      rw [heq]
      simpa only [Zw, ZaU,
        Zi6, abs_div, abs_neg] using hq
  · intro theta
    obtain ⟨theta', htheta', heq⟩ :=
      Zb9 n (ZbJ F alpha) theta
    have hq := hupper theta' htheta'
    simp only [Zw, ZaU, abs_div] at hq ⊢
    rw [heq]
    exact hq
theorem Zg5 {n : ℕ} (hn : 0 < n)
    (F : Za n) (I : (↑F.base : Type)) :
    ∃ a b : ℤ, a < b ∧
      I.1.1 = (a : ℝ) * Real.pi / n ∧
      I.1.2 = (b : ℝ) * Real.pi / n := by
  obtain ⟨a, b, ha, hb⟩ := F.grid_endpoints I.1 I.property
  refine ⟨a, b, ?_, ha, hb⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscalePos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hscaled : (a : ℝ) * (Real.pi / (n : ℝ)) <
      (b : ℝ) * (Real.pi / (n : ℝ)) := by
    simpa only [mul_div_assoc, ha, hb] using
      F.nondegenerate I.1 I.property
  have habR : (a : ℝ) < b := by
    nlinarith [hscalePos]
  exact_mod_cast habR
theorem ZeY {n : ℕ} (hn : 0 < n)
    (F : Za n) {theta : ℝ}
    (I : (↑F.base : Type)) (htheta : Zal I.1 theta) :
    Xq.KernelDistantClaim.ZG n I.1 theta ∈
      Icc ((4 : ℝ) / 3) 4 := by
  obtain ⟨a, b, hab, ha, hb⟩ := Zg5 hn F I
  have hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have htheta' : theta ∈ Icc ((a : ℝ) * Real.pi / n)
      ((b : ℝ) * Real.pi / n) := by
    change theta ∈ Icc I.1.1 I.1.2 at htheta
    simpa only [← ha, ← hb] using htheta
  have hmain := Xq.SineIntegralGrid.Zg1
    n hn a b hab hshort htheta'
  simpa only [Xq.KernelDistantClaim.ZG, ha, hb] using hmain
theorem Zdf {n : ℕ}
    (hn : 0 < n) (F : Za n) {theta : ℝ}
    (I : (↑F.base : Type))
    (hnear : I ∈ Xq.KernelNearGeometry.Zu F theta)
    (hout : ¬Zal I.1 theta) :
    |Xq.KernelDistantClaim.ZG n I.1 theta| ≤ 2 := by
  obtain ⟨a, b, hab, ha, hb⟩ := Zg5 hn F I
  have hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n := by
    rw [← ha, ← hb]
    exact F.short I.1 I.property
  have hnearGap : Xq.KernelNearGeometry.Near n theta I.1 := by
    simpa only [Xq.KernelNearGeometry.Zu,
      Finset.mem_filter, Finset.mem_univ, true_and] using hnear
  rw [Zal, mem_Icc] at hout
  have hside :
      (theta ≤ (a : ℝ) * Real.pi / n ∧
        (a : ℝ) * Real.pi / n - theta ≤ Real.pi / n) ∨
      ((b : ℝ) * Real.pi / n ≤ theta ∧
        theta - (b : ℝ) * Real.pi / n ≤ Real.pi / n) := by
    rcases not_and_or.mp hout with hleft | hright
    · left
      have htheta : theta ≤ I.1.1 := (lt_of_not_ge hleft).le
      have hgap := hnearGap
      rw [Xq.KernelNearGeometry.Near,
        Xq.KernelNearGeometry.ZcN
          (F.ordered I.1 I.property) htheta] at hgap
      rw [← ha]
      exact ⟨htheta, hgap.le⟩
    · right
      have htheta : I.1.2 ≤ theta := (lt_of_not_ge hright).le
      have hgap := hnearGap
      rw [Xq.KernelNearGeometry.Near,
        Xq.KernelNearGeometry.Zck
          (F.ordered I.1 I.property) htheta] at hgap
      rw [← hb]
      exact ⟨htheta, hgap.le⟩
  have hoff := Xq.SineIntegralGrid.Zfn
    n hn a b hab hshort hside
  simpa only [Xq.KernelDistantClaim.ZG, ha, hb] using hoff
theorem Zc7 {n : ℕ}
    (hn : 0 < n) (F : Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Xq.Discrepancy.Zcw alpha)
    (principal : (↑F.base : Type) → ℝ → ℝ) (error : ℝ → ℝ)
    (hdecomposition : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      Zw F alpha theta =
        (∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
          alpha I * principal I theta) + error theta)
    (herror : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |error theta| ≤ 2 / 3)
    (hself_lower : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I : (↑F.base : Type), Zal I.1 theta →
        4 / 3 ≤ |principal I theta|)
    (hself_upper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I : (↑F.base : Type), Zal I.1 theta →
        |principal I theta| ≤ 4)
    (hoff_upper : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ∀ I ∈ Xq.KernelNearGeometry.Zu F theta,
        ¬Zal I.1 theta → |principal I theta| ≤ 2) :
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2), ZaH F theta →
      2 / 3 ≤ |Zw F alpha theta|) ∧
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |Zw F alpha theta| ≤ 14 / 3) := by
  classical
  have halpha_abs (I : (↑F.base : Type)) : |alpha I| = 1 := by
    rcases halpha I with hI | hI <;> simp [hI]
  constructor
  · intro theta htheta hdangerous
    obtain ⟨I, hthetaI, _hunique⟩ :=
      Xq.KernelNearGeometry.ZcO
        hn F htheta hdangerous
    have hnear := Xq.KernelNearGeometry.Zdo hn F
      I.property hthetaI (fun J ↦ alpha J * principal J theta)
    have hmainLower : 4 / 3 ≤ |alpha I * principal I theta| := by
      rw [abs_mul, halpha_abs, one_mul]
      exact hself_lower theta htheta I hthetaI
    have hreverse : |alpha I * principal I theta| ≤
        |Zw F alpha theta| + |error theta| := by
      rw [hdecomposition theta htheta, hnear]
      calc
        |alpha I * principal I theta| =
            |(alpha I * principal I theta + error theta) - error theta| := by
              ring_nf
        _ ≤ _ := abs_sub _ _
    linarith [herror theta htheta]
  · intro theta htheta
    have hmainUpper :
        |∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
          alpha I * principal I theta| ≤ 4 := by
      by_cases hin : Xq.KernelNearGeometry.Zh0 F theta
      · obtain ⟨I, hI, hthetaI⟩ := hin
        rw [Xq.KernelNearGeometry.Zdo hn F hI hthetaI]
        rw [abs_mul, halpha_abs, one_mul]
        exact hself_upper theta htheta ⟨I, hI⟩ hthetaI
      · have htwo :=
          Xq.KernelNearGeometry.Zcg
            hn F hin (show (0 : ℝ) ≤ 2 by norm_num)
            (fun I ↦ alpha I * principal I theta) (by
              intro I hI
              rw [abs_mul, halpha_abs, one_mul]
              exact hoff_upper theta htheta I hI
                (fun hmem ↦ hin ⟨I.1, I.property, hmem⟩))
        norm_num at htwo ⊢
        exact htwo
    rw [hdecomposition theta htheta]
    calc
      |(∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
            alpha I * principal I theta) + error theta| ≤
          |∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
            alpha I * principal I theta| + |error theta| := abs_add_le _ _
      _ ≤ 4 + 2 / 3 := add_le_add hmainUpper (herror theta htheta)
      _ = 14 / 3 := by norm_num
def Zga {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) : ℝ :=
  Zw F alpha theta -
    ∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
      alpha I * Xq.KernelDistantClaim.ZG n I.1 theta
theorem ZjN {n : ℕ} (F : Za n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Zw F alpha theta =
      (∑ I ∈ Xq.KernelNearGeometry.Zu F theta,
        alpha I * Xq.KernelDistantClaim.ZG n I.1 theta) +
        Zga F alpha theta := by
  simp only [Zga]
  ring
theorem ZgH {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Xq.Discrepancy.Zcw alpha) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    |Zga F alpha theta| ≤ 2 / 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have htarget :=
    Xq.OddKernelIdentity.Zcf
      hnpos F alpha htheta
  rw [Zga]
  change Zw F alpha theta =
      ∑ I : (↑F.base : Type), alpha I *
        Xq.ConcreteKernelClaims.ZcW n I.1 theta at htarget
  rw [htarget]
  exact Xq.ConcreteKernelClaims.Zfq
    hn F alpha halpha htheta
theorem Zej {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Xq.Discrepancy.Zcw alpha) :
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2), ZaH F theta →
      2 / 3 ≤ |Zw F alpha theta|) ∧
    (∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      |Zw F alpha theta| ≤ 14 / 3) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply Zc7 hnpos F alpha halpha
    (fun I theta ↦ Xq.KernelDistantClaim.ZG n I.1 theta)
    (Zga F alpha)
  · exact fun theta _ ↦ ZjN F alpha theta
  · exact fun _ htheta ↦ ZgH hn F alpha halpha htheta
  · intro theta _ I htheta
    have hmain := ZeY hnpos F I htheta
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.1
  · intro theta _ I htheta
    have hmain := ZeY hnpos F I htheta
    rw [abs_of_nonneg (by linarith [hmain.1])]
    exact hmain.2
  · intro theta _ I hnear hout
    exact Zdf hnpos F I hnear hout
noncomputable def Zlc {n : ℕ} (hn : 4096 ≤ n)
    (F : Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (halpha : Xq.Discrepancy.Zcw alpha) :
    ZcC F alpha := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hfirst := Zej hn F alpha halpha
  have hglobal := ZfQ F alpha hfirst.1 hfirst.2
  exact ZeT hnpos F alpha hglobal.1 hglobal.2
end
end Xq.OddKernelCertificate
end
section
namespace Xq.OddSine
open scoped BigOperators Interval
open Set
noncomputable section
def ZW (n : ℕ) : ℕ := 16 * n
def ZcK (n : ℕ) (g : Fin (ZW n)) : ℝ :=
  (2 * (g : ℕ) + 1 : ℕ) * Real.pi / (64 * n)
def Zbb (l : ℕ) : ℝ :=
  14 * Real.sqrt ((9 + l : ℕ) * Real.log 2)
@[simp] theorem Zl8 (n : ℕ) : ZW n = 16 * n := rfl
theorem roundingParameter_nonneg (l : ℕ) : 0 ≤ Zbb l := by
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
theorem Zkr (l : ℕ) :
    (Zbb l) ^ 2 = 196 * ((9 + l : ℕ) * Real.log 2) := by
  rw [Zbb, mul_pow, Real.sq_sqrt]
  · norm_num
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
theorem Zj7 (l : ℕ) :
    Real.exp (-(Zbb l) ^ 2 / 196) =
      (1 / 2 : ℝ) ^ (9 + l) := by
  rw [Zkr]
  have hcancel :
      -(196 * (((9 + l : ℕ) : ℝ) * Real.log 2)) / 196 =
        -(((9 + l : ℕ) : ℝ) * Real.log 2) := by ring
  rw [hcancel]
  calc
    Real.exp (-(((9 + l : ℕ) : ℝ) * Real.log 2)) =
        Real.exp (((9 + l : ℕ) : ℝ) * (-Real.log 2)) := by ring_nf
    _ = Real.exp (-Real.log 2) ^ (9 + l) := Real.exp_nat_mul _ _
    _ = (1 / 2 : ℝ) ^ (9 + l) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
theorem ZhL (n : ℕ) :
    (∑ l : Fin n, Real.exp (-(Zbb l) ^ 2 / 196)) ≤
      (1 / 256 : ℝ) := by
  simp_rw [Zj7]
  calc
    (∑ l : Fin n, (1 / 2 : ℝ) ^ (9 + (l : ℕ))) =
        (1 / 512 : ℝ) * ∑ l : Fin n, (1 / 2 : ℝ) ^ (l : ℕ) := by
          simp_rw [pow_add]
          norm_num
          rw [Finset.mul_sum]
    _ ≤ (1 / 512 : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_geometric_two_le n
    _ = 1 / 256 := by norm_num
theorem ZgI (l : ℕ) :
    Zbb l + 30 ≤ 65 + 2 * l := by
  have htwo_exp : (2 : ℝ) < Real.exp (25 / 36) := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg (x := (25 / 36 : ℝ)) (by norm_num) 5)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hlog : Real.log 2 < 25 / 36 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    exact htwo_exp
  have hradicand :
      ((9 + l : ℕ) : ℝ) * Real.log 2 ≤
        ((35 + 2 * (l : ℝ)) / 14) ^ 2 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hlog)
      (show (0 : ℝ) ≤ ((9 + l : ℕ) : ℝ) by positivity)
    push_cast at hmul
    nlinarith [sq_nonneg (l : ℝ)]
  have hsqrt := Real.sqrt_le_sqrt hradicand
  have hright : 0 ≤ (35 + 2 * (l : ℝ)) / 14 := by positivity
  rw [Real.sqrt_sq hright] at hsqrt
  unfold Zbb
  nlinarith
theorem Zjg {n : ℕ} (hn : 0 < n) (theta : ℝ)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∃ g : Fin (ZW n),
      |theta - ZcK n g| ≤ Real.pi / (64 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmesh : 0 < ZW n := by
    simp [ZW, hn]
  by_cases hend : theta = Real.pi / 2
  · let g : Fin (ZW n) :=
      ⟨ZW n - 1, Nat.sub_lt hmesh (by omega)⟩
    refine ⟨g, ?_⟩
    have hsub : (ZW n - 1 : ℕ) + 1 = ZW n := by
      omega
    have hdifference :
        theta - ZcK n g = Real.pi / (64 * n) := by
      rw [hend]
      simp only [ZcK, g]
      rw [show 2 * (ZW n - 1) + 1 =
          2 * ZW n - 1 by omega]
      simp only [ZW]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (16 * n))]
      field_simp
      ring
    rw [hdifference, abs_of_nonneg (by positivity)]
  · have htheta_lt : theta < Real.pi / 2 :=
      lt_of_le_of_ne htheta.2 hend
    let y : ℝ := theta * (32 * n) / Real.pi
    have hy_nonneg : 0 ≤ y := by
      exact div_nonneg (mul_nonneg htheta.1 (by positivity)) hpi.le
    have hy_lt : y < (ZW n : ℕ) := by
      rw [ZW]
      apply (div_lt_iff₀ hpi).2
      have hmul := mul_lt_mul_of_pos_right htheta_lt
        (show (0 : ℝ) < 32 * n by positivity)
      push_cast at hmul ⊢
      nlinarith
    let k : ℕ := ⌊y⌋₊
    have hk_le : (k : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have hy_succ : y < (k : ℝ) + 1 := by
      simpa [k] using Nat.lt_floor_add_one y
    have hk_mesh : k < ZW n := by
      exact_mod_cast lt_of_le_of_lt hk_le hy_lt
    let g : Fin (ZW n) := ⟨k, hk_mesh⟩
    refine ⟨g, ?_⟩
    have habs : |y - ((k : ℝ) + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hdifference :
        theta - ZcK n g =
          (y - ((k : ℝ) + 1 / 2)) * (Real.pi / (32 * n)) := by
      simp only [ZcK, g]
      dsimp only [y]
      push_cast
      field_simp
      ring
    rw [hdifference, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ Real.pi / (32 * (n : ℝ)))]
    calc
      |y - ((k : ℝ) + 1 / 2)| * (Real.pi / (32 * n)) ≤
          (1 / 2) * (Real.pi / (32 * n)) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ = Real.pi / (64 * n) := by ring
def Zj8 {n : ℕ} (hn : 0 < n) :
    ZhD n (Fin (ZW n)) where
  point := ZcK n
  parameter := fun q ↦ Zbb q.2
  parameter_nonneg := fun q ↦ roundingParameter_nonneg q.2
  budget := by
    rw [Fintype.sum_prod_type]
    simp only
    calc
      (∑ _g : Fin (ZW n),
          ∑ l : Fin n, Real.exp (-(Zbb l) ^ 2 / 196)) =
          (ZW n : ℝ) *
            ∑ l : Fin n, Real.exp (-(Zbb l) ^ 2 / 196) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      _ ≤ (ZW n : ℝ) * (1 / 256 : ℝ) := by
        apply mul_le_mul_of_nonneg_left (ZhL n)
        positivity
      _ = (n : ℝ) / 16 := by
        simp [ZW]
        ring
  parameter_bound := fun _g l ↦ ZgI l
  cover := by
    intro a theta
    obtain ⟨theta', htheta', habs⟩ :=
      Zb9 n a theta
    obtain ⟨g, hnear⟩ := Zjg hn theta' htheta'
    exact ⟨g, theta', hnear, habs⟩
theorem Zks {n : ℕ} (hn : 0 < n) :
    Nonempty (ZhD n (Fin (16 * n))) := by
  exact ⟨Zj8 hn⟩
end
end Xq.OddSine
end
section
open Filter Set
open scoped BigOperators Topology
noncomputable section
namespace Xq.Discrepancy
variable {I J : Type*} [Fintype I] [Fintype J]
def Zao [DecidableEq I]
    (epsilon : ℝ) (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - epsilon ≤ |x i|
@[simp]
theorem Zdp [DecidableEq I]
    {epsilon : ℝ} {x : I → ℝ} {i : I} :
    i ∈ Zao epsilon x ↔ 1 - epsilon ≤ |x i| := by
  simp [Zao]
omit [Fintype I] in
theorem Zll : IsCompact {x : I → ℝ | ZdB x} := by
  have hset : {x : I → ℝ | ZdB x} =
      Set.pi Set.univ (fun _ : I ↦ Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, mem_Icc]
    constructor
    · intro hx i
      simpa only [abs_le] using hx i
    · intro hx i
      simpa only [abs_le] using hx i
  rw [hset]
  exact isCompact_univ_pi fun _ ↦ isCompact_Icc
omit [Fintype J] in
theorem Zgb [DecidableEq I]
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ x : I → ℝ,
        ZdB x ∧
          Fintype.card I ≤
            2 * (Zao epsilon x).card ∧
          ∀ j, |dot (x - x₀) (v j)| ≤ c j * ZdC (v j)) :
    ZfY v x₀ c := by
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hepsilon_pos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hwitness : ∀ n : ℕ, ∃ x : I → ℝ,
      ZdB x ∧
        Fintype.card I ≤
          2 * (Zao (epsilon n) x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * ZdC (v j) := by
    intro n
    exact happrox (epsilon n) (hepsilon_pos n)
  choose x hxCube hxCard hxDiscrepancy using hwitness
  obtain ⟨xLimit, hxLimitCube, phi, hphi, hxLimit⟩ :=
    Zll.tendsto_subseq hxCube
  refine ⟨xLimit, hxLimitCube, ?_, ?_⟩
  · have hepsilon_tendsto :
        Tendsto epsilon atTop (nhds (0 : ℝ)) := by
      simpa only [epsilon, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
    have hepsilon_subseq :
        Tendsto (fun n ↦ epsilon (phi n)) atTop (nhds (0 : ℝ)) :=
      hepsilon_tendsto.comp hphi.tendsto_atTop
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hnotApprox (i : I) (hi : i ∉ Za5 xLimit) :
        ∀ᶠ n in atTop,
          i ∉ Zao (epsilon (phi n)) (x (phi n)) := by
      have habs_le : |xLimit i| ≤ 1 := hxLimitCube i
      have habs_ne : |xLimit i| ≠ 1 := by
        simpa [Za5] using hi
      have hgap : 0 < 1 - |xLimit i| := sub_pos.mpr (lt_of_le_of_ne habs_le habs_ne)
      have htendsto :
          Tendsto
            (fun n ↦ 1 - epsilon (phi n) - |x (phi n) i|)
            atTop (nhds (1 - |xLimit i|)) := by
        simpa using
          (tendsto_const_nhds.sub hepsilon_subseq).sub
            ((hxCoordinate i).abs)
      have hpositive :
          ∀ᶠ n in atTop, 0 < 1 - epsilon (phi n) - |x (phi n) i| :=
        htendsto.eventually (isOpen_Ioi.mem_nhds hgap)
      filter_upwards [hpositive] with n hn
      simp only [Zdp, not_le]
      linarith
    have hsubset_eventually :
        ∀ᶠ n in atTop,
          Zao (epsilon (phi n)) (x (phi n)) ⊆
            Za5 xLimit := by
      have hall :
          ∀ᶠ n in atTop, ∀ i : I,
            i ∈ Zao (epsilon (phi n)) (x (phi n)) →
              i ∈ Za5 xLimit := by
        apply Filter.eventually_all.mpr
        intro i
        by_cases hfixed : i ∈ Za5 xLimit
        · exact Eventually.of_forall fun _ _ ↦ hfixed
        · exact (hnotApprox i hfixed).mono fun _ hnot hmem ↦
            False.elim (hnot hmem)
      exact hall.mono fun _ hn _ hi ↦ hn _ hi
    obtain ⟨n, hsubset⟩ := hsubset_eventually.exists
    have hcardSubset := Finset.card_le_card hsubset
    exact (hxCard (phi n)).trans (Nat.mul_le_mul_left 2 hcardSubset)
  · intro j
    have hxCoordinate (i : I) :
        Tendsto (fun n ↦ x (phi n) i) atTop (nhds (xLimit i)) :=
      tendsto_pi_nhds.mp hxLimit i
    have hdot :
        Tendsto (fun n ↦ dot (x (phi n) - x₀) (v j)) atTop
          (nhds (dot (xLimit - x₀) (v j))) := by
      unfold dot
      apply tendsto_finsetSum
      intro i hi
      exact ((hxCoordinate i).sub tendsto_const_nhds).mul_const (v j i)
    exact le_of_tendsto' hdot.abs fun n ↦ hxDiscrepancy (phi n) j
end Xq.Discrepancy
end
section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace Xq.EdgeWalk
open Xq.Discrepancy Xq.GaussianWalk Xq.ProjectionWalk
variable {I J : Type*} [Fintype I] [Fintype J]
abbrev toWalk (v : I → ℝ) : Zm I := WithLp.toLp 2 v
theorem ZgJ (v : Zm I) :
    ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]
theorem Zky (v : I → ℝ) : ZdC v = ‖toWalk v‖ := by
  rw [ZdC, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
theorem ZlY (x v : I → ℝ) :
    dot x v = inner ℝ (toWalk v) (toWalk x) := by
  simp [dot, toWalk, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
def ZH (v : I → ℝ) : Zm I :=
  (ZdC v)⁻¹ • toWalk v
theorem Zdg (v : I → ℝ) :
    ‖ZH v‖ ≤ 1 := by
  by_cases hv : ZdC v = 0
  · simp [ZH, hv]
  · rw [ZH, norm_smul, Real.norm_eq_abs,
      abs_inv, Zky]
    have hnorm : ‖toWalk v‖ ≠ 0 := by
      rw [← Zky]
      exact hv
    rw [abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]
def Zk (v : I → ℝ) (x₀ : I → ℝ)
    (x : Zm I) : ℝ :=
  inner ℝ (ZH v) (x - toWalk x₀)
theorem Zgn {v : I → ℝ}
    (hv : 0 < ZdC v) (x₀ : I → ℝ) (x : Zm I) :
    Zk v x₀ x * ZdC v =
      dot (fun i ↦ x i - x₀ i) v := by
  calc
    Zk v x₀ x * ZdC v =
        inner ℝ (toWalk v) (x - toWalk x₀) := by
      rw [Zk, ZH, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hv.ne']
    _ = inner ℝ (toWalk v) (toWalk (fun i ↦ x i - x₀ i)) := by
      congr 1
    _ = dot (fun i ↦ x i - x₀ i) v :=
      (ZlY _ _).symm
def ZS [DecidableEq I] (delta : ℝ) (x : Zm I) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - delta ≤ |x i|
def ZP [DecidableEq J] (delta : ℝ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) : Finset J :=
  Finset.univ.filter fun j ↦
    0 < ZdC (v j) ∧ c j - delta ≤ |Zk (v j) x₀ x|
@[simp] theorem Zc8 [DecidableEq I]
    {delta : ℝ} {x : Zm I} {i : I} :
    i ∈ ZS delta x ↔ 1 - delta ≤ |x i| := by
  simp [ZS]
@[simp] theorem Zcu [DecidableEq J]
    {delta : ℝ} {v : J → I → ℝ} {x₀ : I → ℝ} {c : J → ℝ}
    {x : Zm I} {j : J} :
    j ∈ ZP delta v x₀ c x ↔
      0 < ZdC (v j) ∧
        c j - delta ≤ |Zk (v j) x₀ x| := by
  simp [ZP]
def ZK (omega : I → ℝ) : Zm I := toWalk omega
def ZO (K : Submodule ℝ (Zm I))
    (v : Zm I) : I → ℝ := fun i ↦ K.starProjection v i
theorem Za8
    (K : Submodule ℝ (Zm I)) (v : Zm I) (omega : I → ℝ) :
    inner ℝ v (K.starProjection (ZK omega)) =
      ∑ i, ZO K v i * omega i := by
  rw [real_inner_comm, K.inner_starProjection_left_eq_right, real_inner_comm]
  simp [PiLp.inner_apply, ZO, ZK, toWalk, mul_comm]
theorem Zd5
    (K : Submodule ℝ (Zm I)) (v : Zm I) (t : ℝ) :
    Integrable (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (ZK omega))))
      (Zi I) := by
  rw [show (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (ZK omega)))) =
      (fun omega ↦ exp (t * ∑ i, ZO K v i * omega i)) by
    funext omega
    rw [Za8]]
  exact (Zb4 I
    (ZO K v)).integrable_exp_mul t
theorem ZhM
    (K : Submodule ℝ (Zm I)) (v : Zm I) :
    ∑ i, ZO K v i ^ 2 = ‖K.starProjection v‖ ^ 2 := by
  simp [ZO, EuclideanSpace.norm_sq_eq]
theorem ZgK
    (K : Submodule ℝ (Zm I)) (v : Zm I) :
    ∑ i, ZO K v i ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [ZhM]
  nlinarith [norm_nonneg (K.starProjection v), norm_nonneg v,
    K.norm_starProjection_apply_le v]
theorem ZdV
    (K : Submodule ℝ (Zm I)) (v : Zm I) (t : ℝ) :
    ∫ omega : I → ℝ,
        exp (t * inner ℝ v (K.starProjection (ZK omega)))
      ∂(Zi I) ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  rw [show (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (ZK omega)))) =
      (fun omega ↦ exp (t * ∑ i, ZO K v i * omega i)) by
    funext omega
    rw [Za8]]
  have hmgf := (Zb4 I
    (ZO K v)).mgf_le t
  rw [mgf] at hmgf
  let q : I → ℝ≥0 := fun i ↦ ⟨ZO K v i ^ 2,
    sq_nonneg (ZO K v i)⟩
  let variance : ℝ≥0 := ∑ i, q i
  change (∫ omega : I → ℝ,
      exp (t * ∑ i, ZO K v i * omega i)
    ∂(Zi I)) ≤ exp ((variance : ℝ) * t ^ 2 / 2) at hmgf
  have hcoe : (variance : ℝ) = ∑ i, ZO K v i ^ 2 := by
    calc
      (variance : ℝ) = ↑(∑ i, q i) := rfl
      _ = ∑ i, (q i : ℝ) := by
        simp
      _ = ∑ i, ZO K v i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
  calc
    ∫ omega : I → ℝ,
        exp (t * ∑ i, ZO K v i * omega i)
      ∂(Zi I) ≤
        exp ((variance : ℝ) * t ^ 2 / 2) := hmgf
    _ ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
      apply exp_le_exp.mpr
      rw [hcoe]
      nlinarith [ZgK K v, sq_nonneg t]
theorem ZcT : MemLp id 2 ZR := by
  exact memLp_of_bounded Zeg
    measurable_id.aestronglyMeasurable 2
theorem Zdq (a : I → ℝ) (i : I) :
    MemLp (fun omega : I → ℝ ↦ a i * omega i) 2 (Zi I) := by
  exact (ZcT.comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : I ↦ ZR) i)).const_mul (a i)
theorem Zdh (a : I → ℝ) :
    ∫ omega, (∑ i, a i * omega i) ∂Zi I = 0 := by
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul]
    have hmap : (Zi I).map (fun omega : I → ℝ ↦ omega i) =
        ZR := by
      unfold Zi
      exact (measurePreserving_eval (μ := fun _ : I ↦ ZR) i).map_eq
    rw [← integral_map (μ := Zi I) (f := fun x : ℝ ↦ x)
      (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable, hmap]
    rw [Zce]
    ring
  · intro i hi
    exact (Zdq a i).integrable (by norm_num)
theorem Zdz
    (K : Submodule ℝ (Zm I)) (v : Zm I) :
    ∫ omega, inner ℝ v (K.starProjection (ZK omega))
      ∂Zi I = 0 := by
  simp_rw [Za8]
  exact Zdh (ZO K v)
theorem Zch (a : I → ℝ) :
    MemLp (fun omega : I → ℝ ↦ ∑ i, a i * omega i) 2
      (Zi I) := by
  have h := memLp_finsetSum Finset.univ
    (fun i _ ↦ Zdq a i)
  simpa only [Finset.sum_apply] using h
theorem ZfE (a : I → ℝ) :
    ∫ omega, (∑ i, a i * omega i) ^ 2 ∂Zi I = ∑ i, a i ^ 2 := by
  have hvar : Var[fun omega : I → ℝ ↦ ∑ i, a i * omega i;
      Zi I] = ∑ i, a i ^ 2 := by
    have hfun : (fun omega : I → ℝ ↦ ∑ i, a i * omega i) =
        ∑ i, fun omega : I → ℝ ↦ a i * omega i := by
      funext omega
      simp
    rw [hfun]
    unfold Zi
    rw [variance_sum_pi]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [variance_const_mul]
      have hid : Var[id; ZR] = 1 := by
        rw [variance_eq_sub ZcT]
        simp only [Pi.pow_apply, id_eq, Zce]
        have hsq : (fun x : ℝ ↦ x ^ 2) =ᵐ[ZR] fun _ ↦ 1 := by
          filter_upwards [Zdm] with x hx
          rw [← sq_abs, hx]
          norm_num
        rw [integral_congr_ae hsq]
        simp
      change a i ^ 2 * Var[id; ZR] = a i ^ 2
      rw [hid, mul_one]
    · intro i
      exact ZcT.const_mul (a i)
  rw [← hvar]
  rw [variance_of_integral_eq_zero]
  · exact (Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul (measurable_pi_apply i)).aemeasurable
  · exact Zdh a
theorem Zcb
    (K : Submodule ℝ (Zm I)) (omega : I → ℝ) :
    ‖K.starProjection (ZK omega)‖ ^ 2 =
      ∑ k : Fin (Module.finrank ℝ K),
        inner ℝ ((stdOrthonormalBasis ℝ K k : K) : Zm I)
          (ZK omega) ^ 2 := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let y : K := ⟨K.starProjection (ZK omega),
    K.starProjection_apply_mem (ZK omega)⟩
  change ‖y‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq y, ← b.sum_inner_mul_inner y y]
  apply Finset.sum_congr rfl
  intro k hk
  have hproj : inner ℝ (b k) y =
      inner ℝ ((b k : K) : Zm I) (ZK omega) := by
    change inner ℝ (b k) (K.orthogonalProjectionOnto (ZK omega)) = _
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_left (b k) (ZK omega)
  have hcomm : inner ℝ y (b k) = inner ℝ (b k) y :=
    (real_inner_comm y (b k)).symm
  rw [hcomm, hproj]
  ring
theorem ZgL (K : Submodule ℝ (Zm I)) :
    ∫ omega, ‖K.starProjection (ZK omega)‖ ^ 2
      ∂Zi I = (Module.finrank ℝ K : ℝ) := by
  simp_rw [Zcb K]
  rw [integral_finsetSum]
  · have hsquare (w : Zm I) :
        ∫ omega, inner ℝ w (ZK omega) ^ 2 ∂Zi I = ‖w‖ ^ 2 := by
      simp_rw [show ∀ omega, inner ℝ w (ZK omega) =
          ∑ i, w i * omega i by
        intro omega
        simp [PiLp.inner_apply, ZK, toWalk, mul_comm]]
      rw [ZfE]
      exact (EuclideanSpace.real_norm_sq_eq w).symm
    simp_rw [hsquare]
    calc
      (∑ k : Fin (Module.finrank ℝ K),
          ‖((stdOrthonormalBasis ℝ K k : K) : Zm I)‖ ^ 2) =
          ∑ _k : Fin (Module.finrank ℝ K), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        change ‖stdOrthonormalBasis ℝ K k‖ ^ 2 = 1
        rw [OrthonormalBasis.norm_eq_one]
        norm_num
      _ = (Module.finrank ℝ K : ℝ) := by simp
  · intro k hk
    have hmem : MemLp
        (fun omega ↦ inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : Zm I) (ZK omega))
        2 (Zi I) := by
      simp_rw [show ∀ omega, inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : Zm I) (ZK omega) =
          ∑ i, (((stdOrthonormalBasis ℝ K k : K) : Zm I) i) * omega i by
        intro omega
        simp [PiLp.inner_apply, ZK, toWalk, mul_comm]]
      exact Zch _
    exact hmem.integrable_sq
variable [DecidableEq I] [DecidableEq J]
def Zab (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) : Submodule ℝ (Zm I) :=
  ZcQ (fun j ↦ ZH (v j))
    (ZS delta x) (ZP delta v x₀ c x)
def Zaf (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ) : Zm I :=
  (Zab delta v x₀ c x).starProjection (ZK omega)
def Zbo (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ) : Zm I :=
  x + gamma • Zaf delta v x₀ c x omega
theorem Zjh (delta : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : Zm I) (omega : I → ℝ) :
    Zaf delta v x₀ c x omega ∈ Zab delta v x₀ c x := by
  exact (Zab delta v x₀ c x).starProjection_apply_mem _
theorem Zcm
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ)
    {i : I} (hi : i ∈ ZS delta x) :
    Zaf delta v x₀ c x omega i = 0 := by
  exact (ZdA
    (fun j ↦ ZH (v j))
    (ZS delta x) (ZP delta v x₀ c x) _).1
      (Zjh delta v x₀ c x omega) |>.1 i hi
theorem Zcn
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ)
    {j : J} (hj : j ∈ ZP delta v x₀ c x) :
    inner ℝ (ZH (v j))
      (Zaf delta v x₀ c x omega) = 0 := by
  exact (ZdA
    (fun j ↦ ZH (v j))
    (ZS delta x) (ZP delta v x₀ c x) _).1
      (Zjh delta v x₀ c x omega) |>.2 j hj
theorem Zg6 (delta : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : Zm I) (omega : I → ℝ) :
    ‖Zaf delta v x₀ c x omega‖ ≤ ‖ZK omega‖ := by
  exact (Zab delta v x₀ c x).norm_starProjection_apply_le _
omit [DecidableEq I] in
theorem Zhm {omega : I → ℝ}
    (homega : ∀ i, |omega i| = 1) :
    ‖ZK omega‖ ^ 2 = Fintype.card I := by
  rw [ZgJ]
  simp only [ZK, toWalk, PiLp.toLp_apply]
  calc
    ∑ i, omega i ^ 2 = ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      nlinarith [sq_abs (omega i), homega i]
    _ = Fintype.card I := by simp
omit [DecidableEq I] in
theorem ZdF {omega : I → ℝ}
    (homega : ∀ i, |omega i| = 1) :
    ‖ZK omega‖ ≤ sqrt (Fintype.card I) := by
  have hsq := Zhm homega
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]
theorem ZaX
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ) (j : J) :
    Zk (v j) x₀ (Zbo delta gamma v x₀ c x omega) =
      Zk (v j) x₀ x +
        gamma * inner ℝ (ZH (v j))
          (Zaf delta v x₀ c x omega) := by
  rw [Zk, Zk, Zbo]
  have hsub : x + gamma • Zaf delta v x₀ c x omega - toWalk x₀ =
      (x - toWalk x₀) + gamma • Zaf delta v x₀ c x omega := by
    abel
  rw [hsub, inner_add_right, inner_smul_right]
def ZaJ (a : ℝ) : ℝ := exp (-a ^ 2 / 16)
def Z1 (sigma gamma : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  ZaJ a *
    exp (sigma * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * t / 2)
def Zb8 (gamma : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  Z1 1 gamma t a y + Z1 (-1) gamma t a y
def Zau (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) : ℝ :=
  ∑ j, Zb8 gamma t (c j) (Zk (v j) x₀ x)
def ZaY (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) : ℝ :=
  ‖x‖ ^ 2 - 5 * Zau gamma t v x₀ c x
omit [DecidableEq I] [DecidableEq J] in
theorem ZiL (gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    Zau gamma 0 v x₀ c (toWalk x₀) =
      2 * ∑ j, ZaJ (c j) := by
  simp [Zau, Zb8, Z1,
    Zk, ZaJ, Finset.mul_sum, two_mul]
theorem Zb2 (sigma gamma : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ Z1 sigma gamma t a y := by
  exact mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))
theorem ZkH (gamma : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ Zb8 gamma t a y :=
  add_nonneg (Zb2 _ _ _ _ _)
    (Zb2 _ _ _ _ _)
theorem ZcP
    (sigma gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) (j : J) (hsigma : sigma ^ 2 = 1) :
    ∫ omega,
        Z1 sigma gamma (t + 1) (c j)
          (Zk (v j) x₀
            (Zbo delta gamma v x₀ c x omega))
      ∂Zi I ≤
        Z1 sigma gamma t (c j)
          (Zk (v j) x₀ x) := by
  let S := Zab delta v x₀ c x
  let w := ZH (v j)
  let a := c j / 5
  let y := Zk (v j) x₀ x
  let q := sigma * a * gamma
  let base := sigma * a * y - a ^ 2 * gamma ^ 2 * t / 2 -
    a ^ 2 * gamma ^ 2 / 2
  let B := ZaJ (c j) * exp base
  have hrewrite (omega : I → ℝ) :
      Z1 sigma gamma (t + 1) (c j)
          (Zk (v j) x₀
            (Zbo delta gamma v x₀ c x omega)) =
        B * exp (q * inner ℝ w (S.starProjection (ZK omega))) := by
    rw [ZaX]
    unfold Z1
    change ZaJ (c j) * exp _ =
      (ZaJ (c j) * exp base) * exp _
    calc
      ZaJ (c j) * exp _ =
          ZaJ (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (ZK omega)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, a, y, q, S, w, Zaf]
        push_cast
        ring
      _ = (ZaJ (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (ZK omega))) := by
        ring
  simp_rw [hrewrite]
  rw [integral_const_mul]
  have hB : 0 ≤ B := mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))
  calc
    B * ∫ omega, exp (q * inner ℝ w (S.starProjection (ZK omega)))
        ∂Zi I ≤ B * exp (q ^ 2 * ‖w‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left
        (ZdV S w q) hB
    _ ≤ B * exp (q ^ 2 / 2) := by
      gcongr
      have hwSq : ‖w‖ ^ 2 ≤ 1 := by
        nlinarith [mul_self_le_mul_self (norm_nonneg w)
          (Zdg (v j))]
      nlinarith [hwSq, sq_nonneg q]
    _ = Z1 sigma gamma t (c j) y := by
      dsimp only [B, base, q, a]
      unfold Z1
      rw [mul_assoc, ← exp_add]
      congr 2
      nlinarith
theorem Zaw
    (sigma gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) (j : J) :
    Integrable (fun omega ↦
      Z1 sigma gamma (t + 1) (c j)
        (Zk (v j) x₀
          (Zbo delta gamma v x₀ c x omega)))
      (Zi I) := by
  let S := Zab delta v x₀ c x
  let w := ZH (v j)
  let q := sigma * (c j / 5) * gamma
  let base := sigma * (c j / 5) * Zk (v j) x₀ x -
    (c j / 5) ^ 2 * gamma ^ 2 * t / 2 -
    (c j / 5) ^ 2 * gamma ^ 2 / 2
  let B := ZaJ (c j) * exp base
  have heq : (fun omega ↦
      Z1 sigma gamma (t + 1) (c j)
        (Zk (v j) x₀
          (Zbo delta gamma v x₀ c x omega))) =
      (fun omega ↦ B * exp (q * inner ℝ w
        (S.starProjection (ZK omega)))) := by
    funext omega
    rw [ZaX]
    unfold Z1
    change ZaJ (c j) * exp _ =
      (ZaJ (c j) * exp base) * exp _
    calc
      ZaJ (c j) * exp _ =
          ZaJ (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (ZK omega)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, q, S, w, Zaf]
        push_cast
        ring
      _ = (ZaJ (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (ZK omega))) := by
        ring
  rw [heq]
  exact (Zd5 S w q).const_mul B
theorem Zhn
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) (j : J) :
    ∫ omega,
        Zb8 gamma (t + 1) (c j)
          (Zk (v j) x₀
            (Zbo delta gamma v x₀ c x omega))
      ∂Zi I ≤
        Zb8 gamma t (c j)
          (Zk (v j) x₀ x) := by
  unfold Zb8
  rw [integral_add]
  · exact add_le_add
      (ZcP 1 gamma delta t v x₀ c x j (by norm_num))
      (ZcP (-1) gamma delta t v x₀ c x j (by norm_num))
  · exact Zaw 1 gamma delta t v x₀ c x j
  · exact Zaw (-1) gamma delta t v x₀ c x j
theorem Zcz
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    Integrable (fun omega ↦ Zau gamma (t + 1) v x₀ c
      (Zbo delta gamma v x₀ c x omega)) (Zi I) := by
  unfold Zau
  exact integrable_finsetSum Finset.univ fun j hj ↦
    Zaw 1 gamma delta t v x₀ c x j |>.add
      (Zaw (-1) gamma delta t v x₀ c x j)
theorem Ze6
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    ∫ omega, Zau gamma (t + 1) v x₀ c
        (Zbo delta gamma v x₀ c x omega)
      ∂Zi I ≤ Zau gamma t v x₀ c x := by
  unfold Zau
  rw [integral_finsetSum]
  · exact Finset.sum_le_sum fun j _ ↦
      Zhn gamma delta t v x₀ c x j
  · intro j _
    exact (Zaw 1 gamma delta t v x₀ c x j).add
      (Zaw (-1) gamma delta t v x₀ c x j)
omit [DecidableEq I] in
theorem Zcc
    (K : Submodule ℝ (Zm I)) (v : Zm I) :
    Integrable (fun omega ↦ inner ℝ v (K.starProjection (ZK omega)))
      (Zi I) := by
  simp_rw [Za8]
  exact (Zch (ZO K v)).integrable
    (by norm_num)
omit [DecidableEq I] in
theorem Zc9
    (K : Submodule ℝ (Zm I)) :
    Integrable (fun omega ↦ ‖K.starProjection (ZK omega)‖ ^ 2)
      (Zi I) := by
  simp_rw [Zcb K]
  exact integrable_finsetSum Finset.univ fun k hk ↦
    ((Zch
      (fun i ↦ (((stdOrthonormalBasis ℝ K k : K) : Zm I) i))).integrable_sq.congr
        (Filter.Eventually.of_forall fun omega ↦ by
          simp [PiLp.inner_apply, ZK, toWalk, mul_comm]))
theorem ZjA
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ) :
    ‖Zbo delta gamma v x₀ c x omega‖ ^ 2 = ‖x‖ ^ 2 +
      2 * gamma * inner ℝ x (Zaf delta v x₀ c x omega) +
      gamma ^ 2 * ‖Zaf delta v x₀ c x omega‖ ^ 2 := by
  rw [Zbo, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, inner_smul_right]
  rw [mul_pow, sq_abs]
  ring
theorem ZiM
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) :
    ∫ omega, ‖Zbo delta gamma v x₀ c x omega‖ ^ 2
      ∂Zi I = ‖x‖ ^ 2 +
        gamma ^ 2 * Module.finrank ℝ (Zab delta v x₀ c x) := by
  simp_rw [ZjA]
  have hconst : Integrable (fun _omega : I → ℝ ↦ ‖x‖ ^ 2)
      (Zi I) := integrable_const _
  have hlinear : Integrable (fun omega : I → ℝ ↦
      2 * gamma * inner ℝ x (Zaf delta v x₀ c x omega))
      (Zi I) :=
    (Zcc
      (Zab delta v x₀ c x) x).const_mul (2 * gamma)
  have hquadratic : Integrable (fun omega : I → ℝ ↦
      gamma ^ 2 * ‖Zaf delta v x₀ c x omega‖ ^ 2)
      (Zi I) :=
    (Zc9
      (Zab delta v x₀ c x)).const_mul (gamma ^ 2)
  have hzero : ∫ omega,
      inner ℝ x (Zaf delta v x₀ c x omega)
        ∂Zi I = 0 := by
    exact Zdz
      (Zab delta v x₀ c x) x
  have hsquare : ∫ omega,
      ‖Zaf delta v x₀ c x omega‖ ^ 2
        ∂Zi I =
        (Module.finrank ℝ (Zab delta v x₀ c x) : ℝ) := by
    exact ZgL (Zab delta v x₀ c x)
  have hmeasure : (Zi I).real Set.univ = 1 := by
    rw [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_const, integral_const_mul,
    hzero, mul_zero, integral_const_mul, hsquare]
      rw [hmeasure]
      simp only [add_zero]
      ring
    · exact hconst
    · exact hlinear
  · exact hconst.add hlinear
  · exact hquadratic
theorem Zey
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) :
    Integrable (fun omega ↦ ‖Zbo delta gamma v x₀ c x omega‖ ^ 2)
      (Zi I) := by
  simp_rw [ZjA]
  exact (integrable_const _).add
    ((Zcc
      (Zab delta v x₀ c x) x).const_mul (2 * gamma)) |>.add
        ((Zc9
          (Zab delta v x₀ c x)).const_mul (gamma ^ 2))
theorem ZiN
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    Integrable (fun omega ↦ ZaY gamma (t + 1) v x₀ c
      (Zbo delta gamma v x₀ c x omega)) (Zi I) := by
  unfold ZaY
  exact (Zey gamma delta v x₀ c x).sub
    ((Zcz gamma delta t v x₀ c x).const_mul 5)
theorem Zik
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    ZaY gamma t v x₀ c x +
        gamma ^ 2 * Module.finrank ℝ (Zab delta v x₀ c x) ≤
      ∫ omega, ZaY gamma (t + 1) v x₀ c
        (Zbo delta gamma v x₀ c x omega) ∂Zi I := by
  rw [ZaY]
  simp_rw [ZaY]
  rw [integral_sub, integral_const_mul, ZiM]
  · have hp := Ze6 gamma delta t v x₀ c x
    linarith
  · exact Zey gamma delta v x₀ c x
  · exact (Zcz gamma delta t v x₀ c x).const_mul 5
omit [DecidableEq I] in
theorem ZiO :
    Zi I {omega | ¬ ∀ i, |omega i| = 1} = 0 := by
  rw [← ae_iff]
  simpa only [Set.mem_ofPred_eq, not_not] using
    (ZeF I)
theorem ZcU
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    ∃ omega : I → ℝ, (∀ i, |omega i| = 1) ∧
      ZaY gamma t v x₀ c x +
          gamma ^ 2 * Module.finrank ℝ (Zab delta v x₀ c x) ≤
        ZaY gamma (t + 1) v x₀ c
          (Zbo delta gamma v x₀ c x omega) := by
  let N : Set (I → ℝ) := {omega | ¬ ∀ i, |omega i| = 1}
  obtain ⟨omega, homegaN, homega⟩ :=
    exists_notMem_null_integral_le
      (μ := Zi I)
      (f := fun omega ↦ ZaY gamma (t + 1) v x₀ c
        (Zbo delta gamma v x₀ c x omega))
      (ZiN gamma delta t v x₀ c x)
      (show Zi I N = 0 by exact ZiO)
  refine ⟨omega, ?_, (Zik gamma delta t v x₀ c x).trans homega⟩
  simpa only [N, Set.mem_ofPred_eq, not_not] using homegaN
end Xq.EdgeWalk
end
section
open Real Set
open scoped BigOperators
noncomputable section
namespace Xq.EdgeWalk
open Xq.Discrepancy Xq.ProjectionWalk
universe u v
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]
def Zke (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) : I → ℝ :=
  Classical.choose (ZcU gamma delta t v x₀ c x)
theorem Zji (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    ∀ i, |Zke gamma delta t v x₀ c x i| = 1 :=
  (Classical.choose_spec
    (ZcU gamma delta t v x₀ c x)).1
theorem Zlm (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    ZaY gamma t v x₀ c x +
        gamma ^ 2 * Module.finrank ℝ (Zab delta v x₀ c x) ≤
      ZaY gamma (t + 1) v x₀ c
        (Zbo delta gamma v x₀ c x
          (Zke gamma delta t v x₀ c x)) :=
  (Classical.choose_spec
    (ZcU gamma delta t v x₀ c x)).2
def Zaz (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) : ℕ → Zm I
  | 0 => toWalk x₀
  | t + 1 => Zbo delta gamma v x₀ c (Zaz delta gamma v x₀ c t)
      (Zke gamma delta t v x₀ c (Zaz delta gamma v x₀ c t))
@[simp] theorem Zmr (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    Zaz delta gamma v x₀ c 0 = toWalk x₀ := rfl
@[simp] theorem Zgc (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    Zaz delta gamma v x₀ c (t + 1) =
      Zbo delta gamma v x₀ c (Zaz delta gamma v x₀ c t)
        (Zke gamma delta t v x₀ c (Zaz delta gamma v x₀ c t)) := rfl
theorem ZkI (delta gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (t : ℕ) :
    ZaY gamma t v x₀ c (Zaz delta gamma v x₀ c t) +
        gamma ^ 2 * Module.finrank ℝ
          (Zab delta v x₀ c (Zaz delta gamma v x₀ c t)) ≤
      ZaY gamma (t + 1) v x₀ c
        (Zaz delta gamma v x₀ c (t + 1)) := by
  simpa only [Zgc] using
    Zlm gamma delta t v x₀ c (Zaz delta gamma v x₀ c t)
omit [DecidableEq I] in
theorem Zh7 (x : Zm I) (i : I) :
    |x i| ≤ ‖x‖ := by
  have hi : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [ZgJ]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]
theorem Zg7
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ)
    (homega : ∀ i, |omega i| = 1) (i : I) :
    |Zaf delta v x₀ c x omega i| ≤
      sqrt (Fintype.card I) := by
  exact (Zh7 _ i).trans
    ((Zg6 delta v x₀ c x omega).trans
      (ZdF homega))
theorem Zfs
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ)
    (homega : ∀ i, |omega i| = 1) (j : J) :
    |inner ℝ (ZH (v j))
        (Zaf delta v x₀ c x omega)| ≤
      sqrt (Fintype.card I) := by
  calc
    |inner ℝ (ZH (v j))
        (Zaf delta v x₀ c x omega)| ≤
        ‖ZH (v j)‖ *
          ‖Zaf delta v x₀ c x omega‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 1 * sqrt (Fintype.card I) := by
      gcongr
      · exact Zdg (v j)
      · exact (Zg6 delta v x₀ c x omega).trans
          (ZdF homega)
    _ = sqrt (Fintype.card I) := one_mul _
theorem Zlz
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ)
    (hx : ZdB x) (homega : ∀ i, |omega i| = 1)
    (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ZdB (Zbo delta gamma v x₀ c x omega) := by
  intro i
  by_cases hi : i ∈ ZS delta x
  · rw [Zbo]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Zcm delta v x₀ c x omega hi,
      mul_zero, add_zero]
    exact hx i
  · have hxi : |x i| < 1 - delta := by
      simpa only [Zc8, not_le] using hi
    have hinc := Zg7
      delta v x₀ c x omega homega i
    rw [Zbo]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      |x i + gamma * Zaf delta v x₀ c x omega i| ≤
          |x i| + |gamma * Zaf delta v x₀ c x omega i| :=
        abs_add_le _ _
      _ = |x i| + gamma * |Zaf delta v x₀ c x omega i| := by
        rw [abs_mul, abs_of_nonneg hgamma]
      _ ≤ |x i| + gamma * sqrt (Fintype.card I) := by gcongr
      _ ≤ 1 := by rw [← hdelta]; linarith
theorem Zgd
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ)
    (hx : ∀ j, |Zk (v j) x₀ x| ≤ c j)
    (homega : ∀ i, |omega i| = 1) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ j, |Zk (v j) x₀
      (Zbo delta gamma v x₀ c x omega)| ≤ c j := by
  intro j
  by_cases hv : ZdC (v j) = 0
  · simpa [Zk, ZH, hv] using hx j
  by_cases hj : j ∈ ZP delta v x₀ c x
  · rw [ZaX,
      Zcn delta v x₀ c x omega hj,
      mul_zero, add_zero]
    exact hx j
  · have hvpos : 0 < ZdC (v j) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
    have hy : |Zk (v j) x₀ x| < c j - delta := by
      simpa only [Zcu, hvpos, true_and, not_le] using hj
    have hinc := Zfs
      delta v x₀ c x omega homega j
    rw [ZaX]
    calc
      |Zk (v j) x₀ x + gamma *
          inner ℝ (ZH (v j))
            (Zaf delta v x₀ c x omega)| ≤
          |Zk (v j) x₀ x| +
            |gamma * inner ℝ (ZH (v j))
              (Zaf delta v x₀ c x omega)| := abs_add_le _ _
      _ = |Zk (v j) x₀ x| + gamma *
            |inner ℝ (ZH (v j))
              (Zaf delta v x₀ c x omega)| := by
        rw [abs_mul, abs_of_nonneg hgamma]
      _ ≤ |Zk (v j) x₀ x| +
            gamma * sqrt (Fintype.card I) := by gcongr
      _ ≤ c j := by rw [← hdelta]; linarith
theorem Zj9
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hx₀ : ZdB x₀) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ t, ZdB (Zaz delta gamma v x₀ c t) := by
  intro t
  induction t with
  | zero => simpa [Zaz] using hx₀
  | succ t ht =>
      rw [Zgc]
      exact Zlz delta gamma v x₀ c _ _ ht
        (Zji gamma delta t v x₀ c _) hgamma hdelta
theorem Zge
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (hgamma : 0 ≤ gamma)
    (hdelta : delta = gamma * sqrt (Fintype.card I)) :
    ∀ t j, |Zk (v j) x₀
      (Zaz delta gamma v x₀ c t)| ≤ c j := by
  intro t
  induction t with
  | zero =>
      intro j
      simpa [Zaz, Zk] using hc j
  | succ t ht =>
      rw [Zgc]
      exact Zgd delta gamma v x₀ c _ _ ht
        (Zji gamma delta t v x₀ c _) hgamma hdelta
theorem ZgM
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ) :
    ZS delta x ⊆
      ZS delta (Zbo delta gamma v x₀ c x omega) := by
  intro i hi
  rw [Zc8]
  rw [Zbo]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Zcm delta v x₀ c x omega hi,
    mul_zero, add_zero]
  exact Zc8.mp hi
theorem Zgf
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : Zm I) (omega : I → ℝ) :
    ZP delta v x₀ c x ⊆
      ZP delta v x₀ c
        (Zbo delta gamma v x₀ c x omega) := by
  intro j hj
  rw [Zcu]
  have hj' := (Zcu.mp hj)
  refine ⟨hj'.1, ?_⟩
  rw [ZaX,
    Zcn delta v x₀ c x omega hj,
    mul_zero, add_zero]
  exact hj'.2
theorem ZgN
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    ZS delta (Zaz delta gamma v x₀ c s) ⊆
      ZS delta (Zaz delta gamma v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [Zgc]
        exact ZgM delta gamma v x₀ c _ _)
theorem Zgg
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) {s t : ℕ} (hst : s ≤ t) :
    ZP delta v x₀ c (Zaz delta gamma v x₀ c s) ⊆
      ZP delta v x₀ c (Zaz delta gamma v x₀ c t) := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by
        rw [Zgc]
        exact Zgf delta gamma v x₀ c _ _)
theorem Zft
    (gamma delta : ℝ) (t : ℕ) (a y : ℝ)
    (ha : 0 ≤ a) (_ : 0 ≤ delta) (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (t : ℝ) ≤ 5)
    (hnear : a - delta ≤ |y|) :
    1 ≤ Zb8 gamma t a y := by
  let Q : ℝ := (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2
  have hQ : Q ≤ a ^ 2 / 10 := by
    have hmul := mul_le_mul_of_nonneg_left htime
      (div_nonneg (sq_nonneg (a / 5)) (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [Q]
    nlinarith
  by_cases hlarge : 16 * delta ≤ 3 * a
  · have hprod : 16 * a * delta ≤ 3 * a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge ha]
    by_cases hy : 0 ≤ y
    · have hay : a - delta ≤ y := by simpa [abs_of_nonneg hy] using hnear
      have haymul : a * (a - delta) ≤ a * y :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + a / 5 * y - Q := by
        nlinarith
      have hone : 1 ≤ Z1 1 gamma t a y := by
        rw [Z1, ZaJ, ← exp_add]
        have heq : -a ^ 2 / 16 +
            (1 * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + a / 5 * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_right
        (Zb2 (-1) gamma t a y))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hay : a - delta ≤ -y := by simpa [abs_of_nonpos hy'] using hnear
      have haymul : a * (a - delta) ≤ a * (-y) :=
        mul_le_mul_of_nonneg_left hay ha
      have hexponent :
          0 ≤ -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
        nlinarith
      have hone : 1 ≤ Z1 (-1) gamma t a y := by
        rw [Z1, ZaJ, ← exp_add]
        have heq : -a ^ 2 / 16 +
            ((-1) * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * (t : ℝ) / 2) =
            -a ^ 2 / 16 + (-1) * (a / 5) * y - Q := by
          dsimp only [Q]
          ring
        rw [heq]
        simpa only [exp_zero] using exp_le_exp.mpr hexponent
      exact hone.trans (le_add_of_nonneg_left
        (Zb2 1 gamma t a y))
  · have haUpper : a < 4 / 3 := by
      have : 3 * a < 16 * delta := lt_of_not_ge hlarge
      nlinarith
    have haSq : 13 * a ^ 2 / 80 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a - 4 / 3)]
    have hbase : -1 / 2 ≤ -a ^ 2 / 16 - Q := by
      nlinarith
    let z : ℝ := a / 5 * y
    let base : ℝ := -a ^ 2 / 16 - Q
    have hsum : 1 ≤ (1 + (base + z)) + (1 + (base - z)) := by
      dsimp only [base]
      nlinarith
    calc
      1 ≤ (1 + (base + z)) + (1 + (base - z)) := hsum
      _ ≤ exp (base + z) + exp (base - z) :=
        add_le_add (by simpa [add_comm] using add_one_le_exp (base + z))
          (by simpa [add_comm] using add_one_le_exp (base - z))
      _ = Zb8 gamma t a y := by
        unfold Zb8 Z1 ZaJ
        rw [← exp_add, ← exp_add]
        dsimp only [base, z, Q]
        congr 1 <;> ring_nf
theorem Zk1
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (t : ℕ) :
    ZaY gamma 0 v x₀ c (toWalk x₀) +
        gamma ^ 2 * ∑ s ∈ Finset.range t,
          (Module.finrank ℝ
            (Zab delta v x₀ c (Zaz delta gamma v x₀ c s)) : ℝ) ≤
      ZaY gamma t v x₀ c (Zaz delta gamma v x₀ c t) := by
  induction t with
  | zero => simp
  | succ t ht =>
      rw [Finset.sum_range_succ]
      calc
        ZaY gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
            ((∑ s ∈ Finset.range t,
              (Module.finrank ℝ (Zab delta v x₀ c
                (Zaz delta gamma v x₀ c s)) : ℝ)) +
              (Module.finrank ℝ (Zab delta v x₀ c
                (Zaz delta gamma v x₀ c t)) : ℝ)) =
            (ZaY gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
              ∑ s ∈ Finset.range t,
                (Module.finrank ℝ (Zab delta v x₀ c
                  (Zaz delta gamma v x₀ c s)) : ℝ)) +
              gamma ^ 2 * (Module.finrank ℝ (Zab delta v x₀ c
                (Zaz delta gamma v x₀ c t)) : ℝ) := by ring
        _ ≤ ZaY gamma t v x₀ c (Zaz delta gamma v x₀ c t) +
              gamma ^ 2 * (Module.finrank ℝ (Zab delta v x₀ c
                (Zaz delta gamma v x₀ c t)) : ℝ) :=
          add_le_add ht (le_refl _)
        _ ≤ ZaY gamma (t + 1) v x₀ c
              (Zaz delta gamma v x₀ c (t + 1)) :=
          ZkI delta gamma v x₀ c t
theorem Zil
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : Zm I) :
    Fintype.card I ≤
      Module.finrank ℝ (Zab delta v x₀ c x) +
        (ZS delta x).card +
        (ZP delta v x₀ c x).card := by
  have h := ZgQ
    (fun j ↦ ZH (v j))
    (ZS delta x) (ZP delta v x₀ c x)
  change Fintype.card I -
      ((ZS delta x).card +
        (ZP delta v x₀ c x).card) ≤
    Module.finrank ℝ (Zab delta v x₀ c x) at h
  omega
omit [DecidableEq I] in
theorem Ze7
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ) (x : Zm I)
    (hc : ∀ j, 0 ≤ c j) (hdelta : 0 ≤ delta)
    (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (t : ℝ) ≤ 5) :
    ((ZP delta v x₀ c x).card : ℝ) ≤
      Zau gamma t v x₀ c x := by
  let A := ZP delta v x₀ c x
  calc
    (A.card : ℝ) = ∑ _j ∈ A, (1 : ℝ) := by simp [A]
    _ ≤ ∑ j ∈ A,
        Zb8 gamma t (c j) (Zk (v j) x₀ x) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Zft gamma delta t (c j)
        (Zk (v j) x₀ x) (hc j) hdelta hdeltaSmall htime
        ((Zcu.mp hj).2)
    _ ≤ ∑ j,
        Zb8 gamma t (c j) (Zk (v j) x₀ x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun j hj₁ hj₂ ↦ ZkH gamma t (c j)
          (Zk (v j) x₀ x))
    _ = Zau gamma t v x₀ c x := rfl
omit [DecidableEq I] in
theorem ZiP (x : Zm I) (hx : ZdB x) :
    ‖x‖ ^ 2 ≤ Fintype.card I := by
  rw [ZgJ]
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsq := mul_self_le_mul_self (abs_nonneg (x i)) (hx i)
      nlinarith [sq_abs (x i)]
    _ = Fintype.card I := by simp
theorem ZjO
    (delta gamma : ℝ) (T : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : ZdB x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (hgamma : 0 ≤ gamma)
    (hdeltaEq : delta = gamma * sqrt (Fintype.card I))
    (hdelta : 0 ≤ delta) (hdeltaSmall : delta ≤ 1 / 4)
    (htime : gamma ^ 2 * (T : ℝ) = 5) :
    Fintype.card I ≤ 2 *
      (ZS delta (Zaz delta gamma v x₀ c T)).card := by
  let xT := Zaz delta gamma v x₀ c T
  let C := (ZS delta xT).card
  let D := (ZP delta v x₀ c xT).card
  let N : ℝ := Fintype.card I
  by_contra hhalf
  have hClt : 2 * C < Fintype.card I := by
    exact Nat.lt_of_not_ge hhalf
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le (2 * C)) hClt)
  have hrank (s : ℕ) (hs : s ∈ Finset.range T) :
      N - C - D ≤
        (Module.finrank ℝ
          (Zab delta v x₀ c (Zaz delta gamma v x₀ c s)) : ℝ) := by
    have hsT : s ≤ T := Nat.le_of_lt (Finset.mem_range.mp hs)
    have hcoord := Finset.card_le_card
      (ZgN delta gamma v x₀ c hsT)
    have hdisc := Finset.card_le_card
      (Zgg delta gamma v x₀ c hsT)
    have hdim := Zil delta v x₀ c
      (Zaz delta gamma v x₀ c s)
    have hcoordR :
        ((ZS delta (Zaz delta gamma v x₀ c s)).card : ℝ) ≤ C := by
      exact_mod_cast hcoord
    have hdiscR :
        ((ZP delta v x₀ c
          (Zaz delta gamma v x₀ c s)).card : ℝ) ≤ D := by
      exact_mod_cast hdisc
    have hdimR : N ≤
        (Module.finrank ℝ
          (Zab delta v x₀ c (Zaz delta gamma v x₀ c s)) : ℝ) +
        (ZS delta (Zaz delta gamma v x₀ c s)).card +
        (ZP delta v x₀ c
          (Zaz delta gamma v x₀ c s)).card := by
      dsimp only [N]
      exact_mod_cast hdim
    linarith
  have hrankSum : (T : ℝ) * (N - C - D) ≤
      ∑ s ∈ Finset.range T,
        (Module.finrank ℝ
          (Zab delta v x₀ c (Zaz delta gamma v x₀ c s)) : ℝ) := by
    calc
      (T : ℝ) * (N - C - D) =
          ∑ _s ∈ Finset.range T, (N - C - D) := by
        simp
        ring
      _ ≤ _ := Finset.sum_le_sum fun s hs ↦ hrank s hs
  have hscore := Zk1 delta gamma v x₀ c T
  have hprogress :
      ZaY gamma 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) ≤
        ZaY gamma T v x₀ c xT := by
    have hmul := mul_le_mul_of_nonneg_left hrankSum (sq_nonneg gamma)
    calc
      ZaY gamma 0 v x₀ c (toWalk x₀) + 5 * (N - C - D) =
          ZaY gamma 0 v x₀ c (toWalk x₀) +
            gamma ^ 2 * ((T : ℝ) * (N - C - D)) := by
        rw [← htime]
        ring
      _ ≤ ZaY gamma 0 v x₀ c (toWalk x₀) + gamma ^ 2 *
          ∑ s ∈ Finset.range T,
            (Module.finrank ℝ (Zab delta v x₀ c
              (Zaz delta gamma v x₀ c s)) : ℝ) := by linarith
      _ ≤ ZaY gamma T v x₀ c xT := hscore
  have hD : (D : ℝ) ≤ Zau gamma T v x₀ c xT := by
    exact Ze7 gamma delta T v x₀ c xT hc
      hdelta hdeltaSmall htime.le
  have hP0 : Zau gamma 0 v x₀ c (toWalk x₀) ≤ N / 8 := by
    rw [ZiL]
    change 2 * ∑ j, exp (-(c j) ^ 2 / 16) ≤ N / 8
    linarith
  have hxTCube : ZdB xT :=
    Zj9 delta gamma v x₀ c hx₀ hgamma hdeltaEq T
  have hxTNorm : ‖xT‖ ^ 2 ≤ N :=
    ZiP xT hxTCube
  have hx₀Norm : 0 ≤ ‖toWalk x₀‖ ^ 2 := sq_nonneg _
  have hlower : -5 * (N / 8) + 5 * (N - C) ≤ ‖xT‖ ^ 2 := by
    dsimp only [xT] at hprogress hD hxTNorm ⊢
    simp only [ZaY] at hprogress
    nlinarith
  have hCltR : 2 * (C : ℝ) < N := by
    dsimp only [N]
    exact_mod_cast hClt
  nlinarith
omit [DecidableEq I] in
theorem ZjP (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ q : ℕ, 0 < q ∧
      let gamma : ℝ := 1 / (q : ℝ)
      let delta : ℝ := gamma * sqrt (Fintype.card I)
      let T : ℕ := 5 * q ^ 2
      0 ≤ gamma ∧ 0 ≤ delta ∧ delta ≤ 1 / 4 ∧ delta ≤ epsilon ∧
        gamma ^ 2 * (T : ℝ) = 5 := by
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max 1 (max (4 * sqrt (Fintype.card I))
      (sqrt (Fintype.card I) / epsilon)))
  have hqOne : (1 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqposR : (0 : ℝ) < q := lt_trans (by norm_num) hqOne
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqFour : 4 * sqrt (Fintype.card I) < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_max_right 1 _)) hq
  have hqEpsilon : sqrt (Fintype.card I) / epsilon < (q : ℝ) := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _)
      (le_max_right _ _)) hq
  refine ⟨q, hqpos, ?_⟩
  dsimp only
  have hgamma : 0 ≤ (1 : ℝ) / q := by positivity
  have hdelta : 0 ≤ (1 / (q : ℝ)) * sqrt (Fintype.card I) := by positivity
  have hdeltaForm : (1 / (q : ℝ)) * sqrt (Fintype.card I) =
      sqrt (Fintype.card I) / q := by ring
  have hdeltaSmall : (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ 1 / 4 := by
    rw [hdeltaForm, div_le_iff₀ hqposR]
    nlinarith
  have hdeltaEpsilon :
      (1 / (q : ℝ)) * sqrt (Fintype.card I) ≤ epsilon := by
    rw [hdeltaForm, div_le_iff₀ hqposR]
    have hsqrt : sqrt (Fintype.card I) < (q : ℝ) * epsilon := by
      have := (div_lt_iff₀ hepsilon).mp hqEpsilon
      nlinarith
    linarith
  refine ⟨hgamma, hdelta, hdeltaSmall, hdeltaEpsilon, ?_⟩
  push_cast
  field_simp
omit [DecidableEq J] in
theorem ZfR
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (hx₀ : ZdB x₀) (hc : ∀ j, 0 ≤ c j)
    (hentropy : (∑ j, exp (-(c j) ^ 2 / 16)) ≤
      (Fintype.card I : ℝ) / 16)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ x : I → ℝ,
      ZdB x ∧
        Fintype.card I ≤ 2 * (Zao epsilon x).card ∧
        ∀ j, |dot (x - x₀) (v j)| ≤ c j * ZdC (v j) := by
  classical
  obtain ⟨q, hq, hgamma, hdelta, hdeltaSmall, hdeltaEpsilon, htime⟩ :=
    ZjP (I := I) epsilon hepsilon
  let gamma : ℝ := 1 / (q : ℝ)
  let delta : ℝ := gamma * sqrt (Fintype.card I)
  let T : ℕ := 5 * q ^ 2
  let xT : Zm I := Zaz delta gamma v x₀ c T
  have hgamma' : 0 ≤ gamma := hgamma
  have hdelta' : 0 ≤ delta := hdelta
  have hdeltaSmall' : delta ≤ 1 / 4 := hdeltaSmall
  have hdeltaEpsilon' : delta ≤ epsilon := hdeltaEpsilon
  have htime' : gamma ^ 2 * (T : ℝ) = 5 := htime
  have hhalf : Fintype.card I ≤
      2 * (ZS delta xT).card := by
    exact ZjO delta gamma T v x₀ c hx₀ hc hentropy
      hgamma' rfl hdelta' hdeltaSmall' htime'
  have hxTCube : ZdB xT :=
    Zj9 delta gamma v x₀ c hx₀ hgamma' rfl T
  have hnormalized : ∀ j,
      |Zk (v j) x₀ xT| ≤ c j :=
    Zge delta gamma v x₀ c hc hgamma' rfl T
  let x : I → ℝ := fun i ↦ xT i
  refine ⟨x, hxTCube, ?_, ?_⟩
  · have hsubset : ZS delta xT ⊆
        Zao epsilon x := by
      intro i hi
      rw [Zdp]
      have hi' := Zc8.mp hi
      dsimp only [x]
      linarith
    exact hhalf.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset))
  · intro j
    by_cases hv : ZdC (v j) = 0
    · rw [Zhf (x - x₀) (v j) hv, hv]
      simp
    · have hvpos : 0 < ZdC (v j) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
      have hscale := Zgn hvpos x₀ xT
      have hnormNonneg : 0 ≤ ZdC (v j) := Real.sqrt_nonneg _
      change |dot (fun i ↦ xT i - x₀ i) (v j)| ≤ c j * ZdC (v j)
      rw [← hscale, abs_mul, abs_of_nonneg hnormNonneg]
      exact mul_le_mul_of_nonneg_right (hnormalized j) hnormNonneg
omit [DecidableEq J] in
theorem ZfH (I : Type u) (J : Type v)
    [Fintype I] [Fintype J] [DecidableEq I] :
    Xq.Discrepancy.Zbz I J := by
  let : DecidableEq J := Classical.decEq J
  intro v x₀ c hx₀ hc hentropy
  apply Zgb v x₀ c
  intro epsilon hepsilon
  exact ZfR v x₀ c hx₀ hc hentropy epsilon hepsilon
end Xq.EdgeWalk
end
section
namespace Xq
open scoped BigOperators
noncomputable section
structure Zv (n : ℕ) where
  C : Finset ℕ
  Se : Finset ℕ
  So : Finset ℕ
  cover : C ∪ Se ∪ So = Finset.Icc 1 (2 * n)
  disjoint_C_Se : Disjoint C Se
  disjoint_C_So : Disjoint C So
  disjoint_Se_So : Disjoint Se So
  epsC : ℕ → ℝ
  epsE : ℕ → ℝ
  epsO : ℕ → ℝ
  epsC_isSign : ∀ k ∈ C, epsC k = 1 ∨ epsC k = -1
  epsE_isSign : ∀ k ∈ Se, epsE k = 1 ∨ epsE k = -1
  epsO_isSign : ∀ k ∈ So, epsO k = 1 ∨ epsO k = -1
def Zv.Za3 {n : ℕ} (D : Zv n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then D.epsE k
  else D.epsO k
def Zv.Za4 {n : ℕ} (D : Zv n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then -D.epsE k
  else -D.epsO k
def Zv.coeff {n : ℕ} (D : Zv n) :
    Fin (4 * n + 1) → ℂ := fun j ↦
  if (j : ℕ) < 2 * n then D.Za4 (2 * n - j)
  else if (j : ℕ) = 2 * n then 1
  else D.Za3 ((j : ℕ) - 2 * n)
private theorem Zv.Zka {n : ℕ}
    (D : Zv n) : Disjoint (D.C ∪ D.Se) D.So := by
  rw [Finset.disjoint_left]
  intro k hk hko
  simp only [Finset.mem_union] at hk
  rcases hk with hkc | hke
  · exact (Finset.disjoint_left.mp D.disjoint_C_So) hkc hko
  · exact (Finset.disjoint_left.mp D.disjoint_Se_So) hke hko
private theorem Zv.Zms {n : ℕ} (D : Zv n) :
    D.C ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]
private theorem Zv.Zmh {n : ℕ} (D : Zv n) :
    D.Se ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]
private theorem Zv.Zmi {n : ℕ} (D : Zv n) :
    D.So ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]
theorem Zv.Zit {n : ℕ} (D : Zv n) :
    ∀ j, Zcw (D.coeff j) := by
  intro j
  by_cases hjlt : (j : ℕ) < 2 * n
  · have hk : 2 * n - (j : ℕ) ∈ Finset.Icc 1 (2 * n) := by
      simp only [Finset.mem_Icc]
      omega
    rw [← D.cover] at hk
    simp only [Finset.mem_union] at hk
    simp only [Zv.coeff, if_pos hjlt,
      Zv.Za4]
    by_cases hC : 2 * n - (j : ℕ) ∈ D.C
    · rw [if_pos hC]
      rcases D.epsC_isSign _ hC with h | h <;> simp [h, Zcw]
    · rw [if_neg hC]
      by_cases hE : 2 * n - (j : ℕ) ∈ D.Se
      · rw [if_pos hE]
        rcases D.epsE_isSign _ hE with h | h <;> simp [h, Zcw]
      · rw [if_neg hE]
        have hO : 2 * n - (j : ℕ) ∈ D.So := by
          rcases hk with (hC' | hE') | hO
          · exact (hC hC').elim
          · exact (hE hE').elim
          · exact hO
        rcases D.epsO_isSign _ hO with h | h <;> simp [h, Zcw]
  · by_cases hjeq : (j : ℕ) = 2 * n
    · simp [Zv.coeff, hjeq, Zcw]
    · have hjgt : 2 * n < (j : ℕ) := by omega
      have hk : (j : ℕ) - 2 * n ∈ Finset.Icc 1 (2 * n) := by
        simp only [Finset.mem_Icc]
        have hjtop : (j : ℕ) ≤ 4 * n := by omega
        omega
      rw [← D.cover] at hk
      simp only [Finset.mem_union] at hk
      simp only [Zv.coeff, if_neg hjlt, if_neg hjeq,
        Zv.Za3]
      by_cases hC : (j : ℕ) - 2 * n ∈ D.C
      · rw [if_pos hC]
        rcases D.epsC_isSign _ hC with h | h <;> simp [h, Zcw]
      · rw [if_neg hC]
        by_cases hE : (j : ℕ) - 2 * n ∈ D.Se
        · rw [if_pos hE]
          rcases D.epsE_isSign _ hE with h | h <;> simp [h, Zcw]
        · rw [if_neg hE]
          have hO : (j : ℕ) - 2 * n ∈ D.So := by
            rcases hk with (hC' | hE') | hO
            · exact (hC hC').elim
            · exact (hE hE').elim
            · exact hO
          rcases D.epsO_isSign _ hO with h | h <;> simp [h, Zcw]
private theorem Zkt {n : ℕ} (D : Zv n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.Za4 (2 * n - j) * z ^ j) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.Za4 k * z ^ (2 * n - k) := by
  classical
  apply Finset.sum_bij (fun j _ ↦ 2 * n - j)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨2 * n - k, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    congr 2
    omega
private theorem Zku {n : ℕ} (D : Zv n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.Za3 (j + 1) * z ^ (2 * n + (j + 1))) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.Za3 k * z ^ (2 * n + k) := by
  classical
  apply Finset.sum_bij (fun j _ ↦ j + 1)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl
private theorem Zv.ZjQ {n : ℕ}
    (D : Zv n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.Za3 k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) +
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) +
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, Finset.sum_union D.Zka,
    Finset.sum_union D.disjoint_C_Se]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k hk
      simp [Zv.Za3, hk]
    · apply Finset.sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [Zv.Za3, hk, hnotC]
  · apply Finset.sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [Zv.Za3, hnotC, hnotE]
private theorem Zv.ZjR {n : ℕ}
    (D : Zv n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.Za4 k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) -
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) -
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, Finset.sum_union D.Zka,
    Finset.sum_union D.disjoint_C_Se]
  simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k hk
      simp [Zv.Za4, hk]
    · apply Finset.sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [Zv.Za4, hk, hnotC]
  · apply Finset.sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [Zv.Za4, hnotC, hnotE]
private theorem Zez {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (hs : s ⊆ Finset.Icc 1 (2 * n))
    (z : ℂ) (hz : z ≠ 0) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n - k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z⁻¹ ^ k := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ 2 * n := (Finset.mem_Icc.mp (hs hk)).2
  rw [pow_sub₀ z hz hkn, inv_pow]
  ring
private theorem ZeA {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (z : ℂ) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n + k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z ^ k := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring
theorem Zv.eval_eq {n : ℕ} (D : Zv n)
    (theta : ℝ) :
    (ZhI (4 * n) D.coeff).eval (Zd theta) =
      Zd theta ^ (2 * n) *
        Zef D.C D.Se D.So D.epsC D.epsE D.epsO theta := by
  classical
  let z := Zd theta
  have hz : z ≠ 0 := Zk2 theta
  rw [ZlN]
  change (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) = _
  let term : ℕ → ℂ := fun j ↦
    if hj : j < 4 * n + 1 then D.coeff ⟨j, hj⟩ * z ^ j else 0
  have hfin :
      (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) =
        ∑ j ∈ Finset.range (4 * n + 1), term j := by
    rw [← Fin.sum_univ_eq_sum_range term (4 * n + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show term (i : ℕ) = D.coeff i * z ^ (i : ℕ) by
      simp only [term, dif_pos i.isLt]]
  rw [hfin]
  rw [show 4 * n + 1 = 2 * n + (1 + 2 * n) by omega,
    Finset.sum_range_add]
  rw [Finset.sum_range_add (fun j ↦
    term (2 * n + j)) 1 (2 * n)]
  simp only [Finset.sum_range_one, Nat.add_zero]
  have hnegative :
      (∑ j ∈ Finset.range (2 * n),
          term j) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.Za4 k * z ^ (2 * n - k) := by
    rw [← Zkt D z]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : j < 4 * n + 1 := by omega
    rw [show term j = D.coeff ⟨j, hjtop⟩ * z ^ j by
      simp only [term, dif_pos hjtop]]
    simp only [Zv.coeff, if_pos hj]
  have hcenter : term (2 * n) = z ^ (2 * n) := by
    have hjtop : 2 * n < 4 * n + 1 := by omega
    rw [show term (2 * n) = D.coeff ⟨2 * n, hjtop⟩ * z ^ (2 * n) by
      simp only [term, dif_pos hjtop]]
    simp [Zv.coeff]
  have hpositive :
      (∑ j ∈ Finset.range (2 * n),
          term (2 * n + (1 + j))) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.Za3 k * z ^ (2 * n + k) := by
    rw [← Zku D z]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : 2 * n + (1 + j) < 4 * n + 1 := by omega
    have hne : 2 * n + (1 + j) ≠ 2 * n := by omega
    rw [show term (2 * n + (1 + j)) =
        D.coeff ⟨2 * n + (1 + j), hjtop⟩ * z ^ (2 * n + (1 + j)) by
      simp only [term, dif_pos hjtop]]
    simp only [Zv.coeff, if_neg (by omega : ¬2 * n + (1 + j) < 2 * n),
      if_neg hne]
    congr 2 <;> omega
  rw [hnegative, hcenter, hpositive]
  rw [D.ZjR (fun k ↦ z ^ (2 * n - k)),
    D.ZjQ (fun k ↦ z ^ (2 * n + k))]
  rw [Zez D.C D.epsC D.Zms z hz,
    Zez D.Se D.epsE D.Zmh z hz,
    Zez D.So D.epsO D.Zmi z hz,
    ZeA D.C D.epsC z,
    ZeA D.Se D.epsE z,
    ZeA D.So D.epsO z]
  simp only [Zef, z]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring
def Zv.Zkb {n : ℕ} (D : Zv n)
    (dangerous : ℝ → Prop)
    (hcosUpper : ∀ theta, |Zfa D.C D.epsC theta| ≤ Real.sqrt n)
    (hevenUpper : ∀ theta, |Zd8 D.Se D.epsE theta| ≤ 6 * Real.sqrt n)
    (hoddUpper : ∀ theta, |Zd8 D.So D.epsO theta| ≤ 2 ^ 10 * Real.sqrt n)
    (hcosLower : ∀ theta, Zbe theta → ¬dangerous theta →
      (1 / 2 ^ 160 : ℝ) * Real.sqrt n + 1 ≤
        2 * |Zfa D.C D.epsC theta|)
    (hoddLower : ∀ theta, Zbe theta → dangerous theta →
      10 * Real.sqrt n ≤ |Zd8 D.So D.epsO theta|) :
    Zaj n where
  coeff := D.coeff
  Zit := D.Zit
  cosine := Zfa D.C D.epsC
  ZeB := Zd8 D.Se D.epsE
  oddSine := Zd8 D.So D.epsO
  dangerous := dangerous
  eval_eq := fun theta ↦ D.eval_eq theta |>.trans
    (congrArg (Zd theta ^ (2 * n) * ·)
      (Zfb
        D.C D.Se D.So D.epsC D.epsE D.epsO theta))
  cosine_upper := hcosUpper
  evenSine_upper := hevenUpper
  oddSine_upper := hoddUpper
  cosine_lower_off_dangerous := hcosLower
  oddSine_lower_on_dangerous := hoddLower
def Zmt (n : ℕ) : Finset ℕ :=
  (Finset.range n).image Xq.Rounding.Zl
@[simp] theorem Zlq {n k : ℕ} :
    k ∈ Zmt n ↔ ∃ j < n, k = 2 * j + 1 := by
  simp [Zmt, Xq.Rounding.Zl, eq_comm]
private theorem Zld {n t : ℕ}
    (hblock : 2 * Zt t + 2 ^ t ≤ n + 1) :
    ZlA t ∪ ZlB n t =
      (Finset.Icc 1 n).image (fun j ↦ 2 * j) := by
  classical
  ext k
  simp only [Finset.mem_union, ZkM, ZkN, Finset.mem_image,
    Finset.mem_Icc]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨j, ?_, rfl⟩
      have hjrange := ZdJ hblock hj
      simp only [Finset.mem_range] at hjrange
      have hjpos : 1 ≤ j := by
        rw [ZaA] at hj
        rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · have hT : 0 < Zt t := by simp [Zt]
          omega
        · have hT : 0 < Zt t := by simp [Zt]
          omega
      exact ⟨hjpos, by omega⟩
    · have hj' := (Zd7 n t j).mp hj
      exact ⟨j, ⟨hj'.1, hj'.2.1⟩, rfl⟩
  · rintro ⟨j, ⟨hjpos, hjn⟩, rfl⟩
    by_cases hjC : j ∈ Zby t
    · exact Or.inl ⟨j, hjC, rfl⟩
    · exact Or.inr ⟨j, (Zd7 n t j).mpr ⟨hjpos, hjn, hjC⟩, rfl⟩
private theorem ZlO {n t : ℕ}
    (hblock : 2 * Zt t + 2 ^ t ≤ n + 1) :
    ZlA t ∪ ZlB n t ∪ Zmt n = Finset.Icc 1 (2 * n) := by
  classical
  rw [Zld hblock]
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Zlq]
  constructor
  · rintro (⟨j, ⟨hjpos, hjn⟩, rfl⟩ | ⟨j, hjn, rfl⟩)
    · omega
    · omega
  · intro hk
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · left
      refine ⟨j, ?_, hj.symm⟩
      omega
    · right
      exact ⟨j, by omega, hj⟩
private theorem ZkJ (n t : ℕ) :
    Disjoint (ZlA t) (Zmt n) := by
  rw [Finset.disjoint_left]
  intro k hkC hkO
  rw [ZkM] at hkC
  rw [Zlq] at hkO
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkO
  omega
private theorem ZkK (n t : ℕ) :
    Disjoint (ZlB n t) (Zmt n) := by
  rw [Finset.disjoint_left]
  intro k hkE hkO
  rw [ZkN] at hkE
  rw [Zlq] at hkO
  obtain ⟨a, ha, rfl⟩ := hkE
  obtain ⟨b, hb, hab⟩ := hkO
  omega
def ZbC (t k : ℕ) : ℝ :=
  ((Zn t).coeff (k / 2)).re
def ZbX (n t u k : ℕ) : ℝ :=
  ((ZF n t u).coeff (k / 2)).re
def Zcd (eps : ℕ → ℝ) (k : ℕ) : ℝ :=
  eps (k / 2)
private theorem ZhN {t k : ℕ} (hk : k ∈ ZlA t) :
    ZbC t k = 1 ∨ ZbC t k = -1 := by
  rw [ZkM] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [ZbC, hdiv]
  rw [ZaA] at hj
  rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [ZaK t a ha]
    rcases Zac ha with h | h <;>
      simp [h]
  · rw [Zav t a ha]
    rcases Zad ha with h | h <;>
      simp [h]
private theorem Zim {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ ZlB n t) :
    ZbX n t u k = 1 ∨ ZbX n t u k = -1 := by
  rw [ZkN] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [ZbX, hdiv]
  rcases ZaD hprefix hj with h | h <;>
    simp [h]
private theorem ZiQ {n k : ℕ} {eps : ℕ → ℝ}
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (hk : k ∈ Zmt n) :
    Zcd eps k = 1 ∨ Zcd eps k = -1 := by
  rw [Zlq] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simpa [Zcd, hdiv] using heps j
def ZjS (n t u : ℕ) (eps : ℕ → ℝ)
    (hblock : 2 * Zt t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) : Zv n where
  C := ZlA t
  Se := ZlB n t
  So := Zmt n
  cover := ZlO hblock
  disjoint_C_Se := Zkf n t
  disjoint_C_So := ZkJ n t
  disjoint_Se_So := ZkK n t
  epsC := ZbC t
  epsE := ZbX n t u
  epsO := Zcd eps
  epsC_isSign := fun _ hk ↦ ZhN hk
  epsE_isSign := fun _ hk ↦ Zim hprefix hk
  epsO_isSign := fun _ hk ↦ ZiQ heps hk
private theorem ZfF (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (theta : ℝ) :
    (p.eval (Zd theta)).re =
      ∑ k ∈ p.support, (p.coeff k).re * Real.cos (k * theta) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.reLm (∑ k ∈ p.support, p.coeff k * Zd theta ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hre : (Zd theta ^ k).re = Real.cos (k * theta) := by
    have h := congrArg Complex.re (Xq.ZdG theta k)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change (p.coeff k * Zd theta ^ k).re = _
  rw [Complex.mul_re, hreal k hk, zero_mul, sub_zero, hre]
private theorem Zgh (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (theta : ℝ) :
    (p.eval (Zd theta)).im =
      ∑ k ∈ p.support, (p.coeff k).re * Real.sin (k * theta) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.imLm (∑ k ∈ p.support, p.coeff k * Zd theta ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have him : (Zd theta ^ k).im = Real.sin (k * theta) := by
    have h := congrArg Complex.im (Xq.ZdG theta k)
    simpa only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      mul_one, add_zero, zero_add] using h
  change (p.coeff k * Zd theta ^ k).im = _
  rw [Complex.mul_im, hreal k hk, zero_mul, add_zero, him]
private theorem Zcq {t k : ℕ}
    (hk : k ∈ (Zn t).support) :
    ((Zn t).coeff k).im = 0 := by
  rw [Zax] at hk
  rw [ZaA] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [ZaK t j hj]
    rcases Zac hj with h | h <;> simp [h]
  · rw [Zav t j hj]
    rcases Zad hj with h | h <;> simp [h]
theorem Zd6 (t : ℕ) (theta : ℝ) :
    Zfa (ZlA t) (ZbC t) theta =
      Zo t theta := by
  classical
  rw [Zfa, ZlA, Finset.sum_image]
  · rw [Zo]
    rw [ZfF
      (Zn t) (fun k hk ↦ Zcq hk)]
    rw [Zax]
    apply Finset.sum_congr rfl
    intro j hj
    have hdiv : 2 * j / 2 = j := by omega
    simp only [ZbC, hdiv]
    congr 2
    push_cast
    ring
  · intro a ha b hb hab
    dsimp only at hab
    omega
private theorem ZcS {n t u : ℕ} :
    (ZF n t u).coeff 0 = 1 := by
  have hzero : 0 ∉ Zby t := by
    rw [ZaA]
    push Not
    constructor
    · intro j hj
      have hT : 0 < Zt t := by simp [Zt]
      omega
    · intro j hj
      have hT : 0 < Zt t := by simp [Zt]
      omega
  rw [ZF, Polynomial.coeff_sub,
    Zak, if_pos (by omega),
    ZaG t 0 hzero, sub_zero]
  have hstable := Zbp
    (a := 0) (b := u) (k := 0) (Nat.zero_le u) (by norm_num)
  simpa [rudinShapiroP] using hstable
private theorem Zdr {n t u : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * Zt t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) :
    (ZF n t u).support =
      insert 0 (ZhO n t) := by
  classical
  ext k
  simp only [Polynomial.mem_support_iff, Finset.mem_insert, ne_eq]
  constructor
  · intro hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      rw [Zd7]
      have hklt : k < n + 1 := by
        by_contra hnot
        have hlarge : n + 1 ≤ k := Nat.le_of_not_gt hnot
        have hkC : k ∉ Zby t := by
          intro hkC
          have hkrange := ZdJ hblock hkC
          simp only [Finset.mem_range] at hkrange
          omega
        apply hk
        rw [ZF, Polynomial.coeff_sub,
          Zak, if_neg (by omega),
          ZaG t k hkC,
          sub_zero]
      refine ⟨by omega, by omega, ?_⟩
      intro hkC
      exact hk (Zda hu hblock hkC)
  · rintro (rfl | hk)
    · rw [ZcS]
      norm_num
    · rcases ZaD hprefix hk with h | h <;>
        rw [h] <;> norm_num
private theorem Zg8 {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * Zt t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (hk : k ∈ (ZF n t u).support) :
    ((ZF n t u).coeff k).im = 0 := by
  rw [Zdr hu hblock hprefix] at hk
  simp only [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · simp [ZcS]
  · rcases ZaD hprefix hk with h | h <;>
      simp [h]
theorem ZiR (n t u : ℕ)
    (hu : t + 12 ≤ u) (hblock : 2 * Zt t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) (theta : ℝ) :
    Zd8 (ZlB n t) (ZbX n t u) theta =
      ZeB n t u theta := by
  classical
  rw [Zd8, ZlB, Finset.sum_image]
  · rw [ZeB]
    rw [Zgh
      (ZF n t u)
      (fun k hk ↦ Zg8 hu hblock hprefix hk)]
    rw [Zdr hu hblock hprefix]
    rw [Finset.sum_insert]
    · simp only [Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      have hdiv : 2 * j / 2 = j := by omega
      simp only [ZbX, hdiv]
      congr 2
      push_cast
      ring
    · simp [Zd7]
  · intro a ha b hb hab
    dsimp only at hab
    omega
theorem ZeZ (n : ℕ) (eps : ℕ → ℝ) (theta : ℝ) :
    Zd8 (Zmt n) (Zcd eps) theta =
      Xq.Rounding.ZL n eps theta := by
  classical
  rw [Zd8, Zmt, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have hdiv : (2 * j + 1) / 2 = j := by omega
    simp [Zcd, hdiv, Xq.Rounding.Zl]
  · intro a ha b hb hab
    simp only [Xq.Rounding.Zl] at hab
    omega
private theorem ZfS {n : ℕ} (hn : 0 < n)
    (F : Xq.OddSine.Za n)
    (alpha : (↑F.base : Type) → ℝ)
    (htarget : ∀ j < n, |Xq.OddSine.ZbJ F alpha j| ≤ 1)
    (hkernel : Xq.OddSine.ZcC F alpha)
    {G : Type} [Fintype G]
    (setup : Xq.OddSine.ZhD n G) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ theta, Xq.OddSine.ZaH F theta →
        10 * Real.sqrt n < |Xq.Rounding.ZL n eps theta|) ∧
      (∀ theta, |Xq.Rounding.ZL n eps theta| ≤
        2 ^ 10 * Real.sqrt n) := by
  classical
  obtain ⟨eps, heps, hround⟩ := Xq.OddSine.Zlv hn setup
    (Xq.OddSine.ZbJ F alpha) htarget
    (fun I _ _ ↦ Xq.EdgeWalk.ZfH I (G × Fin n))
  obtain ⟨hkernelLower, hkernelUpper⟩ :=
    Xq.OddSine.Zi2 hn F alpha hkernel
  refine ⟨eps, heps, ?_, ?_⟩
  · intro theta htheta
    have htri : |Xq.OddSine.ZaU F alpha theta| ≤
        |Xq.Rounding.ZL n eps theta| +
          |Xq.Rounding.ZL n eps theta -
            Xq.OddSine.ZaU F alpha theta| := by
      calc
        |Xq.OddSine.ZaU F alpha theta| =
            |Xq.Rounding.ZL n eps theta -
              (Xq.Rounding.ZL n eps theta -
                Xq.OddSine.ZaU F alpha theta)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have hlower := hkernelLower theta htheta
    have herror := hround theta
    change |Xq.Rounding.ZL n eps theta -
      Xq.OddSine.ZaU F alpha theta| ≤ 72 * Real.sqrt n at herror
    rw [Xq.OddSine.Zmw] at hlower
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [Real.sqrt_pos.2 hnR]
  · intro theta
    have htri := abs_add_le (Xq.OddSine.ZaU F alpha theta)
      (Xq.Rounding.ZL n eps theta -
        Xq.OddSine.ZaU F alpha theta)
    have heq : Xq.OddSine.ZaU F alpha theta +
        (Xq.Rounding.ZL n eps theta -
          Xq.OddSine.ZaU F alpha theta) =
          Xq.Rounding.ZL n eps theta := by ring
    rw [heq] at htri
    have hu := hkernelUpper theta
    have he := hround theta
    change |Xq.Rounding.ZL n eps theta -
      Xq.OddSine.ZaU F alpha theta| ≤ 72 * Real.sqrt n at he
    rw [Xq.OddSine.Zmw] at hu
    norm_num at ⊢
    nlinarith [Real.sqrt_nonneg n]
theorem Zjx {n : ℕ} (hn : 0 < n)
    (F : Xq.OddSine.Za n) {gamma : ℝ}
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (F.base.card : ℝ) ≤ gamma * n)
    (hkernel : ∀ alpha : (↑F.base : Type) → ℝ,
      Xq.Discrepancy.Zcw alpha →
        Xq.OddSine.ZcC F alpha) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ theta, Xq.OddSine.ZaH F theta →
        10 * Real.sqrt n < |Xq.Rounding.ZL n eps theta|) ∧
      (∀ theta, |Xq.Rounding.ZL n eps theta| ≤
        2 ^ 10 * Real.sqrt n) := by
  classical
  obtain ⟨alpha, halpha, htarget⟩ :
      ∃ alpha : (↑F.base : Type) → ℝ,
        Xq.Discrepancy.Zcw alpha ∧
          ∀ j < n, |Xq.OddSine.ZbJ F alpha j| ≤ 1 := by
    by_cases hbase : F.base.card = 0
    · exact Xq.OddSine.Zdw F hbase
    · have hbasePos : 0 < F.base.card := Nat.pos_of_ne_zero hbase
      have hadmissible := Xq.OddSine.ZfO
        hn F hgamma hbasePos hcard
      exact Xq.OddSine.Zjn F
        (fun _ ↦ Xq.OddSine.ZbT n F.base.card)
        hadmissible
        (fun I _ _ ↦ Xq.EdgeWalk.ZfH I (Fin n))
  obtain ⟨setup⟩ := Xq.OddSine.Zks hn
  exact ZfS hn F alpha htarget
    (hkernel alpha halpha) setup
private theorem Zh8 (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      omega
private theorem Zg9 {gamma : ℝ}
    (hgammaLower : (1 / 2 ^ 43 : ℝ) < gamma) :
    (1 / 2 ^ 160 : ℝ) < Xq.CosineConstruction.ZdM gamma := by
  have hgamma : 0 < gamma := by
    exact lt_trans (by positivity : (0 : ℝ) < 1 / 2 ^ 43) hgammaLower
  have hcube : (1 / 2 ^ 43 : ℝ) ^ 3 < gamma ^ 3 := by
    gcongr
  have hsmallSq : (1 / 2 ^ 22 : ℝ) ^ 2 < gamma := by
    have : (1 / 2 ^ 22 : ℝ) ^ 2 < (1 / 2 ^ 43 : ℝ) := by norm_num
    exact this.trans hgammaLower
  have hsqrtSq := Real.sq_sqrt hgamma.le
  have hsqrt : (1 / 2 ^ 22 : ℝ) < Real.sqrt gamma := by
    nlinarith [Real.sqrt_nonneg gamma]
  rw [Xq.CosineConstruction.ZdM]
  calc
    (1 / 2 ^ 160 : ℝ) < (1 / 2 ^ 159 : ℝ) := by norm_num
    _ = (1 / 2 ^ 8 : ℝ) * (1 / 2 ^ 43 : ℝ) ^ 3 * (1 / 2 ^ 22 : ℝ) := by
      norm_num
    _ < (1 / 2 ^ 8 : ℝ) * gamma ^ 3 * Real.sqrt gamma := by
      gcongr
theorem Zek
    {n t : ℕ} {gamma : ℝ}
    (hparam : Xq.CosineConstruction.Parameters n t gamma)
    (F : Xq.OddSine.Za n)
    (hcard : (F.base.card : ℝ) ≤ gamma * n)
    (hcosUpper : ∀ theta, |Zo t theta| ≤ Real.sqrt n)
    (hcosLower : ∀ theta, Zbe theta →
      ¬Xq.OddSine.ZaH F theta →
      Xq.CosineConstruction.ZdM gamma * Real.sqrt n ≤
        |Zo t theta|)
    (hkernel : ∀ alpha : (↑F.base : Type) → ℝ,
      Xq.Discrepancy.Zcw alpha →
        Xq.OddSine.ZcC F alpha)
    (habsorb : 1 ≤ (1 / 2 ^ 160 : ℝ) * Real.sqrt n) :
    Nonempty (Zaj n) := by
  have heven := hparam.Zjz
  have hu : t + 12 ≤ n := by
    have ht : t + 12 ≤ 2 ^ (t + 11) := by
      simpa only [Nat.reduceAdd] using Zh8 (t + 11)
    exact ht.trans heven.Zep
  have hprefix : n + 1 ≤ 2 ^ n := Zh8 n
  obtain ⟨eps, heps, hoddLower, hoddUpper⟩ :=
    Zjx hparam.n_pos F hparam.gamma_upper hcard hkernel
  let D := ZjS n t n eps heven.ZlH hprefix heps
  refine ⟨D.Zkb (Xq.OddSine.ZaH F) ?_ ?_ ?_ ?_ ?_⟩
  · intro theta
    rw [show Zfa D.C D.epsC theta = Zo t theta by
      exact Zd6 t theta]
    exact hcosUpper theta
  · intro theta
    rw [show Zd8 D.Se D.epsE theta = ZeB n t n theta by
      exact ZiR n t n hu heven.ZlH hprefix theta]
    exact ZeD heven hprefix theta
  · intro theta
    rw [show Zd8 D.So D.epsO theta =
        Xq.Rounding.ZL n eps theta by
      exact ZeZ n eps theta]
    exact hoddUpper theta
  · intro theta htheta hsafe
    rw [show Zfa D.C D.epsC theta = Zo t theta by
      exact Zd6 t theta]
    have hlower := hcosLower theta htheta hsafe
    have hdelta := Zg9 hparam.gamma_lower
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  · intro theta _htheta hdanger
    rw [show Zd8 D.So D.epsO theta =
        Xq.Rounding.ZL n eps theta by
      exact ZeZ n eps theta]
    exact (hoddLower theta hdanger).le
private theorem Zkc :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ (1 / 2 ^ 160 : ℝ) * Real.sqrt n := by
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun n : ℕ ↦ (1 / 2 ^ 160 : ℝ) * Real.sqrt n)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (Filter.eventually_ge_atTop 1)
theorem ZlJ : ZbB := by
  rw [ZbB]
  filter_upwards [Xq.CosineConstruction.ZgB,
    Filter.eventually_ge_atTop 4096, Zkc]
    with n hpackage hn habsorb
  obtain ⟨P⟩ := hpackage
  exact Zek P.parameters P.family
    P.base_card P.upper P.lower
    (Xq.OddKernelCertificate.Zlc hn P.family) habsorb
end
end Xq
end

open Filter
open scoped ExponentialSum Finset Topology
theorem bridge_main
    (H : ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    ( √n < c₁ * ‖p.eval z‖ ∧ ‖p.eval z‖ < c₂ * √n )) : type_of% @Green84.green_84 := by
  obtain ⟨c₁, c₂, h⟩ := H
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 h
  have hm : (0:ℝ) < max c₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / (2 * max c₁ 1), by positivity, Filter.eventually_atTop.2 ⟨n0 + 2, fun N hN => ?_⟩⟩
  obtain ⟨p, hdeg, hco, hz⟩ := hn0 (N - 1) (by omega)
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  refine ⟨fun m => if p.coeff (m - 1) = 1 then 1 else -1, ?_, ?_⟩
  · intro n hn
    by_cases h1 : p.coeff (n - 1) = 1 <;> simp [h1]
  · intro θ
    set z : ℂ := Complex.exp ((2 * Real.pi * θ : ℝ) * Complex.I) with hzdef
    have hzn : ‖z‖ = 1 := by
      rw [hzdef, Complex.norm_exp_ofReal_mul_I]
    have hsum : Green84.fourierSum N (fun m => if p.coeff (m - 1) = 1 then 1 else -1) θ
        = z * p.eval z := by
      have hlt : p.natDegree < N := by
        rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]; omega
      have hev : p.eval z = ∑ i ∈ Finset.range N, p.coeff i * z ^ i :=
        Polynomial.eval_eq_sum_range' hlt z
      rw [hev, Finset.mul_sum]
      unfold Green84.fourierSum
      have hr : Finset.Icc 1 N = (Finset.range N).image (fun i => i + 1) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro h; exact ⟨m - 1, by omega, by omega⟩
        · rintro ⟨i, hi, rfl⟩; omega
      rw [hr, Finset.sum_image (by intro a _ b _ h; simpa using h)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ N - 1 := by have := Finset.mem_range.1 hi; omega
      have hc : (((if p.coeff (i + 1 - 1) = 1 then (1:ℤ) else -1 : ℤ)) : ℂ) = p.coeff i := by
        simp only [Nat.add_sub_cancel]
        rcases hco i hi' with h1 | h1
        · simp [h1]
        · rw [h1]; simp
          have : (-1:ℂ) ≠ 1 := by norm_num
          simp [this]
      rw [hc]
      have he : e ((((i + 1 : ℕ)) : ℝ) * θ) = z ^ (i + 1) := by
        rw [hzdef, ← Complex.exp_nat_mul]
        unfold additiveChar
        congr 1
        push_cast
        ring
      rw [he]; ring
    rw [hsum, norm_mul, hzn, one_mul]
    have hh := (hz z hzn).1
    rw [hN1] at hh
    have hsq : √(N : ℝ) ≤ 2 * √((N : ℝ) - 1) := by
      have h1 : (1:ℝ) ≤ (N:ℝ) - 1 := by
        have : (2:ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
        linarith
      rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm,
        ← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      linarith
    have hn : 0 ≤ ‖p.eval z‖ := norm_nonneg _
    have hmax : c₁ * ‖p.eval z‖ ≤ max c₁ 1 * ‖p.eval z‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hn
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith

theorem OMA.solution : type_of% @Green84.green_84 :=
  bridge_main (Xq.Zli Xq.ZlJ)
