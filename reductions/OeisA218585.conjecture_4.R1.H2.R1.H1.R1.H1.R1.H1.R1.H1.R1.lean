import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
import Mathlib

-- Credit: @JaviSoto
/-! The nontrivial angular character on the Eisenstein lattice. H1 is an
archimedean lattice cancellation statement; H2 is the Euler factorization in
the region of absolute convergence. Removing the ramified factor at 3 gives
zero logarithmic-derivative coefficient there, as the parent requires. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
open OeisA218585 Real Filter ArithmeticFunction LSeries
open scoped Topology

/-- Holomorphic continuation of the lattice sum in each nonzero angular mode. -/
def H1 : Prop :=
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  ∀ m : ℕ, m ≠ 0 → ∃ (F : ℂ → ℂ), (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ F s) ∧
    ∀ s : ℂ, 1<s.re → F s = S m s

/-- Euler factorization into split conjugate primes and norm-square inert primes.
The six units account for the division by six; the factor at three is removed. -/
def H2 : Prop :=
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  let θ (k p : ℕ) := (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
  let phase (k n : ℕ) : ℝ :=
    let p := n.minFac
    let j := n.factorization p
    if p%3=1 then cos (j*θ k p) else if p%3=2 ∧ Even j then 1 else 0
  let a (k n : ℕ) : ℂ := ((Λ n*phase k n : ℝ):ℂ)
  let b (k n : ℕ) : ℂ := a k n/(Real.log n:ℝ)
  ∀ k : ℕ, k≠0 → ∀ s : ℂ, 1<s.re →
    (1-(-1:ℂ)^k*(3:ℂ)^(-s))*(S (6*k) s/6) = Complex.exp (2*LSeries (b k) s)

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro lattice factors k hk
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  let θ (k p : ℕ) := (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
  let phase (k n : ℕ) : ℝ :=
    let p := n.minFac
    let j := n.factorization p
    if p%3=1 then cos (j*θ k p) else if p%3=2 ∧ Even j then 1 else 0
  let a (k n : ℕ) : ℂ := ((Λ n*phase k n : ℝ):ℂ)
  let b (k n : ℕ) : ℂ := a k n/(Real.log n:ℝ)
  obtain ⟨F,an,agree⟩ := lattice (6*k) (Nat.mul_ne_zero (by decide) hk)
  let L (s : ℂ) := (1-(-1:ℂ)^k*(3:ℂ)^(-s))*(F s/6)
  let E (s : ℂ) := Complex.exp (2*LSeries (b k) s)
  have cont (s : ℂ) (hs : 1<s.re) : L s=E s := by
    dsimp only [L,E]; rw [agree s hs]; exact factors k hk s hs
  have ba (n : ℕ) : ‖a k n‖ ≤ Λ n := by
    have h : |phase k n| ≤ 1 := by dsimp [phase]; split_ifs <;> simp [abs_cos_le_one]
    simpa [a,abs_mul,abs_of_nonneg vonMangoldt_nonneg] using
      mul_le_mul_of_nonneg_left h (vonMangoldt_nonneg (n:=n))
  have bb (n : ℕ) : ‖b k n‖ ≤ 1 := by
    by_cases hn : n ≤ 1
    · interval_cases n <;> simp [b,a]
    · have pos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      change ‖a k n / ((Real.log n : ℝ) : ℂ)‖ ≤ 1
      have nlog : ‖((Real.log n:ℝ):ℂ)‖ = Real.log n := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
      rw [norm_div,nlog,div_le_one pos]
      exact (ba n).trans vonMangoldt_le_log
  have logb : LSeries.logMul (b k)=a k := by
    funext n
    by_cases hn : n≤1
    · interval_cases n <;> simp [LSeries.logMul,b,a]
    · have pos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      have nz : ((Real.log n:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pos.ne'
      simp only [LSeries.logMul,b,←Complex.natCast_log]
      field_simp
  refine ⟨L,a k,?_,fun s hs => (cont s hs) ▸ Complex.exp_ne_zero _,ba,?_,?_⟩
  · intro s hs
    have d := an s hs
    dsimp only [L]
    rw [show (fun z : ℂ => (1-(-1:ℂ)^k*(3:ℂ)^(-z))*(F z/6)) =
      (fun z : ℂ => (1-(-1:ℂ)^k*Complex.exp (Complex.log 3*(-z)))*(F z/6)) by
      funext z; rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]]
    fun_prop
  · intro p hp; simp [a,phase,θ,hp.minFac_eq,hp.factorization_self]
  · intro s hs
    have ac : abscissaOfAbsConv (b k) ≤ (1:ℝ) :=
      abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => bb n) (by simpa using hy)
    have hd := @LSeries_hasDerivAt (b k) s (ac.trans_lt (by exact_mod_cast hs))
    rw [logb] at hd
    have d := ((hd.const_mul (2:ℂ)).cexp).deriv
    have e : L =ᶠ[𝓝 s] E := by
      filter_upwards [(isOpen_lt (continuous_const (X:=ℂ)) Complex.continuous_re).mem_nhds hs] with z hz
      exact cont z hz
    rw [e.deriv_eq,cont s hs]
    dsimp only [E]
    rw [d]; field_simp [Complex.exp_ne_zero]

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
