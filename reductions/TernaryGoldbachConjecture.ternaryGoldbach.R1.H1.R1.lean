import OMAReductions.R_TernaryGoldbachConjecture_ternaryGoldbach_R1
import Mathlib

/-! Fourier extraction and proper prime powers in the large ternary Goldbach problem. -/
namespace OMA.R_TernaryGoldbachConjecture_ternaryGoldbach_R1_H1_R1

namespace GoldbachFourier
open Finset MeasureTheory
open scoped BigOperators

theorem coefficient {ι : Type*} (s : Finset ι) (k : ι → ℤ) (w : ι → ℂ) (n : ℤ) :
    fourierCoeff (T := 1) (fun x => ∑ j ∈ s, w j * fourier (k j) x) n =
      ∑ j ∈ s, if k j = n then w j else 0 := by
  classical
  let f (j : ι) (x : AddCircle (1:ℝ)) := w j * fourier (k j) x
  have intl (j : ι) : Integrable (f j) AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier (k j)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := congrFun (fourierCoeff.sum s f (fun j _ => intl j)) n
  change fourierCoeff (T := 1) (fun x => ∑ j ∈ s, f j x) n = _
  rw [show (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, f j by ext x; simp]
  rw [h, Finset.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  dsimp only [f]
  rw [fourierCoeff.const_mul, fourierCoeff_fourier]
  by_cases he : k j=n
  · simp [he]
  · simp [he]

theorem product_coeff (s : Finset ℕ) (u v z : ℕ → ℂ) (n : ℕ) :
    fourierCoeff (T := 1) (fun x =>
      (∑ a ∈ s, u a * fourier (a:ℤ) x) *
      (∑ b ∈ s, v b * fourier (b:ℤ) x) *
      (∑ c ∈ s, z c * fourier (c:ℤ) x)) n =
    ∑ t ∈ (s ×ˢ (s ×ˢ s)), if t.1+t.2.1+t.2.2 = n then u t.1*v t.2.1*z t.2.2 else 0 := by
  let g (t : ℕ × ℕ × ℕ) : ℤ := (t.1:ℤ) + t.2.1 + t.2.2
  let w (t : ℕ × ℕ × ℕ) := u t.1*v t.2.1*z t.2.2
  have expand (x : AddCircle (1:ℝ)) :
      (∑ a ∈ s, u a * fourier (a:ℤ) x) *
      (∑ b ∈ s, v b * fourier (b:ℤ) x) *
      (∑ c ∈ s, z c * fourier (c:ℤ) x) =
      ∑ t ∈ (s ×ˢ (s ×ˢ s)), w t * fourier (g t) x := by
    rw [mul_assoc, sum_mul_sum s s, sum_mul_sum s s]
    simp only [g,w, sum_product, fourier_add, mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intros
    ring
  simp_rw [expand]
  rw [coefficient]
  apply sum_congr rfl
  intro t _
  have eqv : g t = n ↔ t.1+t.2.1+t.2.2 = n := by dsimp [g]; omega
  simp [w,eqv]

open ArithmeticFunction

theorem majorant (n : ℕ) (u v z : ℕ → ℂ)
    (hu : ∀ a, ‖u a‖ ≤ vonMangoldt a) (hv : ∀ b, ‖v b‖ ≤ vonMangoldt b)
    (hz : ∀ c, ‖z c‖ ≤ vonMangoldt c) :
    ‖fourierCoeff (T := 1) (fun x =>
      (∑ a ∈ Ioc 0 n, u a * fourier (a:ℤ) x) *
      (∑ b ∈ Ioc 0 n, v b * fourier (b:ℤ) x) *
      (∑ c ∈ Ioc 0 n, z c * fourier (c:ℤ) x)) n‖ ≤
    ∑ t ∈ (((Ioc 0 n) ×ˢ (Ioc 0 n)).filter (fun t : ℕ × ℕ => t.1+t.2<n)),
      vonMangoldt t.1 * vonMangoldt t.2 * vonMangoldt (n-(t.1+t.2)) := by
  classical
  let s := Ioc 0 n
  change ‖fourierCoeff (T := 1) (fun x =>
    (∑ a ∈ s, u a * fourier (a:ℤ) x) * (∑ b ∈ s, v b * fourier (b:ℤ) x) *
    (∑ c ∈ s, z c * fourier (c:ℤ) x)) n‖ ≤ _
  rw [product_coeff]
  apply (norm_sum_le _ _).trans
  rw [sum_filter, sum_product]
  simp only [sum_product]
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  by_cases h : a+b<n
  · rw [if_pos h]
    have hc : n-(a+b) ∈ s := mem_Ioc.mpr ⟨by omega,Nat.sub_le _ _⟩
    rw [sum_eq_single_of_mem (n-(a+b)) hc]
    · rw [if_pos (by omega : a+b+(n-(a+b))=n), norm_mul,norm_mul]
      gcongr
      · exact hu a
      · exact hv b
      · exact hz _
    · intro c _ hne
      rw [if_neg (by omega : ¬ a+b+c=n), norm_zero]
  · rw [if_neg h]
    apply le_of_eq
    apply sum_eq_zero
    intro c hc
    have cp := (mem_Ioc.mp hc).1
    rw [if_neg (by omega : ¬ a+b+c=n), norm_zero]

end GoldbachFourier

open Finset ArithmeticFunction

theorem numerical (x : ℝ) (hx : 10^27 ≤ x) :
    6*x*Real.sqrt x*(Real.log x)^3 < x^2/10000 := by
  have xp : 0 < x := by linarith
  let u := x^(1/18 : ℝ)
  have up : 0 < u := Real.rpow_pos_of_pos xp _
  have e : u^18 = x := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast xp.le]
    norm_num
  have e9 : Real.sqrt x = u^9 := by
    apply (Real.sqrt_eq_iff_eq_sq xp.le (by positivity)).mpr
    rw [← e]; ring
  have six : (10^9 : ℝ) ≤ u^6 := by
    by_contra! hc
    have hh := pow_lt_pow_left₀ hc (by positivity : 0 ≤ u^6) (by decide : 3 ≠ 0)
    rw [← pow_mul] at hh
    norm_num at hh
    linarith
  have logle : Real.log x ≤ 18*u := by
    have h := Real.log_le_rpow_div xp.le (by norm_num : (0:ℝ) < 1/18)
    dsimp [u]
    linarith
  have cub := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) logle 3
  rw [e9]
  calc
    _ ≤ 6*x*u^9*(18*u)^3 := by gcongr
    _ < x^2/10000 := by
      rw [← e]
      have strict : (6*18^3*10000 : ℝ) < u^6 := by linarith
      have bigger := mul_lt_mul_of_pos_left strict (pow_pos up 30)
      linarith only [bigger]

def H1 : Prop := ∀ n : ℕ, 1 ≤ n →
  (∀ a b c : ℕ, a.Prime → b.Prime → c.Prime → a+b+c ≠ n) →
  (∑ v ∈ (((Ioc 0 n) ×ˢ (Ioc 0 n)).filter (fun v : ℕ × ℕ => v.1 + v.2 < n)),
      vonMangoldt v.1 * vonMangoldt v.2 * vonMangoldt (n - (v.1 + v.2))) ≤ 6 * n * Real.sqrt n * (Real.log n)^3

/-- The smoothed correlation lower bound, with the three exponential sums
normalized so their coefficients have magnitude at most the von Mangoldt function.
Helfgott, arXiv:1312.7748, equations (7.49)–(7.50) and the preceding arc estimates. -/
def H2 : Prop := ∀ n : ℕ, 10^27 ≤ n → Odd n →
  ∃ u v z : ℕ → ℂ, (∀ a, ‖u a‖ ≤ vonMangoldt a) ∧
    (∀ b, ‖v b‖ ≤ vonMangoldt b) ∧ (∀ c, ‖z c‖ ≤ vonMangoldt c) ∧
    (n : ℝ)^2/10000 ≤ ‖fourierCoeff (T := 1) (fun x =>
      (∑ a ∈ Ioc 0 n, u a * fourier (a:ℤ) x) *
      (∑ b ∈ Ioc 0 n, v b * fourier (b:ℤ) x) *
      (∑ c ∈ Ioc 0 n, z c * fourier (c:ℤ) x)) n‖

theorem main : H1 → H2 → OMA.R_TernaryGoldbachConjecture_ternaryGoldbach_R1.H1 := by
  intro hbad hfour n hn ho
  obtain ⟨u,v,z,hu,hv,hz,lower⟩ := hfour n hn ho
  by_contra no
  have ex (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) : a+b+c ≠ n :=
    fun eqn => no ⟨a,b,c,ha,hb,hc,eqn.symm⟩
  have upper := hbad n (by omega) ex
  have dom := GoldbachFourier.majorant n u v z hu hv hz
  have cutoff := numerical n (by exact_mod_cast hn)
  exact (not_lt_of_ge lower) ((dom.trans upper).trans_lt cutoff)
end OMA.R_TernaryGoldbachConjecture_ternaryGoldbach_R1_H1_R1
