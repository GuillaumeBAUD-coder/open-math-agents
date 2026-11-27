import FormalConjectures.Paper.Gourevitch
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# A Wilf–Zeilberger certificate for Gourevitch's series

The summand is Guillera's sheared version of Au's Wilf–Zeilberger pair
(<https://arxiv.org/html/2503.00570v1#S4.SS5>). Write `x = 2n` and `y = 2k`.
The polynomial certificate is obtained by coefficient comparison.
-/

open scoped BigOperators

namespace GourevitchWZ

def a (x y : ℂ) : ℂ := x + 3 * y + 1

def b (x y : ℂ) : ℂ := x - y - 1

def c (x y : ℂ) : ℂ := x + y + 1

def d (x y : ℂ) : ℂ := x + 2 * y + 2

def e (x y : ℂ) : ℂ := x + y + 2

def P (x y : ℂ) : ℂ :=
  (3 * x + 3 * y + 1) * (7 * x ^ 2 + 4 * x + 1 + 3 * y ^ 2 + 14 * x * y + 4 * y)

private def homogeneousQ (x y z : ℂ) : ℂ :=
  21 * x ^ 5 + (101 * y + 57) * x ^ 4 * z
    + (74 * y ^ 2 + 12 * y - 42) * x ^ 3 * z ^ 2
    + (-318 * y ^ 3 - 850 * y ^ 2 - 718 * y - 186) * x ^ 2 * z ^ 3
    + (-607 * y ^ 4 - 1796 * y ^ 3 - 1862 * y ^ 2 - 764 * y - 91) * x * z ^ 4
    + (-295 * y ^ 5 - 1007 * y ^ 4 - 1266 * y ^ 3 - 706 * y ^ 2 - 167 * y - 15) * z ^ 5

def Q (x y : ℂ) : ℂ := homogeneousQ x y 1

theorem certificate_poly (x y : ℂ) :
    (a x y) ^ 2 * (c x y) ^ 3 * (b x y) ^ 2 * Q (x + 2) y
      - 64 * x ^ 2 * (d x y + 2) ^ 2 * (e x y) ^ 3 * Q x y =
    (a x y) ^ 2 * (a x y + 2) ^ 2 * (a x y + 4) ^ 2 * (c x y) ^ 3 * P x (y + 2)
      - 64 * (b x y) ^ 2 * (d x y) ^ 2 * (d x y + 2) ^ 2 * (e x y) ^ 3 * P x y := by
  unfold a b c d e P Q homogeneousQ
  ring

noncomputable def nRatio (x y : ℂ) : ℂ :=
  (a x y) ^ 2 * (b x y + 2) ^ 2 * (c x y) ^ 3 /
    (64 * (x + 2) ^ 2 * (d x y) ^ 2 * (e x y) ^ 3)

noncomputable def kRatio (x y : ℂ) : ℂ :=
  (a x y) ^ 2 * (a x y + 2) ^ 2 * (a x y + 4) ^ 2 * (c x y) ^ 3 /
    (64 * (b x y) ^ 2 * (d x y) ^ 2 * (d x y + 2) ^ 2 * (e x y) ^ 3)

noncomputable def cert (x y : ℂ) : ℂ := x ^ 2 * Q x y / ((b x y) ^ 2 * (d x y) ^ 2)

/-- This is the product of `nRatio x y` with `cert (x+2) y` after cancellation. -/
noncomputable def certNext (x y : ℂ) : ℂ :=
  (a x y) ^ 2 * (c x y) ^ 3 * Q (x + 2) y /
     (64 * (d x y) ^ 2 * (d x y + 2) ^ 2 * (e x y) ^ 3)

theorem certificate (x y : ℂ) (hb : b x y ≠ 0) (hd : d x y ≠ 0) (hd' : d x y + 2 ≠ 0)
    (he : e x y ≠ 0) :
    certNext x y - cert x y = kRatio x y * P x (y + 2) - P x y := by
  unfold certNext cert kRatio
  field_simp
  linear_combination certificate_poly x y

def rise (z : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (z + 2 * j)

@[simp] theorem rise_zero (z : ℂ) : rise z 0 = 1 := by simp [rise]

theorem rise_succ (z : ℂ) (n : ℕ) : rise z (n + 1) = rise z n * (z + 2 * n) := by
  simp [rise, Finset.prod_range_succ]

private theorem rise_ne_zero (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    rise z n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _ hj
  have h := congrArg Complex.re hj
  have hp : 0 < z.re + 2 * (j : ℝ) := by positivity
  exact hp.ne' (by simpa [Complex.add_re, Complex.mul_re] using h)

/-- The scaled rising-factorial portion of Guillera's sheared term. -/
noncomputable def U (T : ℂ → ℂ) (n : ℕ) (y : ℂ) : ℂ :=
  T y * (1 / 64 : ℂ) ^ n *
    ((rise (3 * y + 1) n) ^ 2 * (rise (1 - y) n) ^ 2 * (rise (y + 1) n) ^ 3) /
      ((rise 2 n) ^ 2 * (rise (2 * y + 2) n) ^ 2 * (rise (y + 2) n) ^ 3)

noncomputable def G (T : ℂ → ℂ) (n : ℕ) (y : ℂ) : ℂ :=
  U T n y * P (2 * n) y

/-- Use the cancelled product to define the certificate term at all parameters. -/
noncomputable def F (T : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0, _ => 0
  | n + 1, y => U T n y * certNext (2 * n) y

@[simp] theorem F_zero (T : ℂ → ℂ) (y : ℂ) : F T 0 y = 0 := rfl

@[simp] theorem U_zero (T : ℂ → ℂ) (y : ℂ) : U T 0 y = T y := by simp [U]

noncomputable def prefactorRatio (y : ℂ) : ℂ :=
  9 * (y + 1) * (3 * y + 1) ^ 2 * (3 * y + 5) ^ 2 / (1024 * (y + 2) ^ 5)

private theorem nonzero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := by
  intro hzero
  simp [hzero] at h

private theorem d_ne {x y : ℂ} (hx : 0 ≤ x.re) (hy : 0 ≤ y.re) {r : ℝ} (hr : 0 ≤ r) :
    d x y + (r : ℂ) ≠ 0 := by
  apply nonzero_of_re_pos
  simp [d, Complex.add_re, Complex.mul_re]
  positivity

private theorem e_ne {x y : ℂ} (hx : 0 ≤ x.re) (hy : 0 ≤ y.re) {r : ℝ} (hr : 0 ≤ r) :
    e x y + (r : ℂ) ≠ 0 := by
  apply nonzero_of_re_pos
  simp [e, Complex.add_re]
  positivity

private theorem b_ne {x y : ℂ} (hx : x.im = 0) (hy : y.im ≠ 0) (r : ℝ) :
    b x y + (r : ℂ) ≠ 0 := by
  intro hz
  apply hy
  have h := congrArg Complex.im hz
  simpa [b, Complex.sub_im, Complex.add_im, hx] using h

private theorem n_add_two_ne {x : ℂ} (hx : 0 ≤ x.re) : x + 2 ≠ 0 :=
  nonzero_of_re_pos (by simp [Complex.add_re]; positivity)

theorem U_succ (T : ℂ → ℂ) (n : ℕ) {y : ℂ} (hy : 0 ≤ y.re) :
    U T (n+1) y = U T n y * nRatio (2*n) y := by
  have hx : 0 ≤ ((2 : ℂ) * n).re := by simp [Complex.mul_re]
  have ha : 3*y+1+2*n = a (2*n) y := by unfold a; ring
  have hb : 1-y+2*n = b (2*n) y + 2 := by unfold b; ring
  have hc : y+1+2*n = c (2*n) y := by unfold c; ring
  have hd : 2*y+2+2*n = d (2*n) y := by unfold d; ring
  have he : y+2+2*n = e (2*n) y := by unfold e; ring
  have hn : 2+2*(n : ℂ) = 2*n+2 := by ring
  have h₁ := rise_ne_zero 2 (by norm_num) n
  have h₂ := rise_ne_zero (2*y+2) (by simp [Complex.add_re, Complex.mul_re]; positivity) n
  have h₃ := rise_ne_zero (y+2) (by simp [Complex.add_re]; positivity) n
  have h₄ : d (2*n) y ≠ 0 := by simpa using d_ne hx hy (r := 0) le_rfl
  have h₅ : e (2*n) y ≠ 0 := by simpa using e_ne hx hy (r := 0) le_rfl
  have h₆ := n_add_two_ne hx
  simp only [U, rise_succ, ha, hb, hc, hd, he, hn, nRatio, pow_succ (1/64 : ℂ) n]
  field_simp

private theorem kRatio_zero {y : ℂ} (hy : 0 ≤ y.re) : kRatio 0 y = prefactorRatio y := by
  have h₁ : y+1 ≠ 0 := nonzero_of_re_pos (by simp [Complex.add_re]; positivity)
  have h₂ : y+2 ≠ 0 := nonzero_of_re_pos (by simp [Complex.add_re]; positivity)
  have h₃ : -(y+1) ≠ 0 := neg_ne_zero.mpr h₁
  have h₄ : 2*(y+1) ≠ 0 := mul_ne_zero (by norm_num) h₁
  have h₅ : 2*(y+2) ≠ 0 := mul_ne_zero (by norm_num) h₂
  unfold kRatio prefactorRatio
  rw [show b 0 y = -(y+1) by unfold b; ring, show d 0 y + 2 = 2*(y+2) by unfold d; ring,
    show d 0 y = 2*(y+1) by unfold d; ring, show e 0 y = y+2 by unfold e; ring]
  unfold a c
  simp only [zero_add]
  field_simp
  ring

private theorem ratio_commute (x y : ℂ) (hx : 0 ≤ x.re) (hxi : x.im = 0)
    (hy : 0 ≤ y.re) (hyi : y.im ≠ 0) :
    kRatio x y * nRatio x (y+2) = nRatio x y * kRatio (x+2) y := by
  have h₁ : d x y ≠ 0 := by simpa using d_ne hx hy (r := 0) le_rfl
  have h₂ : d x y+2 ≠ 0 := by simpa using d_ne hx hy (r := 2) (by norm_num)
  have h₃ : d x y+4 ≠ 0 := by simpa using d_ne hx hy (r := 4) (by norm_num)
  have h₄ : e x y ≠ 0 := by simpa using e_ne hx hy (r := 0) le_rfl
  have h₅ : e x y+2 ≠ 0 := by simpa using e_ne hx hy (r := 2) (by norm_num)
  have h₆ : b x y ≠ 0 := by simpa using b_ne hxi hyi 0
  have h₇ : b x y+2 ≠ 0 := by simpa using b_ne hxi hyi 2
  have h₈ := n_add_two_ne hx
  unfold kRatio nRatio
  rw [show a x (y+2) = a x y + 6 by unfold a; ring,
    show b x (y+2) + 2 = b x y by unfold b; ring,
    show c x (y+2) = c x y + 2 by unfold c; ring,
    show d x (y+2) = d x y + 4 by unfold d; ring,
    show e x (y+2) = e x y + 2 by unfold e; ring,
    show a (x+2) y = a x y + 2 by unfold a; ring,
    show b (x+2) y = b x y + 2 by unfold b; ring,
    show c (x+2) y = c x y + 2 by unfold c; ring,
    show d (x+2) y + 2 = d x y + 4 by unfold d; ring,
    show d (x+2) y = d x y + 2 by unfold d; ring,
    show e (x+2) y = e x y + 2 by unfold e; ring]
  field_simp
  ring

theorem U_shift (T : ℂ → ℂ)
    (hT : ∀ y : ℂ, 0 ≤ y.re → T (y+2) = T y * prefactorRatio y)
    (n : ℕ) {y : ℂ} (hy : 0 ≤ y.re) (hyi : y.im ≠ 0) :
    U T n (y+2) = U T n y * kRatio (2*n) y := by
  induction n with
  | zero => simpa [kRatio_zero hy] using hT y hy
  | succ n ih =>
    have hy' : 0 ≤ (y+2).re := by simp [Complex.add_re]; positivity
    have hx : 0 ≤ ((2 : ℂ) * n).re := by simp [Complex.mul_re]
    have hxi : ((2 : ℂ) * n).im = 0 := by simp [Complex.mul_im]
    rw [U_succ T n hy', U_succ T n hy, ih, mul_assoc,
      ratio_commute _ _ hx hxi hy hyi, ← mul_assoc]
    rw [Nat.cast_succ, mul_add, mul_one]

private theorem nRatio_mul_cert {x y : ℂ} (hx : 0 ≤ x.re) (hxi : x.im = 0)
    (hy : 0 ≤ y.re) (hyi : y.im ≠ 0) :
    nRatio x y * cert (x+2) y = certNext x y := by
  have h₁ : d x y ≠ 0 := by simpa using d_ne hx hy (r := 0) le_rfl
  have h₂ : d x y+2 ≠ 0 := by simpa using d_ne hx hy (r := 2) (by norm_num)
  have h₃ : e x y ≠ 0 := by simpa using e_ne hx hy (r := 0) le_rfl
  have h₄ : b x y+2 ≠ 0 := by simpa using b_ne hxi hyi 2
  have h₅ := n_add_two_ne hx
  unfold nRatio cert certNext
  rw [show b (x+2) y = b x y + 2 by unfold b; ring,
    show d (x+2) y = d x y + 2 by unfold d; ring]
  field_simp

theorem F_eq (T : ℂ → ℂ) (n : ℕ) {y : ℂ} (hy : 0 ≤ y.re) (hyi : y.im ≠ 0) :
    F T n y = U T n y * cert (2*n) y := by
  cases n with
  | zero => simp [cert]
  | succ n =>
    have hx : 0 ≤ ((2 : ℂ) * n).re := by simp [Complex.mul_re]
    have hxi : ((2 : ℂ) * n).im = 0 := by simp [Complex.mul_im]
    rw [F, U_succ T n hy, mul_assoc, Nat.cast_succ, mul_add, mul_one,
      nRatio_mul_cert hx hxi hy hyi]

theorem wz (T : ℂ → ℂ)
    (hT : ∀ y : ℂ, 0 ≤ y.re → T (y+2) = T y * prefactorRatio y)
    (n : ℕ) {y : ℂ} (hy : 0 ≤ y.re) (hyi : y.im ≠ 0) :
    F T (n+1) y - F T n y = G T n (y+2) - G T n y := by
  have hx : 0 ≤ ((2 : ℂ) * n).re := by simp [Complex.mul_re]
  have hxi : ((2 : ℂ) * n).im = 0 := by simp [Complex.mul_im]
  have hb : b (2*n) y ≠ 0 := by simpa using b_ne hxi hyi 0
  have hd : d (2*n) y ≠ 0 := by simpa using d_ne hx hy (r := 0) le_rfl
  have hd' : d (2*n) y+2 ≠ 0 := by simpa using d_ne hx hy (r := 2) (by norm_num)
  have he : e (2*n) y ≠ 0 := by simpa using e_ne hx hy (r := 0) le_rfl
  rw [F, F_eq T n hy hyi, G, G, U_shift T hT n hy hyi, mul_assoc, ← mul_sub, ← mul_sub,
    certificate _ _ hb hd hd' he]

open Filter Topology

theorem sum_periodic (T : ℂ → ℂ)
    (hT : ∀ y : ℂ, 0 ≤ y.re → T (y+2) = T y * prefactorRatio y)
    {y : ℂ} (hy : 0 ≤ y.re) (hyi : y.im ≠ 0)
    (hg₀ : Summable (fun n => G T n y)) (hg₁ : Summable (fun n => G T n (y+2)))
    (hf : Tendsto (fun n => F T n y) atTop (𝓝 0)) :
    (∑' n, G T n (y+2)) = ∑' n, G T n y := by
  have hs := (hg₁.hasSum.sub hg₀.hasSum).tendsto_sum_nat
  have heq (n : ℕ) : (∑ i ∈ Finset.range n, (G T i (y+2) - G T i y)) = F T n y := by
    simp_rw [← wz T hT _ hy hyi]
    rw [Finset.sum_range_sub (fun j => F T j y), F_zero, sub_zero]
  simp only [heq] at hs
  exact sub_eq_zero.mp (tendsto_nhds_unique hs hf)

@[simp] theorem G_at_one_zero (T : ℂ → ℂ) : G T 0 1 = 32 * T 1 := by
  simp only [G, U_zero, Nat.cast_zero, mul_zero]
  norm_num [P]
  ring

theorem G_at_one_succ (T : ℂ → ℂ) (n : ℕ) : G T (n+1) 1 = 0 := by
  have hz : rise 0 (n+1) = 0 := by
    induction n with
    | zero => simp [rise_succ]
    | succ n ih => rw [rise_succ, ih, zero_mul]
  simp [G, U, hz]

theorem tsum_at_one (T : ℂ → ℂ) : (∑' n, G T n 1) = 32 * T 1 := by
  rw [tsum_eq_single 0 (fun i hi => ?_), G_at_one_zero]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  exact G_at_one_succ T j

private theorem rise_ratio_centralBinom (n : ℕ) :
    rise 1 n / rise 2 n = (Nat.centralBinom n : ℂ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnp : (0 : ℝ) < (n : ℝ)+1 := by positivity
    have hn : (n : ℂ)+1 ≠ 0 := nonzero_of_re_pos (by simpa [Complex.add_re] using hnp)
    have hn' : 1+(n : ℂ) ≠ 0 := by simpa only [add_comm] using hn
    have h₂n : (2 : ℂ) + 2*n ≠ 0 := nonzero_of_re_pos (by simp [Complex.add_re, Complex.mul_re]; positivity)
    have hrec : (Nat.centralBinom (n+1) : ℂ) =
        2 * (2*(n:ℂ)+1) * (Nat.centralBinom n : ℂ) / ((n:ℂ)+1) := by
      apply (eq_div_iff hn).2
      rw [mul_comm _ ((n:ℂ)+1)]
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    calc
      _ = (rise 1 n / rise 2 n) * ((1+2*n)/(2+2*n)) := by
        rw [rise_succ, rise_succ, div_mul_div_comm]
      _ = _ := by
        rw [ih, hrec, pow_succ]
        field_simp [hn, hn', h₂n]
        ring

theorem G_at_zero (T : ℂ → ℂ) (hT : T 0 = 1) (n : ℕ) :
    G T n 0 = ((1 + 14 * n + 76 * n ^ 2 + 168 * n ^ 3) / (2 ^ (20 * n)) : ℂ)
      * (Nat.centralBinom n : ℂ) ^ 7 := by
  have h₂ := rise_ne_zero 2 (by norm_num) n
  have hpow : (64:ℂ)^n * ((4:ℂ)^n)^7 = (2:ℂ)^(20*n) := by
    rw [show (64:ℂ) = 2^6 by norm_num, show (4:ℂ) = 2^2 by norm_num,
      ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hp : P (2*n) 0 = 1+14*(n:ℂ)+76*(n:ℂ)^2+168*(n:ℂ)^3 := by unfold P; ring
  calc
    G T n 0 = (1/64 : ℂ)^n * (rise 1 n / rise 2 n)^7 * P (2*n) 0 := by
      simp only [G, U, hT, one_mul, mul_zero, zero_add, sub_zero]
      rw [div_pow]
      field_simp
    _ = _ := by
      rw [rise_ratio_centralBinom, hp, ← hpow]
      simp only [div_pow, one_pow]
      field_simp

private noncomputable def normalizedNext (y z : ℂ) : ℂ :=
  (2+(3*y-1)*z)^2 * (2+(y-1)*z)^3 * homogeneousQ 2 y z /
    (64 * (2+2*y*z)^2 * (2+(2*y+2)*z)^2 * (2+y*z)^3)

private theorem certNext_normalized (n : ℕ) (y : ℂ) :
    certNext (2*n) y = ((n:ℂ)+1)^3 * normalizedNext y (1 / ((n:ℂ)+1)) := by
  let s := (n:ℂ)+1
  let z := 1 / s
  have hs : s ≠ 0 := nonzero_of_re_pos (by simp [s, Complex.add_re]; positivity)
  have hsz : s*z=1 := by dsimp [z]; field_simp
  have ha : a (2*n) y = s*(2+(3*y-1)*z) := by
    unfold a
    dsimp only [s] at hsz ⊢
    linear_combination -(3*y-1) * hsz
  have hc : c (2*n) y = s*(2+(y-1)*z) := by
    unfold c
    dsimp only [s] at hsz ⊢
    linear_combination -(y-1) * hsz
  have hd : d (2*n) y = s*(2+2*y*z) := by
    unfold d
    dsimp only [s] at hsz ⊢
    linear_combination -(2*y) * hsz
  have hd' : d (2*n) y + 2 = s*(2+(2*y+2)*z) := by
    unfold d
    dsimp only [s] at hsz ⊢
    linear_combination -(2*y+2) * hsz
  have he : e (2*n) y = s*(2+y*z) := by
    unfold e
    dsimp only [s] at hsz ⊢
    linear_combination -y * hsz
  have hQ : Q (2*n+2) y = s^5 * homogeneousQ 2 y z := by
    calc
      _ = homogeneousQ (s*2) y (s*z) := by
        rw [hsz]
        unfold Q
        congr 1
        dsimp only [s]
        ring
      _ = _ := by unfold homogeneousQ; ring
  let num := (2+(3*y-1)*z)^2 * (2+(y-1)*z)^3 * homogeneousQ 2 y z
  let den := 64 * (2+2*y*z)^2 * (2+(2*y+2)*z)^2 * (2+y*z)^3
  calc
    _ = (s^7 * (s^3 * num)) / (s^7 * den) := by
      unfold certNext
      rw [ha, hc, hd', hd, he, hQ]
      congr 1 <;> (dsimp only [num, den]; ring)
    _ = _ := by
      rw [mul_div_mul_left _ _ (pow_ne_zero 7 hs), mul_div_assoc]
      rfl

private theorem continuousAt_normalizedNext (y : ℂ) :
    ContinuousAt (normalizedNext y) 0 := by
  unfold normalizedNext
  apply ContinuousAt.div (by unfold homogeneousQ; fun_prop) (by fun_prop)
  norm_num

theorem F_tendsto_zero_of_geometric (T : ℂ → ℂ) (y : ℂ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr' : r < 1)
    (hU : ∀ᶠ n : ℕ in atTop, ‖U T n y‖ ≤ C*r^n) :
    Tendsto (fun n : ℕ => F T n y) atTop (𝓝 0) := by
  have hgeometric : Tendsto (fun n : ℕ => (8*C)*((n:ℝ)^3*r^n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 3 hr hr').const_mul (8*C)
  have hvanish : Tendsto (fun n : ℕ => U T n y * ((n:ℂ)+1)^3) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hgeometric
    filter_upwards [hU, eventually_ge_atTop (1 : ℕ)] with n hn h₁
    have h₁R : (1 : ℝ) ≤ (n:ℝ) := by exact_mod_cast h₁
    have hs : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
      simpa only [Nat.cast_succ] using Complex.norm_natCast (n+1)
    rw [norm_mul, norm_pow, hs]
    calc
      ‖U T n y‖ * ((n:ℝ)+1)^3 ≤ (C*r^n) * ((n:ℝ)+1)^3 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ ≤ (C*r^n) * (2*(n:ℝ))^3 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        gcongr
        linarith
      _ = _ := by ring
  have hregular : Tendsto (fun n : ℕ => normalizedNext y (1 / ((n:ℂ)+1)))
      atTop (𝓝 (normalizedNext y 0)) :=
    (continuousAt_normalizedNext y).tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [F, certNext_normalized, ← mul_assoc, zero_mul] using hvanish.mul hregular

end GourevitchWZ

namespace GourevitchWZ

open Complex

private theorem norm_le_of_components {z w : ℂ}
    (hr : |z.re| ≤ |w.re|) (hi : |z.im| ≤ |w.im|) : ‖z‖ ≤ ‖w‖ := by
  have h₁ := (sq_le_sq₀ (abs_nonneg z.re) (abs_nonneg w.re)).mpr hr
  have h₂ := (sq_le_sq₀ (abs_nonneg z.im) (abs_nonneg w.im)).mpr hi
  rw [sq_abs, sq_abs] at h₁ h₂
  apply (sq_le_sq₀ (norm_nonneg z) (norm_nonneg w)).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith

private theorem norm_a_le (n : ℕ) {y : ℂ} (hy : 0 ≤ y.re) :
    ‖a (2 * n) y‖ ≤ (3 / 2 : ℝ) * ‖d (2 * n) y‖ := by
  have h : ‖a (2 * n) y‖ ≤ ‖((3 / 2 : ℝ) : ℂ) * d (2 * n) y‖ := by
    apply norm_le_of_components
    · simp [a, d, Complex.mul_re]
      have h₁ : 0 ≤ 2 * (n : ℝ) + 3 * y.re + 1 := by positivity
      have h₂ : 0 ≤ 2 * (n : ℝ) + 2 * y.re + 2 := by positivity
      rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · have he : (a (2 * n) y).im = (((3 / 2 : ℝ) : ℂ) * d (2 * n) y).im := by
        simp [a, d, Complex.mul_im]
        ring
      rw [he]
  simpa [norm_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)] using h

private theorem norm_c_le (n : ℕ) {y : ℂ} (hy : 0 ≤ y.re) :
    ‖c (2 * n) y‖ ≤ ‖e (2 * n) y‖ := by
  apply norm_le_of_components
  · simp [c, e, Complex.mul_re]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    linarith
  · simp [c, e, Complex.mul_im]

private theorem norm_b_add_two_le (n M : ℕ) {y : ℂ} (hM : ‖y‖ ≤ M) :
    ‖b (2 * n) y + 2‖ ≤ 2 * ((n : ℝ) + 1 + (M : ℝ)) := by
  have he : b (2 * n) y + 2 = (((2 * (n : ℝ) + 1 : ℝ)) : ℂ) - y := by
    unfold b
    push_cast
    ring
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  change ‖((2 * (n : ℝ) + 1 : ℝ) : ℂ)‖ + ‖y‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) M]

private theorem choose_ratio (n M : ℕ) :
    ((n + M).choose n : ℝ) * (((n : ℝ) + 1 + M) / ((n : ℝ) + 1)) =
      ((n + 1 + M).choose (n + 1) : ℝ) := by
  have he : (n + 1 + M).choose (n + 1) * (n + 1) =
      (n + M).choose n * (n + 1 + M) := by
    rw [Nat.choose_succ_right_eq, show n + 1 + M = n + M + 1 by omega]
    exact (Nat.choose_mul_succ_eq (n + M) n).symm
  have he' : ((n + 1 + M).choose (n + 1) : ℝ) * ((n : ℝ) + 1) =
      ((n + M).choose n : ℝ) * ((n : ℝ) + 1 + M) := by exact_mod_cast he
  rw [← mul_div_assoc]
  exact ((eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0)).mpr he').symm

private theorem norm_nRatio_le (n M : ℕ) {y : ℂ} (hy : 0 ≤ y.re) (hM : ‖y‖ ≤ M) :
    ‖nRatio (2 * n) y‖ ≤ (9 / 256 : ℝ) *
      ((((n : ℝ) + 1 + M) / ((n : ℝ) + 1))) ^ 2 := by
  let x : ℂ := 2 * n
  have hdR : 0 < (d x y).re := by
    simp [x, d, Complex.mul_re]
    positivity
  have heR : 0 < (e x y).re := by
    simp [x, e, Complex.mul_re]
    positivity
  have hd : d x y ≠ 0 := fun h => hdR.ne' (by simp [h])
  have he : e x y ≠ 0 := fun h => heR.ne' (by simp [h])
  have hxR : 0 < (x + 2).re := by simp [x, Complex.mul_re]; positivity
  have hx : x + 2 ≠ 0 := fun h => hxR.ne' (by simp [h])
  have hform : nRatio x y = ((a x y / d x y)^2 * ((b x y + 2) / (x + 2))^2 *
      (c x y / e x y)^3) / 64 := by
    unfold nRatio
    field_simp
  change ‖nRatio x y‖ ≤ _
  rw [hform]
  simp only [norm_div, norm_mul, norm_pow]
  have hA : ‖a x y‖ / ‖d x y‖ ≤ (3 / 2 : ℝ) :=
    (div_le_iff₀ (norm_pos_iff.mpr hd)).mpr (norm_a_le n hy)
  have hB : ‖b x y + 2‖ / ‖x + 2‖ ≤ ((n : ℝ) + 1 + M) / ((n : ℝ) + 1) := by
    have hxN : ‖x + 2‖ = 2 * ((n : ℝ) + 1) := by
      rw [show x + 2 = (((2 * ((n : ℝ) + 1) : ℝ)) : ℂ) by push_cast; dsimp [x]; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hxN]
    calc
      _ ≤ (2 * ((n : ℝ) + 1 + M)) / (2 * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right (norm_b_add_two_le n M hM) (by positivity)
      _ = _ := by field_simp
  have hC : ‖c x y‖ / ‖e x y‖ ≤ 1 := by
    rw [div_le_iff₀ (norm_pos_iff.mpr he), one_mul]
    exact norm_c_le n hy
  calc
    _ ≤ ((3 / 2 : ℝ)^2 * (((n : ℝ) + 1 + M) / ((n : ℝ) + 1))^2 * 1^3) / ‖(64 : ℂ)‖ := by
      gcongr
    _ = _ := by norm_num; ring

/-- The hypergeometric factor has geometric decay after a binomial bound. -/
theorem norm_U_le (T : ℂ → ℂ) (n M : ℕ) {y : ℂ} (hy : 0 ≤ y.re) (hM : ‖y‖ ≤ M) :
    ‖U T n y‖ ≤ ‖T y‖ * (4 : ℝ)^M * (9 / 64 : ℝ)^n := by
  have hs (j : ℕ) : ‖U T j y‖ ≤ ‖T y‖ * (9 / 256 : ℝ)^j * ((j + M).choose j : ℝ)^2 := by
    induction j with
    | zero => simp [U]
    | succ j ih =>
      rw [U_succ T j hy, norm_mul]
      calc
        _ ≤ (‖T y‖ * (9 / 256 : ℝ)^j * ((j + M).choose j : ℝ)^2) *
            ((9 / 256 : ℝ) * ((((j : ℝ) + 1 + M) / ((j : ℝ) + 1))) ^ 2) :=
          mul_le_mul ih (norm_nRatio_le j M hy hM) (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ', ← choose_ratio j M, mul_pow]; ring
  refine (hs n).trans ?_
  calc
    _ ≤ ‖T y‖ * (9 / 256 : ℝ)^n * ((2 : ℝ)^(n + M))^2 := by
      gcongr
      exact_mod_cast Nat.choose_le_two_pow (n + M) n
    _ = _ := by
      have hb (j : ℕ) : ((2 : ℝ)^j)^2 = (4 : ℝ)^j := by
        rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
        norm_num
      rw [pow_add, mul_pow, hb, hb]
      calc
        _ = ‖T y‖ * (4 : ℝ)^M * ((9 / 256 : ℝ)^n * (4 : ℝ)^n) := by ring
        _ = _ := by rw [← mul_pow]; norm_num

end GourevitchWZ
namespace GourevitchWZ

open Complex

/-- The polynomial certificate in the summand grows at most cubically. -/
theorem norm_P_le (n : ℕ) (y : ℂ) :
    ‖P (2 * n) y‖ ≤ 800 * (((n : ℝ) + 1) * (‖y‖ + 1)) ^ 3 := by
  let R := ((n : ℝ) + 1) * (‖y‖ + 1)
  let x : ℂ := 2 * n
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hy := norm_nonneg y
  have hprod := mul_nonneg hn hy
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  have hRn : (n : ℝ) ≤ R := by dsimp [R]; nlinarith
  have hRy : ‖y‖ ≤ R := by dsimp [R]; nlinarith
  have hx : ‖x‖ ≤ 2 * R := by
    calc
      ‖x‖ = 2 * (n : ℝ) := by norm_num [x, norm_mul]
      _ ≤ 2 * R := by gcongr
  have hL : ‖3 * x + 3 * y + 1‖ ≤ 10 * R := by
    have h₁ := norm_add_le (3 * x + 3 * y) (1 : ℂ)
    have h₂ := norm_add_le (3 * x) (3 * y)
    norm_num [norm_mul] at h₁ h₂
    linarith
  have hquad : ‖7*x^2 + 4*x + 1 + 3*y^2 + 14*x*y + 4*y‖ ≤
      7*‖x‖^2 + 4*‖x‖ + 1 + 3*‖y‖^2 + 14*‖x‖*‖y‖ + 4*‖y‖ := by
    have h₁ := norm_add_le (7*x^2 + 4*x + 1 + 3*y^2 + 14*x*y) (4*y)
    have h₂ := norm_add_le (7*x^2 + 4*x + 1 + 3*y^2) (14*x*y)
    have h₃ := norm_add_le (7*x^2 + 4*x + 1) (3*y^2)
    have h₄ := norm_add_le (7*x^2 + 4*x) (1 : ℂ)
    have h₅ := norm_add_le (7*x^2) (4*x)
    norm_num [norm_mul, norm_pow] at h₁ h₂ h₃ h₄ h₅
    linarith only [h₁, h₂, h₃, h₄, h₅]
  have hB : ‖7*x^2 + 4*x + 1 + 3*y^2 + 14*x*y + 4*y‖ ≤ 80 * R^2 := by
    calc
      _ ≤ 7*‖x‖^2 + 4*‖x‖ + 1 + 3*‖y‖^2 + 14*‖x‖*‖y‖ + 4*‖y‖ := hquad
      _ ≤ 7*(2*R)^2 + 4*(2*R) + 1 + 3*R^2 + 14*(2*R)*R + 4*R := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hR) (by linarith : 0 ≤ R)]
  change ‖P x y‖ ≤ 800 * R^3
  unfold P
  rw [norm_mul]
  calc
    _ ≤ (10 * R) * (80 * R^2) := mul_le_mul hL hB (norm_nonneg _) (by linarith)
    _ = _ := by ring

end GourevitchWZ

namespace GourevitchWZ

noncomputable def envelope (n : ℕ) : ℝ := ((n : ℝ) + 1)^3 * (9 / 64 : ℝ)^n

theorem envelope_nonneg (n : ℕ) : 0 ≤ envelope n := by
  unfold envelope
  positivity

theorem summable_envelope : Summable envelope := by
  have hs (k : ℕ) : Summable (fun n : ℕ => (n : ℝ)^k * (9 / 64 : ℝ)^n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num [Real.norm_eq_abs])
  have h := ((hs 3).add ((hs 2).mul_left 3)).add (((hs 1).mul_left 3).add (hs 0))
  convert h using 1
  funext n
  unfold envelope
  simp only [pow_zero, pow_one, one_mul]
  ring

/-- Uniform norm bound on any norm-bounded subset of the closed right half-plane. -/
theorem norm_G_le_envelope (T : ℂ → ℂ) {n M : ℕ} {y : ℂ} (hy : 0 ≤ y.re)
    (hM : ‖y‖ ≤ M) (hT : ‖T y‖ ≤ 1) :
    ‖G T n y‖ ≤ (800 * (4 : ℝ)^M * ((M : ℝ)+1)^3) * envelope n := by
  calc
    ‖G T n y‖ = ‖U T n y‖ * ‖P (2 * n) y‖ := by rw [G, norm_mul]
    _ ≤ (‖T y‖ * (4 : ℝ)^M * (9 / 64 : ℝ)^n) *
        (800 * (((n : ℝ)+1) * (‖y‖+1))^3) :=
      mul_le_mul (norm_U_le T n M hy hM) (norm_P_le n y) (norm_nonneg _) (by positivity)
    _ ≤ (1 * (4 : ℝ)^M * (9 / 64 : ℝ)^n) * (800 * (((n : ℝ)+1) * ((M : ℝ)+1))^3) := by
      gcongr
    _ = _ := by unfold envelope; ring

theorem summable_G_of_norm_T (T : ℂ → ℂ) {y : ℂ} (hy : 0 ≤ y.re) (hT : ‖T y‖ ≤ 1) :
    Summable (fun n : ℕ => G T n y) := by
  let M := ⌈‖y‖⌉₊
  have hM : ‖y‖ ≤ M := Nat.le_ceil _
  exact ((summable_envelope.mul_left (800 * (4 : ℝ)^M * ((M : ℝ)+1)^3))).of_norm_bounded
    (fun n => norm_G_le_envelope T (n := n) hy hM hT)

end GourevitchWZ

/-
# The gamma normalization for the Gourevitch series

The normalization is the complex extension of Guillera's prefactor, with his
parameter `k` written as `y / 2`.
-/

namespace GourevitchGamma

open Complex

noncomputable def T (y : ℂ) : ℂ :=
  (729 / 1024 : ℂ) ^ (y / 2) *
    (Gamma ((y+1)/2) * (Gamma ((3*y+1)/6))^2 * (Gamma ((3*y+5)/6))^2) /
      (Gamma (1/2) * (Gamma (1/6))^2 * (Gamma (5/6))^2 * (Gamma ((y+2)/2))^5)

private theorem gammaHalf_ne : Gamma (1/2 : ℂ) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by norm_num [Complex.div_re, Complex.normSq_apply])

private theorem gammaSixth_ne : Gamma (1/6 : ℂ) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by norm_num [Complex.div_re, Complex.normSq_apply])

private theorem gammaFiveSixths_ne : Gamma (5/6 : ℂ) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by norm_num [Complex.div_re, Complex.normSq_apply])

private theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  exact fun h => by simp [h] at hz

theorem T_shift (y : ℂ) (hy : 0 ≤ y.re) :
    T (y+2) = T y * (9*(y+1)*(3*y+1)^2*(3*y+5)^2 / (1024*(y+2)^5)) := by
  have hy₁ : y+1 ≠ 0 := ne_zero_of_re_pos (by simp [Complex.add_re]; positivity)
  have hy₂ : y+2 ≠ 0 := ne_zero_of_re_pos (by simp [Complex.add_re]; positivity)
  have hy₃ : 3*y+1 ≠ 0 := ne_zero_of_re_pos (by simp [Complex.add_re, Complex.mul_re]; positivity)
  have hy₄ : 3*y+5 ≠ 0 := ne_zero_of_re_pos (by simp [Complex.add_re, Complex.mul_re]; positivity)
  have hg : Gamma ((y+2)/2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    have hcast : (2 : ℂ) = (↑(2 : ℝ) : ℂ) := by norm_num
    rw [hcast, Complex.div_ofReal_re]
    simp [Complex.add_re]
    positivity
  have hbase : (729 / 1024 : ℂ) ^ ((y+2)/2) =
      (729 / 1024 : ℂ) ^ (y/2) * (729 / 1024 : ℂ) := by
    rw [show (y+2)/2 = y/2+1 by ring, cpow_add _ _ (by norm_num), cpow_one]
  unfold T
  rw [hbase, show ((y+2)+1)/2 = (y+1)/2+1 by ring,
    show (3*(y+2)+1)/6 = (3*y+1)/6+1 by ring,
    show (3*(y+2)+5)/6 = (3*y+5)/6+1 by ring,
    show ((y+2)+2)/2 = (y+2)/2+1 by ring,
    Gamma_add_one _ (div_ne_zero hy₁ (by norm_num)),
    Gamma_add_one _ (div_ne_zero hy₃ (by norm_num)),
    Gamma_add_one _ (div_ne_zero hy₄ (by norm_num)),
    Gamma_add_one _ (div_ne_zero hy₂ (by norm_num))]
  field_simp [gammaHalf_ne, gammaSixth_ne, gammaFiveSixths_ne, hg, hy₂]
  ring

theorem T_zero : T 0 = 1 := by
  norm_num [T, Complex.Gamma_one, Complex.cpow_zero, gammaHalf_ne, gammaSixth_ne,
    gammaFiveSixths_ne]

private theorem gamma_half_sq : Gamma (1/2 : ℂ)^2 = (Real.pi : ℂ) := by
  have h := Gamma_mul_Gamma_one_sub (1/2 : ℂ)
  rw [show 1-(1/2:ℂ)=1/2 by norm_num, show (Real.pi:ℂ)*(1/2:ℂ)=(Real.pi:ℂ)/2 by ring,
    Complex.sin_pi_div_two, div_one] at h
  simpa only [pow_two] using h

private theorem gamma_sixth_pair : Gamma (1/6 : ℂ) * Gamma (5/6 : ℂ) = 2*(Real.pi:ℂ) := by
  have h := Gamma_mul_Gamma_one_sub (1/6 : ℂ)
  have hsin : sin ((Real.pi:ℂ)*(1/6:ℂ)) = (1/2:ℂ) := by
    rw [show (Real.pi:ℂ)*(1/6:ℂ) = ((Real.pi/6:ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, Real.sin_pi_div_six]
    norm_num
  rw [show 1-(1/6:ℂ)=5/6 by norm_num, hsin] at h
  rw [h]
  ring

private theorem gamma_two_thirds_pair_sq :
    (Gamma (2/3 : ℂ) * Gamma (4/3 : ℂ))^2 = (4/27 : ℂ)*(Real.pi:ℂ)^2 := by
  have h := Gamma_mul_Gamma_one_sub (1/3 : ℂ)
  rw [show 1-(1/3:ℂ)=2/3 by norm_num] at h
  have hs : sin ((Real.pi:ℂ)*(1/3:ℂ))^2 = (3/4:ℂ) := by
    rw [show (Real.pi:ℂ)*(1/3:ℂ) = ((Real.pi/3:ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, ← Complex.ofReal_pow, Real.sq_sin_pi_div_three]
    norm_num
  calc
    _ = (Gamma (1/3 : ℂ) * Gamma (2/3 : ℂ))^2 / 9 := by
      rw [show (4/3:ℂ)=1/3+1 by norm_num, Gamma_add_one _ (by norm_num)]
      ring
    _ = _ := by rw [h, div_pow, hs]; ring

private theorem constant_cpow_half : (729/1024 : ℂ)^(1/2:ℂ) = 27/32 := by
  have h := (Complex.ofReal_cpow (x := 729/1024) (by norm_num) (1/2)).symm
  have h₁ : (729/1024 : ℝ) ^ (1/2:ℝ) = (27/32:ℝ) := by
    rw [← Real.sqrt_eq_rpow, show (729/1024:ℝ) = (27/32)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h₁] at h
  push_cast at h
  exact h

theorem T_one : T 1 = 1/(Real.pi : ℂ)^3 := by
  have hΓ : Gamma (3/2 : ℂ) = (1/2) * Gamma (1/2) := by
    rw [show (3/2:ℂ)=1/2+1 by norm_num, Gamma_add_one _ (by norm_num)]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold T
  rw [show ((1:ℂ)+1)/2=1 by norm_num, show (3*(1:ℂ)+1)/6=2/3 by norm_num,
    show (3*(1:ℂ)+5)/6=4/3 by norm_num, show ((1:ℂ)+2)/2=3/2 by norm_num,
    constant_cpow_half, Gamma_one, one_mul, hΓ]
  rw [show Gamma (2/3 : ℂ)^2*Gamma (4/3 : ℂ)^2 =
      (Gamma (2/3)*Gamma (4/3))^2 by ring, gamma_two_thirds_pair_sq,
    show Gamma (1/2)*(Gamma (1/6))^2*(Gamma (5/6))^2*((1/2)*Gamma (1/2))^5 =
      ((Gamma (1/2:ℂ))^2)^3 * (Gamma (1/6)*Gamma (5/6))^2/32 by ring,
    gamma_half_sq, gamma_sixth_pair]
  field_simp
  ring

end GourevitchGamma

/-
The normalizing gamma ratios are quotients of beta integrals. On the right
half-plane each such integral is bounded in norm by its value at zero.
-/

namespace GourevitchGamma

open Complex Filter MeasureTheory Set intervalIntegral

private theorem norm_beta_le (z : ℂ) (hz : 0 ≤ z.re) (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    ‖betaIntegral (z+(a:ℂ)) (1-(a:ℂ))‖ ≤ ‖betaIntegral a (1-(a:ℂ))‖ := by
  let f (x : ℝ) := (x:ℂ)^((z+(a:ℂ))-1) * (1-(x:ℂ))^((1-(a:ℂ))-1)
  let g (x : ℝ) := (x:ℂ)^((a:ℂ)-1) * (1-(x:ℂ))^((1-(a:ℂ))-1)
  have hg : IntegrableOn g (Ioo (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent (by simpa only [ofReal_re] using ha)
        (by simpa only [sub_re, one_re, ofReal_re] using sub_pos.mpr ha'))
  have hnorm (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : ‖f x‖ ≤ ‖g x‖ := by
    have hx' : 0 < 1-x := sub_pos.mpr hx.2
    have hcast : (1:ℂ)-(x:ℂ) = ((1-x:ℝ):ℂ) := by push_cast; rfl
    simp only [f, g, norm_mul, hcast, norm_cpow_eq_rpow_re_of_pos hx.1,
      norm_cpow_eq_rpow_re_of_pos hx', sub_re, add_re, ofReal_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by linarith)) (by positivity)
  have hnonneg (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : (‖g x‖ : ℂ) = g x := by
    have hx' : 0 < 1-x := sub_pos.mpr hx.2
    have hcast : (1:ℂ)-(x:ℂ) = ((1-x:ℝ):ℂ) := by push_cast; rfl
    simp only [g, norm_mul, hcast, norm_cpow_eq_rpow_re_of_pos hx.1,
      norm_cpow_eq_rpow_re_of_pos hx', sub_re, ofReal_re, one_re]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow hx'.le]
    push_cast
    rfl
  have hg_eq : (∫ x in Ioo (0:ℝ) 1, g x) = ((∫ x in Ioo (0:ℝ) 1, ‖g x‖ : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioo (fun x hx => (hnonneg x hx).symm)
  have hInt : ‖∫ x in Ioo (0:ℝ) 1, f x‖ ≤ ∫ x in Ioo (0:ℝ) 1, ‖g x‖ := by
    apply MeasureTheory.norm_integral_le_of_norm_le hg.norm
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo (0:ℝ) 1) measurableSet_Ioo] with x hx
    exact hnorm x hx
  simp only [betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  change ‖∫ x in Ioo (0:ℝ) 1, f x‖ ≤ ‖∫ x in Ioo (0:ℝ) 1, g x‖
  rw [hg_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact hInt

theorem norm_Gamma_le (z : ℂ) (hz : 0 ≤ z.re) (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    ‖Gamma (z+(a:ℂ))‖ ≤ ‖Gamma a‖ * ‖Gamma (z+1)‖ := by
  have h := norm_beta_le z hz a ha ha'
  have h₁ : 0 < (z+(a:ℂ)).re := by simp [add_re]; positivity
  have h₂ : 0 < (1-(a:ℂ)).re := by simpa using sub_pos.mpr ha'
  have h₃ : 0 < (z+1).re := by simp [add_re]; positivity
  rw [betaIntegral_eq_Gamma_mul_div _ _ h₁ h₂,
    betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) h₂,
    show z+(a:ℂ)+(1-(a:ℂ)) = z+1 by ring,
    show (a:ℂ)+(1-(a:ℂ))=1 by ring, Gamma_one, div_one] at h
  simp only [norm_div, norm_mul] at h
  have hp₀ : 0 < ‖Gamma (1-(a:ℂ))‖ := norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos h₂)
  have hp₁ : 0 < ‖Gamma (z+1)‖ := norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos h₃)
  apply (mul_le_mul_iff_right₀ hp₀).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using (div_le_iff₀ hp₁).mp h

theorem norm_T_le (y : ℂ) (hy : 0 ≤ y.re) : ‖T y‖ ≤ 1 := by
  let z := y/2
  have hz : 0 ≤ z.re := by
    simpa only [z, show (2:ℂ)=(↑(2:ℝ):ℂ) by norm_num, div_ofReal_re] using
      (div_nonneg hy (by norm_num : (0:ℝ) ≤ 2))
  have hhalf := norm_Gamma_le z hz (1/2) (by norm_num) (by norm_num)
  have hsixth := norm_Gamma_le z hz (1/6) (by norm_num) (by norm_num)
  have hfivesixths := norm_Gamma_le z hz (5/6) (by norm_num) (by norm_num)
  push_cast at hhalf hsixth hfivesixths
  have hexp : ‖(729 / 1024 : ℂ) ^ z‖ ≤ 1 := by
    rw [show (729 / 1024 : ℂ) = ((729/1024:ℝ):ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    exact Real.rpow_le_one (by norm_num) (by norm_num) hz
  have hGamma : Gamma (z+1) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simp [add_re]
    positivity
  have hposHalf : 0 < ‖Gamma (1/2 : ℂ)‖ := norm_pos_iff.mpr gammaHalf_ne
  have hposSixth : 0 < ‖Gamma (1/6 : ℂ)‖ := norm_pos_iff.mpr gammaSixth_ne
  have hposFiveSixths : 0 < ‖Gamma (5/6 : ℂ)‖ := norm_pos_iff.mpr gammaFiveSixths_ne
  have hposZ : 0 < ‖Gamma (z+1)‖ := norm_pos_iff.mpr hGamma
  unfold T
  rw [show (y+1)/2 = z+1/2 by unfold z; ring,
    show (3*y+1)/6 = z+1/6 by unfold z; ring,
    show (3*y+5)/6 = z+5/6 by unfold z; ring,
    show (y+2)/2 = z+1 by unfold z; ring]
  simp only [norm_div, norm_mul, norm_pow]
  apply (div_le_one (by
    positivity : 0 < ‖Gamma (1/2 : ℂ)‖ * ‖Gamma (1/6 : ℂ)‖^2 *
      ‖Gamma (5/6 : ℂ)‖^2 * ‖Gamma (z+1)‖^5)).2
  calc
    _ ≤ 1 * ((‖Gamma (1/2 : ℂ)‖*‖Gamma (z+1)‖) *
        (‖Gamma (1/6 : ℂ)‖*‖Gamma (z+1)‖)^2 *
        (‖Gamma (5/6 : ℂ)‖*‖Gamma (z+1)‖)^2) := by
      change ‖(729 / 1024 : ℂ) ^ z‖ * _ ≤ _
      gcongr
    _ = _ := by ring

private theorem gamma_differentiable_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  refine differentiableAt_Gamma z (fun n he => ?_)
  have he' := congrArg Complex.re he
  simp only [neg_re, natCast_re] at he'
  linarith [Nat.cast_nonneg (α:=ℝ) n]

private theorem pos_re_div_real {z : ℂ} (hz : 0 < z.re) {r : ℝ} (hr : 0 < r) :
    0 < (z/(r:ℂ)).re := by
  rw [div_ofReal_re]
  positivity

theorem differentiableAt_T (y : ℂ) (hy : 0 ≤ y.re) : DifferentiableAt ℂ T y := by
  have h₁ : 0 < ((y+1)/2).re := by
    simpa using pos_re_div_real (z:=y+1) (by simp [add_re]; positivity) (r:=2) (by norm_num)
  have h₂ : 0 < ((3*y+1)/6).re := by
    simpa using pos_re_div_real (z:=3*y+1) (by simp [add_re, mul_re]; positivity)
      (r:=6) (by norm_num)
  have h₃ : 0 < ((3*y+5)/6).re := by
    simpa using pos_re_div_real (z:=3*y+5) (by simp [add_re, mul_re]; positivity)
      (r:=6) (by norm_num)
  have h₄ : 0 < ((y+2)/2).re := by
    simpa using pos_re_div_real (z:=y+2) (by simp [add_re]; positivity) (r:=2) (by norm_num)
  have hg₁ : DifferentiableAt ℂ (fun z => Gamma ((z+1)/2)) y :=
    (gamma_differentiable_of_re_pos h₁).comp y (by fun_prop)
  have hg₂ : DifferentiableAt ℂ (fun z => Gamma ((3*z+1)/6)) y :=
    (gamma_differentiable_of_re_pos h₂).comp y (by fun_prop)
  have hg₃ : DifferentiableAt ℂ (fun z => Gamma ((3*z+5)/6)) y :=
    (gamma_differentiable_of_re_pos h₃).comp y (by fun_prop)
  have hg₄ : DifferentiableAt ℂ (fun z => Gamma ((z+2)/2)) y :=
    (gamma_differentiable_of_re_pos h₄).comp y (by fun_prop)
  have hexp : DifferentiableAt ℂ (fun z : ℂ => (729/1024 : ℂ)^(z/2)) y :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
  unfold T
  apply DifferentiableAt.div (by fun_prop) (by fun_prop)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero gammaHalf_ne (pow_ne_zero _ gammaSixth_ne))
      (pow_ne_zero _ gammaFiveSixths_ne))
    (pow_ne_zero _ (Gamma_ne_zero_of_re_pos h₄))

end GourevitchGamma

/-
Differentiability of the individual terms and extension of the period identity
to the real axis.
-/

namespace GourevitchWZ

open Filter Topology

private theorem differentiableAt_rise {f : ℂ → ℂ} {y : ℂ}
    (hf : DifferentiableAt ℂ f y) (n : ℕ) :
    DifferentiableAt ℂ (fun z => rise (f z) n) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [rise_succ]
    exact ih.mul (by fun_prop)

theorem differentiableAt_G (n : ℕ) (y : ℂ) (hy : 0 ≤ y.re) :
    DifferentiableAt ℂ (fun z => G GourevitchGamma.T n z) y := by
  have hT := GourevitchGamma.differentiableAt_T y hy
  have hA : DifferentiableAt ℂ (fun z => rise (3*z+1) n) y :=
    differentiableAt_rise (by fun_prop) n
  have hB : DifferentiableAt ℂ (fun z => rise (1-z) n) y :=
    differentiableAt_rise (by fun_prop) n
  have hC : DifferentiableAt ℂ (fun z => rise (z+1) n) y :=
    differentiableAt_rise (by fun_prop) n
  have hD : DifferentiableAt ℂ (fun z => rise (2*z+2) n) y :=
    differentiableAt_rise (by fun_prop) n
  have hE : DifferentiableAt ℂ (fun z => rise (z+2) n) y :=
    differentiableAt_rise (by fun_prop) n
  have h0 : rise 2 n ≠ 0 := rise_ne_zero 2 (by norm_num) n
  have h1 : rise (2*y+2) n ≠ 0 :=
    rise_ne_zero (2*y+2) (by simp [Complex.add_re, Complex.mul_re]; positivity) n
  have h2 : rise (y+2) n ≠ 0 :=
    rise_ne_zero (y+2) (by simp [Complex.add_re]; positivity) n
  have hU : DifferentiableAt ℂ (fun z => U GourevitchGamma.T n z) y := by
    unfold U
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h1)) (pow_ne_zero _ h2)
  unfold G
  exact hU.mul (by unfold P; fun_prop)

theorem periodic_of_nonreal (f : ℂ → ℂ) (hcont : ContinuousOn f {z | 0 ≤ z.re})
    (hperiodic : ∀ z : ℂ, 0 ≤ z.re → z.im ≠ 0 → f (z+2) = f z)
    (y : ℂ) (hy : 0 ≤ y.re) : f (y+2) = f y := by
  by_cases hi : y.im = 0
  · let ε (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)
    let u (n : ℕ) : ℂ := y + (ε n : ℂ) * Complex.I
    have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hεC : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 0) := by
      simpa only [Complex.ofReal_zero, Function.comp_def] using
        (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.comp hε
    have hu : Tendsto u atTop (𝓝 y) := by
      simpa only [u, zero_mul, add_zero] using
        tendsto_const_nhds.add (hεC.mul_const Complex.I)
    have huRe (n : ℕ) : (u n).re = y.re := by
      simp [u, Complex.add_re, Complex.mul_re]
    have huIm (n : ℕ) : (u n).im ≠ 0 := by
      simp only [u, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, hi, zero_add]
      exact (by unfold ε; positivity : 0 < ε n).ne'
    have hShift {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (z+2).re := by
      simp [Complex.add_re]
      positivity
    have huNonneg (n : ℕ) : 0 ≤ (u n).re := (huRe n).symm ▸ hy
    have hu₀ : Tendsto u atTop (𝓝[{z : ℂ | 0 ≤ z.re}] y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall huNonneg⟩
    have hu₂ : Tendsto (fun n => u n+2) atTop (𝓝[{z : ℂ | 0 ≤ z.re}] (y+2)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu.add_const 2,
        Eventually.of_forall (fun n => hShift (huNonneg n))⟩
    have hleft := (hcont (y+2) (hShift hy)).tendsto.comp hu₂
    have hright := (hcont y hy).tendsto.comp hu₀
    exact tendsto_nhds_unique (hleft.congr' (Eventually.of_forall
      (fun n => hperiodic (u n) (huNonneg n) (huIm n)))) hright
  · exact hperiodic y hy hi

end GourevitchWZ

/- Periodic uniqueness for the analytic step in Guillera's WZ proof. -/

open Complex Filter Function
open scoped Topology

namespace GourevitchPeriodic

private theorem q_one_periodic : Periodic (Periodic.qParam 1) (1 : ℂ) := by
  intro z
  simp [Periodic.qParam, mul_add, Complex.exp_add, Complex.exp_two_pi_mul_I]

private theorem q_one_neg (z : ℂ) : Periodic.qParam 1 (-z) = (Periodic.qParam 1 z)⁻¹ := by
  simp [Periodic.qParam, Complex.exp_neg]

/-- The periodic function descends holomorphically through the puncture
when its growth toward the upper half-plane is strictly subexponential in the inverse cusp parameter. -/
theorem exists_entire_cusp {f : ℂ → ℂ} {a C : ℝ}
    (hf : Differentiable ℂ f) (hp : Periodic f (1 : ℂ)) (ha : a < 2 * Real.pi)
    (hg : ∀ z, 0 ≤ z.im → ‖f z‖ ≤ C * Real.exp (a * z.im)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z, F (Periodic.qParam 1 z) = f z := by
  let q := Periodic.qParam 1
  let g := fun z => q z * f z
  have hgd : Differentiable ℂ g := (Periodic.differentiable_qParam (h := 1)).mul hf
  have hgp : Periodic g (1 : ℂ) := q_one_periodic.mul hp
  have hgp' : Periodic g ((1 : ℝ) : ℂ) := by simpa using hgp
  let L := comap Complex.im (atTop : Filter ℝ)
  have him : Tendsto Complex.im L atTop := tendsto_comap
  have hnotneg : ∀ᶠ z in L, 0 ≤ z.im := him.eventually (eventually_ge_atTop 0)
  have hu : Tendsto (fun z : ℂ => C * Real.exp ((a - 2 * Real.pi) * z.im)) L (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp
      (him.const_mul_atTop_of_neg (sub_neg.mpr ha))).const_mul C)
  have hz : ZeroAtFilter L g := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg (g z))) ?_ hu
    filter_upwards [hnotneg] with z hz
    calc
      ‖g z‖ = Real.exp (-2 * Real.pi * z.im) * ‖f z‖ := by
        simp [g, q, Periodic.norm_qParam]
      _ ≤ Real.exp (-2 * Real.pi * z.im) * (C * Real.exp (a * z.im)) :=
        mul_le_mul_of_nonneg_left (hg z hz) (Real.exp_pos _).le
      _ = C * Real.exp ((a - 2 * Real.pi) * z.im) := by
        rw [sub_mul, sub_eq_add_neg, Real.exp_add]
        ring
  let H := Periodic.cuspFunction 1 g
  have hH0 : H 0 = 0 := Periodic.cuspFunction_zero_of_zero_at_inf zero_lt_one hz
  have hHd : Differentiable ℂ H := by
    intro w
    by_cases hw : w = 0
    · subst w
      exact Periodic.differentiableAt_cuspFunction_zero zero_lt_one hgp'
        (Eventually.of_forall hgd) hz.boundedAtFilter
    · rw [← Periodic.qParam_right_inv (h := 1) one_ne_zero hw]
      exact Periodic.differentiableAt_cuspFunction one_ne_zero hgp' (hgd _)
  let F := dslope H 0
  have hFd : Differentiable ℂ F :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
      hHd.differentiableOn)
  refine ⟨F, hFd, fun z => ?_⟩
  change dslope H 0 (q z) = f z
  rw [dslope_of_ne _ (Periodic.qParam_ne_zero (h := 1) z), slope_def_field, hH0, sub_zero, sub_zero]
  have hcomp : H (q z) = g z := Periodic.eq_cuspFunction one_ne_zero hgp' z
  rw [hcomp]
  exact mul_div_cancel_left₀ _ (Periodic.qParam_ne_zero (h := 1) z)

/-- A one-periodic entire function of exponential type strictly below two pi
in both imaginary directions is constant. -/
theorem periodic_eq_of_growth {f : ℂ → ℂ} {a C : ℝ}
    (hf : Differentiable ℂ f) (hp : Periodic f (1 : ℂ))
    (ha : a < 2 * Real.pi)
    (hg : ∀ z, ‖f z‖ ≤ C * Real.exp (a * |z.im|)) (x y : ℂ) : f x = f y := by
  obtain ⟨F, hFd, hF⟩ := exists_entire_cusp hf hp ha
    (fun z hz => by simpa [abs_of_nonneg hz] using hg z)
  let negf := fun z : ℂ => f (-z)
  have hnper : Periodic negf (1 : ℂ) := by
    intro z
    have heq : -(z + 1) + 1 = -z := by ring
    simpa [negf, heq] using (hp (-(z + 1))).symm
  obtain ⟨H, hHd, hH⟩ := exists_entire_cusp (hf.comp differentiable_neg) hnper ha
    (fun z hz => by simpa [negf, Complex.neg_im, abs_of_nonneg hz] using hg (-z))
  let K := Metric.closedBall (0 : ℂ) 1
  have hrel {w : ℂ} (hw : w ≠ 0) : F w = H w⁻¹ := by
    let z := Periodic.invQParam 1 w
    have hz : Periodic.qParam 1 z = w := Periodic.qParam_right_inv one_ne_zero hw
    have hneg : Periodic.qParam 1 (-z) = w⁻¹ := (q_one_neg z).trans (congrArg Inv.inv hz)
    rw [← hneg, hH, ← hz, hF]
    simp
  have hsub : Set.range F ⊆ F '' K ∪ H '' K := by
    rintro _ ⟨w, rfl⟩
    by_cases hw : ‖w‖ ≤ 1
    · exact Or.inl ⟨w, by simpa [K, Metric.mem_closedBall, dist_zero_right] using hw, rfl⟩
    · have hn : w ≠ 0 := by rintro rfl; simp at hw
      have hi : ‖w⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hw))
      exact Or.inr ⟨w⁻¹, by simpa [K, Metric.mem_closedBall, dist_zero_right] using hi, (hrel hn).symm⟩
  have hK : IsCompact K := isCompact_closedBall _ _
  have hb := ((hK.image hFd.continuous).isBounded.union
    (hK.image hHd.continuous).isBounded).subset hsub
  rw [← hF x, ← hF y]
  exact hFd.apply_eq_apply_of_bounded hb _ _


/-- A holomorphic function on the right half-plane is constant there if it is
one-periodic and has subcritical exponential growth on a fundamental strip. -/
theorem halfPlane_eq_of_growth {f : ℂ → ℂ} {a C : ℝ}
    (hd : ∀ z, 0 < z.re → DifferentiableAt ℂ f z)
    (hp : ∀ z, 0 ≤ z.re → f (z + 1) = f z)
    (ha : a < 2 * Real.pi)
    (hg : ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ C * Real.exp (a * |z.im|))
    {x y : ℂ} (hx : 0 ≤ x.re) (hy : 0 ≤ y.re) : f x = f y := by
  let reduce (z : ℂ) : ℂ := z - (⌊z.re⌋ : ℤ)
  let g : ℂ → ℂ := f ∘ reduce
  have hre (z : ℂ) : (reduce z).re = z.re - (⌊z.re⌋ : ℤ) := by simp [reduce]
  have hs₁ (z : ℂ) : 0 ≤ (reduce z).re := by
    rw [hre]
    exact sub_nonneg.mpr (Int.floor_le _)
  have hs₂ (z : ℂ) : (reduce z).re ≤ 1 := by
    rw [hre]
    linarith [Int.lt_floor_add_one z.re]
  have hnat (z : ℂ) (hz : 0 ≤ z.re) (n : ℕ) : f (z + (n : ℂ)) = f z := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0 ≤ (z + (n : ℂ)).re := by
        simp only [Complex.add_re, Complex.natCast_re]
        positivity
      calc
        f (z + ((n + 1 : ℕ) : ℂ)) = f (z + (n : ℂ) + 1) := by
          rw [Nat.cast_add, Nat.cast_one, add_assoc]
        _ = f (z + (n : ℂ)) := hp _ hpos
        _ = f z := ih
  have hshift (z : ℂ) (d : ℤ) (hz : 0 ≤ (z + (d : ℂ)).re) :
      g z = f (z + (d : ℂ)) := by
    have hd0 : 0 ≤ ⌊z.re⌋ + d := by
      rw [← Int.floor_add_intCast]
      exact Int.floor_nonneg.mpr (by simpa using hz)
    let n : ℕ := (⌊z.re⌋ + d).toNat
    have hn : (n : ℤ) = ⌊z.re⌋ + d := Int.toNat_of_nonneg hd0
    have hn' : (n : ℂ) = (⌊z.re⌋ : ℤ) + (d : ℂ) := by exact_mod_cast hn
    change f (reduce z) = f (z + (d : ℂ))
    rw [← hnat (reduce z) (hs₁ z) n]
    congr 1
    simp only [reduce, hn']
    ring
  have hper : Periodic g (1 : ℂ) := by
    intro z
    change f (reduce (z + 1)) = f (reduce z)
    congr 1
    simp only [reduce, Complex.add_re, Complex.one_re, Int.floor_add_one, Int.cast_add,
      Int.cast_one]
    ring
  have hdiff : Differentiable ℂ g := by
    intro z
    let d := 1 - ⌊z.re⌋
    have hpos : 0 < (z + (d : ℂ)).re := by
      simp only [d, Int.cast_sub, Int.cast_one, Complex.add_re, Complex.sub_re,
        Complex.one_re, Complex.intCast_re]
      linarith [Int.floor_le z.re]
    have hmem : {w : ℂ | 0 < (w + (d : ℂ)).re} ∈ 𝓝 z := by
      apply (isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_id.add continuous_const))).mem_nhds
      exact hpos
    have hloc : g =ᶠ[𝓝 z] fun w => f (w + (d : ℂ)) := by
      filter_upwards [hmem] with w hw
      exact hshift w d hw.le
    exact ((hd _ hpos).comp z
      (differentiable_id.add_const (d : ℂ)).differentiableAt).congr_of_eventuallyEq hloc
  have hbound (z : ℂ) : ‖g z‖ ≤ C * Real.exp (a * |z.im|) := by
    simpa [g, reduce] using hg (reduce z) (hs₁ z) (hs₂ z)
  have hreal (z : ℂ) (hz : 0 ≤ z.re) : g z = f z := by
    simpa using hshift z 0 (by simpa using hz)
  rw [← hreal x hx, ← hreal y hy]
  exact periodic_eq_of_growth hdiff hper ha hbound x y

end GourevitchPeriodic

namespace GourevitchWZ

open Complex Filter Set
open scoped Topology

noncomputable def series (y : ℂ) : ℂ := ∑' n : ℕ, G GourevitchGamma.T n y

private theorem summable_terms {y : ℂ} (hy : 0 ≤ y.re) :
    Summable (fun n : ℕ => G GourevitchGamma.T n y) :=
  summable_G_of_norm_T _ hy (GourevitchGamma.norm_T_le y hy)

noncomputable def amplitude (M : ℕ) : ℝ := 800 * (4 : ℝ)^M * ((M : ℝ) + 1)^3

private theorem term_le {n M : ℕ} {y : ℂ} (hy : 0 ≤ y.re) (hM : ‖y‖ ≤ M) :
    ‖G GourevitchGamma.T n y‖ ≤ amplitude M * envelope n :=
  norm_G_le_envelope _ hy hM (GourevitchGamma.norm_T_le y hy)

theorem continuousOn_series : ContinuousOn series {y | 0 ≤ y.re} := by
  intro y hy
  let M : ℕ := ⌈‖y‖ + 1⌉₊
  have hM : ‖y‖ < (M : ℝ) := by
    have := Nat.le_ceil (‖y‖ + 1)
    linarith
  let B : Set ℂ := Metric.ball 0 M
  have hyB : y ∈ B := by simpa [B, Metric.mem_ball, dist_zero_right] using hM
  have hcont : ContinuousOn series ({y | 0 ≤ y.re} ∩ B) := by
    apply continuousOn_tsum (u := fun n => amplitude M * envelope n)
    · intro n z hz
      exact (differentiableAt_G n z hz.1).continuousAt.continuousWithinAt
    · exact summable_envelope.mul_left _
    · intro n z hz
      exact term_le hz.1 (le_of_lt (by simpa [B, Metric.mem_ball, dist_zero_right] using hz.2))
  exact (hcont y ⟨hy, hyB⟩).mono_of_mem_nhdsWithin
    (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hyB)))

theorem differentiableAt_series (y : ℂ) (hy : 0 < y.re) : DifferentiableAt ℂ series y := by
  let M : ℕ := ⌈‖y‖ + 1⌉₊
  have hM : ‖y‖ < (M : ℝ) := by
    have := Nat.le_ceil (‖y‖ + 1)
    linarith
  let B : Set ℂ := Metric.ball 0 M
  let U := {z : ℂ | 0 < z.re} ∩ B
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hyU : y ∈ U := ⟨hy, by simpa [B, Metric.mem_ball, dist_zero_right] using hM⟩
  have hdiff : DifferentiableOn ℂ series U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_envelope.mul_left (amplitude M))
      (F := fun n z => G GourevitchGamma.T n z) ?_ hU ?_
    · intro n z hz
      exact (differentiableAt_G n z (le_of_lt hz.1)).differentiableWithinAt
    · intro n z hz
      exact term_le (le_of_lt hz.1)
        (le_of_lt (by simpa [B, Metric.mem_ball, dist_zero_right] using hz.2))
  exact hdiff.differentiableAt (hU.mem_nhds hyU)

theorem series_periodic (y : ℂ) (hy : 0 ≤ y.re) : series (y + 2) = series y := by
  refine periodic_of_nonreal series continuousOn_series ?_ y hy
  intro z hz hzim
  have hz' : 0 ≤ (z + 2).re := by simp [Complex.add_re]; positivity
  let M : ℕ := ⌈‖z‖⌉₊
  have hM : ‖z‖ ≤ M := Nat.le_ceil _
  have hF : Tendsto (fun n : ℕ => F GourevitchGamma.T n z) atTop (𝓝 0) := by
    apply F_tendsto_zero_of_geometric _ _ (C := ‖GourevitchGamma.T z‖ * (4 : ℝ)^M)
      (r := 9 / 64) (by positivity) (by norm_num) (by norm_num)
    exact Eventually.of_forall (fun n => norm_U_le _ n M hz hM)
  exact sum_periodic _ (fun v hv => GourevitchGamma.T_shift v hv) hz hzim
    (summable_terms hz) (summable_terms hz') hF

private theorem series_norm_le {y : ℂ} {M : ℕ} (hy : 0 ≤ y.re) (hM : ‖y‖ ≤ M) :
    ‖series y‖ ≤ amplitude M * (∑' n, envelope n) := by
  have hb := summable_envelope.mul_left (amplitude M)
  have hs : Summable (fun n : ℕ => ‖G GourevitchGamma.T n y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => term_le hy hM) hb
  calc
    ‖series y‖ ≤ ∑' n : ℕ, ‖G GourevitchGamma.T n y‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, amplitude M * envelope n := hs.tsum_le_tsum (fun _ => term_le hy hM) hb
    _ = _ := tsum_mul_left

private theorem amplitude_le (M : ℕ) : amplitude M ≤ 4800 * Real.exp (3 * (M : ℝ) + 1) := by
  have hlog : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have hfour : (4 : ℝ)^M ≤ Real.exp (2 * (M : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hpoly : ((M : ℝ) + 1)^3 ≤ 6 * Real.exp ((M : ℝ) + 1) := by
    have h := Real.pow_div_factorial_le_exp (x := (M : ℝ) + 1) (by positivity) 3
    norm_num [Nat.factorial] at h
    linarith
  calc
    amplitude M ≤ 800 * Real.exp (2 * (M : ℝ)) * (6 * Real.exp ((M : ℝ) + 1)) := by
      unfold amplitude
      gcongr
    _ = 4800 * (Real.exp (2 * (M : ℝ)) * Real.exp ((M : ℝ) + 1)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem norm_series_doubled_le (z : ℂ) (hz : 0 ≤ z.re) (hz' : z.re ≤ 1) :
    ‖series (2 * z)‖ ≤ (4800 * Real.exp 10 * (∑' n, envelope n)) * Real.exp (6 * |z.im|) := by
  let M : ℕ := ⌈‖(2 : ℂ) * z‖⌉₊
  have hM : ‖(2 : ℂ) * z‖ ≤ M := Nat.le_ceil _
  have hz2 : 0 ≤ ((2 : ℂ) * z).re := by simp [Complex.mul_re, hz]
  have hn : ‖(2 : ℂ) * z‖ ≤ 2 + 2 * |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz] at h
    norm_num [norm_mul]
    linarith
  have hM' : (M : ℝ) ≤ 3 + 2 * |z.im| := by
    have h := Nat.ceil_lt_add_one (norm_nonneg ((2 : ℂ) * z))
    linarith
  have hsum : 0 ≤ ∑' n : ℕ, envelope n := tsum_nonneg envelope_nonneg
  calc
    _ ≤ amplitude M * (∑' n, envelope n) := series_norm_le hz2 hM
    _ ≤ (4800 * Real.exp (3 * (M : ℝ) + 1)) * (∑' n, envelope n) :=
      mul_le_mul_of_nonneg_right (amplitude_le M) hsum
    _ ≤ (4800 * Real.exp (10 + 6 * |z.im|)) * (∑' n, envelope n) := by
      have hh : Real.exp (3 * (M : ℝ) + 1) ≤ Real.exp (10 + 6 * |z.im|) :=
        Real.exp_le_exp.mpr (by linarith [hM'])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hsum
    _ = _ := by rw [Real.exp_add]; ring

theorem series_zero_eq_one : series 0 = series 1 := by
  let f := fun z : ℂ => series (2 * z)
  have hdiff (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ f z := by
    have hz2 : 0 < ((2 : ℂ) * z).re := by
      simp [Complex.mul_re]
      positivity
    exact (differentiableAt_series _ hz2).comp z
      (differentiable_id.const_mul (2 : ℂ)).differentiableAt
  have hper (z : ℂ) (hz : 0 ≤ z.re) : f (z + 1) = f z := by
    have hz2 : 0 ≤ ((2 : ℂ) * z).re := by simp [Complex.mul_re, hz]
    simpa [f, mul_add] using series_periodic (2 * z) hz2
  have hconst := GourevitchPeriodic.halfPlane_eq_of_growth (f := f) hdiff hper
    (show (6 : ℝ) < 2 * Real.pi by linarith [Real.pi_gt_three]) norm_series_doubled_le
    (x := 0) (y := 1 / 2) (by norm_num) (by norm_num [Complex.div_re])
  have hnum : (2 : ℂ) * (1 / 2) = 1 := by norm_num
  simpa [f, hnum] using hconst

end GourevitchWZ

theorem OMA.solution : type_of% @Gourevitch.gourevitch_series_identity := by
  have hterm (n : ℕ) :
      Complex.ofReal (((1 + 14 * (n : ℝ) + 76 * (n : ℝ)^2 + 168 * (n : ℝ)^3) /
        (2 ^ (20 * n))) * (Nat.centralBinom n : ℝ) ^ 7) =
      GourevitchWZ.G GourevitchGamma.T n 0 := by
    rw [GourevitchWZ.G_at_zero _ GourevitchGamma.T_zero]
    push_cast
    rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  simp only [hterm, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  change GourevitchWZ.series 0 = _
  rw [GourevitchWZ.series_zero_eq_one, GourevitchWZ.series,
    GourevitchWZ.tsum_at_one, GourevitchGamma.T_one]
  ring