import OMAReductions.R_oeis_a026125_R1
import Mathlib.RingTheory.PowerSeries.Derivative

open PowerSeries

private theorem euler_eq (g : PowerSeries ℤ) :
    PowerSeries.mk (fun n => (n : ℤ) * coeff n g) = X * derivative ℤ g := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_derivative, Nat.cast_succ, mul_comm]

theorem OMA.solution : OMA.R_oeis_a026125_R1.H2 := by
  intro r hr
  let x : PowerSeries ℤ := X
  let b : PowerSeries ℤ := derivative ℤ r
  let c : PowerSeries ℤ := derivative ℤ b
  have h0 : r - x * (1 + r + r ^ 2) = 0 := by dsimp [x]; rw [← hr]; ring
  have h1 : b - (1 + r + r ^ 2) - x * (b + 2 * r * b) = 0 := by
    have h := congrArg (derivative ℤ) hr
    dsimp only [x, b] at *
    simp only [Derivation.leibniz, smul_eq_mul, map_add, derivative_X, derivative_one, derivative_pow] at h
    linear_combination h
  have h2 : c - 2 * (b + 2 * r * b) - x * (c + 2 * b ^ 2 + 2 * r * c) = 0 := by
    have h := congrArg (derivative ℤ) h1
    dsimp only [x, b, c] at *
    simp only [map_sub, Derivation.leibniz, smul_eq_mul, map_add, derivative_X, derivative_one, derivative_pow, map_ofNat, map_zero] at h
    have htwo : derivative ℤ (2 : PowerSeries ℤ) = 0 := by
      simpa using (derivative ℤ).map_natCast 2
    rw [htwo] at h
    linear_combination h
  let f : PowerSeries ℤ := r ^ 3 + 2 * r ^ 5 + r ^ 7
  let d : PowerSeries ℤ := x * (3 * r ^ 2 + 10 * r ^ 4 + 7 * r ^ 6) * b
  let dd : PowerSeries ℤ := d + x ^ 2 * ((6 * r + 40 * r ^ 3 + 42 * r ^ 5) * b ^ 2 + (3 * r ^ 2 + 10 * r ^ 4 + 7 * r ^ 6) * c)
  let t : PowerSeries ℤ := -dd - 4 * d + 21 * f + x * (4 * dd + 13 * d - 42 * f) + x ^ 2 * (-2 * dd + 5 * d + 45 * f) + x ^ 3 * (-4 * dd - 17 * d) + x ^ 4 * (3 * dd + 3 * d)
  have hm : (1 - x - 2 * x * r) ^ 3 * t = 0 := by
    dsimp only [t, dd, d, f]
    linear_combination (84*r ^ 8*x ^ 8 - 112*r ^ 8*x ^ 7 - 56*r ^ 8*x ^ 6 + 112*r ^ 8*x ^ 5 - 28*r ^ 8*x ^ 4 + 84*r ^ 7*x ^ 8 - 196*r ^ 7*x ^ 7 + 56*r ^ 7*x ^ 6 + 168*r ^ 7*x ^ 5 - 140*r ^ 7*x ^ 4 + 28*r ^ 7*x ^ 3 + 141*r ^ 6*x ^ 8 - 230*r ^ 6*x ^ 7 - 17*r ^ 6*x ^ 6 + 188*r ^ 6*x ^ 5 - 117*r ^ 6*x ^ 4 + 42*r ^ 6*x ^ 3 - 7*r ^ 6*x ^ 2 + 120*r ^ 5*x ^ 8 - 280*r ^ 5*x ^ 7 + 80*r ^ 5*x ^ 6 + 240*r ^ 5*x ^ 5 - 200*r ^ 5*x ^ 4 + 40*r ^ 5*x ^ 3 + 66*r ^ 4*x ^ 8 - 148*r ^ 4*x ^ 7 + 66*r ^ 4*x ^ 6 + 88*r ^ 4*x ^ 5 - 122*r ^ 4*x ^ 4 + 60*r ^ 4*x ^ 3 - 10*r ^ 4*x ^ 2 + 36*r ^ 3*x ^ 8 - 84*r ^ 3*x ^ 7 + 24*r ^ 3*x ^ 6 + 72*r ^ 3*x ^ 5 - 60*r ^ 3*x ^ 4 + 12*r ^ 3*x ^ 3 + 9*r ^ 2*x ^ 8 - 30*r ^ 2*x ^ 7 + 27*r ^ 2*x ^ 6 + 12*r ^ 2*x ^ 5 - 33*r ^ 2*x ^ 4 + 18*r ^ 2*x ^ 3 - 3*r ^ 2*x ^ 2) * h2 + (420*b*r ^ 7*x ^ 8 - 560*b*r ^ 7*x ^ 7 - 280*b*r ^ 7*x ^ 6 + 560*b*r ^ 7*x ^ 5 - 140*b*r ^ 7*x ^ 4 + 462*b*r ^ 6*x ^ 8 - 1078*b*r ^ 6*x ^ 7 + 308*b*r ^ 6*x ^ 6 + 924*b*r ^ 6*x ^ 5 - 770*b*r ^ 6*x ^ 4 + 154*b*r ^ 6*x ^ 3 + 486*b*r ^ 5*x ^ 8 - 900*b*r ^ 5*x ^ 7 + 138*b*r ^ 5*x ^ 6 + 648*b*r ^ 5*x ^ 5 - 582*b*r ^ 5*x ^ 4 + 252*b*r ^ 5*x ^ 3 - 42*b*r ^ 5*x ^ 2 + 420*b*r ^ 4*x ^ 8 - 980*b*r ^ 4*x ^ 7 + 280*b*r ^ 4*x ^ 6 + 840*b*r ^ 4*x ^ 5 - 700*b*r ^ 4*x ^ 4 + 140*b*r ^ 4*x ^ 3 + 156*b*r ^ 3*x ^ 8 - 448*b*r ^ 3*x ^ 7 + 336*b*r ^ 3*x ^ 6 + 208*b*r ^ 3*x ^ 5 - 452*b*r ^ 3*x ^ 4 + 240*b*r ^ 3*x ^ 3 - 40*b*r ^ 3*x ^ 2 + 54*b*r ^ 2*x ^ 8 - 126*b*r ^ 2*x ^ 7 + 36*b*r ^ 2*x ^ 6 + 108*b*r ^ 2*x ^ 5 - 90*b*r ^ 2*x ^ 4 + 18*b*r ^ 2*x ^ 3 + 18*b*r*x ^ 8 - 60*b*r*x ^ 7 + 54*b*r*x ^ 6 + 24*b*r*x ^ 5 - 66*b*r*x ^ 4 + 36*b*r*x ^ 3 - 6*b*r*x ^ 2 - 210*r ^ 8*x ^ 7 - 84*r ^ 8*x ^ 6 + 336*r ^ 8*x ^ 5 - 28*r ^ 8*x ^ 4 - 14*r ^ 8*x ^ 3 - 336*r ^ 7*x ^ 7 + 126*r ^ 7*x ^ 6 + 728*r ^ 7*x ^ 5 - 420*r ^ 7*x ^ 4 - 168*r ^ 7*x ^ 3 + 70*r ^ 7*x ^ 2 - 516*r ^ 6*x ^ 7 + 161*r ^ 6*x ^ 6 + 785*r ^ 6*x ^ 5 - 566*r ^ 6*x ^ 4 + 38*r ^ 6*x ^ 3 + 133*r ^ 6*x ^ 2 - 35*r ^ 6*x - 426*r ^ 5*x ^ 7 + 174*r ^ 5*x ^ 6 + 916*r ^ 5*x ^ 5 - 572*r ^ 5*x ^ 4 - 170*r ^ 5*x ^ 3 + 78*r ^ 5*x ^ 2 - 318*r ^ 4*x ^ 7 + 198*r ^ 4*x ^ 6 + 606*r ^ 4*x ^ 5 - 616*r ^ 4*x ^ 4 - 30*r ^ 4*x ^ 3 + 210*r ^ 4*x ^ 2 - 50*r ^ 4*x - 156*r ^ 3*x ^ 7 + 154*r ^ 3*x ^ 6 + 208*r ^ 3*x ^ 5 - 252*r ^ 3*x ^ 4 + 44*r ^ 3*x ^ 3 + 2*r ^ 3*x ^ 2 - 36*r ^ 2*x ^ 7 + 9*r ^ 2*x ^ 6 + 141*r ^ 2*x ^ 5 - 126*r ^ 2*x ^ 4 - 42*r ^ 2*x ^ 3 + 69*r ^ 2*x ^ 2 - 15*r ^ 2*x - 18*r*x ^ 7 + 42*r*x ^ 6 - 12*r*x ^ 5 - 36*r*x ^ 4 + 30*r*x ^ 3 - 6*r*x ^ 2) * h1 + (210*r ^ 8*x ^ 6 + 84*r ^ 8*x ^ 5 + 24*r ^ 8*x ^ 4 - 308*r ^ 8*x ^ 3 + 182*r ^ 8*x ^ 2 + 336*r ^ 7*x ^ 6 + 84*r ^ 7*x ^ 5 - 464*r ^ 7*x ^ 4 - 264*r ^ 7*x ^ 3 + 448*r ^ 7*x ^ 2 - 140*r ^ 7*x + 516*r ^ 6*x ^ 6 - 35*r ^ 6*x ^ 5 - 335*r ^ 6*x ^ 4 - 342*r ^ 6*x ^ 3 + 486*r ^ 6*x ^ 2 - 119*r ^ 6*x + 21*r ^ 6 + 426*r ^ 5*x ^ 6 + 6*r ^ 5*x ^ 5 - 540*r ^ 5*x ^ 4 - 436*r ^ 5*x ^ 3 + 818*r ^ 5*x ^ 2 - 274*r ^ 5*x + 318*r ^ 4*x ^ 6 - 78*r ^ 4*x ^ 5 - 526*r ^ 4*x ^ 4 + 72*r ^ 4*x ^ 3 + 390*r ^ 4*x ^ 2 - 218*r ^ 4*x + 42*r ^ 4 + 156*r ^ 3*x ^ 6 - 136*r ^ 3*x ^ 5 - 112*r ^ 3*x ^ 4 - 120*r ^ 3*x ^ 3 + 340*r ^ 3*x ^ 2 - 128*r ^ 3*x + 36*r ^ 2*x ^ 6 + 9*r ^ 2*x ^ 5 - 183*r ^ 2*x ^ 4 + 138*r ^ 2*x ^ 3 + 78*r ^ 2*x ^ 2 - 99*r ^ 2*x + 21*r ^ 2 + 18*r*x ^ 6 - 42*r*x ^ 5 + 12*r*x ^ 4 + 36*r*x ^ 3 - 30*r*x ^ 2 + 6*r*x) * h0
  have hne : (1 - x - 2 * x * r) ^ 3 ≠ 0 := by
    intro h
    have hc := congrArg (coeff 0) h
    simp [x] at hc
  have ht : t = 0 := (mul_eq_zero.mp hm).resolve_left hne
  have hconst (n : ℕ) : derivative ℤ (n : PowerSeries ℤ) = 0 := (derivative ℤ).map_natCast n
  dsimp only
  simp only [euler_eq, show (2 : ℤ) • r ^ 5 = r ^ 5 + r ^ 5 by simp [two_zsmul]; ring]
  convert ht using 1 <;> dsimp [t, dd, d, f, x, b, c] <;>
    simp only [map_add, map_sub, map_neg, map_nsmul, Derivation.leibniz,
      smul_eq_mul, derivative_X, derivative_pow, hconst] <;>
    (try simp only [map_add, Derivation.leibniz, smul_eq_mul, derivative_X, derivative_pow, hconst]) <;> ring